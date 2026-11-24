#!/usr/bin/env python3
"""Keep `proof` issues in step with the `sorry`s in RiemannMasullo/.

    scripts/issues.py            show what would change
    scripts/issues.py --apply    open an issue per new sorry, close issues whose sorry is gone,
                                 and unblock section issues whose prerequisites are closed

Run from an up-to-date `main`. Lean itself reports the sorries (`lake build` warnings), so this
never misreads the source. An issue is tied to its declaration by a hidden marker in the body.
A section issue lists the issues it waits for in a marker `<!-- needs: 12 15 -->`; when all of
them are closed, its `blocked` label is removed.
"""
import json, pathlib, re, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
WARN = re.compile(r"warning: (RiemannMasullo/\S+?\.lean):(\d+):(\d+): declaration uses `sorry`")
MARK = re.compile(r"<!-- sorry: (\S+) -->")
DECL = re.compile(r"\s*(@\[[^\]]*\]\s*)*((private|protected|noncomputable|nonrec|unsafe|partial|public|meta)\s+)*"
                  r"(theorem|lemma|def|instance|abbrev|example|structure|class|inductive|opaque)\b")


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, **kw)


def list_issues(state, label):
    """All issues with a label, through the REST listing. `gh issue list` with a label goes
    through GitHub's search, which stops at 1,000 results, and a truncated list of open proof
    issues makes this script open duplicates."""
    out = run(["gh", "api", "--paginate",
               f"repos/{{owner}}/{{repo}}/issues?state={state}&labels={label}&per_page=100",
               "--jq", ".[] | select(.pull_request | not) "
                        "| {number, state, title, body, labels: [.labels[].name]} | tojson"])
    if out.returncode:
        sys.exit(out.stderr)
    return [json.loads(line) for line in out.stdout.splitlines() if line.strip()]


def sorries():
    out = run(["lake", "build", "RiemannMasullo"])
    if out.returncode:
        sys.exit("lake build failed; fix the build first\n" + (out.stdout + out.stderr)[-3000:])
    found = {}
    for path, line, col in WARN.findall(out.stdout + out.stderr):
        lines = (ROOT / path).read_text().splitlines()
        i = int(line) - 1
        # The warning points into the file as Lean compiled it. If the file on disk is another
        # version (the checkout moved during the build), the position lands on arbitrary text
        # and everything below would be read off the wrong lines. Stop instead.
        if i >= len(lines) or not DECL.match(lines[i]):
            sys.exit(f"{path}:{line}: the build reports a `sorry` here, but this line of the file is "
                     "not a declaration. The checkout does not match the build (did it change "
                     "during the run?). Nothing was changed; update, rebuild and run again.")
        name = re.match(r"[^\s:({\[]+", lines[i][int(col):])
        name = name.group(0) if name else f"line{line}"
        top = i
        while top > 0 and lines[top - 1].lstrip().startswith("@["):
            top -= 1
        if top > 0 and lines[top - 1].rstrip().endswith("-/"):
            top -= 1
            while top > 0 and "/--" not in lines[top]:
                top -= 1
        end = i
        while end < len(lines) - 1 and "sorry" not in lines[end] and end - i < 80:
            end += 1
        block = "\n".join(lines[top:end + 1])
        paper = re.search(r"Paper:\s*(.*?\bpp?\.\s*\d+(?:[-–]\d+)?)", block)
        found[f"{path}::{name}"] = dict(path=path, line=int(line), name=name, block=block,
                                        paper=paper.group(1) if paper else "")
    return found


UNPROVED = re.compile(r"(?<![\w.'])(sorry|admit)(?![\w'])")


def text_has_sorry(lines, i):
    """Whether the declaration that starts on line `i` (0-based) has `sorry` in its text: from
    that line to the next declaration or comment block, with `--` comments left out."""
    end = i + 1
    while end < len(lines) and not DECL.match(lines[end]) and not lines[end].lstrip().startswith("/-"):
        end += 1
    return bool(UNPROVED.search("\n".join(re.sub(r"--.*", "", line) for line in lines[i:end])))


def still_sorry(key):
    """Whether the declaration that an issue names (`path::name`) still has `sorry` in its text
    on this checkout. False if the file or the declaration is gone."""
    path, name = key.split("::", 1)
    if not (ROOT / path).is_file():
        return False
    lines = (ROOT / path).read_text().splitlines()
    for i, text in enumerate(lines):
        m = DECL.match(text)
        if m and re.match(rf"\s+{re.escape(name)}(?=$|[\s:({{\[])", text[m.end():]) and text_has_sorry(lines, i):
            return True
    return False


def disagreements(current, new, stale):
    """The build says what is proved; the text of the files is a second opinion, and the two
    must agree before anything is changed. An issue to close whose declaration still reads
    `sorry`, or one to open whose declaration does not, means the build output was read against
    the wrong text. That is what happened on 2026-11-21: positions from a build of one commit
    were looked up in the files of another, 110 issues were opened under names that were not
    the unproved declarations, and 150 good ones were closed."""
    bad = [f"would close the issue of {k}, which still has `sorry` in the file" for k in stale if still_sorry(k)]
    for k in new:
        lines = (ROOT / current[k]["path"]).read_text().splitlines()
        if not text_has_sorry(lines, current[k]["line"] - 1):
            bad.append(f"would open an issue for {k}, which has no `sorry` in the file")
    return bad


def statement_of(block):
    """The declaration in an issue's Lean block without its docstring, spacing aside: what must
    not change under someone who is working on the issue."""
    lines = block.splitlines()
    start = next((k for k, text in enumerate(lines) if DECL.match(text)), 0)
    return " ".join(" ".join(lines[start:]).split())


def is_gap(block):
    """A recorded gap: the docstring has a line starting `Gap:` (see AGENTS.md). Its issue is
    labelled `gap` and stays out of the provers' queue."""
    return bool(re.search(r"^\s*Gap:", block, re.M))


def issue_body(s, url, full_sha, key):
    gap = ("**This is a recorded gap**: the project has not been able to prove or refute it, and "
           "the work above it goes on assuming it. It is not in the provers' queue, but a proof, "
           "a refutation or a smaller gap is very welcome.\n\n" if is_gap(s["block"]) else "")
    return (f"[`{s['path']}`, line {s['line']}]({url}/blob/{full_sha}/{s['path']}#L{s['line']})\n\n"
            f"```lean\n{s['block']}\n```\n\n" + gap +
            "Try to prove this statement as written. A different proof from the paper's is welcome, "
            "and a proof that is too large can be split into smaller, precise lemmas "
            f"([prover guide]({url}/blob/main/prompts/prover.md)). **Do not change the statement.**\n\n"
            "If you find a counterexample, a mismatch between the Lean and the manuscript, or a "
            "specific gap in the printed argument, report it here instead: give the paper item and "
            "page, and say exactly what fails, with a concrete counterexample or the failing step "
            "(best of all, a Lean proof of the negation). That is a successful contribution in its "
            "own right, and you need not propose a repair. If you can neither prove nor refute the "
            "statement, leave a short note here on what you tried and where you got stuck.\n\n"
            "**To take this issue**, comment `Claiming`, then follow "
            f"[CONTRIBUTING.md]({url}/blob/main/CONTRIBUTING.md). The paper is in "
            f"[`paper/`]({url}/tree/main/paper).\n\n"
            f"<!-- sorry: {key} -->\n")


def chapter_label(path):
    m = re.match(r"RiemannMasullo/(Ch\d+|App[A-E])", path)
    return m.group(1)[0].lower() + m.group(1)[1:] if m else None


# The parts of the paper that were left out of the first pass and are stated as supplementary
# material (README, "Roadmap"): Chapters 8 and 14, Appendix E, §A.4 and §B.7. Their issues carry
# the label `supplementary`, so that the progress page can count them apart from the statements
# the trace formula rests on. A new part is added here and in the README's table.
SUPPLEMENTARY = (
    "RiemannMasullo/Ch08_",
    "RiemannMasullo/Ch14_",
    "RiemannMasullo/AppE_",
    "RiemannMasullo/AppA_AlgebraicNT/Sec4",
    "RiemannMasullo/AppB_AnalyticNT/Sec7",
)


def is_supplementary(path):
    return path.startswith(SUPPLEMENTARY)


def at_main():
    """Whether this checkout is at the tip of origin/main. Applying from an older commit would
    close the issues of every `sorry` added since, and reopen those proved since."""
    run(["git", "fetch", "-q", "origin", "main"])
    head = run(["git", "rev-parse", "HEAD"]).stdout.strip()
    tip = run(["git", "rev-parse", "origin/main"]).stdout.strip()
    return head == tip, head[:7], tip[:7]


def main():
    apply = "--apply" in sys.argv
    if apply:
        # The integrator and the merger may both run this, from different checkouts. One at a
        # time, so that neither opens an issue the other has just opened.
        import fcntl
        common = run(["git", "rev-parse", "--path-format=absolute", "--git-common-dir"]).stdout.strip()
        lockdir = pathlib.Path(common).parent / ".agent"
        lockdir.mkdir(exist_ok=True)
        global _lock
        _lock = open(lockdir / "issues.lock", "w")
        fcntl.flock(_lock, fcntl.LOCK_EX)
        # A checkout a few merges behind is handled below. One far behind is refused.
        run(["git", "fetch", "-q", "origin", "main"])
        behind = int(run(["git", "rev-list", "--count", "HEAD..origin/main"]).stdout.strip() or 0)
        if behind > 40:
            sys.exit(f"this checkout is {behind} commits behind origin/main: update it, then rerun")
    branch = run(["git", "rev-parse", "--abbrev-ref", "HEAD"]).stdout.strip()
    if branch != "main":
        print(f"note: on branch {branch}, not main", file=sys.stderr)
    sha = run(["git", "rev-parse", "--short", "HEAD"]).stdout.strip()
    full_sha = run(["git", "rev-parse", "HEAD"]).stdout.strip()
    url = run(["gh", "repo", "view", "--json", "url", "--jq", ".url"]).stdout.strip()
    state = lambda: (run(["git", "rev-parse", "HEAD"]).stdout.strip(),
                     run(["git", "status", "--porcelain", "--untracked-files=no", "--", "RiemannMasullo"]).stdout)
    before = state()
    current = sorries()
    if state() != before:
        sys.exit("the checkout changed while this ran (another commit was checked out, or files "
                 "were edited). Nothing was changed; run again from a checkout nobody else is using.")
    open_issues, issue_of = {}, {}
    for issue in sorted(list_issues("open", "proof"), key=lambda i: -i["number"]):
        m = MARK.search(issue["body"] or "")
        if m:
            open_issues[m.group(1)] = issue["number"]      # the oldest issue wins
            issue_of[m.group(1)] = issue

    new = [k for k in current if k not in open_issues]
    stale = [k for k in open_issues if k not in current]
    # `main` moves while this runs, and the checkout may be a few merges behind. What this
    # checkout cannot know about is left alone: a `sorry` whose issue was closed after this
    # commit was made (it has just been proved), and an issue opened after it (its `sorry` is
    # newer than this checkout). The next run, from a later commit, settles both.
    head_time = run(["git", "show", "-s", "--format=%cI", "HEAD"]).stdout.strip()
    since = run(["date", "-u", "-d", f"{head_time} - 2 minutes", "+%Y-%m-%dT%H:%M:%SZ"]).stdout.strip()
    recent = run(["gh", "api", "--paginate",
                  f"repos/{{owner}}/{{repo}}/issues?state=all&labels=proof&since={since}&per_page=100",
                  "--jq", ".[] | select(.pull_request | not) | {number, state, body, created_at} | tojson"])
    if recent.returncode:
        sys.exit(recent.stderr)
    recent = [json.loads(line) for line in recent.stdout.splitlines() if line.strip()]
    just_closed = {m.group(1) for i in recent if i["state"] == "closed"
                   for m in [MARK.search(i["body"] or "")] if m}
    just_opened = {i["number"] for i in recent if i["created_at"] >= since}
    skipped = [k for k in new if k in just_closed] + [k for k in stale if open_issues[k] in just_opened]
    new = [k for k in new if k not in just_closed]
    stale = [k for k in stale if open_issues[k] not in just_opened]
    if skipped:
        print(f"note: {len(skipped)} left for the next run (changed on main after {sha})")
    print(f"{len(current)} sorries at {sha}; {len(open_issues)} open proof issues; "
          f"{len(new)} to open, {len(stale)} to close")
    # Many issues at once are normal: a section's statements arrive sixty at a time, and a file
    # that is closed out takes forty issues with it. What must not happen is a wrong one.
    bad = disagreements(current, new, stale)
    for line in bad[:30]:
        print("  DISAGREES:", line)
    force = "--force" in sys.argv
    if apply and bad and not force:
        sys.exit(f"{len(bad)} of these changes disagree with the text of the files (listed above). "
                 "Nothing was changed. Either the build and the files do not match, or the text "
                 "check is fooled by something unusual in those declarations: look at them, and "
                 "pass --force only if the changes are right.")
    if apply and len(stale) > max(60, len(open_issues) // 2) and not force:
        sys.exit(f"this would close {len(stale)} of the {len(open_issues)} open proof issues at "
                 "once. Nothing was changed; look at the dry run, and pass --force if it is right.")
    for key in new:
        s = current[key]
        title = f"Prove `{s['name']}`" + (f" ({s['paper']})" if s["paper"] else "")
        body = issue_body(s, url, full_sha, key)
        print(f"  open   {title}")
        if apply:
            cmd = ["gh", "issue", "create", "--title", title, "--body", body, "--label", "proof"]
            if chapter_label(s["path"]):
                cmd += ["--label", chapter_label(s["path"])]
            if is_gap(s["block"]):
                cmd += ["--label", "gap"]
            if s["path"].endswith("_Printed.lean"):
                cmd += ["--label", "refutation"]
            if is_supplementary(s["path"]):
                cmd += ["--label", "supplementary"]
            r = run(cmd)
            print("        ", (r.stdout or r.stderr).strip())
            time.sleep(1.5)   # stay under GitHub's limit on creating content
    for key in stale:
        print(f"  close  #{open_issues[key]}  {key}")
        if apply:
            run(["gh", "issue", "close", str(open_issues[key]), "--comment",
                 f"`{key.split('::')[1]}` is no longer a `sorry` on main at {sha}."])
    # An issue shows the statement as it was when the issue was opened. When the declaration has
    # changed since (a repaired statement, a corrected docstring), bring the issue up to date, and
    # say so if the statement itself changed: someone may be working from the old text.
    for key, s in current.items():
        issue = issue_of.get(key)
        if issue is None or key in skipped:
            continue
        number, labels = issue["number"], issue["labels"]
        shown = re.search(r"```lean\n(.*?)\n```", issue["body"] or "", re.S)
        if shown and shown.group(1) != s["block"]:
            changed = statement_of(shown.group(1)) != statement_of(s["block"])
            print(f"  refresh #{number}  {key}" + ("  (statement changed)" if changed else ""))
            if apply:
                run(["gh", "issue", "edit", str(number), "--body", issue_body(s, url, full_sha, key)])
                if changed:
                    run(["gh", "issue", "comment", str(number), "--body",
                         f"The statement of this declaration has changed on `main` (at {sha}); the text "
                         "above is now the current one. If you are working on it, update your branch "
                         "before you go on."])
                time.sleep(1.0)
        if is_gap(s["block"]) != ("gap" in labels):
            print(f"  {'mark' if is_gap(s['block']) else 'unmark'} #{number} as a gap  {key}")
            if apply:
                run(["gh", "issue", "edit", str(number),
                     "--add-label" if is_gap(s["block"]) else "--remove-label", "gap"])
        if is_supplementary(s["path"]) and "supplementary" not in labels:
            print(f"  mark #{number} as supplementary  {key}")
            if apply:
                run(["gh", "issue", "edit", str(number), "--add-label", "supplementary"])
    ready = unblock(apply)
    if not apply and (new or stale or ready):
        print("dry run; pass --apply to make these changes")


def unblock(apply):
    """Remove `blocked` from open issues whose `<!-- needs: ... -->` issues are all closed."""
    states = {i["number"]: i["state"] for i in list_issues("all", "section")}
    blocked = list_issues("open", "blocked")
    ready = []
    for issue in sorted(blocked, key=lambda i: i["number"]):
        m = re.search(r"<!-- needs:([\d\s]*)-->", issue["body"] or "")
        if m and all(states.get(int(n)) == "closed" for n in m.group(1).split()):
            ready.append(issue["number"])
            print(f"  unblock #{issue['number']}  {issue['title']}")
            if apply:
                run(["gh", "issue", "edit", str(issue["number"]), "--remove-label", "blocked"])
    return ready


if __name__ == "__main__":
    main()
