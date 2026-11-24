#!/usr/bin/env python3
"""Tests for auto_merge.py against a stand-in for the GitHub API."""
import base64
import io
import json
import os
import re
import unittest
import zipfile
from unittest import mock

import auto_merge

REPO_ID = 1
BASE = "b" * 40          # main when the check ran
MERGE_BASE = "a" * 40
LEAN = "RiemannMasullo/AppA/Sec1.lean"
OLD = "theorem t : True := by\n  sorry\n\nvariable (n : Nat)\n"
NEW = "theorem t : True := by\n  trivial\n\nvariable (n : Nat)\n"


def zipped(files):
    data = io.BytesIO()
    with zipfile.ZipFile(data, "w") as archive:
        for name, content in files.items():
            archive.writestr(name, content)
    return data.getvalue()


class FakeApi:
    """Canned answers for reads; a record of every change asked for."""

    repo = "owner/name"
    dry_run = False

    def __init__(self):
        self.calls = 0
        self.changes = []
        self.artifacts, self.prs, self.runs = [], {}, {}
        self.common, self.heads, self.blobs = {}, {}, {}   # the merge base's files; each head's changes
        self.main_files = []          # files main changed since BASE
        self.not_on_main = set()      # commits that are not ancestors of main
        self.merge_errors = {}
        self._ids = iter(range(100, 10_000))

    # -- building a scenario --

    def blob_id(self, content):
        sha = format(next(self._ids), "040x")
        self.blobs[sha] = content.encode() if isinstance(content, str) else content
        return sha

    def pull_request(self, number, files, head=None, verdict="merge", base=BASE, name=None,
                     draft=False, labels=(), run=None, verdict_json=None, mode="100644"):
        """A pull request changing {path: (old text or None, new text or None)}."""
        head = head or format(number, "040x")
        changes = {}
        for path, (old, new) in files.items():
            if old is not None and path not in self.common:
                self.common[path] = ("100644", "blob", self.blob_id(old))
            changes[path] = None if new is None else (mode, "blob", self.blob_id(new))
        self.heads[head] = changes
        self.prs[number] = dict(number=number, state="open", draft=draft, labels=[dict(name=l) for l in labels],
                                head=dict(sha=head, ref=f"branch-{number}", repo=dict(id=50 + number)),
                                base=dict(ref="main", repo=dict(id=REPO_ID)), mergeable_state="clean")
        run_id = 1000 + number
        self.runs[run_id] = dict(id=run_id, path=auto_merge.CHECK_WORKFLOW, event="pull_request", head_sha=head,
                                 head_repository=dict(id=50 + number), status="completed", conclusion="success",
                                 run_attempt=1, run_started_at="2026-01-01T00:00:00Z")
        self.runs[run_id].update(run or {})
        content = verdict_json if verdict_json is not None else json.dumps(
            dict(schema=1, verdict=verdict, pr=number, head_sha=head, base_sha=base, reasons=[]))
        self.artifacts.append(dict(
            id=2000 + number, name=name or f"verdict-{verdict}", expired=False, size_in_bytes=300,
            created_at=f"2026-01-01T00:10:{number % 60:02d}Z", zip=zipped({"verdict.json": content}),
            workflow_run=dict(id=run_id, repository_id=REPO_ID, head_repository_id=50 + number,
                              head_branch=f"branch-{number}", head_sha=head)))
        return head

    # -- the API --

    def call(self, path, method="GET", body=None, binary=False):
        self.calls += 1
        if method != "GET":
            raise AssertionError(f"a change through call(): {method} {path}")
        if path == "":
            return dict(id=REPO_ID)
        if path.startswith("actions/artifacts?"):
            name = re.search(r"name=([a-z-]+)", path).group(1)
            return dict(artifacts=[{k: v for k, v in a.items() if k != "zip"}
                                   for a in self.artifacts if a["name"] == name])
        if m := re.fullmatch(r"actions/artifacts/(\d+)/zip", path):
            return next(a["zip"] for a in self.artifacts if a["id"] == int(m.group(1)))
        if path.startswith("pulls?"):
            return [p for p in self.prs.values() if p["state"] == "open"] if "page=1" in path else []
        if m := re.fullmatch(r"pulls/(\d+)", path):
            return self.prs[int(m.group(1))]
        if path.startswith("actions/runs?"):
            sha = re.search(r"head_sha=([0-9a-f]+)", path).group(1)
            return dict(workflow_runs=[r for r in self.runs.values() if r["head_sha"] == sha])
        if m := re.fullmatch(r"compare/([0-9a-f]{40})\.\.\.([0-9a-f]{40})\?per_page=1", path):
            return dict(merge_base_commit=dict(sha=MERGE_BASE))
        if m := re.fullmatch(r"compare/([0-9a-f]{40})\.\.\.main\?per_page=1", path):
            if m.group(1) in self.not_on_main:
                return dict(status="diverged", ahead_by=3, behind_by=2, files=[])
            if not self.main_files:
                return dict(status="identical", ahead_by=0, behind_by=0, files=[])
            return dict(status="ahead", ahead_by=len(self.main_files), behind_by=0,
                        files=[dict(filename=f) for f in self.main_files])
        if m := re.fullmatch(r"git/trees/([0-9a-f]{40})\?recursive=1", path):
            return dict(truncated=False, tree=[dict(path=p, mode=e[0], type=e[1], sha=e[2])
                                               for p, e in self.tree(m.group(1)).items()])
        if m := re.fullmatch(r"git/blobs/([0-9a-f]{40})", path):
            data = self.blobs[m.group(1)]
            return dict(size=len(data), encoding="base64", content=base64.b64encode(data).decode())
        raise AssertionError(f"unexpected call {path}")

    def tree(self, sha):
        files = dict(self.common)
        for path, entry in self.heads.get(sha, {}).items():
            if entry is None:
                files.pop(path, None)
            else:
                files[path] = entry
        return files

    def change(self, what, path, method, body=None):
        self.changes.append((method, path, body))
        if m := re.fullmatch(r"pulls/(\d+)/merge", path):
            number = int(m.group(1))
            if number in self.merge_errors:
                raise auto_merge.ApiError(*self.merge_errors[number])
            assert body == dict(merge_method="squash", sha=self.prs[number]["head"]["sha"])
            self.prs[number]["state"] = "closed"
            # main now contains what the pull request changed
            self.main_files += list(self.heads[self.prs[number]["head"]["sha"]])
            return dict(merged=True, sha="c" * 40)
        if m := re.fullmatch(r"actions/artifacts/(\d+)", path):
            self.artifacts = [a for a in self.artifacts if a["id"] != int(m.group(1))]
        return {}

    def did(self, method, pattern):
        return [c for c in self.changes if c[0] == method and re.fullmatch(pattern, c[1])]


class AutoMerge(unittest.TestCase):
    def setUp(self):
        self.api = FakeApi()
        # Not the repository id, run id or summary file of the workflow these tests run in.
        environment = mock.patch.dict(os.environ, clear=True)
        environment.start()
        self.addCleanup(environment.stop)

    def drain(self, **options):
        merger = auto_merge.Merger(self.api, **options)
        import contextlib
        with contextlib.redirect_stdout(io.StringIO()) as out:
            merger.drain()
        self.out = out.getvalue()
        return {number: outcome for number, _sha, outcome in merger.rows}

    def merged(self):
        return [int(re.search(r"\d+", c[1]).group(0)) for c in self.api.did("PUT", r"pulls/\d+/merge")]

    def test_plain_proof_is_merged_at_the_checked_commit(self):
        self.api.pull_request(7, {LEAN: (OLD, NEW)})
        self.assertEqual(self.drain(), {7: "merged"})
        self.assertEqual(self.merged(), [7])
        self.assertTrue(self.api.did("POST", r"actions/workflows/main_state.yml/dispatches"))

    def test_nothing_waiting_costs_one_call(self):
        self.drain()
        self.assertEqual(self.api.calls, 1)

    def test_forged_verdict_for_a_change_to_the_workflows(self):
        self.api.pull_request(7, {LEAN: (OLD, NEW), ".github/workflows/pr_check.yml": ("a", "b")})
        self.assertIn("refused", self.drain()[7])
        self.assertEqual(self.merged(), [])
        self.assertFalse(self.api.artifacts)                        # the hint is used up
        self.assertEqual(self.api.did("POST", r"statuses/.*")[0][2]["state"], "failure")

    def test_forged_verdict_for_other_files(self):
        for path in ("lakefile.toml", "lean-toolchain", "lake-manifest.json", "scripts/lint.sh", "Main.lean",
                     "RiemannMasullo/External/X.lean", "RiemannMasullo/External/ATTRIBUTION.md",
                     "RiemannMasullo/a b.lean", "RiemannMasullo/X.txt"):
            api = self.api = FakeApi()
            api.pull_request(7, {path: ("a", "b")})
            self.assertIn("refused", self.drain()[7], path)
            self.assertEqual(self.merged(), [], path)

    def test_forged_verdict_for_text_that_is_not_a_proof(self):
        for new in (NEW + "variable [Fact False]\n", OLD.replace("sorry", "trivial initialize x : Unit ← pure ()"),
                    OLD.replace("sorry", "native_decide"), OLD.replace("(n : Nat)", "(n : Nat) (h : False)"),
                    OLD + "theorem u : True := by\n  sorry\n"):
            self.api = FakeApi()
            self.api.pull_request(7, {LEAN: (OLD, new)})
            self.assertIn("refused", self.drain()[7], new)
            self.assertEqual(self.merged(), [], new)

    def test_new_deleted_and_special_files(self):
        for files, mode in (({LEAN: (None, NEW)}, "100644"), ({LEAN: (OLD, None)}, "100644"),
                            ({LEAN: (OLD, NEW)}, "120000"), ({LEAN: (OLD, NEW)}, "100755")):
            self.api = FakeApi()
            self.api.pull_request(7, files, mode=mode)
            self.assertIn("refused", self.drain()[7])
            self.assertEqual(self.merged(), [])

    def test_artifact_that_is_not_a_verdict(self):
        head = format(7, "040x")
        good = dict(schema=1, verdict="merge", pr=7, head_sha=head, base_sha=BASE)
        for bad in (dict(good, verdict="read"), dict(good, pr=8), dict(good, head_sha="f" * 40),
                    dict(good, base_sha="main"), dict(good, base_sha=BASE + "; rm -rf /"), dict(good, schema=2),
                    dict(good, pr="7"), [good], "x" * (auto_merge.MAX_VERDICT_BYTES + 10)):
            self.api = FakeApi()
            self.api.pull_request(7, {LEAN: (OLD, NEW)}, verdict_json=bad if isinstance(bad, str) else json.dumps(bad))
            self.assertIn("refused", self.drain()[7], bad)
            self.assertEqual(self.merged(), [])

    def test_verdict_against_a_commit_that_is_not_main(self):
        # A pull request can name one of its own commits as "main", against which the rest of
        # it looks like a plain proof.
        self.api.pull_request(7, {LEAN: (OLD, NEW)}, base="d" * 40)
        self.api.not_on_main.add("d" * 40)
        self.assertIn("refused", self.drain()[7])
        self.assertEqual(self.merged(), [])
        self.assertFalse(self.api.did("POST", r"actions/runs/\d+/rerun"))

    def test_main_changed_the_same_file(self):
        self.api.pull_request(7, {LEAN: (OLD, NEW)})
        self.api.main_files = ["README.md", LEAN]
        self.assertIn("checking again", self.drain()[7])
        self.assertEqual(self.merged(), [])
        self.assertTrue(self.api.did("POST", r"actions/runs/1007/rerun"))
        self.assertFalse(self.api.artifacts)

    def test_main_changed_the_checker(self):
        for path in ("scripts/lint.sh", "scripts/proof_review.sh", ".github/workflows/pr_check.yml",
                     "lean-toolchain", "lakefile.toml", "lake-manifest.json", "Main.lean",
                     "RiemannMasullo/External/X.lean"):
            self.api = FakeApi()
            self.api.pull_request(7, {LEAN: (OLD, NEW)})
            self.api.main_files = [path]
            self.assertIn("checking again", self.drain()[7], path)
            self.assertEqual(self.merged(), [])

    def test_main_changed_something_else(self):
        self.api.pull_request(7, {LEAN: (OLD, NEW)})
        self.api.main_files = ["RiemannMasullo/AppB/Sec2.lean", "ERRATA.md", "README.md",
                               "RiemannMasullo/External/ATTRIBUTION.md"]
        self.assertEqual(self.drain(), {7: "merged"})

    def test_main_changed_the_progress_map_and_statement_reviewer(self):
        self.api.pull_request(7, {LEAN: (OLD, NEW)})
        self.api.main_files = ["scripts/progress/template.html", "scripts/review.sh"]
        self.assertEqual(self.drain(), {7: "merged"})
        self.assertFalse(self.api.did("POST", r"actions/runs/\d+/rerun"))

    def test_two_pull_requests_for_one_file_are_not_merged_on_one_check(self):
        self.api.pull_request(7, {LEAN: (OLD, NEW)})
        self.api.pull_request(8, {LEAN: (OLD, OLD.replace("sorry", "exact True.intro"))})
        self.api.pull_request(9, {"RiemannMasullo/AppB/Sec2.lean": (OLD, NEW)})
        outcomes = self.drain()
        self.assertEqual(outcomes[7], "merged")
        self.assertIn("checking again", outcomes[8])
        self.assertEqual(outcomes[9], "merged")
        self.assertEqual(self.merged(), [7, 9])

    def test_gives_up_after_many_checks(self):
        self.api.pull_request(7, {LEAN: (OLD, NEW)}, run=dict(run_attempt=auto_merge.MAX_ATTEMPTS))
        self.api.main_files = [LEAN]
        self.assertIn("given up", self.drain()[7])
        self.assertFalse(self.api.did("POST", r"actions/runs/\d+/rerun"))

    def test_left_alone(self):
        self.api.pull_request(7, {LEAN: (OLD, NEW)}, draft=True)
        self.api.pull_request(8, {LEAN: (OLD, NEW)}, labels=["integrator"])
        self.api.pull_request(9, {LEAN: (OLD, NEW)}, verdict="read")
        self.api.pull_request(10, {LEAN: (OLD, NEW)}, labels=["train"])
        outcomes = self.drain()
        self.assertEqual(self.api.changes, [])
        self.assertNotIn(9, outcomes)
        self.assertIn("left to the batch", outcomes[10])

    def test_check_running_again_or_superseded(self):
        self.api.pull_request(7, {LEAN: (OLD, NEW)}, run=dict(status="in_progress", conclusion=None))
        self.assertIn("running again", self.drain()[7])
        self.assertEqual(self.api.changes, [])
        self.api = FakeApi()
        head = self.api.pull_request(7, {LEAN: (OLD, NEW)})
        self.api.runs[5000] = dict(self.api.runs[1007], id=5000, run_started_at="2026-01-02T00:00:00Z")
        self.assertIn("newer run", self.drain()[7])
        self.assertEqual(self.merged(), [])
        self.api = FakeApi()
        self.api.pull_request(7, {LEAN: (OLD, NEW)}, run=dict(run_started_at="2026-01-03T00:00:00Z"))
        self.assertIn("earlier attempt", self.drain()[7])
        self.assertEqual(self.merged(), [])
        self.assertTrue(head)

    def test_run_of_another_workflow_does_not_count(self):
        self.api.pull_request(7, {LEAN: (OLD, NEW)}, run=dict(path=".github/workflows/other.yml"))
        self.assertIn("newer run", self.drain()[7])
        self.assertEqual(self.merged(), [])

    def test_pushed_after_the_check(self):
        self.api.pull_request(7, {LEAN: (OLD, NEW)})
        self.api.prs[7]["head"]["sha"] = "e" * 40
        self.assertEqual(self.drain(), {})          # no open pull request has that head any more
        self.api = FakeApi()
        self.api.pull_request(7, {LEAN: (OLD, NEW)})
        self.api.merge_errors[7] = (409, "Head branch was modified. Review and try the merge again.")
        self.assertIn("pushed to after the check", self.drain()[7])

    def test_conflict_and_branch_rules(self):
        self.api.pull_request(7, {LEAN: (OLD, NEW)})
        self.api.merge_errors[7] = (405, "Pull Request is not mergeable")
        self.api.prs[7]["mergeable_state"] = "dirty"
        self.assertIn("no longer merges cleanly", self.drain()[7])
        self.api = FakeApi()
        self.api.pull_request(7, {LEAN: (OLD, NEW)})
        self.api.merge_errors[7] = (405, "At least 1 approving review is required by reviewers with write access.")
        self.api.prs[7]["mergeable_state"] = "blocked"
        self.assertIn("GitHub refused", self.drain()[7])
        self.assertFalse(self.api.did("POST", r"actions/runs/\d+/rerun"))

    def test_one_merge_denied_to_the_workflow_token_leaves_the_next_pr_eligible(self):
        self.api.pull_request(7, {LEAN: (OLD, NEW)})
        verdict = self.api.artifacts[0]
        self.api.pull_request(8, {LEAN: (OLD, NEW)})
        self.api.merge_errors[7] = (403, "Resource not accessible by integration")
        outcomes = self.drain()
        self.assertIn("needs a project member", outcomes[7])
        self.assertEqual(outcomes[8], "merged")
        self.assertEqual(self.api.prs[7]["state"], "open")
        self.assertIn(verdict, self.api.artifacts)

    def test_rate_limit_on_merge_stops_the_queue(self):
        self.api.pull_request(7, {LEAN: (OLD, NEW)})
        self.api.pull_request(8, {LEAN: (OLD, NEW)})
        self.api.merge_errors[7] = (403, "API rate limit exceeded")
        outcomes = self.drain()
        self.assertIn("rate limit", outcomes[7])
        self.assertNotIn(8, outcomes)

    def test_errors_are_retried_only_when_asked(self):
        self.api.pull_request(7, {LEAN: (OLD, NEW)}, verdict="error", run=dict(conclusion="failure"))
        self.assertEqual(self.drain(), {})
        self.assertIn("checking again", self.drain(retry_errors=True)[7])
        self.assertEqual(self.merged(), [])


class Verdict(unittest.TestCase):
    good = dict(schema=1, verdict="merge", pr=3, head_sha="1" * 40, base_sha="2" * 40)

    def test_reads_what_verdict_py_writes(self):
        self.assertEqual(auto_merge.read_verdict(zipped({"verdict.json": json.dumps(self.good)}))["pr"], 3)

    def test_rejects_everything_else(self):
        for data in (b"", b"not a zip", zipped({"other.json": "{}"}), zipped({"verdict.json": "{"}),
                     zipped({"verdict.json": "[]"}), zipped({"verdict.json": b"\xff"}),
                     zipped({"../verdict.json": json.dumps(self.good)}),
                     zipped({"verdict.json": json.dumps(dict(self.good, pr=True))})):
            self.assertIsNone(auto_merge.read_verdict(data))

    def test_size_limit(self):
        big = json.dumps(dict(self.good, reasons=["x" * auto_merge.MAX_VERDICT_BYTES]))
        self.assertIsNone(auto_merge.read_verdict(zipped({"verdict.json": big})))


class Paths(unittest.TestCase):
    def test_what_matters_to_every_check(self):
        for path in ("lakefile.toml", "lean-toolchain", "lake-manifest.json", "scripts/ci/verdict.py",
                     ".github/workflows/pr_check.yml", "Main.lean", "Statements.lean", "RiemannMasullo/External/A.lean"):
            self.assertTrue(auto_merge.matters_to_everyone(path), path)
        for path in ("RiemannMasullo/AppA/Sec1.lean", "ERRATA.md", "paper/paper.pdf", "prompts/prover.md",
                     "RiemannMasullo/External/ATTRIBUTION.md", ".github/workflows/claims.yml",
                     "scripts/ci/stale_claims.py", "scripts/ci/test_stale_claims.py",
                     "scripts/ci/auto_merge.py", "scripts/ci/test_auto_merge.py"):
            self.assertFalse(auto_merge.matters_to_everyone(path), path)


if __name__ == "__main__":
    unittest.main()
