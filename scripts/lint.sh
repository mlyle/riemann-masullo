#!/usr/bin/env bash
# Text check for constructs that must not appear in the library. See AGENTS.md.
#
#   scripts/lint.sh          check this checkout
#   scripts/lint.sh <dir>    check another tree with this checkout's rules (used by the CI checks,
#                            which never run a script that came from the pull request)
set -uo pipefail
cd "${1:-$(dirname "$0")/..}" || exit 2
# Never allowed.
forbidden='^[[:space:]]*(private |protected |noncomputable |unsafe )*(axiom|opaque)[[:space:]]|native_decide|decide[[:space:]]*\+native|bv_decide|ofReduceBool|trustCompiler|implemented_by|@\[extern|^[[:space:]]*unsafe[[:space:]]|set_option[[:space:]]+debug\.|skipKernelTC|sorryAx'
# Code that runs when the file is built. Vendored code under External/ is reviewed by hand instead.
buildtime='#eval|run_cmd|run_elab|run_meta|run_tac|by_elab|\bd?simproc\b|^[[:space:]]*(builtin_)?initialize\b|^[[:space:]]*(local |scoped )?elab(_rules)?\b|@\[(command_elab|term_elab|tactic|init)\b'
[ -d RiemannMasullo ] || { echo "lint: no RiemannMasullo directory in $PWD" >&2; exit 2; }
# Only paths that exist: grep reports a missing path with status 2 even when it found a match.
targets=(RiemannMasullo); [ -e Main.lean ] && targets+=(Main.lean)
[ -d RiemannMasulloClassField ] && targets+=(RiemannMasulloClassField)
status=0
grep -rnE --include='*.lean' "$forbidden" "${targets[@]}" && status=1
grep -rnE --include='*.lean' --exclude-dir=External "$buildtime" "${targets[@]}" && status=1
if [ $status = 1 ]; then
  echo "lint: forbidden construct found (see AGENTS.md)" >&2
  exit 1
fi
echo "lint: ok"
