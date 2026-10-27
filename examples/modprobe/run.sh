#!/usr/bin/env bash
# Probe modules for chapter 28, section 15 (module visibility).
# They import only the core library, so each compiles in a second or two.
# Usage, from any directory:  bash examples/modprobe/run.sh
# Needs `lean` (the toolchain pinned by lean-toolchain) on PATH.
# Some probes are meant to fail. Exit status: 0 if every probe ends as expected,
# 1 if any does not (or is skipped because its prerequisite failed), 2 if `lean` is missing.
cd "$(dirname "$0")" || exit 2
command -v lean >/dev/null 2>&1 || { echo "run.sh: lean not found on PATH" >&2; exit 2; }
D="$(pwd -W 2>/dev/null || pwd)"
# Remove outputs of earlier runs, so a probe can never read a stale .olean.
rm -f ModProbe*.olean ModProbe*.olean.* ModProbe*.ilean ModProbe*.ir ModProbe*.ir.sig
bad=0
built=" "
# module | expected: ok, or fail:<text the output must contain> | prerequisite module
while IFS='|' read -r m want dep; do
  echo "=== $m ==="
  if [ -n "$dep" ]; then
    case $built in
      *" $dep "*) ;;
      *) echo "UNEXPECTED: skipped, prerequisite $dep did not build"; bad=1; continue ;;
    esac
  fi
  out=$(LEAN_PATH="$D" lean -DautoImplicit=false -R . -o "$m.olean" "$m.lean" 2>&1)
  rc=$?
  [ -n "$out" ] && printf '%s\n' "$out"
  echo "exit=$rc"
  case $want in
    ok)
      if [ "$rc" -eq 0 ]; then built="$built$m "
      else echo "UNEXPECTED: $m should compile"; bad=1; fi ;;
    fail:*)
      case $rc:$out in
        0:*) echo "UNEXPECTED: $m should fail"; bad=1 ;;
        *"${want#fail:}"*) ;;
        *) echo "UNEXPECTED: $m failed without the expected \"${want#fail:}\""; bad=1 ;;
      esac ;;
  esac
done <<'EOF'
ModProbeE|fail:Not a definitional equality|
ModProbeA|ok|
ModProbeF|fail:Unknown identifier `secretA`|ModProbeA
ModProbeB|ok|ModProbeA
ModProbeC|fail:Unknown identifier `shownBody`|ModProbeB
ModProbeD|ok|ModProbeA
ModProbeG|ok|ModProbeA
ModProbeH|ok|ModProbeG
EOF
if [ "$bad" -eq 0 ]; then echo "run.sh: all probes ended as expected"
else echo "run.sh: some probes did not end as expected"; fi
exit "$bad"
