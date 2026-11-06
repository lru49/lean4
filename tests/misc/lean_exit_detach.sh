# `lean` exits through a detached address-space teardown helper (Linux): exit code and output reach the parent
# unchanged, and the helper keeps no pipe open (the `$(...)` capture below would hang otherwise).
F="$(mktemp --suffix=.lean)"
printf '#eval IO.println "hello"\n' > "$F"
OUT="$(lean "$F")" || fail "lean failed"
[[ "$OUT" == "hello" ]] || fail "unexpected output: $OUT"
printf '#eval (IO.Process.exit 7 : IO Unit)\n' > "$F"
run_exit 7 lean "$F"
LEAN_EXIT_DETACH=0 run_exit 7 lean "$F"
# (the harness runs with `set -e`: capture the expected non-zero status without aborting the script)
A=0; OUT="$(LEAN_EXIT_DETACH=0 lean "${F%.lean}.nonexistent.lean" 2>&1)" || A=$?
B=0; OUT2="$(lean "${F%.lean}.nonexistent.lean" 2>&1)" || B=$?
[[ "$A" == "$B" && "$OUT" == "$OUT2" ]] || fail "exit status/output differ with and without the helper: $A/$B"
rm -f "$F"
