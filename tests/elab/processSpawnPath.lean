/-!
Spawning a program given by an absolute path (the `posix_spawn` fast path on glibc): stdio
modes, environment set/unset/clear, `setsid`, and a missing program (reported by the child with
exit code 255, as with `fork` + `execvp`).
-/
open IO.Process

def sh (script : String) (env : Array (String × Option String) := #[]) (inheritEnv := true)
    (setsid := false) : IO Output :=
  output { cmd := "/bin/sh", args := #["-c", script], env, inheritEnv, setsid }

/-- info: (0, "out\n", "err\n") -/
#guard_msgs in #eval do
  let o ← sh "echo out; echo err >&2"
  return (o.exitCode, o.stdout, o.stderr)

/-- info: "set:1 unset:" -/
#guard_msgs in #eval do
  let o ← sh "printf 'set:%s unset:%s' \"$DF_A\" \"$HOME\"" (env := #[("DF_A", some "1"), ("HOME", none)])
  return o.stdout

/-- info: "only:x path:" -/
#guard_msgs in #eval do
  let o ← sh "printf 'only:%s path:%s' \"$DF_B\" \"$DF_C\"" (env := #[("DF_B", some "x")]) (inheritEnv := false)
  return o.stdout

/-- info: true -/
#guard_msgs in #eval do
  let o ← sh "ps -o sid= -p $$ | tr -d ' '; echo $$" (setsid := true)
  let ls := o.stdout.splitOn "\n"
  return ls[0]! == ls[1]!

/-- info: "piped\n" -/
#guard_msgs in #eval do
  let child ← spawn { cmd := "/usr/bin/head", args := #["-n1"], stdin := .piped, stdout := .piped }
  child.stdin.putStrLn "piped"
  child.stdin.flush
  discard child.wait
  child.stdout.readToEnd

/-- info: (0, "") -/
#guard_msgs in #eval do
  let child ← spawn { cmd := "/bin/sh", args := #["-c", "cat"], stdin := .null, stdout := .piped }
  let out ← child.stdout.readToEnd
  return (← child.wait, out)

/-- info: 255 -/
#guard_msgs in #eval do
  let o ← output { cmd := "/nonexistent/df-no-such-program" }
  return o.exitCode
