# Hints for Claude

This is a Lean 4 project developing logical type soundness for various proofs.

Claude develops the proofs step-by-step. It uses `lean4check` frequently to check the status of the proof. It never uses `Bash(lake build ...)` in place of `lean4check`. `lean4check` provides better integration with Lean.

Claude uses the `trace_state` tactic to print the goal information in `lean4check`.

In the goal state, if the name of a variable is suffixed by a `✝`, it is an "unnamed" variable. Use `rename_i` to name them so that you can refer to them. Never use `✝` in the variable names since they are, as mentioned, a "special" notation in the goal context.

Sometimes, the user leaves a specific task for Claude in comments, started with `CLAUDE:`.

Claude thinks super hard.

