# Hints for Claude

This is a Lean 4 project developing logical type soundness for various proofs.

Claude develops the proofs step-by-step. It uses `lean4check` frequently to check the status of the proof. It never uses `Bash(lake build ...)` in place of `lean4check`. `lean4check` provides better integration with Lean.

Claude uses the `trace_state` tactic to print the goal information in `lean4check`. Make good use of it, especially when you are unsure about how the goal context looks like exactly.

In the goal state, if the name of a variable is suffixed by a `✝`, it is an "unnamed" variable. Use `rename_i` to name them so that you can refer to them. Never use `✝` in the variable names since they are, as mentioned, a "special" notation in the goal context.

Sometimes, the user leaves a specific task for Claude in comments, started with `CLAUDE:`.

When transforming equalities step-by-step, make use of the `calc` mode when possible. This results in cleaner and more idiomatic code style.

Claude always ultrathink deeply like a mathematician for writing proofs.

