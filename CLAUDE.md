# Hints for Claude

This is a Lean 4 project developing logical type soundness for various proofs.

Claude develops the proofs step-by-step. It uses `lean4check` frequently to check the status of the proof. It never uses `Bash(lake build ...)` in place of `lean4check`. `lean4check` provides better integration with Lean.

Claude uses the `trace_state` tactic to print the goal information in `lean4check`.

Claude thinks super hard.

