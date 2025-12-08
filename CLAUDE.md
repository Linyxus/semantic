# Hints for Claude

This is a Lean 4 project developing logical type soundness for various proofs.

Claude develops the proofs step-by-step. It uses `lean4check` frequently to check the status of the proof. It never uses `Bash(lake build ...)` in place of `lean4check`. `lean4check` provides better integration with Lean.

Claude uses the `trace_state` tactic to print the goal information in `lean4check`. Make good use of it, especially when you are unsure about how the goal context looks like exactly.

In the goal state, if the name of a variable is suffixed by a `✝`, it is an "unnamed" variable. Use `rename_i` to name them so that you can refer to them. Never use `✝` in the variable names since they are, as mentioned, a "special" notation in the goal context.

When using `rename_i`, unnamed variables are named from the bottom of the goal context. For instance, given a goal state:
```
a✝ : P1
b✝ : P2
c✝ : P3
d✝ : P4
e✝ : P5
```
Running `rename_i x1 x2 x3` renames the LAST THREE unnamed variables in the goal context, in the order they appear in the context. For example, this tactic results in:
```
a✝ : P1
b✝ : P2
x1 : P3
x2 : P4
x3 : P5
```
And you can use `_` for names you want to skip. So `rename_i x1 _ x3` will be:
```
a✝ : P1
b✝ : P2
x1 : P3
d✝ : P4
x3 : P5
```
Note that a prefix `_` NEVER make sense: `rename_i _ _ x3` is equivalent to just `rename_i x3`, since naming starts from the BOTTOM. However, a suffix `_` does make sense: `rename_i t _ _ _` transforms the goal state to:
```
a✝ : P1
t  : P2
c✝ : P3
d✝ : P4
e✝ : P5
```

Sometimes, the user leaves a specific task for Claude in comments, started with `CLAUDE:`.

When transforming equalities step-by-step, make use of the `calc` mode when possible. This results in cleaner and more idiomatic code style.

NEVER state an `axiom`. When something is to be assumed, always state a `theorem` and leave the proof as `sorry`.

Claude always ultrathink deeply like a mathematician for writing proofs.

