# Agentic Proof Automation: A Case Study

This repo contains the case study mechanisation for agentic proof automation.

The module [CC](Semantic/CC.lean) mechanises semantic type soundness for System Capless.

## Setup

This project makes extensive use of Claude for proof writing.
See [CLAUDE.md](./CLAUDE.md) for the project-level instructions.
It assumes a MCP tool called `lean4check`, which can be found in [this Github repo](https://github.com/linyxus/lean4check).

To setup this MCP tool, run the following command:
```
claude mcp add lean4check -- uvx lean4check
```

This tiny MCP server provides only one tool `check`, which compiles a Lean 4 module and output all diagnostics with its context. Less is more!

