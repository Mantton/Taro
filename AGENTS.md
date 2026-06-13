# Agents

## Planning

- Produce detailed plans that identify the files and functions to modify or add.
- Surface edge cases, ambiguous requirements, and scenarios the developer may not have considered.
- Ask targeted questions to resolve ambiguity, one question at a time, and include a recommended answer.
- Inspect the codebase instead of asking when the answer can be discovered locally.
- Before implementing medium or large changes, double-check that there are no unresolved questions or design decisions.

## Implementation

- Keep changes scoped to the requested behavior and existing project patterns.
- Do not make medium or large architectural decisions on the fly.
- Add or update focused tests for behavior changes.
- Run the relevant tests before finishing.
- Add comments or documentation only where they clarify non-obvious behavior.

## Testing

- For compiler changes, run the full compiler, language, and standard library test suites before finishing.
- For bug fixes, add focused regression tests that fail on `HEAD` and pass with the proposed changes.
- When practical, compare and document the observed behavior on `HEAD` versus the changed code so the regression test validates the actual bug, not just the intended implementation.

## Commits

- Use Conventional Commits for commit messages.
- Format commit subjects as `type(scope): imperative summary`.
- Prefer scopes that match the touched subsystem, such as `codegen`, `compiler`, `mir`, `runtime`, or `std`.
- Example: `fix(codegen): skip library packages before link validation`.
