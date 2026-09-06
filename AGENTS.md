# Agents

## Testing

- For compiler changes, run the full compiler, language, and standard library test suites before finishing.
- For bug fixes, add focused regression tests that fail on `HEAD` and pass with the proposed changes.
- When practical, compare and document the observed behavior on `HEAD` versus the changed code so the regression test validates the actual bug, not just the intended implementation.

## Commits

- Use Conventional Commits for commit messages.
- Format commit subjects as `type(scope): imperative summary`.
- Prefer scopes that match the touched subsystem, such as `codegen`, `compiler`, `mir`, `runtime`, or `std`.
- Example: `fix(codegen): skip library packages before link validation`.
