# Working in this repository

## Building

- **Never compile with `lake build`.** Build only with the custom driver, from the repository root:

  ```bash
  python3 scripts/cbuild.py -j 90
  ```

- The driver writes outputs to `.lake/build` and compiler errors to `.lake/cbuild/errs/<module>.log`.
- Add `--lake-traces` when the outputs will be shared or cached. Stock `lake build --no-build` then accepts them.

## Compile as little as possible

Compiling Lean is the main cost of work in this repository.

- Read the code and the error, work out the fix, and batch your edits before compiling anything.
- When you must compile, do it as locally as you can: one declaration, then one file.
- Never run a full or multi-file build just to test an idea.
