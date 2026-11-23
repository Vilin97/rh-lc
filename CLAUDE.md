# Working in this repository

## Building

- **Never run `lake build`.** Build only with the custom driver, from the repository root:

  ```bash
  python3 scripts/cbuild.py -j 90
  ```

- The driver writes outputs to `.lake/build/lib/lean` and compiler errors to `.lake/cbuild/errs/<module>.log`.
- Lake does not recognize the driver's outputs, so a `lake build` would recompile the whole project.

## Compile as little as possible

Compiling Lean is the main cost of work in this repository.

- Read the code and the error, work out the fix, and batch your edits before compiling anything.
- When you must compile, do it as locally as you can: one declaration, then one file.
- Never run a full or multi-file build just to test an idea.
