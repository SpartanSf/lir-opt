# opt.lua
The Lua IR optimizer

Includes several optimizations:

* `ube` - Unreachable Block Elimination
  Removes blocks of code that cannot be reached from the entry point, cleaning up dead code and reducing IR size.

* `cf` - Constant Folding
  Computes results of constant expressions at compile time (e.g., `2 + 3` -> `5`).

* `ms` - Math Simplification
  Simplifies mathematical operations (e.g., `x * 1` -> `x`, `x + 0` -> `x`).

* `lvp` - Local Value Numbering (LVN)
  Detects and eliminates redundant computations within a basic block.

* `ssad` - SSA Dead Code Elimination
  Removes assignments to registers that are never used.

* `lcp` - Local Copy Propagation
  Replaces registers that are simple copies of others with their source.

* `pep` - Peephole Optimization
  Performs small, localized instruction replacements and simplifications (e.g., folding `const` followed by `move`).

* `mb` - Merge Blocks
  Merges sequential blocks when possible.

* `rucu` - Remove Unused Constants and Upvalues
  Cleans up constants and upvalues that are no longer referenced.

* `-all` applies all available optimizations in a single pass.

The optimizer iterates multiple times until no further changes are detected.
