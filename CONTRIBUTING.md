# Contributing

## File roles

Per representation, four kinds of file, and a file does only its own job:

| File | Holds |
| --- | --- |
| `API.lean` | the structure, `construct`, the operations |
| `Theorems.lean` | guarantees per operation, stated in full with proofs outsourced* |
| `Proofs/*.lean` | one proof each, plus the lemmas only it needs |
| `Proofs.lean` | just imports of the above for convenience |

*`Theorems` restates the type and delegates to the lemma of the same name in `Proofs`. 
The restatement is checked against the proved one, so the two cannot drift.

Naming convention follows the CORA repositoy: `plus`, `mtimes`, `reduce`, `interval`, ...

## The two layers

`Real` is the specification, `Float` the refinement which obtains soundness guarantees through transitivity. 
Thus, `Float` imports `Real`, never the reverse.
New float operations pay their rounding into an interval error box via `InflatedContSet`.

## Proofs

Write them explicitly. `maxHeartbeats` is 5000 in `lakefile.toml`, well under
Lean's default, so a proof that starts searching fails rather than quietly
costing seconds. Override per declaration when justified.

Mathlib is imported only in `Global/Mathlib.lean`, one lemma group at a time. A
new lemma may mean a new import there.

## Documentation

Every file opens with a module docstring saying what it is for and what is
non-obvious about it. Keep it, and all other comments, short and precise (ideally one line); 
State how the code is now — not what it used to be, or what was tried instead.

There are no per-directory READMEs. 
The module docstring of a directory's `API.lean` is its entry point.

## Author blocks

Content files carry a CORA-style block between the module docstring and the
code:

```lean
-- Authors:       Your Name
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---
```

Files that only collect or re-export do not: `Proofs.lean`, `Theorems.lean`, the
layer-level `API.lean` files, `Global/Mathlib.lean`, `CORALean.lean`.
