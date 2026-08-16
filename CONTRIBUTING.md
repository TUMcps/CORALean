# Contributing

## File roles

Per representation, four kinds of file, and a file does only its own job:

| File | Holds |
| --- | --- |
| `API.lean` | the structure, `construct`, the operations |
| `Theorems.lean` | one guarantee per operation, stated in full |
| `Proofs/*.lean` | one proof each, plus the lemmas only it needs |
| `Proofs.lean` | imports of the above, nothing else |

`Theorems` restates the type and delegates to the lemma of the same name in
`Proofs`. The restatement is checked against the proved one, so the two cannot
drift.

Names come from CORA: `plus`, `mtimes`, `reduce`, `interval`.

## The two layers

`Real` is the specification, `Float` the refinement. `Float` imports `Real`,
never the reverse.

A float operation does not prove soundness directly. It proves that it encloses
the exact operation (`plus_refines`, `mtimes_refines`, or a `_nominal` lemma),
and soundness follows by transitivity. Set-level reasoning — Minkowski sums,
images under a linear map, the sign of a coefficient — is written once, in
`Real`. If you find yourself repeating it in `Float`, the lemma belongs in
`Real`.

New float operations pay their rounding into the error box rather than into new
generators, via `InflatedContSet`. Generator count is what reachability costs.

## Proofs

Write them explicitly. `maxHeartbeats` is 5000 in `lakefile.toml`, well under
Lean's default, so a proof that starts searching fails rather than quietly
costing seconds. Override per declaration when justified.

Mathlib is imported only in `Global/Mathlib.lean`, one lemma group at a time. A
new lemma may mean a new import there.

## Documentation

Every file opens with a module docstring saying what it is for and what is
non-obvious about it. Keep it to a sentence or two per point; declaration
docstrings should fit on one line wherever the point does. State how the code is
now — not what it used to be, or what was tried instead.

There are no per-directory READMEs. The module docstring of a directory's
`API.lean` is its entry point.

Lines wrap at 100 characters, prose and code alike.

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

## Build

```
cd lean && lake exe cache get && lake build
```
