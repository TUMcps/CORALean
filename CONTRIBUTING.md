# Contributing

## Tooling

`.mcp.json` registers the [lean-lsp](https://github.com/oOo0oOo/lean-lsp-mcp)
MCP server, which gives an AI agent goal state, diagnostics, and Mathlib search
without a rebuild. It needs [`uv`](https://docs.astral.sh/uv/) on `PATH`; `uvx`
fetches the server itself.

The Lean project root is `lean/`, not the repository root, hence the
`--lean-project-path` flag. Build once before first use, since the server starts
`lake serve` and otherwise builds from cold.

## File roles

Per representation, six kinds of file plus `Helper/` where an operation needs it,
and a file does only its own job. Scalar models and systems follow the same shape:

| File | Holds |
| --- | --- |
| `Structure.lean` | the structure, and what it denotes: `construct`, `toReal`, `Trajectory` |
| `Helper/*.lean` | what one operation is built from, when `API` should not carry it |
| `API.lean` | the operations |
| `Theorems.lean` | guarantees per operation, stated in full with proofs outsourced* |
| `Proofs/*.lean` | one proof each, plus the lemmas only it needs |
| `Proofs/API.lean` | just imports of the above for convenience |
| `Instance.lean` | the class instances, whose fields *are* the guarantees |

A directory collects itself in its own `API.lean`, `Proofs/` and `Helper/` included,
so an import never names a file that sits beside the directory it belongs to.

*`Theorems` restates the type and delegates to the lemma of the same name in `Proofs`.
The restatement is checked against the proved one, so the two cannot drift.

Naming convention follows the CORA repository: `plus`, `mtimes`, `reduce`, `interval`, ...

A suffix says what a guarantee claims, and a file in `Proofs/` is named after the
theorem it proves:

| Suffix | Claim |
| --- | --- |
| `_outer` | the result contains the exact set |
| `_inner` | the result is contained in it |
| `_exact` | both, so the operation loses nothing |

`_outer` rather than `_sound`, since an inner approximation is sound too.
`_exact` only when equality holds for every input.

`_refines` measures against the real counterpart instead of the exact set, and
takes the direction too: `_outer_refines`. Composing the two gives the float
guarantee, the weaker direction winning.

## The two layers

`Real` is the specification, `Float` the refinement which obtains soundness guarantees through transitivity.
Thus, `Float` imports `Real`, never the reverse.
New float operations pay their rounding into an interval error box via `InflatedContSet`.

`𝕋` is the scalar a layer computes in — ℝ in `Real`, a machine scalar in `Float`.
`Global.Scalar` reads a matrix of it as a real one, which is how a guarantee
stated once covers both layers.

## Proofs

Write them explicitly. `maxHeartbeats` is 5000 in `lakefile.toml`, well under
Lean's default, so a proof that starts searching fails rather than quietly
costing seconds. Override per declaration when justified.

Mathlib is imported only in `Global/Mathlib.lean`, one lemma group at a time. A
new lemma may mean a new import there.

## Documentation

Every file opens with a brief module docstring saying what it is for and what is
non-obvious about it. Keep it, and all other comments, short and precise (ideally one line).
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

Files that only collect or re-export do not: `Theorems.lean`, every collecting
`API.lean`, `Global/Mathlib.lean`, `CORALean.lean`.
