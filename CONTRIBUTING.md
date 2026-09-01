# Contributing

## Source layout

```
lean/src/CORALean/
  Global/          shared: array types, the scalar, index partitions, Mathlib
    Float/         the floating-point scalar, and models of it
  ContSet/         representations of a set of points
    ContSet/       the interface every representation instantiates
    InflatedContSet/  nominal part + error box, what a float representation adds
    Interval/
      Real/        Interval.lean (the type), Operations/ (one per operation),
                   Theorems/ (one per guarantee),
                   Instances.lean (the interface, instantiated),
                   API.lean (the whole directory, and nothing but imports)
      Float/       the same representation, rounded
    Zonotope/      Real/ and Float/, as above
  MatSet/          representations of a *set of matrices*, same interface
    IntervalMat/   what an enclosed matrix exponential needs
  ContDynamics/    algorithms, written against the interfaces alone
    LinearSysDT/   discrete-time linear systems, and reachability
    LinearSys/     continuous-time linear systems: the flow in closed form,
                   reachability at the sample times by sampling into
                   LinearSysDT, and an enclosure over a whole step
```

A representation present in both arithmetic layers holds one directory per
layer, named for the namespace it declares. One present in a single layer stays
flat, and then only the namespace says which: `InflatedContSet` is float-only,
`IntervalMat` and `ContDynamics` real-only.

The remaining directory names — `ContSet`, `Interval`, `Operations` — are
organizational and appear in no namespace. So a path never contradicts a
namespace, but a flat directory does leave the layer to the file itself.

`ContSet` itself belongs to neither layer — it denotes a set over ℝ whichever
scalar the representation computes in — and so sits in namespace `CORALean`.

The class is indexed by the ambient type, so `ContSet/` and `MatSet/` hold
instances of one interface and the directory only says which type a
representation denotes into: `Vec ℝ n` for the first, `Mat ℝ m n` for the
second. Not indexed by a `Tensor` shape — `Mat` is Mathlib's `Matrix`, which
carries the ring structure the exponential needs and which instance search does
not identify with `Tensor ℝ [m, n]`.

## Tooling

`.mcp.json` registers the [lean-lsp](https://github.com/oOo0oOo/lean-lsp-mcp)
MCP server, which gives an AI agent goal state, diagnostics, and Mathlib search
without a rebuild. It needs [`uv`](https://docs.astral.sh/uv/) on `PATH`; `uvx`
fetches the server itself.

The Lean project root is `lean/`, not the repository root, hence the
`--lean-project-path` flag. Build once before first use, since the server starts
`lake serve` and otherwise builds from cold.

## File roles

Per representation, four kinds of file, and a file does only its own job. Scalar
models and systems follow the same shape:

| File | Holds |
| --- | --- |
| `<Name>.lean` | the structure it is named for, and what it denotes: `construct`, `toReal`, `Trajectory` |
| `Operations/*.lean` | one operation each, as CORA gives it a file each |
| `Theorems/*.lean` | one guarantee each, stated and proved together |
| `Instances.lean` | the class instances, whose fields *are* the guarantees |

A file is named after what it declares, not after the role it plays:
`Zonotope/Zonotope.lean` and `Operations/Reduce.lean`, as in CORA's
`@zonotope/zonotope.m` and `@zonotope/reduce.m`. `Instances.lean` is the
exception, because a Lean instance has no name to use.

`Operations` stays a single file where splitting would not pay: `LinearSysDT`
has one operation, and `Dyadic`'s are one-line compositions of an exact step and
a rounding.

### `aux_`

What a file needs and nothing else uses carries the `aux_` prefix, as in CORA —
`aux_girardSplit`, `aux_plus_nominal`. Everything else is public, so the
distinction is visible at each use site rather than kept in a list somewhere.
The test is mechanical: used outside its own file, or not.

### `API.lean`

Holds nothing but imports: a directory collects itself there, `Operations/`,
`Theorems/` and `Instances` included. Two rules keep it acyclic and make it the
only name anything outside needs:

- inside a directory, a file imports its siblings by name —
  `Theorems/PlusExact.lean` imports `Operations.API`, never its own `API`;
- across directories, an import names an `API.lean` and nothing else, so reaching
  another representation's lemma never names the file it happens to sit in.

`Global/API.lean` is the one file that does not collect its whole directory: it
leaves out `Global/Float/`. Every `Real` file imports `Global.API`, so reaching
the float scalar through it would break the rule below that deleting `Float`
leaves the specification standing.

Note that an import cannot filter: `Theorems/API.lean` re-exports the `aux_`
lemmas too. The prefix is the only thing marking them, which is why it is a
naming rule and not a file boundary.

### Naming

Follows the CORA repository: `plus`, `mtimes`, `reduce`, `interval`, ...

A suffix says what a guarantee claims, and a file in `Theorems/` is named after
the theorem it states:

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

Files that only collect or re-export do not: every `API.lean`,
`Global/Mathlib.lean`, `CORALean.lean`.
