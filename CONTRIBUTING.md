# Contributing

## Source layout

```
src/CORALean/
  Global/          shared: array types, the scalar, index partitions, Mathlib
    Float/         the floating-point scalar, and models of it
    LinProg/       bounds on a linear objective, and what certifies them
      Float/       the same bound with a machine-representable value
  ContSet/         set representations, over whichever ambient type they suit
    ContSet/       the interface every representation instantiates
    InflatedContSet/  nominal part + error box, what a float representation adds
    Interval/
      Real/        Interval.lean (the type), Operations/ (one per operation),
                   Theorems/ (one per guarantee),
                   Instances.lean (the interface, instantiated),
                   API.lean (the whole directory, and nothing but imports)
      Float/       the same representation, rounded
    Zonotope/      Real/ and Float/, as above
    HPolytope/     polytopes by halfspaces: exact under intersection and preimage;
                   Real/ and Float/, the latter with an interval right-hand side
    VPolytope/     the same sets by vertices: exact under sum, image and hull;
                   Real/ and Float/, the latter paying rounding into an error box
    ConZonotope/   a zonotope whose coefficients an HPolytope cuts down;
                   Real/ and Float/, the latter splitting its rounding two ways
    Conversion/    one file per ordered pair, `<Source>_to_<Target>.lean`;
                   Real/ and Float/
  ContDynamics/    algorithms, written against the interfaces alone
    LinearSysDT/   discrete-time linear systems, and reachability
    NonlinearSys/  the representation and its trajectories; no reachability yet
    LinearSys/     continuous-time linear systems: the flow in closed form,
                   reachability at the sample times by sampling into
                   LinearSysDT, and an enclosure over a whole step
      MatExp/      enclosing e^{A dt}, which is what a step is taken against
```

A conversion goes in `Conversion/`, not in either representation: two
representations of equal standing cannot each import the other, so
`VPolytope → HPolytope` inside `VPolytope/` and the reverse inside `HPolytope/`
is a cycle Lean rejects. One file per ordered pair keeps a new pair to a file
rather than a directory, and keeps every representation independent of every
other. The exception is a conversion a representation needs for its *own*
operations, which has to sit below it — `VPolytope.ofInterval` stays in
`VPolytope/` because `VPolytope.and` is built from it.

A representation present in both arithmetic layers holds one directory per
layer, named for the namespace it declares; one present in a single layer stays
flat, and then only the namespace says which. The remaining directory names —
`ContSet`, `Interval`, `Operations` — are organizational and appear in no
namespace, so a path never contradicts a namespace. `ContSet` itself belongs to
neither layer and sits in namespace `CORALean`.

### The ambient type

`ContSet` is indexed by the ambient type, so a representation is written once and
instantiated wherever it makes sense: `Zonotope (Mat ℝ n m)` is CORA's
`matZonotope` and `Interval (Mat ℝ m n)` its `intervalMatrix`, neither needing a
development or a name of its own. Not indexed by a `Tensor` shape — `Mat` is
Mathlib's `Matrix`, which carries the ring structure the exponential needs and
which instance search does not identify with `Tensor ℝ [m, n]`.

An operation then generalizes as far as the structure it uses. `plus` and `map`
need only a module; an interval hull, a generator ranking and an entrywise bound
need `Entrywise`, which both `Vec` and `Mat` have; `reduce` and `mtimes` stay at
`Vec`, one ranking generators by coordinate and the other moving a dimension.

One class per operation — `Plus`, `LinComb`, `Reduce` — as CORA gives each
representation one method per operation. A representation instantiates what it
computes; an algorithm asks for what it calls, so `LinearSysDT.reach` wants
`Plus` and `Reduce` and runs at a representation with no `linComb` at all.

There is deliberately no class collecting them. A bundle would make every
representation owe every operation, so the one that cannot compute an operation
would have to invent it — which is what `HPolytope` would have had to do, and
what pushed `ConZonotope`'s `linComb` through its enclosing zonotope. A theorem
that does not call an operation says so with `omit`, and that line is worth
reading: it is the record of which interfaces the algorithm actually needs.

Each of these takes and returns the same ambient type, so each is a class over
one representation rather than a family indexed by dimension. `mtimes` is the
only operation that moves between ambient types, so it stays its own class
`Mtimes`, over a family, and an algorithm that travels between dimensions asks
for it on top.

### Notation

| | |
| --- | --- |
| `x ∈ s` | membership in what a representation denotes |
| `s₁ ⊞ s₂` | `plus`, and deliberately not `+`: it is only *outer*, so `construct (s₁ ⊞ s₂)` merely contains `construct s₁ + construct s₂` |
| `𝒵`, `ℐ` | the zonotope and interval-matrix families, for pinning `(S := 𝒵)` where the elaborator cannot read a family off one member |

Bundling the binders of a generic file into a `class abbrev` was tried and
reverted: each use adds an unfolding step to instance search, which produced
timeouts rather than slow proofs at the heartbeat limit of the time.

## Tooling

`.mcp.json` registers the [lean-lsp](https://github.com/oOo0oOo/lean-lsp-mcp)
MCP server, which gives an AI agent goal state, diagnostics, and Mathlib search
without a rebuild. It needs [`uv`](https://docs.astral.sh/uv/) on `PATH`; `uvx`
fetches the server itself.

Build once before first use, since the server starts `lake serve` and otherwise
builds from cold.

`.gitlab-ci.yml` rebuilds the project on every push to the default branch and on
every merge request, and fails on a warning as well as on an error. It caches
nothing: `lake exe cache get` fetches Mathlib's prebuilt oleans from Mathlib's
own CDN, which beats moving 7.6 GB of packages through GitLab's cache. The file
carries the measurements behind that choice.

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
exception, a Lean instance having no name to use.

`Operations` stays a single file where splitting would not pay — `LinearSysDT`
has one operation, and `Dyadic`'s are one-line compositions.

### `aux_`

What a file needs and nothing else uses carries the `aux_` prefix, as in CORA.
The test is mechanical: used outside its own file, or not.

### `API.lean`

Holds nothing but imports: a directory collects itself there, `Operations/`,
`Theorems/` and `Instances` included. It is the entry point *into* the library —
one import puts a whole representation in scope, which is what someone using
CORALean, or trying something out, wants.

Inside the project, a file imports the exact modules it names and never a
collector: `Theorems/PlusExact.lean` imports `Operations/Plus.lean`, not
`Operations/API.lean`. Importing a collector makes a file wait for everything in
that directory, and the build is bound by the longest such chain rather than by
the work — it was 37 files deep under the old rule and is 20 under this one, on
a machine with 16 cores that were idle either way.

A file still never imports its own directory's `API.lean`, which would be a
cycle.

`Global/API.lean` is the one file that does not collect its whole directory: it
leaves out `Global/Float/`, which every `Real` file would otherwise reach,
breaking the rule below that deleting `Float` leaves the specification standing.

An import cannot filter, so `Theorems/API.lean` re-exports the `aux_` lemmas
too. The prefix is the only thing marking them.

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

`Real` is the specification, `Float` the refinement, which obtains its soundness
guarantees by transitivity — so `Float` imports `Real`, never the reverse. A new
float operation pays its rounding into an interval error box via
`InflatedContSet`.

`𝕋` is the scalar a layer computes in — ℝ in `Real`, a machine scalar in `Float`.
`Global.Scalar` reads a matrix of it as a real one, which is how a guarantee
stated once covers both layers.

## Certificates, not algorithms

Several operations have no definition — a Minkowski sum of halfspace
descriptions, a bounding box, a conversion. What they have in common is one
question: how far does this set reach in direction `c`? For a polytope that is a
linear program, and `Global/LinProg` answers it once.

A `SupportBound S c` is a real number together with the fact that no point of
`S` exceeds it in direction `c`. It says nothing about where the number came
from. That is the point: a simplex implementation supplies the dual solution,
weak duality turns the dual solution into the proof, and the proof is what gets
carried — so an unverified solver stays outside the trusted base, and a wrong
dual solution yields no bound rather than a wrong one. Nothing here is
axiomatised and nothing is `sorry`.

Write a new operation of this kind as `ofBounds` over directions the caller
names, and let `Composition` do the work: a direction sees a sum as a sum of
extents, a union as the larger of two, an image as the direction pulled back,
a hull as no further than its points. Soundness never depends on the directions,
only precision does, so enumerating the true facets stays outside as an
optimisation.

`FloatBound` is the same object with a float value. Its composition rules are
these with `+` replaced by `addUp` and `max` by `maximum` — a bound only stays
sound by growing.

## Proofs

Write them explicitly. `maxHeartbeats` is 40000 in `lakefile.toml`, a fifth of
Lean's default, so a proof that starts searching fails rather than quietly
costing seconds. Override per declaration when justified — and only then, since
an override is meant to read as a deliberate cost.

Mathlib is imported only in `Global/Mathlib.lean`, one lemma group at a time. A
new lemma may mean a new import there.

### `aux_sum_univ_<op>`

A size-changing operation needs one of these, and it is not copy-paste that
could be factored out: `Fin.sum_univ_add` cannot rewrite a sum whose index type
reads `Fin (Z₁.plus Z₂).h` rather than `Fin (Z₁.h + Z₂.h)`, since unifying the
two is not type-correct at the elaborator's transparency. The restatement names
the operation, so it has to live with it; the proof is always
`Fin.sum_univ_add f`. Ascribe the binder in any statement that sums over an
operation's result, or the lemma will not match there either.

## Documentation

Every file opens with a module docstring saying what it is for and what is
non-obvious about it: where it departs from CORA or from Althoff's thesis, which
hypothesis is doing the work, which Lean detail a reader would otherwise trip
over. Not the file's role in the layout, which is this document's job, and not
what the code already says.

Keep every comment short and precise — one line where one will do — and state
how the code is now, not what it used to be or what was tried instead.

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
