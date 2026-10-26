# Contributing

**How this code was written.** Most of it was written by AI agents (Claude) under
human direction and review. Lean's kernel checks every proof, so the review effort
goes into whether the statements and definitions match the papers and CORA, which
the kernel cannot judge.

## Source layout

```
src/CORALean/
  Global/          shared: array types, the scalar, index partitions, the model
                   every running cost is stated against, Mathlib
    Float/         the floating-point scalar, models of it, and the support
                   bound stored in it
    LinProg/       linear programming: duality, Farkas, the simplex solver
    SupportFunction/  bounds on a linear objective, and how they compose
  ContSet/         set representations, over whichever ambient type they suit
    ContSet/       the interfaces every representation instantiates, in
                   Interfaces.lean; ContSet.lean instantiates them at a plain
                   set and a matrix
    InflatedContSet/  nominal part + error box, what a float representation adds
    OptEmpty/      a representation or nothing, for an operation whose result
                   can be empty where the representation cannot say so
    EmptySet/      `∅` in a stated dimension, a set class of its own as in CORA
    Fullspace/     the whole space, the same way; neither carries a scalar, so
                   both are Real/ only
    Interval/
      Real/        Interval.lean (the type), Operations/ (one per operation),
                   Theorems/ (one per guarantee),
                   Counterexamples/ (what refutes a printed statement, and the
                   model of CORA's code it refutes),
                   Complexity/Space/Theorems/ (how large a result is, proved),
                   Complexity/Time/Operations/ (what running it costs, asserted)
                   and Complexity/Time/Theorems/ (what is proved of the costs),
                   Instances.lean (the interfaces, instantiated),
                   API.lean (the whole directory, and nothing but imports)
      Float/       the same representation, rounded
    Zonotope/      Real/ and Float/, as above
    HPolytope/     polytopes by halfspaces: exact under intersection and preimage;
                   Real/ and Float/, the latter carrying an error box
    VPolytope/     the same sets by vertices: exact under sum, image and hull;
                   Real/ and Float/, the latter paying rounding into an error box
    ConZonotope/   a zonotope whose coefficients an HPolytope cuts down;
                   Real/ and Float/, the latter splitting its rounding two ways
    PolyZonotope/  generators carrying monomials: not convex, and exact under
                   quadMap; Real/ and Float/
    ConPolyZono/   the same with polynomial constraints on the factors, which is
                   what makes intersection exact; Real/ and Float/
    ZonoBundle/    a family of zonotopes denoting their intersection, exactly;
                   Real/ and Float/
    Ellipsoid/     CORA's shape matrix `Q` and center `q`, the one representation whose
                   support function is closed form; Real/ and Float/
    SpectraShadow/ the projection of a spectrahedron: exact under sum, image and
                   product, the representation a semidefinite program lands in;
                   Real/ and Float/
    Capsule/       a segment thickened by a ball, for an obstacle rather than a
                   reachable set: Real/ and Float/, being closed under almost nothing
    StarSet/       the star set `{c + G α | α ∈ [l, u], α ∈ P}`, its predicate any representation
                   in coefficient space; at an `HPolytope`, CORA's `C α ≤ d`, the form a network
                   layer steps through, a bounded polytope exactly; Real/ and Float/, the
                   latter at CORA's predicate
    Taylm/         a polynomial over `[-1, 1]ⁿ` and a remainder interval, enclosing
                   a function rather than describing a set; Real/ and Float/
    Conversion/    what an ordered pair of representations builds, in `Operations/`, one
                   file per pair, `<Source>_to_<Target>.lean`, and what it guarantees, in
                   `Theorems/`, one theorem to a file; Real/ and Float/
  Specification/   what a computed set is checked against — a safe set or an
                   unsafe one — and why checking it on an outer approximation
                   answers for the exact set
  ContDynamics/    one directory per system class, written against the
                   interfaces alone; Interfaces.lean holds the classes every
                   system instantiates: ContDynamics (ContDynamicsDT), its
                   dimensions and what a run of it is, and Reach
    Reach/         what goes with the reachability class: how a reach operation
                   takes its arguments, CORA's `params` (the problem) and
                   `options` (the algorithm), as two structures, and checking a
                   specification on what it returns
    LinearSysDT/   discrete-time linear systems, and reachability
    LinearSys/     continuous-time linear systems: the flow in closed form,
                   reachability at the sample times by sampling into
                   LinearSysDT, and an enclosure over a whole step
      MatExp/      enclosing e^{A dt}, which is what a step is taken against
    NonlinearSys/  conservative linearization, which hands a confined run to
                   LinearSys, and re-linearization, which iterates that with a
                   fresh certificate; NonlinearSysDT/ is the discrete case
    LinParamSys/   a set-valued system matrix: one continuous-time step at an
                   interval matrix, and the sampled case in LinParamSysDT/;
                   NonlinParamSys/ is the nonlinear class with uncertain
                   parameters, reached with the parameter as extra states
    NonlinDASys/   ẋ = f(x,y,u), 0 = g(x,y,u): index 1, reached through a
                   reduced model that eliminates y, supplied as data
    NeurNetContrSys/  a plant closed around a network, one class over every
                   ContDynamics plant as CORA's: each control period is reached as the
                   extended system [x; u], u̇ = 0, from the state set times
                   what NN encloses; NeurNetContrSysDT/ steps any
                   ContDynamicsDT plant
    OutputEq/      y = C x + D u, kept out of the system classes so that it
                   applies to all of them
  DiscrDynamics/   CORA's discrDynamics, written over ℝ: GridPartition/ cuts a box
                   into cells numbered from 1 and says which cells a set meets;
                   MarkovChain/ holds the transition probabilities between them
  HybridDynamics/  locations, transitions and the automaton; a run alternates
                   flowing inside a location with jumping between them
  NN/              neural network verification: propagating an input set through
                   a graph of layers, and checking the result, written once over
                   the scalar; NeuralNetwork.lean (the class), Definitions/ (what
                   a network means), Operations/, Theorems/ and Theorems/Real/
    Layers/        the standard layers, Layer.lean their class, laid out the
                   same way; an elementwise activation is a `Relaxation` and
                   nothing else, softmax the exception, its outputs sharing a
                   denominator
    Graph/         graph neural networks, over ℝ only so far
  Examples/        one worked example per component, proved and never run
    Demo/          the one executable, and the only place anything here is
                   evaluated rather than proved
```

A conversion goes in `Conversion/`, not in either representation: two representations of equal
standing cannot each import the other, so `VPolytope → HPolytope` inside `VPolytope/` and the
reverse inside `HPolytope/` is a cycle Lean rejects. The layout is a representation's: `Real/`
and `Float/` each hold `Operations/`, `Theorems/`, `Definitions/`, `Instances.lean` and
`API.lean`, and nothing else.

What a pair builds — `Zonotope.polyZonotope`, with the `aux_` definitions only it needs — is the
file `Operations/<Source>_to_<Target>.lean`. The ordered pair is the unit there, so that file may
declare several definitions (a conversion and its variants), and a pair that builds one small thing
is a section of `Operations/Basic.lean`, as anywhere; a pair with variants stays a file, a section
being one declaration. Every file keeps every representation independent of every other. What the
pair guarantees is in `Theorems/`, one theorem to a file, as for a representation, a file named for
its theorem — `Zonotope.interval_contains` is `Theorems/ZonotopeIntervalContains.lean`, the source
in the name because no representation's directory supplies it — or a section of `Theorems/Basic.lean`
where it is small. The declaration is named for the target, as in CORA, where `interval(zonotope)` is
how a zonotope becomes a box. `Real/` holds every ordered pair of the nine representations its own
collector names — 72 pairs — and `Capsule_to_Interval` and the `Taylm` pairs besides; `Float/`
holds the pairs written so far.

Two classes belong to no pair but stand where one would: `IntervalOuter` and `OfInterval` are the
pairs whose other side is a variable, for an algorithm that must reach a box, or come back from one,
without naming what it is propagating. The class is in `Definitions/`, and the instances are in
`Instances.lean`, not beside it: each field is the guarantee of a conversion, which a definition file
does not import. Only the representations that can do it without certificates instantiate them,
which is the same rule as everywhere else.

An operation may be *implemented* by conversion — `VPolytope.intersection` goes
out to halfspaces, where intersection is free, and comes back — and then imports
these files by exact path. That is a dependency, not a cycle: the conversion imports
the representation's own files, never its `API.lean`.

A representation holds one directory per arithmetic layer, named for the
namespace it declares, and keeps it when only one layer is written: `SpectraShadow`
and `Capsule` each hold a `Real/` and a `Float/`, and a representation with only
the first would still hold the folder. That split is permanent, and it is the only
one: the scalar is a folder only where the data of a type differs by layer, which is
exactly `ContSet/`'s representations — a float zonotope stores an error box a
real one has no use for. Everywhere else an object is written once over the
scalar `𝕋`, ℝ among its instances, and no `Real/` or `Float/` folder appears:
`Operations/` holds the algorithms, generic over `𝕋`; `Definitions/` holds what
an object means — its types, the propositions and sets its guarantees are
stated in, and the exact objects only ℝ has, built from `Real.exp` or by choice,
which are free to be `noncomputable`; `Theorems/` holds the statements that do
not fix the scalar, and `Theorems/Real/` those only ℝ can state — the
per-statement version of a representation's whole `<Rep>/Real/Theorems/`.
`Global/Float/` is the scalar interface itself, and the one other `Float/`.

A directory holding any of `Operations/`, `Theorems/` or `Definitions/` is a
*class root*: beside them it holds its class file, `Interfaces.lean`, `Instances.lean` and
`API.lean`, and nothing else; `ContSet/Conversion/Real/` and `Float/` are class roots with no class
file. A `Definitions/` file declares types, `abbrev`s,
propositions, sets and `noncomputable` specifications; a computable `def`
returning data is an algorithm, and belongs in `Operations/`, as does any `def`
returning an `Option` — a search that can fail — and a theorem belongs in
`Theorems/`. All of this is checked, and the class roots not yet sorted are a
named list in the script, which only shrinks. Two things no script can see are
review items: whether a statement in `Theorems/` secretly holds only at ℝ, and
whether one in `Theorems/Real/` really needs ℝ.

### Interfaces

A `class` is an interface, and it is declared in a file named `Interfaces.lean`, as its
instances sit in `Instances.lean`: `ContSet/ContSet/Interfaces.lean` holds every class a set
representation instantiates, `ContDynamics/Interfaces.lean` every class a system does
(`ContDynamics`, `ContDynamicsDT`, `Reach`). So what a directory offers is one file to read, and
what a representation or a system provides is the other. A generic algorithm or theorem is
written over the interface alone — the closed loops in `NeurNetContrSys/` are over any
`ContDynamics` — and a concrete one at the instance. `check-conventions.sh` refuses a `class`
anywhere else. The base classes sit in `Global/Interfaces.lean` and `Global/Float/Interfaces.lean`,
below every other interface; the ones whose law needs what the guarded
`ContSet/ContSet/Interfaces.lean` keeps out of its closure sit in the `Interfaces.lean` of the
directory that owns them (`ContSet/ContSet/Definitions/`, `VPolytope/Real/`, `Conversion/`).

The remaining directory names — `ContSet`, `Interval`, `Operations` — are
organizational and appear in no namespace, so a path never contradicts a
namespace; a `Theorems/Real/` file outside `ContSet/` keeps the namespace of the
object it states a fact of. `ContSet` itself belongs to neither layer and sits
in namespace `CORALean`.

### Which layer a declaration belongs to

`ContSet` is not a special case. A declaration sits in `CORALean.Real` or
`CORALean.Float` when it *names an arithmetic*: a representation that stores
numbers of one kind, an operation computed in one kind, or a class whose two
layers are two different classes, as `Real.OfInterval` and `Float.OfInterval`
are. A declaration parametric in the representation, whose only ℝ is the
ambient space both layers denote into, belongs to `CORALean`: the system classes
in `ContDynamics`, the automaton in `HybridDynamics`, and `Layer`,
`NeuralNetwork` and the refinement framework in `NN`. `Layer` stores
`enclose : S n → S m` and nothing real — the exact function it refines lives in
a `Prop` — which is what lets a float network hold one. The standard layers that
*build* a `Layer` are written once, `Layer.linear` against `Mat 𝕋` in `CORALean`:
at `𝕋 := ℝ` every rounding is the exact operation, so the exact layer is the same
definition. Only what ℝ alone has — the exact sigmoid relaxation, an exact
polynomial fit — sits in `CORALean.Real`, under `Definitions/`.

A Lean namespace cannot be split. `sys.reach` resolves to
`CORALean.LinearSysDT.reach` and looks nowhere else, so a type takes its whole
namespace with it. Where one of its theorems is then about a particular
representation — `LinearSysDT.reach_order_le` at a zonotope,
`LinearSys.timeInterval` at the exact interval matrices — the representation
is named with its layer, `Real.Zonotope`, rather than left to the enclosing
namespace to supply; a file that needs the scoped family notation `𝒵` or `ℐ`
says `open CORALean.Real` and that line is the record of which layer it works at.

Systems are not split by layer the way sets are. In a system namespace the
plain name is the algorithm as the paper describes it, generic over the set
family and used by the `Reach` class: `LinearSys.reach`. Its sound
rounded-arithmetic implementation is the `Float` twin, `LinearSys.reachFloat`,
and the true reachable set is `LinearSys.reachExact`, which is never an
algorithm. `Exact` and `Real` are not variant suffixes, and a top-level type
takes the `Float.` namespace (`Float.Zonotope`), never a `Float` suffix; the
suffix is for twins nested in a system namespace, as `LinearSys.AutoStateFloat`.

A definition that denotes the *true* set, a `Set` the semantics defines by trajectories and no
algorithm computes, ends in `Exact`, whatever it is the set of: `LinearSys.reachSetExact`,
`LinearSys.timeIntervalReachSetExact`, `LinearSysDT.backReachSetExistsExact`,
`NonlinearSys.robustReachSetExact`, `HybridAutomaton.reachSetExact`. A computed set is a
representation named by its algorithm, never a bare `Set`. `check-conventions.sh` runs
`scripts/check-exact-names.py`, which rejects a `Set`-valued definition in a `Definitions/`
directory of `ContDynamics/` or `HybridDynamics/` whose name says reach set, output, state,
window or locations and does not end in `Exact`.

### A component is its own representation's

A representation that stores a set of another representation stores that set and reuses its
operations (#174): `ConZonotope` stores an `HPolytope`, `ConPolyZono` a `PolyLevelSet`, `StarSet` a
predicate (an `HPolytope` at CORA's form), `ZonoBundle` and `Zoo` their members, denoted through
`SetIntersection`. Whatever an operation does to the component is one of the component's
operations, with its theorem, and an operation the representation needs but the component lacks is
added to the component, general and with its own exactness or membership theorem, rather than
written row by row where it is used: the union's lower rows are `PolyLevelSet.cartProd`, `padVars`
and `switch`, the convex hull's copies `copies` beside `linear`, `getSubset`'s substitution
`PolyLevelSet.getSubset`, `reduceCon`'s elimination `eliminate`, and the float merge
`PolyLevelSet.compact`; a constrained zonotope's `compact` is `HPolytope.dropTrivialEqs` and
`comap` (float: `selectCols` and `dropZeros`), `keepRows` is `toIneqs`, `relax` and `comap`, the
float `reduceLiftBy` is `keepCols`, `dropEqs`, `padLeft`, `stackRows` and `eqsWithin`, `rescale`
is `rescaleCols`, and `zeroFeasible`, `interiorCert` and `interiorMargin` are `containsOrigin`,
`ineqsContainBall` and `ineqMargin`; a ReLU step on a star set builds its predicate with
`HPolytope.lift_` and `intersection` of `ineqs` (float: `stackRows`), and `absorbRounding` with
`lift_`; the intersection's agreement rows and the union's selector rows of a constrained
polynomial zonotope are `PolyLevelSet.andRows`.
`check-conventions.sh` runs `scripts/check-component-reuse.py`, whose per-representation table
says what counts as doing the component's work by hand: under `ContSet/ConPolyZono/`, a definition
returning a matrix, an exponent matrix or a vector indexed by the constraint's rows or monomials,
or named after a constraint field (`…A`, `…B`, `…R`); under `ContSet/ConZonotope/`, one that reads
the polytope's rows (`P.A`, `P.b`, `P.Ae`, `P.be`, the slacks) or builds an `HPolytope` field by
field; and under `ContSet/StarSet/` and the star-set files of `NN/Layers/`, one that reads the
polytope predicate's rows (`pred.A`, `pred.b`, …) or builds an `HPolytope` field by field. `Counterexamples/` model
CORA's code as written and are not read. What is not the
component's work says so in its docstring, in one sentence `Not the constraint's work (<kind>):
<reason>` (`polytope's` or `predicate's` for the others), with `<kind>` one of `generators` (the
generator block), `data` (data of one construction), `conversion`, `certificate` or `proposal`
(rows read as numbers for a solver); there is no list.

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
would have to invent it — which is what `Capsule` would have had to do for a
Minkowski sum, two capsules' sum being no capsule. A theorem
that does not call an operation says so with `omit`, and that line is worth
reading: it is the record of which interfaces the algorithm actually needs.

Each of these takes and returns the same ambient type, so each is a class over
one representation rather than a family indexed by dimension. `mtimes` is the
only operation that moves between ambient types, so it stays its own class
`Mtimes`, over a family, and an algorithm that travels between dimensions asks
for it on top.

### Bounds of one quantity

Two bounds of one quantity are an `Interval` (`Interval ℝ`, `Interval 𝕋`, a box
`Interval (Vec ℝ n)`), read through `inf` and `sup`, not a pair `ℝ × ℝ` read with `.1`/`.2`, nor two
sibling fields `…Inf`/`…Sup` or `lo…`/`hi…`. A pair is fine where it makes sense: a product domain,
a point, values returned together. This is a recommendation, not a checked rule.

A pair of two different quantities is not read with `.1`/`.2` either. Where it is a domain
concept, it is a small structure with the paper's or CORA's names for its fields (`LinearSys.StepSets`
with `Rtp` and `Rti`, `NonlinearSys.TunedStep` with `step` and `gain`); where a structure would be
overkill, such as the two halves of a split, it is read through `.fst` and `.snd`.

### Notation

| | |
| --- | --- |
| `x ∈ s` | membership in what a representation denotes |
| `s₁ ⊞ s₂` | `plus`, and deliberately not `+`: it is only *outer*, so `construct (s₁ ⊞ s₂)` merely contains `construct s₁ + construct s₂` |
| `𝒵`, `ℐ`, `𝕄𝒵`, `ℐ𝒱`, `𝒫𝒵`, `𝒵ℬ`, `𝒱𝒫`, … | the zonotope and interval-matrix families, for pinning `(S := 𝒵)` where the elaborator cannot read a family off one member |
| `𝒵[𝕋]`, `ℐ[𝕋]`, … | the same families in the float layer, scoped in `CORALean.Float`; the scalar is an argument because a notation cannot capture a section variable such as `𝕋` |
| `𝒮` | the family of sets of real vectors, `fun n => Set (Vec ℝ n)`, in `Global/Interfaces.lean`, the lowest file with ℝ in scope |

A family is written with its notation, never as `fun k => Zonotope (Vec 𝕋 k)`;
`check-conventions.sh` rejects the long form outside the notation definitions.
The exact layer's notations are scoped in `CORALean.Real` (`open CORALean.Real`),
the float layer's in `CORALean.Float`, and both are defined next to the instances
of the representation, in its `Instances.lean`.

Bundling the binders of a generic file into a `class abbrev` was tried and
reverted: each use adds an unfolding step to instance search, which produced
timeouts rather than slow proofs at the heartbeat limit of the time.

## What is left

Open work is one [issue](https://gitlab.lrz.de/cps/CORALean/-/issues) per task,
labelled by area: `whole-repository`, `representations`, `dynamics`, `hybrid`,
`neural-networks`, `float-scalar`, `infrastructure`. Close them from the merge
request that does the work.

There is no roadmap file. What is *done* is the code and its docstrings, which
say what each file is for and where it departs from CORA or from the paper it
cites; a second account of that in prose only drifts from it.

## Landing work

Nothing is pushed to `main`. Every change — a new representation, a CI fix, a
one-line typo — reaches it through a merge request, so that what landed and why
is reviewable after the fact rather than reconstructible from a commit message.

```
git switch -c <topic>
git push -u origin <topic> -o merge_request.create \
  -o merge_request.target=main \
  -o merge_request.title="..." -o merge_request.description="..."
```

Pass the description. Without it GitLab fills one in from the body of the
branch's *first* commit, which describes an early step rather than the change,
and drags the commit trailers in with it. Push options reject newlines, so a
multi-paragraph description is either folded with `<br>` or, better, passed as
a file to `scripts/gl.py mr new`.

Merge requests are squashed on merge: a branch lands as one commit, and the
merge request keeps the history of how it got there. Merge through GitLab rather
than locally — a local `git merge --squash` produces content GitLab cannot match
to the branch, so the merge request ends up *closed* rather than *merged* and
its review is lost.

`.githooks/pre-push` refuses a direct push to `main`, and the protected-branch
setting on the server is what enforces it for a clone that has not run the
`core.hooksPath` line below.

## Tooling

`.mcp.json` registers the [lean-lsp](https://github.com/oOo0oOo/lean-lsp-mcp)
MCP server, which gives an AI agent goal state, diagnostics, and Mathlib search
without a rebuild. It needs [`uv`](https://docs.astral.sh/uv/) on `PATH`; `uvx`
fetches the server itself.

Build once before first use, since the server starts `lake serve` and otherwise
builds from cold.

`scripts/check-conventions.sh` checks the conventions on this page that the
compiler cannot: that an `aux_` name is used only in the file that declares it (or in
that algorithm's satellite theorem files, #227),
that an `API.lean` holds nothing but imports, that it collects its whole
directory unless its own docstring says which sibling it deliberately leaves
out, that no file imports its own directory's collector, that no `Real` file of
a representation reaches into `Float`, that a file under a representation's
`Real/` or any `Float/` declares the namespace its directory claims, that a class
root holds only its class file, `Interfaces.lean`, `Instances.lean` and `API.lean`, that a
`class` is declared only in an `Interfaces.lean`, that a
`Definitions/` file declares only meanings, that no `Real/` or `Float/` folder
sits outside `ContSet/` but a `Theorems/Real/` and `Global/Float/`, that a float
type is named as its exact twin, the layer being the namespace — no `GZonotope`,
no `StarSetFloat`, no abbreviation of a representation at `Vec` — that every
file carries a module docstring and
— unless it is a collector — a well-formed author block one line under it, that
every file outside `Examples/` and the short list of exceptions is a `module`
with its header at fixed lines (see "The module header"), that
nothing is `sorry` or a search tactic, that nothing outside the three files
named in the script is an `axiom` — the second holding `nearestUnsound` alone
and imported from nowhere outside `Examples/Bench/`, the third holding
`trustedFlint` alone — that every `maxHeartbeats` bump
carries a reason, that a `def` under `Complexity/Time/` is named for the cost it asserts and is
not `0`,
that every `[N]` cited resolves, that the comment lengths and the comment
density above are respected, that every module is reachable from one of the
target roots, so a file written but never collected is caught rather than
silently left out of the build, that a declaration of at most five code lines
is a section of its directory's `Basic.lean` and every section is well formed
(through `scripts/check-basic-bundles.py`; see "Small declarations"), that a theorem file
defines nothing ("A theorem file defines nothing"), that a float definition is not the exact
operation at `nominal` under a second name (`scripts/check-float-wrappers.py`; "Float
definitions earn their name"), that a definition citing a paper's algorithm carries its steps
(`scripts/check-algorithm-steps.py`; "Algorithms read like the paper"), that a long subterm
is not spelled out three times in one declaration (`scripts/check-repeated-subterms.py`;
"Name what repeats"), that a discrete-time class (`<X>DT`) has the fields of its continuous twin
`<X>` (`scripts/check-dt-twins.py`; the sampling time `dt` is the one field a discrete-time class
has and its twin has not), that a public theorem that exactly one other file reads is
that file's `aux_` lemma unless something outward-facing names it
(`scripts/check-single-use.py`; "A theorem used once is a lemma of its user"), and that
`noncomputable` stays where it is legitimate — see below.

**Principle.** Keep `noncomputable` to a minimum: a definition should compute wherever it can;
where the real version cannot, there should at least be a float variant that does.

**Rule** (`scripts/check-noncomputable.py`, no list). A `noncomputable` declaration is allowed if it
is in a real layer (a file under a `Real/` folder, or a declaration that works over ℝ rather than
the float scalar `𝕋`: its text mentions ℝ, or the file's `variable` lines do, and `𝕋` is at most
the index of a system, never the type of a value), or its type is a `Set`, a `Prop` or ℝ-valued,
or its docstring says why it cannot compute (a choice, an integral, an infimum, a classical
decision, `Noncomputable: …`). In the float layer, a `Float/` folder (its `Theorems/` files state
things about floats and never run) or a declaration whose result is a value of `𝕋`, it is never
allowed: the float layer exists to run. `noncomputable section` is refused outright.

Every limit it applies is a named variable at the top of the script, set from
what the tree actually contains, so raising one is a decision rather than a
drift. Every message says what to do, not only what is wrong.

It is text only: no Lean, no build, no network — which is why it runs on every
commit rather than on request. Over the whole tree it takes about fifteen
seconds on Linux (several times that in Git Bash on Windows); the hook does not
pay that for a commit that only edits existing Lean files. `scripts/precommit-scope.py`
compares the index with `HEAD`, and a commit that leaves every file's imports,
namespaces, type declarations and `noncomputable` lines as they were runs the
per-file rules on the changed files alone (`check-conventions.sh --staged`,
well under a second). Anything that could change a rule reading several files
(a file added, deleted or renamed, one of those lines, `scripts/`, `lakefile.toml`,
the CI file) runs the whole tree, and `check-references.py` runs when a commit
touches anything outside `src/` or what that check reads of a Lean file. The hook
checks the index, not the working tree: when the two differ, the whole-tree runs
use a checkout of the index in a temporary directory. CI always runs the whole
tree, so a commit that bypasses the hook, or that the scope wrongly called small,
fails there. The Python scripts are started through `scripts/find-python.sh`, which
takes the first of `python3`, `python`, `py -3` that really runs a program (on
Windows `python3` is by default a Store stub that runs nothing) and stops with a
message when none does, and sets `PYTHONUTF8=1` so that reading the sources and printing `ℝ`
works under Windows' code page; a script in `scripts/` also passes `encoding="utf-8"` to every
`read_text`, `write_text` and `open` (binary modes excepted), which `check-conventions.sh` checks.
Setting a clone up means

```
git config core.hooksPath .githooks
```

That line is required, not a convenience: git cannot ship an enabled hook in a
repository, so this is the one setup step. CI runs the same script as its own
job, so a commit that bypasses the hook fails there instead.

The parsing is deliberately shallow — comments are stripped by a two-character
scanner and declarations are matched at the start of a line — which is what
keeps it fast and dependency-free. It reports; it never rewrites.

`scripts/check-demo.sh` runs the demo and diffs what it prints against
`scripts/demo-expected.txt`. It is the only check here that measures
*precision*: every theorem in this repository is an enclosure, and an enclosure
the size of the state space satisfies all of them, so a widening is invisible to
the compiler and visible in that file. It needs a built tree, which is why it is
not on the pre-commit hook.

`scripts/check-axioms.sh` asks Lean, through `collectAxioms` on the built tree,
whether any library declaration rests on `nearestUnsound`, the bench's false
round-to-nearest axiom: the headline guarantees by name, every declaration of
every module outside `Examples/Bench/` by sweep, and two deliberately tainted
copies of `reachFloat_outer` as the positive control. It runs the same sweep
for `trustedFlint`, the optional FLINT backend's axiom, over the whole tree
outside `Global/Float/Instances/Flint/` and `Examples/BenchFlint.lean`, with
`reachFloat_outer` at `Flint 53` as that sweep's positive control. It also
asserts that these and `trustedHardware` are the only three axioms CORALean
declares. It needs a built tree too, and runs beside `check-demo.sh` in CI's
build job.

`scripts/check-references.py` checks `references/` against the tree: that every page has
one well-formed BibTeX entry and every docstring entry equals its rendering (below), that every
paper cited has a page, that every link on a page resolves and lands on a file
that really cites that paper, that every result cited anywhere is a row, that a
row deferring to an earlier paper names a row that is really on that paper's
page and does not defer in a circle, that the README's counts are the counts,
that a paper's findings are listed where the index says they are, that every row's `Class` cell is one of the allowed values and gives a reason when it is not `correct`, that a `correct` row's note does not say the Lean theorem is other than the printed one (unless an `**As printed:**` marker says why the printed statement follows; see [references/README.md](references/README.md#the-class-column)), that a `—` row's note reads `— partial: <declarations that exist, linked>; missing: <what is left>` and its links resolve, that a complexity statement sits in a row of its own (see [references/README.md](references/README.md#the-class-column)), and that `experiments/paper/formalization-stats.json` is what `scripts/formalization-stats.py` writes from the tables (rerun it after a row changes). A coverage table is a claim about where
a theorem lives, which is the kind of prose that rots quietly; this is what
stops it. It runs beside the conventions, on the same hook and the same CI job.

### The BibTeX entry of a page, and the line every docstring writes

Every `references/<year>/*.md` page carries exactly one fenced `bibtex` block under its heading,
the page's only bibliographic record (#265):

````
```bibtex
@inproceedings{althoff2012avoiding,
  author = {Althoff, M. and Krogh, B. H.},
  title = {Avoiding Geometric Intersection Operations in Reachability Analysis of Hybrid Systems},
  booktitle = {Proceedings of the 15th ACM international conference on Hybrid Systems: Computation and Control},
  year = {2012}
}
```
````

The fields are `author` (`Last, F. M.` joined by ` and `), `title`, `journal` or `booktitle`
(`publisher` too in an `@incollection`) and `year`, in that order, and no others: no volume,
pages, DOI, note or URL. The type is `article`, `inproceedings` or `incollection`. The key is
the one the paper cites. Non-ASCII letters are written as such (`Černý`); `scripts/refentry.py`
turns them into LaTeX commands for the `.bib`. Braces protect a capital (`{Minkowski}`) and are
dropped wherever the entry is printed. The venue is the publication's own name for it: the
journal, the proceedings title as the publisher's DOI record gives it, `arXiv preprint
arXiv:<id>` for a preprint. What the publisher, DOI page, dblp or arXiv does not confirm is
left blank (`journal = {}`), never filled from memory or a secondary source. The link to the
exact version read (`arxiv.org/pdf/…v3`) stays in the page's `**Source:**` line, below the
entry, and is not part of it. A key that is already an entry of the paper's own `references.bib`
adds the line `**In the paper's bibliography.**` under the block; every other page with a
`false` or `fixed` row is written to `experiments/paper/latex/appendix-errors.bib` by
`scripts/formalization-stats.py`, which nobody edits.

The line every `## References` entry of a module docstring under that page writes is the
rendering of the entry, in one format:

```
* [1] <authors>. "<Title>". <Venue>, <year>.
```

`<authors>` is `A. Name`, `A. Name and B. Name` or `A. Name, B. Name and C. Name`: the initials
first, the names in the order of the entry, the last two joined by `and`, no Oxford comma.
`<Title>` and `<Venue>` are the entry's `title` and `journal`/`booktitle` without braces; a blank
venue drops its comma. The line is wrapped at 100 characters with a six-space hanging indent.
`python3 scripts/render-references.py` rewrites every entry that names a page (found by its
quoted title) and `check-references.py` renders the same line from the entry and fails on any
entry that differs, on a page without exactly one well-formed entry, and on a repeated key. An
entry that begins with a CORA file in backticks, `None: <reason>`, and the stamps are untouched.
Correct a reference on the page, run the generator, and nothing else needs a hand.

Nobody types a count. After a row changes, `python3 scripts/check-references.py
--fix` writes the counts it computed into the README's cells, and re-points a
declaration link whose file no longer declares the name (a declaration moved
into or out of a `Basic.lean`). Everything else it finds, it only reports.

`scripts/gl.py` is the GitLab client: issues, merge requests and pipelines from
the command line, so that reading an issue or leaving a comment is not a
hand-rolled `curl`. The token is never an argument and never in the tree. It is
read from `$CORALEAN_GITLAB_TOKEN`, then `$GITLAB_TOKEN`, then
`~/.config/coralean/gl.token`, so every clone, worktree and agent on a machine
reaches the API the same way with nothing to pass along. `git push` needs none
of it — the credential helper answers for that.

```
python scripts/gl.py issue show 11
python scripts/gl.py mr new <branch> "<title>" desc.md
python scripts/gl.py mr merge 42
```

It takes a merge-request description as a *file*, which is the one thing the
push options above cannot do, and it comments before it closes anything, since
an issue or a merge request closed without a reason leaves no record of one.

`.gitlab-ci.yml` runs the conventions script as its own job, and rebuilds the
project on every push to the default branch and on every merge request, failing
on a warning as well as on an error, then runs the demo check in the same job.
It caches
nothing: `lake exe cache get` fetches Mathlib's prebuilt oleans from Mathlib's
own CDN, which beats moving 7.6 GB of packages through GitLab's cache. The file
carries the measurements behind that choice, and behind keeping the demo check
out of a job of its own — with no cache a second job rebuilds everything.

## Targets

Eight, all named in `lakefile.toml`, and `check-conventions.sh` walks the import
graph from each of their roots, so a new one belongs in both files.

`CORALean` is the development. `Examples` is the worked examples, built
alongside the library rather than inside it, so the library carries no use sites
of its own. `Demo` lives under `Examples/` and runs `LinearSysDT.reach` and
`NeuralNetwork.enclose` at `Dyadic`, printing what comes out — the definitions
the theorems are about, not copies of them.

### An example and the demo are not the same thing

Both are use sites and neither is in the library, which is why they sit
together; what they catch is different, and each is blind to the other's
failure.

An **example** is proved and never runs. It holds `example`, `theorem` and `def`
declarations, prints nothing, and its job is to fail the build when an instance
stops resolving or an algorithm stops accepting a representation — something a
library cannot notice from the inside, because only a use site asks. Every
`def` in one is a plain `def`: a `noncomputable def` compiles the same way a
`def` does, so it would pass unnoticed, and a structure *parameter* is erased
by the code generator where an ordinary function argument is not, so a generic
`def` can compile and only fail once instantiated at a concrete
representation — which is what `Examples/RunnableFloat.lean` instantiates
every runnable algorithm at, one small value per representation. It may carry
a handful of `#eval`s, uncommitted and undiffed, to show a definition runs to
a value and not only that it elaborates; that alone does not make it a demo.

The **demo** runs, and is the only place a definition in this repository is
evaluated *and checked*. Its output is committed as `scripts/demo-expected.txt`
and `check-demo.sh` diffs against it, so an enclosure that silently widens
fails the build. No theorem can do that job: `_outer` is as true of a box the
size of the state space as of a tight one, and the only way to tell those
apart is to compute one and look. `Dyadic` is exact integer arithmetic, so the
committed numbers do not depend on the machine, the compiler, or the order of
anything. The last table is the exception and is meant to be: it runs the
same system at native binary64, where the numbers are reproducible only
because IEEE 754 fixes every operation, and where the error box is nonzero
from the first step.

So: an example says the library still *fits together*; the demo says it still
*computes, and computes tightly*. A change that loosens a bound passes every
example in the tree.

`lake exe demo` builds it as an executable, which has to link, and linking
against Mathlib means compiling the C emitted for every module it reaches. CI
and `check-demo.sh` therefore run the same `main` through the interpreter with
`lake env lean --run src/CORALean/Examples/Demo.lean`, which needs only the
oleans.

## File roles

Per representation, seven kinds of file, and a file does only its own job. Scalar
models and systems follow the same shape:

| File | Holds |
| --- | --- |
| `<Name>.lean` | the structure it is named for, and what it denotes: `construct`, `toReal`, `IsTrajectory` — no theorem, and no storage helper (see "Main-type files") |
| `Operations/*.lean` | one operation each, as CORA gives it a file each |
| `Theorems/*.lean` | one guarantee each, stated and proved together |
| `Counterexamples/*.lean` | a refutation of a printed statement or of CORA's code, with the model of CORA's code it refutes (see "Counterexamples") |
| `Complexity/Space/Theorems/*.lean` | how large a result is — a theorem, proved from the definition, one per count — and its `O` corollary, a file of its own |
| `Complexity/Time/Operations/*.lean` | how much running it costs — a `def`, asserted against a model, one per operation |
| `Complexity/Time/Theorems/*.lean` | what is proved of the asserted costs: monotonicity in the operand sizes, bounds, and the `O` corollary, one per file |
| `Interfaces.lean` | the classes a directory offers, each with the laws its instances owe (see "Interfaces") |
| `Instances.lean` | the class instances, whose fields *are* the guarantees |

A file is named after what it declares, not after the role it plays:
`Zonotope/Zonotope.lean` and `Operations/Reduce.lean`, as in CORA's
`@zonotope/zonotope.m` and `@zonotope/reduce.m`. `Instances.lean` is the
exception, a Lean instance having no name to use.

`Operations` stays a single file where splitting would not pay — `LinearSysDT`
has three, and `Dyadic`'s are one-line compositions.

"One each" is meant literally, and `check-conventions.sh` enforces it: a file
under `Operations/` or `Theorems/` declares exactly one public thing — or, if
that thing is small, it is a section of the directory's `Basic.lean` (see
"Small declarations" below). What it
needs and nothing else uses is `aux_` (a step of one algorithm is `aux_` in that algorithm's
file, see "`aux_`"); what the tree needs earns a file of its own. `<Name>.lean` and `Instances.lean` sit outside the rule — a type is
declared with what it denotes, and instances have no names to collect.
`Complexity/` follows the same layout as every other directory (issue #187): the
exact count (`plusCost`) is a file of `Complexity/Time/Operations/`, its
monotonicity and its `O` corollary (`..._mono`, `..._isBigO`) are files of
`Complexity/Time/Theorems/`, and a size (`plus_h`) is a file of
`Complexity/Space/Theorems/`, which has no `Operations/` because a size is a
theorem about the result, not a definition. The small ones are sections of the
`Basic.lean` of those directories, so most of a Complexity directory is its
`Basic.lean`. Nothing sits directly in `Complexity/`, `Complexity/Time/` or
`Complexity/Space/` but `API.lean`, and no `Cost/` directory exists;
`check-conventions.sh` rejects all three. `Counterexamples/` is the one
exception to "one each", and says why below.

The rule is what keeps the table above true, and it is checked because a
convention nobody tests is one the tree drifts out of: a helper that quietly
grows a second user is the usual way a file stops doing only its own job.

### Counterexamples

A statement that fails, whether the paper's or CORA's code, is a **refutation**; CORA's code as printed,
written down only to be refuted, is a **model** (`…Cora`: `Polygon.representsaOriginCora`, the
`'origin'` test with `all([])` true). Both live in the `Counterexamples/` folder of the layer they
refute, next to `Theorems/`: `ContSet/Zonotope/Real/Counterexamples/`,
`Specification/STL/Counterexamples/`, `Global/Counterexamples/`. A repaired statement (the fix of a
`fixed` row) is library content and stays in `Theorems/`; so does a theorem about the corrected
counterexample of a paper, whose file name may still end in `Counterexample`
(`HeldSimSupportCounterexample.lean`).

A model and its refutation share one file, named for the model:
`Counterexamples/RepresentsaOriginCora.lean` holds `representsaOriginCora` and
`representsaOriginCora_counterexample`. The model exists for that refutation, and the one-public-declaration
rule does not apply here. A model that several refutations use, or that is used by another model, keeps a
file of its own, named for it. A refutation of a paper statement with no model is named for its theorem,
without a suffix: no file name ends in `Counterexample`, the folder says it. The module docstring holds
one `# ` title per part and may be `20` lines long for each of them.

Nothing else is a counterexample: `check-conventions.sh` sends a file named `…Cora`, or declaring a
`…Cora` definition or a `…counterexample` theorem, into a `Counterexamples/` folder, and refuses a file
there that neither says `counterexample` or `Cora`, nor declares a negated statement (`not_`, `_ne`). A model the library does not need (it has a better or exact
version, such as `zonotopeEven` for `zonotopeCora`) belongs in the folder, imported from there by the
refutations and by theorems about the model; only a theorem that states CORA's own test on purpose
(`isFullDimCora_of_interior`) keeps its model where it is, listed with the reason in
`COUNTEREXAMPLE_EXCEPTIONS`. `noncomputable` is free in the folder, its models being read and never run.
`Counterexamples/API.lean` collects the folder, and the `API.lean` that collects `Theorems/` imports it.
The `**Counterexample:**` links of `references/`, the appendix tables `scripts/errors-table.py` and
`scripts/cora-bugs-table.py` and the paper's statistics find a counterexample by that folder.

**Recording a bug in CORA.** A bug found in CORA's code is recorded in two places and nowhere else:
the `cora-issue — …` part of the note of its row in `references/coverage/<group>/<class>.md`, and an
entry of `experiments/paper/cora-bugs.json` (a description of at most ten words, the `kind`, and a
`cex` / `fix` file only where the default pick is wrong). The note is the whole account: what the
CORA code does, a case in which it goes wrong (`read from the source, not run`, unless it was run),
what the formalization does instead, and the Lean witness, a link to the file in `Counterexamples/`,
or the reason there is none (`no Lean witness: …`). There is no further file to enter it in. A way the
formalization parts from CORA that belongs to no single method is a row of the table "Departures from
CORA that belong to no single method" at the end of `references/coverage/README.md`. An error in a
paper goes on that paper's page, under its `## Findings`. `python3 scripts/check-findings.py` checks
the notes, the table and the entries.

### Main-type files

The file that holds a `MAIN TYPE` banner at `<Name>/<Name>.lean` or
`<Name>/<Layer>/<Name>.lean` is where a reader meets the type first, so it holds the type and
what it denotes and nothing said or done about it. Kept: the structure or class, its
`nominal` view and `construct`, the `InflatedContSet` instance that gives the float sets their
meaning, and the other definitions the type is stated with (`Taylm.polyOf`, `Specification.Holds`).
Moved out: every `theorem` and `lemma` — the `nominal_h` fields that let a proof see through
an instance, `materialise_eq`, `mem_construct` — to `Theorems/`, and the storage helper
`materialise`, which rebuilds a float set's function-typed fields as vectors and is the
identity, to `Operations/`. Each goes where its size puts it: a section of `Basic.lean` when it
is at most five code lines ("Small declarations"), a file of its own otherwise.
A validity predicate (`IsValid`, `IsWellFormed` and the like) is no part of the type: it is a
definition in `Definitions/IsValid.lean` of the same class, like any other proposition about the type.
`check-conventions.sh` rejects a `theorem`, `lemma`, validity predicate or `materialise…` definition
in a main-type file.
The rule is not about the file's name: any file with a `MAIN TYPE` banner (`NN/NeuralNetwork.lean`,
`NN/Layers/Layer.lean`) declares no `theorem` or `lemma` and no operation, a `def` returning data
that nothing else in the file is stated with (#134); `NeuralNetwork.Encloses` is in
`Definitions/Encloses.lean`, `Enclose.toLayer` and `Layer.comp` in `Layers/Operations/Basic.lean`.
`Global/`, `Examples/` and `Interfaces.lean` (whose operation classes are #135's) are out of scope,
and nothing else is exempt. What a system class denotes is its runs, so the main file of `ContDynamics/<C>/` declares
`<C>.IsTrajectory`, with what it is stated with (the closed loop's plant input `[a; e]`), and
`check-conventions.sh` asks for it; `OutputEq`, which is no system, is the named exception
(`LinProbSys.IsTrajectory` gives a run by its law at each time, since the process itself is not
defined). A continuous-time run, a hybrid
automaton's flow among them, is a Carathéodory run (#105): the integral equation
`x t = x 0 + ∫₀ᵗ f`, its integrand measurable and integrable (or, for a linear class, its input
measurable), not a derivative at every point, which a zero-order-hold input does not have. A
classical run reaches it through the class's `IsTrajectory.of_hasDerivWithinAt`, and back, at a
continuous field, through `IsTrajectory.hasDerivWithinAt`. `check-conventions.sh` refuses a
derivative in those definitions; `DiffInclAutomaton`, whose paper defines its flow by a
derivative, is the named exception. A class with an output equation, as CORA gives one
(`out_fun`, or `C`, `D`, `k` at a linear class), carries the output in its runs, the same way in
every class (#179): the output signal is the run's last argument and `output` states
`y t = g (x t) (u t)`, at a linear class `outputEq.eval (x t) (u t)` with the noise `F v t` beside
it; a canonical form has none. `check-conventions.sh` asks for the field.

A main-type file also cites the publication it formalizes: its module docstring has at least one
numbered entry, `* [1] ...`, under `## References`, and says what it takes from it (`[1, Def. 5]`).
A cross-reference in backticks does not count, as it is no publication. The publication is the
paper that introduces the representation, or a standard or manual that defines it (a public
one, read for what the file takes from it). A file with genuinely nothing to cite writes one
line `None: <reason>` under `## References`. `check-conventions.sh` asks for one of the two;
there is no list.

### A theorem used once is a lemma of its user

A public `theorem` that exactly one other file reads, and that nothing outward-facing points
at, is an auxiliary lemma of that file: it goes there as an `aux_` one, under its `AUXILIARY`
banner (and an `rfl` lemma used once is inlined at its use, and deleted).
`scripts/check-single-use.py` reports it. A file counts as a user when the last component of the
theorem's name occurs in its code, whatever the namespace or the dot notation in front, so the
count errs towards "more users"; a declaration's own name is no use of a twin of the same name,
and a file that declares a name of its own with that last component reads the theorem only where
it spells it qualified or as a field of a value (`h.foo`). The theorem stays public when

* its own file reads it too, or two declarations of the user's `Basic.lean` do (a bundle holds one
  declaration per section, so no lemma);
* it reads an `aux_` step of its operation, which no other file may read (the theorem is a
  satellite of that operation, "`aux_`" below);
* its file carries a review stamp (`-- Reviewed:` with a reviewer's name and date, not `---`): folding
  it would drop the review, so a reviewed file keeps its own file;
* a page of `references/` or the paper sources under `experiments/paper/` name it or link the
  file that declares it (a ledger row is a promise about it);
* another file's comment or docstring mentions it;
* one of its users is an `Examples/` file or an `Instances.lean`, where a theorem is the
  guarantee an instance or a demonstration shows; or
* it carries an attribute (`@[simp]`, ...), which reads it without naming it.

There is no list of exceptions. Where the one user is a single small declaration of a
`Basic.lean`, which holds no lemma, that declaration gets a file of its own and the theorem
becomes its `aux_` lemma.

A theorem with no other user at all is not reported: that is a guarantee nobody builds on yet,
which a ledger row or a `Counterexamples/` folder may well want.

### A theorem file defines nothing

A file under `Theorems/` (which includes `Complexity/Space/Theorems/`, whose claims are
proved from the definition) states and proves a guarantee about something declared elsewhere. A `def`,
`abbrev`, `instance`, `structure`, `class`, `inductive` or `opaque` there is a definition in the
wrong file: a type, a proposition, a set or a specification goes to `Definitions/`, an
algorithm to `Operations/`, and a conversion's construction to the `Operations/` of its
`Conversion/` layer. The one thing a theorem file may declare is a helper of its own proof,
`private` or `aux_`. `check-conventions.sh` rejects the rest.

The mirror image holds for `Operations/` (#198): a file there holds definitions, and no `theorem`
or `lemma`. A guarantee about an operation is a `Theorems/` file's to state; a general fact about
matrices or vectors, with no operation in it, belongs to the global lemmas
(`toRealMat_append_mulVec_natAdd`, in `Global/Float/ToRealMatMulVec.lean`) or, with one user, is a
`private` lemma there. The one place a theorem may stay in `Operations/` is the `Basic.lean` of
an `Operations/` directory, where a theorem of at most five lines is a section when the
`Basic.lean` of its `Theorems/` directory would close an import cycle
(`HPolytope.mem_stackRows_iff`); there is no list.

### A size is proved; a running cost is asserted

`Complexity/Space/Theorems/` and `Complexity/Time/Operations/` look alike from outside and only
one of them can be wrong, so they are kept apart deliberately.

A **size** — how many generators an operation's result has — is a field of the
result, so `Zonotope.plus_h` is a `theorem` and its proof is `rfl` against the
structure instance in `Operations/`. A **running cost** is not derivable at all:
a Lean `def` says what is computed and never what computing it costs. So a cost
is stated against an explicit model, `Global/Cost.lean`, and justified in the
file's docstring by reading the operation's definition by hand. The model counts scalar
arithmetic and one write for every scalar of the result, copied or padded entries included, so an
operation that builds a result is never free and a cost needing the result's size takes the operand
sizes as arguments. It is an axiom
in the informal sense, and must never be dressed as a theorem about the
definition.

Three things say which a reader is looking at, and the third is checked:

* the directory — `Complexity/Space/Theorems/` or `Complexity/Time/Operations/`;
* the form — a `theorem` about `.h`, or a `def` returning a `Cost`, a type that
  is not `ℕ` and so cannot be equated with a size by accident;
* the name — a public `def` under `Complexity/Time/` is `...Cost` or `...Bound`, which
  `check-conventions.sh` enforces.

Nothing under `Complexity/Time/Operations/` is proved `rfl` against an operation. What *is* proved
there is everything above the assertions: that each count is monotone in the
operand sizes it takes, and that an algorithm's cost is the sum of its
operations' — `LinearSysDT.reachCost_le` assembles `reach`'s bound out of the
asserted per-operation counts and the proved size fact `reach_order_le`, and
asserts nothing of its own. That composition is the point of the arrangement:
a new algorithm's bound is a size fact per operation, a cost per operation,
monotonicity to join them, and induction over the loop.

The primitives in `Global/Cost.lean` are the part of the model most likely to
be restated, so a proof elsewhere reads their stated properties and not their
shapes. `Cost.sort` was `k * k` and is now `k * (log₂ k + 1)`; the change cost
nothing wherever `Cost.sort_mono` was what a caller used, and broke an `IsBigO`
proof three directories away that had unfolded the old product by `rfl`. That
proof goes through `Cost.sort_le_mul_succ` now, and a proof needing something
else of a primitive should ask for a lemma beside the `def` rather than unfold
it. `check-conventions.sh` cannot see this one: a `rfl`, `simp [Cost.…]` or
`unfold` that reaches through a primitive is caught in review or not at all.

`Asymptotics.IsBigO` is deliberately *not* the vehicle for the counts. It takes
a function of one argument along one filter, while a cost grows in several
sizes at once — a step of `reach` in the dimension, the order and the input
set's generator count — and it discards the constant that composition needs.
So a cost is an explicit bounding function and a plain `≤`, and `IsBigO` appears
once at the end, to read one parameter's slice off a bound already proved:
`LinearSysDT.reachStepBound_isBigO`.

### Small declarations

A declaration of at most **five code lines** does not get a file of its own: it is
a section of its directory's `Basic.lean` (`Operations/Basic.lean`,
`Theorems/Basic.lean`, `Global/Basic.lean`, …), which holds that directory's small
declarations and nothing else. A file's header — imports, module docstring, author
block, markers — is at least nine lines, so a file of five code lines was mostly
header. Code lines are the non-blank, non-comment lines between the code markers,
a declaration's docstring included; `namespace`, `section`, `end`, `open`,
`variable` and `universe` lines are context and do not count.

```lean
namespace CORALean.Real

variable {n : ℕ}


-- ======================================  `Interval.abs`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The componentwise absolute value of an interval: the interval of `|x|` over its points. -/
def Interval.abs (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  …


-- ======================================  `Interval.max`  ====================================== --
…

end CORALean.Real
```

**A bundle is its context blocks, each with its sections.** What the old files each said
for themselves — `namespace`, `open`, `variable` — is said once for the sections that
share it. A *block* is a `namespace` line (nested ones allowed), then `open` lines,
then `variable` lines, then the sections, then the `end` lines; the block's lines are
context and do not count toward a section's five. A file usually has one block; it has
several where the sections cannot share one: another namespace (`CORALean.Float`
beside `CORALean.Float.Binary64`), or `variable`s that disagree (the same name at two
types, or a different set of instance arguments, which Lean would otherwise add to
every declaration that mentions the type). Adjacent blocks with the same lines are one
block (checked). A block opens with `namespace` or `section`, never a bare `open` or
`variable`, which would leak into every section after it.

**One namespace, opened once.** Where the `variable`s disagree inside one namespace, the
namespace is not closed and reopened: `end X` directly followed by `namespace X` is
rejected (checked). The `namespace` line stands once, and each set of `open`s and
`variable`s lives in a nested `section` … `end` with its own sections; the last `end X`
closes the namespace after the last of them.

```lean
namespace CORALean

section
open ContSet
variable {S α : Type} [ContSet S α] [Isequal S]

-- … the sections that use these `variable`s …

end

section
open ContSet Scalar
variable {𝕋 : Type} [Scalar 𝕋] {S : ℕ → Type}

-- … the sections that use those …

end

end CORALean
```

Lean puts a `variable` binder into a declaration only where the declaration uses it,
and an instance argument only where it uses the type the instance is about, so a block's
`variable` lines are the union of what its sections each needed, in an order that keeps
every section's own binders in their own order (the order of the arguments of a
declaration is the order of the `variable` list). Two sections whose instance arguments
differ for a type both use, or which bind one name at two types, are not in one block:
the first would silently gain arguments, the second would shadow. A section that needs a
binder or an `open` its block lacks adds it to the block's line if that changes no other
section's declaration, and otherwise starts a block of its own. The conversion that
introduced blocks was checked on every constant of the 103 bundles: its type and value
hashed alike before and after.

A section is its banner, 100 characters with the declaration's name in backticks
(as written, or with its namespace below `CORALean` — `Float.MatExp.corrTerm` —
where two layers' declarations of one name share a bundle), its own author block
directly under it, one blank line, and then the declaration with its `/-- … -/`:
nothing of `namespace`, `open` or `variable`, and no `section` … `end` of its own.
One declaration per section, in `Complexity/` as everywhere else. There is
no per-section module docstring: the declaration's own `/-- … -/` is its description, and
every section's declaration has one. Moving a
file in moves its module docstring there, less the title line: it becomes the
docstring of a declaration that had none, and is appended, paragraph by paragraph
where not already said, to one that had. Since a docstring counts as code, a file
is eligible only if its declaration fits five code lines and the docstring limits
*after* that move — a long explanation keeps its file. The file has a module
docstring of its own and no author block outside the sections; `review.py`
reviews it section by section.

**Order.** Within a block, alphabetical by the banner's name, unless a section uses
a declaration of an alphabetically later one; then the used one comes first, and among
the sections free to go next the alphabetically first does. The blocks themselves are
ordered the same way by the name of their first section, after the blocks whose sections
they use. The check reads "uses"
off the text in two strengths: a section that names another's declaration in full
(`Interval.center`) *certainly* uses it, and must follow it; one whose identifiers
contain the last component (`I.center`, `center`) *possibly* does, which dot
notation makes the most text can say — so a section may come before an
alphabetically earlier one only if that one possibly uses a section in between.

**What stays a file of its own**, whatever its size: a main-type file, `API.lean`,
`Instances.lean`, anything in a `Counterexamples/` folder (a CORA model or a
refutation), a CORA model the library imports (`COUNTEREXAMPLE_EXCEPTIONS` in
`check-conventions.sh`), every file the CORA-bug appendix links, anything under `Examples/`, a file whose module docstring has a
`## References` block — its citation is what `references/` links to, and a section
has no docstring to keep it in — and a file whose name says `Float` where neither
its directory nor its declaration does, since the file name is what marks it as
float layer to `check-references.py` and the paper's statistics.

**Import cycles.** A bundle imports what its sections import. If one section's
file imported a file outside the bundle that imports another section back, the
bundle would import itself, so that declaration keeps its file; it stays in its
file. A declaration of at most five code lines is therefore a section of its directory's
`Basic.lean` unless moving it there would close an import cycle, which
`scripts/check-basic-bundles.py` tests on the import graph; there is no list. Only `Basic.lean`
is a bundle — a cycle is never resolved by a second bundle file in the same directory.

**Moving in and out.** A section that grows past five code lines moves out into a
file of its own, and a file that shrinks to five moves in; `check-conventions.sh`
reports both. Dependents import `…/Basic` (the exact module, never a collector),
and `python3 scripts/check-references.py --fix` re-points the declaration links
of `references/`, which name the declaration and so find it in
its new file.

**What a bundle changes.** Importing one section imports all of them, and a
definition change rebuilds the dependents of the whole bundle; for one-liners
that rarely change that is accepted. A section also sees every section before it,
and a file importing the bundle sees all of them: inside a declaration named
`Interval.…` the namespace `Interval` is open, so a bare `max` there, which meant
`Max.max`, would find `Interval.max` once that is in scope. A declaration whose
name shadows a root one that way is `protected` — the float layer's
`Interval.abs`, `Interval.max`, `Interval.min` and `Interval.le` are — and is then
reached as `I.max` or `Interval.max` only. A proof downstream can likewise meet a `@[simp]` lemma it
never imported before; such a proof states the lemmas and cases it needs.

### `aux_`

What a file needs and nothing else uses carries the `aux_` prefix, as in CORA.
The test is mechanical: used outside its own file, or not.

An `aux_` declaration that no other file reads is `private` (#269), so the compiler rejects any
use from another file; it stays public only where its own file needs it public: in a theorem's
statement (a `let` in it included) or in the body of a public definition, where Lean rejects a
`private` name, and for an `@[csimp]` lemma. A step that a satellite theorem file reads stays public
`aux_` (#227), and an `aux_` that later gains a reader drops `private` again. `private`
declarations count like public ones in the paper's theorem total, and
`scripts/check-private-aux.py` reports a public `aux_` that no other file reads and that its own
file uses only in `private` declarations or in proofs.

#### A step of one algorithm is `aux_` (#227)

What a file needs and nothing else uses is `aux_`, and the file may be an algorithm's. A step
of exactly one algorithm — an `Operations/` definition that one other `Operations/` file reads,
and that is read otherwise only by that algorithm's satellite theorem files — is an `aux_`
declaration in the algorithm's file, under its `AUXILIARY` banner, before the main definition,
and the main definition keeps one numbered step comment per printed step. It does not get a file
of its own because the algorithm's invariant proof needs to name it: that proof is the algorithm's
satellite, and may read the algorithm's `aux_` declarations; nothing else may.

The **satellite** theorem files of the algorithm `<D>/Operations/<X>.lean` are the files
`<D>/Theorems/<S>.lean`, same directory `<D>`, where `<X>` occurs in `<S>` as a whole run of
CamelCase words: `<S>` starts with `<X>` or has it at an uppercase letter, and it is followed by
the end of `<S>`, `_` or an uppercase letter. `IsMinSuffExplanationGreedyMinimalExplanation` is a
satellite of `GreedyMinimalExplanation`, `ExistsAutoStepAutoRun` of `AutoStep` and of `AutoRun`.
Where several operations of the directory match, a stem that is a substring of a longer matching
stem is dropped, so `ExistsAutoStepFloat` belongs to `AutoStepFloat` and not to `AutoStep`. A
`Basic.lean` has no satellites. `scripts/satellites.py` computes it.

A step keeps its **own file** (the D exceptions) when

* the paper prints it as an Algorithm of its own: its docstring cites its own `Alg.` or
  `Algorithm`, not just lines of one (`[1, Alg. 1, l. 3-5]`, `Lines 6-10`);
* two algorithms read it (a second `Operations/` file, or the theorem of another algorithm);
* a float twin calls it from the real layer: its one reader is a `Float/` file and the step is not
  under `Float/`;
* it belongs to another directory than its reader (a `Capsule/Float/Operations/` function that a
  `LinearSys` algorithm calls): it is that directory's public operation;
* it has theorems of its own, or any other reader (an example, a `Counterexamples/` file);
* its file carries a review stamp (`-- Reviewed:` with a reviewer's name and date, not `---`); or
* a page of `references/` or the paper sources under `experiments/paper/` link the file (a results
  row is a promise about it).

`scripts/check-steps.py` reports every other `Operations/` definition with exactly one
`Operations/` reader (and no reader but that reader's satellites). The single-use check treats
an algorithm and its satellites as one unit: a theorem whose one reader is in its own unit is left
alone. `check-conventions.sh` accepts an `aux_` name in a satellite theorem file when the
algorithm's file declares it.

Never on an `instance`. Type class search reaches an instance from every file
that imports it and never names it, so no file can claim nothing else uses one.
An instance that earns a name earns a file; the check rejects the prefix there
outright.

### Section markers

Lean requires a helper to be declared before whatever uses it, so the
declaration a reader opens a file to find is always at the bottom, under every
`aux_` name it needed — the one place the source order works against the
reader instead of for them. A file that declares anything carries four
full-line, 100-character banners, CORA-styled, that say where things are
regardless: `BEGIN CODE` after the author block and before `namespace`;
`AUXILIARY` immediately before the first `aux_` declaration, omitted when
there is none; a `MAIN ...` marker immediately above the main declaration and
above its docstring, so the docstring stays attached to what it documents; and
`END OF CODE` as the file's last line. `API.lean` and any file that declares
nothing carry none of this — there is nothing to find. A `Basic.lean` carries
`BEGIN CODE` and `END OF CODE`, and in place of `MAIN ...` one banner per section
naming its declaration.

The `MAIN` label names the kind of the declaration under it —
`MAIN THEOREM`, `MAIN DEFINITION`, `MAIN INSTANCE`, `MAIN TYPE` — so a
refactor that changes what a file's main declaration is cannot leave a stale
label behind unnoticed; `check-conventions.sh` checks the label against the
declaration, the same way it checks everything else here that the compiler
cannot. A type file with several public declarations — the structure and what
denotes it, `construct`, `toReal` — carries the marker before the first of
them, the type itself, rather than the last. `Instances.lean` has no single
main instance among its several anonymous ones, so it carries `INSTANCES`
instead, with the same placement.

One further marker rides on a line that already exists
rather than costing one of its own: a declaration's `:= by` may end with
`-- --- PROOF ---` to show where the claim stops and the argument starts.

```lean
theorem aux_norm_constTail_le (A : Mat ℝ n n) {r : ℝ} (hr : 0 < r) (η : ℕ) :
    ‖…‖ ≤ r * MatExp.expRemainderBound (r • A) η := by -- --- PROOF ---
```

A proof of **five lines or more**, or a signature of **five lines or more**
(counted from the `theorem` line to the `:= by` line, inclusive), must carry one,
and a declaration with both shorter must not: below that the `:= by` is still in
view, and a flag on every two-line proof would say only what the source already
shows. A long signature hides the seam as well as a long proof does. Required and
refused on either side of one number, so the flag always means the same thing — and
it lands on roughly two theorems in five. No exact count is quoted here: it moves
with every proof written, and a figure CI cannot keep honest goes stale the
day after it is written.

It rides on a `theorem` or a `lemma` and on nothing else. A `def` that proves
something in a structure field — `Ellipsoid.supportBound`'s `le :=`, eight lines
of it — carries no flag however long that field runs, because the checker's
notion of a declaration does not reach inside one. So the count above is a count
of *theorems*, and a proof living in a `def` is invisible to it.

Its length is what it spans: from the `:= by` to the proof's last line, blank
lines inside it counted and the blank lines between it and whatever follows
not. A theorem proved by a structure instance — `... : sys.IsTrajectory … where`
— has no `:= by` of its own and so carries no flag; the fields' own `by` blocks
are not it.

When the line has no room for it inside the hundred-character limit, **the
statement gets wrapped** rather than the flag moved: a declaration head breaks
after the colon that closes its binders, anything else at the first space that
lets both halves fit. Moving the flag somewhere else instead would leave two
forms to recognise and two habits to keep.

Only the declaration's own `:= by` takes it, never a nested `have … := by`:
the flag marks the proof of the thing the file is named for, and one on every
inner block would mark nothing at all.

### The conclusion marker

The PROOF flag marks where the claim stops; its twin marks where the claim starts. Every theorem
or lemma that carries `-- --- PROOF ---` ends the line of the colon that closes its binders with
`-- --- CONCL ---`, so that what is given stands above the flag and what should hold below it, and
no declaration carries one without the other:

```lean
theorem NonlinDASys.exists_lagrange_remainder {C : Set (Vec ℝ d)} (hC : Convex ℝ C)
    {F : Vec ℝ d → ℝ} {Ff : Vec ℝ d → (Vec ℝ d →L[ℝ] ℝ)}
    {Hf : Vec ℝ d → (Vec ℝ d →L[ℝ] Vec ℝ d →L[ℝ] ℝ)}
    (hF : ∀ ξ ∈ C, HasFDerivAt F (Ff ξ) ξ) (hH : ∀ ξ ∈ C, HasFDerivAt Ff (Hf ξ) ξ)
    {zs z : Vec ℝ d} (hzs : zs ∈ C) (hz : z ∈ C) : -- --- CONCL ---
    ∃ ξ ∈ segment ℝ zs z,
      F z = F zs + Ff zs (z - zs) + (1 / 2) * Hf ξ (z - zs) (z - zs) := by -- --- PROOF ---
```

The two flags go together: `-- --- CONCL ---` is required wherever `-- --- PROOF ---` is and
refused everywhere else, so there is no threshold of its own and no list of exceptions. It rides on
the colon line only: the conclusion starts on the line below, so a statement whose conclusion
shared the colon line is broken after the colon, and a colon line with no room for the flag has its
last binders moved down to it (or the colon on a line of its own). A proof written as a term has no
`:= by`, hence no PROOF flag and no CONCL flag. `check-conventions.sh` checks both. The flag
carries no meaning for Lean and none for `Last update:`; adding or moving it is layout and leaves
`Reviewed:` alone.

### `API.lean`

Holds nothing but imports: a directory collects itself there, `Operations/`,
`Theorems/` and `Instances` included. It is the entry point *into* the library —
one import puts a whole representation in scope, which is what someone using
CORALean, or trying something out, wants.

Inside the project, a file imports the exact modules it names and never a
collector: `Theorems/PlusExact.lean` imports `Operations/Plus.lean`, not
`Operations/API.lean`. Importing a collector makes a file wait for everything in
that directory, and the build is bound by the longest such chain rather than by
the work — the rule nearly halved it when it landed, 37 files to 20, on a
machine with 16 cores that were idle either way.

A file still never imports its own directory's `API.lean`, which would be a
cycle. Only an `API.lean`, which collects, and a root named in `lakefile.toml`,
which is an entry point, import a collector; this is checked.

"Collects itself" is checked, and it means every sibling `.lean` file and every
sub-directory, the latter through its own `API.lean`. A file that some other
file happens to import by exact path is not thereby collected: `Global/Block.lean`
sat outside `Global/API.lean` with four importers and a green build, because
reaching a module is not the same as a directory owning it.

An omission that is meant states itself, on one line of the collector's own
module docstring:

```
`Float/` is deliberately not collected here
```

naming the sibling the way the directory spells it — `Float/` for a
sub-directory, `Block.lean` for a file — and a sub-directory named that way
excuses everything under it. The exception then lives beside the imports it is
about, rather than in a list inside a script that nothing makes anyone reread;
`check-conventions.sh` also reports a marker that excuses nothing, so an
exception cannot outlive the thing it was written for.

Three omissions are stated that way today. `Global/API.lean` leaves out its
`Float/`, which every `Real` file would otherwise reach, breaking the rule below that deleting `Float` leaves the
specification standing. `CORALean.lean` leaves out `Examples/` and
`Examples/API.lean` leaves out `Demo.lean`, both being targets of their own, so
that the library holds the development and nothing that merely uses it.

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

A containment between two *represented* sets says `contains`, CORA's way round:
`contains(X, Y)` is `X ⊇ Y`. The name reads the statement with the receiver
elided, so `Zonotope.interval_contains` is "its interval contains it" and
`HPolytope.contains_vPolytope` is "it contains its vPolytope" — one word, and
the side the target sits on says which way the inclusion runs. Every containment
in `Conversion/` is `Source.target_contains`, unless it is the inclusion the
other way, which is `Source.contains_target`, or both hold and it is
`Source.target_exact`. An `_of_` name says the hypothesis instead:
`HPolytope.contains_of_pinned`.

Not a relation of its own: the statement stays `X.construct ⊆ Y.construct`. A
`contains` over `ContSet` would need both instances, and `Instances.lean`
imports the operations, some of which are implemented by conversion —
`VPolytope.intersectionH` is — so a conversion file cannot import it without a
cycle. The one word used everywhere is what fixes the direction; there is
nothing else it could mean.

`subset_` is left where one side is a bare `Set` and not a representation:
`HPolytope.subset_ofBounds`, `Interval.subset_nominal_zonotope`. `_outer` is
left on the class obligations — `Plus.plus_outer`, `IntervalOuter.interval_outer`
— which quantify over a representation instead of naming a pair, and whose
suffix is the table above.

No binder is called `temp`, `tmp` or a variant of either (`tmp1`, `temp_`, `tmpX`,
`temp₁`): a `let`, `have`, `fun`, `obtain`/`rcases` pattern, `intro` or declaration
argument names the value for what it is — the CORA variable it mirrors, or what it
holds (`preInf`, `quotient`, `shiftedCenter`). `check-conventions.sh` rejects the
name in code, and leaves comments and strings alone (#191).

A `Prop`-valued definition (a `def`, `abbrev`, `structure`, `inductive` or `class` whose type is
`Prop` or ends in `→ Prop`) is named so that `X.Name args` reads as a statement (#196):

* a property is `Is…` or `Has…` (`IsCompact`, `HasDerivAt`, `IsAdmissible`): `sys.IsTrajectory …`,
  `IsRun`, `IsStay`, `IsCanonicalConstTrajectory`; an adjective or a noun alone (`Sorted`,
  `Branch`, `Exact`) is not a statement and takes the `Is`;
* a relation is a third-person verb form (`Encloses`, `Holds`, `HoldsOn`, `Reaches`, `Refines`,
  `Satisfies`): the first word of the name, up to the next capital letter, digit or `_`, is a
  word of at least four letters that ends in `s` but not in `ss`, `us` or `is`;
* a predicate that mirrors a CORA method keeps CORA's lower-case name when the name starts with a
  method of `references/coverage/cora-inventory.json` (`eq`, `le`, `isequal`, `representsa_point`,
  `constrSat`), and the model of CORA's code ends in `Cora`.

A theorem that embeds the name follows Lean's rule, `IsTrajectory` as `isTrajectory` in a snake-case
name (`simulate_isTrajectory`, `ofFull_isTrajectory_iff`). `check-conventions.sh` runs
`scripts/check-prop-names.py`, which rejects a Prop-valued definition whose name has none of these
forms; there is no list.

CORA's spelling is `center`: `center`, `centerMat`, `recenter`, `IsCenter`, never `centre`, in
identifiers, file names, docstrings and comments alike. `check-conventions.sh` rejects `centre`
anywhere in a source file (#199).

A float negation is written `-A` or `-b`, never `fun i j => neg (A i j)` or `fun i => neg (b i)`:
negation is exact, so the `Neg` on a float matrix or vector is the entrywise `neg`, and
`toRealMat (-A) = -toRealMat A` (`toRealMat_neg`, `toRealVec_neg`) says what it reads as.
`check-conventions.sh` rejects the spelled-out lambda (#197).

When an operation returns `Option`, its result cannot be named in a claim, and the main theorem
quantifies over the results instead of taking a hypothesis `(hE : f … = some E)`:
`∀ E ∈ f …, claim`, the call in the statement, `Option` membership doing the work of `= some`
(a pair is `∀ a b, (a, b) ∈ f …`; an `Option (Option _)` is `∀ o ∈ f …, ∀ x ∈ o`). Hypotheses
about the result go in the claim as arrows, in front of it. The proof starts with
`intro E (hE : f … = some E)`, and a caller supplies `_` for `E`. Every other operation is called
directly in the claim. `check-conventions.sh` runs `scripts/check-option-hyps.py`, which rejects a
binder `(h… : <call> = some …)` in the signature of the theorem under a `MAIN THEOREM` banner,
except a lookup (`l[i]? = some a`, `.head?`, `.find?`) and a verdict (`= some true`,
`= some false`), which name no result.

## The two layers

`Real` is the specification, `Float` the refinement, which obtains its soundness
guarantees by transitivity — so `Float` imports `Real`, never the reverse. A new
float operation pays its rounding into an interval error box via
`InflatedContSet`.

`𝕋` is the scalar a layer computes in — ℝ in `Real`, a machine scalar in `Float`.
`Scalar` (`Global/Interfaces.lean`) reads a matrix of it as a real one, which is how a guarantee
stated once covers both layers. Outside `ContSet/` the two layers are one
definition: `Global/Float/Instances/Real` instantiates the scalar interface at ℝ
with every rounding exact, so a generic algorithm at `𝕋 := ℝ` *is* the exact
one, and its soundness theorem, stated once, is both layers' guarantee.

### Float definitions earn their name

`X.nominal` is the exact set the stored floats of `X` describe, so a float definition that is
only `X.nominal.op args` is the exact operation under a second name, and its uses can say what
it says. A float operation is a definition of its own when it computes something the exact one
does not: a result in `𝕋` where the exact one is a real number (`nominalSupportBound` is the
`FloatBound` above `nominal.supportBound`, with every rounding upward), another algorithm
(`HPolytope.levelSet`, which writes an equation as two inequalities), or the error box. The
bare form is rejected by `scripts/check-float-wrappers.py`, and so is the exact operation applied
to the arguments read as reals — `Real.HPolytope.rowLin (toRealMat M) i` — which is no more than the
conversion under a name. The one bare wrapper that stays is recognized by its form: `X.construct`
in the float main file `ContSet/X/Float/X.lean` of a set with no error box (`Interval.construct`),
which the `ContSet` instance and every `I.construct` in a statement resolve through by dot
notation; there is no list. A name for the conversion (`rowLin` was one) is not kept: its uses spell it out.

**The float layer is part of the work, not a follow-up.** New work carries both
layers wherever it can, and a contribution that lands only the `Real` half must
say why in its module docstring — not as an apology, but because the reason is
usually informative: the operation is a specification with nothing to round, or
it needs a decidable order the float scalar has and ℝ does not, or the rounding
has a genuine design choice behind it. A real definition alone is a specification
of something no machine runs, and it is far cheaper to refine an operation while
its proof is still in hand than to come back to it.

In `Specification/` the rule is checked (`scripts/check-float-refinement.py`): an operation
file under `Operations/` whose code mentions `ℝ` and not `𝕋` says why in its module
docstring, in one sentence that opens with a marker. `Real-only, a specification:` says what
it specifies — a `Set`, a truth value, a formula or another object no machine runs, so there
is nothing to round. A computable definition that does arithmetic on real values CORA
computes in doubles is not that: it is `Refinement pending:`, with the refinement generic
over `𝕋` it is waiting for; writing the refinement removes the sentence. The check is by form
alone, with no list.

### The error box and `absorbRounding`

Every float set records its rounding explicitly in an `I_error` box (`InflatedContSet`: the set
denotes `nominal ⊕ I_error`); rounding is never folded silently into a parameter. Each float
representation provides a sound `absorbRounding`, which moves `I_error` into the parameters where
the representation can hold it (a zonotope into box generators, a polyhedron into the right-hand
side `b`, together with the slack its rows record besides the box, a constrained polynomial
zonotope into independent generators, the slack its constraint's equality rows record
(`cons.b_error`) into a factor per row, a star set into factors with the box's own bounds, a capsule into its radius, a Taylor
model into its remainder, an ellipsoid into its shape matrix by an outer ellipsoid of its sum with
a ball holding the box), with `absorbRounding_outer : S.construct ⊆ S.absorbRounding.construct`.
A row that is an equation has no interior to absorb its own rounding, so a float representation
with equality rows records it per row in a field `<name>_error` beside the box, read through
`|·|`, and its constructors set it to zero; a representation that holds its rows in a float
representation of their own (`ConZonotope.P`, `ConPolyZono.cons`) inherits that one's `_error`
fields, and its `absorbRounding` names them too, moving them or saying where they stay. A float
type none of whose operations moves a point, a constraint system such as the float `PolyLevelSet`
whose rounding is all in its rows' coefficients, has no box to absorb: it records its rounding in its `_error` fields and says so on one line of its
main docstring, `` There is no `I_error` and no `absorbRounding`: `` and the reason, which the check
accepts in place of the box, and refuses on a type that has one.
`absorbRounding` may itself round, so it does **not** promise an empty `I_error` afterwards: the
result's box holds only the rounding of the absorption step, often exactly zero, and a caller
must not assume `I_error = 0` after absorbing; where it is cheap, a lemma bounds the residual
(`Zonotope.absorbError` is the midpoint-centred variant that leaves one). A theorem about the nominal
part alone is `absorbRounding_nominal : S.construct ⊆ nominalSet S.absorbRounding`, which
`absorbRounding_outer` follows from when the box left is the origin
(`InflatedContSet.nominalSet_subset_construct`). A representation that cannot hold the box, or has
none of its own, says so in its main-type docstring in one line `There is no \`I_error\` and no
\`absorbRounding\`: <reason>`, which the check accepts for a type with no box and no
`absorbRounding` (`Interval`, `Polygon`, `ProbZonotope`, `ZonoBundle`, `Zoo`); a type with a box that
cannot move it says `There is no \`absorbRounding\`: <reason>` (`VPolytope`);
`scripts/check-absorb-rounding.py' (run by `check-conventions.sh`, #185)
requires the rest to have an `I_error` field, a `def X.absorbRounding` that names every other
recorded rounding field `<name>_error` of the type, and a `theorem X.absorbRounding_outer` under
`ContSet/X/Float/`, and rejects the former name `dependent_outer`.

### Two scalars a definition can be run at

`SoundFloatArithmetic` fixes no format, so the float layer has more than one
model. `Dyadic p` is exact integer arithmetic with an unbounded exponent: every
obligation is a theorem, nothing overflows, and a result computed there rests on
`propext`, `Classical.choice` and `Quot.sound` and on nothing else. Native
binary64 is Lean's `Float`, compiled to a machine double and fast — and opaque
in the logic, so the ten obligations are bundled into one property,
`IsTrustedHardware`, and assumed in one line in
`Global/Float/Instances/Binary64/Definitions/Axioms.lean` — one of the three files
in the tree that may carry an `axiom` (see the end of this section), and one of
those `check-conventions.sh` names. A result that
reaches `Float` therefore reports exactly one name beyond Lean's own, and a
verified model of binary64 would discharge it without another line changing.

The assumptions are true of IEEE 754 binary64 on a run in which every value
stays finite and nothing underflows into the subnormals. Neither restriction can
be written into the class, whose obligations are unconditional; instead
`Binary64/Operations/InRange.lean` checks them at runtime, and an operation that
leaves the range returns NaN, which propagates. Prefer `Dyadic` where the cost is bearable, reach for
`Float` where it is not, and say which a number came from.

Directed rounding is achieved without a rounding mode and without C of its own:
the machine's round-to-nearest result is stepped one unit in the last place
outward by an increment of its bit pattern. It costs one ulp per operation, paid
whether or not the operation rounded, which the demo's third table shows.

A third pair of scalars is not a model at all. `Examples/Bench/NearestUnsound`
rounds to nearest in both directions, as CORA does, and instantiates the class
by one axiom, `nearestUnsound`, that is FALSE by design — the paper's
"round-to-nearest (as in CORA)" baseline, run by `bench --type nearest` on the
unchanged library. Where `trustedHardware` states what the hardware really does,
it states what it does not; it is tolerable only because nothing outside the
bench can reach it, which `check-conventions.sh` and `check-axioms.sh` check
between them.

A fourth scalar is optional and not built by default: `Flint p`
(`Global/Float/Instances/Flint/`, README "FLINT backend (optional)") is
`Dyadic p`'s own representation with its six rounded operations handed to
FLINT's `arf_add`/`arf_mul`/`arf_div` through a C shim instead of pure Lean, for
arbitrary precision without `Dyadic`'s big-integer cost. `trustedFlint`
(`Global/Float/Instances/Flint/Definitions/Axioms.lean`) is TRUE, unlike
`nearestUnsound`, but opt-in the same way: `check-conventions.sh` and
`check-axioms.sh` keep it out of every result outside that backend and
`Examples/BenchFlint.lean`. CORALean has exactly these three axioms.

## Certificates, not algorithms

Several operations have no definition — a Minkowski sum of halfspace
descriptions, a bounding box, a conversion. What they have in common is one
question: how far does this set reach in direction `c`? For a polytope that is a
linear program, and `Global/SupportFunction` answers it once.

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

`FloatBound` is the same object with a float value, and lives with the scalar
interface in `Global/Float/`. Its composition rules are these with `+` replaced
by `addUp` and `max` by `maximum` — a bound only stays sound by growing.

## Verification

An algorithm here returns a superset of a set nothing computes: the reachable
set of a system, the exact image of a network. `Specification` is what turns that
into an answer — a safe set every point must lie in, or an unsafe set no point
may — and `holds_of_outer` says a check passed on the superset is passed by
everything inside it. One theorem, both directions, and it knows nothing about
what produced either set, which is why `LinearSysDT.holds_of_reach` and
`NeuralNetwork.holds_of_enclose` are a line each.

`Reach` is that superset's interface, once for every system class. `reach` returns an
`Option`: `none` where the run could not certify its own soundness conditions — a horizon no
multiple of `Δt`, a linearization region missing the set computed in it — which is where CORA
raises an error. `reach_outer` takes the set by `reach sys params options = some R`, so a
failed run has no `R` and nothing follows about it; `Reach.check` answers `false` for it.
State every guarantee about an `Option` result that way, never as a `match` whose `none` arm
is `True`, which proves something of a run that returned nothing and reads like a passed check
(`check-conventions.sh` refuses the arm). A side condition the run can decide belongs in the
test that chooses `none`, not among `reach_outer`'s hypotheses; one fixed when `options` is
built, a positive zonotope order, is a field with a default proof, refused at elaboration.

The converse fails, and that is the method's whole cost: a specification that
fails on the computed set is not a counterexample, and the answer to it is a
tighter enclosure rather than an argument about the system.

Discharging the check is `Global.SupportFunction` again — a separating direction proves
disjointness from an unsafe set, a bound per halfspace proves containment in a
safe one, and `m - 1` bounds prove a classifier picks the same label across a
whole input set.

## Proofs

Write them explicitly. `maxHeartbeats` is 40000 in `lakefile.toml`, a fifth of
Lean's default, so a proof that starts searching fails rather than quietly
costing seconds. `aesop`, `decide`, `exact?` and the rest of the search tactics
are refused outright, in tactic position.

Override the limit per declaration when justified, and say in one line above the
`set_option` what is expensive — the cost is visible in the number, but what
causes it is the part a later reader cannot reconstruct.

`set_option ... in` goes above the docstring. Between the docstring and the
declaration it silently detaches the two.

Import Mathlib modules in the file that uses them, never through a shared file:
a shared import list rebuilds every importer when any import is added to it.

### Name what repeats

A subterm used more than once in a statement or a proof gets a name, once, where it is first
needed: the reader then sees what the repeated part *is* and compares the places that use it at
a glance. A fact is a `have h : … := …`. A term in a proof is a `set x := … with hx` (after the
`obtain` or `intro` it depends on, and before the hypotheses it should replace, since `set`
rewrites the context as well as the goal), or an `obtain ⟨x, hx⟩ : ∃ x, x = … := ⟨_, rfl⟩` where
the name should stay opaque. A term in a statement that its readers will see is named by a local
`let` at the head of the statement (`let mid := … ; a ≤ mid ∧ mid ≤ b`), which a proof takes
with `intro mid`. Where a `set` name is opaque to `simp` and `linarith`, `simp only [x]` unfolds it
at that step. Naming changes how a statement or proof is written, not what it states, so it
does not count as a change of the file for the `Reviewed:` line.

`scripts/check-repeated-subterms.py` reports the clearest case: a parenthesised or `⟨ … ⟩` group
of 70 characters or more that one declaration spells out three times or more. There is no list of exceptions: a
repeated group in a statement is named with a `let` or, where it is a concept, a definition.

### `aux_sum_univ_<op>`

A size-changing operation needs one of these, and it is not copy-paste that
could be factored out: `Fin.sum_univ_add` cannot rewrite a sum whose index type
reads `Fin (Z₁.plus Z₂).h` rather than `Fin (Z₁.h + Z₂.h)`, since unifying the
two is not type-correct at the elaborator's transparency. The restatement names
the operation, so it has to live with it; the proof is `Fin.sum_univ_add f`, or
`rfl` where the result's index type needs no splitting at all. Ascribe the
binder in any statement that sums over an operation's result, or the lemma will
not match there either.

### Sentences that explain an absence

A docstring saying why something is *not* there is the kind a reader trusts
without checking, and the kind nothing ever brings back into contact with the
code. Seven went false in two days: three claimed a float layer the same commit
had added, the Real/Float split having copied the prose across; two claimed a
missing class that existed; one claimed a missing instance declared thirty lines
below it.

`python3 scripts/stale-claims.py` catches the shapes that recur. It is not in
CI — every check is a heuristic and a hit needs reading, not obeying — so run it
when a class, an instance or a float layer lands. Better still, when a change
fills a gap, ask which docstring explained that gap and fix it in the same
merge request.

It catches shapes, not sentences, so do not read a clean run as a clean tree.
Four sentences went stale in one day that it cannot see: three named a *theorem*
that was missing and has since been written — no pattern can know what the
theorem was — and one sat in a representation's own `API.lean`, one level above
`Real/`, which the float check did not look at until it was widened to. A rename
invalidates prose by construction and the script sees none of that either.

### A notation's literal tokens are not available as identifiers

A notation's literal string tokens take those words out of circulation as
identifiers everywhere the notation is in scope — `and := Foo.and` fails to
parse if some in-scope notation spells out the token `and`. `scoped` does not
narrow this within the namespace tree: it stays active throughout its own
namespace *and every sub-namespace*, so scoping a notation to `CORALean`
still reaches every `CORALean.*` file, which is nearly the whole library.

`Global/Partition.lean` learned this the hard way: its two-part notation once
read `Split α into β and γ`, and the bare word `and` then blocked named-field
syntax on every instance of the intersection class, whose field was then called
`and`. The fix is not scoping harder; it is not choosing an English word in the
first place. The notation now reads `Split α into β ⊕ γ`, which is also the
right connective on the merits, since `Partition₂ α β γ` states exactly that
`β ⊕ γ ≃ α`.

A class field named after an English word is worth checking against notations
in scope before naming — and better still, not named after one: the class is
now `Intersection` and its field `intersection`, which no notation can take.

### An expected type that will not unify

Two lemmas can be about the same statement, elaborate instantly as bare terms,
and still hang forever when one is offered to the other as a goal. It happened
with `Zonotope.mtimesMatZonotope_outer`, which is `bilin_outer` at Mathlib's
`Matrix.mulVecBilin`: `simp only [← Matrix.mulVecBilin_apply ℝ ℝ]` followed by
`exact Zonotope.bilin_outer ...` does not terminate even at `maxHeartbeats 0`,
and `show`ing the goal into the same syntactic shape first does not help. The
matrix module instances are what run away, and only when there is an expected
type to unify against.

Bind the lemma before touching the goal:

```lean
have h := Zonotope.bilin_outer (Matrix.mulVecBilin ℝ ℝ) M Z
simp only [← Matrix.mulVecBilin_apply ℝ ℝ]
exact h
```

Six seconds instead of never. This is not a proof that needed restructuring, so
say in a comment that the order is deliberate — the next reader will otherwise
tidy the `have` away.

## Documentation

Every file opens with a module docstring saying what it is for and what is
non-obvious about it: where it departs from CORA or from the paper it cites,
which hypothesis is doing the work, which Lean detail a reader would otherwise
trip over. Not the file's role in the layout, which is this document's job, and
not what the code already says.

Keep every comment short and precise — one line where one will do — and state
how the code is now, not what it used to be or what was tried instead. Where the
comparison of alternatives is worth keeping at all, keep the *current* design
positively and drop the post-mortem.

There are no per-directory READMEs.
The module docstring of a directory's `API.lean` is its entry point.

### Algorithms read like the paper

A definition whose docstring cites a paper's algorithm (`Alg. 1`, `Algorithm 2`) is that
algorithm, so its body reads as the printed one does: one named `let` per printed step, in the
paper's own symbols, each under a `-- <n>. …` line comment that says what the step does in the
paper's words (`Taylm.rangeBound` is the model). `scripts/check-algorithm-steps.py` sees the
form — a citing docstring, a body of three lines or more, no `-- <n>.` comment — and refuses it.

### Lengths, which `check-conventions.sh` enforces

| | |
| --- | --- |
| module docstring, content file | 12 lines of prose — not `## Inputs`, `## Hypotheses`, `## Output`, `## Conclusion`, `## References` |
| module docstring, collector | 25 lines — it is the directory's entry point |
| docstring above a declaration | 3 lines; longer explanation belongs in the header |
| inline `--` comment | 1 line; two in a row is a paragraph in the wrong place |
| code with no comment | 20 lines, which is a *minimum* density and aimed at proofs |

The density check counts from the first declaration body in the file, not from
the top: a signature and the file preamble above it are not proof steps, so
neither has to carry a comment every 20 lines.

The module-docstring cap measures the prose only, up to the first `## Inputs`,
`## Hypotheses`, `## Output`, `## Conclusion` or `## References` heading: a bibliography
and a list of arguments are not text that grows the way an explanation does. The cap has no
exceptions: the references hold the detail.

### Inputs and outputs of the main declaration (#251)

CORA's help text names every argument and the result; so does the module docstring of a content
file, for its **main declaration** (the one under the `MAIN THEOREM` / `MAIN DEFINITION` banner),
in sections that follow the prose and precede `## References`:

* a **definition** has `## Inputs` and `## Output`;
* a **theorem** has `## Inputs`, `## Hypotheses` and `## Conclusion`.

`## Inputs` lists the *non-`Prop`* binders of the declaration, explicit or implicit, named exactly as
in the declaration and in its order, without instance arguments (`[..]`) and without the dimension
variables a `variable` line supplies; an anonymous binder `(_ : T)` is listed as `_`. `## Hypotheses` lists the `Prop` binders the same way.
`## Output` / `## Conclusion` has exactly one entry. Entries are terse, one line each:
``* `Z` – zonotope``. A section with nothing to list says `* none`. A definition that takes
`Prop` binders (a `dite` condition, say) lists them under `## Hypotheses` between `## Inputs` and
`## Output`; one without has no such section. An auxiliary declaration gets an entry only where it is
needed to understand it, in its own `/--` docstring. `Basic.lean` bundles and the other summary
and collector files (`API.lean`, `Instances.lean`, `Interfaces.lean`, `MAIN TYPE` and
`MAIN INSTANCE` files) are exempt.

### Every declaration is documented in words once (#257)

The main declaration is documented by the module docstring's sections above, so a `/--` on it is
optional. Every other `def`, `abbrev`, `theorem`, `lemma`, `structure`, `class`, `inductive` and
`instance` under a `MAIN THEOREM`, `MAIN DEFINITION`, `MAIN TYPE` or `MAIN INSTANCE` banner has its
own `/--` docstring: every declaration in the files exempt from the sections (`Basic.lean`,
`API.lean`, `Instances.lean`, `Interfaces.lean`, and files with only `MAIN TYPE` or
`MAIN INSTANCE` banners), and the second and later declarations under a banner in the other files.
Attributes (`@[simp]`) between the docstring and the declaration are fine. Structure fields and
`aux_` declarations in `AUXILIARY` sections are not covered. The docstring says in words, in one to
three lines, what the declaration is or states, without copying the formula; an abbreviated name
(`stBeta`) says where it comes from (CORA's `'approx:st'`, Sadraddini and Tedrake's β).
`check-conventions.sh` reports each missing docstring; the rule has no list.

For a definition (`Zonotope.reduceGirard (Z : Zonotope (Vec ℝ n)) (o : ℕ)`):

```
## Inputs
* `Z` – zonotope
* `o` – target order

## Output
* zonotope of order at most `o` enclosing `Z`
```

For a theorem (`Zonotope.reduceGirard_order_le (Z : Zonotope (Vec ℝ n)) {o : ℕ} (ho : 0 < o)`),
which re-lists the variables of its definition as inputs and keeps what it assumes apart:

```
## Inputs
* `Z` – zonotope
* `o` – target order

## Hypotheses
* `ho` – `0 < o`

## Conclusion
* the reduced zonotope has at most `o * n` generators
```

`scripts/check-io-doc.py` (run by `check-conventions.sh`) checks the sections' presence and order
for the kind of the main declaration, that the names listed under `## Inputs` and
`## Hypotheses` are exactly the declaration's binders in its order, none missing and none extra,
and that `## Output` / `## Conclusion` has exactly one entry. It cannot elaborate, so it sorts
binders into hypotheses by a text proxy: a name `h…` (unless its type is headed by a data type such as `Fin`, `Vec`, `ℕ` and
has no relation symbol), a depth-0 relation or logic symbol in the type (`= ≠ ≤ ≥ < > ∈ ∉ ⊆ ⊂ ∣ ∀ ∃ ¬ ∧ ∨ ↔`), or an
`Is…` / `Has…` head or a listed Mathlib predicate (`Convex`, `Continuous`, `Nonempty`, …). A
`Prop` binder that none of these catches is taken for an input, and a data binder named `h…` whose type has a relation symbol for a
hypothesis; rename the binder in either case. The rule has no exceptions: every content file with
a main declaration carries the sections.

### References

A publication named in prose cannot be checked and cannot be looked up, so cite
it as CORA does — `[1]`, or `[1, Prop. 3.1]` — and define the number at the end
of the module docstring:

```
## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
```

Every `[N]` cited is defined, every one defined is cited, and the numbering is
dense from 1. An identifier that happens to carry a name — `reduceGirard` — is
not a citation.

**Name the result, not only the paper.** `[1, Prop. 3.1]` is what lets
[`references/`](references/README.md) put this file in that proposition's row;
a bare `[1]` lands in the page's "cited without a result" list instead, which is
where a reader looks to find out what is still imprecise. An entry in backticks
— a CORALean declaration, or a path into CORA's own `.m` sources — is a
cross-reference rather than a publication, and needs no page.

**Every publication cited has a page under `references/`**, in a directory for
its year, holding that paper's results and where each is formalized. Citing a
paper for the first time means adding one; `check-references.py` says so if you
forget.

**Cite where the result actually is.** Cite the paper, never a thesis: a thesis reproduces
results that first appeared in papers, and the paper's own numbering is the one a reader can
look up. Find the paper that states the result, read it, and cite it for what it says — a
result a paper only defers ("see [27]", a thesis) is cited for the statement it makes and no
more. Where no paper we hold states a result, remove the citation and say so in the docstring
("not in a paper; CORA's `priv_inputTie`"), citing CORA's `.m` source as the reference entry.
A book is fine where no paper stands behind the result — CORA cites one for the matrix zonotope
product, and so do we. Where none can be confirmed, leave the section out; a blank is honest and
a wrong citation is not. `check-conventions.sh` runs `scripts/check-thesis-refs.py`, which rejects
a `## References` entry that says `thesis`, `dissertation`, `PhD` or `habilitation`, in every
file and with no exception list.

## The module header

Every file under `src/` is a Lean module, and its header sits at fixed lines:

```lean
module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

/-!
# An interval is convex
…
-/

-- Authors:       …
```

`module` on line 1, one blank line, the imports from line 3 on, one blank line,
`@[expose] public section`, one blank line, then the module docstring and the
author block as below. A collector (`API.lean`) declares nothing, so it is
`module` and its `public import`s only, with no section.

Why: in a module a proof is private, so the `.olean` a file exports holds its
statements and definitions but not its proofs. A change that touches only a
proof leaves that interface unchanged and rebuilds the file alone rather than
every file that imports it. `public` keeps every declaration visible as before,
and `@[expose]` keeps every definition unfoldable downstream, so `rfl`,
`decide` and `simp [f]` see what they saw. What a module changes for itself: it
sees only what Mathlib exports publicly, so a tactic it uses (`ring`,
`norm_num`) is imported in the file itself rather than reached through another
import; and a `private` definition cannot be used by an exposed one, so such a
helper is public, under a name that does not clash.

A file stays a non-module only when its proofs unfold a definition that core or
Mathlib does not expose (`Nat.fold`, a list sort by `rfl`), or when it imports
such a file, since a module cannot import a non-module (the reverse is fine).
Today no file is one; everything under `Examples/` stays non-module, since
`#eval` in a module needs `meta import`. `check-conventions.sh` checks the
header lines and refuses any other file that is not a module.

## Import guards and layering

A handful of files are imported by most of the tree: `Global/Tensor` by about nine
thousand files, the entrywise and scalar layers, `Float/FloatOps`, the abstract
`ContSet` class and `Interval/Real/Interval` by thousands each. An import added to
one of them is added to all of them, so a heavy theory (measure theory, probability,
determinants and spectra, the analytic special functions, calculus, inner-product
geometry) that reaches such a file's closure rebuilds the whole tree on every change
to it. Mathlib guards its base files the same way, and so do we: after the author
block, under a `-- Import guards` comment, each of these files states what must stay
out of its closure, one commented line per guard:

```lean
-- Probability, which sits on top of measure theory.
assert_not_exists ProbabilityTheory.IndepFun
-- The abstract set class sits above this file.
assert_not_imported CORALean.ContSet.ContSet.ContSet
```

`assert_not_exists D` fails the build if declaration `D` is in the environment,
`assert_not_imported M` if module `M` is in the closure. A guard holds today, which
the build proves, and names something that would be a realistic regression. A guard
on a name that does not exist passes silently, so check a new one with a scratch file
that imports `Mathlib` and the module and ends in `#check_assertions!`; the
conventions check does confirm that an `assert_not_imported` module has a file.

`scripts/check-conventions.sh` enforces two things. `GUARDED_FILES` lists the guarded
files with their guard counts, and a missing guard, a guard without its comment or a
count that differs is reported. `LAYERS` lists, per top-level directory of
`src/CORALean/`, the directories it may not import: `Global/` imports no other layer (but
the five `Global/Float/` enclosure files that name their results `Float.Interval` import
`ContSet/Interval/Float/Interval`, which needs nothing above `Global/Float/SoundFloatArithmetic`;
an exception names a path prefix such as `ContSet/Interval` and then admits only imports under
it),
`ContSet/` no dynamics, network or specification code, and nothing but `Examples/`
imports `HybridDynamics/`. `ContDynamics/`, `NN/` and `Specification/` import one
another and stay unordered. The imports that break a row are `LAYER_EXCEPTIONS`, each
with its reason; code is not moved to hide one, and an exception whose import is gone
is reported.

To change a guard on purpose, edit the file and the count in `GUARDED_FILES` in one
commit, and say in the commit message why the closure may now contain that theory. To
guard another file, add the marker comment, the guards and a `GUARDED_FILES` row. To
add a layering row, first measure that the tree satisfies it.

## Author blocks

Content files carry a CORA-style block between the module docstring and the
code:

```lean
-- Authors:       Claude Sonnet 5.5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---
```

`Authors:` names the model that wrote the file, as `Claude <Opus|Sonnet|Fable|Haiku>
<version>`: an agent writes its own model, and a model that substantially changes a
file someone else wrote appends itself, comma-separated. `Reviewed:` records human
reviews only, as lines `DD-Month-YYYY (Name)` oldest first, continuation lines
aligned to the value column; `---` means not yet reviewed. A change keeps the stamp
unless it is meaningful, and most changes are not: only a statement or definition that now
says something different, or a new proof idea, resets it to `---`. Moving declarations out,
renaming, changed notation, reformatting and reworded comments all keep it. A kept stamp
keeps its original date, so a later `Last update:` shows the file changed since its review.
`Last update:` itself moves only for a meaningful change (a statement, a definition, a proof
idea, real content); a rename, a `.1`/`.2` turned into a named field, a repointed import, a
comment edit or a move leaves it alone.
To review, run
`python3 scripts/review.py` (`--in ContSet/Zonotope` restricts it, `--main` picks only main-type files,
`--updated` picks only files updated since their last review, `--commit` commits each review)
or the VS Code task "Review a random Lean file or Basic.lean
section". A file added in the old
format is fixed by `python3 scripts/author-blocks.py`.

Files that only collect or re-export do not: every `API.lean`, `CORALean.lean`.
A `Basic.lean` carries one block per section instead of one for the file, each
directly under its section's banner; `review.py` then picks a random unreviewed
section, opens the file at its banner and writes `Reviewed:` into that block.
