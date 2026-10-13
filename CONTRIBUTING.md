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
    LinProg/       bounds on a linear objective, and what certifies them
  ContSet/         set representations, over whichever ambient type they suit
    ContSet/       the interface every representation instantiates
    InflatedContSet/  nominal part + error box, what a float representation adds
    WithEmpty/     a representation or nothing, for an operation whose result
                   can be empty where the representation cannot say so
    EmptySet/      `∅` in a stated dimension, a set class of its own as in CORA
    Fullspace/     the whole space, the same way; neither carries a scalar, so
                   both are Real/ only
    Interval/
      Real/        Interval.lean (the type), Operations/ (one per operation),
                   Theorems/ (one per guarantee),
                   Complexity/ (how large a result is, proved),
                   Cost/ (what running it costs, asserted),
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
    PolyZonotope/  generators carrying monomials: not convex, and exact under
                   quadMap; Real/ and Float/
    ConPolyZono/   the same with polynomial constraints on the factors, which is
                   what makes intersection exact; Real/ and Float/
    ZonoBundle/    a family of zonotopes denoting their intersection, exactly;
                   Real/ and Float/
    Ellipsoid/     a centre and a generator matrix, the one representation whose
                   support function is closed form; Real/ and Float/
    SpectraShadow/ the projection of a spectrahedron: exact under sum, image and
                   product, the representation a semidefinite program lands in;
                   Real/ and Float/
    Capsule/       a segment thickened by a ball, for an obstacle rather than a
                   reachable set: Real/ and Float/, being closed under almost nothing
    Taylm/         a polynomial over `[-1, 1]ⁿ` and a remainder interval, enclosing
                   a function rather than describing a set; Real/ and Float/
    Conversion/    one file per ordered pair, `<Source>_to_<Target>.lean`;
                   Real/ and Float/
  Specification/   what a computed set is checked against — a safe set or an
                   unsafe one — and why checking it on an outer approximation
                   answers for the exact set
  ContDynamics/    one directory per system class, written against the
                   interfaces alone
    Reach/         the reachability class every system instantiates, and how a
                   reach operation takes its arguments: CORA's `params` (the
                   problem) and `options` (the algorithm), as two structures
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
    NeurNetContrSys/  a plant closed around a network, whose input set is what
                   NN encloses; NeurNetContrSysDT/ steps a discrete plant
    OutputEq/      y = C x + D u, kept out of the system classes so that it
                   applies to all of them
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

A conversion goes in `Conversion/`, not in either representation: two
representations of equal standing cannot each import the other, so
`VPolytope → HPolytope` inside `VPolytope/` and the reverse inside `HPolytope/`
is a cycle Lean rejects. One file per ordered pair keeps a new pair to a file
rather than a directory, and keeps every representation independent of every
other. `Real/` holds every ordered pair of the nine representations its own
collector names — 72 files — and `Capsule_to_Interval` and the `Taylm` pairs
besides; `Float/` holds the pairs written so far. The declaration is named for the target, as in CORA,
where `interval(zonotope)` is how a zonotope becomes a box.

Two of those files hold a class instead of a conversion: `ContSet_to_Interval`
and `Interval_to_ContSet` are the pairs whose other side is a variable, for an
algorithm that must reach a box, or come back from one, without naming what it
is propagating. Only the representations that can do it without certificates
instantiate them, which is the same rule as everywhere else.

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
*class root*: beside them it holds its class file, `Instances.lean` and
`API.lean`, and nothing else. `ContSet/Conversion/` is the exception, a table of
pairs rather than a class. A `Definitions/` file declares types, `abbrev`s,
propositions, sets and `noncomputable` specifications; a computable `def`
returning data is an algorithm, and belongs in `Operations/`, as does any `def`
returning an `Option` — a search that can fail — and a theorem belongs in
`Theorems/`. All of this is checked, and the class roots not yet sorted are a
named list in the script, which only shrinks. Two things no script can see are
review items: whether a statement in `Theorems/` secretly holds only at ℝ, and
whether one in `Theorems/Real/` really needs ℝ.

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
`LinearSys.timeIntervalStep` at the exact interval matrices — the representation
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

### Notation

| | |
| --- | --- |
| `x ∈ s` | membership in what a representation denotes |
| `s₁ ⊞ s₂` | `plus`, and deliberately not `+`: it is only *outer*, so `construct (s₁ ⊞ s₂)` merely contains `construct s₁ + construct s₂` |
| `𝒵`, `ℐ` | the zonotope and interval-matrix families, for pinning `(S := 𝒵)` where the elaborator cannot read a family off one member |

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
compiler cannot: that an `aux_` name is used only in the file that declares it,
that an `API.lean` holds nothing but imports, that it collects its whole
directory unless its own docstring says which sibling it deliberately leaves
out, that no file imports its own directory's collector, that no `Real` file of
a representation reaches into `Float`, that a file under a representation's
`Real/` or any `Float/` declares the namespace its directory claims, that a class
root holds only its class file, `Instances.lean` and `API.lean`, that a
`Definitions/` file declares only meanings, that no `Real/` or `Float/` folder
sits outside `ContSet/` but a `Theorems/Real/` and `Global/Float/`, that a float
type is named as its exact twin, the layer being the namespace — no `GZonotope`,
no `StarSetFloat`, no abbreviation of a representation at `Vec` — that every
file carries a module docstring and
— unless it is a collector — a well-formed author block one line under it, that
nothing is `sorry` or a search tactic, that nothing outside the three files
named in the script is an `axiom` — the second holding `nearestUnsound` alone
and imported from nowhere outside `Examples/Bench/`, the third holding
`trustedFlint` alone — that every `maxHeartbeats` bump
carries a reason, that a `def` under `Cost/` is named for the cost it asserts,
that every `[N]` cited resolves, that the comment lengths and the comment
density above are respected, that every module is reachable from one of the
target roots, so a file written but never collected is caught rather than
silently left out of the build, and that `noncomputable` stays where it is
legitimate — see below.

`noncomputable` is checked against the rule the float layer exists to keep:
free in a representation's `Real/` layer, in the ℝ model of the scalar
interface, in a `Definitions/` file, which says what an object means and is
never run, and on an `aux_` declaration anywhere, since that is a helper
rather than something a caller runs. Everywhere else it needs a reason, on one
line of `scripts/noncomputable-allowlist.txt`: `spec:` for a specification
object with nothing to compute (a reachable set defined by trajectories, a
norm, a Hausdorff distance, a real-valued certificate), `cost:` for an asserted
running cost, `real-layer:` for the real half of a representation or an ℝ-only
part of a directory otherwise written over the scalar, or `pending #N:` for an
algorithm with no float refinement yet. Under `Float/` even the allowlist
does not reach: a float declaration is free only as that same kind of `aux_`,
because the whole point of the float layer is that it runs. An allowlist
entry that stops matching anything is itself an error, so the list only
shrinks honestly.

Every limit it applies is a named variable at the top of the script, set from
what the tree actually contains, so raising one is a decision rather than a
drift. Every message says what to do, not only what is wrong.

It is text only: no Lean, no build, no network, about a second — which is why it
runs on every commit rather than on request. Setting a clone up means

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

`scripts/check-references.py` checks `references/` against the tree: that every
paper cited has a page, that every link on a page resolves and lands on a file
that really cites that paper, that every result cited anywhere is a row, that a
row deferring to an earlier paper names a row that is really on that paper's
page and does not defer in a circle, that the README's counts are the counts,
that a paper's findings are listed where the index says they are, that every row's `Class` cell is one of the allowed values and gives a reason when it is not `correct`, that a `correct` row's note does not say the Lean theorem is other than the printed one (unless an `**As printed:**` marker says why the printed statement follows; see [references/README.md](references/README.md#the-class-column)), that a `—` row's note reads `— partial: <declarations that exist, linked>; missing: <what is left>` and its links resolve, that a complexity statement sits in a row of its own (see [references/README.md](references/README.md#the-class-column)), and that `experiments/paper/formalization-stats.json` is what `scripts/formalization-stats.py` writes from the tables (rerun it after a row changes). A coverage table is a claim about where
a theorem lives, which is the kind of prose that rots quietly; this is what
stops it. It runs beside the conventions, on the same hook and the same CI job.

Nobody types a count. After a row changes, `python3 scripts/check-references.py
--fix` writes the counts it computed into the README's cells. Everything else it
finds, it only reports.

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

Per representation, six kinds of file, and a file does only its own job. Scalar
models and systems follow the same shape:

| File | Holds |
| --- | --- |
| `<Name>.lean` | the structure it is named for, and what it denotes: `construct`, `toReal`, `Trajectory` |
| `Operations/*.lean` | one operation each, as CORA gives it a file each |
| `Theorems/*.lean` | one guarantee each, stated and proved together |
| `Complexity/*.lean` | how large a result is — a theorem, proved from the definition |
| `Cost/*.lean` | how much running it costs — a `def`, asserted against a model |
| `Instances.lean` | the class instances, whose fields *are* the guarantees |

A file is named after what it declares, not after the role it plays:
`Zonotope/Zonotope.lean` and `Operations/Reduce.lean`, as in CORA's
`@zonotope/zonotope.m` and `@zonotope/reduce.m`. `Instances.lean` is the
exception, a Lean instance having no name to use.

`Operations` stays a single file where splitting would not pay — `LinearSysDT`
has three, and `Dyadic`'s are one-line compositions.

"One each" is meant literally, and `check-conventions.sh` enforces it: a file
under `Operations/` or `Theorems/` declares exactly one public thing. What it
needs and nothing else uses is `aux_`; what the tree needs earns a file of its
own. `<Name>.lean` and `Instances.lean` sit outside the rule — a type is
declared with what it denotes, and instances have no names to collect — and so
do `Complexity/` and `Cost/`, whose files hold a claim per operation rather
than an operation, and are read as a table.

The rule is what keeps the table above true, and it is checked because a
convention nobody tests is one the tree drifts out of: a helper that quietly
grows a second user is the usual way a file stops doing only its own job.

### A size is proved; a running cost is asserted

`Complexity/` and `Cost/` look alike from outside and only one of them can be
wrong, so they are kept apart deliberately.

A **size** — how many generators an operation's result has — is a field of the
result, so `Zonotope.plus_h` is a `theorem` and its proof is `rfl` against the
structure instance in `Operations/`. A **running cost** is not derivable at all:
a Lean `def` says what is computed and never what computing it costs. So a cost
is stated against an explicit model, `Global/Cost.lean`, and justified in the
file's docstring by reading the operation's definition by hand. It is an axiom
in the informal sense, and must never be dressed as a theorem about the
definition.

Three things say which a reader is looking at, and the third is checked:

* the directory — `Complexity/` or `Cost/`;
* the form — a `theorem` about `.h`, or a `def` returning a `Cost`, a type that
  is not `ℕ` and so cannot be equated with a size by accident;
* the name — a public `def` under `Cost/` is `...Cost` or `...Bound`, which
  `check-conventions.sh` enforces.

Nothing under `Cost/` is proved `rfl` against an operation. What *is* proved
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

### `aux_`

What a file needs and nothing else uses carries the `aux_` prefix, as in CORA.
The test is mechanical: used outside its own file, or not.

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
nothing carry none of this — there is nothing to find.

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

A proof of **five lines or more** must carry one, and a shorter proof must
not: below that the `:= by` is still in view, and a flag on every two-line
proof would say only what the source already shows. Required and refused on
either side of one number, so the flag always means the same thing — and it
lands on roughly two theorems in five. No exact count is quoted here: it moves
with every proof written, and a figure CI cannot keep honest goes stale the
day after it is written.

It rides on a `theorem` or a `lemma` and on nothing else. A `def` that proves
something in a structure field — `Ellipsoid.supportBound`'s `le :=`, eight lines
of it — carries no flag however long that field runs, because the checker's
notion of a declaration does not reach inside one. So the count above is a count
of *theorems*, and a proof living in a `def` is invisible to it.

Its length is what it spans: from the `:= by` to the proof's last line, blank
lines inside it counted and the blank lines between it and whatever follows
not. A theorem proved by a structure instance — `... : sys.Trajectory … where`
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
cycle.

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

## The two layers

`Real` is the specification, `Float` the refinement, which obtains its soundness
guarantees by transitivity — so `Float` imports `Real`, never the reverse. A new
float operation pays its rounding into an interval error box via
`InflatedContSet`.

`𝕋` is the scalar a layer computes in — ℝ in `Real`, a machine scalar in `Float`.
`Global.Scalar` reads a matrix of it as a real one, which is how a guarantee
stated once covers both layers. Outside `ContSet/` the two layers are one
definition: `Global/Float/Instances/Real` instantiates the scalar interface at ℝ
with every rounding exact, so a generic algorithm at `𝕋 := ℝ` *is* the exact
one, and its soundness theorem, stated once, is both layers' guarantee.

**The float layer is part of the work, not a follow-up.** New work carries both
layers wherever it can, and a contribution that lands only the `Real` half must
say why in its module docstring — not as an apology, but because the reason is
usually informative: the operation is a specification with nothing to round, or
it needs a decidable order the float scalar has and ℝ does not, or the rounding
has a genuine design choice behind it. A real definition alone is a specification
of something no machine runs, and it is far cheaper to refine an operation while
its proof is still in hand than to come back to it.

### Two scalars a definition can be run at

`SoundFloatArithmetic` fixes no format, so the float layer has more than one
model. `Dyadic p` is exact integer arithmetic with an unbounded exponent: every
obligation is a theorem, nothing overflows, and a result computed there rests on
`propext`, `Classical.choice` and `Quot.sound` and on nothing else. Native
binary64 is Lean's `Float`, compiled to a machine double and fast — and opaque
in the logic, so the ten obligations are bundled into one property,
`TrustedHardware`, and assumed in one line in
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

The converse fails, and that is the method's whole cost: a specification that
fails on the computed set is not a counterexample, and the answer to it is a
tighter enclosure rather than an argument about the system.

Discharging the check is `Global.LinProg` again — a separating direction proves
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

### Lengths, which `check-conventions.sh` enforces

| | |
| --- | --- |
| module docstring, content file | 20 lines |
| module docstring, collector | 25 lines — it is the directory's entry point |
| docstring above a declaration | 3 lines; longer explanation belongs in the header |
| inline `--` comment | 1 line; two in a row is a paragraph in the wrong place |
| code with no comment | 20 lines, which is a *minimum* density and aimed at proofs |

The density check counts from the first declaration body in the file, not from
the top: a signature and the file preamble above it are not proof steps, so
neither has to carry a comment every 20 lines.

The module-docstring cap measures the prose only, up to a `## References`
heading: a bibliography is not text that grows the way an explanation does.

### References

A publication named in prose cannot be checked and cannot be looked up, so cite
it as CORA does — `[1]`, or `[1, Prop. 3.1]` — and define the number at the end
of the module docstring:

```
## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
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

**Cite where the result actually is.** Prefer the original paper: a *cumulative*
thesis reproduces its chapters as papers, so cite the paper rather than the
thesis — that is the case for Kochdumper's and Wetzlinger's. A monograph thesis
is different: where a result appears only there, as much of Althoff's 2010 does,
the thesis *is* the source and citing it is correct, not a fallback. A book is
equally fine where no paper stands behind the result — CORA cites one for the
matrix zonotope product, and so do we. Where none can be confirmed, leave the
section out; a blank is honest and a wrong citation is not.

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
aligned to the value column; `---` means not yet reviewed. To review, run
`python3 scripts/review.py` (`--in ContSet/Zonotope` restricts it, `--main` picks only main-type files,
`--commit` commits each review) or the VS Code task "Review a random Lean file". A file added in the old
format is fixed by `python3 scripts/author-blocks.py`.

Files that only collect or re-export do not: every `API.lean`, `CORALean.lean`.
