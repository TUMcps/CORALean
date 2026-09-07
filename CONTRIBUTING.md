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
  Specification/   what a computed set is checked against — a safe set or an
                   unsafe one — and why checking it on an outer approximation
                   answers for the exact set
  ContDynamics/    algorithms, written against the interfaces alone
    LinearSysDT/   discrete-time linear systems, and reachability
    NonlinearSys/  the representation and its trajectories; no reachability yet
    LinearSys/     continuous-time linear systems: the flow in closed form,
                   reachability at the sample times by sampling into
                   LinearSysDT, and an enclosure over a whole step
      MatExp/      enclosing e^{A dt}, which is what a step is taken against
  HybridDynamics/  locations, transitions and the automaton; a run alternates
                   flowing inside a location with jumping between them
  NN/              neural network verification: propagating an input set through
                   a graph of layers, and checking the result
    Layers/        the standard layers, one file each; every activation is a
                   `Relaxation` and nothing else
  Examples/        one worked example per component, proved and never run
    Demo/          the one executable, and the only place anything here is
                   evaluated rather than proved
```

A conversion goes in `Conversion/`, not in either representation: two
representations of equal standing cannot each import the other, so
`VPolytope → HPolytope` inside `VPolytope/` and the reverse inside `HPolytope/`
is a cycle Lean rejects. One file per ordered pair keeps a new pair to a file
rather than a directory, and keeps every representation independent of every
other. All twenty ordered pairs of `Interval`, `Zonotope`, `HPolytope`,
`VPolytope` and `ConZonotope` are there in both layers; the declaration is
named for the target, as in CORA, where
`interval(zonotope)` is how a zonotope becomes a box.

Two of those files hold a class instead of a conversion: `ContSet_to_Interval`
and `Interval_to_ContSet` are the pairs whose other side is a variable, for an
algorithm that must reach a box, or come back from one, without naming what it
is propagating. Only the representations that can do it without certificates
instantiate them, which is the same rule as everywhere else.

An operation may be *implemented* by conversion — `VPolytope.and` goes out to
halfspaces, where intersection is free, and comes back — and then imports these
files by exact path. That is a dependency, not a cycle: the conversion imports
the representation's own files, never its `API.lean`.

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
would have to invent it — which is what `HPolytope` would have had to do for a
Minkowski sum, having no rows to state one with. A theorem
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
that an `API.lean` holds nothing but imports, that no file imports its own
directory's collector, that no `Real` file reaches into `Float`, that a file
under `Real/` or `Float/` declares the namespace its directory claims, that every
file carries a module docstring and — unless it is a collector — a well-formed
author block one line under it, that nothing is `sorry`, `axiom` or a search
tactic, that every `maxHeartbeats` bump carries a reason, that every `[N]` cited
resolves, that the comment lengths and the comment density above are respected,
and that every module is reachable from one of the target roots, so a file
written but never collected is caught rather than silently left out of the build.

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

Three, all named in `lakefile.toml`, and `check-conventions.sh` walks the import
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
library cannot notice from the inside, because only a use site asks.

The **demo** runs, and is the only place a definition in this repository is ever
evaluated. Its output is committed as `scripts/demo-expected.txt` and
`check-demo.sh` diffs against it, so an enclosure that silently widens fails the
build. No theorem can do that job: `_outer` is as true of a box the size of the
state space as of a tight one, and the only way to tell those apart is to
compute one and look. `Dyadic` is exact integer arithmetic, so the committed
numbers do not depend on the machine, the compiler, or the order of anything.

So: an example says the library still *fits together*; the demo says it still
*computes, and computes tightly*. A change that loosens a bound passes every
example in the tree.

`lake exe demo` builds it as an executable, which has to link, and linking
against Mathlib means compiling the C emitted for every module it reaches. CI
and `check-demo.sh` therefore run the same `main` through the interpreter with
`lake env lean --run src/CORALean/Examples/Demo.lean`, which needs only the
oleans.

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

"One each" is meant literally, and `check-conventions.sh` enforces it: a file
under `Operations/` or `Theorems/` declares exactly one public thing. What it
needs and nothing else uses is `aux_`; what the tree needs earns a file of its
own. `<Name>.lean` and `Instances.lean` sit outside the rule — a type is
declared with what it denotes, and instances have no names to collect.

The rule is what keeps the table above true, and it is checked because a
convention nobody tests is one the tree drifts out of: a helper that quietly
grows a second user is the usual way a file stops doing only its own job.

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
theorem MatExp.constCorrectionMatrix_mem (A : Mat ℝ n n) (r : ℝ) (η : ℕ) :
    ‖…‖ ≤ r * MatExp.expRemainderBound (r • A) η := by -- --- PROOF ---
```

A proof of **five lines or more** must carry one, and a shorter proof must
not: below that the `:= by` is still in view, and a flag on every two-line
proof would say only what the source already shows. Required and refused on
either side of one number, so the flag always means the same thing — 495 of
them, on a little under half the theorems in the tree.

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

**The float layer is part of the work, not a follow-up.** New work carries both
layers wherever it can, and a contribution that lands only the `Real` half must
say why in its module docstring — not as an apology, but because the reason is
usually informative: the operation is a specification with nothing to round, or
it needs a decidable order the float scalar has and ℝ does not, or the rounding
has a genuine design choice behind it. A real definition alone is a specification
of something no machine runs, and it is far cheaper to refine an operation while
its proof is still in hand than to come back to it.

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

## Verification

An algorithm here returns a superset of a set nothing computes: the reachable
set of a system, the output set of a network. `Specification` is what turns that
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

### A notation's literal tokens are not available as identifiers

A notation's literal string tokens take those words out of circulation as
identifiers everywhere the notation is in scope — `and := Foo.and` fails to
parse if some in-scope notation spells out the token `and`. `scoped` does not
narrow this within the namespace tree: it stays active throughout its own
namespace *and every sub-namespace*, so scoping a notation to `CORALean`
still reaches every `CORALean.*` file, which is nearly the whole library.

`Global/Partition.lean` learned this the hard way: its two-part notation once
read `Split α into β and γ`, and the bare word `and` then blocked named-field
syntax on every `And` instance in the library. The fix is not scoping harder;
it is not choosing an English word in the first place. The notation now reads
`Split α into β ⊕ γ`, which is also the right connective on the merits, since
`Partition₂ α β γ` states exactly that `β ⊕ γ ≃ α`.

A class field named after an English word is worth checking against notations
in scope before naming.

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
