# CORA coverage

How much of CORA does CORALean answer? One table per CORA class, one row per CORA
method, so "is `zonotope/reduce` done?" is a lookup. The tables sit beside the
paper tables in [../README.md](../README.md) and are checked the same way, by
`scripts/check-references.py`, which CI runs.

**The unit is one method file**: `~/CORA/contSet/@<class>/<method>.m`,
`~/CORA/contDynamics/@<class>/<method>.m`, `~/CORA/hybridDynamics/@<class>/<method>.m` or
`~/CORA/specification/@<class>/<method>.m`, and for `others` `~/CORA/matrixSet/@<class>/<method>.m`, `~/CORA/discrDynamics/@<class>/<method>.m` or, for `converter/`, the files of a subdirectory. A class of `specification/` that CORA writes as one
file (`atomicProposition.m`, `kleene.m`, `signals/kleeneSignal.m`, ...) has no method files: its
rows are the `function`s of its `methods` blocks, constructor included, and the declarations of
an `Abstract` block (`logicSignal`); `Access = private` and `protected` methods and local
functions are implementation and have no row, as `private/` has none.
Files under `private/` are implementation helpers of those methods and have no row. The
constructor `<class>.m` is one row like any other: it counts for the class definition
(the structure and its denotation), and is `proved` when a theorem about that
denotation exists (convexity, closedness, compactness, a conversion lemma), not for
CORA's argument parsing. The abstract superclasses `contSet` and `contDynamics` are
tabulated too: CORALean's counterparts of their dispatching methods are the interface
classes of `ContSet/ContSet/Interfaces.lean` (`Plus`, `Mtimes`, `Intersection`, `Reduce`,
...), whose fields carry the guarantee, so such a row links the class.

The classes tabulated are every class under CORA's `contSet/`, `contDynamics/`,
`hybridDynamics/` and `specification/`. The group `specification` holds `specification`, `stl`,
`stlInterval`, `rtl`, the signals, the analyzers and the logics `kleene` and `fourValued`. The
neural networks of `nn/` (`nn/@neuralNetwork` and `nn/layers/`) are tabulated too.

The group `others` is shown in the paper only as one aggregate bar, with no per-class figure. It
holds three kinds of class:

* `matrixSet/`: `intervalMatrix`, `matZonotope`, `matPolytope` and `matrixSet`.
* `discrDynamics/`: `markovchain`, `partition`, and `ProbOccupancyPrediction`. The last is a
  traffic-prediction case study and no class. Its `@road` and `@simulation` classes are `road` and
  `simulation`, and its other functions are the table `ProbOccupancyPrediction`, with one row per
  file. Its example inputs `scenarios/`, `velocityProfiles/` and `vehicleModels/` have no rows, as
  CORA's `examples/` has none.
* `converter/`: one table per subdirectory, one row per `.m` file however deep, `private/`
  excluded. Every row is `io/conversion-to-matlab-objects`: file-format converters from and to
  SpaceEx, CommonRoad, CommonOcean, VNN-LIB and power-system files.

`global/` is not tracked: it holds helper functions (validation, numerics, printing), not classes.

CORALean has no matrix-set classes of its own. `matZonotope` is `Zonotope (Mat ℝ m n)`,
`intervalMatrix` is `Interval (Mat ℝ m n)` and `matPolytope` is `VPolytope (Mat ℝ m n)`. A row
links the generic declaration only where its theorem is stated at (or generically over) the matrix
ambient type and states the CORA operation's result.

A class with no counterpart in CORALean is tabulated all the same, every method `—` (or out of
scope for a reason that holds for it), so the denominator is CORA's, not ours. Those are
`spectraShadow`, `taylm`, `affine`, `levelSet`, `polygon`, `probZonotope`, `zoo`, `linProbSys`,
`nonlinDASys`, `nonlinearARX`, `abstractReset`, `linearReset`, `nonlinearReset` and
`hybridDynamics`.

Three classes are answered by differently named ones. `polytope` is answered by `HPolytope` and
`VPolytope`, `location` and `transition` by `Location` and `Transition`, and `contDynamics` by
`Reach` and `OutputEq`.

## The table

```
| Method | State | In CORALean | Note |
```

**State.** One of five:

| State | Meaning |
|---|---|
| `proved` | a real-layer definition and a theorem about it: an exact, outer or inner statement (or, for a property such as `isBounded`, the theorem that characterizes it), linked in the third cell. A definition alone is not `proved`. |
| `float` | `proved`, and runnable at float, by one of two routes (below). |
| `bound` | CORALean has a theorem about a **sound but different or looser** result than CORA's, so the row is better than `—` but is not CORA's method (definition below). The note says what differs. |
| `—` | not yet: nothing usable. A definition without a theorem lands here, and says so in the note. |
| `out-of-scope` | CORALean does not do this, for one of the reasons below. "Hard" is never a reason. |

**When a method is `proved` or `float` at all.** Only when the Lean definition *is* CORA's method: the same algorithm and the same outputs. Options or secondary outputs of CORA that the Lean definition does not model are stated in the note; if CORA's *main* output differs (a different set, a tighter or looser set, another default algorithm whose result is not the same set), the row is not `proved`/`float`.

**When a method is `bound`.** The row links a definition and a theorem (as `proved`) such that

* the result is a **sound** statement about the mathematical object CORA's method approximates (the exact set, function range or exponential, as the method's name and help text say): an outer approximation of it, or an inner one, and the theorem says so (it need not contain the particular set CORA's own, possibly different, enclosure returns); and
* the definition is **not** CORA's method: the result is coarser, or computed by a different algorithm than CORA's default. Coarser means, for example, a bounding box or interval hull where CORA returns a tight set, a larger remainder, an enclosure of a segment where CORA solves an LP, or a box where CORA builds eigen generators.

The note names what differs from CORA, first, in plain words ("box, CORA: eigen generators"; "different remainder"; "pieces: ..."). An empty note is refused, as is a `route b` note. A `bound` row has no float/real split of its own: one state keeps the tables and the figure simple, and whether the bound runs at float is read from its links (a `float:` part lists the float layer), as for any row; the float backlog is `proved` only. A `bound` row becomes `proved`/`float` when a definition that is CORA's method is added and linked. It is never used for a result that is merely a consequence of other pieces with no statement about CORA's output, or that is unsound.

A `proved` row that is not `float` is the **float backlog** (`needs_float` in
`experiments/paper/formalization-stats.json`).

**When a method counts as `float`.** A method is `float` iff it is `proved` and either

* **(a)** a float-layer counterpart exists with an outer (or inner) theorem: a computable
  definition, and a theorem about it, in a `Float/` directory or in a declaration or file with
  `Float` in its name. The row links them after `float:`.
  The float counterpart is CORA's method at float (the same algorithm, outward rounding), not a coarser bound of the same quantity and not a definition that takes as input what CORA computes;
  a certificate checked at float stands in for a solver call only where CONTRIBUTING's "Certificates, not algorithms" allows it; or
* **(b)** its definition is generic over the scalar `𝕋` (or over the set representation, whose
  scalar the instances carry), is computable (not `noncomputable`), and its soundness theorem is stated for that generic
  `𝕋` or representation, not only at ℝ. Such a method needs no `Float/` counterpart: at
  `Dyadic`/`Float` with float set representations the same definition runs and the same theorem is
  its soundness proof (`Examples/ReachFloat.lean`, `Examples/RunnableFloat.lean`). The row's note
  starts `route b —` and says what is generic, and the row links the generic definition besides the
  theorem.

Both are faithful to what is written: a theorem stated only at ℝ, a definition at the real layer
(`Real/`), a definition on the allowlist (a specification object, a cost, or an entry marked
`pending #1`, the continuous-time code at the real matrix exponential), or an instance no float
representation supplies (`Real.OfInterval`, which `Transition.jump` needs) keeps the row `proved`.
A row that links both a runnable and a non-runnable definition of CORA's method is as runnable as
its worst one. An interface class (`Plus`, `Contains`, `Reach`, ...) is `float` when a float
representation instantiates it. The theorem categories are not affected: a generic theorem is a
paper theorem or a lemma, never a "float refinement".

**In CORALean.** Links to the declarations, as `` [`Zonotope.plus`](path) `` — the text is
the declaration's name as written in the file, and the checker looks for it there. For
`—` the cell is `—`; for out of scope it is `n/a — <reason>`.

**Note.** Empty, or `definition only, no theorem: ...` on a `—` row, or
`cora-issue — <what CORA gets wrong>` (a part of the note, first or after a `;` or sentence end, so it may follow a `route a —` part) on a row where CORA's own implementation was found
unsound or wrong and CORALean does it differently on purpose. The part is the whole account: what the
CORA code does, a case in which it goes wrong (read from the source, not run, unless it was run), what the
formalization does instead, and the Lean witness, a link to the counterexample, or the reason there is none
(a MATLAB error, a name that does not resolve: "no Lean witness"). Only a result that is an
error of CORA is marked; a design difference is not one, and one that belongs to no single method stands in
[the departures table](#departures-from-cora-that-belong-to-no-single-method) at the end of this page.
A CORA bug is also an entry of `experiments/paper/cora-bugs.json`, which `scripts/check-findings.py` and
`scripts/formalization-stats.py` check against the rows.

## Out of scope

Only these, and the row says which:

| Reason | What it covers |
|---|---|
| `plotting/display` | `display`, `plot*`, `print*`, `getPrintSetInfo`, `printSet`, `viewGraph`: output for a person at a MATLAB prompt |
| `random/sampling` | `randPoint_`, `generateRandom`, `simulateRandom`, `createTestSuite`, `gridPoints`: results that are random draws or sample grids |
| `solver-dependent` | the method is an encoding for an external solver (`dynamicsEncodingMILP`), not a set operation |
| `io/conversion-to-matlab-objects` | `full`, `sparse`, `double`, `single`, `string`, `jsonencode`: conversions between MATLAB storage formats; also the file-format converters of `converter/` (SpaceEx, CommonRoad, CommonOcean, VNN-LIB, power-system case files), which parse an external file into CORA objects or write one |
| `matlab-runtime` | MATLAB language plumbing: `copy`, `isemptyobject`, `size`, `length`, `subsref`, `subsasgn`, `reshape`, `parfor` variants, function-handle generators; also `eq`, `ne` and `isequal` of system, reset, location, transition and automaton objects, which compare MATLAB objects field by field (structural equality, not a mathematical claim; `isequal`/`eq` of two sets is one and stays in scope) |
| `deprecated` | the method's own help text says `DEPRECATED` |

Rulings on borderline cases:

* **Specification objects: `isequal`, `eq`, `ne` of `specification`, `stl`, `rtl` and `syntaxTree`, and `subsref` of `stl`** are `matlab-runtime` (they compare or index MATLAB objects field by field); `isequal` of `stlInterval` compares two intervals and stays in scope. `disp` and `toStr` are `plotting/display`; `robustnessEncodingMILP` is `solver-dependent`.
* **eventFcn** (polytope, fullspace, levelSet, location, transition) is `matlab-runtime`, note "ODE event callback": it returns the value, `isterminal` and `direction` of MATLAB's `ode45` event interface.
* **Field setters and getters** (taylm `set`, `setName`, polytope `setVertices`, nn `getOrderPattern`, probZonotope `center`) are `matlab-runtime`, note "field setter" or "field getter".
* **Validating wrappers** of an abstract `<m>_` (contSet `cartProd`, `convHull`, `lift`, `projectHighDim`, `volume`, `norm`, `representsa`, `boundaryPoint`) are `matlab-runtime`, note "validating wrapper of `<m>_`": argument checks, defaults, an empty-set fallback in a `try/catch`, and one call to `<m>_` (`boundaryPoint` throws). A wrapper with real per-class content stays in scope.
* **Route b for verdicts and merges** is accepted where the definition is generic over `Scalar 𝕋` and computable and the guarantee is stated for that `𝕋`: `mergeInvariants` (guarantee `Lifting.mem_inv`) and hybridDynamics `verify` (`HybridAutomaton.holds_of_check`), as for the sibling rows already `float`.
* **R-S: constructor rows of scalar-carrying structures** count as `float` by route b when the structure is generic over `Scalar 𝕋`, computable, and the row's theorem is stated for it: `linearARX` (`LinearARX 𝕋`, with the computable `toLinearSysDT`) and `neurNetContrSys` (`NeurNetContrSys (LinearSys 𝕋 n)`). Not for structures whose `f` is a real function (`nonlinearARX`, `nonlinearSysDT`).
* **R-FB: `FloatBound` is the float side of `SupportBound`.** The abstract contSet rows `supportFunc` and `supportFunc_` are `float` by route b through that interface, which each float class instantiates by its `boundDot`.
* **R-FB-contains: `le` and similar comparison rows count as `float` by route b** through the `Contains`/`IsDisjoint` classes (`le` is `contains_` with the operands swapped) when the float class instantiates them with a soundness theorem; the note says `route b —`, and discloses where the instances stop (polytope `le`: the float instances take the polytope as container).
* **R-SF: scalar-free Bool and constant rows are `float` by route b** (emptySet and fullspace `isBounded`, `isFullDim`, `center`, `radius`, `volume_`, `enclosePoints`, the constructor rows) when the Lean definition is computable and generic: it holds no scalar, so there is nothing to round, and the note says `route b (scalar-free) —`. A row whose result is `Inf` (fullspace `radius`, `volume_`, `supportFunc_`) stays `proved`, as does one with no computable definition (fullspace `representsa_`, a family of statements over CORA's type names).
* **R-LS: symbolic levelSet rows are `float` by route b** (`Inf`, `empty`, `and_`, `lift_`, `splitEquality`, the constructor) only when the Lean definition is computable and never evaluates the real function: it restructures the symbolic data (lists appended, variables renamed, rows filtered). `not` (negates the function) stays `proved`; `contains_` (whose real test evaluates the function) is `float` only by route a, the function's values entering as stored float bounds assumed to enclose them, as for `isIntersecting_` and `representsa_`.
* **R-SIM: a DT `simulate` row is `float`** when an interval-valued run `simulateBox` (the system's step applied to float `Interval.point` start and inputs, with directed rounding) is linked with `simulate_mem_simulateBox` (the real trajectory lies in the float boxes): linearSysDT, linearARX and neurNetContrSys. The guarantee is an enclosure, so the row note says "outer". Not for nonlinearSysDT and nonlinearARX, whose `f` is a real function with no interval step.
* **Alias-stale rows** are linked to the declaration that already exists under another row: linearReset `nonlinearReset` (`Transition.toNonlinearReset`, `NonlinearReset.evaluate_toNonlinearReset`) and conZonotope `enclose` (the generic `ContSet.enclose`, as the float `ConZonotope` has `Plus`, `LinComb` and `Mtimes`).
* **`deprecated` also covers a method that itself emits `CORAwarning('CORA:deprecated')`**, even if its help text does not say `DEPRECATED` (polygon `simplify`).
* **`matlab-runtime`, further rows:** nonlinearSys `taylor` (symbolic derivative code generation), nn `instantiateFromString` (string dispatch), contSet `representsa_emptyObject` (dispatch on `isemptyobject`), contSet `compact` and `vertices` (validating wrappers of `compact_` and `vertices_`), nn `nnGNNLayer` (abstract class constructor). **`random/sampling`, further rows:** polytope `reduce` (its only method is `'rand'`), zonotope `orthVectors` (random completion columns). capsule `vertices_` stays in scope: a deterministic arc grid, not a random draw. **`matlab-runtime`, polyshape library calls:** polygon `enclosePoints` (one call of `boundary`, an alpha-shape shrink-wrap) and `expandBoundaries` (one call of `polybuffer`), each a single MATLAB routine whose floating-point polygon comes with no enclosure statement.
* **R-CTSIM: continuous-time `simulate` rows that call `ode45` or `ode15s` stay `—`** (linearSys, nonlinearSys, nonlinParamSys, nonlinDASys): formalizing them as the exact flow would claim more than the numerical integrator computes. The same holds for the rows that run the continuous `simulate` per location: hybridAutomaton, location and parallelHybridAutomaton `simulate`, and hybridAutomaton `bestInitialMode` (which also resamples by `interp1`).
* **Optimiser-driven workflows are `solver-dependent` when the result is determined by an external optimiser or a training loop** (`fmincon`, `linprog`, `quadprog`, genetic programming, decision-tree learning, a training loop): `falsify` (linearSys, linearSysDT, nonlinearSys, nonlinearSysDT, hybridAutomaton: a solver and wall-clock search), `confSynth_dyn`, `confSynth_gray`, `conform`, `estimateParameter`, nonlinearARX and hybridAutomaton `identify`, nn `train`. A method whose body is computed from sets or by a closed form stays in scope: `computeGO` (deterministic stacked output matrices), `isconform` and `isconform_dyn` (halfspace containment of unified outputs), and `identify` of the linear and nonlinear continuous or discrete systems (default algorithm `dmd`, an SVD fit; `opt`/`nested`/`sparse` are further options).
* **nn `backpropZonotopeBatch_` and the activation layer's `backpropZonotopeBatch` are `solver-dependent`**: the gradient step of the set-based training loop (stored slope variables, generator ranking, weight updates), as `train`; the `neuralNetwork` `backpropZonotopeBatch` is a validating wrapper, `matlab-runtime`. **nn `enumerateLayers` and `prepareForZonoBatchEval` are `matlab-runtime`**: bookkeeping on layer handle objects (flattening nested composite layers into cell arrays and index vectors, caching generator and neuron ids in the layers), no set semantics; a `NeuralNetwork` is a flat chain.
* **R-WE: `empty` of a representation that cannot denote `∅`** (zonotope, ellipsoid, polyZonotope) is answered by `OptEmpty.empty`, the wrapper's own empty member, and counts as `float` by route b (scalar-free). The wrapper holds no scalar and is generic over the class, and `OptEmpty.construct_empty` says it denotes `∅`. The note says why the representation itself has no such member: the zonotope's center and the polynomial zonotope's factor vector `0` are always members, and an ellipsoid has no empty shape.
* **R-PG: a polygon denotes its region; methods are formalized against the region given as convex pieces.** CORA's `polyshape` boundary (vertex lists with holes) is not converted to convex pieces, so a method whose result is defined by the boundary representation itself stays `—` with the reason "boundary representation (R-PG)". Such results are the vertex order, collinear-point removal, triangulation output, `expandBoundaries` and boundary vertex counts. The exception is a region-level statement that captures the method honestly: `isFullDim`, `isIntersecting_`, `isConvex`, `volume_`, `splitIntoConvexSets`, `isequal` one-sided, and `triangulation`, a cover of the region by vertex triangles. Also `subtract`, `mldivide` and `minkDiff`, the regularized difference as a region, `hausdorffDist`, the point branch, and `quadMap`, the images of those triangles. The row note says which region statement is proved and that the boundary computation is not.
* **R-VS: capsule `vertices_` returns sampled boundary points, not vertices** (a capsule has none): `proved` (or `float`) only with a theorem that the returned points lie on the boundary (`Capsule.vertices_mem_frontier`), and the row note says "points on the boundary, not vertices"; no exactness is claimed, the hull of the points is inside the capsule, not equal to it.

## Counts

<!-- coverage-counts -->
| Class | Group | Methods | proved | float | bound | not yet | out of scope | CORA issues |
|---|---|---|---|---|---|---|---|---|
| [affine](contSet/affine.md) | contSet | 1 | 0 | 1 | 0 | 0 | 0 | 0 |
| [capsule](contSet/capsule.md) | contSet | 39 | 0 | 26 | 3 | 0 | 10 | 9 |
| [conPolyZono](contSet/conPolyZono.md) | contSet | 47 | 1 | 30 | 7 | 1 | 8 | 4 |
| [conZonotope](contSet/conZonotope.md) | contSet | 50 | 1 | 31 | 6 | 1 | 11 | 6 |
| [contSet](contSet/contSet.md) | contSet | 101 | 1 | 28 | 0 | 0 | 72 | 0 |
| [ellipsoid](contSet/ellipsoid.md) | contSet | 50 | 3 | 33 | 2 | 0 | 12 | 8 |
| [emptySet](contSet/emptySet.md) | contSet | 30 | 2 | 21 | 0 | 0 | 7 | 0 |
| [fullspace](contSet/fullspace.md) | contSet | 33 | 5 | 20 | 0 | 0 | 8 | 1 |
| [interval](contSet/interval.md) | contSet | 110 | 0 | 92 | 0 | 0 | 18 | 5 |
| [levelSet](contSet/levelSet.md) | contSet | 22 | 4 | 9 | 0 | 0 | 9 | 3 |
| [polyZonotope](contSet/polyZonotope.md) | contSet | 73 | 1 | 52 | 2 | 3 | 15 | 10 |
| [polygon](contSet/polygon.md) | contSet | 46 | 1 | 32 | 0 | 2 | 11 | 10 |
| [polytope](contSet/polytope.md) | contSet | 58 | 3 | 39 | 3 | 1 | 12 | 10 |
| [probZonotope](contSet/probZonotope.md) | contSet | 28 | 2 | 15 | 2 | 0 | 9 | 5 |
| [spectraShadow](contSet/spectraShadow.md) | contSet | 33 | 0 | 24 | 0 | 0 | 9 | 6 |
| [taylm](contSet/taylm.md) | contSet | 51 | 1 | 27 | 11 | 0 | 12 | 1 |
| [zonoBundle](contSet/zonoBundle.md) | contSet | 44 | 3 | 31 | 3 | 0 | 7 | 6 |
| [zonotope](contSet/zonotope.md) | contSet | 80 | 4 | 57 | 5 | 0 | 14 | 16 |
| [zoo](contSet/zoo.md) | contSet | 12 | 0 | 10 | 0 | 0 | 2 | 2 |
| [contDynamics](contDynamics/contDynamics.md) | contDynamics | 19 | 1 | 6 | 1 | 0 | 11 | 4 |
| [linParamSys](contDynamics/linParamSys.md) | contDynamics | 11 | 1 | 6 | 0 | 0 | 4 | 3 |
| [linProbSys](contDynamics/linProbSys.md) | contDynamics | 8 | 3 | 0 | 0 | 0 | 5 | 1 |
| [linearARX](contDynamics/linearARX.md) | contDynamics | 7 | 1 | 4 | 0 | 0 | 2 | 0 |
| [linearSys](contDynamics/linearSys.md) | contDynamics | 33 | 1 | 21 | 0 | 1 | 10 | 3 |
| [linearSysDT](contDynamics/linearSysDT.md) | contDynamics | 17 | 4 | 7 | 0 | 0 | 6 | 2 |
| [neurNetContrSys](contDynamics/neurNetContrSys.md) | contDynamics | 5 | 0 | 4 | 0 | 0 | 1 | 0 |
| [nonlinDASys](contDynamics/nonlinDASys.md) | contDynamics | 13 | 5 | 4 | 0 | 1 | 3 | 5 |
| [nonlinParamSys](contDynamics/nonlinParamSys.md) | contDynamics | 9 | 1 | 3 | 0 | 1 | 4 | 1 |
| [nonlinearARX](contDynamics/nonlinearARX.md) | contDynamics | 8 | 0 | 5 | 0 | 0 | 3 | 1 |
| [nonlinearSys](contDynamics/nonlinearSys.md) | contDynamics | 18 | 3 | 6 | 0 | 1 | 8 | 2 |
| [nonlinearSysDT](contDynamics/nonlinearSysDT.md) | contDynamics | 11 | 1 | 7 | 0 | 0 | 3 | 2 |
| [abstractReset](hybridDynamics/abstractReset.md) | hybridDynamics | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| [hybridAutomaton](hybridDynamics/hybridAutomaton.md) | hybridDynamics | 15 | 0 | 2 | 0 | 2 | 11 | 1 |
| [hybridDynamics](hybridDynamics/hybridDynamics.md) | hybridDynamics | 2 | 0 | 1 | 0 | 0 | 1 | 0 |
| [linearReset](hybridDynamics/linearReset.md) | hybridDynamics | 10 | 0 | 7 | 0 | 0 | 3 | 0 |
| [location](hybridDynamics/location.md) | hybridDynamics | 24 | 0 | 13 | 2 | 1 | 8 | 6 |
| [nonlinearReset](hybridDynamics/nonlinearReset.md) | hybridDynamics | 9 | 0 | 5 | 0 | 0 | 4 | 2 |
| [parallelHybridAutomaton](hybridDynamics/parallelHybridAutomaton.md) | hybridDynamics | 13 | 0 | 6 | 0 | 1 | 6 | 3 |
| [transition](hybridDynamics/transition.md) | hybridDynamics | 12 | 0 | 5 | 0 | 0 | 7 | 1 |
| [layers](nn/layers.md) | nn | 43 | 0 | 39 | 0 | 0 | 4 | 10 |
| [neuralNetwork](nn/neuralNetwork.md) | nn | 61 | 2 | 18 | 0 | 0 | 41 | 2 |
| [atomicProposition](specification/atomicProposition.md) | specification | 5 | 0 | 5 | 0 | 0 | 0 | 0 |
| [finiteKleeneSignalBuilder](specification/finiteKleeneSignalBuilder.md) | specification | 4 | 0 | 4 | 0 | 0 | 0 | 0 |
| [finiteSignal](specification/finiteSignal.md) | specification | 10 | 0 | 9 | 0 | 0 | 1 | 0 |
| [fourValued](specification/fourValued.md) | specification | 5 | 0 | 5 | 0 | 0 | 0 | 0 |
| [fourValuedSignal](specification/fourValuedSignal.md) | specification | 18 | 0 | 16 | 0 | 0 | 2 | 0 |
| [kleene](specification/kleene.md) | specification | 4 | 0 | 4 | 0 | 0 | 0 | 0 |
| [kleeneSignal](specification/kleeneSignal.md) | specification | 15 | 0 | 13 | 0 | 0 | 2 | 0 |
| [logicSignal](specification/logicSignal.md) | specification | 10 | 0 | 0 | 0 | 0 | 10 | 0 |
| [onlineAnalyzerNode](specification/onlineAnalyzerNode.md) | specification | 7 | 0 | 4 | 0 | 0 | 3 | 0 |
| [onlineReachSetAnalyzer](specification/onlineReachSetAnalyzer.md) | specification | 5 | 0 | 4 | 0 | 0 | 1 | 0 |
| [pointSegmentSignal](specification/pointSegmentSignal.md) | specification | 11 | 0 | 10 | 0 | 0 | 1 | 0 |
| [reachSetAnalyzer](specification/reachSetAnalyzer.md) | specification | 5 | 0 | 5 | 0 | 0 | 0 | 1 |
| [rtl](specification/rtl.md) | specification | 5 | 0 | 4 | 0 | 0 | 1 | 0 |
| [specification](specification/specification.md) | specification | 14 | 0 | 2 | 0 | 6 | 6 | 2 |
| [stl](specification/stl.md) | specification | 52 | 2 | 30 | 0 | 15 | 5 | 4 |
| [stlInterval](specification/stlInterval.md) | specification | 19 | 1 | 16 | 0 | 0 | 2 | 1 |
| [syntaxTree](specification/syntaxTree.md) | specification | 27 | 0 | 27 | 0 | 0 | 0 | 3 |
| [tentativeKleeneSignal](specification/tentativeKleeneSignal.md) | specification | 6 | 0 | 5 | 0 | 0 | 1 | 0 |
| [trajectoryAnalyzer](specification/trajectoryAnalyzer.md) | specification | 2 | 0 | 2 | 0 | 0 | 0 | 0 |
| [ProbOccupancyPrediction](others/ProbOccupancyPrediction.md) | others | 25 | 0 | 0 | 0 | 21 | 4 | 0 |
| [commonocean2cora](others/commonocean2cora.md) | others | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| [commonroad2cora](others/commonroad2cora.md) | others | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| [cora2spaceex](others/cora2spaceex.md) | others | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| [intervalMatrix](others/intervalMatrix.md) | others | 39 | 3 | 20 | 1 | 5 | 10 | 3 |
| [markovchain](others/markovchain.md) | others | 12 | 5 | 0 | 0 | 2 | 5 | 1 |
| [matPolytope](others/matPolytope.md) | others | 20 | 4 | 7 | 0 | 1 | 8 | 5 |
| [matZonotope](others/matZonotope.md) | others | 33 | 3 | 13 | 4 | 3 | 10 | 3 |
| [matrixSet](others/matrixSet.md) | others | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| [neuralnetwork2cora](others/neuralnetwork2cora.md) | others | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| [partition](others/partition.md) | others | 12 | 3 | 7 | 0 | 0 | 2 | 0 |
| [powerSystem2cora](others/powerSystem2cora.md) | others | 2 | 0 | 0 | 0 | 0 | 2 | 0 |
| [road](others/road.md) | others | 15 | 0 | 0 | 0 | 9 | 6 | 0 |
| [simulation](others/simulation.md) | others | 7 | 0 | 0 | 0 | 4 | 3 | 0 |
| [spaceex2cora](others/spaceex2cora.md) | others | 40 | 0 | 0 | 0 | 0 | 40 | 0 |
<!-- /coverage-counts -->

`python3 scripts/check-references.py --fix` rewrites the table above.

## What the check does

* every method file of a tabulated class has a row, and a row names a method file: the
  method lists are in [cora-inventory.json](cora-inventory.json), committed so CI needs no
  CORA checkout, and compared with one (`CORA_DIR`, default `~/CORA`) where it exists;
* the state is one of the five, the out-of-scope reason one of the six;
* every link points at a Lean file that exists and declares the named declaration;
* a `proved` or `bound` row links a theorem (or a class whose fields carry the guarantee), a `bound` row's note says what differs. A `float` row links a float-layer definition and a float-layer theorem (route a), or carries a `route b —` note whose linked definitions are outside `Real/`, not `noncomputable`, not on the
  allowlist, and whose theorem or class names a scalar or a set representation (route b).
* a `proved` row is not stale: it fails when its linked definition already counts as `float`, so the figure cannot lag behind the code. The definition counts by route a when the row's own definition, the first it links, has a `…Float` twin, `opFloat` or `opFloat?`, that a float-layer theorem is about. A helper linked after it has no say, except on the constructor row, which stands for the whole class. It counts by route b when every linked definition is outside `Real/`, computable, not a `Prop` and generic over `𝕋` in its signature, and a linked theorem is stated for `𝕋`.
* the counts above are the tables' counts, and `experiments/paper/formalization-stats.json`
  is what `scripts/formalization-stats.py` writes now.

What it cannot check is that the *right* declaration is linked for a CORA method: that is a
judgement, made when the row is written, and argued with in review.

## Which class a paper result lands on

The paper tables' `Class` column says how the paper's statement fared. The figure in the
paper breaks that down by CORA class, by the first Lean file the row links:
`ContSet/Zonotope/...` is `zonotope`; `ContSet/Conversion/.../Zonotope_to_Interval.lean` is
`zonotope` (the conversion is the source's method). `ContSet/ContSet`, `SetUnion`,
`SetIntersection`, `InflatedContSet`, `OptEmpty` are `contSet`;
`ContDynamics/LinParamSys` and `LinParamSysDT` are `linParamSys`, `NeurNetContrSys` and
`NeurNetContrSysDT` are `neurNetContrSys`, `OutputEq` and `Reach` are `contDynamics`;
`HybridDynamics/Parallel` is `parallelHybridAutomaton` and the rest of `HybridDynamics/` is
`hybridAutomaton`. Files that belong to no CORA class land in `global` (`Global/`),
`neuralNetwork` (`NN/`) or `specification` (`Specification/`).

## Departures from CORA that belong to no single method

Where this formalization deliberately parts from CORA or from its sources in a way that is not one
CORA method's `cora-issue` (those stand in the method's own row, in the tables above). A line each —
the linked file's module docstring carries the argument; a `—` stands where nothing is formalized
and the row is the whole argument. An error in a paper is not here: it lives on that paper's page
under [references/](../README.md), beside the result it is about.

**What belongs here.** Settled facts, which will not change: this formalization does something
differently on purpose. Anything with work still to do goes to the issue tracker instead, under
its label. A departure can give rise to both: it is recorded here, the closing of it is an issue.

| Subject | What differs | Details |
|---|---|---|
| Float until: the time shift rounded inward | CORA's untils shift a time interval by `minus` in doubles, rounded to nearest. A float until that is `True` only where the exact one is needs the shift inside the exact one: `minusInward` rounds the lower bound of the difference up and the upper one down. The point-segment until takes it for a signal true only where the exact one is and `minus` (rounded outward) for one true wherever it is; the Kleene and four-valued untils take the first for their minimal refinement and the second for their maximal one, so their `True` and `False` are exact ones. The finite-signal until rounds its `((lint(i) & rint(j)) - int) & lint(i)` inward, tests `lb - ub <= eps` on the difference rounded up, and drops a piece whose ends cross rather than turning it around, as CORA's `min`/`max` of the ends would. | [`MinusInward.lean`](../../src/CORALean/Specification/STLInterval/Operations/MinusInward.lean), [`UntilFloat.lean`](../../src/CORALean/Specification/PointSegmentSignal/Operations/UntilFloat.lean), [`UntilFloat.lean`](../../src/CORALean/Specification/KleeneSignal/Operations/UntilFloat.lean), [`UntilFloat.lean`](../../src/CORALean/Specification/FiniteSignal/Operations/UntilFloat.lean) |
| Float `withinTol` decided exactly | CORA evaluates `withinTol(a,b,tol)` in doubles. The float specification operations decide it on the reals the stored values denote (`ExactLe.withinTol`, from the exact decoding into ℚ), so a test of time stamps goes the way the exact one goes on the same stored values, and the online analyzer's float operations read as reals are the exact ones. | [`Interfaces.lean`](../../src/CORALean/Global/Float/Interfaces.lean), [`WithinTolFloat.lean`](../../src/CORALean/Specification/STLInterval/Operations/WithinTolFloat.lean) |
| Float factors that may reach a polytope, clipped to the box | The polytope `K` of Kochdumper and Bak's `Prop. 2` is unbounded in the factors, and its rows `C G(·,H)` rounded to floats miss the real ones by an error that only a bound on the factors absorbs. The float polytope is therefore read with the factor box `[-1, 1]^p`, where the paper's statement and every use of the factors stay, and its offset pays the rounding gap of the rows on that box. CORA computes the rows in doubles and does not clip. | [`UnsafeFactorsFloat.lean`](../../src/CORALean/Specification/STL/Operations/UnsafeFactorsFloat.lean), [`UnsafeFactorsFloatOuter.lean`](../../src/CORALean/Specification/STL/Theorems/UnsafeFactorsFloatOuter.lean) |
| Homogeneous time-interval step | `linComb` in place of CORA's convex hull, so a non-convex representation keeps its shape. | [`TimeInterval.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/TimeInterval.lean) |
| `ConPolyZono.union` | The source states its union identity with no hypothesis on the operands, and it is false without one: an all-zero exponent column is a degree-`0` monomial, so it survives on the branch that pins its own operand's factors to `0` and is added twice. Formalized with `HasNoZeroCol` on all four exponent matrices — the half of the source's `regular` its own proof uses, the duplicate-free half being irrelevant here. One further hypothesis is this representation's rather than the source's: neither operand carries independent generators, which the source's representation cannot. | [`UnionExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/UnionExact.lean) |
| `ConPolyZono.convHull` | The source states its convex hull identity with no hypothesis on the operands, and it is false when exactly one of them is empty. The step that replaces the union by the linear combination needs a point of the *other* operand to pair with. The closed form carries that combination's constraint system `n + 1` times over, so it is empty whenever either operand is while the hull is not. Formalized with both operands non-empty, which is what that step actually asks for; CORA guards the same case by returning the other set outright. One further hypothesis is this representation's rather than the source's: neither operand carries independent generators, which the source's representation cannot. | [`ConvHullExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/ConvHullExact.lean) |
| `ConPolyZono.reduceCon` | The two cleanups the source appends, `compactGens` and dropping the all-zero exponent rows, change the representation and not the set, and are left to their own operations. | [`ReduceConOuter.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/ReduceConOuter.lean) |
| `ConZonotope.eliminate` | The source's `Thm. 2` states its identity `Zc = Zr` from `a_{r,c} ≠ 0` and `R_{r,c} ⊆ [-1,1]` alone. Its own proof of the `⊆` direction solves row `r` for the eliminated coefficient from the *other* coordinates and bounds it via `R_{r,c}`. That needs those coordinates already known within their own `E_k`, not merely within `[-1,1]`. The proof never argues this step, and Algorithm 1's Gauss-Seidel passes can make it false without more (a worked 2×2 counterexample is on the paper's page). Formalized with a dependency-closure hypothesis on a set `S` — the columns row `r` reads besides `c`, `c` excluded, closed under what every row reads from `S` — the same closure `tighten_outer_safe` already carries, and what the source's own procedural remark (apply Gauss-Jordan with full pivoting first) gestures at without ever stating it as a hypothesis or connecting it to the proof. | [`EliminateExact.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/EliminateExact.lean) |
| `abstrErr`'s region | Alg. 2 computes the region its Lagrange remainder is taken over, by `zono` of a Cartesian product; here it is supplied, as `lagrangeRemainder` and `abstrErrLin` already take theirs. The source asserts its property (6) of every operation it uses, and that is false of `zonotope`, which returns a function of the representation rather than of the set — so computing the region would put a refutable assumption inside the definition, where `Lemma 3` could not be proved without it. | [`AbstrErr.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/AbstrErr.lean) |
| Abstraction error of a linearization | `A` and `B` need not be the Jacobians; any pair admits a certificate. | [`IsAbstractionError.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Definitions/IsAbstractionError.lean) |
| Linearization error as an input | Althoff, Stursberg and Buss (CDC 2008, Sec. IV-A) compute the linearized system's reachable set without the error and add the error's own, `R_lin ⊕ R_err`, by superposition. Here the error set `L` joins the input set (`linInput`) and the linearized system is run once: a confined nonlinear run is one of its runs. The split form needs the run's input divided into a measurable linear part and a measurable error part, and a run here carries no measurable input — only its derivative is — so it is not stated. | [`Linearize.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/Linearize.lean), [`ReachOuter.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ReachOuter.lean) |
| Float nonlinear abstraction error | CORA's `'lin'` (`priv_abstrerr_lin`) bounds the remainder by the second-order Lagrange term from an interval Hessian. A `FloatHessModel` run does the same (`hessRemainder`), plus the first-order slack of linearizing at the centers of the Jacobian box rather than at the Jacobian. Details below. | [`SlopeRemainder.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/SlopeRemainder.lean), [`HessRemainder.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/HessRemainder.lean), [`AbstrErrPolyFloat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/AbstrErrPolyFloat.lean), [`RegionFloat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/RegionFloat.lean) |
| Float `Zonotope.reduceGirard` | `sortPerm` in place of `Tuple.sort`: no float type is a `LinearOrder`. | [`ReduceGirard.lean`](../../src/CORALean/ContSet/Zonotope/Float/Operations/ReduceGirard.lean) |
| `PolyZonotope.mul` | Exactness is over `point`, not `construct`. | [`MulExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MulExact.lean) |
| Polynomial zonotope identifiers | No identifier vector: the dependent factors of a `PolyZonotope` are positional, `Fin p`, and two sets share a factor exactly when they share its index, so Kochdumper and Althoff's `mergeID` (TAC 2021, Prop. 1) has no lookup or permutation to do. What remains of it is padding the shorter factor list with zero exponent rows, which is exact. | [`PadBackExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/PadBackExact.lean) |
| `PolyZonotope.quadMap` with independent generators | Exact: every independent generator is made dependent first, so the quadratic map of the whole set is computed with no `zono()` enclosure of the cross terms the extended factors produce. Kochdumper and Althoff (TAC 2021, Prop. 13) trade that exactness for fewer factors and print the over-approximation; the tree keeps the exact map, as it does for `evalPoly` ([the coverage README](README.md#departures-from-cora-that-belong-to-no-single-method)). | [`QuadMapExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/QuadMapExact.lean) |
| A polynomial applied to a polynomial zonotope | `evalPoly` runs on `absorbRounding` first, so every independent generator becomes an exact one rather than spending a fresh independent factor on the cross terms a closed-form quadratic map would otherwise bound. | [`ActivationPoly.lean`](../../src/CORALean/NN/Layers/Operations/ActivationPoly.lean) |
| `PolyZonotope.getSubset` | One factor per call, and every generator expanded to a uniform `maxExp + 1` columns rather than to its own degree, so the generator index stays a product type; the surplus columns carry `Nat.choose e j = 0` and are `compact`'s to drop, as are CORA's constant-column fold and its point return. | [`GetSubset.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/GetSubset.lean) |
| Inverse square root, TMLR'25 Lemma 2 | The source computes `max \|f - p\|` exactly at the critical points; `Relaxation` asks only for a sound error at any slope, and `invSqrtRelaxation` bounds rather than attains it. | [`InvSqrtRelaxation.lean`](../../src/CORALean/NN/Layers/Definitions/InvSqrtRelaxation.lean) |
| Input solution over a time interval | The split of the input set is a hypothesis of the generic theorem; `Recenter` and `OfPoint` are the interface a representation supplies it from, and `Zonotope` is so far the only one that can. | [`InputSolutionTimeIntervalOuterSplit.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/InputSolutionTimeIntervalOuterSplit.lean), [`TimeIntervalOuterSplit.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TimeIntervalOuterSplit.lean) |
| `MinkDiff`'s obligation | Inner, not outer: a difference is a guarantee, so an implementation may only ever return a subset. The one class here whose direction flips. | [`Interfaces.lean`](../../src/CORALean/ContSet/ContSet/Interfaces.lean) |
| Star set's coefficient box | A `StarSet` always carries CORA's box `[l, u]` on its coefficients beside the predicate (Duggirala and Viswanathan, CAV 2016, Def. 1, has the predicate alone), so a star set is bounded; the arrows of Kochdumper and Althoff's Fig. 1 into star sets hold for bounded sets. | [`StarSet.lean`](../../src/CORALean/ContSet/StarSet/Real/StarSet.lean) |
| `ZonoBundle` at `k = 0` | An intersection over an empty family is the whole space, not `∅` — the opposite of `VPolytope`'s zero vertices, and why compactness is a theorem taking `0 < k` rather than an instance. | [`ZonoBundle.lean`](../../src/CORALean/ContSet/ZonoBundle/Real/ZonoBundle.lean) |
| `Capsule` at a negative radius | Denotes `∅`, following `Interval`'s crossed box, so the structure carries no `0 ≤ r` field. The distance is written as `Real.sqrt (∑ …)` rather than through a norm: `Vec ℝ n`'s own norm is the supremum one. | [`Capsule.lean`](../../src/CORALean/ContSet/Capsule/Real/Capsule.lean) |
| Float `minMaxDiffOrder`'s sample grid | CORA samples the box at equally spaced points. No float expression can be *proved* to step by a bounded amount — rounding is constrained in one direction per operation — so the grid is proposed and certified by `le` instead, and one that fails the check falls back to the whole width rather than being wrong. | [`GridChecked.lean`](../../src/CORALean/NN/Layers/Operations/GridChecked.lean), [`PolyRelaxationOfSampling.lean`](../../src/CORALean/NN/Layers/Operations/PolyRelaxationOfSampling.lean) |
| Float `log` | CORA calls a library logarithm. `SoundFloatArithmetic` bounds each operation in one direction only, so no float series can be shown to converge to `log`; it is inverted instead — a candidate is certified by `expUp`/`expDown`, and bisection over `[0, a]` turns the check into a value. That is why `logDown` needs `1 ≤ a`, the left endpoint `zero` being the certificate it starts from. | [`Log.lean`](../../src/CORALean/Global/Float/Log.lean) |
| Adaptive tuning's searches | The papers pick a step size and a set-representation order by searches with no termination bound, and this tree's own precedent — `expRemainderOrder`, `expRemainderStep`, `reduceBoxOrder` — resolves such a choice classically, by `Nat.find` or `Classical.choose`. Chosen deliberately against that here: every decision goes through a supplied `le : ℝ → ℝ → Bool`, so each loop is a bounded structural recursion a float layer transcribes with `FloatOps.le`. Details below. | [`AdaptTimeStepSearch.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/AdaptTimeStepSearch.lean), [`AdaptSetOrder.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/AdaptSetOrder.lean), [`OptDeltat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/OptDeltat.lean), [`EstimateGain.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/EstimateGain.lean), [`AdaptStep.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/AdaptStep.lean), [`TuneDeltat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/TuneDeltat.lean), [`AutoTuneDeltaT.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/AutoTuneDeltaT.lean), [`AutoTuneSetOrder.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/AutoTuneSetOrder.lean), [`Verify.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/Verify.lean) |
| TAC'23 `Alg. 3`'s outer/inner approximation and `Prop. 7`/`Prop. 8` checks | The source's own pseudocode treats `Alg. 2`'s reach, `Sec. V`'s Minkowski-difference inner approximation, and `Prop. 7`/`Prop. 8`'s linear-program optimum as call-outs — "comp. with Alg. 2", "see Sec. V", "see (46)/(45)", "see Prop. 8" — none inlined there either. Formalized the same way: `reachFn`, `innerApprox`, `distG`, `distF` are caller-supplied functions rather than composed from this tree's own `Alg. 2`/`Prop. 6`-`Prop. 8`, since no solver exists here to instantiate `Prop. 7`/`Prop. 8`'s `ν` (that paper's own page records why) and `Alg. 2`'s `autoReach` is `Set`-valued rather than the single zonotope a containment/intersection check needs. | [`Verify.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/Verify.lean) |
| Scope of the trusted hardware | The axiom `trustedHardware` states the ten obligations unconditionally, as the class asks, and read that way it is false at the extremes: `toReal` decodes `+∞` as `2 ^ 1024`, below the exact sum of two largest doubles, and halving a subnormal loses a bit. It is trusted only while all values stay in binary64's normal range, and the operations return NaN wherever a value would leave it, which propagates to the result, so a run outside the scope is detected at run time rather than trusted, provided the result is inspected for NaN, which the library's theorems do not do. The argument and its limits are in the README's trust base. `IEEE binary64` rounds onto the same grid, subnormals included, with every obligation proved. | [`Axioms.lean`](../../src/CORALean/Global/Float/Instances/Binary64/Definitions/Axioms.lean), [`Half.lean`](../../src/CORALean/Global/Float/Instances/Binary64/Operations/Half.lean) |
| Negation symmetry under directed rounding | `Zonotope.mtimes`'s stored center, `mulVecDown M Z.c`, rounds down regardless of `Z.c`'s sign, so `f(-x)` and `-f(x)` can differ by an ulp once the dot product actually needs rounding; round-to-nearest, as in CORA, is odd-symmetric. `reachFloat` feeds its own center back every step, so the ulp compounds; `reachWrappingFreeFloat`'s windows carry the same asymmetric bit but never compound it, each being multiplied fresh out of one fixed `X₀`. Soundness is unaffected — the residual is charged to the error box `E` either way. | [`Mtimes.lean`](../../src/CORALean/ContSet/Zonotope/Float/Operations/Mtimes.lean) |
| Floating-point Taylor model arithmetic | Makino and Berz's IJPAM 2003 paper (`Def. 4`, `Def. 6`, `Def. 7`) assumes a floating-point environment described by a relative accuracy `εm` and an underflow threshold `εu`, and COSY's algorithms on top of it: coefficients below a cutoff `εc` swept into a variable `s`, rounding errors tallied in `t`, and the remainder widened by `e⊗εm⊗[-t, t] ⊕ e⊗[-s, s]`. The float layer here assumes directed rounding instead (`SoundFloatArithmetic`), which bounds each operation in a stated direction and needs no `εm`; each coefficient is enclosed by its two roundings, the upper end stored and the width added to the remainder, and nothing is swept. The guarantee is the paper's `Thm. 3`, that a run encloses, which `Taylm.codeEval_encloses` proves for this arithmetic. | [`SoundFloatArithmetic.lean`](../../src/CORALean/Global/Float/SoundFloatArithmetic.lean), [`Times.lean`](../../src/CORALean/ContSet/Taylm/Float/Operations/Times.lean), [`CodeEvalEncloses.lean`](../../src/CORALean/ContSet/Taylm/Float/Theorems/CodeEvalEncloses.lean) |
| Floating-point zonotopes, DeepZ's interval affine forms | [Singh et al., NeurIPS 2018, Eq. 2](../2018/singh-neurips-deepz.md) makes a float zonotope sound by storing every coefficient as an interval and evaluating with outward-rounded interval arithmetic, so its ReLU and S-shape transformers carry `[λl, λu]` and `[μl, μu]`. A float set here stores point coefficients and pays every rounding into an error box (`InflatedContSet`), and a `Relaxation` stores one slope, offset and error, the error measured against the values actually stored: DeepZ's ReLU transformer at ℝ is `reluRelaxation reluSlope` (`Real.deepZRelu_eq_reluRelaxation`), whose soundness `reluRelaxation_encloses` holds at every float scalar without intervals. | [`DeepZReluEq.lean`](../../src/CORALean/NN/Layers/Theorems/Real/DeepZReluEq.lean), [`ReluRelaxationEncloses.lean`](../../src/CORALean/NN/Layers/Theorems/ReluRelaxationEncloses.lean) |

### Details of the departures

**Float nonlinear abstraction error — the plain `FloatModel`.** A plain `FloatModel` run has no
Hessian. It keeps the first-order mean-value form `([J] - A)(X - x✱)` from the Jacobian slopes,
`O(‖δ‖)` in the deviation rather than `O(‖δ‖²)`.

**Float nonlinear abstraction error — `'poly'`.** CORA's `'poly'` (`priv_abstrerr_poly`) bounds what
the Hessian at `z✱` leaves by the third-order tensor. The float `'poly'` step carries no third
derivative. It bounds the remainder by the second-order Lagrange form over the Hessian box,
`½ z₀ᵀ([H] - H(z✱)) z₀`, and boxes the products carrying a difference where CORA keeps them as a
reduced zonotope.

**Float nonlinear abstraction error — the region.** In both variants the region is checked before
the step (ball, then Picard refinement) instead of enlarged after it. So CORA's
`while perfIndCurr > 1` loop is one pass, and the step runs in CORA's deviation coordinates.

**Adaptive tuning's searches — what soundness needs.** Soundness needs only
`le a b = true → a ≤ b`, and the converse buys the existence theorem. The searches remain
`noncomputable` solely because ℝ arithmetic is. The step sweep carries explicit fuel and returns
`Option` where the source loops forever.

**Adaptive tuning's searches — TAC'23 `Alg. 2`.** Its own order search (lines 8-12) is replaced for
one further reason. It tests convergence of a numerical `T(j)` rather than the bounds `η_k` has to
meet, and eq. (17)'s `I_1(Δt)` divides by zero at `η_k = 1`.

**Adaptive tuning's searches — TAC'23 `Alg. 3`.** Its outer `repeat...until` is likewise
`fuel`-bounded and `Option`-valued rather than assumed to terminate. Its own `Thm. 1` bounds only
`Alg. 2`, not this loop.
