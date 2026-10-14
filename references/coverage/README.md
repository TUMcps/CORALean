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
classes of `ContSet/ContSet/ContSet.lean` (`Plus`, `Mtimes`, `Intersection`, `Reduce`,
...), whose fields carry the guarantee, so such a row links the class.

The classes tabulated are every class under CORA's `contSet/`, `contDynamics/`,
`hybridDynamics/` and `specification/` (the group `specification`: `specification`, `stl`,
`stlInterval`, `rtl`, the signals, the analyzers and the logics `kleene` and `fourValued`), the
neural networks of `nn/` (`nn/@neuralNetwork` and `nn/layers/`), and the group `others`, which
the paper shows only as one aggregate bar (no per-class figure): `matrixSet/` (`intervalMatrix`,
`matZonotope`, `matPolytope`, `matrixSet`), `discrDynamics/` (`markovchain`, `partition`, and
`ProbOccupancyPrediction`, a traffic-prediction case study that is no class: its `@road` and
`@simulation` classes are `road` and `simulation`, its other functions the table
`ProbOccupancyPrediction`, with one row per file; its example inputs `scenarios/`,
`velocityProfiles/` and `vehicleModels/` have none, as CORA's `examples/` has none) and
`converter/` (one table per subdirectory, one row per `.m` file however deep, `private/`
excluded; every row is `io/conversion-to-matlab-objects`, file-format converters from and to
SpaceEx, CommonRoad, CommonOcean, VNN-LIB and power-system files). `global/` is not tracked:
it holds helper functions (validation, numerics, printing), not classes. CORALean has no matrix-set classes of its
own: `matZonotope` is `Zonotope (Mat ℝ m n)`, `intervalMatrix` is `Interval (Mat ℝ m n)` and
`matPolytope` is `VPolytope (Mat ℝ m n)`, so a row links the generic declaration only where its
theorem is stated at (or generically over) the matrix ambient type and states the CORA
operation's result. A class with no counterpart in CORALean is
tabulated all the same, every method `—` (or out of scope for a reason that holds for it),
so the denominator is CORA's, not ours. Those are `spectraShadow`, `taylm`, `affine`,
`levelSet`, `polygon`, `probZonotope`, `zoo`, `linProbSys`, `nonlinDASys`,
`nonlinearARX`, `abstractReset`, `linearReset`, `nonlinearReset` and `hybridDynamics`.
`polytope` is answered by `HPolytope` and `VPolytope`; `location` and `transition` by
`Location` and `Transition`; `contDynamics` by `Reach` and `OutputEq`.

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
* the definition is **not** CORA's method: the result is coarser (a bounding box or interval hull where CORA returns a tight set; a larger remainder; an enclosure of a segment where CORA solves an LP; a box where CORA builds eigen generators), or computed by a different algorithm than CORA's default.

The note names what differs from CORA, first, in plain words ("box, CORA: eigen generators"; "different remainder"; "pieces: ..."); an empty note is refused, as is a `route b` note. A `bound` row has no float/real split of its own: one state keeps the tables and the figure simple, and whether the bound runs at float is read from its links (a `float:` part lists the float layer), as for any row; the float backlog is `proved` only. A `bound` row becomes `proved`/`float` when a definition that is CORA's method is added and linked. It is never used for a result that is merely a consequence of other pieces with no statement about CORA's output, or that is unsound.

A `proved` row that is not `float` is the **float backlog** (`needs_float` in
`experiments/paper/formalization-stats.json`).

**When a method counts as `float`.** A method is `float` iff it is `proved` and either

* **(a)** a float-layer counterpart exists with an outer (or inner) theorem: a computable
  definition, and a theorem about it, in a `Float/` directory or in a declaration or file with
  `Float` in its name. The row links them after `float:`; or
* **(b)** its definition is generic over the scalar `𝕋` (or over the set representation, whose
  scalar the instances carry), is computable (not `noncomputable`, so not on
  `scripts/noncomputable-allowlist.txt`), and its soundness theorem is stated for that generic
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
unsound or wrong and CORALean does it differently on purpose. Only a result that
[FINDINGS.md](../../FINDINGS.md) or a docstring documents as an error of CORA is marked;
a design difference is not one.

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
* **R-WE: `empty` of a representation that cannot denote `∅`** (zonotope, ellipsoid, polyZonotope) is answered by `WithEmpty.empty`, the wrapper's own empty member, and counts as `float` by route b (scalar-free): the wrapper holds no scalar and is generic over the class, `WithEmpty.construct_empty` says it denotes `∅`, and the note says why the representation itself has no such member (the zonotope's centre and the polynomial zonotope's factor vector `0` are always members; an ellipsoid has no empty shape).
* **R-PG: a polygon denotes its region; methods are formalized against the region given as convex pieces.** CORA's `polyshape` boundary (vertex lists with holes) is not converted to convex pieces, so a method whose result is defined by the boundary representation itself (vertex order, collinear-point removal, triangulation output, `expandBoundaries`, boundary vertex counts) stays `—` with the reason "boundary representation (R-PG)" unless a region-level statement captures it honestly (`isFullDim`, `isIntersecting_`, `isConvex`, `volume_`, `splitIntoConvexSets`, `isequal` one-sided, and `triangulation`, a cover of the region by vertex triangles; `subtract`, `mldivide` and `minkDiff`, the regularized difference as a region; `hausdorffDist`, the point branch; `quadMap`, the images of those triangles). The row note says which region statement is proved and that the boundary computation is not.
* **R-VS: capsule `vertices_` returns sampled boundary points, not vertices** (a capsule has none): `proved` (or `float`) only with a theorem that the returned points lie on the boundary (`Capsule.vertices_mem_frontier`), and the row note says "points on the boundary, not vertices"; no exactness is claimed, the hull of the points is inside the capsule, not equal to it.

## Counts

<!-- coverage-counts -->
| Class | Group | Methods | proved | float | bound | not yet | out of scope | CORA issues |
|---|---|---|---|---|---|---|---|---|
| [affine](contSet/affine.md) | contSet | 1 | 0 | 1 | 0 | 0 | 0 | 0 |
| [capsule](contSet/capsule.md) | contSet | 39 | 1 | 22 | 6 | 0 | 10 | 7 |
| [conPolyZono](contSet/conPolyZono.md) | contSet | 47 | 2 | 30 | 6 | 1 | 8 | 4 |
| [conZonotope](contSet/conZonotope.md) | contSet | 50 | 2 | 31 | 5 | 0 | 12 | 5 |
| [contSet](contSet/contSet.md) | contSet | 101 | 1 | 28 | 0 | 0 | 72 | 0 |
| [ellipsoid](contSet/ellipsoid.md) | contSet | 50 | 3 | 33 | 2 | 0 | 12 | 6 |
| [emptySet](contSet/emptySet.md) | contSet | 30 | 2 | 21 | 0 | 0 | 7 | 0 |
| [fullspace](contSet/fullspace.md) | contSet | 33 | 5 | 20 | 0 | 0 | 8 | 0 |
| [interval](contSet/interval.md) | contSet | 110 | 0 | 92 | 0 | 0 | 18 | 3 |
| [levelSet](contSet/levelSet.md) | contSet | 22 | 4 | 9 | 0 | 0 | 9 | 3 |
| [polyZonotope](contSet/polyZonotope.md) | contSet | 73 | 3 | 50 | 2 | 3 | 15 | 8 |
| [polygon](contSet/polygon.md) | contSet | 46 | 1 | 32 | 0 | 2 | 11 | 9 |
| [polytope](contSet/polytope.md) | contSet | 58 | 4 | 38 | 4 | 0 | 12 | 8 |
| [probZonotope](contSet/probZonotope.md) | contSet | 28 | 3 | 14 | 2 | 0 | 9 | 4 |
| [spectraShadow](contSet/spectraShadow.md) | contSet | 33 | 1 | 23 | 0 | 0 | 9 | 5 |
| [taylm](contSet/taylm.md) | contSet | 51 | 1 | 27 | 11 | 0 | 12 | 0 |
| [zonoBundle](contSet/zonoBundle.md) | contSet | 44 | 3 | 28 | 6 | 0 | 7 | 5 |
| [zonotope](contSet/zonotope.md) | contSet | 80 | 5 | 57 | 4 | 0 | 14 | 12 |
| [zoo](contSet/zoo.md) | contSet | 12 | 0 | 10 | 0 | 0 | 2 | 2 |
| [contDynamics](contDynamics/contDynamics.md) | contDynamics | 19 | 2 | 6 | 0 | 0 | 11 | 4 |
| [linParamSys](contDynamics/linParamSys.md) | contDynamics | 11 | 1 | 6 | 0 | 0 | 4 | 2 |
| [linProbSys](contDynamics/linProbSys.md) | contDynamics | 8 | 3 | 0 | 0 | 0 | 5 | 1 |
| [linearARX](contDynamics/linearARX.md) | contDynamics | 7 | 1 | 4 | 0 | 0 | 2 | 0 |
| [linearSys](contDynamics/linearSys.md) | contDynamics | 33 | 1 | 21 | 0 | 1 | 10 | 3 |
| [linearSysDT](contDynamics/linearSysDT.md) | contDynamics | 17 | 4 | 7 | 0 | 0 | 6 | 2 |
| [neurNetContrSys](contDynamics/neurNetContrSys.md) | contDynamics | 5 | 0 | 4 | 0 | 0 | 1 | 0 |
| [nonlinDASys](contDynamics/nonlinDASys.md) | contDynamics | 13 | 6 | 3 | 0 | 1 | 3 | 5 |
| [nonlinParamSys](contDynamics/nonlinParamSys.md) | contDynamics | 9 | 1 | 3 | 0 | 1 | 4 | 1 |
| [nonlinearARX](contDynamics/nonlinearARX.md) | contDynamics | 8 | 0 | 5 | 0 | 0 | 3 | 1 |
| [nonlinearSys](contDynamics/nonlinearSys.md) | contDynamics | 18 | 3 | 6 | 0 | 1 | 8 | 2 |
| [nonlinearSysDT](contDynamics/nonlinearSysDT.md) | contDynamics | 11 | 1 | 7 | 0 | 0 | 3 | 2 |
| [abstractReset](hybridDynamics/abstractReset.md) | hybridDynamics | 4 | 0 | 0 | 0 | 0 | 4 | 0 |
| [hybridAutomaton](hybridDynamics/hybridAutomaton.md) | hybridDynamics | 15 | 0 | 2 | 0 | 2 | 11 | 1 |
| [hybridDynamics](hybridDynamics/hybridDynamics.md) | hybridDynamics | 2 | 0 | 1 | 0 | 0 | 1 | 0 |
| [linearReset](hybridDynamics/linearReset.md) | hybridDynamics | 10 | 0 | 7 | 0 | 0 | 3 | 0 |
| [location](hybridDynamics/location.md) | hybridDynamics | 24 | 2 | 13 | 0 | 1 | 8 | 5 |
| [nonlinearReset](hybridDynamics/nonlinearReset.md) | hybridDynamics | 9 | 0 | 5 | 0 | 0 | 4 | 1 |
| [parallelHybridAutomaton](hybridDynamics/parallelHybridAutomaton.md) | hybridDynamics | 13 | 0 | 6 | 0 | 1 | 6 | 2 |
| [transition](hybridDynamics/transition.md) | hybridDynamics | 12 | 0 | 5 | 0 | 0 | 7 | 1 |
| [layers](nn/layers.md) | nn | 43 | 0 | 39 | 0 | 0 | 4 | 1 |
| [neuralNetwork](nn/neuralNetwork.md) | nn | 61 | 7 | 13 | 0 | 0 | 41 | 2 |
| [atomicProposition](specification/atomicProposition.md) | specification | 5 | 0 | 0 | 0 | 5 | 0 | 0 |
| [finiteKleeneSignalBuilder](specification/finiteKleeneSignalBuilder.md) | specification | 4 | 0 | 0 | 0 | 4 | 0 | 0 |
| [finiteSignal](specification/finiteSignal.md) | specification | 10 | 0 | 0 | 0 | 9 | 1 | 0 |
| [fourValued](specification/fourValued.md) | specification | 5 | 0 | 0 | 0 | 5 | 0 | 0 |
| [fourValuedSignal](specification/fourValuedSignal.md) | specification | 18 | 0 | 0 | 0 | 16 | 2 | 0 |
| [kleene](specification/kleene.md) | specification | 4 | 0 | 0 | 0 | 4 | 0 | 0 |
| [kleeneSignal](specification/kleeneSignal.md) | specification | 15 | 0 | 0 | 0 | 13 | 2 | 0 |
| [logicSignal](specification/logicSignal.md) | specification | 10 | 0 | 0 | 0 | 9 | 1 | 0 |
| [onlineAnalyzerNode](specification/onlineAnalyzerNode.md) | specification | 7 | 0 | 0 | 0 | 6 | 1 | 0 |
| [onlineReachSetAnalyzer](specification/onlineReachSetAnalyzer.md) | specification | 5 | 0 | 0 | 0 | 4 | 1 | 0 |
| [pointSegmentSignal](specification/pointSegmentSignal.md) | specification | 11 | 0 | 0 | 0 | 10 | 1 | 0 |
| [reachSetAnalyzer](specification/reachSetAnalyzer.md) | specification | 5 | 0 | 0 | 0 | 5 | 0 | 0 |
| [rtl](specification/rtl.md) | specification | 5 | 0 | 0 | 0 | 4 | 1 | 0 |
| [specification](specification/specification.md) | specification | 14 | 0 | 2 | 0 | 6 | 6 | 1 |
| [stl](specification/stl.md) | specification | 52 | 28 | 4 | 0 | 15 | 5 | 4 |
| [stlInterval](specification/stlInterval.md) | specification | 19 | 0 | 0 | 0 | 17 | 2 | 0 |
| [syntaxTree](specification/syntaxTree.md) | specification | 27 | 0 | 0 | 0 | 27 | 0 | 0 |
| [tentativeKleeneSignal](specification/tentativeKleeneSignal.md) | specification | 6 | 0 | 0 | 0 | 5 | 1 | 0 |
| [trajectoryAnalyzer](specification/trajectoryAnalyzer.md) | specification | 2 | 0 | 0 | 0 | 2 | 0 | 0 |
| [ProbOccupancyPrediction](others/ProbOccupancyPrediction.md) | others | 25 | 0 | 0 | 0 | 21 | 4 | 0 |
| [commonocean2cora](others/commonocean2cora.md) | others | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| [commonroad2cora](others/commonroad2cora.md) | others | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| [cora2spaceex](others/cora2spaceex.md) | others | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| [intervalMatrix](others/intervalMatrix.md) | others | 39 | 5 | 4 | 1 | 19 | 10 | 0 |
| [markovchain](others/markovchain.md) | others | 12 | 0 | 0 | 0 | 7 | 5 | 0 |
| [matPolytope](others/matPolytope.md) | others | 20 | 3 | 0 | 0 | 10 | 7 | 0 |
| [matZonotope](others/matZonotope.md) | others | 33 | 3 | 2 | 3 | 16 | 9 | 0 |
| [matrixSet](others/matrixSet.md) | others | 3 | 0 | 0 | 0 | 0 | 3 | 0 |
| [neuralnetwork2cora](others/neuralnetwork2cora.md) | others | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| [partition](others/partition.md) | others | 12 | 0 | 0 | 0 | 10 | 2 | 0 |
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
* a `proved` or `bound` row links a theorem (or a class whose fields carry the guarantee), a `bound` row's note says what differs, and a
  `float` row links a float-layer definition and a float-layer theorem (route a) or carries a
  `route b —` note whose linked definitions are outside `Real/`, not `noncomputable`, not on the
  allowlist, and whose theorem or class names a scalar or a set representation (route b);
* the counts above are the tables' counts, and `experiments/paper/formalization-stats.json`
  is what `scripts/formalization-stats.py` writes now.

What it cannot check is that the *right* declaration is linked for a CORA method: that is a
judgement, made when the row is written, and argued with in review.

## Which class a paper result lands on

The paper tables' `Class` column says how the paper's statement fared. The figure in the
paper breaks that down by CORA class, by the first Lean file the row links:
`ContSet/Zonotope/...` is `zonotope`; `ContSet/Conversion/.../Zonotope_to_Interval.lean` is
`zonotope` (the conversion is the source's method); `ContSet/ContSet`, `SetUnion`,
`SetIntersection`, `InflatedContSet`, `WithEmpty` are `contSet`;
`ContDynamics/LinParamSys` and `LinParamSysDT` are `linParamSys`, `NeurNetContrSys` and
`NeurNetContrSysDT` are `neurNetContrSys`, `OutputEq` and `Reach` are `contDynamics`;
`HybridDynamics/Parallel` is `parallelHybridAutomaton` and the rest of `HybridDynamics/` is
`hybridAutomaton`. Files that belong to no CORA class land in `global` (`Global/`),
`neuralNetwork` (`NN/`) or `specification` (`Specification/`).
