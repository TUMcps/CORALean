# CORA coverage

How much of CORA does CORALean answer? One table per CORA class, one row per CORA
method, so "is `zonotope/reduce` done?" is a lookup. The tables sit beside the
paper tables in [../README.md](../README.md) and are checked the same way, by
`scripts/check-references.py`, which CI runs.

**The unit is one method file**: `~/CORA/contSet/@<class>/<method>.m`,
`~/CORA/contDynamics/@<class>/<method>.m` or `~/CORA/hybridDynamics/@<class>/<method>.m`.
Files under `private/` are implementation helpers of those methods and have no row. The
constructor `<class>.m` is one row like any other: it counts for the class definition
(the structure and its denotation), and is `proved` when a theorem about that
denotation exists (convexity, closedness, compactness, a conversion lemma), not for
CORA's argument parsing. The abstract superclasses `contSet` and `contDynamics` are
tabulated too: CORALean's counterparts of their dispatching methods are the interface
classes of `ContSet/ContSet/ContSet.lean` (`Plus`, `Mtimes`, `Intersection`, `Reduce`,
...), whose fields carry the guarantee, so such a row links the class.

The classes tabulated are every class under CORA's `contSet/`, `contDynamics/` and
`hybridDynamics/`. `matrixSet/`, `nn/`, `specification/`, `discrDynamics/`, `converter/` and
`global/` are not part of this count. A class with no counterpart in CORALean is
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

**State.** One of four:

| State | Meaning |
|---|---|
| `proved` | a real-layer definition and a theorem about it: an exact, outer or inner statement (or, for a property such as `isBounded`, the theorem that characterizes it), linked in the third cell. A definition alone is not `proved`. |
| `float` | `proved`, and runnable at float, by one of two routes (below). |
| `—` | not yet. A definition without a theorem lands here, and says so in the note. |
| `out-of-scope` | CORALean does not do this, for one of the reasons below. "Hard" is never a reason. |

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
`cora-issue — <what CORA gets wrong>` on a row where CORA's own implementation was found
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
| `io/conversion-to-matlab-objects` | `full`, `sparse`, `double`, `single`, `string`, `jsonencode`: conversions between MATLAB storage formats |
| `matlab-runtime` | MATLAB language plumbing: `copy`, `isemptyobject`, `size`, `length`, `subsref`, `subsasgn`, `reshape`, `parfor` variants, function-handle generators; also `eq`, `ne` and `isequal` of system, reset, location, transition and automaton objects, which compare MATLAB objects field by field (structural equality, not a mathematical claim; `isequal`/`eq` of two sets is one and stays in scope) |
| `deprecated` | the method's own help text says `DEPRECATED` |

## Counts

<!-- coverage-counts -->
| Class | Group | Methods | proved | float | not yet | out of scope | CORA issues |
|---|---|---|---|---|---|---|---|
| [affine](contSet/affine.md) | contSet | 1 | 0 | 0 | 1 | 0 | 0 |
| [capsule](contSet/capsule.md) | contSet | 39 | 4 | 12 | 13 | 10 | 1 |
| [conPolyZono](contSet/conPolyZono.md) | contSet | 47 | 8 | 15 | 16 | 8 | 0 |
| [conZonotope](contSet/conZonotope.md) | contSet | 50 | 7 | 16 | 15 | 12 | 0 |
| [contSet](contSet/contSet.md) | contSet | 101 | 5 | 18 | 19 | 59 | 0 |
| [ellipsoid](contSet/ellipsoid.md) | contSet | 50 | 4 | 12 | 25 | 9 | 0 |
| [emptySet](contSet/emptySet.md) | contSet | 30 | 10 | 12 | 1 | 7 | 0 |
| [fullspace](contSet/fullspace.md) | contSet | 33 | 11 | 12 | 3 | 7 | 0 |
| [interval](contSet/interval.md) | contSet | 110 | 16 | 61 | 15 | 18 | 0 |
| [levelSet](contSet/levelSet.md) | contSet | 22 | 7 | 0 | 8 | 7 | 0 |
| [polyZonotope](contSet/polyZonotope.md) | contSet | 73 | 10 | 16 | 33 | 14 | 0 |
| [polygon](contSet/polygon.md) | contSet | 46 | 5 | 11 | 24 | 6 | 0 |
| [polytope](contSet/polytope.md) | contSet | 58 | 12 | 18 | 20 | 8 | 0 |
| [probZonotope](contSet/probZonotope.md) | contSet | 28 | 0 | 0 | 22 | 6 | 0 |
| [spectraShadow](contSet/spectraShadow.md) | contSet | 33 | 5 | 2 | 18 | 8 | 0 |
| [taylm](contSet/taylm.md) | contSet | 51 | 14 | 10 | 18 | 9 | 0 |
| [zonoBundle](contSet/zonoBundle.md) | contSet | 44 | 1 | 18 | 18 | 7 | 0 |
| [zonotope](contSet/zonotope.md) | contSet | 80 | 13 | 25 | 29 | 13 | 1 |
| [zoo](contSet/zoo.md) | contSet | 12 | 0 | 0 | 10 | 2 | 0 |
| [contDynamics](contDynamics/contDynamics.md) | contDynamics | 19 | 1 | 3 | 5 | 10 | 1 |
| [linParamSys](contDynamics/linParamSys.md) | contDynamics | 11 | 3 | 2 | 3 | 3 | 0 |
| [linProbSys](contDynamics/linProbSys.md) | contDynamics | 8 | 0 | 0 | 4 | 4 | 0 |
| [linearARX](contDynamics/linearARX.md) | contDynamics | 7 | 1 | 1 | 3 | 2 | 0 |
| [linearSys](contDynamics/linearSys.md) | contDynamics | 33 | 7 | 7 | 10 | 9 | 0 |
| [linearSysDT](contDynamics/linearSysDT.md) | contDynamics | 17 | 1 | 4 | 10 | 2 | 0 |
| [neurNetContrSys](contDynamics/neurNetContrSys.md) | contDynamics | 5 | 3 | 1 | 0 | 1 | 0 |
| [nonlinDASys](contDynamics/nonlinDASys.md) | contDynamics | 13 | 2 | 0 | 8 | 3 | 0 |
| [nonlinParamSys](contDynamics/nonlinParamSys.md) | contDynamics | 9 | 3 | 0 | 3 | 3 | 0 |
| [nonlinearARX](contDynamics/nonlinearARX.md) | contDynamics | 8 | 3 | 0 | 3 | 2 | 0 |
| [nonlinearSys](contDynamics/nonlinearSys.md) | contDynamics | 18 | 6 | 1 | 5 | 6 | 1 |
| [nonlinearSysDT](contDynamics/nonlinearSysDT.md) | contDynamics | 11 | 5 | 0 | 4 | 2 | 0 |
| [abstractReset](hybridDynamics/abstractReset.md) | hybridDynamics | 4 | 0 | 0 | 0 | 4 | 0 |
| [hybridAutomaton](hybridDynamics/hybridAutomaton.md) | hybridDynamics | 15 | 0 | 2 | 4 | 9 | 0 |
| [hybridDynamics](hybridDynamics/hybridDynamics.md) | hybridDynamics | 2 | 1 | 0 | 0 | 1 | 0 |
| [linearReset](hybridDynamics/linearReset.md) | hybridDynamics | 10 | 2 | 1 | 4 | 3 | 0 |
| [location](hybridDynamics/location.md) | hybridDynamics | 24 | 2 | 3 | 13 | 6 | 0 |
| [nonlinearReset](hybridDynamics/nonlinearReset.md) | hybridDynamics | 9 | 0 | 0 | 5 | 4 | 0 |
| [parallelHybridAutomaton](hybridDynamics/parallelHybridAutomaton.md) | hybridDynamics | 13 | 2 | 4 | 1 | 6 | 0 |
| [transition](hybridDynamics/transition.md) | hybridDynamics | 12 | 0 | 2 | 4 | 6 | 0 |
| [layers](nn/layers.md) | nn | 43 | 5 | 24 | 13 | 1 | 0 |
| [neuralNetwork](nn/neuralNetwork.md) | nn | 61 | 4 | 7 | 15 | 35 | 0 |
<!-- /coverage-counts -->

`python3 scripts/check-references.py --fix` rewrites the table above.

## What the check does

* every method file of a tabulated class has a row, and a row names a method file: the
  method lists are in [cora-inventory.json](cora-inventory.json), committed so CI needs no
  CORA checkout, and compared with one (`CORA_DIR`, default `~/CORA`) where it exists;
* the state is one of the four, the out-of-scope reason one of the six;
* every link points at a Lean file that exists and declares the named declaration;
* a `proved` row links a theorem (or a class whose fields carry the guarantee), and a
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
