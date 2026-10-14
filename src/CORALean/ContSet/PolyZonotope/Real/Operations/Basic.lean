module

public import CORALean.ContSet.PolyZonotope.Real.Operations.CubMapDep
public import CORALean.ContSet.PolyZonotope.Real.Operations.ExtE
public import CORALean.ContSet.PolyZonotope.Real.Operations.Jacobian
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import CORALean.ContSet.PolyZonotope.Real.Operations.SplitLongestGen
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `ContSet/PolyZonotope/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

variable {n m : ℕ} {α : Type} [AddCommGroup α] [Module ℝ α]


-- =========================================  `inCone`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- What the LP of `aux_inCone` decides: `d = N x` for some `x ≥ 0`.

What the linear program of `aux_inCone` in CORA's `isPolytope` decides: `d = N x`, `x ≥ 0`. -/
def inCone {m : ℕ} (N : Fin m → α) (d : α) : Prop :=
  ∃ x : Fin m → ℝ, (∀ j, 0 ≤ x j) ∧ d = ∑ j, x j • N j


-- =================================  `PolyZonotope.cubMapDep`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `cubMapDepOn` with the identity three times.

`cubMapDepOn` of a set in its own ambient space: the single form `{ (xᵀ T x) * x | x ∈ pZ }`. -/
def PolyZonotope.cubMapDep (T : Fin m → Fin n → Mat ℝ n n) (pZ : PolyZonotope (Vec ℝ n)) :
    PolyZonotope (Vec ℝ m) :=
  PolyZonotope.cubMapDepOn LinearMap.id LinearMap.id LinearMap.id T pZ


-- ===================================  `PolyZonotope.extM`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Split out of `QuadMap.lean` (issue #62): read by `Theorems/SumExtEqPoint.lean`,
`Theorems/QuadEvalSumExt.lean` and `Theorems/MulPoint.lean`, all outside this
file. -/
def PolyZonotope.extM (pZ : PolyZonotope α) (a : Fin pZ.p → ℝ) : Fin (pZ.h + 1) → ℝ :=
  PolyZonotope.monomial (PolyZonotope.extE pZ) a


-- ================================  `PolyZonotope.jacobianMat`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The Jacobian of the point map at a factor vector: column `k` is the point of the derivative
along factor `k` (`jacobian`). -/
def PolyZonotope.jacobianMat (pZ : PolyZonotope (Vec ℝ n)) (a : Fin pZ.p → ℝ) :
    Matrix (Fin n) (Fin pZ.p) ℝ :=
  Matrix.of fun i k => (pZ.jacobian k).point a i


-- ===============================  `PolyZonotope.polygonRound`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- One round of `polygon`'s loop: every piece the verdict `pick` selects is replaced by its two
halves along the longest generator, the others are kept. -/
noncomputable def PolyZonotope.polygonRound (pick : PolyZonotope (Vec ℝ 2) → Bool)
    (L : List (PolyZonotope (Vec ℝ 2))) : List (PolyZonotope (Vec ℝ 2)) :=
  L.flatMap fun q => if pick q then [q.splitLongestGen.fst, q.splitLongestGen.snd] else [q]


-- ===============================  `PolyZonotope.polygonPieces`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The pieces `polygon` ends with: `splits` rounds, `pick i` choosing the pieces refined in round
`i`. -/
noncomputable def PolyZonotope.polygonPieces (pZ : PolyZonotope (Vec ℝ 2)) (splits : ℕ)
    (pick : ℕ → PolyZonotope (Vec ℝ 2) → Bool) : List (PolyZonotope (Vec ℝ 2)) :=
  (List.range splits).foldl (fun L i => PolyZonotope.polygonRound (pick i) L) [pZ]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
