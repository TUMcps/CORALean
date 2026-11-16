module

public import CORALean.ContSet.PolyZonotope.Real.Operations.CubMapDep
public import CORALean.ContSet.PolyZonotope.Real.Operations.ExtE
public import CORALean.ContSet.PolyZonotope.Real.Operations.Jacobian
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import CORALean.ContSet.PolyZonotope.Real.Operations.SplitLongestGen
public import CORALean.ContSet.PolyZonotope.Real.Definitions.PowerOps
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

section
variable {n m : ℕ} {α : Type} [AddCommGroup α] [Module ℝ α]


-- ========================================  `IsInCone`  ======================================== --
-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- What the LP of `aux_inCone` decides: `d = N x` for some `x ≥ 0`.

What the linear program of `aux_inCone` in CORA's `isPolytope` decides: `d = N x`, `x ≥ 0`. -/
def IsInCone {m : ℕ} (N : Fin m → α) (d : α) : Prop :=
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

end

section
variable {α β γ : Type}


-- =================================  `PolyZonotope.crossWith`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `f` of every entry of `a` with every entry of `b`, the entries of `a` running fastest: the
order of CORA's `calcSquaredG` for two different powers. -/
def PolyZonotope.crossWith (f : α → β → γ) (a : List α) (b : List β) : List γ :=
  b.flatMap fun y => a.map fun x => f x y


-- =================================  `PolyZonotope.pairsWith`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `f` of every pair of entries `i < j` of a list, `j` running fastest: the off-diagonal terms
of CORA's `calcSquaredG` for a power with itself. -/
def PolyZonotope.pairsWith (f : α → α → β) : List α → List β
  | [] => []
  | x :: r => r.map (f x) ++ PolyZonotope.pairsWith f r


-- ================================  `PolyZonotope.powerParts`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The generators of the powers `1, …, k` that are their own: all of the first, and of the power
`i` what follows the `len (i/2) + len ((i+1)/2)` entries of the two powers it is made of. -/
def PolyZonotope.powerParts (len : ℕ → ℕ) (F : ℕ → List α) (k : ℕ) : List α :=
  F 1 ++ (List.range' 2 (k - 1)).flatMap fun i => (F i).drop (len (i / 2) + len ((i + 1) / 2))


-- =====================================  `PowerOps.real`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The real numbers' own sum, product, `0`, `2` and `1/2`: the powers computed exactly. -/
noncomputable def PowerOps.real : PowerOps ℝ := ⟨(· + ·), (· * ·), 0, 2, 1 / 2⟩

end

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
