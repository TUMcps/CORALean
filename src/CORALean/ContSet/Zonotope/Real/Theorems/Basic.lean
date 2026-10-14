module

public import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope
public import CORALean.ContSet.Interval.Real.Theorems.NormLe
public import CORALean.ContSet.Zonotope.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Operations.CompactZeros
public import CORALean.ContSet.Zonotope.Real.Operations.MinnormOffset
public import CORALean.ContSet.Zonotope.Real.Operations.NormUb
public import CORALean.ContSet.Zonotope.Real.Operations.RotMat
public import CORALean.ContSet.Zonotope.Real.Theorems.FilterGenConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
public import CORALean.ContSet.Zonotope.Real.Theorems.MapExact
public import CORALean.ContSet.Zonotope.Real.Theorems.RankEqFinrankIff
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Tensor
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `ContSet/Zonotope/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ==================================  `rotMat_mulVec_other`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Matrix

/-- The other coordinates are unchanged. -/
theorem rotMat_mulVec_other {n : ℕ} (i j : Fin n) (angle : ℝ) (x : Vec ℝ n) (k : Fin n)
    (hki : k ≠ i) (hkj : k ≠ j) : (rotMat n i j angle *ᵥ x) k = x k := by
  simp only [mulVec, dotProduct, rotMat, hki, hkj, if_false]
  simp

end CORALean.Real


-- ==================================  `Zonotope.comb_apply`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

/-- `(c + ∑ βⱼ gⱼ)_k = c_k + ∑ βⱼ g_{j,k}`. -/
theorem Zonotope.comb_apply (Z : Zonotope (Vec ℝ 2)) (β : Fin Z.h → ℝ) (k : Fin 2) :
    (Z.c + ∑ j, β j • Z.G j) k = Z.c k + ∑ j, β j * Z.G j k := by
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end CORALean.Real


-- ==============================  `Zonotope.compactZeros_exact`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open scoped Classical

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- Exact: the dropped generators are zero, and `Zonotope.filterGen_construct` says dropping zero
generators denotes the same set. -/
theorem Zonotope.compactZeros_exact (Z : Zonotope α) :
    Z.compactZeros.construct = Z.construct :=
  Z.filterGen_construct _ fun j hj => by simpa using hj

end CORALean.Real


-- =================================  `Zonotope.corner_apply`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

/-- The coordinates of `corner s` in a planar zonotope: `c_k + ∑ ±g_{j,k}`. -/
theorem Zonotope.corner_apply (Z : Zonotope (Vec ℝ 2)) (s : Fin Z.h → Bool) (k : Fin 2) :
    Z.corner s k = Z.c k + ∑ j, (if s j then (1 : ℝ) else -1) * Z.G j k := by
  simp only [Zonotope.corner, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end CORALean.Real


-- ==============================  `Zonotope.isClosed_construct`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       19-August-2026
-- Last update:   04-September-2026
-- Reviewed:      ---

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]

/-- Read off compactness rather than proved directly, because an affine image of a
merely closed set need not be closed. Closedness on its own is what the
integrand of a set-valued integral is asked for. -/
theorem Zonotope.isClosed_construct (Z : Zonotope α) : IsClosed Z.construct :=
  Z.isCompact_construct.isClosed

end CORALean.Real


-- =============================  `Zonotope.minnormOffset_nonneg`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- A sum of absolute values over a square root: the lower bound `0` that makes `minnorm`, an
infimum of offsets, a nonnegative number attained. -/
theorem Zonotope.minnormOffset_nonneg (Z : Zonotope (Vec ℝ (n + 1))) (S : Fin n → Fin Z.h) :
    0 ≤ Z.minnormOffset S :=
  div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Real.sqrt_nonneg _)

end CORALean.Real


-- ================================  `Zonotope.norm₂_le_normUb`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open ContSet

variable {n : ℕ}

/-- The box contains the zonotope (`interval_contains`) and `Interval.norm` bounds the box.
An upper bound only, and not tight in general: a box is larger than its zonotope. -/
theorem Zonotope.norm₂_le_normUb {Z : Zonotope (Vec ℝ n)} {x : Vec ℝ n}
    (hx : x ∈ Z.construct) : ‖x‖₂ ≤ Z.normUb :=
  Interval.norm_le (Z.interval_contains hx)

end CORALean.Real


-- =================================  `Zonotope.project_exact`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n m : ℕ}

/-- Reading the same coordinates of every member, no hypothesis on `dims`: a linear map is exact
without injectivity, so nothing is added and nothing lost. -/
theorem Zonotope.project_exact (Z : Zonotope (Vec ℝ n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' Z.construct = (Z.project dims).construct :=
  Zonotope.map_exact (LinearMap.funLeft ℝ ℝ dims) Z

end CORALean.Real


-- ==================================  `Zonotope.rank_eq_iff`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- `Zonotope.rank_eq_finrank_iff` at `Vec ℝ n`, whose dimension is `n`. -/
theorem Zonotope.rank_eq_iff (Z : Zonotope (Vec ℝ n)) :
    Z.rank = n ↔ (interior Z.construct).Nonempty := by
  rw [← Zonotope.rank_eq_finrank_iff]
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
