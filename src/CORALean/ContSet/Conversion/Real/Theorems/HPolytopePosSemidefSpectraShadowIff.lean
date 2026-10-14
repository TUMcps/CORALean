module

public import CORALean.Global.BlockDiag
public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Theorems.Basic

@[expose] public section

/-!
# A polytope as a spectrahedral shadow

Exact. CORA's `@polytope/spectraShadow` stacks `C = [A; Ae; -Ae]` and `d = [b; be; -be]` and
writes one 1x1 block `d_j - C_j x` per row: `A₀ = diag(d)`, `A_i = diag(-C(:,i))`. A diagonal
matrix is positive semidefinite exactly when its entries are nonnegative, so the inequality
holds exactly on the polytope. The centre is `0` and the generators are the unit vectors.
With no rows the matrices are `0 × 0`, trivially positive semidefinite, and the shadow is the
whole space, which is what CORA's `spectraShadow.Inf(n)` branch returns.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The inequality's matrix is the diagonal of the slacks `d_j - C_j β`. -/
theorem HPolytope.aux_lmi_spectraShadow (P : HPolytope (Vec ℝ n)) (β : Fin n → ℝ) :
    (diagonal P.stackedBounds + ∑ i, β i • diagonal fun j =>
        -(P.stackedRows j (Pi.single i 1 : Fin n → ℝ)) : Mat ℝ (P.m + P.me + P.me) _)
      = diagonal fun j => P.stackedBounds j - P.stackedRows j β := by -- --- PROOF ---
  ext j k
  by_cases hjk : j = k
  · subst hjk
    have h := congrArg (P.stackedRows j) (HPolytope.eq_sum_single β)
    rw [map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    simp [Matrix.sum_apply, h, sub_eq_add_neg, Finset.sum_neg_distrib]
  · simp [Matrix.sum_apply, hjk]

/-- The slacks are all nonnegative exactly on the polytope. -/
theorem HPolytope.aux_slack_iff (P : HPolytope (Vec ℝ n)) (β : Fin n → ℝ) :
    (∀ j, 0 ≤ P.stackedBounds j - P.stackedRows j β) ↔ β ∈ P.construct := by -- --- PROOF ---
  simp only [HPolytope.stackedBounds, HPolytope.stackedRows, Fin.forall_fin_add, Fin.append_left,
    Fin.append_right, LinearMap.neg_apply, sub_nonneg]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    exact ⟨h₁, fun i => le_antisymm (h₂ i) (by linarith [h₃ i])⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨h₁, fun i => (h₂ i).le⟩, fun i => by linarith [h₂ i]⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.posSemidef_spectraShadow_iff (P : HPolytope (Vec ℝ n)) (β : Fin n → ℝ) :
    (P.spectraShadow.A₀ + ∑ i, β i • P.spectraShadow.A i).PosSemidef ↔ β ∈ P.construct := by
  change (diagonal P.stackedBounds + ∑ i, β i • diagonal fun j =>
    -(P.stackedRows j (Pi.single i 1 : Fin n → ℝ)) : Mat ℝ (P.m + P.me + P.me) _).PosSemidef ↔ _
  rw [HPolytope.aux_lmi_spectraShadow, posSemidef_diagonal_iff]
  exact (HPolytope.aux_slack_iff P β)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
