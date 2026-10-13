module

public import CORALean.ContSet.Ellipsoid.Real.Operations.IsBiggerCora
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsBiggerIffSubset
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-!
# CORA's `isBigger` answers `true` for every pair in dimension `1`

The intervals `[-2, 2]` (`G = 2`) and `[-1, 1]` (`G = 1`) in `ℝ¹`: the first does not lie in
the second, so `isBigger([-1, 1], [-2, 2])` is `false`, yet CORA's `dim(E1)==1` shortcut
returns `true`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isBigger_cora_counterexample :
    ∃ E₁ E₂ : Ellipsoid 1, E₁.isBiggerCora E₂ ∧
      ¬ ((fun x => x - E₂.q) '' E₂.construct ⊆
        (fun x => x - E₁.q) '' E₁.construct) := by -- --- PROOF ---
  -- the data, unit and double generator
  let E₁ : Ellipsoid 1 := ⟨1, 0, 1⟩
  let E₂ : Ellipsoid 1 := ⟨1, 0, Matrix.of fun _ _ => 2⟩
  refine ⟨E₁, E₂, Or.inl rfl, ?_⟩
  -- `E₁` has full rank, so containment is `isBigger`, which fails at `v = 1`
  have hr : E₁.rank = 1 := by
    show (1 : Mat ℝ 1 1).rank = 1
    simp
  rw [← Ellipsoid.isBigger_iff_subset E₁ E₂ hr]
  intro h
  have := h (fun _ => 1)
  simp [E₁, E₂, Ellipsoid.shape, Matrix.mulVec, dotProduct, Matrix.mul_apply] at this
  norm_num at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
