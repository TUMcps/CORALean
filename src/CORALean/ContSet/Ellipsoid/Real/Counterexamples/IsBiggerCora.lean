module

public import CORALean.ContSet.Ellipsoid.Real.Operations.IsBigger
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsBiggerIffSubset
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-!
# `Ellipsoid.isBiggerCora`

CORA's `@ellipsoid/isBigger` as the code answers: in dimension `1` it returns `true` before
looking at the ellipsoids (`if dim(E1)==1 res = true`), otherwise the test of `isBigger`.
`isBigger_cora_counterexample` shows the shortcut is wrong.

# CORA's `isBigger` answers `true` for every pair in dimension `1`

The intervals `[-2, 2]` (`Q = 4`) and `[-1, 1]` (`Q = 1`) in `ℝ¹`: the first does not lie in
the second, so `isBigger([-1, 1], [-2, 2])` is `false`, yet CORA's `dim(E1)==1` shortcut
returns `true`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's `isBigger` holds though the inclusion fails
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
def Ellipsoid.isBiggerCora (E₁ E₂ : Ellipsoid n) : Prop := n = 1 ∨ E₁.isBigger E₂

end CORALean.Real

namespace CORALean.Real

open Matrix
open scoped MatrixOrder


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isBigger_cora_counterexample : -- --- CONCL ---
    ∃ E₁ E₂ : Ellipsoid 1, E₁.isBiggerCora E₂ ∧
      ¬ ((fun x => x - E₂.q) '' E₂.construct ⊆
        (fun x => x - E₁.q) '' E₁.construct) := by -- --- PROOF ---
  -- the data: shape `1` and shape `4`
  let E₁ : Ellipsoid 1 := ⟨1, 0, .one⟩
  let E₂ : Ellipsoid 1 := ⟨(4 : ℝ) • 1, 0, PosSemidef.one.smul (by norm_num)⟩
  refine ⟨E₁, E₂, Or.inl rfl, ?_⟩
  -- `E₁` has full rank, so containment is `isBigger`, which fails at `v = 1`
  have hr : E₁.rank = 1 := by
    show (1 : Mat ℝ 1 1).rank = 1
    simp
  rw [← Ellipsoid.isBigger_iff_subset E₁ E₂ hr]
  intro h
  have := h (fun _ => 1)
  simp [E₁, E₂, Matrix.mulVec, dotProduct] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
