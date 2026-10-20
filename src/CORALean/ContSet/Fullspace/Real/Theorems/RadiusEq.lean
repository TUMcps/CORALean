module

public import CORALean.ContSet.Fullspace.Real.Operations.Basic
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

/-!
# `Fullspace.radius` is the radius of the set

The supremum of the norms over the whole space is unbounded in positive dimension: the point
with one coordinate `r` has norm `r`, for every `r`.

## Inputs
* `F` – full space

## Hypotheses
* `hn` – dimension positive

## Conclusion
* the supremum of the norms is `F.radius`
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.radius_eq (hn : 0 < n) (F : Fullspace n) : -- --- CONCL ---
    ⨆ x ∈ F.construct, (‖x‖₊ : ENNReal) = F.radius := by -- --- PROOF ---
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  refine le_iSup₂_of_le (Pi.single ⟨0, hn⟩ (r : ℝ) : Vec ℝ n) (Set.mem_univ _) ?_
  have : ‖(Pi.single ⟨0, hn⟩ (r : ℝ) : Vec ℝ n)‖₊ = r := by
    rw [← NNReal.coe_inj, coe_nnnorm, Pi.norm_single]
    simp
  rw [this]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
