import CORALean.ContSet.Fullspace.Real.Operations.Radius

/-!
# `Fullspace.radius` is the radius of the set

The supremum of the norms over the whole space is unbounded in positive dimension: the point
with one coordinate `r` has norm `r`, for every `r`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.radius_eq (hn : 0 < n) (F : Fullspace n) :
    ⨆ x ∈ F.construct, (‖x‖₊ : ENNReal) = F.radius := by -- --- PROOF ---
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  refine le_iSup₂_of_le (Pi.single ⟨0, hn⟩ (r : ℝ) : Vec ℝ n) (Set.mem_univ _) ?_
  have : ‖(Pi.single ⟨0, hn⟩ (r : ℝ) : Vec ℝ n)‖₊ = r := by
    rw [← NNReal.coe_inj, coe_nnnorm, Pi.norm_single]
    simp
  rw [this]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
