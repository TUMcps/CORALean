import CORALean.ContSet.Zonotope.Real.Operations.GeneratorLength

/-!
# A point of a zonotope is within the sum of the generator lengths of the centre

The triangle inequality over `x - c = Σ βⱼ Gⱼ` with `|βⱼ| ≤ 1`: the bound `Zonotope.radius₂`
takes the smaller of this and a box bound.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.norm₂_sub_centre_le_sum_generatorLength {Z : Zonotope (Vec ℝ n)}
    {x : Vec ℝ n} (hx : x ∈ Z.construct) :
    ‖x - Z.c‖₂ ≤ ∑ j, Z.generatorLength j := by -- --- PROOF ---
  obtain ⟨β, hβ, rfl⟩ := hx
  rw [add_sub_cancel_left]
  refine (norm₂_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm₂_smul]
  exact mul_le_of_le_one_left (norm₂_nonneg _) (hβ j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
