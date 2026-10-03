import CORALean.ContSet.Taylm.Real.Definitions.Scaled

/-!
# The weight is nonnegative

A sum of magnitudes over positive powers of a positive `h`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.weight_nonneg (L : List (ℝ × (Fin n → ℕ))) {h : ℝ} (h0 : 0 < h) :
    0 ≤ Taylm.weight L h :=
  List.sum_nonneg fun x hx => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact div_nonneg (abs_nonneg _) (pow_pos h0 _).le

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
