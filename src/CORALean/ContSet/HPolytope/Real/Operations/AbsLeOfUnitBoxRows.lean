import CORALean.ContSet.HPolytope.Real.Operations.MemUnitBoxIff

/-!
# The box read at a weight

`unitBox`'s rows against a weighted right-hand side bound the coordinates by
that weight. What makes it worth stating is the weight zero, where the rows say
the point is the origin and no rescaling reaches them: the bound comes from
every weight strictly above instead.

This is what pins one side of a convex combination to a point as its weight
vanishes, and so what makes the combination exact at its endpoints.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.abs_le_of_unitBox_rows {u : Vec ℝ n} {w : ℝ} (hw : 0 ≤ w)
    (h : ∀ i, (HPolytope.unitBox n).A i u ≤ w * (HPolytope.unitBox n).b i) (j : Fin n) :
    |u j| ≤ w := by -- --- PROOF ---
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hpos : (0:ℝ) < w + ε := by linarith
  -- at any weight above `w` the point rescales into the box itself
  have hmem : (w + ε)⁻¹ • u ∈ (HPolytope.unitBox n).construct := by
    refine ⟨fun i => ?_, fun i => i.elim0⟩
    rw [map_smul, smul_eq_mul]
    have hrow : (HPolytope.unitBox n).A i u ≤ w * 1 := h i
    have hb : (HPolytope.unitBox n).b i = 1 := rfl
    rw [hb]
    rw [inv_mul_le_iff₀ hpos]
    linarith
  have hj := (HPolytope.mem_unitBox_iff.mp hmem) j
  rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hpos)] at hj
  rw [inv_mul_le_iff₀ hpos] at hj
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
