module

public import CORALean.ContSet.Zonotope.Real.Operations.Cloud2zonotopeCompress

@[expose] public section

/-!
# `Zonotope.cloud2zonotopeCompress` moves each point along `g` by at most `g`

[1, Eq. 43]: `X ⊂ X' ⊕ g [-1, 1]`, point by point: every point of the cloud is its compressed
image plus a multiple `t g` with `|t| ≤ 1`. Any `g`, including `0`.

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on
      Automatic Control, 61(9):2341-2356, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ} {κ : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.cloud2zonotopeCompress_mem (X : κ → Vec ℝ n) (g : Vec ℝ n) (j : κ) :
    ∃ t : ℝ, |t| ≤ 1 ∧ X j = Zonotope.cloud2zonotopeCompress X g j + t • g := by -- --- PROOF ---
  simp only [Zonotope.cloud2zonotopeCompress]
  -- the clamped coordinate along `u`
  set d : ℝ := min ‖g‖₂ (max (-‖g‖₂) (X j ⬝ᵥ (‖g‖₂)⁻¹ • g)) with hd
  by_cases h0 : ‖g‖₂ = 0
  · -- `g = 0`: `u = 0`, nothing moves
    have hg : g = 0 := by
      by_contra hne
      have : 0 < ‖g‖₂ := by
        unfold norm₂
        apply Real.sqrt_pos.mpr
        by_contra hle
        apply hne
        funext i
        have hs : ∑ i, g i ^ 2 = 0 :=
          le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun i _ => sq_nonneg _)
        have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (g i)).mp hs i
          (Finset.mem_univ i)
        simpa using this
      exact absurd h0 this.ne'
    subst hg
    exact ⟨0, by simp, by simp⟩
  · -- `g ≠ 0`: the multiple is `d / ‖g‖`
    have hpos : 0 < ‖g‖₂ := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h0)
    refine ⟨d / ‖g‖₂, ?_, ?_⟩
    · rw [abs_div, abs_of_pos hpos, div_le_one hpos, abs_le]
      constructor
      · exact le_min (by linarith) (le_max_left _ _)
      · exact min_le_left _ _
    · funext r
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
