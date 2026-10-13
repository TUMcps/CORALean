module

public import CORALean.ContSet.Zonotope.Real.Definitions.PRadius
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

/-!
# The bound of Eq. 28 of [1, Thm. 4] as printed fails

[1, Thm. 4] prints `ℓ_{W+} < max_z ‖M z‖²₂` Eq. 28 of [1, Thm. 4]. In one dimension, the zonotope
`⟨0, [1/2]⟩`, `W = 1` and `M = [1/2]` satisfy the matrix inequality Eq. 27 of [1, Thm. 4],
`[1/2 1/2; 1/2 1] ≻ 0`, yet the W-radius is `1/4` and `max_{|z| ≤ 1} (z/2)² = 1/4`, so the strict
inequality fails. `M - ĤᵀWĤ = 1/4 > 0` bounds `zᵀĤᵀWĤz` by `zᵀMz = z²/2`, not by `‖Mz‖² = z²/4`:
the corrected bound is `Zonotope.pRadius_lt_of_lmi`.

## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 93:435-443, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.pRadius_lt_of_lmi_counterexample :
    let Z : Zonotope (Vec ℝ 1) := ⟨1, 0, fun _ _ => 1 / 2⟩
    let W : Mat ℝ 1 1 := 1
    let m : Vec ℝ 1 := fun _ => 1 / 2
    let H : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun i j => Z.G j i
    W.PosDef ∧ (fromBlocks (diagonal m) (W * H)ᵀ (W * H) W).PosDef ∧
      ¬ Z.pRadius W < sSup ((fun z : Vec ℝ 1 => (diagonal m *ᵥ z) ⬝ᵥ (diagonal m *ᵥ z)) ''
        {z | ∀ i, |z i| ≤ 1}) := by -- --- PROOF ---
  intro Z W m H
  refine ⟨PosDef.one, ?_, ?_⟩
  · -- `[1/2 1/2; 1/2 1]`: its form is `(a + b)²/2 + b²/2`
    refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
    · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [W, H, Z, fromBlocks]
    · have hx' : x (Sum.inl 0) ≠ 0 ∨ x (Sum.inr 0) ≠ 0 := by
        by_contra h
        push Not at h
        exact hx (funext fun k => by rcases k with k | k <;> fin_cases k <;> simp [h.1, h.2])
      simp only [star_trivial, dotProduct, mulVec, fromBlocks, Fintype.sum_sum_type,
        Fin.sum_univ_one, of_apply, Sum.elim_inl, Sum.elim_inr]
      simp [W, H, Z, m]
      rcases hx' with h | h
      · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x (Sum.inl 0) + x (Sum.inr 0)),
          sq_nonneg (x (Sum.inr 0))]
      · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x (Sum.inl 0) + x (Sum.inr 0))]
  · -- the radius is `1/4`, the printed bound at most `1/4`
    have hval : ∀ z ∈ Z.construct, (z - Z.c) ⬝ᵥ (W *ᵥ (z - Z.c)) ≤ 1 / 4 := by
      rintro _ ⟨β, hβ, rfl⟩
      have h := hβ 0
      simp [Z, W, dotProduct, abs_le] at h ⊢
      nlinarith [h.1, h.2]
    have hge : 1 / 4 ≤ Z.pRadius W := by
      refine le_csSup ⟨1 / 4, ?_⟩ ⟨fun _ => 1 / 2, ⟨fun _ => 1, by simp, ?_⟩, ?_⟩
      · rintro _ ⟨z, hz, rfl⟩; exact hval z hz
      · ext i; fin_cases i; simp [Z]
      · simp [Z, W, dotProduct]; norm_num
    have hle : sSup ((fun z : Vec ℝ 1 => (diagonal m *ᵥ z) ⬝ᵥ (diagonal m *ᵥ z)) ''
        {z | ∀ i, |z i| ≤ 1}) ≤ 1 / 4 := by
      refine csSup_le ⟨_, 0, by simp, rfl⟩ ?_
      rintro _ ⟨z, hz, rfl⟩
      have h := hz 0
      simp [m, dotProduct, mulVec_diagonal, abs_le] at h ⊢
      nlinarith [h.1, h.2]
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
