import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoRemainder

/-!
# Every matrix within the bound lies in the remainder zonotope

The generator carrying entry `(i, j)` is the only one that reaches it, so the
coefficient it needs is that entry's share of the bound. A zero bound pins every
entry to zero and the coefficient with it, which is the only case the division
has to be kept away from.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The share of the bound that entry `(i, j)` takes, zero where there is none
to take. -/
noncomputable def MatExp.aux_remCoeff (b : ℝ) (D : Mat ℝ m m) (k : Fin (m * m)) : ℝ :=
  if b = 0 then 0 else D (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 / b


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.mem_expMatZonoRemainder {b : ℝ} {D : Mat ℝ m m} (hD : ∀ i j, |D i j| ≤ b) :
    D ∈ (MatExp.expMatZonoRemainder m b).construct := by -- --- PROOF ---
  refine ⟨MatExp.aux_remCoeff b D, fun k => ?_, ?_⟩
  -- an entry never exceeds the bound, so its share of the generator stays in `[-1, 1]`
  · by_cases hb : b = 0
    · simp [MatExp.aux_remCoeff, hb]
    · set q := finProdFinEquiv.symm k with hq
      have hpos : 0 < b :=
        lt_of_le_of_ne (le_trans (abs_nonneg (D q.1 q.2)) (hD q.1 q.2)) (Ne.symm hb)
      rw [MatExp.aux_remCoeff, ← hq, if_neg hb, abs_div, abs_of_pos hpos, div_le_one hpos]
      exact hD q.1 q.2
  · refine Matrix.ext fun i j => ?_
    show D i j = ((0 : Mat ℝ m m) + ∑ k, MatExp.aux_remCoeff b D k •
      (MatExp.expMatZonoRemainder m b).G k) i j
    rw [Matrix.add_apply, Matrix.zero_apply, zero_add, Matrix.sum_apply,
      Finset.sum_eq_single (finProdFinEquiv (i, j))]
    -- the one generator that reaches `(i, j)`, carrying exactly the bound there
    · by_cases hb : b = 0
      · have hz : D i j = 0 := by
          have := hD i j
          rw [hb] at this
          exact abs_nonpos_iff.mp this
        simp [MatExp.aux_remCoeff, MatExp.expMatZonoRemainder, hb, hz]
      · simp only [MatExp.aux_remCoeff, MatExp.expMatZonoRemainder, Matrix.smul_apply,
          smul_eq_mul, if_neg hb, Equiv.symm_apply_apply, if_true]
        field_simp
    · intro k _ hk
      simp only [MatExp.expMatZonoRemainder, Matrix.smul_apply, smul_eq_mul,
        if_neg (Ne.symm hk), mul_zero]
    · intro hc
      exact absurd (Finset.mem_univ _) hc

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
