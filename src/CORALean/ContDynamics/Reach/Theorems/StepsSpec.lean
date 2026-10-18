module

public import CORALean.ContDynamics.Reach.Operations.Steps

@[expose] public section

/-!
# What a step count `Reach.steps` returns means

`N` steps of `timeStep` span the horizon exactly, and `timeStep` is positive.
A quotient with denominator one is its numerator, and a nonnegative integer is
the cast of its `toNat`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem Reach.steps_spec {tStart tFinal timeStep : ℚ} :
    ∀ N ∈ Reach.steps tStart tFinal timeStep,
      0 < timeStep ∧ (N : ℚ) * timeStep = tFinal - tStart := by -- --- PROOF ---
  intro N (h : Reach.steps tStart tFinal timeStep = some N)
  simp only [Reach.steps] at h
  split_ifs at h with hc
  obtain ⟨hpos, hden, hnn⟩ := hc
  cases h
  -- the quotient is an integer, and a nonnegative one
  have hq : (((tFinal - tStart) / timeStep).num.toNat : ℚ) = (tFinal - tStart) / timeStep := by
    have hnum : 0 ≤ ((tFinal - tStart) / timeStep).num := Rat.num_nonneg.mpr hnn
    rw [show (((tFinal - tStart) / timeStep).num.toNat : ℚ)
        = ((((tFinal - tStart) / timeStep).num.toNat : ℤ) : ℚ) from rfl,
      Int.toNat_of_nonneg hnum]
    exact Rat.coe_int_num_of_den_eq_one hden
  refine ⟨hpos, ?_⟩
  rw [hq, div_mul_cancel₀ _ hpos.ne']

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
