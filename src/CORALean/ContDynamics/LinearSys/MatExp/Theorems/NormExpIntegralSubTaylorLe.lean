module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegral
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpIntegralTermLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TsumLeExpTail

@[expose] public section

/-!
# Truncating the integrated exponential costs one step times the remainder

`expIntegral` is the exponential integrated once over `[0, r]`, so its order `i`
carries `r^{i+1}/(i+1)!` where the exponential carries `r^i/i!`. One factor of
`r` comes out in front and the rest is bounded by the exponential's own tail,
which is why `inputRemainder`'s radius is `r · expRemainderBound (r A) η` and not
a bound of its own.

`norm_expIntegralTerm_le` is the estimate one order at a time; here it is summed
over the orders past `η`, every one of which is at least `1`, which is what lets
that estimate apply at all.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- What the integrated series has left after order `η`. -/
theorem MatExp.norm_expIntegral_sub_taylor_le (A : Mat ℝ n n) {r : ℝ} (hr : 0 ≤ r) (η : ℕ)
    (hε : ‖r • A‖ / ((η : ℝ) + 2) < 1) : -- --- CONCL ---
    ‖MatExp.expIntegral A r
        - ∑ i ∈ Finset.range (η + 1), ((Nat.factorial (i + 1) : ℝ)⁻¹ * r ^ (i + 1)) • A ^ i‖
      ≤ r * MatExp.expRemainderBound (r • A) η := by -- --- PROOF ---
  set f : ℕ → Mat ℝ n n := fun i => ((Nat.factorial (i + 1) : ℝ)⁻¹ * r ^ (i + 1)) • A ^ i
    with hf
  have hEI : MatExp.expIntegral A r = ∑' i : ℕ, f i := rfl
  have hsum : Summable f := MatExp.summable_expIntegral A r
  have hnorm : Summable (fun i => ‖f i‖) := MatExp.summable_norm_expIntegral A r
  -- what is left past order `η`, as a tail of the same series
  have htail : MatExp.expIntegral A r - ∑ i ∈ Finset.range (η + 1), f i
      = ∑' i : ℕ, f (i + (η + 1)) := by
    rw [hEI, ← hsum.sum_add_tsum_nat_add (η + 1)]
    abel
  have hns : Summable (fun i : ℕ => ‖f (i + (η + 1))‖) :=
    (summable_nat_add_iff (f := fun i => ‖f i‖) (η + 1)).mpr hnorm
  rw [htail]
  refine (norm_tsum_le_tsum_norm hns).trans ?_
  rw [MatExp.expRemainderBound, hf]
  exact tsum_le_expTail (norm_nonneg _) hr η hε (fun _ => norm_nonneg _)
    (fun i => MatExp.norm_expIntegralTerm_le A hr (by omega))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
