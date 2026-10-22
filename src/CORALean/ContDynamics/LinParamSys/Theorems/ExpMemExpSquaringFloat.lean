module

public import CORALean.ContDynamics.LinParamSys.Operations.ExpSquaringFloat
public import CORALean.ContDynamics.LinParamSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Instances

@[expose] public section

/-!
# `e^{At}` lies in `expSquaringFloat` at every member and every time of its range

`LinearSys.exp_mem_expSquaringFloat` at a member `A ∈ sys.A`: the base holds
`e^{A t/2^s}` at the halved range, and each squaring doubles the time, the same
member in both factors so `Interval.matMul_outer` applies.

## Inputs
* `sys` – system
* `tLo` – lower time bound
* `tHi` – upper time bound
* `η` – Taylor order
* `s` – number of squarings
* `A` – system matrix member
* `t` – time

## Hypotheses
* `hη` – order admissible
* `hA` – `A` lies in the matrix set
* `htLo` – time at least the lower bound
* `htHi` – time at most the upper bound

## Conclusion
* the member's exponential lies in the squaring enclosure
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Halving `s` times divides by `2^s`, exactly. -/
theorem LinParamSys.aux_toReal_half_iterate (a : 𝕋) : -- --- CONCL ---
    ∀ s : ℕ, toReal (half^[s] a) = toReal a / 2 ^ s := by -- --- PROOF ---
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply', toReal_half, ih, pow_succ]
    ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.exp_mem_expSquaringFloat
    (sys : LinParamSys ℐ[𝕋] n) {tLo tHi : 𝕋} {η s : ℕ}
    (hη : sys.OrderAdmissibleFloat (half^[s] tLo) (half^[s] tHi) η) {A : Mat ℝ n n}
    (hA : A ∈ sys.A.construct) {t : ℝ} (htLo : toReal tLo ≤ t)
    (htHi : t ≤ toReal tHi) : -- --- CONCL ---
    exp (t • A) ∈ (sys.expSquaringFloat tLo tHi η s).construct := by -- --- PROOF ---
  have h2s : (0 : ℝ) < 2 ^ s := by positivity
  -- the base: `t / 2^s` is in the halved range
  have hbase := sys.exp_mem_expIntervalFloat hη hA (t := t / 2 ^ s)
    (by rw [LinParamSys.aux_toReal_half_iterate]; exact div_le_div_of_nonneg_right htLo h2s.le)
    (by rw [LinParamSys.aux_toReal_half_iterate]; exact div_le_div_of_nonneg_right htHi h2s.le)
  -- each squaring doubles the time
  have hsq : ∀ j ≤ s, exp ((t / 2 ^ s * 2 ^ j) • A) ∈
      ((fun P => (Interval.matMul P P).materialiseMat)^[j]
        (sys.expIntervalFloat (half^[s] tLo) (half^[s] tHi) η)).construct := by
    intro j _
    induction j with
    | zero => simpa using hbase
    | succ j ih =>
      rw [Function.iterate_succ_apply', Interval.materialiseMat_eq]
      have hc : Commute ((t / 2 ^ s * 2 ^ j) • A) ((t / 2 ^ s * 2 ^ j) • A) := Commute.refl _
      have hexp := exp_add_of_commute hc
      rw [← add_smul, show t / 2 ^ s * 2 ^ j + t / 2 ^ s * 2 ^ j = t / 2 ^ s * 2 ^ (j + 1)
        by rw [pow_succ]; ring] at hexp
      convert Interval.matMul_outer _ _ (ih (by omega)) (ih (by omega)) using 1
      exact hexp
  have h := hsq s le_rfl
  rwa [div_mul_cancel₀ t h2s.ne'] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
