module

public import CORALean.ContDynamics.LinearSys.Operations.ExpSquaringFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter

@[expose] public section

/-!
# `e^{At}` lies in `expSquaringFloat` at every time of its range

`t/2^s` lies in the halved range, `half` being exact, so
`exp_mem_expIntervalFloat` puts `e^{A t/2^s}` in the base enclosure; then by
induction `e^{A t 2^j/2^s}` is in the `j`-th square, since
`e^{2xA} = e^{xA} e^{xA}` and `Interval.matMul_outer` holds a product of members.

## Inputs
* `sys` – linear system
* `tLo` – lower time bound
* `tHi` – upper time bound
* `η` – Taylor order
* `s` – number of squarings
* `t` – time

## Hypotheses
* `hη` – order admissible for the halved range
* `htLo` – time at least the lower bound
* `htHi` – time at most the upper bound

## Conclusion
* the exponential at the time lies in the squared float enclosure
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
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
theorem LinearSys.aux_toReal_half_iterate (a : 𝕋) :
    ∀ s : ℕ, toReal (half^[s] a) = toReal a / 2 ^ s := by -- --- PROOF ---
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply', toReal_half, ih, pow_succ]
    ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.exp_mem_expSquaringFloat (sys : LinearSys 𝕋 n) {tLo tHi : 𝕋} {η s : ℕ}
    (hη : sys.OrderAdmissibleFloat (half^[s] tLo) (half^[s] tHi) η) {t : ℝ}
    (htLo : toReal tLo ≤ t) (htHi : t ≤ toReal tHi) : -- --- CONCL ---
    exp (t • Scalar.toRealMat sys.A)
      ∈ (sys.expSquaringFloat tLo tHi η s).construct := by -- --- PROOF ---
  have h2s : (0 : ℝ) < 2 ^ s := by positivity
  -- the base: `t / 2^s` is in the halved range
  have hbase := sys.exp_mem_expIntervalFloat hη (t := t / 2 ^ s)
    (by rw [LinearSys.aux_toReal_half_iterate]; exact div_le_div_of_nonneg_right htLo h2s.le)
    (by rw [LinearSys.aux_toReal_half_iterate]; exact div_le_div_of_nonneg_right htHi h2s.le)
  -- each squaring doubles the time
  have hsq : ∀ j ≤ s, exp ((t / 2 ^ s * 2 ^ j) • Scalar.toRealMat sys.A) ∈
      ((fun P => (Interval.matMul P P).materialiseMat)^[j]
        (sys.expIntervalFloat (half^[s] tLo) (half^[s] tHi) η)).construct := by
    intro j _
    induction j with
    | zero => simpa using hbase
    | succ j ih =>
      rw [Function.iterate_succ_apply', Interval.materialiseMat_eq]
      have hc : Commute ((t / 2 ^ s * 2 ^ j) • Scalar.toRealMat sys.A)
          ((t / 2 ^ s * 2 ^ j) • Scalar.toRealMat sys.A) := Commute.refl _
      have hexp := exp_add_of_commute hc
      rw [← add_smul, show t / 2 ^ s * 2 ^ j + t / 2 ^ s * 2 ^ j = t / 2 ^ s * 2 ^ (j + 1)
        by rw [pow_succ]; ring] at hexp
      convert Interval.matMul_outer _ _ (ih (by omega)) (ih (by omega)) using 1
      exact hexp
  have h := hsq s le_rfl
  rwa [div_mul_cancel₀ t h2s.ne'] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
