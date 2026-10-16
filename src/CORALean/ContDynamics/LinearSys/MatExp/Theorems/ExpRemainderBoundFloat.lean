module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.FactorialDownFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PowUpFloat

@[expose] public section

/-!
# `MatExp.expRemainderBound` bounds the real remainder, under a margin

Two roundings composed: the real bound at `‖x‖` is first bounded, entirely in
ℝ, by the numerator at `toReal nrm` times the constant `2` (`hε` keeping the
geometric factor under it); then `powUp`, `factorialDown` and the two
`divUp`/`mulUp` calls each pay their own rounding to reach the float value.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The real bound, at `toReal nrm` rather than `‖x‖`, with the geometric
factor collapsed to the constant `2`. -/
theorem aux_expRemainderBound_real {n : ℕ} {x : Mat ℝ n n} {r : ℝ} (η : ℕ) (hx : ‖x‖ ≤ r)
    (hε : r / ((η : ℝ) + 2) ≤ 1 / 2) :
    Real.MatExp.expRemainderBound x η
      ≤ (r ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) * 2 := by -- --- PROOF ---
  have hxnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hrnn : (0 : ℝ) ≤ r := le_trans hxnn hx
  have h2 : (0 : ℝ) < (η : ℝ) + 2 := by positivity
  have hxr : ‖x‖ / ((η : ℝ) + 2) ≤ r / ((η : ℝ) + 2) := by gcongr
  have h12 : (1 : ℝ) / 2 ≤ 1 - ‖x‖ / ((η : ℝ) + 2) := by linarith [le_trans hxr hε]
  have hgeom : (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹ ≤ 2 := by
    have hh := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) h12
    norm_num at hh; exact hh
  have hnum0 : ‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)
      ≤ r ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) := by gcongr
  calc Real.MatExp.expRemainderBound x η
      = (‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) * (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹ := rfl
    _ ≤ (r ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) * 2 :=
        mul_le_mul hnum0 hgeom (inv_nonneg.mpr (by linarith)) (by positivity)


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expRemainderBound_le {n : ℕ} {x : Mat ℝ n n} {nrm : 𝕋} (η : ℕ)
    (hx : ‖x‖ ≤ toReal nrm) (hnn : 0 ≤ toReal nrm) (hε : toReal nrm / ((η : ℝ) + 2) ≤ 1 / 2) :
    Real.MatExp.expRemainderBound x η
      ≤ toReal (MatExp.expRemainderBound nrm η) := by -- --- PROOF ---
  have hfactpos : (0 : ℝ) < (Nat.factorial (η + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (η + 1)
  have hreal := aux_expRemainderBound_real η hx hε
  have hpow : toReal nrm ^ (η + 1) ≤ toReal (MatExp.powUp (η + 1) nrm) :=
    MatExp.le_powUp hnn (η + 1)
  have hfd := MatExp.factorialDown_mem (𝕋 := 𝕋) (η + 1)
  have hfdpos : (0 : ℝ) < toReal (MatExp.factorialDown (𝕋 := 𝕋) (η + 1)) :=
    lt_of_lt_of_le zero_lt_one hfd.1
  have hpownn : (0 : ℝ) ≤ toReal (MatExp.powUp (η + 1) nrm) :=
    le_trans (by positivity) hpow
  -- the numerator up, then the denominator down to `factorialDown`, then `divUp`
  have step1 : toReal nrm ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)
      ≤ toReal (MatExp.powUp (η + 1) nrm) / (Nat.factorial (η + 1) : ℝ) :=
    div_le_div_of_nonneg_right hpow hfactpos.le
  have step2 : toReal (MatExp.powUp (η + 1) nrm) / (Nat.factorial (η + 1) : ℝ)
      ≤ toReal (MatExp.powUp (η + 1) nrm) / toReal (MatExp.factorialDown (𝕋 := 𝕋) (η + 1)) :=
    div_le_div_of_nonneg_left hpownn hfdpos hfd.2
  have step3 : toReal (MatExp.powUp (η + 1) nrm) / toReal (MatExp.factorialDown (𝕋 := 𝕋) (η + 1))
      ≤ toReal (divUp (MatExp.powUp (η + 1) nrm) (MatExp.factorialDown (η + 1))) :=
    div_le_divUp (MatExp.powUp (η + 1) nrm) (MatExp.factorialDown (η + 1)) hfdpos
  have hchain : toReal nrm ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)
      ≤ toReal (divUp (MatExp.powUp (η + 1) nrm) (MatExp.factorialDown (η + 1))) :=
    le_trans step1 (le_trans step2 step3)
  have h2u : (2 : ℝ) ≤ toReal (addUp (one : 𝕋) one) := by
    have h := add_le_addUp (one : 𝕋) one
    rw [toReal_one] at h
    linarith
  -- the two rounded factors, multiplied, then `mulUp` to reach the stored value
  refine le_trans hreal ?_
  calc (toReal nrm ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) * 2
      ≤ toReal (divUp (MatExp.powUp (η + 1) nrm) (MatExp.factorialDown (η + 1)))
          * toReal (addUp (one : 𝕋) one) :=
        mul_le_mul hchain h2u (by norm_num) (le_trans (by positivity) hchain)
    _ ≤ toReal (MatExp.expRemainderBound nrm η) := by
        rw [MatExp.expRemainderBound]
        exact mul_le_mulUp _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
