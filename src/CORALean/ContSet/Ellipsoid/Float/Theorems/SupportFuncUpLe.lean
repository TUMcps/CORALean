module

public import CORALean.ContSet.Ellipsoid.Float.Operations.SupportFuncUp
public import CORALean.ContSet.Ellipsoid.Float.Operations.NominalBoundDot
public import CORALean.ContSet.Ellipsoid.Float.Theorems.NominalCenterEq
public import CORALean.ContSet.Ellipsoid.Float.Theorems.NominalQEq
public import CORALean.ContSet.Interval.Float.Operations.BoundDot

@[expose] public section

/-!
# `Ellipsoid.supportFuncUp` bounds the support function

A point of the set is a nominal point plus a point of the error box. The nominal point reads at
most the exact support value `aᵀq + √(aᵀ Q a)`; the shift is below `dotUp`, the form below `quadUp`
and its root below the upward root. The box's point reads at most the box's own bound
(`Interval.boundDot`), and the sums are rounded up.

## Inputs
* `k` – Newton steps of the square root
* `E` – ellipsoid
* `c` – linear functional
* `a` – float vector of `c`

## Hypotheses
* `hc` – `c x = ∑ aᵢ xᵢ`

## Conclusion
* `c` is at most `supportFuncUp k a` on every point of `E`
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet
open scoped Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A functional given by a float vector has that vector, read as reals, as its `dualVec`. -/
private theorem Ellipsoid.aux_dualVec_eq {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) : -- --- CONCL ---
    Real.dualVec c = toRealVec a := by -- --- PROOF ---
  funext i
  rw [Real.dualVec, hc, Finset.sum_eq_single i]
  · rw [if_pos rfl, mul_one]
    rfl
  · intro b _ hb
    rw [if_neg (Ne.symm hb), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The nominal part reads at most the shift and the spread, unrounded. -/
private theorem Ellipsoid.aux_nominal_le (k : ℕ) (E : Ellipsoid 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (a : Vec 𝕋 n) (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) {y : Vec ℝ n}
    (hy : y ∈ nominalSet E) : -- --- CONCL ---
    c y ≤ toReal (dotUp a E.q)
      + toReal (sqrtUp k (maximum zero (E.quadUp a))) := by -- --- PROOF ---
  have hle := ((nominal E).ellipsoid.supportBound c).le y hy
  -- the shift: the nominal center is the stored one
  have h₁ : c (nominal E).ellipsoid.q ≤ toReal (dotUp a E.q) := by
    rw [hc, E.nominal_q]
    exact le_dotUp a E.q
  -- the form: the stored one, or `0` where the shape is refused
  have hquad : Real.dualVec c ⬝ᵥ ((nominal E).ellipsoid.Q *ᵥ Real.dualVec c)
      ≤ toReal (maximum zero (E.quadUp a)) := by
    rw [Ellipsoid.aux_dualVec_eq a hc, Ellipsoid.nominal_Q_eq, toReal_maximum, toReal_zero]
    split_ifs
    · exact le_trans (E.quad_le_quadUp a) (le_max_right _ _)
    · simp
  have h₂ := le_trans (Real.sqrt_le_sqrt hquad) (le_sqrtUp k (maximum zero (E.quadUp a)))
  have hval : c y ≤ c (nominal E).ellipsoid.q
      + Real.sqrt (Real.dualVec c ⬝ᵥ ((nominal E).ellipsoid.Q *ᵥ Real.dualVec c)) := hle
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.supportFuncUp_le (k : ℕ) (E : Ellipsoid 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (a : Vec 𝕋 n) (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) : -- --- CONCL ---
    ∀ x ∈ E.toSet, c x ≤ toReal (E.supportFuncUp k a) := by -- --- PROOF ---
  rintro _ ⟨y, hy, e, he, rfl⟩
  -- the nominal point and the point of the box, each below its bound
  have hy' := Ellipsoid.aux_nominal_le k E a hc hy
  have he' : c e ≤ toReal (E.I_error.boundDot a hc).val := (E.I_error.boundDot a hc).le e he
  -- the two sums, rounded up
  have h₃ := add_le_addUp (dotUp a E.q) (sqrtUp k (maximum zero (E.quadUp a)))
  have h₄ := add_le_addUp (addUp (dotUp a E.q) (sqrtUp k (maximum zero (E.quadUp a))))
    (E.I_error.boundDot a hc).val
  show c (y + e) ≤ toReal (addUp (addUp (dotUp a E.q) (sqrtUp k (maximum zero (E.quadUp a))))
    (E.I_error.boundDot a hc).val)
  rw [map_add]
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
