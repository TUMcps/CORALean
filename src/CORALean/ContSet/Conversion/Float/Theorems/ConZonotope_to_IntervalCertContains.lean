module

public import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_IntervalCert
public import CORALean.ContSet.Conversion.Float.Theorems.ConZonotopeIntervalTightContains
public import CORALean.ContSet.Interval.Float.Theorems.IntersectionExact

@[expose] public section

/-!
# The box from dual certificates holds the constrained zonotope, at every multiplier

Each end is a `FloatBound` of `boundDotWeights`, sound at every weight vector, along `eᵢ` for the
upper end and `−eᵢ` for the lower one, whose negation is the lower end. So the multipliers, from a
solver or from nowhere, only decide how tight the box is.

## Inputs
* `cZ` – float constrained zonotope
* `up` – multipliers of the upper end of each coordinate
* `lo` – multipliers of the lower end of each coordinate

## Hypotheses
* none

## Conclusion
* the set lies in the box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The direction `s · eᵢ` as a functional reads `s xᵢ`. -/
private theorem aux_axis (s : 𝕋) (i : Fin n) (x : Vec ℝ n) :
    Real.HPolytope.rowLin (toRealMat fun (_ : Fin 1) => ConZonotope.step_axis s i) 0 x
      = toReal s * x i := by
  simp [Real.HPolytope.rowLin, Matrix.mulVec, dotProduct, toRealMat, ConZonotope.step_axis,
    apply_ite toReal, toReal_zero]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The box from any multipliers holds the set. -/
theorem ConZonotope.intervalCertWith_contains (cZ : ConZonotope 𝕋 (Vec 𝕋 n))
    (up lo : Fin n → ConZonotope.CertWeights cZ) : -- --- CONCL ---
    cZ.toSet ⊆ (cZ.intervalCertWith up lo).toSet := by -- --- PROOF ---
  intro x hx
  refine Interval.mem_vec_iff.mpr fun i => ⟨?_, ?_⟩
  -- the lower end: the bound along `-eᵢ`, negated
  · have h := (ConZonotope.step_certBound cZ (ConZonotope.step_axis (neg one) i) (lo i)).le x hx
    rw [aux_axis, toReal_neg, toReal_one] at h
    show toReal (neg _) ≤ x i
    rw [toReal_neg]
    linarith
  -- the upper end: the bound along `eᵢ`
  · have h := (ConZonotope.step_certBound cZ (ConZonotope.step_axis one i) (up i)).le x hx
    rw [aux_axis, toReal_one] at h
    have h' : x i ≤ toReal
        (ConZonotope.step_certBound cZ (ConZonotope.step_axis one i) (up i)).val := by
      linarith
    exact h'

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
