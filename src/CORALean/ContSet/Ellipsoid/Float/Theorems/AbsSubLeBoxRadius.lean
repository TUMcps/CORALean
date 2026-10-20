module

public import CORALean.ContSet.Ellipsoid.Float.Theorems.AbsSubLeOfMemNominalSet
public import CORALean.ContSet.Ellipsoid.Float.Operations.BoxRadius

@[expose] public section

/-!
# The nominal part lies in the box `q ± boxRadius`

CORA's `interval(E)`, `q ± √diag(Q)`, read at the stored floats and rounded up:
`abs_sub_le_of_mem_nominalSet` and `le_sqrtUp`.

## Inputs
* `E` – ellipsoid
* `x` – point
* `p` – Newton steps per root
* `i` – coordinate

## Hypotheses
* `hx` – `x` in the nominal part

## Conclusion
* `x` is within `boxRadius` of the center in coordinate `i`
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic InflatedContSet Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the nominal part is within `boxRadius` of the center in coordinate `i`. -/
theorem Ellipsoid.abs_sub_le_boxRadius {E : Ellipsoid 𝕋 n} {x : Vec ℝ n}
    (hx : x ∈ nominalSet E) (p : ℕ) (i : Fin n) : -- --- CONCL ---
    |x i - toReal (E.q i)| ≤ toReal (Ellipsoid.boxRadius p E i) := by -- --- PROOF ---
  -- the rounded-up root of the floored diagonal entry
  have hroot : Real.sqrt (max 0 (toReal (E.Q i i))) ≤ toReal (Ellipsoid.boxRadius p E i) := by
    have h := le_sqrtUp p (FloatOps.maximum FloatOps.zero (E.Q i i))
    rwa [toReal_maximum, toReal_zero] at h
  exact le_trans (Ellipsoid.abs_sub_le_of_mem_nominalSet hx i) hroot

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
