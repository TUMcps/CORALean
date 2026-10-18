module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Capsule.Real.Instances
public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Conversion.Real.Theorems.CapsuleIntervalContains
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# A capsule as a box, over a floating-point scalar

CORA's `interval(capsule)`: the center give or take the generator's reach and the radius in each
coordinate, `|gᵢ| + r`. The reach is rounded up, so each end is rounded away from the capsule:
the lower bound down, the upper bound up, and the error box's ends are added to them, rounded the
same way. An empty capsule (`r < 0`) is boxed all the same, by whatever the bounds say, as over ℝ.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.interval_contains (C : Capsule 𝕋 n) :
    C.construct ⊆ C.interval.construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, e, he, rfl⟩ i
  have h := CORALean.Real.Capsule.interval_contains C.nominal hx i
  have he' := (he i)
  have hreach : |toReal (C.g i)| + toReal C.r ≤ toReal (addUp (absolute (C.g i)) C.r) := by
    have := add_le_addUp (absolute (C.g i)) C.r
    rwa [toReal_absolute] at this
  have hlo := subDown_le_sub (C.c i) (addUp (absolute (C.g i)) C.r)
  have hhi := add_le_addUp (C.c i) (addUp (absolute (C.g i)) C.r)
  have hlo' := addDown_le_add (subDown (C.c i) (addUp (absolute (C.g i)) C.r)) (C.I_error.inf i)
  have hhi' := add_le_addUp (addUp (C.c i) (addUp (absolute (C.g i)) C.r)) (C.I_error.sup i)
  have h1 : toReal (C.c i) - (|toReal (C.g i)| + toReal C.r) ≤ x i := h.1
  have h2 : x i ≤ toReal (C.c i) + (|toReal (C.g i)| + toReal C.r) := h.2
  have e1 : toReal (C.I_error.inf i) ≤ e i := he'.1
  have e2 : e i ≤ toReal (C.I_error.sup i) := he'.2
  -- each end: the nominal bound and the box's, rounded outward
  constructor
  · show toReal (addDown (subDown (C.c i) (addUp (absolute (C.g i)) C.r)) (C.I_error.inf i))
      ≤ x i + e i
    linarith
  · show x i + e i ≤ toReal (addUp (addUp (C.c i) (addUp (absolute (C.g i)) C.r)) (C.I_error.sup i))
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
