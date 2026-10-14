module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Capsule.Real.Instances
public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Conversion.Real.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Capsule_to_Interval

@[expose] public section

/-!
# A capsule as a box, over a floating-point scalar

CORA's `interval(capsule)`: the centre give or take the generator's reach and the radius in each
coordinate, `|gᵢ| + r`. The reach is rounded up, so each end is rounded away from the capsule:
the lower bound down, the upper bound up. An empty capsule (`r < 0`) is boxed all the same, by
whatever the bounds say, as over ℝ.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.interval_contains (C : Capsule 𝕋 n) :
    C.construct ⊆ C.interval.construct := by -- --- PROOF ---
  intro x hx i
  have h := CORALean.Real.Capsule.interval_contains C.nominal hx i
  have hreach : |toReal (C.g i)| + toReal C.r ≤ toReal (addUp (absolute (C.g i)) C.r) := by
    have := add_le_addUp (absolute (C.g i)) C.r
    rwa [toReal_absolute] at this
  have hlo := subDown_le_sub (C.c i) (addUp (absolute (C.g i)) C.r)
  have hhi := add_le_addUp (C.c i) (addUp (absolute (C.g i)) C.r)
  have h1 : toReal (C.c i) - (|toReal (C.g i)| + toReal C.r) ≤ x i := h.1
  have h2 : x i ≤ toReal (C.c i) + (|toReal (C.g i)| + toReal C.r) := h.2
  constructor
  · show toReal (subDown (C.c i) (addUp (absolute (C.g i)) C.r)) ≤ x i
    linarith
  · show x i ≤ toReal (addUp (C.c i) (addUp (absolute (C.g i)) C.r))
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
