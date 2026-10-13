module

public import CORALean.ContSet.Conversion.Float.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Float.Interval_to_Ellipsoid

@[expose] public section

/-!
# A capsule as an ellipsoid, over a floating-point scalar

Via the bounding box: `Capsule.interval`, then the box's own conversion. An outer enclosure,
coarser than CORA's conversion, as over ℝ: the capsule is first replaced by its axis-aligned box,
which loses the rounded ends and the slant of the segment.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- The scaling `σ` is the one `Interval.ellipsoid` asks for: a float at least `√n`. -/
def Capsule.ellipsoid (C : Capsule 𝕋 n) (σ : 𝕋) : Ellipsoid 𝕋 n :=
  C.interval.ellipsoid σ


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.ellipsoid_contains (C : Capsule 𝕋 n) (σ : 𝕋) (hσ : 0 < toReal σ)
    (hn : (n : ℝ) ≤ toReal (mulDown σ σ)) :
    C.construct ⊆ (C.ellipsoid σ).construct :=
  subset_trans C.interval_contains (Interval.ellipsoid_contains _ σ hσ hn)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
