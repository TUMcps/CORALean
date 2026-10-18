module

public import CORALean.ContSet.Capsule.Float.Capsule

@[expose] public section

/-!
# A capsule whose error box is the origin is its nominal capsule

The set is the nominal capsule plus the box, and adding `{0}` changes nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A box that is the origin adds nothing: the set is the nominal capsule's. -/
theorem Capsule.construct_eq_nominal {C : Capsule 𝕋 n} (h : C.I_error.construct = {0}) :
    C.construct = C.nominal.construct := by
  show InflatedContSet.nominalSet C + C.I_error.construct = _
  rw [h, Set.add_singleton]
  simp only [add_zero, Set.image_id']
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
