module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Capsule.Real.Instances
public import CORALean.ContSet.Capsule.Real.Theorems.CenterMemConstructIff
public import CORALean.ContSet.InflatedContSet.Theorems.Basic

@[expose] public section

/-!
# `Capsule.center_mem_construct_iff`, over a floating-point scalar

The stored center is in the capsule exactly when the stored radius is non-negative, given an
error box that holds the origin. A point of the set has a point of the nominal capsule in it, so a
negative radius, which empties the nominal capsule, excludes the center whatever the box; with the
origin in the box, the nominal capsule is in the set, and the exact layer's
`center_mem_construct_iff` gives the rest.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- It is in the capsule exactly when the stored radius is non-negative, given a box that holds
the origin: a negative radius empties the nominal part, whatever the box. -/
theorem Capsule.center_mem_construct_iff (C : Capsule 𝕋 n)
    (h0 : (0 : Vec ℝ n) ∈ C.I_error.construct) : toRealVec C.c ∈ C.construct ↔ 0 ≤ toReal C.r :=
  ⟨fun ⟨_, ⟨_, _, hle⟩, _, _, _⟩ => le_trans (Real.sqrt_nonneg _) hle,
    fun hr => InflatedContSet.nominalSet_subset_construct h0
      ((CORALean.Real.Capsule.center_mem_construct_iff C.nominal).mpr hr)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
