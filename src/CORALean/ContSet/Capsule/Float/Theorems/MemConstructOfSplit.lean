module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Capsule.Real.Theorems.MemConstructIffNorm

@[expose] public section

/-!
# A point of a float capsule, split into the stored capsule and the error box

The shape every enclosure proof of a float capsule takes (#185): a point `x` is in the capsule
when, for some segment parameter `t ∈ [-1, 1]` and some `w` no longer than the stored radius, what
`x` misses of `c + t g + w` (`c`, `g` the stored center and generator read as reals) is in the
error box. `Capsule.exists_split_of_mem` gives the pieces of a point of an exact capsule, and
`Capsule.smul_mem_symmetric` the box of a generator's rounding.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open CORALean Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x` is in the capsule when what it misses of `c + t g + w`, for some `t ∈ [-1, 1]` and some `w`
no longer than the stored radius, is in the error box. -/
theorem Capsule.mem_construct_of_split (C : Capsule 𝕋 n) {x w : Vec ℝ n} {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hw : ‖w‖₂ ≤ toReal C.r)
    (he : x - (toRealVec C.c + t • toRealVec C.g + w) ∈ C.I_error.construct) :
    x ∈ C.construct := by -- --- PROOF ---
  refine ⟨toRealVec C.c + t • toRealVec C.g + w, ?_, _, he, add_sub_cancel _ _⟩
  refine (Real.Capsule.mem_construct_iff_norm₂ C.nominal _).mpr ⟨t, ht, ?_⟩
  have h : toRealVec C.c + t • toRealVec C.g + w - C.nominal.c - t • C.nominal.g = w := by
    show toRealVec C.c + t • toRealVec C.g + w - toRealVec C.c - t • toRealVec C.g = w
    abel
  rw [h]
  exact hw

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
