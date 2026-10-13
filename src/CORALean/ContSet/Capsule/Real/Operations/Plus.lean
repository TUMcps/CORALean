import CORALean.ContSet.Capsule.Real.Capsule

/-!
# `Capsule.plus`

CORA's `@capsule/plus.m` for two capsules. The sum is not a capsule, and CORA encloses it: the
centres add, the longer of the two generators is kept, and the shorter one is absorbed into the
radius, `r = r₁ + r₂ + ‖shorter g‖₂`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Capsule plus capsule: the longer generator is kept, the shorter one is added to the radius.
The comparison is on the squared lengths, which orders the same way. -/
noncomputable def Capsule.plus (C₁ C₂ : Capsule n) : Capsule n :=
  let c := C₁.c + C₂.c
  if ∑ i, C₂.g i ^ 2 ≤ ∑ i, C₁.g i ^ 2 then
    ⟨c, C₁.g, C₁.r + C₂.r + Real.sqrt (∑ i, C₂.g i ^ 2)⟩
  else
    ⟨c, C₂.g, C₁.r + C₂.r + Real.sqrt (∑ i, C₁.g i ^ 2)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
