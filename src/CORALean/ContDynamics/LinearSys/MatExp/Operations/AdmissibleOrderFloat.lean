import CORALean.Global.Float.SoundFloatArithmetic

/-!
# `MatExp.admissibleOrder`, a computed Taylor order the float remainder admits

The float remainder bounds (`expRemainderBound`, and every enclosure built on
it) are sound once `nrm / (η + 2) ≤ 1/2`, with `nrm` a float bound on the norm
of the matrix they are taken at. This finds the first such `η` from `η₀` on,
checked by the float comparison `le`, whose `true` is sound; the search is
bounded by `fuel` and says `none` rather than returning an unchecked order.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The first `η ∈ [η₀, η₀ + fuel)` with `nrm ≤ (η + 2)/2` certified by `le`,
the count `η + 2` rounded down. -/
def MatExp.admissibleOrder (nrm : 𝕋) (η₀ fuel : ℕ) : Option ℕ :=
  ((List.range fuel).map (η₀ + ·)).find? fun η => le nrm (half (nsmulDown (η + 2) one))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
