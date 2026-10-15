module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Float.Operations.PsdCheck

@[expose] public section

/-!
# A certificate that a factor covers a shape matrix

`G Gᵀ - Q` bracketed entry by entry in outward rounding and checked diagonally dominant by
`psdCheck` against the zero factor, with `Q` checked symmetric: `true` makes `G Gᵀ - Q`, read as
reals, positive semi-definite (`posSemidef_of_isOuterFactor`), so that the ellipsoid of the factor
`G` contains the one of `Q`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `G Gᵀ - Q` is certified positive semi-definite. -/
def Ellipsoid.isOuterFactor (Q G : Mat 𝕋 n n) : Bool :=
  -- `G Gᵀ - Q`, entrywise between two roundings
  let X : Interval (Mat 𝕋 n n) := ⟨fun i j => subDown (dotDown (G i) (G j)) (Q i j),
    fun i j => subUp (dotUp (G i) (G j)) (Q i j)⟩
  Ellipsoid.isSymm Q && Ellipsoid.psdCheck X fun _ _ => zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
