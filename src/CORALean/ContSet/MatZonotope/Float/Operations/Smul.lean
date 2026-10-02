import CORALean.ContSet.Interval.Float.Operations.MulHi
import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.ContSet.Interval.Float.Operations.Smul
import CORALean.ContSet.MatZonotope.Float.Operations.OfEntryBounds

/-!
# `MatZonotope.smul`, by a scalar known only to lie in `[cLo, cHi]`

`Real.Zonotope.map` at `c • ·`, for every `c ∈ [cLo, cHi]` at once, as `Interval.smul`
scales a box: each entry of the centre and of every generator is bracketed by the corner
hull `mulLo`/`mulHi`, and the box is scaled by `Interval.smul`. At `cLo = cHi` this is a
rounded scaling by one exact scalar, which is what `1/i!` and `Δt` need; for a wide
`[cLo, cHi]` the brackets widen with it, and the width lands in the box rather than in a
new generator.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every entry of the centre and the generators scaled by `[cLo, cHi]`, bracketed. -/
def MatZonotope.smul (cLo cHi : 𝕋) (Z : MatZonotope 𝕋 m n) : MatZonotope 𝕋 m n :=
  let lo : Mat 𝕋 m n → Mat 𝕋 m n := fun A i j => Interval.mulLo cLo cHi (A i j) (A i j)
  let hi : Mat 𝕋 m n → Mat 𝕋 m n := fun A i j => Interval.mulHi cLo cHi (A i j) (A i j)
  MatZonotope.ofEntryBounds (lo Z.c) (hi Z.c) (fun k => lo (Z.G k)) (fun k => hi (Z.G k))
    (Interval.smul cLo cHi Z.E)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
