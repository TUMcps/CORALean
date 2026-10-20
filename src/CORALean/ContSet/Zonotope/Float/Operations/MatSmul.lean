module

public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.ContSet.Zonotope.Float.Operations.OfEntryBoundsMat

@[expose] public section

/-!
# `Zonotope.matSmul`, by a scalar known only to lie in `[cLo, cHi]`

`Real.Zonotope.map` at `c • ·`, for every `c ∈ [cLo, cHi]` at once, as `Interval.smul`
scales a box: each entry of the center and of every generator is bracketed by the corner
hull `mulLo`/`mulHi`, and the box is scaled by `Interval.smul`. At `cLo = cHi` this is a
rounded scaling by one exact scalar, which is what `1/i!` and `Δt` need; for a wide
`[cLo, cHi]` the brackets widen with it, and the width lands in the box rather than in a
new generator.

## Inputs
* `cLo` – lower end of the scalar
* `cHi` – upper end of the scalar
* `Z` – matrix zonotope

## Output
* matrix zonotope scaled by the bracketed scalar
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every entry of the center and the generators scaled by `[cLo, cHi]`, bracketed. -/
def Zonotope.matSmul (cLo cHi : 𝕋) (Z : Zonotope (Mat 𝕋 m n)) : Zonotope (Mat 𝕋 m n) :=
  let lo : Mat 𝕋 m n → Mat 𝕋 m n := fun A i j => Interval.mulLo cLo cHi (A i j) (A i j)
  let hi : Mat 𝕋 m n → Mat 𝕋 m n := fun A i j => Interval.mulHi cLo cHi (A i j) (A i j)
  Zonotope.ofEntryBoundsMat (lo Z.c) (hi Z.c) (fun k => lo (Z.G k)) (fun k => hi (Z.G k))
    (Interval.smul cLo cHi Z.I_error)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
