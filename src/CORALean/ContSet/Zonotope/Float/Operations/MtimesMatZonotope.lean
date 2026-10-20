module

public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Operations.OfEntryBounds
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `Zonotope.mtimesMatZonotope`, over a floating-point scalar

`Real.Zonotope.mtimesMatZonotope` rounded: `bilin` at the matrix-vector product, so the
center `C c`, then `Gᵢ c`, `C gⱼ` and every cross product `Gᵢ gⱼ`, each bracketed by
`mulVecDown`/`mulVecUp` and stored low by `ofEntryBounds`. The two error boxes are taken
as interval products: for `(a + e)(z + f) = az + af + e(z + f)`, `a` in the box around
the matrix zonotope's nominal part and `z + f` in the zonotope's `interval`.

## Inputs
* `M` – matrix zonotope
* `Z` – zonotope

## Output
* zonotope of the matrix-vector product
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `bilin`'s center and generators at the matrix-vector product, bracketed, plus the two
error terms as interval products. -/
def Zonotope.mtimesMatZonotope (M : Zonotope (Mat 𝕋 m n)) (Z : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 m) :=
  let g : Fin Z.h → Vec 𝕋 n := Z.G                                -- Z's generators
  let gens : (Mat 𝕋 m n → Vec 𝕋 n → Vec 𝕋 m) → Mat 𝕋 m (M.h + Z.h + M.h * Z.h) :=
    fun mul i k => Fin.append (Fin.append (fun l => mul (M.G l) Z.c) (fun j => mul M.c (g j)))
      (fun k => mul (M.G (finProdFinEquiv.symm k).1) (g (finProdFinEquiv.symm k).2)) k i
  let IM :=                                                         -- a
    ({ M with I_error := Interval.point fun _ _ => zero } : Zonotope (Mat 𝕋 m n)).matInterval
  let E := (Interval.mtimesIntervalMat IM Z.I_error).plus
      (Interval.mtimesIntervalMat M.I_error Z.interval)
  Zonotope.ofEntryBounds (mulVecDown M.c Z.c) (mulVecUp M.c Z.c) (gens mulVecDown)
    (gens mulVecUp) E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
