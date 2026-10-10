import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Zonotope.Float.Operations.OfEntryBounds

/-!
# `Zonotope.mtimesMatZonotope`, over a floating-point scalar

`Real.Zonotope.mtimesMatZonotope` rounded: `bilin` at the matrix-vector product, so the
centre `C c`, then `Gᵢ c`, `C gⱼ` and every cross product `Gᵢ gⱼ`, each bracketed by
`mulVecDown`/`mulVecUp` and stored low by `ofEntryBounds`. The two error boxes are taken
as interval products: for `(a + e)(z + f) = az + af + e(z + f)`, `a` in the box around
the matrix zonotope's nominal part and `z + f` in the zonotope's `interval`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `bilin`'s centre and generators at the matrix-vector product, bracketed, plus the two
error terms as interval products. -/
def Zonotope.mtimesMatZonotope (M : GZonotope (Mat 𝕋 m n)) (Z : Zonotope 𝕋 n) : Zonotope 𝕋 m :=
  let g : Fin Z.h → Vec 𝕋 n := Z.G                                -- Z's generators
  let gens : (Mat 𝕋 m n → Vec 𝕋 n → Vec 𝕋 m) → Mat 𝕋 m (M.h + Z.h + M.h * Z.h) :=
    fun mul i k => Fin.append (Fin.append (fun l => mul (M.G l) Z.c) (fun j => mul M.c (g j)))
      (fun k => mul (M.G (finProdFinEquiv.symm k).1) (g (finProdFinEquiv.symm k).2)) k i
  let IM :=                                                         -- a
    ({ M with E := Interval.point fun _ _ => zero } : GZonotope (Mat 𝕋 m n)).interval
  let E := (Interval.mtimesIntervalMat IM Z.E).plus (Interval.mtimesIntervalMat M.E Z.interval)
  Zonotope.ofEntryBounds (mulVecDown M.c Z.c) (mulVecUp M.c Z.c) (gens mulVecDown)
    (gens mulVecUp) E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
