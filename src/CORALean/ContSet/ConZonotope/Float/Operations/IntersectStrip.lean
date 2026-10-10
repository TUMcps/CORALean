import CORALean.ContSet.ConZonotope.Float.ConZonotope
import CORALean.ContSet.HPolytope.Float.Operations.Eqs
import CORALean.ContSet.HPolytope.Float.Operations.Intersection
import CORALean.ContSet.HPolytope.Float.Operations.PadLeft
import CORALean.ContSet.Interval.Float.Operations.Minus
import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Residual
import CORALean.ContSet.Zonotope.Float.Operations.GeneratorError
import CORALean.ContSet.Zonotope.Float.Operations.Mtimes

/-!
# `ConZonotope.intersectStrip` over a floating-point scalar

CORA's `@conZonotope/intersectStrip` with a numeric gain (`aux_conZonotopeFromLambda`) on the
stored floats: the strip `{x | |C x - y| ≤ φ}` enters as `s` new factors `ν` and `s` equality
rows `C G ξ - φ ν = y - C c`, the centre moves to `c + Λ (y - C c)` and the generators become
`[(I - Λ C) G, φ₁ Λ₁, …, φₛ Λₛ]`, the old constraints acting on the old factors, as over ℝ.

At float the stored point carries an error `e`, which the exact construction would have to
carry as `(I - Λ C) e`; it goes into the error box as `e - Λ (C e)`, each product an interval
image. The strip rows are built from the float image `Zonotope.mtimes C` of the set (as the float
`conIntersect` does), their right-hand side widened by that image's error box. The new centre and
the first generator block are rounded down from interval bounds (`Λ (y - C c)` and `Λ C G` as
interval images), the second block entry by entry, and what each rounding costs goes into the
error box. The gain is an argument, as over ℝ; the result is outer, never exact.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n s : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.intersectStrip (cZ : ConZonotope 𝕋 n) (C : Mat 𝕋 s n) (φ y : Vec 𝕋 s)
    (Λ : Mat 𝕋 n s) : ConZonotope 𝕋 n :=
  -- C (c + G ξ + e): centre and generators rounded down, the rest in a box
  let W := Zonotope.mtimes C ⟨cZ.h, cZ.c, fun j i => cZ.G i j, cZ.E⟩
  -- c + Λ (y - C c), as bounds around the stored centre
  let w : Interval (Vec 𝕋 s) :=
    ⟨fun k => subDown (y k) (dotUp (C k) cZ.c), fun k => subUp (y k) (dotDown (C k) cZ.c)⟩
  let shift := Interval.mtimes Λ w
  let cLo : Vec 𝕋 n := fun i => addDown (cZ.c i) (shift.inf i)
  let cHi : Vec 𝕋 n := fun i => addUp (cZ.c i) (shift.sup i)
  -- (I - Λ C) G, column by column from the box of Λ C G, rounded down, and its gap
  let LCG : Fin cZ.h → Interval (Vec 𝕋 n) := fun j =>
    Interval.mtimes Λ ⟨fun k => matMulDown C cZ.G k j, fun k => matMulUp C cZ.G k j⟩
  let G₁ : Mat 𝕋 n cZ.h := fun i j => subDown (cZ.G i j) ((LCG j).sup i)
  let gap₁ : Mat 𝕋 n cZ.h := fun i j => subUp (subUp (cZ.G i j) ((LCG j).inf i)) (G₁ i j)
  -- φₖ Λₖ, rounded down, and its gap
  let G₂ : Mat 𝕋 n s := fun i k => mulDown (Λ i k) (φ k)
  let gap₂ : Mat 𝕋 n s := fun i k => subUp (mulUp (Λ i k) (φ k)) (G₂ i k)
  -- the strip rows `C G ξ - φ ν = y - C c`, widened by what the image's box lets them be off
  let Astrip : Mat 𝕋 s (cZ.h + s) := fun k =>
    Fin.append (fun j => W.G j k) fun l => if l = k then neg (φ k) else zero
  let bstrip : Interval (Vec 𝕋 s) :=
    ⟨fun k => subDown (subDown (y k) (W.c k)) (W.E.sup k),
     fun k => subUp (subUp (y k) (W.c k)) (W.E.inf k)⟩
  { h := cZ.h + s
    c := cLo
    G := fun i => Fin.append (G₁ i) (G₂ i)
    P := (cZ.P.padLeft s).intersection (HPolytope.eqs Astrip bstrip)
    E := (((cZ.E.minus (Interval.mtimes Λ (Interval.mtimes C cZ.E))).plus
        (Interval.residual cLo cHi cLo)).plus (Zonotope.generatorError gap₁)).plus
      (Zonotope.generatorError gap₂) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
