module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.HPolytope.Float.Operations.Eqs
public import CORALean.ContSet.HPolytope.Float.Operations.Intersection
public import CORALean.ContSet.HPolytope.Float.Operations.PadLeft
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes

@[expose] public section

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

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n s : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.intersectStrip (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (C : Mat 𝕋 s n) (φ y : Vec 𝕋 s)
    (Λ : Mat 𝕋 n s) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  -- C (c + G ξ + e): centre and generators rounded down, the rest in a box
  let W := Zonotope.mtimes C ⟨cZ.h, cZ.c, cZ.G, cZ.I_error⟩
  -- c + Λ (y - C c), as bounds around the stored centre
  let w : Interval (Vec 𝕋 s) :=
    ⟨fun k => subDown (y k) (dotUp (C k) cZ.c), fun k => subUp (y k) (dotDown (C k) cZ.c)⟩
  let shift := Interval.mtimes Λ w
  let cLo : Vec 𝕋 n := fun i => addDown (cZ.c i) (shift.inf i)
  let cHi : Vec 𝕋 n := fun i => addUp (cZ.c i) (shift.sup i)
  -- (I - Λ C) G, column by column from the box of Λ C G, rounded down, and its gap
  let LCG : Fin cZ.h → Interval (Vec 𝕋 n) := fun j =>
    Interval.mtimes Λ ⟨mulVecDown C (cZ.G j), mulVecUp C (cZ.G j)⟩
  let G₁ : Fin cZ.h → Vec 𝕋 n := fun j i => subDown (cZ.G j i) ((LCG j).sup i)
  let gap₁ : Mat 𝕋 n cZ.h := fun i j => subUp (subUp (cZ.G j i) ((LCG j).inf i)) (G₁ j i)
  -- φₖ Λₖ, rounded down, and its gap
  let G₂ : Fin s → Vec 𝕋 n := fun k i => mulDown (Λ i k) (φ k)
  let gap₂ : Mat 𝕋 n s := fun i k => subUp (mulUp (Λ i k) (φ k)) (G₂ k i)
  -- the strip rows `C G ξ - φ ν = y - C c`, widened by what the image's box lets them be off
  let Astrip : Mat 𝕋 s (cZ.h + s) := fun k =>
    Fin.append (fun j => W.G j k) fun l => if l = k then neg (φ k) else zero
  let bstrip : Interval (Vec 𝕋 s) :=
    ⟨fun k => subDown (subDown (y k) (W.c k)) (W.I_error.sup k),
     fun k => subUp (subUp (y k) (W.c k)) (W.I_error.inf k)⟩
  { h := cZ.h + s
    c := cLo
    G := Fin.append G₁ G₂
    P := (cZ.P.padLeft s).intersection (HPolytope.eqs Astrip bstrip)
    I_error := (((cZ.I_error.minus (Interval.mtimes Λ (Interval.mtimes C cZ.I_error))).plus
        (Interval.residual cLo cHi cLo)).plus (Zonotope.generatorError gap₁)).plus
      (Zonotope.generatorError gap₂) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
