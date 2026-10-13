import CORALean.ContSet.Conversion.Float.Zonotope_to_VPolytope
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Float.Interval_to_VPolytope

/-!
# `Zonotope.polygon`, over a floating-point scalar

CORA's `@zonotope/polygon` for a planar zonotope: the `2 h` vertices from the generators sorted by
angle, `c - Σ g + 2 Σ_{j<k} g` and its mirror image through the centre, in place of the `2ʰ` corners
of `Zonotope.vPolytope`. Generators are flipped into the half-plane `y > 0 ∨ (y = 0 ∧ x ≥ 0)` (a
zonotope is symmetric), sorted by the sign of their cross product, and each walk corner is rounded
down with the gap to its rounded-up value, plus the zonotope's own box, as the error box.

The sort is `List.mergeSort` on the float comparison, which rounding can get wrong, so the result
is *checked*: the half-plane and the pairwise `cross(g_i, g_j) ≥ 0` for `i < j`, with the cross
product rounded down. If a check fails the box's four corners are returned instead, which encloses
all the same; there is nothing to tune.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The walk's `2 (h + 1)` corners of the sorted generators, or the box's four corners. -/
def Zonotope.polygon (Z : Zonotope (Vec 𝕋 2)) : VPolytope (Vec 𝕋 2) :=
  -- the stored fields, so that reading a generator costs nothing
  let Zm : Zonotope (Vec 𝕋 2) := Z.materialise
  -- the generators in the half-plane `y > 0 ∨ (y = 0 ∧ x ≥ 0)`, up to sign
  let hat : Fin Z.h → Vec 𝕋 2 := fun j i =>
    if ltStrict (Zm.G j 1) zero || (!ltStrict zero (Zm.G j 1) && ltStrict (Zm.G j 0) zero)
    then neg (Zm.G j i) else Zm.G j i
  -- `cross(a, b)` rounded down, and the generators sorted by it
  let cross : Vec 𝕋 2 → Vec 𝕋 2 → 𝕋 := fun a b => subDown (mulDown (a 0) (b 1)) (mulUp (a 1) (b 0))
  let order : List (Fin Z.h) := (List.finRange Z.h).mergeSort fun i j =>
    le zero (cross (hat i) (hat j))
  let Zs : Zonotope (Vec 𝕋 2) := Zonotope.materialise
    ⟨Z.h, Zm.c, fun i => hat (order.getD i.val i), Zm.E⟩
  -- the checks the walk needs
  let halfPlane : Bool := (List.finRange Z.h).all fun j =>
    le zero (Zs.G j 1) && (ltStrict zero (Zs.G j 1) || le zero (Zs.G j 0))
  let sorted : Bool := (List.finRange Z.h).all fun i => (List.finRange Z.h).all fun j =>
    !decide (i < j) || le zero (cross (Zs.G i) (Zs.G j))
  -- the walk's corners, rounded down and up
  let lo : Fin ((Z.h + 1) + (Z.h + 1)) → Vec 𝕋 2 := Fin.append
    (fun k => Zs.cornerLo ((signEquiv Zs.h).symm fun j => decide (j.val < k.val)))
    (fun k => Zs.cornerLo ((signEquiv Zs.h).symm fun j => !decide (j.val < k.val)))
  let hi : Fin ((Z.h + 1) + (Z.h + 1)) → Vec 𝕋 2 := Fin.append
    (fun k => Zs.cornerHi ((signEquiv Zs.h).symm fun j => decide (j.val < k.val)))
    (fun k => Zs.cornerHi ((signEquiv Zs.h).symm fun j => !decide (j.val < k.val)))
  if halfPlane && sorted then ⟨(Z.h + 1) + (Z.h + 1), lo, (VPolytope.columnGap lo hi).plus Z.E⟩
  else Z.interval.vPolytope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
