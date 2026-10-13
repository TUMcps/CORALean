import CORALean.ContSet.Polygon.Real.Theorems.SubtractOuter

/-!
# `Polygon.mldivide` encloses the difference with any set

CORA's `polygon/mldivide(pgon, S)` is `subtract(pgon, polygon(S))`: the second operand goes
through the conversion `polygon(S)`, which is the set itself for a polygon and an inner
polygon (`Ellipsoid.polygon_inner`) for the others. So the result is
`Polygon.subtract` at the converted operand, and when that polygon lies inside `S` it encloses
the difference with `S`: outer, and larger than `P \ S` by the part of `S` the polygon misses.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.mldivide_outer (P Sp : Polygon) {S : Set (Vec ℝ 2)}
    (hSp : ContSet.construct Sp ⊆ S)
    (hreg : ContSet.construct P = closure (interior (ContSet.construct P))) :
    ContSet.construct P \ S ⊆ Polygon.subtract P Sp :=
  fun _ hx => (Polygon.subtract_outer P Sp hreg).1 ⟨hx.1, fun h => hx.2 (hSp h)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
