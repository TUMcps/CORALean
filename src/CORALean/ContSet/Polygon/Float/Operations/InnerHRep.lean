import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
import CORALean.ContSet.Polygon.Float.Operations.OrientBounds
import CORALean.ContSet.Polygon.Float.Polygon

/-!
# `Polygon.innerHRep`

A halfspace description of a float piece that lies inside it: one inequality per edge, so the
vertices are taken in the stored order, each edge `vᵢ → vᵢ₊₁` (the last closing to `v₀`) giving
the halfspace on its left, `aᵀx ≤ aᵀvᵢ` with `a = (dᵢ₁, -dᵢ₀)` and `dᵢ = vᵢ₊₁ - vᵢ`.

Two roundings could make it larger than the piece, so neither is allowed to. The edge
direction is a difference of stored coordinates; a rounded normal turns its line about some
point, which no shift of the bound can repair, so the difference must be exact: it is
computed rounded down and certified equal to its upward rounding by `le` (Sterbenz's lemma
makes this common for nearby vertices, and small integers or dyadic coordinates always pass).
The bound `aᵀvᵢ` is a dot product and is rounded down, which only shrinks the halfspace.

What makes the edge halfspaces inner without assuming the vertices are in convex position is
the fan from `v₀`: every triangle `v₀ vᵢ vᵢ₊₁` is certified counterclockwise by `ltStrict`.
A point left of every edge then lies in one of these triangles (`innerHRep_inner`). The
piece's error box must hold `0`, certified by `le`, so the hull of the stored vertices lies in
the piece. Anything uncertified, or fewer than three vertices, gives `none`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The edge halfspaces of a piece, when they are certified to lie inside it. -/
def Polygon.innerHRep (p : VPolytope 𝕋 2) : Option (HPolytope 𝕋 2) :=
  -- the edge `vᵢ₊₁ - vᵢ`, the last edge closing the loop to `v₀`
  let d : Fin p.k → Vec 𝕋 2 := fun i j => subDown (p.V (finRotate p.k i) j) (p.V i j)
  -- every difference is exact: its upward rounding is no larger than its downward one
  let exact : Bool := (List.finRange p.k).all fun i => (List.finRange 2).all fun j =>
    le (subUp (p.V (finRotate p.k i) j) (p.V i j)) (d i j)
  -- the fan from `v₀`: every triangle `v₀ vᵢ vᵢ₊₁` for `0 < i < k - 1` turns left
  let fan : Bool := (List.finRange p.k).all fun i =>
    i.val == 0 || i.val + 1 == p.k ||
      ltStrict zero (Polygon.orientBounds (p.V ⟨0, i.pos⟩) (p.V i) (p.V (finRotate p.k i))).1
  -- the error box holds the origin
  let origin : Bool := (List.finRange 2).all fun j => le (p.E.inf j) zero && le zero (p.E.sup j)
  -- the outward normal `(dᵢ₁, -dᵢ₀)` and its bound at `vᵢ`, rounded down
  let A : Mat 𝕋 p.k 2 := fun i => ![d i 1, neg (d i 0)]
  let b : Vec 𝕋 p.k := fun i => dotDown (A i) (p.V i)
  if 3 ≤ p.k ∧ exact = true ∧ fan = true ∧ origin = true then some (HPolytope.ineqs A b)
  else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
