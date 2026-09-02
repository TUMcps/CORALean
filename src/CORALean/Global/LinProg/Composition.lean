import CORALean.Global.LinProg.LinProg

/-!
# How a bound travels across set operations

A direction sees a Minkowski sum as a sum of extents, a union as the larger of
two, a linear image as the direction pulled back through the map, and a convex
hull as no further than the points it was taken of. So one bound per operand is
enough, and a representation that can answer `SupportBound` for itself can be
enclosed after any of these without knowing how the result is described.

This is what makes the hard polytope operations definable: the enclosure is a
list of directions, and its right-hand side is assembled here.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean

open Pointwise

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
variable {S T : Set α} {c : α →ₗ[ℝ] ℝ}

def SupportBound.add (u : SupportBound S c) (v : SupportBound T c) :
    SupportBound (S + T) c where
  val := u.val + v.val
  le := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    show c (x + y) ≤ u.val + v.val
    rw [map_add]
    exact add_le_add (u.le x hx) (v.le y hy)

/-- Directions add. This is what makes an inexact dual solution usable: `c`
splits as `d + (c - d)`, the dual bounds `d`, and whatever it missed by is
bounded separately — over an enclosure already in hand, when the miss is a
rounding error. -/
def SupportBound.addDir {d : α →ₗ[ℝ] ℝ} (u : SupportBound S c) (v : SupportBound S d) :
    SupportBound S (c + d) where
  val := u.val + v.val
  le x hx := by
    show c x + d x ≤ u.val + v.val
    exact add_le_add (u.le x hx) (v.le x hx)

def SupportBound.union (u : SupportBound S c) (v : SupportBound T c) :
    SupportBound (S ∪ T) c where
  val := max u.val v.val
  le x hx :=
    hx.elim (fun h => le_trans (u.le x h) (le_max_left _ _))
      fun h => le_trans (v.le x h) (le_max_right _ _)

/-- The image under `M` reaches as far in direction `c` as the source does in
direction `c ∘ M`, which is how a bound survives a change of space. -/
def SupportBound.image {d : β →ₗ[ℝ] ℝ} (M : α →ₗ[ℝ] β) (u : SupportBound S (d.comp M)) :
    SupportBound (M '' S) d where
  val := u.val
  le := by
    rintro _ ⟨x, hx, rfl⟩
    exact u.le x hx

def SupportBound.smul {r : ℝ} (hr : 0 ≤ r) (u : SupportBound S c) :
    SupportBound (r • S) c where
  val := r * u.val
  le := by
    rintro _ ⟨x, hx, rfl⟩
    show c (r • x) ≤ r * u.val
    rw [map_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (u.le x hx) hr

/-- The sublevel set of a linear functional, which is the halfspace a bound
names. -/
theorem convex_le (c : α →ₗ[ℝ] ℝ) (v : ℝ) : Convex ℝ {w : α | c w ≤ v} := by
  intro p hp q hq a b ha hb hab
  show c (a • p + b • q) ≤ v
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  calc a * c p + b * c q ≤ a * v + b * v :=
        add_le_add (mul_le_mul_of_nonneg_left hp ha) (mul_le_mul_of_nonneg_left hq hb)
    _ = v := by rw [← add_mul, hab, one_mul]

/-- A halfspace is convex, so it holds the hull as soon as it holds the points.
This is what lets a convex hull be enclosed without ever forming it. -/
def SupportBound.convexHull (u : SupportBound S c) : SupportBound (convexHull ℝ S) c where
  val := u.val
  le _ hx := convexHull_min (fun y hy => u.le y hy) (convex_le c u.val) hx

end CORALean
