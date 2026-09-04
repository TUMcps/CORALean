import CORALean.Global.EuclideanNorm

/-!
# Ellipsoids: the representation

CORA's `ellipsoid` stores a positive semi-definite shape matrix `Q` and a centre
`q`. CORALean stores the *generator* matrix `G` instead and denotes the same
family as the affine image of a Euclidean unit ball,

  `E = {q + G u | ‖u‖₂ ≤ 1}`,   `Q = G Gᵀ`.

The generator form needs no matrix inverse, no positive-semi-definiteness side
condition to carry through every operation, and no matrix square root to get
back out of one. A degenerate ellipsoid is a singular `G` and costs nothing.

`G` is `n × k` with `k` a field, as the zonotope's generator count is. That is
what makes a linear image exact without a square root: `M G` is `m × k`, where a
square `G` would have forced one back in.

`‖·‖₂` is `CORALean.norm₂`, deliberately not `‖·‖`: `Vec ℝ n` is `Fin n → ℝ` and
carries the supremum norm.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

structure Ellipsoid (n : ℕ) where
  k : ℕ
  q : Vec ℝ n
  G : Mat ℝ n k

def Ellipsoid.construct (E : Ellipsoid n) : Set (Vec ℝ n) :=
  {x | ∃ u : Vec ℝ E.k, ‖u‖₂ ≤ 1 ∧ x = E.q + E.G *ᵥ u}

/-- CORA's shape matrix, so the correspondence can be checked rather than taken
on trust. Nothing below uses it: every operation and every guarantee is stated
against `G`. -/
def Ellipsoid.shape (E : Ellipsoid n) : Mat ℝ n n := E.G * E.Gᵀ

theorem Ellipsoid.mem_construct {E : Ellipsoid n} {u : Vec ℝ E.k} (hu : ‖u‖₂ ≤ 1) :
    E.q + E.G *ᵥ u ∈ E.construct := ⟨u, hu, rfl⟩

/-- Never empty, which is what the support function's maximum is attained at
when the direction is one `G` collapses. -/
theorem Ellipsoid.q_mem_construct (E : Ellipsoid n) : E.q ∈ E.construct :=
  ⟨0, by rw [norm₂_zero]; exact zero_le_one, by rw [Matrix.mulVec_zero, add_zero]⟩

/-- The affine image the definition already is, spelt as an image so that
convexity and compactness transfer from the ball in one step. -/
theorem Ellipsoid.construct_eq_image (E : Ellipsoid n) :
    E.construct = (fun u : Vec ℝ E.k => E.q + E.G *ᵥ u) '' unitBall₂ E.k := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

end CORALean.Real
