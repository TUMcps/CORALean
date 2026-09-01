import CORALean.Real.ContSet.ContSet.API

/-!
# Interval matrices: the representation

CORA's `intervalMatrix`, entrywise bounds, denoting every real matrix between
them. What a discretization needs: `e^{AΔt}` is transcendental, so a layer that
cannot hold it holds an interval around it instead.

Entrywise and not a set of matrices with structure — the enclosures that produce
one bound each entry on its own, and nothing downstream asks for more.

`center` and `radius` split it the way the multiplication proof uses it: an
`A` it denotes is `center` plus a perturbation bounded by `radius`.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {m n : ℕ}

structure IntervalMat (m n : ℕ) where
  inf : Mat ℝ m n
  sup : Mat ℝ m n

/-- `sup i j < inf i j` denotes the empty set, as for `Interval`. -/
def IntervalMat.construct (IM : IntervalMat m n) : Set (Mat ℝ m n) :=
  {A | ∀ i j, IM.inf i j ≤ A i j ∧ A i j ≤ IM.sup i j}

noncomputable def IntervalMat.center (IM : IntervalMat m n) : Mat ℝ m n :=
  fun i j => (IM.inf i j + IM.sup i j) / 2

noncomputable def IntervalMat.radius (IM : IntervalMat m n) : Mat ℝ m n :=
  fun i j => (IM.sup i j - IM.inf i j) / 2

/-- The split the multiplication proof runs on: every matrix denoted is the
centre off by at most the radius, entry by entry. -/
theorem IntervalMat.abs_sub_center_le {IM : IntervalMat m n} {A : Mat ℝ m n}
    (hA : A ∈ IM.construct) (i : Fin m) (j : Fin n) :
    |A i j - IM.center i j| ≤ IM.radius i j := by
  have h := hA i j
  rw [abs_le, IntervalMat.center, IntervalMat.radius]
  constructor <;> linarith [h.1, h.2]

end CORALean.Real
