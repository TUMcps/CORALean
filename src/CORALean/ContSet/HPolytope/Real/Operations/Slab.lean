import CORALean.ContSet.HPolytope.Real.Theorems.AndExact
import CORALean.ContSet.HPolytope.Real.Operations.OfMat

/-!
# `HPolytope.slab`

`Ae x ∈ [lo, hi]`: an equality row with room in it. One row per constraint, as an
equality has, but with a right-hand side that can be widened.

This is what a float layer needs. An inequality absorbs its rounding by raising
`b`; an equality has no slack of its own, since any rounding of `Ae` or `be`
names a different hyperplane and a hyperplane has empty interior. Widening the
right-hand side into an interval is where that rounding can go.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {q n : ℕ}

def HPolytope.slab (Ae : Mat ℝ q n) (lo hi : Vec ℝ q) : HPolytope (Vec ℝ n) :=
  (HPolytope.ineqs Ae hi).and (HPolytope.ineqs (-Ae) (-lo))

theorem HPolytope.mem_slab_iff {Ae : Mat ℝ q n} {lo hi : Vec ℝ q} {x : Vec ℝ n} :
    x ∈ (HPolytope.slab Ae lo hi).construct ↔
      ∀ i, lo i ≤ (Ae *ᵥ x) i ∧ (Ae *ᵥ x) i ≤ hi i := by
  have hand : x ∈ (HPolytope.slab Ae lo hi).construct ↔
      x ∈ (HPolytope.ineqs Ae hi).construct
        ∧ x ∈ (HPolytope.ineqs (-Ae) (-lo)).construct := HPolytope.mem_and_iff
  rw [hand, HPolytope.mem_ineqs_iff, HPolytope.mem_ineqs_iff]
  -- both directions, the lower bound being the negated row read back
  constructor
  · rintro ⟨hhi, hlo⟩ i
    have h := hlo i
    rw [Matrix.neg_mulVec, Pi.neg_apply, Pi.neg_apply, neg_le_neg_iff] at h
    exact ⟨h, hhi i⟩
  · intro h
    refine ⟨fun i => (h i).2, fun i => ?_⟩
    rw [Matrix.neg_mulVec, Pi.neg_apply, Pi.neg_apply, neg_le_neg_iff]
    exact (h i).1

/-- An equality is the degenerate slab, which is how CORA's `Ae x = be` reads in
this form. -/
theorem HPolytope.mem_slab_self_iff {Ae : Mat ℝ q n} {be : Vec ℝ q} {x : Vec ℝ n} :
    x ∈ (HPolytope.slab Ae be be).construct ↔ ∀ i, (Ae *ᵥ x) i = be i := by
  rw [HPolytope.mem_slab_iff]
  exact forall_congr' fun i => ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

end CORALean.Real
