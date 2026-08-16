import CORALean.ContSet.Interval.API

/-!
# `Interval.mtimes` over-approximates the image under a linear map

Each summand `M i k * x k` lies between the two endpoint products; `min`/`max`
absorb the sign of `M i k`, leaving one case split inside `key`. Summing over
`k` finishes it.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Interval.Proofs

open Matrix

variable {n m : ℕ}

theorem mtimes_sound (M : Mat m n) (I : Interval n) :
    (M *ᵥ ·) '' I.construct ⊆ (Interval.mtimes M I).construct := by
  rintro _ ⟨x, hx, rfl⟩ i
  have key : ∀ k, min (M i k * I.inf k) (M i k * I.sup k) ≤ M i k * x k ∧
      M i k * x k ≤ max (M i k * I.inf k) (M i k * I.sup k) := by
    intro k
    rcases le_total 0 (M i k) with hM | hM
    · exact ⟨(min_le_left _ _).trans (by nlinarith [(hx k).1]),
             le_trans (by nlinarith [(hx k).2]) (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (by nlinarith [(hx k).2]),
             le_trans (by nlinarith [(hx k).1]) (le_max_left _ _)⟩
  simp only [Interval.mtimes, Matrix.mulVec, dotProduct]
  exact ⟨Finset.sum_le_sum fun k _ => (key k).1, Finset.sum_le_sum fun k _ => (key k).2⟩

end CORALean.Interval.Proofs
