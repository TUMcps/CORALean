module

public import CORALean.ContSet.Zonotope.Real.Theorems.BasisReach

@[expose] public section

/-!
# A checked approximate right inverse reaches a whole box of vectors

If `G H = 1 - K` for a `G : n × h` and an `H : h × n`, every row of `K` summing in absolute value to
at most `q ≤ 1/2`, then every vector `d` with `|dᵢ| ≤ B` is `G β` for a coefficient vector `β` with
`|βⱼ| ≤ δ`, whenever `2 B ∑ₖ |Hⱼₖ| ≤ δ`. Nothing says `H` is a right inverse: the certificate `K`
small is what makes it good enough, as for `Zonotope.basis_reach`, which is applied to the square
matrix `G H` with the identity as its approximate inverse; `β = H w` for the coordinates `w` of `d`
in that basis.

## Inputs
* `G` – generator matrix
* `H` – approximate right inverse
* `q` – contraction bound
* `B` – bound on the target
* `δ` – coefficient bound
* `d` – target vector

## Hypotheses
* `hq` – bound at most one half
* `hK` – row sums of `1 - G H` at most `q`
* `hδ` – row sums of `H` give the coefficient bound
* `hd` – target entries at most `B`

## Conclusion
* a preimage of `d` exists with bounded coefficients
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.rightInv_reach (G : Mat ℝ n h) (H : Mat ℝ h n) {q B δ : ℝ} (hq : q ≤ 1 / 2)
    (hK : ∀ i, ∑ j, |((1 : Mat ℝ n n) - G * H) i j| ≤ q)
    (hδ : ∀ j, 2 * B * ∑ k, |H j k| ≤ δ) (d : Vec ℝ n) (hd : ∀ i, |d i| ≤ B) :
    ∃ β : Vec ℝ h, G *ᵥ β = d ∧ ∀ j, |β j| ≤ δ := by -- --- PROOF ---
  have hK' : ∀ i, ∑ j, |((1 : Mat ℝ n n) - (1 : Mat ℝ n n) * (G * H)) i j| ≤ q := fun i => by
    simpa only [Matrix.one_mul] using hK i
  obtain ⟨w, hw, hwB⟩ := Zonotope.basis_reach (G * H) (1 : Mat ℝ n n) hq hK' d
    (fun i => by simpa only [Matrix.one_mulVec] using hd i)
  refine ⟨H *ᵥ w, ?_, fun j => ?_⟩
  · rw [Matrix.mulVec_mulVec, hw]
  · calc |(H *ᵥ w) j| = |∑ k, H j k * w k| := rfl
      _ ≤ ∑ k, |H j k * w k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, |H j k| * (2 * B) := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hwB k) (abs_nonneg _)
      _ = 2 * B * ∑ k, |H j k| := by rw [← Finset.sum_mul]; ring
      _ ≤ δ := hδ j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
