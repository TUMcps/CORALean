module

public import CORALean.ContSet.ConZonotope.Real.Operations.FourierMotzkinIter
public import CORALean.ContSet.ConZonotope.Real.Theorems.FourierMotzkinBoundsInterEq

@[expose] public section

/-!
# Repeated Fourier-Motzkin bounds still enclose the constrained hypercube

`k` passes of [1, Prop. 3] from the unit box (`ConZonotope.fourierMotzkinIter`), as [1, App. D]
allows, contain every factor `β ∈ [-1, 1]^q` with `C β ≤ d`: each pass keeps
`⟨C, d⟩_H ∩ [β̲, β̄]` the same set (`ConZonotope.fourierMotzkinBounds_inter_eq`), so by
induction it is `⟨C, d⟩_H ∩ B_q`.

## Inputs
* `C` – constraint matrix
* `d` – constraint offset
* `k` – number of passes
* `β` – factor

## Hypotheses
* `hβ` – `β` lies in the unit box
* `hP` – `β` satisfies the constraints

## Conclusion
* `β` lies in the bounds after `k` passes

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for
      Neural Network Verification". ICLR, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {p q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every factor of the constrained hypercube lies in the bounds after `k` passes. -/
theorem ConZonotope.fourierMotzkinIter_outer (C : Mat ℝ p q) (d : Vec ℝ p) (k : ℕ)
    (β : Vec ℝ q) (hβ : ∀ j, |β j| ≤ 1)
    (hP : β ∈ (HPolytope.ineqs C d).construct) : -- --- CONCL ---
    β ∈ (ConZonotope.fourierMotzkinIter C d k).construct := by -- --- PROOF ---
  -- the invariant: `β` stays in `⟨C, d⟩_H ∩ [β̲, β̄]` after every pass
  suffices h : ∀ k, β ∈ (HPolytope.ineqs C d).construct ∩
      ((ConZonotope.fourierMotzkinBounds C d)^[k] ⟨fun _ => -1, fun _ => 1⟩).construct from
    (h k).2
  intro k
  induction k with
  | zero => exact ⟨hP, fun j => abs_le.1 (hβ j)⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← fourierMotzkinBounds_inter_eq]
    exact ih

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
