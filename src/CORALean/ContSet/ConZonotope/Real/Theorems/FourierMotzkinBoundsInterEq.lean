module

public import CORALean.ContSet.ConZonotope.Real.Theorems.FourierMotzkinBoundsOuter

@[expose] public section

/-!
# The Fourier-Motzkin bounds can be applied again

[1, App. D] after [1, Prop. 3]: for `P = ⟨C, d⟩_H ∩ [β̲₀, β̄₀]` with bounds `[β̲, β̄]`,
`P = ⟨C, d⟩_H ∩ [β̲, β̄]`, so [1, Prop. 3] applies to the new box and may tighten it further. The
new box lies in the old one (each bound is a `max` with `β̲₀(j)`, a `min` with `β̄₀(j)`) and
contains `P` (`ConZonotope.fourierMotzkinBounds_outer`).

## Inputs
* `C` – constraint matrix
* `d` – constraint offset
* `B` – initial bounds `[β̲₀, β̄₀]`

## Hypotheses
* none

## Conclusion
* the constraints cut the old and the new bounds to the same set

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {p q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, App. D]: intersecting the constraints with the new bounds gives the same set. -/
theorem ConZonotope.fourierMotzkinBounds_inter_eq (C : Mat ℝ p q) (d : Vec ℝ p)
    (B : Interval (Vec ℝ q)) : -- --- CONCL ---
    (HPolytope.ineqs C d).construct ∩ B.construct =
      (HPolytope.ineqs C d).construct ∩
        (ConZonotope.fourierMotzkinBounds C d B).construct := by -- --- PROOF ---
  refine Set.Subset.antisymm (fun β hβ => ⟨hβ.1, fourierMotzkinBounds_outer C d B hβ⟩)
    fun β ⟨hP, hβ⟩ => ⟨hP, fun j => ?_⟩
  -- `β̲₀(j) ≤ β̲(j)` and `β̄(j) ≤ β̄₀(j)`: the new box is inside the old
  obtain ⟨hlo, hhi⟩ := hβ j
  simp only [ConZonotope.fourierMotzkinBounds] at hlo hhi ⊢
  exact ⟨le_trans ((Finset.le_fold_max _).2 (Or.inl le_rfl)) hlo,
    le_trans hhi ((Finset.fold_min_le _).2 (Or.inl le_rfl))⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
