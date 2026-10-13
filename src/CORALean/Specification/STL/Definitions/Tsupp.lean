import CORALean.Specification.STL.STL

/-!
# The time support of a formula

[1, Eq. 12]: `tsupp(ϕ) = {t | ∃ ξ ξ', ξ ⊨ₜ ϕ ∧ ξ' ⊭ₜ ϕ ∧ ∀ t' ≠ t, ξ(t') = ξ'(t')}`, the points in
time where a change in the trace can affect whether `ϕ` is true. `DecidedOn ϕ T` says the
truth of `ϕ` is settled by a trace's values on `T`: two traces that agree there agree on `ϕ`.
`tsupp` is the smallest set that can decide (`tsupp_subset_of_decided`); that it does decide is
what [1, Eq. 12]'s proof uses and does not show.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 12]: the times at which changing one point of a trace can change `ϕ`. -/
def STL.Formula.tsupp (φ : STL.Formula X) : Set ℝ≥0 :=
  {t | ∃ ξ ξ' : ℝ≥0 → X, φ.Sat ξ ∧ ¬ φ.Sat ξ' ∧ ∀ t', t' ≠ t → ξ t' = ξ' t'}

/-- Traces agreeing on `T` agree on `ϕ`. -/
def STL.Formula.DecidedOn (φ : STL.Formula X) (T : Set ℝ≥0) : Prop :=
  ∀ ξ ξ' : ℝ≥0 → X, (∀ t ∈ T, ξ t = ξ' t) → (φ.Sat ξ ↔ φ.Sat ξ')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
