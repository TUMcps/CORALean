import CORALean.ContDynamics.LinearSys.Definitions.InputLaws

/-!
# The laws of the input solution over a time interval

`[1, Prop. 4]`: the enclosing probabilistic hull `R̄([t₁, t₂])` of the input solution over a
time interval, as the family of all its laws at the times of the interval
(`LinearSys.inputLaws`).

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar MeasureTheory

variable {n m : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The laws at the times of `[t₁, t₂]`. -/
noncomputable def LinearSys.inputLawsOver (sys : LinearSys 𝕋 n) (C : Mat ℝ n m) (U : S n)
    (t₁ t₂ : ℝ) : Set (Measure (EuclideanSpace ℝ (Fin n))) :=
  {ν | ∃ t ∈ Set.Icc t₁ t₂, ν ∈ sys.inputLaws C U t}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
