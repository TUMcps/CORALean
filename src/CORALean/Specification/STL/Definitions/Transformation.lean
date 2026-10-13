module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Definitions.ReachSequence
public import CORALean.Specification.STL.Definitions.RTL

@[expose] public section

/-!
# Sound and complete transformations

[1, Sec. 4]: `Υ` from STL to RTL is sound when `R ⊨ᵣ Υ(φ) ⇒ C(R) ⊨ₜ φ` and complete when
`C(R) ⊨ₜ φ ⇒ R ⊨ᵣ Υ(φ)`, for the reach sequences the paper has in view, which `𝓡` names:
[1, Eq. 10] takes any, [1, Lemma 2] the c-divisible finitely represented ones.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `R ⊨ᵣ Υ(φ) ⇒ C(R) ⊨ₜ φ` for every `R ∈ 𝓡`. -/
def STL.IsSound (𝓡 : Set (ℝ≥0 → Set X)) (Υ : STL.Formula X → RTL.Formula X) : Prop :=
  ∀ R ∈ 𝓡, ∀ φ, (Υ φ).Sat R → φ.HoldsOn (ReachSequence.traceSet R)

/-- `C(R) ⊨ₜ φ ⇒ R ⊨ᵣ Υ(φ)` for every `R ∈ 𝓡`. -/
def STL.IsComplete (𝓡 : Set (ℝ≥0 → Set X)) (Υ : STL.Formula X → RTL.Formula X) : Prop :=
  ∀ R ∈ 𝓡, ∀ φ, φ.HoldsOn (ReachSequence.traceSet R) → (Υ φ).Sat R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
