module

public import CORALean.Specification.FourValuedSignal.Theorems.AtNot
public import CORALean.Specification.FourValuedSignal.Theorems.Basic
public import CORALean.Specification.KleeneSignal.Theorems.Basic

@[expose] public section

/-!
# The negation of four-valued signals respects refinement

If the Kleene signal `Λ` refines the four-valued `Λ̃` (`Λ ≺ Λ̃`), then `¬Λ ≺ ¬Λ̃`: the step of the
induction in [1, Thm. 2] (and [1, Sec. 4.3 (refinements)]) for `¬`.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.not_isRefinedBy (s : FourValuedSignal ℝ) (k : KleeneSignal ℝ)
    (hs : s.IsValid) (hk : k.IsValid) (h : s.IsRefinedBy k) :
    s.not.IsRefinedBy k.not := by -- --- PROOF ---
  intro t ht
  rw [FourValuedSignal.at_not s hs, KleeneSignal.at_not k hk]
  intro hne
  have h1 : s.at t ≠ FourValued.ii := fun h0 => hne (by rw [h0]; rfl)
  rw [FourValued.fromKleene_not, h t ht h1]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
