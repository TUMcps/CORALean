module

public import CORALean.Specification.FourValuedSTL.Definitions.Hat
public import CORALean.Specification.FourValuedSignal.Definitions.IsValid
public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.KleeneSignal.Definitions.IsValid
public import Mathlib.Data.NNReal.Defs

@[expose] public section

/-!
# The satisfaction signal of an atom over a partial reachable set

For `R̃ : T → 2^X`, `⟦a⟧_R̃(t) := â(R̃(t))` for `t ∈ T` and ⊣₂ otherwise
([1, Sec. 4.3 (satisfaction)]). `IsPartialAtomSignal T Rp a s` says that the `U₂`-signal `s` is that
function of time, and valid: the paper's signals are arbitrary functions, and the operators that
combine them need the finite variability a valid signal has ([1, Sec. 2.3 (signals)]).

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

open scoped NNReal


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- `s` is the signal `t ↦ ⟦a⟧_R̃(t)` of the atom `a`, of finite variability. -/
def FourValuedSTL.IsPartialAtomSignal {X : Type} (T : Set ℝ≥0) (Rp : ℝ≥0 → Set X)
    (a : X → Prop) (s : FourValuedSignal ℝ) : Prop := s.IsValid ∧ ∀ t : ℝ≥0, s.at t =
  if t ∈ T then FourValued.fromKleene (FourValuedSTL.hat a (Rp t)) else FourValued.ii

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
