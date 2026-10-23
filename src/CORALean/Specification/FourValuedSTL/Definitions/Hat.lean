module

public import CORALean.Specification.Kleene.Operations.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Logic.Basic

@[expose] public section

/-!
# The set-based version of an atomic predicate

`â(X') = ⊤` if `X' ≠ ∅` and `X' ⊆ ⟦a⟧`, `⊥` if `X' ≠ ∅` and `X' ∩ ⟦a⟧ = ∅`, and ⊣₁ otherwise
([1, Sec. 3 (predicate)]), `⟦a⟧ = {x ∣ a x}` the states satisfying `a`.

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


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- `â(X')`. Noncomputable: nonemptiness and inclusion of a set are decided classically. -/
noncomputable def FourValuedSTL.hat {X : Type} (a : X → Prop) (S : Set X) : Kleene :=
  if S.Nonempty ∧ S ⊆ {x | a x} then .tt
  else if S.Nonempty ∧ S ∩ {x | a x} = ∅ then .ff else .uu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
