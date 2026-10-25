module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Plus

@[expose] public section

/-!
# `PolyZonotope.plusBox`: what a sub-box of the factors becomes under `plus`

`plus` lays the two factor blocks side by side, so a constraint on the first
operand's factors travels into the sum untouched while the summand's are fresh
and stay free in their own box. The bookkeeping [1, Lemma 4]'s (23) step does,
named so a statement about one post step can be read.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope
* `B` – box of factor values of the first set

## Output
* box of factor values of the sum

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control, 2020.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The first operand's factors held where `B` holds them, the second's left
free in their own box. -/
def PolyZonotope.plusBox (pZ₁ pZ₂ : PolyZonotope α) (B : Set (Fin pZ₁.p → ℝ)) :
    Set (Fin (pZ₁.plus pZ₂).p → ℝ) :=
  {a | (fun k => a (Fin.castAdd pZ₂.p k)) ∈ B ∧ ∀ k, |a (Fin.natAdd pZ₁.p k)| ≤ 1}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
