module

public import CORALean.Specification.STL.Operations.NnfToFormula
public import CORALean.Specification.STL.Operations.SampToFormula

@[expose] public section

/-!
# A normal form that rewrites to sampled time

[1, Lemma 4]: `n` has a sampled time formula implying it, and one implying `F_I n` and `G_I n`, `I
= (0,1)`. The last two are the contexts [1, Table 1]'s rows create: they wrap a rewritten formula,
not a rewritten formula's own temporal operators.

## Inputs
* `n` – formula in negation normal form

## Output
* the formula and its eventually and always have sampled time rewrites

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and Hybrid
      Systems". Automated Technology for Verification and Analysis, 2016.
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

/-- `n`, `F_I n` and `G_I n` each have a sampled time formula, at step `1`, implying them. -/
def STL.Nnf.HasSampledRewrite (n : STL.Nnf X) : Prop :=
  (∃ s : STL.Samp X, ∀ ξ, (s.toFormula 1).Satisfies ξ → n.toFormula.Satisfies ξ) ∧
  (∃ s : STL.Samp X, ∀ ξ, (s.toFormula 1).Satisfies ξ → (STL.Formula.finOpen 1
      n.toFormula).Satisfies ξ) ∧
  (∃ s : STL.Samp X, ∀ ξ, (s.toFormula 1).Satisfies ξ → (STL.Formula.globOpen 1
      n.toFormula).Satisfies ξ)


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
