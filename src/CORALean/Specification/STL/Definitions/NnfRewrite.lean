import CORALean.Specification.STL.Operations.NnfToFormula
import CORALean.Specification.STL.Operations.SampToFormula

/-!
# A normal form that rewrites to sampled time

[1, Lemma 4]: `n` has a sampled time formula implying it, and one implying `F_I n` and `G_I n`, `I
= (0,1)`. The last two are the contexts [1, Table 1]'s rows create: they wrap a rewritten formula,
not a rewritten formula's own temporal operators.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `n`, `F_I n` and `G_I n` each have a sampled time formula, at step `1`, implying them. -/
def STL.Nnf.HasSampledRewrite (n : STL.Nnf X) : Prop :=
  (∃ s : STL.Samp X, ∀ ξ, (s.toFormula 1).Sat ξ → n.toFormula.Sat ξ) ∧
  (∃ s : STL.Samp X, ∀ ξ, (s.toFormula 1).Sat ξ → (STL.Formula.finOpen 1 n.toFormula).Sat ξ) ∧
  (∃ s : STL.Samp X, ∀ ξ, (s.toFormula 1).Sat ξ → (STL.Formula.globOpen 1 n.toFormula).Sat ξ)


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
