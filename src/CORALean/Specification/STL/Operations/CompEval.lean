import CORALean.Specification.STL.Definitions.Composition

/-!
# Evaluating a composition

`f(φ₁, …, φ_n)`, the formula a composition builds from its parts [1, Lemma 3].

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

/-- `f(φ₁, …, φ_n)`. -/
def STL.Comp.eval {n : ℕ} : STL.Comp n → (Fin n → STL.Formula X) → STL.Formula X
  | .hole i, φ => φ i
  | .and f g, φ => (f.eval φ).and (g.eval φ)
  | .or f g, φ => .or (f.eval φ) (g.eval φ)
  | .next c f, φ => .next c (f.eval φ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
