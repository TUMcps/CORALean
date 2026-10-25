module

public import CORALean.Specification.STL.Definitions.DiscreteFormula

@[expose] public section

/-!
# Eventually as until

[1, Sec. II-B (eventually)]: `◇[a,b] φ = ⊤ U[a,b] φ`, so that `x ⊨ ◇[a,b] φ` iff `φ` holds at some
step between `a` and `b`. With `⊤` the predicate `μ ≡ 1`, the until's `φ₁` holds everywhere and
only the witness of `φ` remains.

## Inputs
* `a` – interval lower bound
* `b` – interval upper bound
* `φ` – formula
* `x` – trace
* `t` – time step

## Hypotheses
* `hab` – the bounds are ordered

## Conclusion
* eventually holds iff the until with true holds

## References

* [1] V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and
      S. A. Seshia. "Model Predictive Control with Signal Temporal Logic Specifications". In
      Proc. of the 53rd IEEE Conference on Decision and Control (CDC), pp. 81-87, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.DFormula.eventually_sat_iff (a b : ℕ) (hab : a ≤ b) (φ : STL.DFormula X)
    (x : ℕ → X) (t : ℕ) :
    (STL.DFormula.eventually a b hab φ).Satisfies x t ↔
      (STL.DFormula.until a b hab STL.DFormula.tt φ).Satisfies x t := by
  simp [STL.DFormula.Satisfies]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
