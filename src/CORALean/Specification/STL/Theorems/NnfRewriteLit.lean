module

public import CORALean.Specification.STL.Definitions.NnfRewrite

@[expose] public section

/-!
# A literal rewrites to sampled time

[1, Lemma 4]: a non-temporal literal `ϱ` is already sampled time, and so are `F(0,1) ϱ` and
`G(0,1) ϱ`.

## Inputs
* `ϱ` – predicate

## Hypotheses
* none

## Conclusion
* the literal rewrites to sampled time

## References

* [1] [H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". Automated Technology for Verification and Analysis,
      2016.](../../../../../references/2016/roehm-atva-stl-model-checking.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Nnf.hasSampledRewrite_lit (ϱ : Pform X) : (STL.Nnf.lit ϱ).HasSampledRewrite :=
  ⟨⟨.lit ϱ, fun _ h => h⟩, ⟨.fin ϱ, fun _ h => h⟩, ⟨.glob ϱ, fun _ h => h⟩⟩


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
