module

public import CORALean.ContSet.Taylm.Real.Operations.Cos
public import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter
public import CORALean.Global.ElementaryDerivBounds

@[expose] public section

/-!
# `Taylm.cos` encloses `cos ∘ f`

Every derivative of `cos` is bounded by one.

[1, Def. 3 (cos)]: the result is a Taylor model of `cos ∘ f`.

## Inputs
* `T` – Taylor model
* `f` – enclosed function

## Hypotheses
* `h` – the model encloses the function

## Conclusion
* the result encloses cosine of the function

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.cos_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    T.cos.Encloses fun t => Real.cos (f t) := by
  refine Taylm.taylor_outer h _ _ _ (fun ξ _ => Real.contDiff_cos.contDiffAt) fun ξ _ => ?_
  exact abs_iteratedDeriv_cos_le _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
