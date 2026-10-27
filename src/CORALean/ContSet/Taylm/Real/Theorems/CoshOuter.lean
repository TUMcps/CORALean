module

public import CORALean.ContSet.Taylm.Real.Operations.Cosh
public import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter
public import CORALean.ContSet.Taylm.Real.Theorems.AbsLeMag
public import CORALean.Global.ElementaryDerivBounds

@[expose] public section

/-!
# `Taylm.cosh` encloses `cosh ∘ f`

The magnitude bounds the hull, and `cosh` is monotone in `|x|`.

[1, Def. 3 (cosh)]: the result is a Taylor model of `cosh ∘ f`.

## Inputs
* `T` – Taylor model
* `f` – enclosed function

## Hypotheses
* `h` – the model encloses the function

## Conclusion
* the result encloses hyperbolic cosine of the function

## References

* [1] [K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics,
      2003.](../../../../../../references/2003/makino-ijpam-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.cosh_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    T.cosh.Encloses fun t => Real.cosh (f t) := by
  refine Taylm.taylor_outer h _ _ _ (fun ξ _ => Real.contDiff_cosh.contDiffAt) fun ξ hξ => ?_
  exact abs_iteratedDeriv_cosh_le _ (T.abs_le_mag hξ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
