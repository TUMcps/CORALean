module

public import CORALean.ContSet.Taylm.Real.Operations.Asin
public import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter
public import CORALean.ContSet.Taylm.Real.Theorems.AbsLeMag
public import CORALean.Global.ElementaryDerivBounds

@[expose] public section

/-!
# `Taylm.asin` encloses `asin ∘ f`

Where the magnitude is below one, so that the hull stays inside `(-1, 1)`.

[1, Def. 3 (arcsin)]: a Taylor model of `arcsin ∘ f`.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.asin_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hdom : T.mag < 1) :
    T.asin.Encloses fun t => Real.arcsin (f t) := by -- --- PROOF ---
  refine Taylm.taylor_outer h _ _ _ (fun ξ hξ => ?_) fun ξ hξ => ?_
  · have hm := lt_of_le_of_lt (T.abs_le_mag hξ) hdom
    rw [abs_lt] at hm
    exact Real.contDiffAt_arcsin (by linarith [hm.1]) (by linarith [hm.2])
  · exact abs_iteratedDeriv_asin_le _ (T.abs_le_mag hξ) hdom

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
