module

public import CORALean.ContSet.Taylm.Real.Operations.Acos
public import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter
public import CORALean.ContSet.Taylm.Real.Theorems.AbsLeMag
public import CORALean.Global.ElementaryDerivBounds

@[expose] public section

/-!
# `Taylm.acos` encloses `acos ∘ f`

Where the magnitude is below one, so that the hull stays inside `(-1, 1)`.

[1, Def. 3 (arccos)]: a Taylor model of `arccos ∘ f`.

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

theorem Taylm.acos_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hdom : T.mag < 1) :
    T.acos.Encloses fun t => Real.arccos (f t) := by -- --- PROOF ---
  refine Taylm.taylor_outer h _ _ _ (fun ξ hξ => ?_) fun ξ hξ => ?_
  · have hm := lt_of_le_of_lt (T.abs_le_mag hξ) hdom
    rw [abs_lt] at hm
    exact Real.contDiffAt_arccos (by linarith [hm.1]) (by linarith [hm.2])
  · exact abs_iteratedDeriv_acos_le _ (T.abs_le_mag hξ) hdom

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
