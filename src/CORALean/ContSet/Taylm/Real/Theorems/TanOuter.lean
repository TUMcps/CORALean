module

public import CORALean.ContSet.Taylm.Real.Operations.Tan
public import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter
public import CORALean.ContSet.Taylm.Real.Theorems.AbsLeMag
public import CORALean.Global.ElementaryDerivBounds

@[expose] public section

/-!
# `Taylm.tan` encloses `tan ∘ f`

Where the magnitude is below `π/2`, so that the hull stays in `tan`'s first branch.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.tan_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hdom : T.mag < Real.pi / 2) :
    T.tan.Encloses fun t => Real.tan (f t) := by -- --- PROOF ---
  refine Taylm.taylor_outer h _ _ _ (fun ξ hξ => ?_) fun ξ hξ =>
    abs_iteratedDeriv_tan_le _ (T.abs_le_mag hξ) hdom
  have hm := lt_of_le_of_lt (T.abs_le_mag hξ) hdom
  rw [abs_lt] at hm
  exact Real.contDiffAt_tan.2 (Real.cos_pos_of_mem_Ioo ⟨hm.1, hm.2⟩).ne'

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
