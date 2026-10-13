module

public import CORALean.ContSet.Zonotope.Real.Operations.SortByLength

@[expose] public section

/-!
# `Zonotope.reduceUnderApproxKochdumper`

The method of Kochdumper and Bak (CDC 2022, Prop. 1) as [1, Sec. III-C] prints it: sort the
generators by 2-norm (`sortByLength`), keep the first `ν̂ - 1` and replace the rest by their
sum, each signed by the sign of its first element (`sign x = -1` if `x < 0`, else `1`).
`r = ν̂ ≤ ν`; indices count from `0`, so "the first `ν̂ - 1`" is `i + 1 < r`.

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. III-C], Steps 1) and 2). -/
noncomputable def Zonotope.reduceUnderApproxKochdumper [NeZero n] (Z : Zonotope (Vec ℝ n))
    (r : ℕ) (hr : r ≤ Z.h) : Zonotope (Vec ℝ n) :=
  let Zs := Z.sortByLength                                   -- 1) G_s
  let gsum : Vec ℝ n := ∑ j ∈ Finset.univ.filter fun j : Fin Zs.h => r ≤ (j : ℕ) + 1,
    (if Zs.G j 0 < 0 then (-1 : ℝ) else 1) • Zs.G j        -- Σ_{i=ν̂}^{ν} sign(g_{s,i}(1)) g_{s,i}
  ⟨r, Zs.c, fun i => if (i : ℕ) + 1 < r then Zs.G (i.castLE hr) else gsum⟩  -- 2) Ĝ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
