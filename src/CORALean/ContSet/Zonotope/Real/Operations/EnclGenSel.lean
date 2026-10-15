module

public import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
public import CORALean.ContSet.Zonotope.Real.Operations.EnclCoverLoop
public import CORALean.ContSet.Zonotope.Real.Operations.EnclRatioLoop
public import CORALean.ContSet.Zonotope.Real.Operations.Recenter
public import CORALean.Global.Sort

@[expose] public section

/-!
# `Alg. 1`: which generators of the minuend have to enclose the subtrahend

[1, Alg. 1] picks `Z_{m,encl} ⊇ Z_s` out of the minuend's own generators, so
that [1, Prop. 4] can take the difference against the enclosing part alone and
add the remainder back afterwards. Longest generators first, greedily, while
the interval hulls' worst coordinate ratio is still above `µ̄`; then one at a
time until the subtrahend actually fits.

`sort` ranks by the squared length, which orders generators as `‖·‖₂` does
without a square root; `enclGenSel_subset` proves what holds whatever the
caller's `encloses` answers.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: the generators of `Zm` that are kept to enclose `Zs`. -/
noncomputable def Zonotope.enclGenSel (le lt : ℝ → ℝ → Bool)
    (encloses : Zonotope (Vec ℝ n) → Bool) (Zm Zs : Zonotope (Vec ℝ n)) (μbar : ℝ) :
    Zonotope (Vec ℝ n) :=
  -- 1. `G_sort ← sort(G_m)`, longest first
  let Gsort := sortPerm fun i j => le (∑ k, Zm.G j k ^ 2) (∑ k, Zm.G i k ^ 2)
  -- 2. `r_sel ← 0`
  let rsel : Vec ℝ n := 0
  -- 3. `r_s ← rad(box(Z_s))`
  let rs := Zs.recenter.absBound
  -- 4. lines 4-10: `µ ← inf`, `ξ ← 0`; while `µ > µ̄` and `ξ < n_m`, grow `ξ` by the ratio
  let ξratio := Zm.enclRatioLoop lt Gsort rs μbar Zm.h 0 rsel
  -- 11. lines 11-13: while `Z_s ⊄ (c_s, g_sort^(1), …, g_sort^(ξ))`, `ξ ← ξ + 1`
  let ξ := Zm.enclCoverLoop encloses Gsort Zs.c Zm.h ξratio
  -- 14. `Z_{m,encl} ← (c_m, g_sort^(1), …, g_sort^(ξ))`
  Zm.genSelection Gsort Zm.c ξ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
