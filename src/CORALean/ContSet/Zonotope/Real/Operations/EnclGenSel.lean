import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
import CORALean.ContSet.Zonotope.Real.Operations.EnclCoverLoop
import CORALean.ContSet.Zonotope.Real.Operations.EnclRatioLoop
import CORALean.ContSet.Zonotope.Real.Operations.Recentre
import CORALean.Global.Sort

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
  let Gsort := sortPerm fun i j => le (∑ k, Zm.G j k ^ 2) (∑ k, Zm.G i k ^ 2)  -- 1. sort(Gm)
  let rsel : Vec ℝ n := 0                                       -- 2. r_sel ← 0
  let rs := Zs.recentre.absBound                                -- 3. r_s ← rad(box(Zs))
  let ξratio := Zm.enclRatioLoop lt Gsort rs μbar Zm.h 0 rsel   -- 4.-10. grow by the ratio
  let ξ := Zm.enclCoverLoop encloses Gsort Zs.c Zm.h ξratio     -- 11.-13. grow until Zs fits
  Zm.genSelection Gsort Zm.c ξ                                  -- 14. Z_{m,encl}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
