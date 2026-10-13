module

public import CORALean.ContSet.Zonotope.Real.Operations.MulGens
public import CORALean.ContSet.Zonotope.Real.Operations.SortByLength

@[expose] public section

/-!
# `Zonotope.reduceUnderApproxRaghuraman`

The method of Raghuraman and Koeln (their Sec. 5.1; inner by [2, Thm. 3]) as [1, Sec. III-B]
prints it: sort the generators by 2-norm (`sortByLength`), take `P(j,i) = g_{s,i}ᵀ g_{s,j}` for
the `ν̂` large `i` and the small `j`, and add or subtract each small generator `j` to the large
one `i` it is strictly most aligned with. `r = ν̂ ≤ ν`; indices count from `0`. Where the strict
maximum is a `0` the printed `P/|P|` is `0/0`, which is `0` here.

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
* [2] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for constrained
      zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. III-B], Steps 1) to 3): `Ĝ = G_s T` with the printed `T`. -/
noncomputable def Zonotope.reduceUnderApproxRaghuraman (Z : Zonotope (Vec ℝ n)) (r : ℕ)
    (hr : r ≤ Z.h) : Zonotope (Vec ℝ n) :=
  let Zs := Z.sortByLength                                   -- 1) G_s
  let P := fun (j i : Fin Zs.h) => dotProduct (Zs.G i) (Zs.G j)  -- 2) P(j,i) = g_{s,i}ᵀ g_{s,j}
  let T : Mat ℝ Zs.h r := fun j i =>                         -- 3) T
    if (j : ℕ) = i then 1
    else if r ≤ j ∧ ∀ k : Fin r, k ≠ i → |P j (k.castLE hr)| < |P j (i.castLE hr)|
      then P j (i.castLE hr) / |P j (i.castLE hr)| else 0
  Zs.mulGens T                                               -- Ĝ = G_s T

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
