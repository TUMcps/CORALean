import CORALean.ContSet.Zonotope.Real.Operations.OfEchelon
import CORALean.ContSet.Zonotope.Real.Operations.ReduceScottStep

/-!
# `Zonotope.ofEchelon_reduceScottStep_h`

[1, Sec. 4.3 (new reduction)]: "`Z̃ = X̃ + Y` is defined, which has one fewer generator than `Z`".
`rfl`: the state goes from `n + (k + 1)` generators to `n + k`, so `k` steps reduce `n_g` to
`n_g − k`.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.3 (new reduction)]: one step removes exactly one generator. -/
theorem Zonotope.ofEchelon_reduceScottStep_h {n k : ℕ} (c : Vec ℝ n) (T : Mat ℝ n n)
    (R : Fin (k + 1) → Vec ℝ n) (ind : Fin (k + 1)) :
    (Zonotope.ofEchelon c (Zonotope.reduceScottStep T R ind).1
        (Zonotope.reduceScottStep T R ind).2).h + 1
      = (Zonotope.ofEchelon c T R).h := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
