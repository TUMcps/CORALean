module

public import CORALean.ContSet.Zonotope.Real.Operations.EnclosePointsMaiga
public import CORALean.ContSet.Zonotope.Real.Theorems.Cloud2zonotopeMem

@[expose] public section

/-!
# `Zonotope.enclosePointsMaiga` contains every point

Each candidate of [1, Alg. 5] does (`cloud2zonotope_mem`, for every `ratio`) and the least one is
one of them. Outer only: the choice of `ratio` and of principal direction decides the size, not the
enclosure.

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on
      Automatic Control, 61(9):2341-2356, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.enclosePointsMaiga_mem [NeZero N] (dir : (Fin N → Vec ℝ n) → Vec ℝ n)
    (pts : Fin N → Vec ℝ n) (j : Fin N) :
    pts j ∈ (Zonotope.enclosePointsMaiga dir pts).construct := by -- --- PROOF ---
  unfold Zonotope.enclosePointsMaiga
  generalize List.range' 2 99 = is
  generalize hZ : Zonotope.cloud2zonotope dir (1 / 100) n 0 pts = Z₀
  have h₀ : pts j ∈ Z₀.construct := hZ ▸ Zonotope.cloud2zonotope_mem dir _ n 0 pts j
  clear hZ
  induction is generalizing Z₀ with
  | nil => exact h₀
  | cons i is ih =>
    rw [List.foldl_cons]
    dsimp only
    split_ifs
    · exact ih _ (Zonotope.cloud2zonotope_mem dir _ n 0 pts j)
    · exact ih _ h₀

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
