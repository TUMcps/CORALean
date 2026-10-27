module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Zonotope.reduceUnderApproxCluster`

The clustering method of [1, Sec. IV-A], Steps 2) and 3): the generators of each cluster
`C_k` are summed, each signed by the sign of its first element, and the sums are the reduced
generators. The partition into clusters (Step 1, `k`-means++ on the distance `1 - dcos`, a
randomized algorithm) is the argument `cl : i ↦ k` with `gᵢ ∈ C_k`.

## Inputs
* `Z` – zonotope
* `r` – cluster count
* `cl` – cluster assignment of the generators

## Output
* zonotope of the signed cluster sums

## References

* [1] [L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the Order Reduction
      of Zonotopes". IEEE Control Systems Letters,
      2025.](../../../../../../references/2025/luetzow-lcss-underapprox-order-reduction.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. IV-A]: `ĝ_k = Σ_{g ∈ C_k} sign(g(1)) g`, `Ĝ = [ĝ_1 … ĝ_ν̂]`. -/
noncomputable def Zonotope.reduceUnderApproxCluster [NeZero n] (Z : Zonotope (Vec ℝ n)) {r : ℕ}
    (cl : Fin Z.h → Fin r) : Zonotope (Vec ℝ n) :=
  let C := fun k : Fin r => Finset.univ.filter fun i => cl i = k   -- 1) the clusters C_k
  let ĝ := fun k : Fin r =>                                         -- 2) ĝ_k
    ∑ i ∈ C k, (if Z.G i 0 < 0 then (-1 : ℝ) else 1) • Z.G i
  ⟨r, Z.c, ĝ⟩                                                       -- 3) Ĝ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
