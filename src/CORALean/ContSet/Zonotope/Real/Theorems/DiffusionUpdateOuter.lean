import CORALean.ContSet.Zonotope.Real.Operations.DiffusionUpdate
import CORALean.ContSet.Zonotope.Real.Theorems.AndAveragingOuter
import CORALean.ContSet.Zonotope.Real.Theorems.AveragingWeightsOptimal
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter

/-!
# The diffusion update encloses the intersection

[1, Alg. 1] Step 2, [1, Alg. 2] Step 2: a point in every one of the `m` shared zonotopes `Z̄ʲ` is in
the diffused zonotope. The weights of [1, Prop. 1] have sum one when every `tr(Ḡʲ Ḡʲᵀ)` is positive
(`averagingWeights_optimal`), so [1, Thm. 1] applies (`andAveraging_outer`), and the reduction
`↓_q` only enlarges (`reduce_outer`).

## References

* [1] A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute,
      360(10):6976-6993, 2023. arXiv:2003.10347.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.diffusionUpdate_outer [NeZero m] (o : ℕ) (Zb : Fin m → Zonotope (Vec ℝ n))
    (hα : ∀ j, 0 < ∑ i, ∑ k, (Zb j).G k i ^ 2) :
    (⋂ j, (Zb j).construct) ⊆ (Zonotope.diffusionUpdate o Zb).construct := by -- --- PROOF ---
  intro x hx
  have hw := (Zonotope.averagingWeights_optimal Zb hα).1
  have h1 := Zonotope.andAveraging_outer Zb (Zonotope.averagingWeights Zb)
    (by rw [hw]; exact one_ne_zero) hx
  exact Zonotope.reduce_outer _ o h1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
