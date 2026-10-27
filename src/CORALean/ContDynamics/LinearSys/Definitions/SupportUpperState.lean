module

public import CORALean.Global.Tensor
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# What [1, Alg. 1 (upper bounds)]'s upper bounds carry from one step to the next

The quantities lines 1-13 keep for the upper bounds after `k` steps: the back-propagated
direction, the constant input's particular solution as a point, and the five support function
values of lines 10-13. No set is held: [1, Alg. 1 (upper bounds)] evaluates every set through its
support function, along `ℓ`, once.

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control,
      2023.](../../../../../references/2023/wetzlinger-hscc-support-functions.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- What step `k` of [1, Alg. 1 (upper bounds)] hands the next. -/
structure LinearSys.SupportUpperState (n : ℕ) where
  /-- `d_k`, lines 1 and 8: `ℓ` propagated back by `(e^{AΔt})ᵀ`, `k` times. -/
  d : Vec ℝ n →ₗ[ℝ] ℝ
  /-- `P_u(t_k)`, lines 3 and 9 — the constant input's particular solution, a point. -/
  Pu : Vec ℝ n
  /-- `ρ(H(t_k), ℓ)`, lines 1 and 10. -/
  ρH : ℝ
  /-- `ρ(P̂_U(t_k), ℓ)`, lines 3 and 11. -/
  ρP : ℝ
  /-- `ρ(R̂(t_k), ℓ)`, line 12. -/
  ρR : ℝ
  /-- `ρ(R̂(τ_{k-1}), ℓ)`, line 13 — over the step that ends at `t_k`. -/
  ρRτ : ℝ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
