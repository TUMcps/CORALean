import CORALean.Global.Tensor
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Real.Basic

/-!
# What [1, Alg. 1 (lower bounds)]'s lower bounds carry from one step to the next

The quantities lines 1-16 keep for the lower bounds after `k` steps: the
back-propagated direction, the constant input's particular solution as a point,
and the four support function values of lines 10 and 14-16. No set is held:
[1, Alg. 1 (lower bounds)] evaluates every set through its support function, along `ℓ`, once.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- What step `k` of [1, Alg. 1 (lower bounds)] hands the next. -/
structure LinearSys.SupportLowerState (n : ℕ) where
  /-- `d_k`, lines 1 and 8: `ℓ` propagated back by `(e^{AΔt})ᵀ`, `k` times. -/
  d : Vec ℝ n →ₗ[ℝ] ℝ
  /-- `P_u(t_k)`, lines 3 and 9 — the constant input's particular solution, a point. -/
  Pu : Vec ℝ n
  /-- `ρ(H(t_k), ℓ)`, lines 1 and 10. -/
  ρH : ℝ
  /-- `ρ(P̌_U(t_k), ℓ)`, lines 3 and 14. -/
  ρP : ℝ
  /-- `ρ(Ř(t_k), ℓ)`, line 15. -/
  ρR : ℝ
  /-- `ρ(Ř(τ_{k-1}), ℓ)`, line 16 — over the step that ends at `t_k`. -/
  ρRτ : ℝ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
