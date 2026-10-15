module

public import CORALean.ContDynamics.LinearSys.Operations.SupportLower

@[expose] public section

/-!
# Line 16's lower bound is no more than line 15's at one end of the step

[1, Alg. 1 (lower bounds)], line 16:
`ρ(Ř(τ_k), ℓ) = max{ρ(H(t_k), ℓ), ρ(H(t_{k+1}), ℓ)} + ρ(P̌_U(t_k), ℓ)`. When the
maximum is `ρ(H(t_k), ℓ)` this is line 15's `ρ(Ř(t_k), ℓ)`. When it is
`ρ(H(t_{k+1}), ℓ)` it is line 15's `ρ(Ř(t_{k+1}), ℓ)` less line 14's last summand
`ρ(T U₀, d_k)`, which is not negative exactly when `0 ∈ U₀`, that is when line 2's
`ũ` lies in `U`. So line 16 is a lower bound on the time-interval reachable set only
because one of the two time-point lower bounds at the ends of `τ_k` is, and the
point attaining it is a state at `t_k` or at `t_{k+1}`, not one inside the step.

The hypothesis `hc` is that `ũ` lies in `U` as `νU` sees it: no point `νU d` is
below `ũ` along `d`. A support vector of a set containing `ũ` satisfies it; the
center of `U`'s bounding box, which [1]'s Sec. 3 offers in place of the geometric
center, need not lie in `U`, and then line 16 can exceed both ends.

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

open CORALean.Real
open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1 (lower bounds)]: with `ũ ∈ U`, line 16's `ρ(Ř(τ_k), ℓ)` is at most the larger of
line 15's `ρ(Ř(t_k), ℓ)` and `ρ(Ř(t_{k+1}), ℓ)`. -/
theorem LinearSys.supportLower_timeInterval_le (sys : LinearSys 𝕋 n) (Δt : ℝ)
    (ν₀ νU : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n) {c : Vec ℝ n}
    (hc : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, d c ≤ d (νU d))
    (ℓ : Vec ℝ n →ₗ[ℝ] ℝ) (k : ℕ) :
    (sys.supportLower Δt ν₀ νU c ℓ (k + 1)).ρRτ
      ≤ max (sys.supportLower Δt ν₀ νU c ℓ k).ρR
          (sys.supportLower Δt ν₀ νU c ℓ (k + 1)).ρR := by -- --- PROOF ---
  set s := sys.supportLower Δt ν₀ νU c ℓ k
  set s' := sys.supportLower Δt ν₀ νU c ℓ (k + 1)
  set dT := s.d.comp (mulVecLin (MatExp.expIntegral (toRealMat sys.A) Δt))
  have hR : s.ρR = s.ρH + s.ρP := by cases k <;> rfl
  have hτ : s'.ρRτ = max s.ρH s'.ρH + s.ρP := rfl
  have hR' : s'.ρR = s'.ρH + (s.ρP + (dT (νU dT) - dT c)) := rfl
  rw [hτ, hR, hR', ← max_add_add_right]
  exact max_le_max le_rfl (by linarith [hc dT])

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
