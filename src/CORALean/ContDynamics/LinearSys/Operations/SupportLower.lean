module

public import CORALean.ContDynamics.LinearSys.Definitions.SupportLowerState
public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral

@[expose] public section

/-!
# [1, Alg. 1 (lower bounds)]'s lower bounds on the support function of the reachable set

Lines 1-4, 6-10 and 14-16 of `[1, Alg. 1 (lower bounds)]`, the half that computes the lower
bounds `ρ(Ř(t_k), ℓ)` and `ρ(Ř(τ_k), ℓ)`, for one direction `ℓ` and a step `Δt`.
The system is `ẋ = Ax + u`, `u ∈ U`, so `[1]`'s `B` is the identity and `p` is
zero: `ũ` is a point `c` of `U` (line 2's `center(U)`) and `U₀ = U - ũ`.

Every set enters through a support vector, which is what [1, Def. 1] pairs each
support function with and what the counterexample of [1, Sec. 4.2] is built from:
`ν₀ d` is `ν(X₀, d)` and `νU d` is `ν(U, d)`, so `ρ(X₀, d) = d (ν₀ d)` and
`ρ(U₀, d) = d (νU d) - d ũ`. Nothing here asks that they be maximizers; the
theorems that need it say so. `T` is `MatExp.expIntegral`, [1]'s Eq. (13) without
its `A⁻¹`. The loop of line 6 is the recursion on `k`; the state after `k` steps
carries `d_k`, `P_u(t_k)`, `ρ(H(t_k), ℓ)`, `ρ(P̌_U(t_k), ℓ)` and the two outputs,
`ρ(Ř(t_k), ℓ)` and `ρ(Ř(τ_{k-1}), ℓ)`.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1 (lower bounds)]: the state after `k` steps of `Δt`, lines 1-4 at `k = 0` and the
body of line 6's loop, lines 7-10 and 14-16, after that. -/
noncomputable def LinearSys.supportLower (sys : LinearSys 𝕋 n) (Δt : ℝ)
    (ν₀ νU : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n) (c : Vec ℝ n) (ℓ : Vec ℝ n →ₗ[ℝ] ℝ) :
    ℕ → LinearSys.SupportLowerState n
  | 0 =>
      let ρX₀ := fun d : Vec ℝ n →ₗ[ℝ] ℝ => d (ν₀ d)                  -- Def. 1
      let d₀ := ℓ                                                       -- l. 1
      let ρH₀ := ρX₀ ℓ                                                  -- l. 1
      let Pu₀ : Vec ℝ n := 0                                            -- l. 3
      let ρP₀ : ℝ := 0                                                  -- l. 3
      ⟨d₀, Pu₀, ρH₀, ρP₀, ρH₀ + ρP₀, ρH₀ + ρP₀⟩
  | k + 1 =>
      let s := sys.supportLower Δt ν₀ νU c ℓ k                         -- step `k`
      let A := toRealMat sys.A
      let ρX₀ := fun d : Vec ℝ n →ₗ[ℝ] ℝ => d (ν₀ d)                  -- Def. 1
      let ũ := c                                                        -- l. 2
      let ρU₀ := fun d : Vec ℝ n →ₗ[ℝ] ℝ => d (νU d) - d ũ            -- l. 2, U₀ = U - ũ
      let T := MatExp.expIntegral A Δt                                  -- (13)
      let PuΔt := T *ᵥ ũ                                                -- l. 4, (12)
      let ρPΔt := fun d : Vec ℝ n →ₗ[ℝ] ℝ => ρU₀ (d.comp (mulVecLin T)) -- l. 4, (17), (1)
      let d' := s.d.comp (mulVecLin (exp (Δt • A)))                     -- l. 8
      let Pu' := exp (Δt • A) *ᵥ s.Pu + PuΔt                            -- l. 9
      let ρH' := ρX₀ d' + ℓ Pu'                                         -- l. 10
      let ρP' := s.ρP + ρPΔt s.d                                        -- l. 14
      let ρR' := ρH' + ρP'                                              -- l. 15
      let ρRτ := max s.ρH ρH' + s.ρP                                    -- l. 16
      ⟨d', Pu', ρH', ρP', ρR', ρRτ⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
