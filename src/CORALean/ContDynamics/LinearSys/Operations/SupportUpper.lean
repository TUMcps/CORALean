module

public import CORALean.ContDynamics.LinearSys.Definitions.SupportUpperState
public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution

@[expose] public section

/-!
# [1, Alg. 1 (upper bounds)]'s upper bounds on the support function of the reachable set

Lines 1-5, 7-13 of `[1, Alg. 1 (upper bounds)]`, for one direction `ℓ` and a step `Δt`. The system
is `ẋ = Ax + u`, `u ∈ U`, so `[1]`'s `B` is the identity and `p` is zero, and every set is a
set of the representation `S`: the representation's own `Recenter` splits `U` into `ũ`, a
point, and `U₀`, a set holding the origin (line 2); `P̂_U(Δt)` is `inputSolution` at `U₀`
(Eq. 16), and `C = F X₀ ⊕ G ũ` (Eq. 14-15) the two correction matrices applied to `X₀` and to
`ũ`, with `X₀` itself where `[1]` encloses it by `box(X₀)` for a representation that cannot
multiply an interval matrix. Every support function is read from `ρ`, which any representation
that can bound `ρ(X, d)` supplies. The loop of line 6 is the recursion on `k`; the state after
`k` steps carries `d_k`, `P_u(t_k)`, `ρ(H(t_k), ℓ)`, `ρ(P̂_U(t_k), ℓ)` and the two outputs,
`ρ(R̂(t_k), ℓ)` and `ρ(R̂(τ_{k-1}), ℓ)`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable [∀ n, Recenter (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1 (upper bounds)]: the state after `k` steps of `Δt` at truncation order `η`, lines
1-5 at `k = 0` and the body of line 6's loop, lines 7-13, after that. -/
noncomputable def LinearSys.supportUpper (sys : LinearSys 𝕋 n) (Δt : ℝ) (η : ℕ) (X₀ U : S n)
    (ρ : S n → (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ) (ℓ : Vec ℝ n →ₗ[ℝ] ℝ) :
    ℕ → LinearSys.SupportUpperState n
  | 0 =>
      -- 1. d₀ ← ℓ
      let d₀ := ℓ
      -- 1. ρ(H(t₀), ℓ) ← ρ(X₀, ℓ)
      let ρH₀ := ρ X₀ ℓ
      -- 3. P_u(t₀) ← 0
      let Pu₀ : Vec ℝ n := 0
      -- 3. ρ(P̂_U(t₀), ℓ) ← 0
      let ρP₀ : ℝ := 0
      ⟨d₀, Pu₀, ρH₀, ρP₀, ρH₀ + ρP₀, ρH₀ + ρP₀⟩
  | k + 1 =>
      let s := sys.supportUpper Δt η X₀ U ρ ℓ k                         -- step `k`
      let A := toRealMat sys.A
      -- 2. ũ ← center(U)
      let ũ := Recenter.center U
      -- 2. U₀ ← U - ũ
      let U₀ := Recenter.recenter U
      let T := MatExp.expIntegral A Δt                                  -- (13)
      -- 4. P_u(Δt), eq. (12)
      let PuΔt := T *ᵥ ũ
      -- 4. P̂_U(Δt), eq. (16)
      let PUΔt := sys.inputSolution Δt η U₀
      let F := MatExp.correctionMatrix A Δt η                           -- (14)
      let G := MatExp.constCorrectionMatrix A Δt η                      -- (15)
      -- 5. C ← F X₀ ⊕ G ũ
      let C := Plus.plus (Mtimes.mtimes (𝕄 := ℐ) F X₀)
        (Mtimes.mtimes (𝕄 := ℐ) G (OfPoint.ofPoint ũ))
      -- 8. d_{k+1} ← (e^{AΔt})ᵀ d_k
      let d' := s.d.comp (mulVecLin (exp (Δt • A)))
      -- 9. P_u(t_{k+1})
      let Pu' := exp (Δt • A) *ᵥ s.Pu + PuΔt
      -- 10. ρ(H(t_{k+1}), ℓ)
      let ρH' := ρ X₀ d' + ℓ Pu'
      -- 11. ρ(P̂_U(t_{k+1}), ℓ)
      let ρP' := s.ρP + ρ PUΔt s.d
      -- 12. ρ(R̂(t_{k+1}), ℓ)
      let ρR' := ρH' + ρP'
      -- 13. ρ(R̂(τ_k), ℓ)
      let ρRτ := max s.ρH ρH' + ρ C s.d + ρP'
      ⟨d', Pu', ρH', ρP', ρR', ρRτ⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
