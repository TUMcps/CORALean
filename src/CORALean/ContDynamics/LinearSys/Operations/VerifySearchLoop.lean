module

public import CORALean.ContDynamics.LinearSys.Definitions.HeldSim
public import CORALean.ContDynamics.LinearSys.Definitions.VerifySearchState
public import CORALean.ContDynamics.LinearSys.Operations.SupportCounterexample
public import CORALean.ContDynamics.LinearSys.Operations.SupportLower
public import CORALean.ContDynamics.LinearSys.Operations.SupportUpper
public import CORALean.Specification.Definitions.VerifyAnswer

@[expose] public section

/-!
# [1, Alg. 3 (search)]: the `repeat` loop

Lines 3, 7-9 and 14-25 of `[1, Alg. 3 (search)]`, with the two exits of lines 4-6 and 12-13
where the paper has them. `Alg. 1` of line 3 is `supportUpper` and `supportLower` at `Δt`,
`k = t/Δt` steps. Everything `Alg. 3` asks of a set it asks through support functions and
support vectors, which are arguments: `ρL` and `νL` for `L`, `νhat` for the outer approximation
`R̂(t)` (`[1]` computes it "in the same way" as the inner one), `ν₀` and `νU` for the inner one,
whose `ν(Ř(t), ℓ)` is the run of Eq. (18) from `supportCounterexample`. So are the tests and
constructions of the polytopes: `inHull` for `0 ∈ P`, `closestFacet` for lines 19-20 (the
quadratic program `min_{x ∈ P̌} ‖x‖²` and the vertices on the facet it finds) and `gramSchmidt`
for line 23. The loop has no stated iteration count, so `fuel` is an argument and `undecided`
its answer when it runs out. `ℓ₁ ← I_n(·,1)` of line 1 is an argument too, the restart of line 15
returning to it with `i ← 1`; `falsifiable ← false` of lines 7-9 is the conjunction of the old
flag with the failure of the test. The polytopes are the lists of their vertices.

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
variable [∀ n, Recentre (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3 (search)] from the loop variables `s`: the answer of the first exit reached within
`fuel` iterations, `undecided` if there is none. -/
noncomputable def LinearSys.verifySearchLoop (sys : LinearSys 𝕋 n) (X₀ U : S n) (η : ℕ)
    (ρ : S n → (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ) (ν₀ νU νL : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n)
    (νhat : ℝ → (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n) (ρL : (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ)
    (inHull : List (Vec ℝ n) → Bool)
    (closestFacet : List (Vec ℝ n) → (Vec ℝ n →ₗ[ℝ] ℝ) × List ℕ)
    (gramSchmidt : List (Vec ℝ n) → (Vec ℝ n →ₗ[ℝ] ℝ)) (ℓ₁ : Vec ℝ n →ₗ[ℝ] ℝ) :
    ℕ → LinearSys.VerifySearchState n → VerifyAnswer
  | 0, _ => .undecided
  | fuel + 1, s =>
      -- 3. ρ(R̂(t), ℓ_i), the upper bound of Alg. 1 with Δt
      let ρRhat := (sys.supportUpper s.Δt η X₀ U ρ s.ℓ s.k).ρR
      -- 3. ρ(Ř(t), ℓ_i), the lower bound of Alg. 1 with Δt
      let ρRcheck :=
        (sys.supportLower s.Δt ν₀ νU (Recentre.centre U) s.ℓ s.k).ρR
      -- 4.-6. return safe
      if ρRhat + ρL (-s.ℓ) < 0 then .safe
      else
        -- 7.-9. falsifiable ← false where ρ(Ř(t), ℓ_i) + ρ(L, -ℓ_i) < 0
        let falsifiable := s.falsifiable && !decide (ρRcheck + ρL (-s.ℓ) < 0)
        -- 10. v̂_i ← ν(R̂(t), ℓ_i) - ν(L, -ℓ_i)
        let vhat := νhat s.Δt s.ℓ - νL (-s.ℓ)
        -- 10. v̌_i ← ν(Ř(t), ℓ_i) - ν(L, -ℓ_i)
        let vcheck := sys.heldSim s.Δt (sys.supportCounterexample s.Δt ν₀ νU s.ℓ s.k).1
          (sys.supportCounterexample s.Δt ν₀ νU s.ℓ s.k).2 s.k - νL (-s.ℓ)
        -- 11. P̂ ← conv(P̂, v̂_i)
        let Phat := s.Phat ++ [vhat]
        -- 11. P̌ ← conv(P̌, v̌_i)
        let Pcheck := s.Pcheck ++ [vcheck]
        -- 12.-13. return unsafe where 0 ∈ P̌
        if inHull Pcheck then .violated
        -- 14. else if falsifiable = false ∧ 0 ∈ P̂
        else if falsifiable = false ∧ inHull Phat = true then
          -- 15.-16. Δt ← 0.5 Δt, i ← 1, P̂, P̌ ← ∅, falsifiable ← true; continue
          sys.verifySearchLoop X₀ U η ρ ν₀ νU νL νhat ρL inHull closestFacet gramSchmidt ℓ₁
            fuel ⟨1, ℓ₁, s.Δt / 2, 2 * s.k, [], [], true⟩
        -- 18. if i > n + 1
        else if s.i > n + 1 then
          -- 19. H ← the halfspace of the facet of P̌ closest to 0
          let facet := closestFacet Pcheck
          -- 20. o₁, …, o_n ← the indices of the vertices on the facet
          let o := facet.2
          -- 21. P̂ ← ⟨[v̂_{o₁} … v̂_{o_n}]⟩_V
          let Phat' := o.filterMap fun j => Phat[j]?
          -- 21. P̌ ← ⟨[v̌_{o₁} … v̌_{o_n}]⟩_V
          let Pcheck' := o.filterMap fun j => Pcheck[j]?
          -- 25. ℓ_{i+1} ← the facet's normal, i ← i + 1
          sys.verifySearchLoop X₀ U η ρ ν₀ νU νL νhat ρL inHull closestFacet gramSchmidt ℓ₁
            fuel ⟨s.i + 1, facet.1, s.Δt, s.k, Phat', Pcheck', falsifiable⟩
        else
          -- 23. h ← a vector orthogonal to v̌_1, …, v̌_i, by Gram-Schmidt
          let h := gramSchmidt Pcheck
          -- 25. ℓ_{i+1} ← h, i ← i + 1
          sys.verifySearchLoop X₀ U η ρ ν₀ νU νL νhat ρL inHull closestFacet gramSchmidt ℓ₁
            fuel ⟨s.i + 1, h, s.Δt, s.k, Phat, Pcheck, falsifiable⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
