import CORALean.ContDynamics.LinearSys.Definitions.HeldSim
import CORALean.ContDynamics.LinearSys.Definitions.VerifySearchState
import CORALean.ContDynamics.LinearSys.Operations.SupportCounterexample
import CORALean.ContDynamics.LinearSys.Operations.SupportLower
import CORALean.ContDynamics.LinearSys.Operations.SupportUpper
import CORALean.Specification.Definitions.VerifyAnswer

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

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


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
      let ρRhat := (sys.supportUpper s.Δt η X₀ U ρ s.ℓ s.k).ρR                 -- l. 3, upper
      let ρRcheck :=
        (sys.supportLower s.Δt ν₀ νU (Recentre.centre U) s.ℓ s.k).ρR           -- l. 3, lower
      if ρRhat + ρL (-s.ℓ) < 0 then .safe                                     -- l. 4-6
      else
        let falsifiable := s.falsifiable && !decide (ρRcheck + ρL (-s.ℓ) < 0)  -- l. 7-9
        let vhat := νhat s.Δt s.ℓ - νL (-s.ℓ)                                 -- l. 10
        let vcheck := sys.heldSim s.Δt (sys.supportCounterexample s.Δt ν₀ νU s.ℓ s.k).1
          (sys.supportCounterexample s.Δt ν₀ νU s.ℓ s.k).2 s.k - νL (-s.ℓ)    -- l. 10
        let Phat := s.Phat ++ [vhat]                                          -- l. 11
        let Pcheck := s.Pcheck ++ [vcheck]                                    -- l. 11
        if inHull Pcheck then .violated                                       -- l. 12-13
        else if falsifiable = false ∧ inHull Phat = true then                 -- l. 14
          sys.verifySearchLoop X₀ U η ρ ν₀ νU νL νhat ρL inHull closestFacet gramSchmidt ℓ₁
            fuel ⟨1, ℓ₁, s.Δt / 2, 2 * s.k, [], [], true⟩                     -- l. 15-16
        else if s.i > n + 1 then                                              -- l. 18
          let facet := closestFacet Pcheck                                    -- l. 19
          let o := facet.2                                                    -- l. 20
          let Phat' := o.filterMap fun j => Phat[j]?                          -- l. 21
          let Pcheck' := o.filterMap fun j => Pcheck[j]?                      -- l. 21
          sys.verifySearchLoop X₀ U η ρ ν₀ νU νL νhat ρL inHull closestFacet gramSchmidt ℓ₁
            fuel ⟨s.i + 1, facet.1, s.Δt, s.k, Phat', Pcheck', falsifiable⟩    -- l. 25
        else
          let h := gramSchmidt Pcheck                                         -- l. 23
          sys.verifySearchLoop X₀ U η ρ ν₀ νU νL νhat ρL inHull closestFacet gramSchmidt ℓ₁
            fuel ⟨s.i + 1, h, s.Δt, s.k, Phat, Pcheck, falsifiable⟩            -- l. 25

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
