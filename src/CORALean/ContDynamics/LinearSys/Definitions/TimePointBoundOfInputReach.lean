module

public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetEq
public import CORALean.Global.SupportFunction.Composition

@[expose] public section

/-!
# A support bound on the reachable set, term for term

[1, Alg. 1 (upper bounds)]'s lines 10-12 from a bound on `inputReach` itself:
`ρ(R₀, ℓᵀe^{tA}) + ρ(P, ℓ)`, assembled by `SupportBound.image` and `.add` and
carried across `reachSet_eq`, an equality rather than an enclosure, so no `mono`
is needed. `timePointBound` is the same bound from one on `inputSolution`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A bound on `R₀` and on `sys.inputReach U t`, in every direction, give a
bound on the time-point reachable set at `t` — no set built, and
`reachSet` named only in the conclusion. -/
noncomputable def LinearSys.timePointBoundOfInputReach (sys : LinearSys 𝕋 n) (R₀ U : S n)
    {t : ℝ} (ht : 0 ≤ t) (hU : Bornology.IsBounded (construct U))
    (b₀ : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportBound (construct R₀) d)
    (bP : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportBound (sys.inputReach U t) d)
    (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    SupportBound (sys.reachSet (Set.Icc 0 t) R₀ U t) c :=
  sys.reachSet_eq R₀ U ht hU ▸
    (SupportBound.image (mulVecLin (exp (t • toRealMat sys.A)))
      (b₀ (c.comp (mulVecLin (exp (t • toRealMat sys.A)))))).add (bP c)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
