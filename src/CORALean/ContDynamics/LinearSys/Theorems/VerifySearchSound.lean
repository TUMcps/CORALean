module

public import CORALean.ContDynamics.LinearSys.Operations.VerifySearch
public import CORALean.ContDynamics.LinearSys.Theorems.VerifySearchLoopSound

@[expose] public section

/-!
# [1, Alg. 3 (search)]: `safe` and `unsafe` are right

`verifySearch` starts the loop at line 1: `Δt = t` in one step, `P̌ = ∅`. Its two exits are
sound whatever the oracles do, as `verifySearchLoop_sound` says of any state in which the
invariants hold, and at line 1 they do: `1·t = t`, `P̌` has no vertex, and `Δt = t` is small
enough for `Alg. 1` when `‖tA‖ < η + 2`. Not claimed: that the loop ever reaches an exit.

## Inputs
* `sys` – linear system
* `X₀` – initial set
* `U` – input set
* `t` – time
* `m` – Taylor order offset
* `ρ` – support function oracle
* `ν₀` – support vector map of the initial set
* `νU` – support vector map of the input set
* `νL` – support vector map of the specification set
* `L` – specification set
* `ρL` – support function of the specification set
* `νhat` – support vector map of the outer approximation
* `inHull` – origin-in-hull test
* `closestFacet` – closest facet finder
* `gramSchmidt` – orthogonal direction finder
* `fuel` – number of iterations

## Hypotheses
* `hX₀` – initial set convex
* `hUconv` – input set convex
* `ht` – time positive
* `hε` – scaled norm small enough for the Taylor order
* `hρ` – oracle bounds the support function of every set
* `hν₀` – initial support vectors lie in the initial set
* `hνU` – input support vectors lie in the input set
* `hL` – specification set convex
* `hνL` – specification support vectors lie in the set
* `hρL` – specification support function bounds the set
* `hhull` – hull test is sound

## Conclusion
* a safe answer means the sets are disjoint and a violated one that they meet

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 3 (search)]: `safe` means `R(t) ∩ L = ∅` and `violated` means `R(t) ∩ L ≠ ∅`, for
any support-function and support-vector oracles that are what they are named. -/
theorem LinearSys.verifySearch_sound
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]
    (sys : LinearSys 𝕋 n) (X₀ U : S n) (hX₀ : Convex ℝ (construct X₀))
    (hUconv : Convex ℝ (construct U)) {t : ℝ} (ht : 0 < t) {m : ℕ}
    (hε : ‖t • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {ρ : S n → (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ}
    (hρ : ∀ X : S n, ∀ x ∈ construct X, ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, d x ≤ ρ X d)
    {ν₀ νU νL : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n} (hν₀ : ∀ d, ν₀ d ∈ construct X₀)
    (hνU : ∀ d, νU d ∈ construct U) {L : Set (Vec ℝ n)} (hL : Convex ℝ L)
    (hνL : ∀ d, νL d ∈ L) {ρL : (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ} (hρL : ∀ d, ∀ y ∈ L, d y ≤ ρL d)
    {νhat : ℝ → (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n} {inHull : List (Vec ℝ n) → Bool}
    (hhull : ∀ V, inHull V = true → (0 : Vec ℝ n) ∈ convexHull ℝ {v | v ∈ V})
    (closestFacet : List (Vec ℝ n) → (Vec ℝ n →ₗ[ℝ] ℝ) × List ℕ)
    (gramSchmidt : List (Vec ℝ n) → (Vec ℝ n →ₗ[ℝ] ℝ)) (fuel : ℕ) :
    (sys.verifySearch X₀ U t (m + 2) ρ ν₀ νU νL νhat ρL inHull closestFacet gramSchmidt fuel
        = .safe → Disjoint (sys.reachSetExact (Set.Icc 0 t) X₀ U t) L) ∧
    (sys.verifySearch X₀ U t (m + 2) ρ ν₀ νU νL νhat ρL inHull closestFacet gramSchmidt fuel
        = .violated → ¬ Disjoint (sys.reachSetExact (Set.Icc 0 t) X₀ U t) L) :=
  sys.verifySearchLoop_sound X₀ U hX₀ hUconv hρ hν₀ hνU hL hνL hρL hhull closestFacet
    gramSchmidt _ fuel _ ht (by simp) hε (fun v hv => by simp at hv)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
