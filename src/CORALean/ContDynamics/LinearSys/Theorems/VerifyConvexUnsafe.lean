module

public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetExactEq
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachConvex
public import CORALean.Specification.Theorems.Intersection
public import CORALean.Specification.Operations.VerifyConvex
public import CORALean.Specification.Theorems.VerifyConvexFoldInv

@[expose] public section

/-!
# [1, Alg. 3 (exits), l. 12-13]: `verifyConvex`'s `violated` answer is sound

The exit `not_holds_unsafeSet_of_zero_mem_convexHull` was already available;
what was missing was a reachable set the hull-membership argument could reach
*into* — `reachSetExact_eq` is an equality, so the points `exists_convexHull…`
names are genuine reachable-trajectory points, not merely enclosed ones. The
reachable set's own convexity, needed alongside the caller-supplied convexity
of the unsafe set, is proved rather than assumed: `reachSetExact_eq` turns
it into a linear image of `R₀` summed with `inputReach`, `Convex.linear_image`
and `inputReach_convex` handling the two halves.

## Inputs
* `sys` – linear system
* `R₀` – initial set
* `Uin` – input set
* `t` – time
* `L` – convex unsafe set
* `bO` – support bound on the reach set
* `bL` – support bound on the unsafe set
* `wO` – support witness on the reach set
* `wL` – support witness on the unsafe set
* `ℓ` – direction sequence
* `fuel` – number of iterations

## Hypotheses
* `ht` – time nonnegative
* `hR₀` – initial set convex
* `hUin` – input set convex
* `hbdd` – input set bounded
* `hL` – unsafe set convex
* `h` – verification answers violated

## Conclusion
* the reach set really meets the unsafe set
## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open scoped Pointwise
variable {α : Type} [AddCommGroup α] [Module ℝ α] {O U : Set α}

/-- An `unsafe` answer came from a finite set of accumulated `O - U` points
whose hull already reaches the origin. -/
theorem aux_exists_convexHull_of_verifyConvex_eq_unsafe (bO : ∀ d : α →ₗ[ℝ] ℝ, SupportBound O d)
    (bU : ∀ d : α →ₗ[ℝ] ℝ, SupportBound U d) (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (ℓ : ℕ → α →ₗ[ℝ] ℝ) (fuel : ℕ)
    (h : verifyConvex bO bU wO wU ℓ fuel = .violated) :
    ∃ V : Set α, V ⊆ O - U ∧ (0 : α) ∈ convexHull ℝ V :=
  let inv := verifyConvexFold_inv bO bU wO wU ℓ (List.range fuel)
    (Set.empty_subset _) (fun h => by cases h) (fun h => by cases h)
  ⟨_, inv.1, inv.2.1 h⟩

end


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 3 (exits)]: a `violated` answer from `verifyConvex`, run at the
continuous-time reachable set, means it really does meet a convex unsafe set. -/
theorem LinearSys.not_holds_unsafeSet_of_verifyConvex_violated (sys : LinearSys 𝕋 n) (R₀ Uin : S n)
    {t : ℝ} (ht : 0 ≤ t) (hR₀ : Convex ℝ (construct R₀)) (hUin : Convex ℝ (construct Uin))
    (hbdd : Bornology.IsBounded (construct Uin)) {L : Set (Vec ℝ n)} (hL : Convex ℝ L)
    (bO : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportBound (sys.reachSetExact (Set.Icc 0 t) R₀ Uin t) d)
    (bL : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportBound L d)
    (wO : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportWitness (sys.reachSetExact (Set.Icc 0 t) R₀ Uin t) d)
    (wL : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportWitness L d) (ℓ : ℕ → Vec ℝ n →ₗ[ℝ] ℝ) (fuel : ℕ)
    (h : verifyConvex bO bL wO wL ℓ fuel = .violated) :
    ¬ (Specification.unsafeSet L).Holds (sys.reachSetExact (Set.Icc 0 t) R₀ Uin t) :=
  let ⟨_, hV, h0⟩ := aux_exists_convexHull_of_verifyConvex_eq_unsafe bO bL wO wL ℓ fuel h
  let hOconv : Convex ℝ (sys.reachSetExact (Set.Icc 0 t) R₀ Uin t) :=
    sys.reachSetExact_eq R₀ Uin ht hbdd ▸
      (hR₀.linear_image (mulVecLin (exp (t • toRealMat sys.A)))).add
        (sys.inputReach_convex ht hUin hbdd)
  Specification.not_holds_unsafeSet_of_zero_mem_convexHull hOconv hL hV h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
