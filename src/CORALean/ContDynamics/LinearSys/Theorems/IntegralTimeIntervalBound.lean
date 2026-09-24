import CORALean.ContDynamics.LinearSys.Theorems.IntegralTimeIntervalReachSetSubsetSegmentsSum
import CORALean.ContSet.ContSet.Operations.SupportBoundSegments

/-!
# A support bound over a whole step of the exact reachable set

[1, Alg. 1]'s line 13, `LinearSys.timeIntervalBound`'s own statement carried over to
`integralTimeIntervalReachSet`: `ρ(R̂(τ_k), ℓ) ← max{ρ(H(t_k), ℓ), ρ(H(t_{k+1}), ℓ)} +
ρ(C, d_k) + ρ(P̂_U(t_{k+1}), ℓ)`, assembled the same way — `SupportBound.segments` for the
`max`, `.image` for the direction pulled back through `e^{Ar}`, `.add` twice — but crossing
`integralTimeIntervalReachSet_subset_segments_sum` in place of the `Trajectory`-layer lemma.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Tobias Ladner
-- Written:       16-September-2026
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
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Bounds on `R₀`, on the correction term and on the particular solution, in every direction,
give a bound on the exact time-interval reachable set over one step — no set built, and
`integralTimeIntervalReachSet` named only in the conclusion. -/
noncomputable def LinearSys.integralTimeIntervalBound (sys : LinearSys 𝕋 n) {T : Set ℝ}
    (R₀ U : S n) {r : ℝ} (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (h0 : (0 : Vec ℝ n) ∈ construct U)
    (b₀ : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportBound (construct R₀) d)
    (bC : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportBound (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.correctionMatrix (toRealMat sys.A) r (m + 2)) R₀)) d)
    (bP : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ,
      SupportBound (construct (sys.inputSolution r (m + 2) U)) d)
    (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    SupportBound (sys.integralTimeIntervalReachSet T R₀ U r) c :=
  (((b₀ c).segments (SupportBound.image (mulVecLin (exp (r • toRealMat sys.A)))
      (b₀ (c.comp (mulVecLin (exp (r • toRealMat sys.A))))))).add (bC c)).add (bP c) |>.mono
    (sys.integralTimeIntervalReachSet_subset_segments_sum R₀ U hr hT hε hconv hclosed hbdd hRconv
      hRclosed hRbdd h0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
