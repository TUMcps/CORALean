import CORALean.ContDynamics.LinearSys.Theorems.ReachSetSubsetImageInputSolution
import CORALean.Global.LinProg.API

/-!
# A support bound at the end of a step, not over the whole of it

[1, Alg. 1 (upper bounds)]'s lines 10-12:
`ρ(R(t_{k+1}), ℓ) ← ρ(R₀, ℓᵀe^{Ar}) + ρ(P̂_U(t_{k+1}), ℓ)`, term for term —
`SupportBound.image` for the direction pulled back through `e^{Ar}` rather than the value
moved, `SupportBound.add` for the `+`, and
`SupportBound.mono` to cross `reachSet_subset_image_inputSolution`.

The two bounds are hypotheses, exactly as `timeIntervalBound` takes its three:
any representation that can answer `SupportBound` on `R₀` and on the particular
solution may be handed in, and neither is named here.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Tobias Ladner
-- Written:       15-September-2026
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

/-- A bound on `R₀` and on the particular solution, in every direction, give a
bound on the time-point reachable set at the end of one step — no set built,
and `reachSet` named only in the conclusion. -/
noncomputable def LinearSys.timePointBound (sys : LinearSys 𝕋 n) {T : Set ℝ} (R₀ U : S n)
    {r : ℝ} (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) (η : ℕ)
    (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    (b₀ : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportBound (construct R₀) d)
    (bP : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportBound (construct (sys.inputSolution r η U)) d)
    (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    SupportBound (sys.reachSet T R₀ U r) c :=
  (SupportBound.image (mulVecLin (exp (r • toRealMat sys.A)))
      (b₀ (c.comp (mulVecLin (exp (r • toRealMat sys.A))))) |>.add (bP c)).mono
    (sys.reachSet_subset_image_inputSolution R₀ U hr hT η hε hconv hclosed hbdd hRconv hRclosed
      hRbdd)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
