module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.HausdorffDist2ParticularSolutionLe
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemInputReach

@[expose] public section

/-!
# [1, Prop. 11] at the exact particular solution itself

`LinearSys.inputReach U Δt` *is* [1]'s `P^U(Δt) = {∫₀^{Δt}e^{A(Δt-θ)}u(θ)dθ | u(θ)∈U0}`, so this is
`Prop. 11` with its own subject in place of a squeezed stand-in. The inner half of the squeeze is
discharged here rather than assumed: `expIntegral_mem_inputReach` is [1]'s own `qP^U(Δt) ⊆ P^U(Δt)`,
holding the input at one point of `U`. What stays a hypothesis is the outer half, eq. (20)'s
soundness `P^U(Δt) ⊆ bPU(Δt)`, which [1] cites to Althoff's thesis and does not prove either.
`inputReach_subset_inputSolution` is that statement for `MatExp.inputRemainder`'s norm-based
remainder block, not for the entrywise `E(Δt,η)` eq. (20) and `Lemma 2` are built from, and the two
are incomparable (see `MatExp/Theorems/HausdorffDist2ParticularSolutionLe.lean`).

## Inputs
* `sys` – linear system
* `tk` – step start time
* `U` – input set
* `Δt` – step length
* `η` – Taylor order

## Hypotheses
* `hU` – input set bounded
* `hΔt` – step length positive
* `houter` – outer approximation encloses the input reach

## Conclusion
* the propagated Hausdorff distance is at most the particular solution error

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 11] at `P^U(Δt)` itself: eq. (25) bounds the distance between the propagated exact
particular solution and eq. (20)'s outer-approximation, given only that the latter encloses it. -/
theorem LinearSys.hausdorffDist₂_inputReach_le (sys : LinearSys 𝕋 n) (tk : ℝ) {U : S n}
    (hU : Bornology.IsBounded (construct U)) {Δt : ℝ} (hΔt : 0 < Δt) (η : ℕ)
    (houter : sys.inputReach U Δt
      ⊆ MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 Δt η) :
    hausdorffDist₂
        ((fun x => (exp (tk • toRealMat sys.A)).mulVec x) '' sys.inputReach U Δt)
        ((fun x => (exp (tk • toRealMat sys.A)).mulVec x)
          '' MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 Δt η)
      ≤ MatExp.particularSolutionError (toRealMat sys.A) tk (construct U) Δt η :=
  MatExp.hausdorffDist₂_particularSolution_le _ tk hU hΔt η
    (by rintro _ ⟨c, hc, rfl⟩; exact sys.expIntegral_mem_inputReach hΔt.le hc) houter

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
