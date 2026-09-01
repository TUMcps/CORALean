import CORALean.Real.ContDynamics.LinearSys.LinearSys
import CORALean.Real.ContDynamics.LinearSysDT.API
import CORALean.Real.MatSet.API

/-!
# Continuous-time linear systems: sampling

Sampling every `Δt` turns the system into the discrete-time one whose matrix is
`e^{AΔt}`, so reachability at the sample times is `LinearSysDT`'s and needs
nothing new. What the inputs contribute over a step is `stepInput`, an integral
rather than a set: enclosing it is the representation's job, not this file's.

The result is a `LinearSysDT ℝ`, never `LinearSysDT 𝕋`: `e^{AΔt}` is
transcendental, so no machine scalar holds it. A float layer has to carry an
interval matrix here instead.

`exp` needs a norm on `Mat`, which is a choice rather than an instance, so every
file reasoning about these definitions must make the same one — the `l∞`
operator norm — or the terms will not match.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) n] [OuterContSet S ℝ]

/-- The system a step of `Δt` leaves behind. -/
noncomputable def LinearSys.discretize (sys : LinearSys 𝕋 n) (Δt : ℝ) : LinearSysDT ℝ n :=
  ⟨exp (Δt • toRealMat sys.A)⟩

/-- Everything the input contributed over step `k`, propagated to its end. -/
noncomputable def LinearSys.stepInput (sys : LinearSys 𝕋 n) (u : ℝ → Vec ℝ n) (Δt : ℝ)
    (k : ℕ) : Vec ℝ n :=
  ∫ s in (k * Δt)..((k + 1) * Δt), exp (((k + 1) * Δt - s) • toRealMat sys.A) *ᵥ u s

/-- The matrix order `i` contributes to the input solution: `Aⁱ r^{i+1}/(i+1)!`,
the `i`-th term of the exponential integrated once over the step. -/
noncomputable def LinearSys.inputTerm (sys : LinearSys 𝕋 n) (r : ℝ) (i : ℕ) : Mat ℝ n n :=
  (r ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) • (toRealMat sys.A) ^ i

/-- The exact orders of the input solution, `0` through `η`, summed. Recursive
rather than a fold over `Finset`, so that `plus` — which is only an enclosure,
not an associative operation — never has to be reassociated, and the guarantee
is one induction. -/
noncomputable def LinearSys.inputTaylorSum (sys : LinearSys 𝕋 n) (r : ℝ) (U : S n) : ℕ → S n
  | 0 => Mtimes.mtimes (sys.inputTerm r 0) U
  | i + 1 => OuterContSet.plus (sys.inputTaylorSum r U i)
      (Mtimes.mtimes (sys.inputTerm r (i + 1)) U)

/-- Althoff's Thm. 3.1: everything the input can contribute over one step,
`⊕ᵢ Aⁱr^{i+1}/(i+1)! U ⊕ E(r)·r·U`. The orders up to `η` exactly, and everything
past `η` in the same remainder that bounds the exponential. -/
noncomputable def LinearSys.inputSolution [Mtimes IntervalMat S]
    (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ) (U : S n) : S n :=
  OuterContSet.plus (sys.inputTaylorSum r U η)
    (Mtimes.mtimes (IntervalMat.inputRemainder (toRealMat sys.A) r η) U)

/-- CORA's `CH(X₀, e^{Ar}X₀) ⊕ F X₀`, over a whole step rather than at its ends:
the segment from the set to its image, widened by what the curvature of the flow
adds. `linComb` rather than a convex hull, so a non-convex representation keeps
its shape. -/
noncomputable def LinearSys.timeIntervalStep [Mtimes IntervalMat S]
    (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ) (X₀ : S n) : S n :=
  OuterContSet.plus
    (OuterContSet.linComb X₀ (Mtimes.mtimes (exp (r • toRealMat sys.A)) X₀))
    (Mtimes.mtimes (IntervalMat.correctionMatrix (toRealMat sys.A) r η) X₀)

end CORALean.Real
