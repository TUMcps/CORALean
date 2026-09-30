import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetConfinementOfSubset
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetSubsetRelinTimeInterval

/-!
# The reachable set inside a computed one, with nothing left to assume

The two halves composed: `reachSet_confinement_of_subset` discharges the
confinement `reachSet_subset_relinTimeInterval` asks for, at the same order
`q + 2`, so what remains are properties of each step's `linInput`, a bound `M`
on the field over each certified region, and the ball check `hsub` — every one
of them a condition on `R₀`, `U`, `steps` and the sets `relinReach` computes.

This is the shape `LinearSys.reachSet_subset_timeInterval_inputSolution` has in
the linear case, and it is as far as the nonlinear one gets: `M` and `ρ` are
extra data there is no linear counterpart to, since a linear field needs no
region to be conservative over.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Plus Mtimes OfInterval

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reachable set over step `i` lies in one computed set, on hypotheses a
caller can check against the computed sets alone: no trajectory, no input
signal and no confinement assumption anywhere. -/
theorem NonlinearSys.reachSet_subset_relinTimeInterval_of_subset (sys : NonlinearSys n m)
    {T : Set ℝ} (R₀ : S n) (U : S m) {steps : ℕ → sys.LinStep U} {Δt : ℝ} {N : ℕ}
    {M ρ : ℝ} (hΔt : 0 < Δt) (hT : Set.Icc 0 ((N : ℝ) * Δt) ⊆ T)
    (q : ℕ) (hε : ∀ i < N, ‖Δt • (steps i).A‖ / (((q + 2 : ℕ) : ℝ) + 2) < 1)
    (hconv : ∀ i < N, Convex ℝ (construct (steps i).linInput))
    (hclosed : ∀ i < N, IsClosed (construct (steps i).linInput))
    (hbdd : ∀ i < N, Bornology.IsBounded (construct (steps i).linInput))
    (h0 : ∀ i < N, (0 : Vec ℝ n) ∈ construct (steps i).linInput)
    (hRconv : ∀ i < N, Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt (q + 2)) (steps i).linInput)))
    (hRclosed : ∀ i < N, IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt (q + 2)) (steps i).linInput)))
    (hRbdd : ∀ i < N, Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt (q + 2)) (steps i).linInput)))
    (hM₀ : 0 ≤ M) (hM : ∀ i < N, ∀ y ∈ (steps i).R, ∀ v ∈ construct U, ‖sys.f y v‖ ≤ M)
    (hρ : M * Δt < ρ) {o : ℕ} (ho : 0 < o)
    (hsub : ∀ i < N, ∀ y ∈ construct (sys.relinReach ⟨R₀, 0, i⟩ ⟨Δt, o, ho⟩ steps (fun i =>
      (NonlinearSys.linearize (steps i).A).inputSolution Δt (q + 2)
        (steps i).linInput)), Metric.closedBall y ρ ⊆ (steps i).R)
    (i : ℕ) (hi : i < N) {t : ℝ} (ht : t ∈ Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt)) :
    sys.reachSet T R₀ U t ⊆ construct (sys.relinTimeInterval o ho Δt (q + 2) steps
      (fun i => (NonlinearSys.linearize (steps i).A).inputSolution Δt (q + 2)
        (steps i).linInput) R₀ i) :=
  sys.reachSet_subset_relinTimeInterval R₀ U hΔt hT
    (sys.reachSet_confinement_of_subset R₀ U hΔt hT (q + 2) hε hconv hclosed hbdd
      hRconv hRclosed hRbdd hM₀ hM hρ ho hsub)
    q hε hconv hclosed hbdd h0 hRconv hRclosed hRbdd ho i hi ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
