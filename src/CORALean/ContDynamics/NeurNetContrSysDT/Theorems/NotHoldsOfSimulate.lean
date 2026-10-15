module

public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.HoldsOfReach
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.SimulateIsTrajectory

@[expose] public section

/-!
# One sampled run can falsify what reachability can only fail to prove

The contrapositive of `holds_of_reach` at `simulate_isTrajectory`: a specification
violated along one sampled run cannot have held on the reachable set either.
This is the point of simulation. An enclosure is a superset, so a specification
holding on it proves safety and one violated on it proves nothing — the
violation may sit entirely in the approximation error. A run is exact: one
point genuinely reached, so a specification it violates is genuinely violated.
Reachability and simulation answer opposite halves of the same question.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       06-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable [OfScalarPoint 𝕋 S]
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.not_holds_of_simulate (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n)
    (U_ext : S sys.nExt) {o : ℕ}
    (ho : 0 < o) (R₀ : S n) (spec : Specification ContSet) {π : Vec ℝ n → Vec ℝ sys.m}
    (hπ : sys.contr.Sound π) {v : ℕ → Vec ℝ sys.nExt} (hv : ∀ k, v k ∈ construct U_ext)
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀)
    (k : ℕ) (hbad : ¬ spec.Holds {sys.simulate π v x₀ k}) :
    ¬ spec.Holds (construct (sys.reach U_ext ⟨R₀, 0, k⟩ ⟨o, ho⟩)) :=
  fun h => hbad (sys.holds_of_reach U_ext ho R₀ spec hπ
    (fun v hv => by rw [Set.mem_singleton_iff.1 hv, Matrix.mulVec_zero])
    (sys.simulate_isTrajectory π (Set.mem_singleton 0) hv hx₀) k h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
