module

public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.HoldsOfReach
public import CORALean.Specification.Theorems.CheckSound

@[expose] public section

/-!
# A passed check on the closed loop's reachable set holds along every trajectory

`holds_of_reach` with its hypothesis discharged by running `Specification.check` on the
set `reach` computed, through the pair's `Contains` or `IsDisjoint`: a `true`, found by
evaluation, is the specification on the exact state, with nothing left to prove by hand.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       24-September-2026
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

theorem NeurNetContrSysDT.holds_of_check [Contains ContSet (S n)] [IsDisjoint ContSet (S n)]
    (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n) (U_ext : S sys.nExt) {o : ℕ} (ho : 0 < o)
    (R₀ : S n) (spec : Specification ContSet) {π : Vec ℝ n → Vec ℝ sys.m}
    (hπ : sys.contr.Encloses π) {W : Set (Vec ℝ sys.plant.r)}
    (hW : ∀ v ∈ W, toRealMat sys.plant.E *ᵥ v = 0) {x : ℕ → Vec ℝ n} {v : ℕ → Vec ℝ sys.nExt}
    {w : ℕ → Vec ℝ sys.plant.r} (traj : sys.IsTrajectory π R₀ (construct U_ext) W x v w)
    (k : ℕ) : -- --- CONCL ---
    spec.check (sys.reach U_ext ⟨R₀, 0, k⟩ ⟨o, ho⟩) → (spec.Holds {x k}) :=
  fun h => sys.holds_of_reach U_ext ho R₀ spec hπ hW traj k (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
