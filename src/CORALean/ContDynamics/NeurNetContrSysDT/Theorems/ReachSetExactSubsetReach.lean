module

public import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachSetExact
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter

@[expose] public section

/-!
# `reach` encloses the reachable set

`reach_outer` restated on `reachSetExact`: what it says of every run at `k`, this
says of the set of them at once, so a specification about the reachable set
meets the loop's enclosure as a single inclusion.

At every `k`, unlike `NeurNetContrSys`: one plant step and one controller
invocation coincide here, with no period between them for `reachSetExact` and
`reach` to fall silent over — the gap that theorem's docstring names does not
arise in the purely discrete loop.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable [OfScalarPoint 𝕋 S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this at every step; the guarantee attaches to the reachable set,
not to a run of it. -/
theorem NeurNetContrSysDT.reachSetExact_subset_reach (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n)
    (U_ext : S sys.nExt) {o : ℕ} (ho : 0 < o) (R₀ : S n) {π : Vec ℝ n → Vec ℝ sys.m}
    (hπ : sys.contr.Encloses π) (W : Set (Vec ℝ sys.plant.r))
    (hW : ∀ v ∈ W, toRealMat sys.plant.E *ᵥ v = 0) (k : ℕ) : -- --- STMT ---
    sys.reachSetExact π R₀ (construct U_ext) W k ⊆
      construct (sys.reach U_ext ⟨R₀, 0, k⟩ ⟨o, ho⟩) := by -- --- PROOF ---
  rintro _ ⟨x, v, w, traj, rfl⟩
  exact sys.reach_outer U_ext ho R₀ hπ hW traj k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
