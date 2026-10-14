import CORALean.ContDynamics.LinearSysDT.Operations.Canonical
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.EqOfInit
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.HoldsOfReach
import CORALean.Examples.NeurNetControl

/-!
# A discrete-time plant with a ReLU controller, verified end to end

`NeurNetControl`'s controller (affine, ReLU, affine) in feedback with a discrete-time plant,
`x(k+1) = A x(k) + u(k)` with `u = π(x)`, at `Zonotope`. The alternating recursion of
`reach` — controller on the reached set, then the plant step — encloses every closed-loop run
at every step; a safe set the reached zonotope stays inside is a safe set the run stays
inside; and the loop is deterministic, so a run is settled by where it started. Compiled at
an abstract system, for the reason `NeurNetControl` gives.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Example.nnControlledDT (A : Mat ℝ 2 2) (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3)
    (W₂ : Mat ℝ 2 3) (b₂ : Vec ℝ 2) : NeurNetContrSysDT ℝ 𝒵 2 where
  plant := LinearSysDT.canonical A
  contr := Example.nnController W₁ b₁ W₂ b₂


-- anonymous, since their content is that they elaborate at this representation

/-- Every discrete closed-loop run from `R₀` is inside the alternating recursion
at every step. -/
example (sys : NeurNetContrSysDT ℝ 𝒵 2) (R₀ : Zonotope (Vec ℝ 2)) {o : ℕ} (ho : 0 < o)
    {π : Vec ℝ 2 → Vec ℝ sys.plant.m} (hπ : sys.contr.Sound π)
    {x : ℕ → Vec ℝ 2} (traj : sys.Trajectory π R₀ x) (k : ℕ) :
    x k ∈ construct (sys.reach ⟨R₀, 0, k⟩ ⟨o, ho⟩) :=
  sys.reach_outer ho R₀ hπ traj k

/-- A safe set the reached zonotope stays inside is a safe set the run stays
inside — `Specification.holds_of_outer`, reached from the loop. -/
example (sys : NeurNetContrSysDT ℝ 𝒵 2) (R₀ : Zonotope (Vec ℝ 2)) {o : ℕ} (ho : 0 < o)
    (safe : Set (Vec ℝ 2)) {π : Vec ℝ 2 → Vec ℝ sys.plant.m} (hπ : sys.contr.Sound π)
    {x : ℕ → Vec ℝ 2} (traj : sys.Trajectory π R₀ x) (k : ℕ)
    (h : (Specification.safeSet safe).Holds (construct (sys.reach ⟨R₀, 0, k⟩ ⟨o, ho⟩))) :
    (Specification.safeSet safe).Holds {x k} :=
  sys.holds_of_reach ho R₀ _ hπ traj k h

/-- The discrete loop is deterministic, so a run is settled by where it
started. -/
example (sys : NeurNetContrSysDT ℝ 𝒵 2) (R₀ : Zonotope (Vec ℝ 2))
    {π : Vec ℝ 2 → Vec ℝ sys.plant.m} {x y : ℕ → Vec ℝ 2}
    (hx : sys.Trajectory π R₀ x) (hy : sys.Trajectory π R₀ y) (h : x 0 = y 0) : x = y :=
  hx.eq_of_init hy h

/-- The loop above is one of those, which is the only thing left to check. -/
noncomputable example (A : Mat ℝ 2 2) (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3) (W₂ : Mat ℝ 2 3)
    (b₂ : Vec ℝ 2) (R₀ : Zonotope (Vec ℝ 2)) (o k : ℕ) (ho : 0 < o) : Zonotope (Vec ℝ 2) :=
  (Example.nnControlledDT A W₁ b₁ W₂ b₂).reach ⟨R₀, 0, k⟩ ⟨o, ho⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
