import CORALean.ContDynamics.LinearSysDT.Operations.Canonical
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.EqOfInit
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.HoldsOfReach
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.OfFullTrajectoryIff
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

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Example.nnControlledDT (A : Mat ℝ 2 2) (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3)
    (W₂ : Mat ℝ 2 3) (b₂ : Vec ℝ 2) (dt : ℝ) : NeurNetContrSysDT (LinearSysDT ℝ 2) 𝒵 2 :=
  NeurNetContrSysDT.ofFull (LinearSysDT.canonical A) (Example.nnController W₁ b₁ W₂ b₂) dt

/-- The same plant with the network driving only its first input; the second is external. -/
noncomputable def Example.nnControlledDTExt (A : Mat ℝ 2 2) (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3)
    (W₂ : Mat ℝ 1 3) (b₂ : Vec ℝ 1) (dt : ℝ) : NeurNetContrSysDT (LinearSysDT ℝ 2) 𝒵 2 where
  plant := LinearSysDT.canonical A
  m := 1
  hm := Nat.le_succ 1
  contr := Example.nnController₁ W₁ b₁ W₂ b₂
  dt := dt


-- anonymous, since their content is that they elaborate at this representation

/-- Every discrete closed-loop run from `R₀` is inside the alternating recursion
at every step. -/
example (sys : NeurNetContrSysDT (LinearSysDT ℝ 2) 𝒵 2) (U_ext : Zonotope (Vec ℝ sys.nExt))
    (R₀ : Zonotope (Vec ℝ 2)) {o : ℕ} (ho : 0 < o)
    {π : Vec ℝ 2 → Vec ℝ sys.m} (hπ : sys.contr.Sound π)
    {x : ℕ → Vec ℝ 2} {v : ℕ → Vec ℝ sys.nExt} {w : ℕ → Vec ℝ sys.plant.r}
    (traj : sys.Trajectory π R₀ (construct U_ext) {0} x v w) (k : ℕ) :
    x k ∈ construct (sys.reach U_ext ⟨R₀, 0, k⟩ ⟨o, ho⟩) :=
  sys.reach_outer U_ext ho R₀ hπ
    (fun v hv => by rw [Set.mem_singleton_iff.1 hv, Matrix.mulVec_zero]) traj k

/-- A safe set the reached zonotope stays inside is a safe set the run stays
inside — `Specification.holds_of_outer`, reached from the loop. -/
example (sys : NeurNetContrSysDT (LinearSysDT ℝ 2) 𝒵 2) (U_ext : Zonotope (Vec ℝ sys.nExt))
    (R₀ : Zonotope (Vec ℝ 2)) {o : ℕ} (ho : 0 < o)
    (safe : Set (Vec ℝ 2)) {π : Vec ℝ 2 → Vec ℝ sys.m} (hπ : sys.contr.Sound π)
    {x : ℕ → Vec ℝ 2} {v : ℕ → Vec ℝ sys.nExt} {w : ℕ → Vec ℝ sys.plant.r}
    (traj : sys.Trajectory π R₀ (construct U_ext) {0} x v w) (k : ℕ)
    (h : (Specification.safeSet safe).Holds
      (construct (sys.reach U_ext ⟨R₀, 0, k⟩ ⟨o, ho⟩))) :
    (Specification.safeSet safe).Holds {x k} :=
  sys.holds_of_reach U_ext ho R₀ _ hπ
    (fun v hv => by rw [Set.mem_singleton_iff.1 hv, Matrix.mulVec_zero]) traj k h

/-- The discrete loop is deterministic, so a run is settled by where it started and its external
input. -/
example (sys : NeurNetContrSysDT (LinearSysDT ℝ 2) 𝒵 2) (U_ext : Set (Vec ℝ sys.nExt))
    (R₀ : Zonotope (Vec ℝ 2)) {π : Vec ℝ 2 → Vec ℝ sys.m} {x y : ℕ → Vec ℝ 2}
    {v : ℕ → Vec ℝ sys.nExt} {w₀ w₁ : ℕ → Vec ℝ sys.plant.r}
    (hx : sys.Trajectory π R₀ U_ext {0} x v w₀) (hy : sys.Trajectory π R₀ U_ext {0} y v w₁)
    (h : x 0 = y 0) : x = y :=
  hx.eq_of_init (fun v hv => by rw [Set.mem_singleton_iff.1 hv, Matrix.mulVec_zero])
    (fun v hv => by rw [Set.mem_singleton_iff.1 hv, Matrix.mulVec_zero]) hy h

/-- With the network driving every input, a run of the loop is a run of the plant under the
network's output alone, whatever the (nonempty) set of external inputs. -/
example (A : Mat ℝ 2 2) (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3) (W₂ : Mat ℝ 2 3) (b₂ : Vec ℝ 2)
    (R₀ : Zonotope (Vec ℝ 2)) (π : Vec ℝ 2 → Vec ℝ 2) (dt : ℝ)
    (U_ext : Set (Vec ℝ (Example.nnControlledDT A W₁ b₁ W₂ b₂ dt).nExt)) (hU : U_ext.Nonempty)
    (x : ℕ → Vec ℝ 2) (v : ℕ → Vec ℝ (Example.nnControlledDT A W₁ b₁ W₂ b₂ dt).nExt)
    (w : ℕ → Vec ℝ 2) :
    (Example.nnControlledDT A W₁ b₁ W₂ b₂ dt).Trajectory π R₀ U_ext {0} x v w ↔
      ContDynamicsDT.Trajectory (LinearSysDT.canonical A) (construct R₀) Set.univ {0} x
        (fun k => π (x k)) w :=
  NeurNetContrSysDT.ofFull_trajectory_iff _ _ _ hU

/-- The loop above is one of those, which is the only thing left to check: with no external input,
its `U_ext` is a set of `Vec ℝ 0`s. -/
noncomputable example (A : Mat ℝ 2 2) (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3) (W₂ : Mat ℝ 2 3)
    (b₂ : Vec ℝ 2) (R₀ : Zonotope (Vec ℝ 2)) (o k : ℕ) (ho : 0 < o) (dt : ℝ) : Zonotope (Vec ℝ 2) :=
  (Example.nnControlledDT A W₁ b₁ W₂ b₂ dt).reach (OfPoint.ofPoint 0) ⟨R₀, 0, k⟩ ⟨o, ho⟩

/-- The loop with an external input: the same reach, under an external input set `U_ext`. -/
noncomputable example (A : Mat ℝ 2 2) (W₁ : Mat ℝ 3 2) (b₁ : Vec ℝ 3) (W₂ : Mat ℝ 1 3)
    (b₂ : Vec ℝ 1) (U_ext : Zonotope (Vec ℝ 1)) (R₀ : Zonotope (Vec ℝ 2)) (o k : ℕ)
    (ho : 0 < o) (dt : ℝ) : Zonotope (Vec ℝ 2) :=
  (Example.nnControlledDTExt A W₁ b₁ W₂ b₂ dt).reach U_ext ⟨R₀, 0, k⟩ ⟨o, ho⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
