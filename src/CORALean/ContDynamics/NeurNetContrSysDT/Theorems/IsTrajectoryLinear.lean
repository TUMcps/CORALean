module

public import CORALean.ContDynamics.NeurNetContrSys.Theorems.JoinInputInj
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Map
public import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT

@[expose] public section

/-!
# At a linear plant, a run steps by `map`

A `IsTrajectory` of the closed loop at a `LinearSysDT`, its disturbance in a `W` that `E` sends to
`0`, starts in `R₀`, has its external input `v k` in `U_ext` and steps by `map`:
`A x + B [π(x); v k] + c`, the plant's own equation with `E w` gone. This is what every guarantee
at a linear plant reads a run through, as CORA's loop, which drops `E`, computes.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run with a disturbance `E` sends to `0` starts in `R₀`, has its external input in `U_ext` and
steps by `map` under it. -/
theorem NeurNetContrSysDT.IsTrajectory.linear {sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n}
    {π : Vec ℝ n → Vec ℝ sys.m} {R₀ : S n} {U_ext : Set (Vec ℝ sys.nExt)}
    {W : Set (Vec ℝ sys.plant.r)}
    (hW : ∀ v ∈ W, toRealMat sys.plant.E *ᵥ v = 0) {x : ℕ → Vec ℝ n} {v : ℕ → Vec ℝ sys.nExt}
    {w : ℕ → Vec ℝ sys.plant.r} (traj : sys.IsTrajectory π R₀ U_ext W x v w) : -- --- CONCL ---
    x 0 ∈ construct R₀ ∧ (∀ k, v k ∈ U_ext) ∧
      ∀ k, x (k + 1) = sys.map π (x k) (v k) := by -- --- PROOF ---
  obtain ⟨vv, y, tr⟩ := traj
  refine ⟨tr.init, fun k => ?_, fun k => ?_⟩
  · -- the external input is the part of the plant's input after the network's
    obtain ⟨a', _, e, he, heq⟩ := tr.input k
    rw [(joinInput_inj sys.hm heq).2]
    exact he
  · -- the plant's step, its disturbance term `0`
    rw [tr.step k, hW _ (tr.dist k), add_zero]
    rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
