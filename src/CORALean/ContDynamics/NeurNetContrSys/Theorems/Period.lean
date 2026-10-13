module

public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
public import CORALean.ContDynamics.LinearSys.Definitions.ClassicalTrajectory
public import CORALean.NN.Theorems.EncloseOuter
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# One control period is a linear run under the enclosed input set

The join between the two halves, and the only place they touch. On period `i` the
input is the single vector `π(x(i Δtc))`; the state at `i Δtc` is in whatever set
the previous period was enclosed by, so the network's guarantee puts that vector
in `enclose` of it — and a constant lying in a set is an admissible input of a
`LinearSys.ClassicalTrajectory` at that set.

`R` is a parameter with its membership a hypothesis, as in
`NonlinearSys.Trajectory.shift`: the caller already holds the enclosure and its
proof, and asking for them is what makes this compose into a recursion. The clock
is moved here, every statement in `LinearSys` reading `Set.Icc 0 r ⊆ T`.

**What this throws away.** `LinearSys.ClassicalTrajectory` lets `u` take any value of
`construct U` at each instant independently, so every jittering input inside the
set is admissible too, and the constancy a zero-order hold provides is dropped.
Soundness does not need it, precision does; recovering it means a constant-input
step, which `MatExp` does not yet offer.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Period `i` of a closed-loop run, in the period's own clock, is a linear run
from `R` under the constant input the controller produced at its start. -/
theorem NeurNetContrSys.Trajectory.period {sys : NeurNetContrSys 𝕋 S n} {Δtc : ℝ} {H : ℕ}
    {R₀ : S n} {π : Vec ℝ n → Vec ℝ n} (hπ : sys.contr.Sound π) {x : ℝ → Vec ℝ n}
    (traj : sys.Trajectory π Δtc H R₀ x) (i : ℕ) (hi : i < H)
    (R : S n) (hR : x ((i : ℝ) * Δtc) ∈ construct R) :
    sys.plant.ClassicalTrajectory (Set.Icc 0 Δtc) R (sys.contr.enclose R)
      (fun t => x ((i : ℝ) * Δtc + t))
      (fun _ => π (x ((i : ℝ) * Δtc))) where
  init := by simpa using hR
  input _ _ := hπ.enclose_outer R _ hR
  flow t ht := by
    have hmaps : Set.MapsTo (fun s => (i : ℝ) * Δtc + s) (Set.Icc 0 Δtc)
        (Set.Icc ((i : ℝ) * Δtc) (((i : ℝ) + 1) * Δtc)) := by
      intro s hs
      have hend : ((i : ℝ) + 1) * Δtc = (i : ℝ) * Δtc + Δtc := by ring
      exact ⟨by linarith [hs.1], by rw [hend]; linarith [hs.2]⟩
    have hg : HasDerivWithinAt (fun s : ℝ => (i : ℝ) * Δtc + s) 1 (Set.Icc 0 Δtc) t :=
      ((hasDerivAt_id t).const_add ((i : ℝ) * Δtc)).hasDerivWithinAt
    have h := (traj.flow i hi _ (hmaps ht)).scomp t hg hmaps
    simpa [Function.comp_def] using h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
