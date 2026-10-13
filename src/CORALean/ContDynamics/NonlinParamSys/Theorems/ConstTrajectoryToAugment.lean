import CORALean.ContDynamics.NonlinParamSys.Operations.Augment
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# A constant-parameter trajectory is its augmented system's

`fun t => Fin.append (x t) p` is the augmented state: its first half moves as
`x` does, its second half is the constant `p`, whose derivative is the `0` the
augmented field puts there. `hZ` is what makes the initial state land in
`construct Z₀`, as `hW` does in `TrajectoryToNonlinearSys.lean`, there being no
cartesian-product class on `ContSet` to build `Z₀` from `R₀` and `P` instead.
The derivative is taken coordinatewise, `hasDerivWithinAt_pi`, split by
`Fin.addCases` into the two halves.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m q : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinParamSys.ConstTrajectory.toAugment {sys : NonlinParamSys n m q} {T : Set ℝ}
    {R₀ : S n} {U : S m} {P : S q} {Z₀ : S (n + q)} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    {p : Vec ℝ q} (traj : sys.ConstTrajectory T R₀ U P x u p)
    (hZ : ∀ v ∈ construct R₀, ∀ w ∈ construct P, Fin.append v w ∈ construct Z₀) :
    sys.augment.Trajectory T Z₀ U (fun t => Fin.append (x t) p) u := by -- --- PROOF ---
  refine ⟨hZ (x 0) traj.init p traj.param, traj.input, fun t ht => ?_⟩
  -- the two halves of the augmented state read back as `x t` and `p`
  have hx : Fin.append (x t) p ∘ Fin.castAdd q = x t := funext (Fin.append_left (x t) p)
  have hp : Fin.append (x t) p ∘ Fin.natAdd n = p := funext (Fin.append_right (x t) p)
  simp only [NonlinParamSys.augment, hx, hp]
  -- coordinatewise: `x`'s own derivative in the first half, a constant's in the second
  have hflow := hasDerivWithinAt_pi.mp (traj.flow t ht)
  refine hasDerivWithinAt_pi.mpr fun j => Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa [Fin.append_left] using hflow i
  · simpa [Fin.append_right] using hasDerivWithinAt_const t T (p i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
