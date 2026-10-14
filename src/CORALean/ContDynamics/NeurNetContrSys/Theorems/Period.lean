module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.Extended
public import CORALean.NN.Theorems.EncloseOuter
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-!
# One control period is a run of the extended system

[1, Alg. 2], equation (4): on period `i` of a closed-loop run the state is `x`, the control input
the constant `π(x(i Δtc))`, so `z = (x, u)` with `u` constant satisfies `ż = (f(x, u, w), 0)`. In
the period's own clock this is a trajectory of `extended` on `[0, Δtc]` from any set holding
`(x(iΔtc), π(x(iΔtc)))`, with the disturbance in `W`. At every plant: the join between the
closed loop and whichever reachability algorithm the plant's extended system is reached by.

`R` is a parameter with its membership a hypothesis, as in `NonlinearSys.Trajectory.shift`: the
caller already holds the enclosure and its proof, and asking for them is what makes this compose
into a recursion. The clock is moved here, every reachability statement reading
`Set.Icc 0 Δtc`.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet
open NeurNetContrSys (Plant)

variable {n : ℕ} {P : Type} [Plant P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Period `i` of a run, with the controller's output appended to the state, is a run of the
extended system on `[0, Δtc]`. -/
theorem NeurNetContrSys.Trajectory.period {sys : NeurNetContrSys P S n}
    {π : Vec ℝ n → Vec ℝ (Plant.m sys.plant)} {Δtc : ℝ} {H : ℕ} {X₀ : S n}
    {W : S (Plant.r sys.plant)} {x : ℝ → Vec ℝ n} {w : ℝ → Vec ℝ (Plant.r sys.plant)}
    (traj : sys.Trajectory π Δtc H X₀ W x w) (i : ℕ) (hi : i < H)
    (R : S (n + Plant.m sys.plant))
    (hR : (Fin.append (x ((i : ℝ) * Δtc)) (π (x ((i : ℝ) * Δtc))) : Vec ℝ (n + _))
      ∈ construct R) :
    sys.extended.Trajectory (Set.Icc 0 Δtc) R W
      (fun t => Fin.append (x ((i : ℝ) * Δtc + t)) (π (x ((i : ℝ) * Δtc))))
      (fun t => w ((i : ℝ) * Δtc + t)) where
  init := by simpa using hR
  input t ht := by
    have hΔ : 0 ≤ Δtc := ht.1.trans ht.2
    have hH : ((i : ℝ) + 1) ≤ (H : ℝ) := by exact_mod_cast hi
    refine traj.dist _ ⟨add_nonneg (mul_nonneg (Nat.cast_nonneg i) hΔ) ht.1, ?_⟩
    nlinarith [ht.2, mul_le_mul_of_nonneg_right hH hΔ]
  flow t ht := by
    have hmaps : Set.MapsTo (fun s => (i : ℝ) * Δtc + s) (Set.Icc 0 Δtc)
        (Set.Icc ((i : ℝ) * Δtc) (((i : ℝ) + 1) * Δtc)) := by
      intro s hs
      exact ⟨by linarith [hs.1], by nlinarith [hs.2]⟩
    have hg : HasDerivWithinAt (fun s : ℝ => (i : ℝ) * Δtc + s) 1 (Set.Icc 0 Δtc) t :=
      ((hasDerivAt_id t).const_add ((i : ℝ) * Δtc)).hasDerivWithinAt
    have hx := (traj.flow i hi _ (hmaps ht)).scomp t hg hmaps
    simp only [one_smul, Function.comp_def] at hx
    -- the state coordinates move by the plant's field, the held input coordinates not at all
    rw [hasDerivWithinAt_pi]
    intro k
    refine Fin.addCases (fun e => ?_) (fun u => ?_) k
    · have hxe := (hasDerivWithinAt_pi.1 hx) e
      simpa [NeurNetContrSys.extended, Fin.append_left] using hxe
    · simpa [NeurNetContrSys.extended, Fin.append_right] using
        (hasDerivWithinAt_const t (Set.Icc 0 Δtc) (π (x ((i : ℝ) * Δtc)) u))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
