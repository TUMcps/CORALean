module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachWith
public import CORALean.NN.Theorems.EncloseOuter
public import Mathlib.Tactic.Linarith
public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys

@[expose] public section

/-!
# `Alg. 2` encloses the closed loop at the cycle ends

`reachWith_outer`'s first half on its own, asking of the extended system's reachability algorithm
`rx` only the set at the end of a cycle: a plant whose reachability computes the sampled sets alone,
as `LinearSys`'s does here, has no sets over a cycle to vouch for. Induction on the cycle, the step
being a run of the plant over the cycle (`IsTrajectory.flow`) and the three enclosures `cp`, `rx`
and `pr`: [1, Alg. 2] at the cycle ends.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet
open ContDynamics

variable {n : ℕ} {P : Type} [ContDynamics P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run is, at each of the first `H` cycle ends, inside the set `reachWith` ends at. -/
theorem NeurNetContrSys.reachWith_timePoint_outer (sys : NeurNetContrSys P S n)
    (cp : S n → S sys.m → S (n + sys.m)) (pr : S (n + sys.m) → S n)
    (rx : S (n + sys.m) → S (n + sys.m) × List (S (n + sys.m)))
    {X₀ : S n} {U_ext : Set (Vec ℝ sys.nExt)} {W : Set (Vec ℝ (nrOfDisturbances sys.plant))}
    (hcp : ∀ X Y x u, x ∈ construct X → u ∈ construct Y →
      (Fin.append x u : Vec ℝ (n + _)) ∈ construct (cp X Y))
    (hpr : ∀ Z z, z ∈ construct Z → (fun k => z (Fin.castAdd _ k)) ∈ construct (pr Z))
    (hrx : ∀ R (z : ℝ → Vec ℝ n) (u : Vec ℝ sys.m) (v' : ℝ → Vec ℝ sys.nExt) w,
      (Fin.append (z 0) u : Vec ℝ (n + _)) ∈ construct R →
      ContDynamics.IsTrajectory sys.plant (Set.Icc 0 sys.dt) Set.univ (sys.inputSet {u} U_ext) W z
        (fun t => sys.input u (v' t)) w →
      (Fin.append (z sys.dt) u : Vec ℝ (n + _)) ∈ construct (rx R).1)
    {π : Vec ℝ n → Vec ℝ sys.m} (hπ : sys.contr.Sound π) {H : ℕ}
    {x : ℝ → Vec ℝ n} {v : ℝ → Vec ℝ sys.nExt} {w : ℝ → Vec ℝ (nrOfDisturbances sys.plant)}
    (traj : sys.IsTrajectory π H X₀ U_ext W x v w) :
    ∀ i ≤ H, x ((i : ℝ) * sys.dt) ∈ construct (sys.reachWith cp pr rx X₀ i).1 := by -- --- PROOF ---
  intro i
  induction i with
  | zero =>
    intro _
    show x (((0 : ℕ) : ℝ) * sys.dt) ∈ construct X₀
    simpa using traj.init
  | succ i ih =>
    intro hi
    have hiH : i < H := Nat.lt_of_succ_le hi
    have hend := ih hiH.le
    -- the network puts the held input in `Y`, and the state and input in the product
    have hz := hcp _ _ _ _ hend (hπ.enclose_outer _ _ hend)
    have h := hpr _ _ (hrx _ _ _ _ _ (by simpa only [add_zero] using hz) (traj.flow i hiH))
    simp only [Fin.append_left] at h
    rw [show (i : ℝ) * sys.dt + sys.dt = ((i + 1 : ℕ) : ℝ) * sys.dt by push_cast; ring] at h
    exact h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
