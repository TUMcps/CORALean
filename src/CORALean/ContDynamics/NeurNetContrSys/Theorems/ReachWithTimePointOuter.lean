module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachWith
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.Period

@[expose] public section

/-!
# `Alg. 2` encloses the closed loop at the cycle ends

`reachWith_outer`'s first half on its own, asking of the extended system's reachability
algorithm `rx` only the set at the end of a cycle: a plant whose reachability computes the
sampled sets alone, as `LinearSys`'s does here, has no sets over a cycle to vouch for. Induction
on the cycle, the step being `Trajectory.period` and the three enclosures `cp`, `rx` and `pr`:
[1, Alg. 2] at the cycle ends.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet
open NeurNetContrSys (Plant)

variable {n : ℕ} {P : Type} [Plant P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run is, at each of the first `H` cycle ends, inside the set `reachWith` ends at. -/
theorem NeurNetContrSys.reachWith_timePoint_outer (sys : NeurNetContrSys P S n)
    (cp : S n → S (Plant.m sys.plant) → S (n + Plant.m sys.plant))
    (pr : S (n + Plant.m sys.plant) → S n)
    (rx : S (n + Plant.m sys.plant) → S (n + Plant.m sys.plant) × List (S (n + Plant.m sys.plant)))
    {X₀ : S n} {W : S (Plant.r sys.plant)} {Δtc : ℝ}
    (hcp : ∀ X Y x u, x ∈ construct X → u ∈ construct Y →
      (Fin.append x u : Vec ℝ (n + _)) ∈ construct (cp X Y))
    (hpr : ∀ Z z, z ∈ construct Z → (fun k => z (Fin.castAdd _ k)) ∈ construct (pr Z))
    (hrx : ∀ R z w, sys.extended.Trajectory (Set.Icc 0 Δtc) R W z w →
      z Δtc ∈ construct (rx R).1)
    {π : Vec ℝ n → Vec ℝ (Plant.m sys.plant)} (hπ : sys.contr.Sound π) {H : ℕ}
    {x : ℝ → Vec ℝ n} {w : ℝ → Vec ℝ (Plant.r sys.plant)}
    (traj : sys.Trajectory π Δtc H X₀ W x w) :
    ∀ i ≤ H, x ((i : ℝ) * Δtc) ∈ construct (sys.reachWith cp pr rx X₀ i).1 := by -- --- PROOF ---
  intro i
  induction i with
  | zero =>
    intro _
    show x (((0 : ℕ) : ℝ) * Δtc) ∈ construct X₀
    simpa using traj.init
  | succ i ih =>
    intro hi
    have hiH : i < H := Nat.lt_of_succ_le hi
    have hend := ih hiH.le
    -- the network puts the held input in `Y`, and the state and input in the product
    have hz := hcp _ _ _ _ hend (hπ.enclose_outer _ _ hend)
    have h := hpr _ _ (hrx _ _ _ (traj.period i hiH _ hz))
    simp only [Fin.append_left] at h
    rw [show (i : ℝ) * Δtc + Δtc = ((i + 1 : ℕ) : ℝ) * Δtc by push_cast; ring] at h
    exact h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
