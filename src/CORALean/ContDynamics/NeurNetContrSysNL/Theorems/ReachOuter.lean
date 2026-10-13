import CORALean.ContDynamics.NeurNetContrSysNL.Operations.Reach
import CORALean.ContDynamics.NeurNetContrSysNL.Theorems.PeriodExtended
import CORALean.NN.Theorems.EncloseOuter

/-!
# `Alg. 2` encloses the reachable set of the closed loop

[1, Alg. 2], "Ensure: tight enclosure `R ⊇ R([0, tF])`": every run of the nonlinear plant under the
network is, at the end of each of the first `i` control cycles, in the set `reach` holds, and at
every instant of those cycles in one of the sets over a cycle. Induction on the cycle: the network's
guarantee puts the held input in `Y`, so the state and the input are in the product, the
cycle is a run of the extended system (`Trajectory.period`), and the reachability algorithm `rx`
for it, the product `cp` and the projection `pr` each satisfy the enclosure the algorithm asks of
them.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n m r : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2]: a run is, at each cycle end and in each cycle, inside the sets `reach` holds. -/
theorem NeurNetContrSysNL.reach_outer (sys : NeurNetContrSysNL S n m r)
    (cp : S n → S m → S (n + m)) (pr : S (n + m) → S n)
    (rx : S (n + m) → S (n + m) × S (n + m)) {X₀ : S n} {W : S r} {Δtc : ℝ}
    (hcp : ∀ X Y x u, x ∈ construct X → u ∈ construct Y →
      (Fin.append x u : Vec ℝ (n + m)) ∈ construct (cp X Y))
    (hpr : ∀ Z z, z ∈ construct Z → (fun k => z (Fin.castAdd m k)) ∈ construct (pr Z))
    (hrx : ∀ R z w, sys.extended.Trajectory (Set.Icc 0 Δtc) R W z w →
      z Δtc ∈ construct (rx R).1 ∧ ∀ t ∈ Set.Icc 0 Δtc, z t ∈ construct (rx R).2)
    {π : Vec ℝ n → Vec ℝ m} (hπ : sys.contr.Sound π) {H : ℕ} {x : ℝ → Vec ℝ n}
    {w : ℝ → Vec ℝ r} (traj : sys.Trajectory π Δtc H X₀ W x w) :
    ∀ i ≤ H, x ((i : ℝ) * Δtc) ∈ construct (sys.reach cp pr rx X₀ i).1 ∧
      ∀ j < i, ∀ t ∈ Set.Icc ((j : ℝ) * Δtc) (((j : ℝ) + 1) * Δtc),
        ∃ T ∈ (sys.reach cp pr rx X₀ i).2, x t ∈ construct T := by -- --- PROOF ---
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    show x (((0 : ℕ) : ℝ) * Δtc) ∈ construct X₀
    simpa using traj.init
  | succ i ih =>
    intro hi
    have hiH : i < H := Nat.lt_of_succ_le hi
    obtain ⟨hend, htubes⟩ := ih hiH.le
    -- the network puts the held input in `Y`, and the state and input in the product
    have hY := hπ.enclose_outer _ _ hend
    have hz := hcp _ _ _ _ hend hY
    obtain ⟨hnext, htube⟩ := hrx _ _ _ (traj.period i hiH _ hz)
    have hΔ : (i : ℝ) * Δtc + Δtc = ((i + 1 : ℕ) : ℝ) * Δtc := by push_cast; ring
    refine ⟨?_, fun j hj t ht => ?_⟩
    · -- the end of the cycle, projected
      have h := hpr _ _ hnext
      simp only [Fin.append_left] at h
      rw [hΔ] at h
      exact h
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · obtain ⟨T, hT, hxT⟩ := htubes j hj t ht
        exact ⟨T, List.mem_cons_of_mem _ hT, hxT⟩
      · -- the cycle itself, in its own clock
        have hs : t - (j : ℝ) * Δtc ∈ Set.Icc 0 Δtc := by
          constructor <;> nlinarith [ht.1, ht.2]
        have h := hpr _ _ (htube _ hs)
        simp only [Fin.append_left] at h
        rw [show (j : ℝ) * Δtc + (t - (j : ℝ) * Δtc) = t by ring] at h
        exact ⟨_, List.mem_cons_self .., h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
