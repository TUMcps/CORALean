module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachWith
public import CORALean.NN.Theorems.EncloseOuter
public import Mathlib.Tactic.Linarith
public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys

@[expose] public section

/-!
# `Alg. 2` encloses the reachable set of the closed loop

[1, Alg. 2], "Ensure: tight enclosure `R ⊇ R([0, tF])`": every run of the plant under the network
is, at the end of each of the first `i` control cycles, in the set `reachWith` holds, and at every
instant of those cycles in one of the sets over a cycle. Induction on the cycle: the network's
guarantee puts the held input in `Y`, so the state and the input are in the product, the cycle is a
run of the plant under that held input (`IsTrajectory.flow`), and `rx`, `cp` and `pr` each satisfy
the enclosure the algorithm asks of them. At any plant: `rx` is asked to enclose the plant's own
runs. `reachWith_timePoint_outer` is the cycle ends alone, for an `rx` with no sets over a cycle.

## Inputs
* `sys` – closed-loop system
* `cp` – Cartesian product operation
* `pr` – projection to the state
* `rx` – reachability algorithm of the extended system
* `X₀` – initial set
* `U_ext` – external input set
* `W` – disturbance set
* `π` – controller function
* `H` – number of cycles
* `x` – plant states
* `v` – external input signal
* `w` – disturbance signal

## Hypotheses
* `hcp` – the product encloses stacked pairs
* `hpr` – the projection encloses state parts
* `hrx` – the extended reachability encloses plant runs
* `hπ` – the network encloses `π`
* `traj` – closed-loop trajectory

## Conclusion
* a run lies in the algorithm's sets at each cycle end and within each cycle

## References

* [1] N. Kochdumper, C. Schilling, M. Althoff and S. Bak. "Open- and Closed-Loop Neural Network
      Verification using Polynomial Zonotopes". arXiv preprint arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet
open ContDynamics

variable {n : ℕ} {P : Type} [ContDynamics P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2]: a run is, at each cycle end and in each cycle, inside the sets `reachWith`
holds. -/
theorem NeurNetContrSys.reachWith_outer (sys : NeurNetContrSys P S n)
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
      (Fin.append (z sys.dt) u : Vec ℝ (n + _)) ∈ construct (rx R).1 ∧
        ∀ t ∈ Set.Icc 0 sys.dt, ∃ T ∈ (rx R).2, (Fin.append (z t) u : Vec ℝ (n + _)) ∈ construct T)
    {π : Vec ℝ n → Vec ℝ sys.m} (hπ : sys.contr.Encloses π) {H : ℕ}
    {x : ℝ → Vec ℝ n} {v : ℝ → Vec ℝ sys.nExt} {w : ℝ → Vec ℝ (nrOfDisturbances sys.plant)}
    (traj : sys.IsTrajectory π H X₀ U_ext W x v w) : -- --- CONCL ---
    ∀ i ≤ H, x ((i : ℝ) * sys.dt) ∈ construct (sys.reachWith cp pr rx X₀ i).1 ∧
      ∀ j < i, ∀ t ∈ Set.Icc ((j : ℝ) * sys.dt) (((j : ℝ) + 1) * sys.dt),
        ∃ T ∈ (sys.reachWith cp pr rx X₀ i).2, x t ∈ construct T := by -- --- PROOF ---
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    show x (((0 : ℕ) : ℝ) * sys.dt) ∈ construct X₀
    simpa using traj.init
  | succ i ih =>
    intro hi
    have hiH : i < H := Nat.lt_of_succ_le hi
    obtain ⟨hend, htubes⟩ := ih hiH.le
    -- the network puts the held input in `Y`, and the state and input in the product
    have hY := hπ.enclose_outer _ _ hend
    have hz := hcp _ _ _ _ hend hY
    obtain ⟨hnext, htube⟩ := hrx _ _ _ _ _ (by simpa only [add_zero] using hz) (traj.flow i hiH)
    have hΔ : (i : ℝ) * sys.dt + sys.dt = ((i + 1 : ℕ) : ℝ) * sys.dt := by push_cast; ring
    refine ⟨?_, fun j hj t ht => ?_⟩
    · -- the end of the cycle, projected
      have h := hpr _ _ hnext
      simp only [Fin.append_left] at h
      rw [hΔ] at h
      exact h
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · obtain ⟨T, hT, hxT⟩ := htubes j hj t ht
        exact ⟨T, List.mem_append_right _ hT, hxT⟩
      · -- the cycle itself, in its own clock
        have hs : t - (j : ℝ) * sys.dt ∈ Set.Icc 0 sys.dt := by
          constructor <;> nlinarith [ht.1, ht.2]
        obtain ⟨T, hT, hzT⟩ := htube _ hs
        have h := hpr _ _ hzT
        simp only [Fin.append_left] at h
        rw [show (j : ℝ) * sys.dt + (t - (j : ℝ) * sys.dt) = t by ring] at h
        exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem hT), h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
