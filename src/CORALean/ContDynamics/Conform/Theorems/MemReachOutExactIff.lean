module

public import CORALean.ContDynamics.Conform.Definitions.DevSet
public import CORALean.ContDynamics.Conform.Definitions.ReachOutExact
public import CORALean.ContDynamics.Conform.Definitions.State
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# A measurement is reachable iff its deviation from the nominal run is in the deviation set

`y ∈ R(k)` from `x0 ⊕ X̃₀` under `u` exactly when `y - y_*(k) ∈ C Aᵏ X̃₀ ⊕ ⨁_{i<k} C Aⁱ W ⊕ V`:
[1, Eq. 15], `R_a(k) = R(k) - y_*(k)`, at `X̃₀ = {0}`, and [2, Eq. 8] for the discrete-time
model, which [2, Sec. 3] reaches by "performing the same steps" — an equivalence. That lets
[1, Eq. 16] replace the test-case-specific reachable sets by one deviation set. At `x0 = 0` it
is also [1, Eq. 7] with the input term's powers corrected, `A^{k-i} B u(i)` for the printed
`Aⁱ B u(i)`, and [2, Eq. 7].

## Inputs
* `sys` – plant
* `x0` – nominal initial state
* `X0` – initial uncertainty set
* `W` – disturbance set
* `V` – noise set
* `u` – inputs
* `k` – step
* `y` – output point

## Hypotheses
* none

## Conclusion
* the point is reachable iff its deviation from the nominal run is in the deviation set

## References

* [1] [S. B. Liu, B. Schürmann and M. Althoff. "Guarantees for Real Robotic Systems: Unifying Formal
      Controller Synthesis and Reachset-Conformant Identification". IEEE Transactions on Robotics,
      2023.](../../../../../references/2023/liu-tro-guarantees-real-robotic.md)
* [2] [M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". Proceedings of
      10th International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH23),
      2023.](../../../../../references/2023/althoff-arch-reachset-conformance.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n p q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The run from `x0 + x̃` is the nominal run from `x0` plus the deviation. -/
private theorem Conform.Plant.aux_state_add_dev (sys : Conform.Plant n p q) (x0 xt : Vec ℝ n)
    (u : ℕ → Vec ℝ p) (w : ℕ → Vec ℝ n) (k : ℕ) : -- --- CONCL ---
    sys.state (x0 + xt) u w k = sys.state x0 u 0 k
      + ((sys.A ^ k) *ᵥ xt + ∑ i : Fin k, (sys.A ^ (i : ℕ)) *ᵥ w (k - 1 - i)) := by -- --- PROOF ---
  induction k with
  | zero => simp [Conform.Plant.state]
  | succ k ih =>
    simp only [Conform.Plant.state, ih, Pi.zero_apply, add_zero, mulVec_add, mulVec_mulVec,
      mulVec_sum]
    -- the new disturbance is the `i = 0` term, the old ones move up one power
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mulVec, Fin.val_succ, pow_succ']
    have hidx : ∑ i : Fin k, (sys.A * sys.A ^ (i : ℕ)) *ᵥ w (k + 1 - 1 - ((i : ℕ) + 1))
        = ∑ i : Fin k, (sys.A * sys.A ^ (i : ℕ)) *ᵥ w (k - 1 - i) :=
      Finset.sum_congr rfl fun i _ => by rw [show k + 1 - 1 - ((i : ℕ) + 1) = k - 1 - i by omega]
    rw [hidx, show k + 1 - 1 - 0 = k by omega]
    abel


/-- The output of the run from `x0 + x̃`, the nominal output subtracted. -/
private theorem aux_output_sub_nominal (sys : Conform.Plant n p q) (x0 xt : Vec ℝ n)
    (u : ℕ → Vec ℝ p) (w : ℕ → Vec ℝ n) (k : ℕ) : -- --- CONCL ---
    sys.output (x0 + xt) u w k - sys.nominal x0 u k
      = (sys.C * sys.A ^ k) *ᵥ xt
        + ∑ i : Fin k, (sys.C * sys.A ^ (i : ℕ)) *ᵥ w (k - 1 - i) := by -- --- PROOF ---
  simp only [Conform.Plant.output, Conform.Plant.nominal, sys.aux_state_add_dev, mulVec_add,
    mulVec_sum, ← mulVec_mulVec]
  abel


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 15], [2, Eq. 8]: reachable exactly when the deviation from the nominal run
lies in the deviation set. -/
theorem Conform.Plant.mem_reachOutExact_iff (sys : Conform.Plant n p q) (x0 : Vec ℝ n)
    (X0 W : Set (Vec ℝ n)) (V : Set (Vec ℝ q)) (u : ℕ → Vec ℝ p) (k : ℕ)
    (y : Vec ℝ q) : -- --- CONCL ---
    y ∈ sys.reachOutExact ({x0} + X0) u W V k ↔
      y - sys.nominal x0 u k ∈ sys.devSet X0 W V k := by -- --- PROOF ---
  constructor
  · rintro ⟨_, hx0, w, hw, v, hv, rfl⟩
    rw [Set.singleton_add] at hx0
    obtain ⟨xt, hxt, rfl⟩ := hx0
    have hy : sys.output (x0 + xt) u w k + v - sys.nominal x0 u k
        = (sys.C * sys.A ^ k) *ᵥ xt
          + ∑ i : Fin k, (sys.C * sys.A ^ (i : ℕ)) *ᵥ w (k - 1 - i) + v := by
      rw [← aux_output_sub_nominal]; abel
    rw [hy]
    -- the `i`-th summand is `C Aⁱ w(k-1-i)`, a point of `C Aⁱ W`
    refine Set.add_mem_add (Set.add_mem_add ⟨xt, hxt, rfl⟩ ?_) hv
    exact (Set.mem_fintype_sum _ _).mpr
      ⟨_, fun i => ⟨w (k - 1 - i), hw _ (by omega), rfl⟩, rfl⟩
  · intro hy
    obtain ⟨_, ⟨_, ⟨xt, hxt, rfl⟩, b, hb, rfl⟩, v, hv, hyv⟩ := hy
    obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_sum _ _).mp hb
    choose w' hw' hgw using hg
    -- read the disturbances back in time order
    let w : ℕ → Vec ℝ n := fun j => if h : j < k then w' ⟨k - 1 - j, by omega⟩ else 0
    have hwi : ∀ i : Fin k, w (k - 1 - i) = w' i := fun i => by
      have hlt : k - 1 - (i : ℕ) < k := by omega
      simp only [w, dif_pos hlt]
      congr 1
      exact Fin.ext (by simp only; omega)
    refine ⟨x0 + xt, by rw [Set.singleton_add]; exact ⟨xt, hxt, rfl⟩, w, fun j hj => ?_, v, hv, ?_⟩
    · simp only [w, dif_pos hj]
      exact hw' _
    · have hsum : ∑ i : Fin k, (sys.C * sys.A ^ (i : ℕ)) *ᵥ w (k - 1 - i) = ∑ i, g i :=
        Finset.sum_congr rfl fun i _ => by rw [hwi]; exact hgw i
      have h := aux_output_sub_nominal sys x0 xt u w k
      rw [hsum] at h
      simp only at hyv
      rw [← h] at hyv
      calc y = y - sys.nominal x0 u k + sys.nominal x0 u k := by abel
        _ = _ := by rw [← hyv]; abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
