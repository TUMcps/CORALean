module

public import CORALean.ContDynamics.LinearARX.Definitions.ReachWindowExact
public import CORALean.ContDynamics.LinearARX.Theorems.StackEqTvp
public import CORALean.ContDynamics.LinearARX.Theorems.StackSimulateZero
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

@[expose] public section

/-!
# The reachable windows as one Minkowski sum

[1, Eq. 12]: `Ỹ(k:k₊) = Ã(k) ỹ_init ⊕ ⊕_{i=0}^{k₊} B̃ᵢ(k) Ũ(k₊ - i)`, exactly, read as the
joint window set. [1, Thm. 1] writes each window with every input once, so the sum over
independent inputs is all of them: one way is `stack_eq_tvp`, the other builds the input
signal from the summands and runs `simulate` on it. Every `Ũ(i)` nonempty, so that the
inputs past `k₊`, which no window up to here reads, can be chosen at all.

## Inputs
* `sys` – ARX system
* `y₀` – measured first output window
* `U` – input sets per step
* `k` – step

## Hypotheses
* `hU` – input sets nonempty

## Conclusion
* the reachable windows are one Minkowski sum

## References

* [1] [L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". 2023 62nd IEEE Conference
      on Decision and Control (CDC), 2023.](../../../../../references/2023/luetzow-cdc-armax.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar Pointwise

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.reachWindowExact_eq (sys : LinearARX 𝕋 dy du p) (y₀ : Vec ℝ (p * dy))
    {U : ℕ → Set (Vec ℝ du)} (hU : ∀ i, (U i).Nonempty) (k : ℕ) : -- --- CONCL ---
    sys.reachWindowExact y₀ U k = {sys.Aext ^ k *ᵥ y₀}
      + ∑ i ∈ Finset.range (k + p),
        (sys.Btilde k i *ᵥ ·) '' U (k + p - 1 - i) := by -- --- PROOF ---
  ext w
  constructor
  · rintro ⟨y, u, h₀, hu, hy, rfl⟩
    rw [sys.stack_eq_tvp hy k, h₀]
    refine Set.add_mem_add rfl ((Set.mem_finsetSum _ _ _).mpr ⟨fun i => sys.Btilde k i *ᵥ
      u (k + p - 1 - i), fun _ => ⟨_, hu _, rfl⟩, rfl⟩)
  · rintro ⟨a, ha, t, ht, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetSum _ _ _).mp ht
    -- one input per summand, read back at the time it enters
    have hv : ∀ i, ∃ v : Vec ℝ du, i ∈ Finset.range (k + p) →
        v ∈ U (k + p - 1 - i) ∧ sys.Btilde k i *ᵥ v = g i := by
      intro i
      by_cases hi : i ∈ Finset.range (k + p)
      · obtain ⟨v, hv, hvg⟩ := hg hi
        exact ⟨v, fun _ => ⟨hv, hvg⟩⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose v hv using hv
    let u : ℕ → Vec ℝ du := fun m => if m < k + p then v (k + p - 1 - m) else (hU m).some
    have hu : ∀ m, u m ∈ U m := by
      intro m
      by_cases hm : m < k + p
      · have h := (hv (k + p - 1 - m) (Finset.mem_range.mpr (by omega))).1
        rw [show k + p - 1 - (k + p - 1 - m) = m by omega] at h
        simp only [u, if_pos hm]
        exact h
      · simp only [u, if_neg hm]
        exact (hU m).some_mem
    -- the run that signal drives reaches the window
    have hy : ∀ k, p ≤ k → sys.simulate y₀ u k
        = ∑ i : Fin p, toRealMat (sys.Abar i) *ᵥ sys.simulate y₀ u (k - (i + 1))
          + ∑ j : Fin (p + 1), toRealMat (sys.Bbar j) *ᵥ u (k - j) := fun k hk => by
      rw [LinearARX.simulate, dif_neg (not_lt.mpr hk)]
    refine ⟨sys.simulate y₀ u, u, sys.stack_simulate_zero y₀ u, hu, hy, ?_⟩
    rw [sys.stack_eq_tvp hy k, sys.stack_simulate_zero]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have hlt : k + p - 1 - i < k + p := by omega
    simp only [u, if_pos hlt, show k + p - 1 - (k + p - 1 - i) = i by omega]
    exact ((hv i hi).2).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
