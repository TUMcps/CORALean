module

public import CORALean.HybridDynamics.Operations.ReachGuard
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

/-!
# [1, Alg. 5] is sound, and so [2, Alg. 1]

Given the guarantees its operators owe — `reach k` holds every state of the stay at
`t ∈ [kr, (k+1)r]`, the conversions enclose, `isEmpty` answers `true` only for `∅`, and
`intersectionTimes` brackets every position that meets the guard — every state of a stay in
`ℓ` before `t^end_inv` lies in a piece of `R^H([0, t^end_inv])`, and in `R_j` too where it is
in the guard of `e`. A loop that stopped before the horizon `t_f = N r` did so because a piece
was empty, and then the stay ended before `t^end_inv`: the invariant has been left.

`reach` is the thesis's continuous reachable set, `LinearSys.reachBox_outer` ([1, Alg. 2])
being one way to meet its obligation at linear location dynamics.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
* [2] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [∀ n, ContSet (G n) (Vec ℝ n)] in
/-- The loop moves `k` forward, and stops before `N` only at a piece `isEmpty` rejects. -/
theorem aux_reachGuard_while (RH : ℕ → G n) (isEmpty : G n → Bool) (N : ℕ) :
    let step := fun k => if !isEmpty (RH k) && decide (k < N) then k + 1 else k
    ∀ m k, N ≤ k + m → k ≤ step^[m] k ∧
      (step^[m] k < N → isEmpty (RH (step^[m] k)) = true) := by -- --- PROOF ---
  intro step m
  induction m with
  | zero =>
    intro k hk
    exact ⟨le_rfl, fun h => absurd h (by simp only [Function.iterate_zero, id]; omega)⟩
  | succ m ih =>
    intro k hk
    by_cases hc : (!isEmpty (RH k) && decide (k < N)) = true
    · -- the loop body runs once more, from `k + 1`
      have h := ih (k + 1) (by omega)
      have hs : step k = k + 1 := if_pos hc
      rw [Function.iterate_succ_apply, hs]
      exact ⟨by omega, h.2⟩
    · -- the test fails: `k` is a fixed point of every further pass
      have hs : step k = k := if_neg hc
      rw [Function.iterate_succ_apply, hs, Function.iterate_fixed hs]
      refine ⟨le_rfl, fun hkN => ?_⟩
      cases h : isEmpty (RH k)
      · exact absurd (by simp [h, hkN]) hc
      · rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 5] encloses a stay before `t^end_inv` and where it meets the guard, and a loop
stopped before `t_f = N r` means the stay ended before `t^end_inv`. -/
theorem Location.Trajectory.reachGuard_outer [∀ n, Intersection (G n) (Vec ℝ n)]
    {ℓ : Location S G L 𝕋 n} {τ : ℝ} {x u : ℝ → Vec ℝ n} (traj : ℓ.Trajectory τ x u)
    (e : Transition G L 𝕋 n) {r : ℝ} (hr : 0 < r) (N : ℕ) {reach : ℕ → S n}
    (hreach : ∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc (k * r) ((k + 1) * r) → t ∈ Set.Icc 0 τ →
      x t ∈ construct (reach k))
    {halfspaceConv : S n → G n} (hH : ∀ R, construct R ⊆ construct (halfspaceConv R))
    {isEmpty : G n → Bool} (hE : ∀ P, isEmpty P = true → construct P = ∅)
    {intersectionTimes : List (G n) → G n → ℕ × ℕ}
    (hT : ∀ (Ps : List (G n)) (g : G n) (i : ℕ) (hi : i < Ps.length),
      (construct Ps[i] ∩ construct g).Nonempty →
        (intersectionTimes Ps g).1 ≤ i ∧ i ≤ (intersectionTimes Ps g).2)
    {generatorConv : List (G n) → S n}
    (hG : ∀ Ps, ∀ P ∈ Ps, construct P ⊆ construct (generatorConv Ps)) :
    let out := ℓ.reachGuard e reach halfspaceConv isEmpty intersectionTimes generatorConv N
    (∀ t ∈ Set.Icc 0 τ, t < out.1.length * r → (∃ P ∈ out.1, x t ∈ construct P) ∧
      (x t ∈ construct e.guard → x t ∈ construct out.2)) ∧
    (out.1.length + 1 < N → τ < out.1.length * r) := by -- --- PROOF ---
  intro out
  set RH : ℕ → G n := fun k => Intersection.intersection (halfspaceConv (reach (k - 1))) ℓ.inv
  set K := (fun k => if !isEmpty (RH k) && decide (k < N) then k + 1 else k)^[N] 1
  have hK := aux_reachGuard_while RH isEmpty N N 1 (by omega)
  have hlen : out.1.length = K - 1 := by simp [out, Location.reachGuard, RH, K]
  -- every stay state at `t ∈ [(i-1)r, ir]` is in the piece `R^H([(i-1)r, ir])`
  have hmem : ∀ (i : ℕ) (t : ℝ), t ∈ Set.Icc (i * r) ((i + 1) * r) → t ∈ Set.Icc 0 τ →
      x t ∈ construct (RH (i + 1)) := by
    intro i t hi ht
    refine Intersection.intersection_outer _ _ ⟨hH _ ?_, traj.invariant t ht⟩
    simpa using hreach i t hi ht
  refine ⟨fun t ht htK => ?_, fun hN => ?_⟩
  · -- the piece is the one at `i = ⌊t / r⌋`
    set i := ⌊t / r⌋₊
    have hti : t ∈ Set.Icc (i * r) ((i + 1) * r) :=
      ⟨(le_div_iff₀ hr).1 (Nat.floor_le (div_nonneg ht.1 hr.le)),
        ((div_lt_iff₀ hr).1 (Nat.lt_floor_add_one (t / r))).le⟩
    have hiK : i < K - 1 := by
      rw [hlen] at htK
      exact_mod_cast lt_of_mul_lt_mul_right (lt_of_le_of_lt hti.1 htK) hr.le
    have hx := hmem i t hti ht
    refine ⟨⟨RH (i + 1), ?_, hx⟩, fun hg => ?_⟩
    · simp only [out, Location.reachGuard, List.mem_map, List.mem_range]
      exact ⟨i, hiK, rfl⟩
    · set Ps := (List.range (K - 1)).map fun j => RH (j + 1)
      have hi : i < Ps.length := by simpa [Ps] using hiK
      have htg := hT Ps e.guard i hi ⟨x t, by simpa [Ps] using hx, hg⟩
      refine hG _ (Intersection.intersection (RH (i + 1)) e.guard) ?_
        (Intersection.intersection_outer _ _ ⟨hx, hg⟩)
      simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨i, ⟨hiK, htg⟩, rfl⟩
  · -- stopped before the horizon: `R^H([(K-1)r, Kr])` is empty, so the stay ended first
    rw [hlen] at hN ⊢
    have hempty := hE _ (hK.2 (by omega))
    by_contra hτ
    replace hτ := not_lt.1 hτ
    have hK1 : ((K - 1 : ℕ) : ℝ) + 1 = K := by
      have : 1 ≤ K := hK.1
      push_cast [this]; ring
    have hx := hmem (K - 1) ((K - 1 : ℕ) * r) ⟨le_rfl, by nlinarith⟩
      ⟨mul_nonneg (Nat.cast_nonneg _) hr.le, hτ⟩
    rw [Nat.sub_add_cancel hK.1, hempty] at hx
    exact hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
