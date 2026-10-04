import CORALean.ContDynamics.LinearARX.LinearARX
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

/-!
# The reachable outputs of a state-space model

[1, Prop. 1]: for the model of [1, Def. 1], `x(k+1) = A x(k) + B u(k) + w(k)`,
`y(k) = C x(k) + D u(k) + v(k)`, the outputs are exactly
`Y(k) = C A^k X(0) ⊕ ⊕_{i=1}^k C A^{i-1}(B U(k-i) ⊕ W(k-i)) ⊕ D U(k) ⊕ V(k)`, the baseline
the paper compares ARMAX against. Written with `i - 1` as `i`, over `range k`. Each
input and disturbance enters once, so the Minkowski sums lose nothing; the sets are
nonempty so that the signals past `k`, which `y(k)` does not read, exist.

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". In Proc. of the
  62nd IEEE Conference on Decision and Control (CDC), 2023, pp. 7027-7034.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n m q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The state in closed form: (3a) unrolled. -/
theorem LinearARX.aux_ss_closed (A : Mat ℝ n n) (B : Mat ℝ n m) {x : ℕ → Vec ℝ n}
    {u : ℕ → Vec ℝ m} {w : ℕ → Vec ℝ n} (hx : ∀ i, x (i + 1) = A *ᵥ x i + B *ᵥ u i + w i)
    (k : ℕ) : x k = A ^ k *ᵥ x 0
      + ∑ i ∈ Finset.range k, A ^ i *ᵥ (B *ᵥ u (k - 1 - i) + w (k - 1 - i)) := by -- --- PROOF ---
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hx, ih, Finset.sum_range_succ', mulVec_add, mulVec_mulVec, ← pow_succ', mulVec_sum]
    simp only [pow_zero, one_mulVec, Nat.add_sub_cancel, Nat.sub_zero]
    have h : ∀ i ∈ Finset.range k, A *ᵥ A ^ i *ᵥ (B *ᵥ u (k - 1 - i) + w (k - 1 - i))
        = A ^ (i + 1) *ᵥ (B *ᵥ u (k + 1 - 1 - (i + 1)) + w (k + 1 - 1 - (i + 1))) := by
      intro i _
      rw [mulVec_mulVec, ← pow_succ', show k + 1 - 1 - (i + 1) = k - 1 - i by omega]
    rw [Finset.sum_congr rfl h]
    abel


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.ssReach_eq (A : Mat ℝ n n) (B : Mat ℝ n m) (C : Mat ℝ q n) (D : Mat ℝ q m)
    (X₀ : Set (Vec ℝ n)) {U : ℕ → Set (Vec ℝ m)} {W : ℕ → Set (Vec ℝ n)}
    {V : ℕ → Set (Vec ℝ q)} (hU : ∀ i, (U i).Nonempty) (hW : ∀ i, (W i).Nonempty)
    (hV : ∀ i, (V i).Nonempty) (k : ℕ) :
    {y | ∃ (x : ℕ → Vec ℝ n) (u : ℕ → Vec ℝ m) (w : ℕ → Vec ℝ n) (v : ℕ → Vec ℝ q),
      x 0 ∈ X₀ ∧ (∀ i, u i ∈ U i) ∧ (∀ i, w i ∈ W i) ∧ (∀ i, v i ∈ V i) ∧
      (∀ i, x (i + 1) = A *ᵥ x i + B *ᵥ u i + w i) ∧ y = C *ᵥ x k + D *ᵥ u k + v k}
    = ((C * A ^ k) *ᵥ ·) '' X₀
      + ∑ i ∈ Finset.range k, ((C * A ^ i) *ᵥ ·) '' ((B *ᵥ ·) '' U (k - 1 - i) + W (k - 1 - i))
      + (D *ᵥ ·) '' U k + V k := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨x, u, w, v, hx0, hu, hw, hv, hx, rfl⟩
    rw [LinearARX.aux_ss_closed A B hx k, mulVec_add, mulVec_mulVec, mulVec_sum]
    refine Set.add_mem_add (Set.add_mem_add (Set.add_mem_add ⟨_, hx0, rfl⟩
      ((Set.mem_finsetSum _ _ _).mpr ⟨_, fun {i} _ => ⟨B *ᵥ u (k - 1 - i) + w (k - 1 - i),
        Set.add_mem_add ⟨_, hu _, rfl⟩ (hw _), (mulVec_mulVec _ _ _).symm⟩, rfl⟩))
      ⟨_, hu k, rfl⟩) (hv k)
  · rintro ⟨_, ⟨_, ⟨a, ⟨x0, hx0, rfl⟩, s, hs, rfl⟩, d, ⟨uk, huk, rfl⟩, rfl⟩, vk, hvk, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetSum _ _ _).mp hs
    -- one input and one disturbance per summand
    have hc : ∀ i, ∃ bw : Vec ℝ m × Vec ℝ n, i ∈ Finset.range k →
        bw.1 ∈ U (k - 1 - i) ∧ bw.2 ∈ W (k - 1 - i) ∧ (C * A ^ i) *ᵥ (B *ᵥ bw.1 + bw.2) = g i := by
      intro i
      by_cases hi : i ∈ Finset.range k
      · obtain ⟨z, ⟨_, ⟨b, hb, rfl⟩, ww, hww, rfl⟩, hz⟩ := hg hi
        exact ⟨(b, ww), fun _ => ⟨hb, hww, hz⟩⟩
      · exact ⟨(0, 0), fun h => absurd h hi⟩
    choose bw hbw using hc
    -- the signals, each summand's draw placed at the time it enters
    let u : ℕ → Vec ℝ m := fun j =>
      if j < k then (bw (k - 1 - j)).1 else if j = k then uk else (hU j).some
    let w : ℕ → Vec ℝ n := fun j => if j < k then (bw (k - 1 - j)).2 else (hW j).some
    let v : ℕ → Vec ℝ q := fun j => if j = k then vk else (hV j).some
    let x : ℕ → Vec ℝ n := fun j => Nat.rec x0 (fun i xi => A *ᵥ xi + B *ᵥ u i + w i) j
    have hx : ∀ i, x (i + 1) = A *ᵥ x i + B *ᵥ u i + w i := fun _ => rfl
    have hback : ∀ i ∈ Finset.range k, k - 1 - (k - 1 - i) = i ∧ k - 1 - i < k := by
      intro i hi
      have := Finset.mem_range.mp hi
      omega
    refine ⟨x, u, w, v, hx0, fun j => ?_, fun j => ?_, fun j => ?_, hx, ?_⟩
    -- each signal stays in its set
    · by_cases h1 : j < k
      · have h := (hbw (k - 1 - j) (Finset.mem_range.mpr (by omega))).1
        rw [show k - 1 - (k - 1 - j) = j by omega] at h
        simp only [u, if_pos h1]
        exact h
      · by_cases h2 : j = k
        · simp only [u, if_neg h1, if_pos h2]
          rw [h2]
          exact huk
        · simp only [u, if_neg h1, if_neg h2]
          exact (hU j).some_mem
    · -- the disturbance `w`
      by_cases h1 : j < k
      · have h := (hbw (k - 1 - j) (Finset.mem_range.mpr (by omega))).2.1
        rw [show k - 1 - (k - 1 - j) = j by omega] at h
        simp only [w, if_pos h1]
        exact h
      · simp only [w, if_neg h1]
        exact (hW j).some_mem
    · by_cases h1 : j = k
      · simp only [v, if_pos h1]
        rw [h1]
        exact hvk
      · simp only [v, if_neg h1]
        exact (hV j).some_mem
    -- and the output is the chosen sum
    · rw [LinearARX.aux_ss_closed A B hx k, mulVec_add, mulVec_mulVec, mulVec_sum]
      have hsum : ∀ i ∈ Finset.range k,
          C *ᵥ A ^ i *ᵥ (B *ᵥ u (k - 1 - i) + w (k - 1 - i)) = g i := by
        intro i hi
        obtain ⟨e, hlt⟩ := hback i hi
        simp only [u, w, if_pos hlt, e]
        rw [mulVec_mulVec]
        exact (hbw i hi).2.2
      rw [Finset.sum_congr rfl hsum]
      simp only [u, v, lt_irrefl, if_false, if_true]
      rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
