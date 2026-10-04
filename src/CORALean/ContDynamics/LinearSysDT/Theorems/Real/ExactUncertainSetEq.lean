import CORALean.ContDynamics.LinearSysDT.Definitions.ExactUncertainSet

/-!
# The exact uncertain set is exactly the consistent states

[1, Def. 2]: `X_k` "is equal to the set of states that are consistent with the measured output
vectors and the initial state set `X_0`". Proved as stated, an equality: `x ∈ X_k` iff some
run `x_0 ∈ X_0`, `x_{j+1} = A x_j + ω_j` with `ω_j ∈ W`, meets every measurement
`y_j - C x_j ∈ V` for `1 ≤ j ≤ k` and ends at `x_k = x`. Induction on `k`; a run is extended
past `k` by overwriting its value at `k + 1` and its disturbance at `k`.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.exactUncertainSet_eq (sys : LinearSysDT ℝ n) (C : Mat ℝ p n)
    (V : Set (Vec ℝ p)) (X₀ W : Set (Vec ℝ n)) (y : ℕ → Vec ℝ p) (k : ℕ) (x : Vec ℝ n) :
    x ∈ sys.exactUncertainSet C V X₀ W y k ↔
      ∃ xs ws : ℕ → Vec ℝ n, xs 0 ∈ X₀ ∧
        (∀ j < k, ws j ∈ W ∧ xs (j + 1) = sys.A *ᵥ xs j + ws j) ∧
        (∀ j, 0 < j → j ≤ k → y j - C *ᵥ xs j ∈ V) ∧ xs k = x := by -- --- PROOF ---
  induction k generalizing x with
  | zero =>
    constructor
    · intro hx
      exact ⟨fun _ => x, fun _ => 0, hx, fun j hj => absurd hj (Nat.not_lt_zero _),
        fun j h0 hj => absurd (Nat.le_zero.mp hj) (Nat.pos_iff_ne_zero.mp h0), rfl⟩
    · rintro ⟨xs, ws, h0, -, -, rfl⟩
      exact h0
  | succ k ih =>
    constructor
    · -- extend the run that reaches the predecessor by one step
      rintro ⟨hpred, hy⟩
      obtain ⟨_, ⟨z, hz, rfl⟩, w, hw, rfl⟩ := hpred
      obtain ⟨xs, ws, h0, hstep, hmeas, hk⟩ := (ih z).mp hz
      refine ⟨fun j => if j = k + 1 then mulVecLin sys.A z + w else xs j,
        fun j => if j = k then w else ws j, ?_, ?_, ?_, by simp⟩
      · simpa using h0
      · -- the old steps, and the new one at `k`
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · have hne : j ≠ k := Nat.ne_of_lt hj
          have hne1 : j ≠ k + 1 := by omega
          have hne2 : j + 1 ≠ k + 1 := by omega
          simp only [hne, hne1, hne2, if_false]
          exact hstep j hj
        · simp only [if_true, show j ≠ j + 1 by omega, if_false, hk]
          exact ⟨hw, rfl⟩
      · intro j h0 hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with hj' | rfl
        · have hne : j ≠ k + 1 := by omega
          simp only [hne, if_false]
          exact hmeas j h0 (by omega)
        · simpa [LinearSysDT.consistentSet] using hy
    · -- a run of `k + 1` steps is one of `k` steps and one more
      rintro ⟨xs, ws, h0, hstep, hmeas, rfl⟩
      obtain ⟨hw, hs⟩ := hstep k (Nat.lt_succ_self k)
      refine ⟨⟨_, ⟨xs k, (ih (xs k)).mpr ⟨xs, ws, h0, fun j hj => hstep j (by omega),
        fun j h0 hj => hmeas j h0 (by omega), rfl⟩, rfl⟩, ws k, hw, ?_⟩, ?_⟩
      · rw [hs]; rfl
      · exact hmeas (k + 1) (Nat.succ_pos k) le_rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
