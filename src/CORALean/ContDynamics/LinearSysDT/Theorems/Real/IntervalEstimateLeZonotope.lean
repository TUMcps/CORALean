module

public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntervalEstimateLeOfBounds
public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachErrorSetSuccSubset

@[expose] public section

/-!
# The reachability-based estimator is tighter than the zonotope method

[1, Thm. 6]: with the same gain `L` and `x̂_0 = p₀`, the box of [1, Alg. 1] lies inside the box of
the zonotope method [1, Prop. 1], `x̲ᶻ_k ≤ x̲_k` and `x̅_k ≤ x̅ᶻ_k`. The zonotope method enters
through what [1, Prop. 1] makes it: `X₀ ⊆ Z_0` and
`Z_{k+1} ⊇ (A - LC) Z_k ⊕ (B u_k + L y_k) ⊕ E W ⊕ (-LF) V`, which every outer reduction keeps.
Its Eq. 34b prints the generators `E`, `-LF`, for the sets `⟨0, D_w⟩`, `⟨0, D_v⟩` of
[1, Eq. 9]; read, as the proof's Eq. 50 uses them, as `E W` and `(-LF) V`. By induction
`x̂_k + Ω_k ⊆ Z_k` (its Eq. 52), and the box of Alg. 1 is the hull of `Ω_k`.

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise CORALean.Real

variable {n nu ny nw nv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.intervalEstimate_le_zonotope (A : Mat ℝ n n) (B : Mat ℝ n nu)
    (C : Mat ℝ ny n) (E : Mat ℝ n nw) (F : Mat ℝ ny nv) (L : Mat ℝ n ny)
    (X₀ : Zonotope (Vec ℝ n)) (W : Zonotope (Vec ℝ nw)) (V : Zonotope (Vec ℝ nv))
    (u : ℕ → Vec ℝ nu) (y : ℕ → Vec ℝ ny) (Z : ℕ → Zonotope (Vec ℝ n))
    (hZ0 : X₀.construct ⊆ (Z 0).construct)
    (hZ : ∀ k, ((A - L * C) *ᵥ ·) '' (Z k).construct + {B *ᵥ u k + L *ᵥ y k} +
      (E *ᵥ ·) '' W.construct + ((-(L * F)) *ᵥ ·) '' V.construct ⊆ (Z (k + 1)).construct)
    (k : ℕ) (i : Fin n) :
    (Z k).interval.inf i ≤ (LinearSysDT.intervalEstimate A B C E F L X₀ W V u y k).inf i ∧
      (LinearSysDT.intervalEstimate A B C E F L X₀ W V u y k).sup i ≤
        (Z k).interval.sup i := by -- --- PROOF ---
  set S := LinearSysDT.intervalEstimateState A B C E F L X₀ W V u y
  -- its Eq. 52: the estimate plus any reachable error lies in the zonotope
  have hin : ∀ k, ∀ e ∈ LinearSysDT.reachErrorSet A C E F L X₀ W V k,
      (S k).x + e ∈ (Z k).construct := by
    intro k
    induction k with
    | zero =>
      rintro _ ⟨_, ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩, c, hc, rfl⟩
      obtain ⟨β, hβ, rfl⟩ := ha
      simp only [Finset.range_zero, Finset.sum_empty, Set.mem_zero] at hb hc
      subst hb hc
      exact hZ0 ⟨β, hβ, by simp [S, LinearSysDT.intervalEstimateState]⟩
    | succ k ih =>
      intro e he
      obtain ⟨_, ⟨_, ⟨e', he', rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩ :=
        LinearSysDT.reachErrorSet_succ_subset A C E F L X₀ W V k he
      refine hZ k ⟨_, ⟨_, ⟨_, ⟨_, ih e' he', rfl⟩, _, rfl, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩, _,
        ⟨v, hv, rfl⟩, ?_⟩
      -- the observer update is `(A - LC) x̂ + B u + L y`
      change _ = (LinearSysDT.intervalEstimateStep A B C L (u k) (y k) (S k)).x + _
      simp only [LinearSysDT.intervalEstimateStep, sub_mulVec, mulVec_sub, mulVec_add,
        ← mulVec_mulVec]
      abel
  -- so the zonotope's box bounds `Ω_k`, shifted by the estimate
  obtain ⟨h1, h2⟩ := LinearSysDT.intervalEstimate_le_of_bounds A B C E F L X₀ W V u y k
    ((Z k).interval.inf - (S k).x) ((Z k).interval.sup - (S k).x)
    (fun e he j => by
      have := Zonotope.interval_contains _ (hin k e he) j
      change (Z k).interval.inf j ≤ ((S k).x + e) j ∧ ((S k).x + e) j ≤ (Z k).interval.sup j
        at this
      simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
      constructor <;> linarith [this.1, this.2]) i
  rw [show LinearSysDT.intervalEstimateState A B C E F L X₀ W V u y k = S k from rfl] at h1 h2
  simp only [Pi.sub_apply, add_sub_cancel] at h1 h2
  exact ⟨h1, h2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
