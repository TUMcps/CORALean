module

public import CORALean.ContDynamics.NonlinearSys.Operations.OptDeltat

@[expose] public section

/-!
# `optDeltat` returns the best `λ'` it saw

The soundness of line 10 of [1, Alg. 2] as written here. [1] evaluates eq.
(58)'s `argmin` by increasing `λ'` "until the objective value increases again",
which is a descent and not a global minimization; what it buys is that the
`λ'` reported beats every `λ'` the walk passed through, this one included.

That is the whole guarantee, and saying so is the point: eq. (57) is not shown
convex here, so a `λ'` past the first increase may well be better. [1] makes no
claim otherwise.

[2, Alg. 2] evaluates the same argmin at its lines 8 and 12, its (31) over (30).

One hypothesis, on the caller's check: `le a b = true` implies `a ≤ b`. Nothing
asks the converse, so a check that gives up early stops the walk sooner and
never reports a `λ'` it has not beaten.

The induction is on the search's own fuel; nothing here needs it to terminate.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
* [2] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The walk only moves upward, and every step it takes is one the check
cleared, so the endpoint's cost is under every cost it passed. -/
theorem aux_optDeltatSearch_descent {le : ℝ → ℝ → Bool}
    (hle : ∀ a b : ℝ, le a b = true → a ≤ b) (cost : ℕ → ℝ) : -- --- STMT ---
    ∀ (fuel s : ℕ), s ≤ optDeltatSearch le cost s fuel ∧
      ∀ j, s ≤ j → j ≤ optDeltatSearch le cost s fuel →
        cost (optDeltatSearch le cost s fuel) ≤ cost j := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero =>
    intro s
    rw [show optDeltatSearch le cost s 0 = s from rfl]
    exact ⟨le_refl s, fun j hj hj' => by rw [le_antisymm hj' hj]⟩
  | succ k ih =>
    intro s
    rw [show optDeltatSearch le cost s (k + 1)
      = if le (cost (s + 1)) (cost s) then optDeltatSearch le cost (s + 1) k else s from rfl]
    split
    -- the check cleared the next `λ'`, so the walk moves there with the rest of the fuel
    · rename_i hc
      obtain ⟨hmono, hmin⟩ := ih (s + 1)
      refine ⟨le_trans (Nat.le_succ s) hmono, fun j hj hj' => ?_⟩
      rcases Nat.lt_or_ge s j with hlt | hge
      · exact hmin j hlt hj'
      · rw [le_antisymm hge hj]
        exact le_trans (hmin (s + 1) (le_refl _) hmono) (hle _ _ hc)
    · exact ⟨le_refl s, fun j hj hj' => by rw [le_antisymm hj' hj]⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2] line 10: the step size returned is `h ζ_δ^{λ'}` at a `λ'` whose
estimated set size is at most that of every `λ'` the search passed. -/
theorem optDeltat_descent {le : ℝ → ℝ → Bool} (hle : ∀ a b : ℝ, le a b = true → a ≤ b)
    (ζδ ζZ ζA φ1 r₀ rabs h : ℝ) (fuel : ℕ) : -- --- STMT ---
    (optDeltat le ζδ ζZ ζA φ1 r₀ rabs h fuel).Δt
        = h * ζδ ^ (optDeltat le ζδ ζZ ζA φ1 r₀ rabs h fuel).exponent ∧
      ∀ j ≤ (optDeltat le ζδ ζZ ζA φ1 r₀ rabs h fuel).exponent,
        reachSizeEstimate ζδ ζZ ζA φ1 r₀ rabs (optDeltat le ζδ ζZ ζA φ1 r₀ rabs h fuel).exponent
          ≤ reachSizeEstimate ζδ ζZ ζA φ1 r₀ rabs j := by -- --- PROOF ---
  obtain ⟨-, hmin⟩ := aux_optDeltatSearch_descent hle (reachSizeEstimate ζδ ζZ ζA φ1 r₀ rabs)
    fuel 0
  exact ⟨rfl, fun j hj => hmin j (Nat.zero_le j) hj⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
