module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.ObserveSet

@[expose] public section

/-!
# When `observeSet` throws and when it does nothing

`observeSet` throws for a node that is not a leaf and for an observation of a time that was already
propagated to a parent; a `true` or `false` node, observing a set no earlier than that, is left
as it is.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineAnalyzerNode.observeSet_spec (eps : ℝ)
    (n : OnlineAnalyzerNode (AtomicProposition S d)) (set : S d) (interval : STLInterval)
    (loc : ℕ) (tentative : Bool) : -- --- STMT ---
    ((n.kind = .not ∨ n.kind = .or ∨ n.kind = .and ∨ n.kind = .until) →
      OnlineAnalyzerNode.observeSet (𝕋 := 𝕋) eps n set interval loc tentative = none) ∧
    (OnlineAnalyzerNode.conflicts eps interval.infimum.value interval.infimum.closed n.prop =
        some true →
      OnlineAnalyzerNode.observeSet (𝕋 := 𝕋) eps n set interval loc tentative = none) ∧
    ((n.kind = .true ∨ n.kind = .false) →
      OnlineAnalyzerNode.conflicts eps interval.infimum.value interval.infimum.closed n.prop =
        some false →
      OnlineAnalyzerNode.observeSet (𝕋 := 𝕋) eps n set interval loc tentative =
        some n) := by -- --- PROOF ---
  unfold OnlineAnalyzerNode.observeSet
  refine ⟨fun h => ?_, fun h => ?_, fun h hc => ?_⟩
  -- a node that is not a leaf throws
  · rcases h with h | h | h | h <;> simp [h]
  -- a conflict throws
  · by_cases hk : n.kind ≠ .true ∧ n.kind ≠ .false ∧ n.kind ≠ .ap
    · rw [if_pos hk]
    · rw [if_neg hk, h]; simp
  -- a leaf with nothing in the way is unchanged
  · rcases h with h | h <;> simp [h, hc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
