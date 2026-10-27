module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ObserveAtoms
public import CORALean.Specification.FourValuedSignal.Theorems.SetSpec

@[expose] public section

/-!
# The atom signals of observations are valid and known only where observed

From valid atom signals the observations give valid ones, and a value other than ⊣₂ at `t` was
there before or comes from an observation whose interval holds `t`.

## Inputs
* `obs` – observations: set, time interval, location
* `sig` – atom signals before the observations

## Hypotheses
* `hv` – `sig` is valid

## Conclusion
* the atom signals after `obs` are valid and, where not inconclusive, were so before or observed
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.observeAtoms_spec (obs : List (S d × STLInterval ℝ × ℕ))
    (sig : AtomicProposition S d → FourValuedSignal ℝ)
    (hv : ∀ a, (sig a).IsValid) : -- --- CONCL ---
    (∀ a, (OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋) sig obs a).IsValid) ∧
    ∀ a (t : ℝ), 0 ≤ t → (OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋) sig obs a).at t ≠ .ii →
      (sig a).at t ≠ .ii ∨ ∃ o ∈ obs, t ∈ o.2.1.set := by -- --- PROOF ---
  induction obs generalizing sig with
  | nil => exact ⟨hv, fun a t _ h => Or.inl h⟩
  | cons o obs ih =>
    -- the first observation, then the rest
    have hv1 : ∀ a, (OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋) sig [o] a).IsValid := by
      intro a; simp only [OnlineReachSetAnalyzer.observeAtoms, List.foldl_cons, List.foldl_nil]
      split
      · exact (FourValuedSignal.set_spec _ (hv a) _ _).1
      · exact hv a
    obtain ⟨h1, h2⟩ := ih _ hv1
    refine ⟨h1, fun a t ht hne => ?_⟩
    rcases h2 a t ht hne with h | ⟨o', ho', ht'⟩
    · by_cases hI : t ∈ o.2.1.set
      · exact Or.inr ⟨o, by simp, hI⟩
      · -- outside the first interval the first observation changes nothing
        left
        revert h; simp only [OnlineReachSetAnalyzer.observeAtoms, List.foldl_cons, List.foldl_nil]
        split
        · rw [((FourValuedSignal.set_spec _ (hv a) _ _).2 t ht).2 hI]; exact id
        · exact id
    · exact Or.inr ⟨o', by simp [ho'], ht'⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
