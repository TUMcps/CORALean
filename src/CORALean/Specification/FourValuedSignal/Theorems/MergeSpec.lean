module

public import CORALean.Specification.FourValuedSignal.Definitions.IsValid
public import CORALean.Specification.FourValuedSignal.Operations.Merge
public import CORALean.Specification.FourValuedSignal.Theorems.FindIntervalsSpec
public import CORALean.Specification.FourValuedSignal.Theorems.SetSpec
public import CORALean.Specification.Theorems.FoldlSetSpec

@[expose] public section

/-!
# Merging two four-valued signals

For valid four-valued signals, `merge(obj,other)` is valid and, at every time `t ≥ 0`, has the value
of `other` where that is conclusive or `Unknown`, and the value of `obj` where `other` is
inconclusive.

This is `Merge` in line 9 of [1, Alg. 2]: `n.signal` is overwritten where the new signal is not ⊣₂.

## Inputs
* `obj` – four-valued signal
* `other` – signal whose known values override

## Hypotheses
* `ho` – the first signal is valid
* `ht` – the second signal is valid

## Conclusion
* the merge is valid, taking the second signal where it is conclusive

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `merge` takes `other` wherever it is not inconclusive, `obj` elsewhere. -/
theorem FourValuedSignal.merge_spec (obj other : FourValuedSignal ℝ) (ho : obj.IsValid)
    (ht : other.IsValid) : -- --- CONCL ---
    (obj.merge other).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (other.at t ≠ FourValued.ii → (obj.merge other).at t = other.at t) ∧
      (other.at t = FourValued.ii → (obj.merge other).at t = obj.at t) := by -- --- PROOF ---
  -- setting the intervals where `other` has a value `w` to `w`, in one step
  let F : FourValued → FourValuedSignal ℝ → FourValuedSignal ℝ := fun w sig =>
    (other.findIntervals w).foldl (fun sig I => sig.set I w) sig
  have step : ∀ (w : FourValued) (sig : FourValuedSignal ℝ), sig.IsValid →
      (F w sig).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
        (other.at t = w → (F w sig).at t = w) ∧ (other.at t ≠ w → (F w sig).at t = sig.at t) := by
    intro w sig hsig
    obtain ⟨h1, -⟩ := other.findIntervals_spec ht w
    obtain ⟨hv, h2⟩ := List.foldl_set_spec (fun sig : FourValuedSignal ℝ => sig.IsValid)
      (fun sig t => sig.at t) (other.findIntervals w) (fun I => I.set) w (fun sig I => sig.set I w)
      (fun sig I _ hs' => by
        obtain ⟨hv, h⟩ := FourValuedSignal.set_spec sig hs' I w
        exact ⟨hv, fun t ht => h t ht⟩) sig hsig
    -- inside the intervals the value is `w`, outside it is unchanged
    refine ⟨hv, fun t htt => ⟨fun h => (h2 t htt).1 ((h1 t htt).2 h), fun h => (h2 t htt).2 ?_⟩⟩
    intro hn; exact h ((h1 t htt).1 hn)
  -- the intervals of `True`, `False` and `Unknown` are set in turn
  obtain ⟨v1, a1⟩ := step FourValued.tt obj ho
  obtain ⟨v2, a2⟩ := step FourValued.ff _ v1
  obtain ⟨v3, a3⟩ := step FourValued.uu _ v2
  rw [show obj.merge other = F FourValued.uu (F FourValued.ff (F FourValued.tt obj)) from rfl]
  refine ⟨v3, fun t htt => ?_⟩
  obtain ⟨a1t, a1f⟩ := a1 t htt
  obtain ⟨a2t, a2f⟩ := a2 t htt
  obtain ⟨a3t, a3f⟩ := a3 t htt
  -- the four values of `other` at `t`
  cases h : other.at t
  · -- ff
    exact ⟨fun _ => by rw [a3f (by simp [h]), a2t h], fun h' => absurd h' (by simp)⟩
  · -- uu
    exact ⟨fun _ => by rw [a3t h], fun h' => absurd h' (by simp)⟩
  · -- ii
    exact ⟨fun h' => absurd rfl h', fun _ => by
      rw [a3f (by simp [h]), a2f (by simp [h]), a1f (by simp [h])]⟩
  · -- tt
    exact ⟨fun _ => by rw [a3f (by simp [h]), a2f (by simp [h]), a1t h],
      fun h' => absurd h' (by simp)⟩
end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
