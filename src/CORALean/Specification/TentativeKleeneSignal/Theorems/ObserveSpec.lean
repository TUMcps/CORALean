module

public import CORALean.Specification.PointSegmentSignal.Theorems.SetSpec
public import CORALean.Specification.TentativeKleeneSignal.Definitions.IsValid
public import CORALean.Specification.TentativeKleeneSignal.Operations.Observe

@[expose] public section

/-!
# What an observation adds

`observe(obj,interval,value)` of a valid signal is valid and adds the observed value to what can
hold on the interval: `canBeTrue` holds at `t` iff it did or `t` is in the interval and the value
is not `False`, `canBeFalse` iff it did or `t` is in the interval and the value is not `True`.
Nothing is ever removed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem TentativeKleeneSignal.observe_spec (s : TentativeKleeneSignal ℝ) (hs : s.IsValid)
    (I : STLInterval) (hI : ∀ f, I.fieldsOf = some f → 0 ≤ f.lower) (value : Kleene) :
    (s.observe I value).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      ((s.observe I value).canBeTrue.at t = true ↔
        s.canBeTrue.at t = true ∨ (t ∈ I.set ∧ value ≠ Kleene.ff)) ∧
      ((s.observe I value).canBeFalse.at t = true ↔
        s.canBeFalse.at t = true ∨ (t ∈ I.set ∧ value ≠ Kleene.tt)) := by -- --- PROOF ---
  -- the part that is set takes the value `true` on the interval, the other is kept
  have key : ∀ (p : PointSegmentSignal ℝ) (hp : p.IsValid), (p.set I true).IsValid ∧
      ∀ t : ℝ, 0 ≤ t → ((p.set I true).at t = true ↔ p.at t = true ∨ t ∈ I.set) := by
    intro p hp
    obtain ⟨hv, h⟩ := PointSegmentSignal.set_spec p hp I hI true
    refine ⟨hv, fun t ht => ?_⟩
    by_cases hm : t ∈ I.set
    · simp [(h t ht).1 hm, hm]
    · simp [(h t ht).2 hm, hm]
  obtain ⟨k1, g1⟩ := key _ hs.1
  obtain ⟨k2, g2⟩ := key _ hs.2
  cases value
  · -- False
    refine ⟨⟨hs.1, k2⟩, fun t ht => ⟨?_, ?_⟩⟩
    · simp [TentativeKleeneSignal.observe]
    · simp [TentativeKleeneSignal.observe, g2 t ht]
  · -- Unknown
    refine ⟨⟨k1, k2⟩, fun t ht => ⟨?_, ?_⟩⟩
    · simp [TentativeKleeneSignal.observe, g1 t ht]
    · simp [TentativeKleeneSignal.observe, g2 t ht]
  · -- True
    refine ⟨⟨k1, hs.2⟩, fun t ht => ⟨?_, ?_⟩⟩
    · simp [TentativeKleeneSignal.observe, g1 t ht]
    · simp [TentativeKleeneSignal.observe]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
