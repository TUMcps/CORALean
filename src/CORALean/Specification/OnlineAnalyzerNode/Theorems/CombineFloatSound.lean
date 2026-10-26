module

public import CORALean.Specification.FourValuedSignal.Theorems.AndMapTime
public import CORALean.Specification.FourValuedSignal.Theorems.AtAnd
public import CORALean.Specification.FourValuedSignal.Theorems.AtOr
public import CORALean.Specification.FourValuedSignal.Theorems.OrMapTime
public import CORALean.Specification.FourValuedSignal.Theorems.UntilFloatSound
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Combine
public import CORALean.Specification.OnlineAnalyzerNode.Operations.CombineFloat
public import CORALean.Specification.OnlineAnalyzerNode.Operations.ToRealNode

@[expose] public section

/-!
# The float signal a node derives from its children is sound

If the children's signals read as reals are valid, a `True` or `False` of `combineFloat`, read as
reals, at a time `t ≥ 0` is that of `combine` on the node and children read as reals: the
negation, conjunction and disjunction read the time stamps exactly (`at_and`, `at_or`), and the
until is sound (`FourValuedSignal.untilFloat_sound`). `Unknown` and `Inconclusive` claim nothing.

## Inputs
* `n` – node
* `ch` – children

## Hypotheses
* `hch` – the children's signals read as reals are valid

## Conclusion
* a float `True` or `False` is the exact one
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {A : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every entry of a list, by index or by membership. -/
private theorem aux_forall_get {X : Type} (l : List X) (P : X → Prop) :
    (∀ k : Fin l.length, P (l.get k)) ↔ ∀ x ∈ l, P x := by
  refine ⟨fun h x hx => ?_, fun h k => h _ (List.get_mem l k)⟩
  obtain ⟨k, rfl⟩ := List.get_of_mem hx
  exact h k


/-- Some entry of a list, by index or by membership. -/
private theorem aux_exists_get {X : Type} (l : List X) (P : X → Prop) :
    (∃ k : Fin l.length, P (l.get k)) ↔ ∃ x ∈ l, P x := by
  refine ⟨fun ⟨k, hk⟩ => ⟨_, List.get_mem l k, hk⟩, fun ⟨x, hx, h⟩ => ?_⟩
  obtain ⟨k, rfl⟩ := List.get_of_mem hx
  exact ⟨k, h⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineAnalyzerNode.combineFloat_sound (n : OnlineAnalyzerNode 𝕋 A)
    (ch : List (OnlineAnalyzerNode 𝕋 A))
    (hch : ∀ c ∈ ch, (c.signal.mapTime toReal).IsValid) : -- --- CONCL ---
    ∀ df ∈ n.combineFloat ch, ∀ de ∈ n.toRealNode.combine (ch.map OnlineAnalyzerNode.toRealNode),
      ∀ t : ℝ, 0 ≤ t → ((df.mapTime toReal).at t = FourValued.tt → de.at t = FourValued.tt) ∧
        ((df.mapTime toReal).at t = FourValued.ff → de.at t = FourValued.ff) := by -- --- PROOF ---
  intro df hdf de hde t ht
  have hk : n.toRealNode.kind = n.kind := rfl
  -- the children read as reals, by membership
  have hvR : ∀ c ∈ ch.map OnlineAnalyzerNode.toRealNode, c.signal.IsValid := by
    intro c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    exact hch c' hc'
  unfold OnlineAnalyzerNode.combineFloat at hdf
  unfold OnlineAnalyzerNode.combine at hde
  rw [hk] at hde
  cases hkind : n.kind <;> rw [hkind] at hdf hde <;> dsimp only at hdf hde
  · exact absurd hdf (by simp)
  · exact absurd hdf (by simp)
  · exact absurd hdf (by simp)
  · -- the negation reads the time stamps exactly
    rcases ch with _ | ⟨c, _ | ⟨c', rest⟩⟩
    · exact absurd hdf (by simp)
    · obtain rfl := Option.some.inj hdf
      obtain rfl := Option.some.inj hde
      exact ⟨id, id⟩
    · exact absurd hdf (by simp)
  · -- the disjunction: some child `True`, or all `False`
    by_cases he : ch = []
    · subst he; exact absurd hdf (by simp)
    have hne : (ch.map OnlineAnalyzerNode.toRealNode) ≠ [] := by simpa using he
    rw [if_neg (by simpa using he)] at hdf
    rw [if_neg hne] at hde
    haveI : Nonempty (Fin ch.length) := ⟨⟨0, List.length_pos_iff.2 he⟩⟩
    haveI : Nonempty (Fin (ch.map OnlineAnalyzerNode.toRealNode).length) :=
      ⟨⟨0, List.length_pos_iff.2 hne⟩⟩
    -- the float disjunction read as reals, and the exact one, by their values
    obtain ⟨r, hr, -, hrt⟩ := FourValuedSignal.at_or
      (fun k : Fin ch.length => (ch.get k).signal.mapTime toReal)
      (fun k => hch _ (List.get_mem ch k))
    rw [← FourValuedSignal.or_mapTime, hdf, Option.map_some, Option.some.injEq] at hr
    subst hr
    obtain ⟨r', hr', -, hrt'⟩ := FourValuedSignal.at_or
      (fun k : Fin (ch.map OnlineAnalyzerNode.toRealNode).length =>
        ((ch.map OnlineAnalyzerNode.toRealNode).get k).signal)
      (fun k => hvR _ (List.get_mem _ k))
    obtain rfl : r' = de := Option.some.inj (hr'.symm.trans hde)
    -- the children by membership, read as reals on both sides
    obtain ⟨t1, f1, -⟩ := hrt t ht
    obtain ⟨t2, f2, -⟩ := hrt' t ht
    rw [t1, t2, f1, f2,
      aux_exists_get ch (fun c : OnlineAnalyzerNode 𝕋 A =>
        (c.signal.mapTime toReal).at t = FourValued.tt),
      aux_exists_get _ (fun c : OnlineAnalyzerNode ℝ A => c.signal.at t = FourValued.tt),
      aux_forall_get ch (fun c : OnlineAnalyzerNode 𝕋 A =>
        (c.signal.mapTime toReal).at t = FourValued.ff),
      aux_forall_get _ (fun c : OnlineAnalyzerNode ℝ A => c.signal.at t = FourValued.ff)]
    simp [OnlineAnalyzerNode.toRealNode]
  · -- the conjunction: all children `True`, or some `False`
    by_cases he : ch = []
    · subst he; exact absurd hdf (by simp)
    have hne : (ch.map OnlineAnalyzerNode.toRealNode) ≠ [] := by simpa using he
    rw [if_neg (by simpa using he)] at hdf
    rw [if_neg hne] at hde
    haveI : Nonempty (Fin ch.length) := ⟨⟨0, List.length_pos_iff.2 he⟩⟩
    haveI : Nonempty (Fin (ch.map OnlineAnalyzerNode.toRealNode).length) :=
      ⟨⟨0, List.length_pos_iff.2 hne⟩⟩
    -- the float conjunction read as reals, and the exact one, by their values
    obtain ⟨r, hr, -, hrt⟩ := FourValuedSignal.at_and
      (fun k : Fin ch.length => (ch.get k).signal.mapTime toReal)
      (fun k => hch _ (List.get_mem ch k))
    rw [← FourValuedSignal.and_mapTime, hdf, Option.map_some, Option.some.injEq] at hr
    subst hr
    obtain ⟨r', hr', -, hrt'⟩ := FourValuedSignal.at_and
      (fun k : Fin (ch.map OnlineAnalyzerNode.toRealNode).length =>
        ((ch.map OnlineAnalyzerNode.toRealNode).get k).signal)
      (fun k => hvR _ (List.get_mem _ k))
    obtain rfl : r' = de := Option.some.inj (hr'.symm.trans hde)
    -- the children by membership, read as reals on both sides
    obtain ⟨t1, f1, -⟩ := hrt t ht
    obtain ⟨t2, f2, -⟩ := hrt' t ht
    rw [t1, t2, f1, f2,
      aux_forall_get ch (fun c : OnlineAnalyzerNode 𝕋 A =>
        (c.signal.mapTime toReal).at t = FourValued.tt),
      aux_forall_get _ (fun c : OnlineAnalyzerNode ℝ A => c.signal.at t = FourValued.tt),
      aux_exists_get ch (fun c : OnlineAnalyzerNode 𝕋 A =>
        (c.signal.mapTime toReal).at t = FourValued.ff),
      aux_exists_get _ (fun c : OnlineAnalyzerNode ℝ A => c.signal.at t = FourValued.ff)]
    simp [OnlineAnalyzerNode.toRealNode]
  · -- the until: sound
    rcases ch with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, rest⟩⟩⟩
    · simp at hdf
    · simp at hdf
    swap
    · simp at hdf
    rcases hI : n.interval with _ | I
    · rw [hI] at hdf; exact absurd hdf (by simp)
    rw [hI] at hdf
    have hI' : n.toRealNode.interval = some I.toRealInterval := by
      simp [OnlineAnalyzerNode.toRealNode, hI]
    simp only [List.map_cons, List.map_nil, hI'] at hde
    exact FourValuedSignal.untilFloat_sound c1.signal c2.signal (hch c1 (by simp))
      (hch c2 (by simp)) I df hdf de hde t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
