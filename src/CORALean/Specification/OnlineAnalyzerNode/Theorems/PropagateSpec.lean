module

public import CORALean.Specification.FourValuedSignal.Theorems.MergeSpec
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Propagate
public import CORALean.Specification.OnlineAnalyzerNode.Theorems.SetPropagatedSpec

@[expose] public section

/-!
# What `propagate` does at an inner node

An inner node (negation, conjunction, disjunction or until) merges the signal `delta` of its
children into its own: at every time `t ≥ 0` the new value is `delta`'s where that is conclusive,
the old one where not; and every child gets the conclusive interval of the new signal through
`setPropagated`. The signal `delta` is the negation (`FourValuedSignal.at_not`), conjunction
(`at_and`), disjunction (`at_or`) or until (`until_spec`) of the children's signals.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A successful `mapM` in `Option` relates each element to its image. -/
theorem aux_mapM_forall₂ {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), l.mapM f = some l' → List.Forall₂ (fun a b => f a = some b) l l'
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact List.Forall₂.nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact List.Forall₂.cons hb (aux_mapM_forall₂ f l bs hbs)


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineAnalyzerNode.propagate_spec (eps : ℝ) (n : OnlineAnalyzerNode A)
    (ch : List (OnlineAnalyzerNode A)) (I : STLInterval) (hk1 : n.kind ≠ .true)
    (hk2 : n.kind ≠ .false)
    (hk3 : n.kind ≠ .ap) (hs : n.signal.IsValid) (delta : FourValuedSignal ℝ)
    (hd : n.combine ch = some delta) (hdv : delta.IsValid) (n' : OnlineAnalyzerNode A)
    (ch' : List (OnlineAnalyzerNode A)) (h : n.propagate eps ch I = some (n', ch')) :
    n' = { n with signal := n.signal.merge delta } ∧ n'.signal.IsValid ∧
      (∀ t : ℝ, 0 ≤ t → (delta.at t ≠ FourValued.ii → n'.signal.at t = delta.at t) ∧
        (delta.at t = FourValued.ii → n'.signal.at t = n.signal.at t)) ∧
      List.Forall₂ (fun c c' => c.setPropagated eps n.idx
        (n'.signal.conclusiveInterval (n'.getAllProp eps)) = some c') ch ch' := by -- --- PROOF ---
  -- the node is the one with the merged signal
  unfold OnlineAnalyzerNode.propagate at h
  split at h
  · rename_i hkk; exact absurd hkk hk1
  · rename_i hkk; exact absurd hkk hk2
  · rename_i hkk; exact absurd hkk hk3
  · rw [hd] at h
    simp only [Option.bind_some] at h
    obtain ⟨cs, hcs, hpair⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    obtain ⟨hmv, hm⟩ := n.signal.merge_spec delta hs hdv
    exact ⟨rfl, hmv, fun t ht => hm t ht, aux_mapM_forall₂ _ ch cs hcs⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
