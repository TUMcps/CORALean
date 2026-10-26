module

public import CORALean.Specification.FourValuedSignal.Theorems.ConclusiveIntervalToRealInterval
public import CORALean.Specification.FourValuedSignal.Theorems.MergeMapTime
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Propagate
public import CORALean.Specification.OnlineAnalyzerNode.Operations.PropagateFloat
public import CORALean.Specification.OnlineAnalyzerNode.Theorems.GetAllPropFloatToRealInterval
public import CORALean.Specification.OnlineAnalyzerNode.Theorems.SetPropagatedFloatToRealNode
public import CORALean.Specification.TentativeKleeneSignal.Theorems.GetIntervalMapTime
public import CORALean.Specification.TentativeKleeneSignal.Theorems.SetInvalidMapTime

@[expose] public section

/-!
# What `propagateFloat` does, read as reals

Over a float scalar a `true`, `false` or `AP` node propagates as `propagate` does on the node read
as reals: it reads its time stamps exactly (`merge_mapTime`, `getInterval_mapTime`,
`setInvalid_mapTime`, and `conclusiveInterval_toRealInterval` for the interval an inner node
passes on). An inner node merges the float signal `delta` of its
children (`combineFloat`, whose `True` and `False` are the exact ones, `combineFloat_sound`) into
its own, read as reals, and every child read as reals gets `setPropagated` with the conclusive
interval of the new node read as reals, as `propagate_spec` says of the exact propagation.

## Inputs
* `eps` – machine epsilon
* `n` – node
* `ch` – children
* `I` – interval to make final

## Hypotheses
* none

## Conclusion
* a leaf propagates exactly; an inner node merges the float children's signal
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

/-- `mapM` into `Option` succeeds entry by entry. -/
private theorem aux_mapM_forall₂ {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), l.mapM f = some l' →
      List.Forall₂ (fun a b => f a = some b) l l'
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact List.Forall₂.nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact List.Forall₂.cons hb (aux_mapM_forall₂ f l bs hbs)


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineAnalyzerNode.propagateFloat_toRealNode (eps : 𝕋) (n : OnlineAnalyzerNode 𝕋 A)
    (ch : List (OnlineAnalyzerNode 𝕋 A)) (I : STLInterval 𝕋) : -- --- CONCL ---
    ((n.kind = .true ∨ n.kind = .false ∨ n.kind = .ap) →
      (n.propagateFloat eps ch I).map (fun r => (r.1.toRealNode, r.2.map toRealNode)) =
        n.toRealNode.propagate (toReal eps) (ch.map toRealNode) I.toRealInterval) ∧
    ∀ r ∈ n.propagateFloat eps ch I, n.kind ≠ .true → n.kind ≠ .false → n.kind ≠ .ap →
      ∃ delta ∈ n.combineFloat ch,
        r.1.toRealNode = { n.toRealNode with
          signal := n.toRealNode.signal.merge (delta.mapTime toReal) } ∧
        List.Forall₂ (fun c c' => c.toRealNode.setPropagated (toReal eps) n.idx
          (r.1.toRealNode.signal.conclusiveInterval (r.1.toRealNode.getAllProp (toReal eps))) =
            some c'.toRealNode) ch r.2 := by -- --- PROOF ---
  have hk : n.toRealNode.kind = n.kind := rfl
  refine ⟨fun hleaf => ?_, fun r hr hk1 hk2 hk3 => ?_⟩
  · -- a leaf reads its time stamps exactly
    unfold OnlineAnalyzerNode.propagateFloat OnlineAnalyzerNode.propagate
    rw [hk]
    rcases hleaf with h | h | h <;> rw [h]
    · rfl
    · rfl
    · dsimp only
      have ht : n.toRealNode.tentative = n.tentative.map (·.mapTime toReal) := rfl
      rw [ht]
      rcases n.tentative with _ | tent <;> rcases I with _ | ⟨l, u, lc, rc, hu, hlt, h0⟩
      · rfl
      · rfl
      · rfl
      · -- the tentative values on the interval are made final, read as reals
        have hI : ∃ a b c, (STLInterval.nonempty l u lc rc hu hlt h0).toRealInterval =
            STLInterval.nonempty (toReal l) (u.map toReal) lc rc a b c := by
          rcases u with _ | u <;> exact ⟨_, _, _, rfl⟩
        obtain ⟨a, b, c, hI⟩ := hI
        simp only [Option.map_some, hI]
        rw [← hI, ← TentativeKleeneSignal.getInterval_mapTime,
          ← TentativeKleeneSignal.setInvalid_mapTime]
        simp only [OnlineAnalyzerNode.toRealNode, FourValuedSignal.merge_mapTime, Option.map_some]
  · -- an inner node merges the float signal of its children
    unfold OnlineAnalyzerNode.propagateFloat at hr
    split at hr
    · rename_i hkk; exact absurd hkk hk1
    · rename_i hkk; exact absurd hkk hk2
    · rename_i hkk; exact absurd hkk hk3
    · obtain ⟨delta, hd, hr⟩ := Option.bind_eq_some_iff.1 hr
      obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.1 hr
      refine ⟨delta, hd, ?_, ?_⟩
      · simp only [OnlineAnalyzerNode.toRealNode, FourValuedSignal.merge_mapTime]
      · -- each child gets the conclusive interval, read as reals
        refine List.Forall₂.imp (fun c c' h => ?_) (aux_mapM_forall₂ _ ch cs hcs)
        dsimp only at h
        have key := OnlineAnalyzerNode.setPropagatedFloat_toRealNode eps c n.idx
          ((n.signal.merge delta).conclusiveInterval
            (({ n with signal := n.signal.merge delta } : OnlineAnalyzerNode 𝕋 A).getAllPropFloat
              eps))
        rw [h, Option.map_some, FourValuedSignal.conclusiveInterval_toRealInterval,
          OnlineAnalyzerNode.getAllPropFloat_toRealInterval] at key
        exact key.symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
