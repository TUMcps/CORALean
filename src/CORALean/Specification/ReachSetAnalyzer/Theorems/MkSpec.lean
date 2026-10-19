module

public import CORALean.Global.LookupMapConst
public import CORALean.Specification.FiniteKleeneSignalBuilder.Theorems.MkSpec
public import CORALean.Specification.ReachSetAnalyzer.Definitions.Represents
public import CORALean.Specification.ReachSetAnalyzer.Operations.Mk

@[expose] public section

/-!
# What the constructor builds

`reachSetAnalyzer(aps,dur,masks)` fails for a negative duration (if there is any proposition).
Otherwise it keeps the propositions and masks, and, the keys being distinct, represents the empty
predicates: nothing is marked yet.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.mk?_spec (aps : List (String × AtomicProposition S n)) (dur : ℝ)
    (masks : List (String × FiniteSignal ℝ Bool)) : -- --- CONCL ---
    (dur < 0 → aps ≠ [] → ReachSetAnalyzer.mk? aps dur masks = none) ∧
    (0 ≤ dur → (aps.map Prod.fst).Nodup → ∃ obj, ReachSetAnalyzer.mk? aps dur masks = some obj ∧
      obj.aps = aps ∧ obj.masks = masks ∧
      obj.Represents dur (fun _ _ => False) (fun _ _ => False)) := by -- --- PROOF ---
  refine ⟨fun hd hne => ?_, fun hd hnd => ?_⟩
  · -- the first proposition's builder is rejected
    obtain ⟨p, ps, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp [ReachSetAnalyzer.mk?, (FiniteKleeneSignalBuilder.mk?_spec dur).1 hd]
  · -- every builder is the same empty one
    obtain ⟨b0, hb0, hr⟩ := (FiniteKleeneSignalBuilder.mk?_spec dur).2 hd
    have hall : ∀ l : List (String × AtomicProposition S n),
        (l.mapM fun p => (FiniteKleeneSignalBuilder.mk? dur).map fun builder =>
          (p.1, builder)) = some (l.map fun p => (p.1, b0)) := by
      intro l
      simp only [hb0, Option.map_some]
      induction l with
      | nil => rfl
      | cons p ps ih => simp [List.mapM_cons, ih]
    have hm := hall aps
    refine ⟨⟨aps, aps.map fun p => (p.1, b0), masks⟩, by simp [ReachSetAnalyzer.mk?, hm],
      rfl, rfl, hnd, fun p hp => ⟨b0, lookup_map_const aps b0 p hp, hr⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
