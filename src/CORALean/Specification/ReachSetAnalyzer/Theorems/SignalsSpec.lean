module

public import CORALean.Specification.FiniteKleeneSignalBuilder.Theorems.KleeneSignalSpec
public import CORALean.Specification.ReachSetAnalyzer.Definitions.Represents
public import CORALean.Specification.ReachSetAnalyzer.Operations.Signals

@[expose] public section

/-!
# What `signals` computes

For an analyzer that represents `PT` and `PF`, `signals` succeeds and gives, for each proposition
in order, a valid three-valued signal of duration `d` that is true at `t` exactly where the
proposition can be true and cannot be false, and false exactly where it can be false and cannot be
true (unknown elsewhere).

## Inputs
* `obj` – analyzer
* `d` – signal duration
* `PT` – times where each proposition can be true
* `PF` – times where each proposition can be false

## Hypotheses
* `hobj` – the analyzer represents `PT` and `PF`

## Conclusion
* the signals are valid and true where only `PT` holds, false where only `PF`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.signals_spec (obj : ReachSetAnalyzer ℝ S n) (d : ℝ)
    (PT PF : String → ℝ → Prop) (hobj : obj.Represents d PT PF) : -- --- CONCL ---
    ∃ sigs, obj.signals = some sigs ∧ List.Forall₂ (fun p q => q.1 = p.1 ∧ q.2.IsValid ∧
      q.2.duration = d ∧ ∀ t : ℝ, 0 ≤ t → t ≤ d → ∃ v, q.2.at? t = some v ∧
        (v = Kleene.tt ↔ PT p.1 t ∧ ¬ PF p.1 t) ∧ (v = Kleene.ff ↔ PF p.1 t ∧ ¬ PT p.1 t))
      obj.aps sigs := by -- --- PROOF ---
  -- the signals of a list `l` of the propositions of `obj`, one after the other
  have key : ∀ l : List (String × AtomicProposition S n), (∀ p ∈ l, p ∈ obj.aps) →
      ∃ sigs, (l.mapM fun p => ((obj.sigBuilder.lookup p.1).bind
          FiniteKleeneSignalBuilder.kleeneSignal?).map fun s => (p.1, s)) = some sigs ∧
        List.Forall₂ (fun p q => q.1 = p.1 ∧ q.2.IsValid ∧ q.2.duration = d ∧
          ∀ t : ℝ, 0 ≤ t → t ≤ d → ∃ v, q.2.at? t = some v ∧
            (v = Kleene.tt ↔ PT p.1 t ∧ ¬ PF p.1 t) ∧ (v = Kleene.ff ↔ PF p.1 t ∧ ¬ PT p.1 t))
          l sigs := by
    intro l
    induction l with
    | nil => intro _; exact ⟨[], rfl, List.Forall₂.nil⟩
    | cons p l ih =>
      intro hl
      -- the first proposition's builder, its signal, and the signals of the others
      obtain ⟨b, hb, hr⟩ := hobj.2 p (hl p List.mem_cons_self)
      obtain ⟨s, hs, hv, hd, hat⟩ := FiniteKleeneSignalBuilder.kleeneSignal?_spec b d _ _ hr
      obtain ⟨sigs, hsigs, hf⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
      refine ⟨(p.1, s) :: sigs, ?_, List.Forall₂.cons ⟨rfl, hv, hd, hat⟩ hf⟩
      rw [List.mapM_cons, hsigs]
      simp [hb, hs]
  obtain ⟨sigs, hsigs, hf⟩ := key obj.aps fun p hp => hp
  exact ⟨sigs, hsigs, hf⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
