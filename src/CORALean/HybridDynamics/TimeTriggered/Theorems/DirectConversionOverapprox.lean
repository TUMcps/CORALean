module

public import CORALean.HybridDynamics.TimeTriggered.Definitions.ContOverapprox
public import CORALean.HybridDynamics.TimeTriggered.Definitions.FirstDwell
public import CORALean.HybridDynamics.TimeTriggered.Definitions.SecondDwell
public import CORALean.HybridDynamics.TimeTriggered.Operations.DirectConversion
public import CORALean.HybridDynamics.TimeTriggered.Operations.SpaceTriggered
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import CORALean.HybridDynamics.TimeTriggered.DiffInclAutomaton
public import CORALean.HybridDynamics.TimeTriggered.Theorems.FlowsTimer

@[expose] public section

/-!
# The direct time-triggered conversion overapproximates

[1, Lemma 1]: for every time bound `T`, `H_tt` reaches, within `T`, every continuous part `H`
reaches within `T`. The paper builds the execution of `H_tt` from one of `H` by cases on the
duration against `t₁` and `t₁ + t₂`; here that is an induction over the execution. Two things the
printed proof passes over: an execution of `H` still in `m₁` after `t₁` is not an execution of
`H_tt`, whose `m₁` is left at `t₁`, so it is mirrored in `m_either`, whose flow must contain
`f₁`; and the flow of `H` that crosses `t₁` or `t₁ + t₂` is split there.

## Inputs
* `I` – initial states
* `f₁` – flow in the first mode
* `f₂` – flow in the second mode
* `a` – guard normal
* `b` – guard offset
* `fe` – flow in the either mode
* `t₁` – first dwell time
* `t₂` – second dwell time
* `T` – time bound

## Hypotheses
* `hfe₁` – either flow contains the first flow
* `hfe₂` – either flow contains the second flow
* `ht₁` – first dwell time nonnegative
* `h₁` – first dwell time is valid
* `h₂` – second dwell time is valid

## Conclusion
* the conversion overapproximates the original within the bound

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modelling and Analysis of Timed
      Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {M X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A continuous successor over `t` is one over `s` followed by one over `t - s` ([1, Def. 4]). -/
theorem DiffInclAutomaton.aux_flows_split {H : DiffInclAutomaton M X} {m : M} {x x' : X}
    {t s : ℝ} (h : H.Flows m x t x') (hs : 0 < s) (hst : s < t) : -- --- CONCL ---
    ∃ y, H.Flows m x s y ∧ H.Flows m y (t - s) x' := by -- --- PROOF ---
  obtain ⟨_, g, hd, h0, ht, hg⟩ := h
  refine ⟨g s, ⟨hs, g, hd.mono (Set.Icc_subset_Icc le_rfl hst.le), h0, rfl, fun δ hδ => ?_⟩,
    ⟨by linarith, fun δ => g (s + δ), ?_, by simp, by simpa using ht, fun δ hδ => ?_⟩⟩
  · exact hg δ ⟨hδ.1, hδ.2.trans hst⟩
  · -- the shifted piece is the composite of `g` with `δ ↦ s + δ`
    refine hd.comp ((differentiable_id.const_add s).differentiableOn) fun δ hδ => ⟨?_, ?_⟩
    · linarith [hδ.1]
    · linarith [hδ.2]
  · have h1 := hg (s + δ) ⟨by linarith [hδ.1], by linarith [hδ.2]⟩
    exact ⟨h1.1, by rw [deriv_comp_const_add]; exact h1.2⟩

end


-- =======================================  MAIN THEOREM  ======================================= --

/-- `H_tt` with time bound `T` overapproximates `H` with time bound `T`:
`Reach≤T(H) ⊆ Reach≤T(H_tt)↓Var`, for `H` of [1, Assumption 1, Assumption 2] and `H_tt` of
[1, Sec. 3.1], with `t₁`, `t₂` as selected there and `f_either ⊇ f₁ ∪ f₂`. -/
theorem DiffInclAutomaton.directConversion_overapprox {I : Set X} {f₁ f₂ : X → X} {a : X}
    {b : ℝ} {fe : X → Set X} {t₁ t₂ : ℝ} (hfe₁ : ∀ x, f₁ x ∈ fe x) (hfe₂ : ∀ x, f₂ x ∈ fe x)
    (ht₁ : 0 ≤ t₁) (h₁ : (spaceTriggered I f₁ f₂ a b).FirstDwell t₁)
    (h₂ : (spaceTriggered I f₁ f₂ a b).SecondDwell t₁ t₂) (T : ℝ) : -- --- CONCL ---
    (spaceTriggered I f₁ f₂ a b).ContOverapprox T
      (directConversion I f₁ f₂ fe t₁ t₂) Prod.fst T := by -- --- PROOF ---
  unfold DiffInclAutomaton.ContOverapprox
  set Hs := spaceTriggered I f₁ f₂ a b with hHs
  set Ht := directConversion I f₁ f₂ fe t₁ t₂ with hHt
  -- a flow of `Hs` in mode `m` is a flow of `Ht` in mode `k` once the flow sets and invariants fit
  have flowK : ∀ {m : Fin 2} {k : Fin 3} {c d t τ : ℝ} {x x' : X},
      (∀ y τ', ∀ v ∈ Hs.flow m y, (v, (1 : ℝ)) ∈ Ht.flow k (y, τ')) →
      (∀ y ∈ Hs.inv m, ∀ τ' ≤ c, (y, τ') ∈ Ht.inv k) → Hs.Flows m x t x' →
      Ht.IsExec d k (x, τ) → τ + t ≤ c → Ht.IsExec (d + t) k (x', τ + t) :=
    fun hfl hin hf h hc => h.flow (DiffInclAutomaton.flows_timer hf hfl hin hc)
  -- the three modes of `Ht` and the flows of `Hs` they receive
  have flow0 : ∀ {d t τ : ℝ} {x x' : X}, Hs.Flows 0 x t x' → Ht.IsExec d 0 (x, τ) →
      τ + t ≤ t₁ → Ht.IsExec (d + t) 0 (x', τ + t) := by
    intro d t τ x x' hf h hc
    refine flowK (c := t₁) ?_ ?_ hf h hc
    · intro y τ' v hv
      simp [hHs, hHt, spaceTriggered, directConversion] at hv ⊢
      simp [hv]
    · intro y _ τ' hτ
      simp [hHt, directConversion, hτ]
  -- `m_either` takes the flows of both modes, its flow containing `f₁` and `f₂`
  have flow1 : ∀ {m : Fin 2} {d t τ : ℝ} {x x' : X}, Hs.Flows m x t x' → Ht.IsExec d 1 (x, τ) →
      τ + t ≤ t₂ → Ht.IsExec (d + t) 1 (x', τ + t) := by
    intro m d t τ x x' hf h hc
    refine flowK (c := t₂) ?_ ?_ hf h hc
    · intro y τ' v hv
      fin_cases m
      · simp [hHs, hHt, spaceTriggered, directConversion] at hv ⊢
        simp [hv, hfe₁]
      · simp [hHs, hHt, spaceTriggered, directConversion] at hv ⊢
        simp [hv, hfe₂]
    · intro y _ τ' hτ
      simp [hHt, directConversion, hτ]
  -- `m₂` of `Ht` has no timer bound, so the timer is the one it ends at
  have flow2 : ∀ {d t τ : ℝ} {x x' : X}, Hs.Flows 1 x t x' → Ht.IsExec d 2 (x, τ) →
      Ht.IsExec (d + t) 2 (x', τ + t) := by
    intro d t τ x x' hf h
    refine flowK (c := τ + t) ?_ ?_ hf h le_rfl
    · intro y τ' v hv
      simp [hHs, hHt, spaceTriggered, directConversion] at hv ⊢
      simp [hv]
    · intro y _ τ' _
      simp [hHt, directConversion]
  -- the two time-triggered jumps
  have jump01 : ∀ {d : ℝ} {x : X}, Ht.IsExec d 0 (x, t₁) → Ht.IsExec d 1 (x, 0) := by
    intro d x h
    exact h.jump ⟨0, {p | p.2 = t₁}, fun p => (p.1, 0), 1⟩ (by simp [hHt, directConversion])
      rfl rfl
  have jump12 : ∀ {d : ℝ} {x : X}, Ht.IsExec d 1 (x, t₂) → Ht.IsExec d 2 (x, 0) := by
    intro d x h
    exact h.jump ⟨1, {p | p.2 = t₂}, fun p => (p.1, 0), 2⟩ (by simp [hHt, directConversion])
      rfl rfl
  -- a flow crossing the time `s` is split there, or ends exactly there
  have cross : ∀ {m : Fin 2} {x x' : X} {t s : ℝ}, Hs.Flows m x t x' → 0 < s → s ≤ t →
      ∃ y, Hs.Flows m x s y ∧ (s = t ∧ y = x' ∨ s < t ∧ Hs.Flows m y (t - s) x') := by
    intro m x x' t s hf hs hst
    rcases hst.eq_or_lt with rfl | hlt
    · exact ⟨x', hf, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨y, h1, h2⟩ := DiffInclAutomaton.aux_flows_split hf hs hlt
      exact ⟨y, h1, Or.inr ⟨hlt, h2⟩⟩
  -- the same state at another duration or timer
  have cast : ∀ {k : Fin 3} {d d' τ τ' : ℝ} {x : X}, Ht.IsExec d k (x, τ) → d = d' → τ = τ' →
      Ht.IsExec d' k (x, τ') := by
    intro k d d' τ τ' x h hd hτ
    subst hd; subst hτ; exact h
  -- every state of `H` has the `H_tt` execution of the same duration, in the mode its duration says
  have key : ∀ {d : ℝ} {m : Fin 2} {x : X}, Hs.IsExec d m x → 0 ≤ d ∧
      (m = 0 → (d < t₁ → Ht.IsExec d 0 (x, d)) ∧ (t₁ ≤ d → Ht.IsExec d 1 (x, d - t₁))) ∧
      (m = 1 → t₁ ≤ d ∧ (d < t₁ + t₂ → Ht.IsExec d 1 (x, d - t₁)) ∧
        (t₁ + t₂ ≤ d → ∃ s, Ht.IsExec d 2 (x, s))) := by
    intro d m x h
    induction h with
    | init hx =>
      -- an initial state is in `m₁`, and starts the timer at zero
      rename_i m x
      have hm : m = 0 := by
        by_contra hne
        simp [hHs, spaceTriggered, hne] at hx
      subst hm
      have e0 : Ht.IsExec 0 0 (x, 0) :=
        DiffInclAutomaton.IsExec.init (by
          simp only [hHs, spaceTriggered, if_true] at hx
          simp [hHt, directConversion, hx])
      refine ⟨le_rfl, fun _ => ⟨fun _ => e0, fun ht => ?_⟩, fun h01 => absurd h01 (by decide)⟩
      have h0 : t₁ = 0 := le_antisymm ht ht₁
      exact cast (jump01 (cast e0 rfl h0.symm)) rfl (by rw [h0]; ring)
    | flow h hf ih =>
      rename_i d t m x x'
      have htp : 0 < t := hf.1
      have hd0 := ih.1
      -- the duration stays below `t₁ + t₂` in `m₁`, which the second dwell time says
      fin_cases m
      · have hd' : d + t < t₁ + t₂ := by
          by_contra hc
          exact absurd (h₂ _ (not_lt.1 hc) 0 x' (h.flow hf)) (by decide)
        have ih0 := ih.2.1 rfl
        refine ⟨by linarith, fun _ => ⟨fun hlt => ?_, fun hge => ?_⟩,
          fun h01 => absurd h01 (by decide)⟩
        · exact flow0 hf (ih0.1 (by linarith)) (by linarith)
        · by_cases hd : t₁ ≤ d
          · exact cast (flow1 hf (ih0.2 hd) (by linarith)) rfl (by ring)
          · -- the flow crosses `t₁`: `m₁` up to it, the jump, `m_either` for the rest
            replace hd := not_le.1 hd
            obtain ⟨y, h1, h2⟩ := cross hf (s := t₁ - d) (by linarith) (by linarith)
            have e1 := jump01 (cast (flow0 h1 (ih0.1 hd) (by linarith)) rfl (by ring))
            rcases h2 with ⟨hs, rfl⟩ | ⟨hs, h3⟩
            · exact cast e1 (by linarith) (by linarith)
            · exact cast (flow1 h3 e1 (by linarith)) (by ring) (by ring)
      · have ih1 := ih.2.2 rfl
        refine ⟨by linarith, fun h01 => absurd h01 (by decide),
          fun _ => ⟨by linarith [ih1.1], fun hlt => ?_, fun hge => ?_⟩⟩
        · exact cast (flow1 hf (ih1.2.1 (by linarith)) (by linarith)) rfl (by ring)
        · by_cases hd : t₁ + t₂ ≤ d
          · obtain ⟨s, hs⟩ := ih1.2.2 hd
            exact ⟨s + t, flow2 hf hs⟩
          · -- the flow crosses `t₁ + t₂`: `m_either` up to it, the jump, `m₂` for the rest
            replace hd := not_le.1 hd
            obtain ⟨y, h1, h2⟩ := cross hf (s := t₁ + t₂ - d) (by linarith) (by linarith)
            have e1 := jump12 (cast (flow1 h1 (ih1.2.1 hd) (by linarith)) rfl (by ring))
            rcases h2 with ⟨hs, rfl⟩ | ⟨hs, h3⟩
            · exact ⟨0, cast e1 (by linarith) rfl⟩
            · exact ⟨0 + (t - (t₁ + t₂ - d)), cast (flow2 h3 e1) (by ring) rfl⟩
    | jump h e he hm hx ih =>
      -- the one transition of `Hs` leaves `m₁`, after at least `t₁` and before `t₁ + t₂`
      rename_i d m x
      have hE := DiffInclAutomaton.IsExec.jump h e he hm hx
      obtain rfl : e = ⟨0, {x | inner ℝ a x = b}, id, 1⟩ := by simpa [hHs, spaceTriggered] using he
      have hm0 : (0 : Fin 2) = m := hm
      subst hm0
      have ih0 := ih.2.1 rfl
      -- the first and second dwell times bound the duration of the jump
      have hlt : d < t₁ + t₂ := by
        by_contra hc
        exact absurd (h₂ _ (not_lt.1 hc) 0 x h) (by decide)
      have hge : t₁ ≤ d := by
        by_contra hc
        have h10 := h₁ d (lt_of_not_ge hc) _ _ hE
        simp at h10
      exact ⟨ih.1, fun h01 => by simp at h01,
        fun _ => ⟨hge, fun _ => ih0.2 hge, fun hc => absurd hc (not_le.2 hlt)⟩⟩
  -- read off the execution of `H_tt` at the end state
  rintro x ⟨d, m, hdT, hE⟩
  obtain ⟨hd0, h0, h1⟩ := key hE
  fin_cases m
  · by_cases hlt : d < t₁
    · exact ⟨(x, d), ⟨d, 0, hdT, (h0 rfl).1 hlt⟩, rfl⟩
    · exact ⟨(x, d - t₁), ⟨d, 1, hdT, (h0 rfl).2 (not_lt.1 hlt)⟩, rfl⟩
  · obtain ⟨_, hA, hB⟩ := h1 rfl
    by_cases hlt : d < t₁ + t₂
    · exact ⟨(x, d - t₁), ⟨d, 1, hdT, hA hlt⟩, rfl⟩
    · obtain ⟨s, hs⟩ := hB (not_lt.1 hlt)
      exact ⟨(x, s), ⟨d, 2, hdT, hs⟩, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
