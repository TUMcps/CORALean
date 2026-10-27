module

public import CORALean.Specification.FourValued.Theorems.Basic
public import CORALean.Specification.FourValuedSignal.Theorems.AtAndTwo
public import CORALean.Specification.FourValuedSignal.Theorems.AtNot
public import CORALean.Specification.FourValuedSignal.Theorems.AtOrTwo
public import CORALean.Specification.FourValuedSignal.Theorems.Basic
public import CORALean.Specification.FourValuedSignal.Theorems.ConclusiveIntervalSpec
public import CORALean.Specification.FourValuedSignal.Theorems.MergeSpec
public import CORALean.Specification.FourValuedSignal.Theorems.SetSpec
public import CORALean.Specification.FourValuedSignal.Theorems.UniformSignalSpec
public import CORALean.Specification.FourValuedSignal.Theorems.UntilRefines
public import CORALean.Specification.OnlineAnalyzerNode.Operations.ApValue
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Combine
public import CORALean.Specification.OnlineAnalyzerNode.Operations.GetAllProp
public import CORALean.Specification.OnlineAnalyzerNode.Operations.ObserveSet
public import CORALean.Specification.OnlineAnalyzerNode.Operations.PropBound
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Propagate
public import CORALean.Specification.OnlineAnalyzerNode.Operations.SetPropagated
public import CORALean.Specification.OnlineAnalyzerNode.Theorems.MkSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.IsNodeOf
public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.IsSub
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.FormulaKey
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.FormulaKeyEqv
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Mk
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ObserveSet
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Parse
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ParseNew
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.PropagateRec
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.MkNodesSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ObserveAtomsSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ObserveLeavesSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.SatRefines
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.UpdateNodeSpec
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.IsequalFloatIff
public import CORALean.Specification.STLInterval.Theorems.IsequalZeroIff
public import CORALean.Specification.STLInterval.Theorems.SetInjective
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.WithinTolZero

@[expose] public section

/-!
# The analyzer's root signal is the four-valued semantics of the observations

[1, Alg. 1] with the propagation of [1, Alg. 2], run from the analyzer of `φ` on observations with
pairwise disjoint, nonempty time intervals, ends with the root signal equal, at every `t ≥ 0`, to
the four-valued satisfaction signal of `φ` on the atom signals the observations give. The
analyzer is exact (`eps = 0`) and propagates after every observation; two atoms of `φ` with the
same label are the same, since the analyzer's cache tells subformulas apart by their labels.

## Inputs
* `φ` – formula
* `dp` – whether to propagate down
* `obs` – observations: reachable set, time interval, location

## Hypotheses
* `hlabel` – a label names one atom in `φ`
* `hne` – at least one observation
* `hI` – every observation interval is nonempty
* `hdisj` – the observation intervals are pairwise disjoint

## Conclusion
* for the analyzer of `φ` that propagates after every observation and the analyzer the exact run
  on `obs` from it ends in, the satisfaction signal of `φ` on the observed atoms exists and is
  the root signal

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


open Float SoundFloatArithmetic


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section core

variable {A : Type}

/-- Merging two signals that `s` refines gives one that `s` refines. -/
private theorem aux_merge_refines (obj other s : FourValuedSignal ℝ) (ho : obj.IsValid)
    (ht : other.IsValid) (h1 : s.Refines obj) (h2 : s.Refines other) : -- --- CONCL ---
    s.Refines (obj.merge other) := by -- --- PROOF ---
  intro t h0 hne
  obtain ⟨-, hm⟩ := FourValuedSignal.merge_spec obj other ho ht
  by_cases hi : other.at t = FourValued.ii
  · rw [(hm t h0).2 hi] at hne ⊢; exact h1 t h0 hne
  · rw [(hm t h0).1 hi]; exact h2 t h0 hi

/-- `Combine` at an inner node of `ψ k`: a valid `Δ` that the semantics refines, and equal to it
`at t` where the children agree with theirs from `t` on. -/
private theorem aux_combine_spec (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A)
    (sig : A → FourValuedSignal ℝ) (sem : ℕ → FourValuedSignal ℝ) (k : ℕ)
    (n : OnlineAnalyzerNode ℝ A) (get : ℕ → OnlineAnalyzerNode ℝ A)
    (hshape : OnlineReachSetAnalyzer.IsNodeOf ψ (ψ k) n) (hk : (ψ k).sat sig = some (sem k))
    (hsem : ∀ c ∈ n.children, (ψ c).sat sig = some (sem c) ∧ (sem c).IsValid)
    (hval : ∀ c ∈ n.children, (get c).signal.IsValid) (hinner : n.children ≠ []) : -- --- CONCL ---
    ∃ Δ, n.combine (n.children.map get) = some Δ ∧ Δ.IsValid ∧
      ((∀ c ∈ n.children, (sem c).Refines (get c).signal) → (sem k).Refines Δ) ∧
      ∀ t : ℝ, 0 ≤ t → (∀ c ∈ n.children, ∀ x, t ≤ x → (get c).signal.at x = (sem c).at x) →
        Δ.at t = (sem k).at t := by -- --- PROOF ---
  -- by the operator of the node; a leaf has no children
  unfold OnlineReachSetAnalyzer.IsNodeOf at hshape
  split at hshape
  · exact absurd hshape.2 hinner
  · exact absurd hshape.2 hinner
  · exact absurd hshape.2.1 hinner
  · -- `¬`: the child and its semantics
    rename_i φ hφ
    obtain ⟨hkind, c, hc, hψ⟩ := hshape
    rw [hc] at hsem hval ⊢
    obtain ⟨hsc, hscv⟩ := hsem c (by simp)
    have hv := hval c (by simp)
    rw [hφ] at hk
    simp only [OnlineReachSetAnalyzer.Formula.sat, ← hψ, hsc, Option.map_some,
      Option.some.injEq] at hk
    rw [← hk]
    refine ⟨(get c).signal.not, by simp [OnlineAnalyzerNode.combine, hkind],
      FourValuedSignal.not_isValid _ hv, ?_, ?_⟩
    · intro hr t ht hne
      rw [FourValuedSignal.at_not _ hv] at hne ⊢; rw [FourValuedSignal.at_not _ hscv]
      exact FourValued.not_refines _ _ (hr c (by simp) t ht) hne
    · intro t ht hagree
      rw [FourValuedSignal.at_not _ hv, FourValuedSignal.at_not _ hscv,
        hagree c (by simp) t le_rfl]
  · -- `∧`: the children and their semantics
    rename_i φ φ' hφ
    obtain ⟨hkind, c, c', hc, hψ, hψ'⟩ := hshape
    rw [hc] at hsem hval ⊢
    obtain ⟨hsc, hscv⟩ := hsem c (by simp)
    obtain ⟨hsc', hscv'⟩ := hsem c' (by simp)
    have hv := hval c (by simp)
    have hv' := hval c' (by simp)
    rw [hφ] at hk
    simp only [OnlineReachSetAnalyzer.Formula.sat, ← hψ, ← hψ', hsc, hsc', Option.bind_some] at hk
    -- the conjunction of the children's signals, and of their semantics
    obtain ⟨a, ha, hav, ha'⟩ := FourValuedSignal.at_and_two ![(get c).signal, (get c').signal]
      (by intro k; fin_cases k <;> simpa)
    obtain ⟨b, hb, -, hb'⟩ := FourValuedSignal.at_and_two ![sem c, sem c']
      (by intro k; fin_cases k <;> simpa)
    rw [hb] at hk; cases hk
    -- `Combine` computes it; refinement and agreement are pointwise
    refine ⟨a, ?_, hav, ?_, ?_⟩
    · simp only [OnlineAnalyzerNode.combine, hkind, List.map_cons, List.map_nil]
      rw [if_neg (by simp)]
      rw [← ha]; congr 1; funext i; fin_cases i <;> rfl
    · intro hr t ht hne
      rw [ha' t ht] at hne ⊢; rw [hb' t ht]
      exact FourValued.and_refines _ _ _ _ (hr c (by simp) t ht) (hr c' (by simp) t ht) hne
    · intro t ht hagree
      rw [ha' t ht, hb' t ht]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hagree c (by simp) t le_rfl, hagree c' (by simp) t le_rfl]
  · -- `∨`: the children and their semantics
    rename_i φ φ' hφ
    obtain ⟨hkind, c, c', hc, hψ, hψ'⟩ := hshape
    rw [hc] at hsem hval ⊢
    obtain ⟨hsc, hscv⟩ := hsem c (by simp)
    obtain ⟨hsc', hscv'⟩ := hsem c' (by simp)
    have hv := hval c (by simp)
    have hv' := hval c' (by simp)
    rw [hφ] at hk
    simp only [OnlineReachSetAnalyzer.Formula.sat, ← hψ, ← hψ', hsc, hsc', Option.bind_some] at hk
    -- the disjunction of the children's signals, and of their semantics
    obtain ⟨a, ha, hav, ha'⟩ := FourValuedSignal.at_or_two ![(get c).signal, (get c').signal]
      (by intro k; fin_cases k <;> simpa)
    obtain ⟨b, hb, -, hb'⟩ := FourValuedSignal.at_or_two ![sem c, sem c']
      (by intro k; fin_cases k <;> simpa)
    rw [hb] at hk; cases hk
    -- `Combine` computes it; refinement and agreement are pointwise
    refine ⟨a, ?_, hav, ?_, ?_⟩
    · simp only [OnlineAnalyzerNode.combine, hkind, List.map_cons, List.map_nil]
      rw [if_neg (by simp)]
      rw [← ha]; congr 1; funext i; fin_cases i <;> rfl
    · intro hr t ht hne
      rw [ha' t ht] at hne ⊢; rw [hb' t ht]
      exact FourValued.or_refines _ _ _ _ (hr c (by simp) t ht) (hr c' (by simp) t ht) hne
    · intro t ht hagree
      rw [ha' t ht, hb' t ht]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hagree c (by simp) t le_rfl, hagree c' (by simp) t le_rfl]
  · -- `U_I`: the children and their semantics
    rename_i I φ φ' hφ
    obtain ⟨hkind, hI, c, c', hc, hψ, hψ'⟩ := hshape
    rw [hc] at hsem hval ⊢
    obtain ⟨hsc, hscv⟩ := hsem c (by simp)
    obtain ⟨hsc', hscv'⟩ := hsem c' (by simp)
    have hv := hval c (by simp)
    have hv' := hval c' (by simp)
    rw [hφ] at hk
    simp only [OnlineReachSetAnalyzer.Formula.sat, ← hψ, ← hψ', hsc, hsc', Option.bind_some] at hk
    -- the until refines, and reads only times from `t` on
    obtain ⟨a, b, ha, hb, hav, -, hab, hcaus⟩ := FourValuedSignal.until_refines (get c).signal
      (get c').signal (sem c) (sem c') hv hv' hscv hscv' I
    rw [hb] at hk; cases hk
    refine ⟨a, by simp [OnlineAnalyzerNode.combine, hkind, hI, ha], hav, ?_, ?_⟩
    · intro hr
      exact hab (hr c (by simp)) (hr c' (by simp))
    · intro t ht hagree
      exact hcaus t ht fun x hx => ⟨hagree c (by simp) x hx, hagree c' (by simp) x hx⟩

/-- `P` is empty or starts at `0`, closed: an initial stretch of time. -/
private def aux_IsPrefix (P : STLInterval ℝ) : Prop :=
  P = .empty ∨ ∃ u rc h1 h2 h3, P = .nonempty (0 : ℝ) u true rc h1 h2 h3

/-- The times `x ≥ 0` below the bound `b`, or at it when it is closed. -/
private def aux_bnd (b : WithTop ℝ × Bool) : Set ℝ :=
  {x | 0 ≤ x ∧ ((x : EReal) < STLInterval.toEReal b.1 ∨ (b.2 = true ∧ (x : EReal) =
      STLInterval.toEReal b.1))}

/-- A closed prefix holds `x` iff `x ≥ 0` is below its bound. -/
private theorem aux_prefix_set (u : WithTop ℝ) (rc : Bool) h1 h2 h3 (x : ℝ) : -- --- CONCL ---
    x ∈ (STLInterval.nonempty (0 : ℝ) u true rc h1 h2 h3).set ↔ x ∈ aux_bnd (u, rc)
    := by -- --- PROOF ---
  simp only [STLInterval.set, STLInterval.rawSet, aux_bnd, Set.mem_setOf_eq, toReal_real,
    true_and]
  constructor
  · rintro ⟨h | h, h'⟩
    · exact ⟨by exact_mod_cast h.le, h'⟩
    · exact ⟨by exact_mod_cast h.le, h'⟩
  · rintro ⟨h, h'⟩
    refine ⟨?_, h'⟩
    rcases h.lt_or_eq with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h

/-- The bound `propBound` folds to is the intersection of the prefixes in `l`. -/
private theorem aux_propBound_set (l : List (STLInterval ℝ))
    (hl : ∀ P ∈ l, aux_IsPrefix P) : -- --- CONCL ---
    ∀ (acc : WithTop ℝ × Bool) (x : ℝ), x ∈ aux_bnd (OnlineAnalyzerNode.propBound 0 l acc) ↔
      x ∈ aux_bnd acc ∧ ∀ P ∈ l, x ∈ P.set := by -- --- PROOF ---
  induction l with
  | nil => intro acc x; simp [OnlineAnalyzerNode.propBound]
  | cons P rest ih =>
    intro acc x
    rcases hl P (by simp) with rfl | ⟨u, rc, h1, h2, h3, rfl⟩
    · simp [OnlineAnalyzerNode.propBound, aux_bnd, STLInterval.set_empty]
      intro h; change ((0:ℝ) : EReal) ≤ x; exact_mod_cast h
    · obtain ⟨ub, rcb⟩ := acc
      have ih' := ih (fun P hP => hl P (by simp [hP]))
      simp only [OnlineAnalyzerNode.propBound, STLInterval.withinTol_zero]
      simp only [List.mem_cons, forall_eq_or_imp, aux_prefix_set]
      -- the accumulated bound is kept when it is the smaller one
      split_ifs with hc
      · rw [ih']
        -- the invariant, field by field, from the summary
        constructor
        · rintro ⟨hx, hr⟩
          refine ⟨⟨hx.1, ?_⟩, hx, hr⟩
          rcases hc with hc | ⟨hc, hrc⟩
          · rcases hx.2 with h | ⟨-, h⟩
            · left; exact h.trans hc
            · left; rw [h]; exact hc
          · rcases hx.2 with h | ⟨h', h⟩
            · left; rw [← hc]; exact h
            · simp [hrc] at h'
        · rintro ⟨-, hx, hr⟩; exact ⟨hx, hr⟩
      · rw [ih']
        -- the new prefix is shorter: its bound replaces the accumulated one
        push Not at hc
        constructor
        · rintro ⟨hx, hr⟩
          refine ⟨hx, ⟨hx.1, ?_⟩, hr⟩
          rcases hc.1.lt_or_eq with h | h
          · rcases hx.2 with h' | ⟨-, h'⟩
            · left; exact h'.trans h
            · left; rw [h']; exact h
          · have hrc := hc.2 h.symm
            rcases hx.2 with h' | ⟨-, h'⟩
            · left; rw [← h]; exact h'
            · right; exact ⟨by simpa using hrc, h' ▸ h.symm ▸ rfl⟩
        · rintro ⟨hx, -, hr⟩; exact ⟨hx, hr⟩

/-- The times a node ignores are those in every interval propagated to it. -/
private theorem aux_getAllProp_set (n : OnlineAnalyzerNode ℝ A) (hp : ∀ P ∈ n.prop, aux_IsPrefix P)
    (x : ℝ) : -- --- CONCL ---
    x ∈ (OnlineAnalyzerNode.getAllProp 0 n).set ↔ 0 ≤ x ∧ ∀ P ∈ n.prop, x ∈ P.set
    := by -- --- PROOF ---
  have h := aux_propBound_set n.prop hp (⊤, true) x
  unfold OnlineAnalyzerNode.getAllProp
  rw [STLInterval.set_stlInterval]
  have e : x ∈ STLInterval.rawSet (toReal (0 : ℝ) : ℝ)
      (STLInterval.toEReal (OnlineAnalyzerNode.propBound 0 n.prop (⊤, true)).1) true
      (OnlineAnalyzerNode.propBound 0 n.prop (⊤, true)).2 ↔
      x ∈ aux_bnd (OnlineAnalyzerNode.propBound 0 n.prop (⊤, true)) := by
    simp only [STLInterval.rawSet, aux_bnd, Set.mem_setOf_eq, toReal_real, true_and]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact ⟨by exact_mod_cast h.le, h'⟩
      · exact ⟨by exact_mod_cast h.le, h'⟩
    · rintro ⟨h, h'⟩
      refine ⟨?_, h'⟩
      rcases h.lt_or_eq with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
  rw [e, h]
  simp [aux_bnd, STLInterval.toEReal]


/-- A conclusive interval is a closed prefix. -/
private theorem aux_conclusiveInterval_isPrefix (s : FourValuedSignal ℝ) (ign : STLInterval ℝ) :
    aux_IsPrefix (s.conclusiveInterval ign) := by
  unfold FourValuedSignal.conclusiveInterval STLInterval.stlIntervalBounds STLInterval.stlInterval
  dsimp only
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr ⟨_, _, _, _, _, rfl⟩

/-- A prefix holding `t` holds every `x ∈ [0, t]`. -/
private theorem aux_isPrefix_downClosed (P : STLInterval ℝ) (hP : aux_IsPrefix P) (t : ℝ)
    (ht : t ∈ P.set)
    (x : ℝ) (hx : 0 ≤ x) (hxt : x ≤ t) : -- --- CONCL ---
    x ∈ P.set
    := by -- --- PROOF ---
  rcases hP with rfl | ⟨u, rc, h1, h2, h3, rfl⟩
  · simp [STLInterval.set_empty] at ht
  · rw [aux_prefix_set] at ht ⊢
    refine ⟨hx, ?_⟩
    rcases hxt.lt_or_eq with h | h
    · left
      have h' : (x : EReal) < t := by exact_mod_cast h
      rcases ht.2 with h2 | ⟨-, h2⟩
      · exact h'.trans h2
      · rw [← h2]; exact h'
    · subst h; exact ht.2

/-- An entry `setPropagated` accepts contains the old one: it refuses a shrink. -/
private theorem aux_grow (old new : STLInterval ℝ) (ho : aux_IsPrefix old) (hn : aux_IsPrefix new)
    (h : ¬ (¬ STLInterval.isequal 0 old new ∧ STLInterval.contains_ 0 old new)) : -- --- CONCL ---
    old.set ⊆ new.set := by -- --- PROOF ---
  rcases ho with rfl | ⟨u, rc, h1, h2, h3, rfl⟩
  · simp [STLInterval.set_empty]
  · rcases hn with rfl | ⟨u', rc', h1', h2', h3', rfl⟩
    · exact absurd ⟨by simp [STLInterval.isequal], by simp [STLInterval.contains_]⟩ h
    · intro x hx
      rw [aux_prefix_set] at hx ⊢
      refine ⟨hx.1, ?_⟩
      simp only [STLInterval.isequal, STLInterval.contains_, STLInterval.withinTol_zero,
        toReal_real, not_and, not_or, true_or, and_true, lt_self_iff_false, false_or,
        true_and] at h
      by_cases he : STLInterval.toEReal u = STLInterval.toEReal u' ∧ rc = rc'
      · rw [← he.1, ← he.2]; exact hx.2
      · have h' := (h (fun h0 h1 => he ⟨h0, h1⟩))
        push Not at h'
        -- the new bound is larger, or equal and closed where the old one is
        rcases h'.1.lt_or_eq with hlt | heq
        · rcases hx.2 with hx2 | ⟨-, hx2⟩
          · left; exact hx2.trans hlt
          · left; rw [hx2]; exact hlt
        · obtain ⟨hrc, hrc'⟩ := h'.2 heq
          rcases hx.2 with hx2 | ⟨hr, hx2⟩
          · left; rw [← heq]; exact hx2
          · simp only at hr; simp [hr] at hrc

/-- `setPropagated` stores `P` as parent `p`'s entry, refusing a shrink, and erases the ignored
times when the node drops them. -/
private theorem aux_setPropagated_spec (c c' : OnlineAnalyzerNode ℝ A) (p : ℕ) (P : STLInterval ℝ)
    (h : c.setPropagated 0 p P = some c') : -- --- CONCL ---
    ∃ old, c.prop[c.parents.idxOf p]? = some old ∧
      ¬ (¬ STLInterval.isequal 0 old P ∧ STLInterval.contains_ 0 old P) ∧
      c' = { c with
        prop := c.prop.set (c.parents.idxOf p) P
        signal := if c.dropPropagated then c.signal.set (OnlineAnalyzerNode.getAllProp 0
          { c with prop := c.prop.set (c.parents.idxOf p) P }) .ii else c.signal }
    := by -- --- PROOF ---
  unfold OnlineAnalyzerNode.setPropagated at h
  dsimp only at h
  split at h
  · cases h
  · rename_i old hold
    refine ⟨old, hold, ?_⟩
    split_ifs at h with h1 h2 <;> cases h
    all_goals first | exact ⟨h1, by rw [if_pos h2]⟩ | exact ⟨h1, by rw [if_neg h2]⟩

/-- A leaf propagates nothing. -/
private theorem aux_propagate_leaf (n : OnlineAnalyzerNode ℝ A) (cs : List (OnlineAnalyzerNode ℝ A))
    (hk : n.kind = .true ∨ n.kind = .false ∨ n.kind = .ap) :
    n.propagate 0 cs .empty = some (n, cs) := by
  rcases hk with hk | hk | hk <;> simp only [OnlineAnalyzerNode.propagate, hk]
  split <;> simp_all

/-- An inner node merges `Δ = Combine` into its signal and passes its conclusive interval down. -/
private theorem aux_propagate_inner (n : OnlineAnalyzerNode ℝ A)
    (cs : List (OnlineAnalyzerNode ℝ A))
    (r : OnlineAnalyzerNode ℝ A × List (OnlineAnalyzerNode ℝ A))
    (hk : n.kind ≠ .true ∧ n.kind ≠ .false ∧ n.kind ≠ .ap)
    (h : n.propagate 0 cs .empty = some r) : -- --- CONCL ---
    ∃ Δ, n.combine cs = some Δ ∧ r.1 = { n with signal := n.signal.merge Δ } ∧
      cs.mapM (fun c => c.setPropagated 0 n.idx
        ((n.signal.merge Δ).conclusiveInterval (OnlineAnalyzerNode.getAllProp 0 n))) = some r.2
    := by -- --- PROOF ---
  unfold OnlineAnalyzerNode.propagate at h
  split at h
  · exact absurd ‹_› hk.1
  · exact absurd ‹_› hk.2.1
  · exact absurd ‹_› hk.2.2
  · obtain ⟨Δ, hΔ, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨cs', hcs, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨Δ, hΔ, rfl, hcs⟩


/-- A successful `mapM` relates each input to its output. -/
private theorem aux_mapM_forall₂ {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), l.mapM f = some l' → List.Forall₂ (fun a b => f a = some b) l l'
  | [], l', h => by simp at h; subst h; exact List.Forall₂.nil
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hfa, hl] at h
      | some bs =>
        simp [hfa, hl] at h; subst h
        exact List.Forall₂.cons hfa (aux_mapM_forall₂ f l bs hl)

/-- Writing `bs` at the positions `cl` puts at `j` an element related to `j + 1` if `j + 1 ∈ cl`,
and leaves it otherwise. -/
private theorem aux_foldl_set {B : Type} (R : ℕ → B → Prop) :
    ∀ (cl : List ℕ) (bs : List B), List.Forall₂ R cl bs → ∀ (base : List B),
      (∀ c ∈ cl, 1 ≤ c ∧ c - 1 < base.length) →
      ((cl.zip bs).foldl (fun ns p => ns.set (p.1 - 1) p.2) base).length = base.length ∧
      ∀ j, j < base.length →
        (j + 1 ∈ cl → ∃ b, ((cl.zip bs).foldl (fun ns p => ns.set (p.1 - 1) p.2) base)[j]? =
          some b ∧ R (j + 1) b) ∧
        (j + 1 ∉ cl → ((cl.zip bs).foldl (fun ns p => ns.set (p.1 - 1) p.2) base)[j]? = base[j]?)
  | [], [], _, base, _ => by simp
  | c :: cl, b :: bs, h, base, hcl => by
    cases h with
    | cons hR h =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      have hc := hcl c (by simp)
      obtain ⟨ih1, ih2⟩ := aux_foldl_set R cl bs h (base.set (c - 1) b)
        (fun c' hc' => by simpa using hcl c' (by simp [hc']))
      simp only [List.length_set] at ih1 ih2
      -- the head is written first, the rest of the fold overwrites it only at its own positions
      refine ⟨ih1, fun j hj => ⟨fun hmem => ?_, fun hmem => ?_⟩⟩
      · by_cases hin : j + 1 ∈ cl
        · exact (ih2 j hj).1 hin
        · rw [(ih2 j hj).2 hin]
          have : c = j + 1 := by -- `c` is the one index of the head
            rcases List.mem_cons.1 hmem with h | h
            · exact h.symm
            · exact absurd h hin
          subst this
          exact ⟨b, by simp [hj], hR⟩
      · rw [(ih2 j hj).2 (fun h' => hmem (by simp [h']))]
        rw [List.getElem?_set_ne]
        intro h'; apply hmem; simp; left; omega

/-- Writing the entry of parent `k` leaves the entry of every other parent. -/
private theorem aux_entry_other (prop : List (STLInterval ℝ)) (parents : List ℕ) (v : STLInterval ℝ)
    (p k : ℕ) (hpk : p ≠ k) (hk : k ∈ parents)
        (hlen : prop.length = parents.length) : -- --- CONCL ---
    (prop.set (parents.idxOf k) v)[parents.idxOf p]? = prop[parents.idxOf p]? := by -- --- PROOF ---
  by_cases hp : p ∈ parents
  · rw [List.getElem?_set_ne]
    intro h
    have h1 := List.getElem?_idxOf hk
    have h2 := List.getElem?_idxOf hp
    apply hpk; rw [← h, h1] at h2; exact (Option.some.inj h2).symm
  · have : parents.idxOf p = parents.length := List.idxOf_eq_length_iff.2 hp
    rw [this, List.getElem?_eq_none (by simp [hlen]), List.getElem?_eq_none (by simp [hlen])]

/-- A child's formula is smaller than the node's. -/
private theorem aux_shapeOf_lt (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A)
    (φ : OnlineReachSetAnalyzer.Formula ℝ A) (n : OnlineAnalyzerNode ℝ A)
    (h : OnlineReachSetAnalyzer.IsNodeOf ψ φ n) (c : ℕ) (hc : c ∈ n.children) : -- --- CONCL ---
    sizeOf (ψ c) < sizeOf φ := by -- --- PROOF ---
  cases φ <;> simp only [OnlineReachSetAnalyzer.IsNodeOf] at h
  · simp [h.2] at hc
  · simp [h.2] at hc
  · simp [h.2.1] at hc
  · obtain ⟨-, c0, h1, h2⟩ := h; simp [h1] at hc; subst hc; rw [h2]; simp
  · -- binary operators: either operand
    obtain ⟨-, c0, c1, h1, h2, h3⟩ := h; simp [h1] at hc
    rcases hc with rfl | rfl
    · rw [h2]; simp; omega
    · rw [h3]; simp
  · obtain ⟨-, c0, c1, h1, h2, h3⟩ := h; simp [h1] at hc
    rcases hc with rfl | rfl
    · rw [h2]; simp; omega
    · rw [h3]; simp
  · obtain ⟨-, -, c0, c1, h1, h2, h3⟩ := h; simp [h1] at hc
    rcases hc with rfl | rfl
    · rw [h2]; simp; omega
    · rw [h3]; simp

/-- Being the node of `φ` reads only the kind, the children, the interval and the atom. -/
private theorem aux_shapeOf_congr (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A)
    (φ : OnlineReachSetAnalyzer.Formula ℝ A) (n n' : OnlineAnalyzerNode ℝ A)
    (h1 : n'.kind = n.kind) (h2 : n'.children = n.children) (h3 : n'.interval = n.interval)
    (h4 : n'.ap = n.ap) (h : OnlineReachSetAnalyzer.IsNodeOf ψ φ n) : -- --- CONCL ---
    OnlineReachSetAnalyzer.IsNodeOf ψ φ n' := by -- --- PROOF ---
  cases φ <;> simp only [OnlineReachSetAnalyzer.IsNodeOf] at h ⊢ <;> rw [h1, h2] <;>
    (try rw [h4]) <;> (try rw [h3]) <;> exact h


/-- What propagating an interval `P` from parent `k` does to a child `x`. -/
private theorem aux_child_update (x b : OnlineAnalyzerNode ℝ A) (k : ℕ) (P : STLInterval ℝ)
    (sem : FourValuedSignal ℝ) (hb : x.setPropagated 0 k P = some b)
    (hpre : ∀ Q ∈ x.prop, aux_IsPrefix Q) (hP : aux_IsPrefix P) (hv : x.signal.IsValid)
    (hlen : x.prop.length = x.parents.length) : -- --- CONCL ---
    b.kind = x.kind ∧ b.idx = x.idx ∧ b.parents = x.parents ∧ b.children = x.children ∧
    b.interval = x.interval ∧ b.ap = x.ap ∧ b.prop.length = x.prop.length ∧
    b.dropPropagated = x.dropPropagated ∧ b.signal.IsValid ∧
    (sem.Refines x.signal → sem.Refines b.signal) ∧ (∀ Q ∈ b.prop, aux_IsPrefix Q) ∧
    (OnlineAnalyzerNode.getAllProp 0 x).set ⊆ (OnlineAnalyzerNode.getAllProp 0 b).set ∧
    (∀ t : ℝ, 0 ≤ t → t ∉ (OnlineAnalyzerNode.getAllProp 0 b).set → b.signal.at t = x.signal.at t) ∧
    k ∈ x.parents ∧ b.prop[x.parents.idxOf k]? = some P ∧
    (∀ p, p ≠ k → b.prop[x.parents.idxOf p]? = x.prop[x.parents.idxOf p]?) := by -- --- PROOF ---
  obtain ⟨old, hold, hgrow, rfl⟩ := aux_setPropagated_spec x b k P hb
  -- `k` is a parent, and the new entries are prefixes
  have hi : x.parents.idxOf k < x.prop.length := (List.getElem?_eq_some_iff.1 hold).1
  have hk : k ∈ x.parents := by
    by_contra hk; rw [List.idxOf_eq_length_iff.2 hk] at hi; omega
  have hpre' : ∀ Q ∈ x.prop.set (x.parents.idxOf k) P, aux_IsPrefix Q := by
    intro Q hQ
    rcases List.mem_or_eq_of_mem_set hQ with h | h
    · exact hpre Q h
    · rw [h]; exact hP
  have hold_pre : aux_IsPrefix old := hpre old (List.mem_of_getElem? hold)
  have hsub := aux_grow old P hold_pre hP hgrow
  -- the ignored times only grow
  set E := OnlineAnalyzerNode.getAllProp 0 { x with prop := x.prop.set (x.parents.idxOf k) P }
    with hEdef
  have hE : (OnlineAnalyzerNode.getAllProp 0 x).set ⊆ E.set := by
    intro t ht
    rw [aux_getAllProp_set _ hpre] at ht
    rw [aux_getAllProp_set _ hpre']
    refine ⟨ht.1, fun Q hQ => ?_⟩
    rcases List.mem_or_eq_of_mem_set hQ with h | h
    · exact ht.2 Q h
    · rw [h]; exact hsub (ht.2 old (List.mem_of_getElem? hold))
  obtain ⟨hsv, hs⟩ := FourValuedSignal.set_spec x.signal hv E .ii
  -- only `prop` and `signal` change; the signal is erased on the ignored times at most
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp, rfl, ?_, ?_, hpre', ?_, ?_, hk, ?_, ?_⟩
  · dsimp only; split_ifs <;> assumption
  · intro hr t ht hne
    dsimp only at hne ⊢
    split_ifs at hne ⊢ with hd
    · by_cases htE : t ∈ E.set
      · rw [(hs t ht).1 htE] at hne; exact absurd rfl hne
      · rw [(hs t ht).2 htE] at hne ⊢; exact hr t ht hne
    · exact hr t ht hne
  · exact hE
  · intro t ht htE
    dsimp only
    split_ifs
    · exact (hs t ht).2 htE
    · rfl
  · simp [hi]
  · intro p hp
    exact aux_entry_other x.prop x.parents P p k hp hk hlen


/-- The nodes are the syntax DAG of `ψ`: node `j + 1` is that of `ψ (j + 1)`, and each child has it
as a parent. -/
private def aux_IsDag (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A)
    (nodes : List (OnlineAnalyzerNode ℝ A)) : Prop :=
  ∀ j (h : j < nodes.length), nodes[j].idx = j + 1 ∧
    OnlineReachSetAnalyzer.IsNodeOf ψ (ψ (j + 1)) nodes[j] ∧
    nodes[j].prop.length = nodes[j].parents.length ∧
    ∀ c ∈ nodes[j].children, 1 ≤ c ∧ ∃ hc : c - 1 < nodes.length, j + 1 ∈ nodes[c - 1].parents

/-- Outside the ignored times, the node's signal is `sem k`. -/
private def aux_Complete (sem : ℕ → FourValuedSignal ℝ) (n : OnlineAnalyzerNode ℝ A) (k : ℕ) :
    Prop :=
  ∀ t : ℝ, 0 ≤ t → t ∉ (OnlineAnalyzerNode.getAllProp 0 n).set → n.signal.at t = (sem k).at t

/-- The semantics of the nodes' formulas. -/
private def aux_SemOk (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A) (sig : A → FourValuedSignal ℝ)
    (sem : ℕ → FourValuedSignal ℝ) (len : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ len → (ψ i).sat sig = some (sem i) ∧ (sem i).IsValid

private structure aux_Inv (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A)
    (sem : ℕ → FourValuedSignal ℝ)
    (nodes : List (OnlineAnalyzerNode ℝ A)) (flags : List Bool) : Prop where
  len : flags.length = nodes.length
  dag : aux_IsDag ψ nodes
  valid : ∀ j (h : j < nodes.length), nodes[j].signal.IsValid
  sound : ∀ j (h : j < nodes.length), (sem (j + 1)).Refines nodes[j].signal
  pre : ∀ j (h : j < nodes.length), ∀ P ∈ nodes[j].prop, aux_IsPrefix P
  guard : ∀ j (h : j < nodes.length), ∀ c ∈ nodes[j].children, ∀ (hc : c - 1 < nodes.length)
    (P : STLInterval ℝ), nodes[c - 1].prop[nodes[c - 1].parents.idxOf (j + 1)]? = some P →
    ∀ t : ℝ, 0 ≤ t → t ∉ (OnlineAnalyzerNode.getAllProp 0 nodes[j]).set →
      nodes[j].signal.at t = .ii → t ∉ P.set
  flag : ∀ j (h : j < nodes.length), flags[j]? = some true → aux_Complete sem nodes[j] (j + 1)
  leaf : ∀ j (h : j < nodes.length), nodes[j].children = [] → aux_Complete sem nodes[j] (j + 1)
  root : ∀ h : 0 < nodes.length, nodes[0].parents = [0] ∧ nodes[0].prop = [.empty]

/-- Propagating at the inner node `k`, whose children are complete: merge `Δ`, pass the conclusive
interval to the children, flag `k`; the invariant holds after. -/
private theorem aux_step_inner (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A)
    (sig : A → FourValuedSignal ℝ)
    (sem : ℕ → FourValuedSignal ℝ) (nodes : List (OnlineAnalyzerNode ℝ A)) (flags : List Bool)
    (hsem : aux_SemOk ψ sig sem nodes.length) (inv : aux_Inv ψ sem nodes flags) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k - 1 < nodes.length) (hinner : nodes[k - 1].children ≠ [])
    (hch : ∀ c ∈ nodes[k - 1].children, flags[c - 1]? = some true) (Δ : FourValuedSignal ℝ)
    (hΔ : nodes[k - 1].combine
      (nodes[k - 1].children.map fun c => nodes[c - 1]?.getD nodes[k - 1]) = some Δ)
    (hsucc : ∀ c ∈ nodes[k - 1].children, ∃ b, (nodes[c - 1]?.getD nodes[k - 1]).setPropagated 0 k
      ((nodes[k - 1].signal.merge Δ).conclusiveInterval
        (OnlineAnalyzerNode.getAllProp 0 nodes[k - 1])) = some b) : -- --- CONCL ---
    aux_Inv ψ sem (nodes.mapIdx fun j x => if j + 1 ∈ nodes[k - 1].children then
      (x.setPropagated 0 k ((nodes[k - 1].signal.merge Δ).conclusiveInterval
        (OnlineAnalyzerNode.getAllProp 0 nodes[k - 1]))).getD x
      else if j = k - 1 then { nodes[k - 1] with signal := nodes[k - 1].signal.merge Δ } else x)
      (flags.set (k - 1) true) := by -- --- PROOF ---
  set n := nodes[k - 1] with hn
  set conc := (n.signal.merge Δ).conclusiveInterval (OnlineAnalyzerNode.getAllProp 0 n) with hconc
  set m : OnlineAnalyzerNode ℝ A := { n with signal := n.signal.merge Δ } with hm
  obtain ⟨hnidx, hnshape, hnlen, hnch⟩ := inv.dag (k - 1) hk
  have hk' : k - 1 + 1 = k := by omega
  rw [hk'] at hnidx hnshape
  have hkch : k ∉ n.children := fun h => by
    have := aux_shapeOf_lt ψ _ n hnshape k h; omega
  -- the children and their nodes
  have hcb : ∀ c ∈ n.children, 1 ≤ c ∧ c - 1 < nodes.length := by
    intro c hc
    obtain ⟨h1, h2, -⟩ := hnch c hc
    exact ⟨h1, h2⟩
  have hget : ∀ c ∈ n.children, ∀ h : c - 1 < nodes.length,
      nodes[c - 1]?.getD n = nodes[c - 1] := by
    intro c _ h; simp [h]
  -- the delta
  obtain ⟨Δ', hΔ', hΔv, hΔr, hΔc⟩ := aux_combine_spec ψ sig sem k n
    (fun c => nodes[c - 1]?.getD n) hnshape (hsem k hk1 (by omega)).1
    (fun c hc => hsem c (hcb c hc).1 (by have := (hcb c hc).2; omega))
    (fun c hc => by rw [hget c hc (hcb c hc).2]; exact inv.valid _ _) hinner
  rw [hΔ] at hΔ'; cases hΔ'
  have hsc : ∀ c ∈ n.children, (sem c).Refines (nodes[c - 1]?.getD n).signal := by
    intro c hc
    rw [hget c hc (hcb c hc).2]
    have h' := inv.sound (c - 1) (hcb c hc).2
    have e : c - 1 + 1 = c := by have := (hcb c hc).1; omega
    rwa [e] at h'
  have hnv := inv.valid (k - 1) hk
  obtain ⟨hmv, hmerge⟩ := FourValuedSignal.merge_spec n.signal Δ hnv hΔv
  have hconc_pre : aux_IsPrefix conc := aux_conclusiveInterval_isPrefix _ _
  -- the summary of every position
  have summ : ∀ j (h : j < nodes.length),
      let y := (if j + 1 ∈ n.children then (nodes[j].setPropagated 0 k conc).getD nodes[j]
        else if j = k - 1 then m else nodes[j])
      y.kind = nodes[j].kind ∧ y.idx = nodes[j].idx ∧ y.parents = nodes[j].parents ∧
      y.children = nodes[j].children ∧ y.interval = nodes[j].interval ∧ y.ap = nodes[j].ap ∧
      y.prop.length = nodes[j].prop.length ∧ y.signal.IsValid ∧
      (sem (j + 1)).Refines y.signal ∧ (∀ Q ∈ y.prop, aux_IsPrefix Q) ∧
      (j ≠ k - 1 → (OnlineAnalyzerNode.getAllProp 0 nodes[j]).set ⊆
        (OnlineAnalyzerNode.getAllProp 0 y).set ∧ ∀ t : ℝ, 0 ≤ t →
          t ∉ (OnlineAnalyzerNode.getAllProp 0 y).set → y.signal.at t = nodes[j].signal.at t) ∧
      (∀ p, p ≠ k → y.prop[y.parents.idxOf p]? = nodes[j].prop[nodes[j].parents.idxOf p]?) ∧
      (j + 1 ∈ n.children → y.prop[y.parents.idxOf k]? = some conc) ∧
      (j = k - 1 → y = m) := by
    intro j h y
    by_cases hj : j + 1 ∈ n.children
    · -- a child: `setPropagated` with the conclusive interval
      obtain ⟨b, hb⟩ := hsucc (j + 1) hj
      rw [hget (j + 1) hj (by omega)] at hb
      simp only [Nat.add_sub_cancel] at hb
      have hy : y = b := by simp only [y, if_pos hj, hb, Option.getD_some]
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, -, e9, e10, e11, e12, e13, -, e15, e16⟩ :=
        aux_child_update nodes[j] b k conc (sem (j + 1)) hb (inv.pre j h) hconc_pre
          (inv.valid j h) (inv.dag j h).2.2.1
      have hjk : j ≠ k - 1 := fun e => hkch (by rw [e] at hj; rwa [hk'] at hj)
      rw [hy]
      refine ⟨e1, e2, e3, e4, e5, e6, e7, e9, e10 (inv.sound j h), e11, fun _ => ⟨e12, e13⟩,
        fun p hp => by rw [e3]; exact e16 p hp, fun _ => by rw [e3]; exact e15,
        fun e => absurd e hjk⟩
    · by_cases hjk : j = k - 1
      · subst hjk
        -- the node itself: its signal merged with `Δ`, which the semantics refines
        have hy : y = m := by simp only [y, if_neg hj, ↓reduceIte]
        rw [hy]
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hmv, ?_, inv.pre _ h, fun e => absurd rfl e,
          fun _ _ => rfl, fun e => absurd e hj, fun _ => rfl⟩
        rw [hk']
        exact aux_merge_refines _ _ _ hnv hΔv (by rw [← hk']; exact inv.sound _ h)
          (hΔr hsc)
      · -- any other node is untouched
        have hy : y = nodes[j] := by simp only [y, if_neg hj, if_neg hjk]
        rw [hy]
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, inv.valid j h, inv.sound j h, inv.pre j h,
          fun _ => ⟨le_rfl, fun _ _ _ => rfl⟩, fun _ _ => rfl, fun e => absurd e hj,
          fun e => absurd e hjk⟩
  constructor
  · simp [inv.len]
  · intro j h
    have h' : j < nodes.length := by simpa using h
    simp only [List.getElem_mapIdx]
    -- the DAG: fields and graph are kept
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, -, -, -, -, -, -, -⟩ := summ j h'
    obtain ⟨d1, d2, d3, d4⟩ := inv.dag j h'
    refine ⟨by rw [s2]; exact d1, aux_shapeOf_congr ψ _ _ _ s1 s4 s5 s6 d2,
      by rw [s7, s3]; exact d3, fun c hc => ?_⟩
    rw [s4] at hc
    -- each child is in range and keeps the node as a parent
    obtain ⟨c1, c2, c3⟩ := d4 c hc
    -- a child keeps its parents
    refine ⟨c1, by simpa using c2, ?_⟩
    try simp only [List.getElem_mapIdx]
    rw [(summ (c - 1) c2).2.2.1]; exact c3
  · intro j h
    have h' : j < nodes.length := by simpa using h
    simp only [List.getElem_mapIdx]
    -- valid, sound and prefixes, from the summary
    exact (summ j h').2.2.2.2.2.2.2.1
  · intro j h
    have h' : j < nodes.length := by simpa using h
    simp only [List.getElem_mapIdx]
    exact (summ j h').2.2.2.2.2.2.2.2.1
  · intro j h
    have h' : j < nodes.length := by simpa using h
    simp only [List.getElem_mapIdx]
    exact (summ j h').2.2.2.2.2.2.2.2.2.1
  · -- the guard
    intro j h c hc hc' P hP t ht htE hii
    have h' : j < nodes.length := by simpa using h
    have hc'' : c - 1 < nodes.length := by simpa using hc'
    simp only [List.getElem_mapIdx] at hc hP htE hii
    obtain ⟨-, -, -, s4, -, -, -, -, -, -, s11, s12, -, s14⟩ := summ j h'
    obtain ⟨-, -, c3, -, -, -, -, -, -, -, -, c12, c13, -⟩ := summ (c - 1) hc''
    try rw [s4] at hc
    by_cases hjk : j = k - 1
    · -- the node itself: the new interval is its conclusive one
      subst hjk
      have hy := s14 rfl
      rw [hy] at htE hii
      have hcm : c - 1 + 1 ∈ n.children := by
        have := (hcb c hc).1; rw [show c - 1 + 1 = c by omega]; exact hc
      have c13' := c13 hcm
      rw [hk'] at hP
      have hP' := c13'.symm.trans hP
      cases hP'
      intro hmem
      have := (FourValuedSignal.conclusiveInterval_spec _ hmv _ t).1 hmem
      rcases this.2 t ht le_rfl with h1 | h1
      · exact htE h1
      · exact h1 hii
    · -- another node: its entries and signal are the old ones outside its ignored times
      have c12' := c12 (j + 1) (by omega)
      rw [c3] at c12'
      obtain ⟨e1, e2⟩ := s11 hjk
      exact inv.guard j h' c hc hc'' P ((c12 (j + 1) (by omega)).symm.trans hP) t ht
          (fun hm => htE (e1 hm))
        ((e2 t ht htE).symm.trans hii)
  · -- the flags
    intro j h hf
    have h' : j < nodes.length := by simpa using h
    simp only [List.getElem_mapIdx]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, s11, -, -, s14⟩ := summ j h'
    by_cases hjk : j = k - 1
    · subst hjk
      rw [s14 rfl, hk']
      intro t ht htE
      have htE' : t ∉ (OnlineAnalyzerNode.getAllProp 0 n).set := htE
      show (n.signal.merge Δ).at t = (sem k).at t
      by_cases hni : n.signal.at t = .ii
      · -- the children are complete from `t` on
        have hall : ∀ c ∈ n.children, ∀ x, t ≤ x →
            (nodes[c - 1]?.getD n).signal.at x = (sem c).at x := by
          intro c hc x hx
          obtain ⟨c1, c2, c3⟩ := hnch c hc
          rw [hget c hc c2]
          -- the child's entry for the node `k`
          have hlenc := (inv.dag (c - 1) c2).2.2.1
          have hi : nodes[c - 1].parents.idxOf (k - 1 + 1) < nodes[c - 1].prop.length := by
            rw [hlenc]; exact List.idxOf_lt_length_of_mem c3
          have hP : nodes[c - 1].prop[nodes[c - 1].parents.idxOf (k - 1 + 1)]? =
              some (nodes[c - 1].prop[nodes[c - 1].parents.idxOf (k - 1 + 1)]) :=
            List.getElem?_eq_getElem hi
          -- by the guard, `t` and so every `x ≥ t` lies outside the child's entry
          have htP := inv.guard (k - 1) hk c hc c2 _ hP t ht htE' hni
          have hPpre := inv.pre _ c2 _ (List.getElem_mem hi)
          have hxP : x ∉ (nodes[c - 1].prop[nodes[c - 1].parents.idxOf (k - 1 + 1)]).set :=
            fun hm => htP (aux_isPrefix_downClosed _ hPpre x hm t ht hx)
          have hxE : x ∉ (OnlineAnalyzerNode.getAllProp 0 nodes[c - 1]).set := fun hm =>
            hxP (((aux_getAllProp_set _ (inv.pre _ c2) x).1 hm).2 _ (List.getElem_mem hi))
          -- the child is flagged, so complete there
          have hflag := inv.flag (c - 1) c2 (hch c hc)
          have e : c - 1 + 1 = c := by omega
          rw [e] at hflag
          exact hflag x (ht.trans hx) hxE
        have hd := hΔc t ht hall
        by_cases hdi : Δ.at t = .ii
        · rw [(hmerge t ht).2 hdi, hni, ← hdi, hd]
        · rw [(hmerge t ht).1 hdi, hd]
      · -- a conclusive old value: the semantics, and `Δ` agrees where it is conclusive
        have hs := inv.sound (k - 1) hk t ht hni
        rw [hk'] at hs
        by_cases hdi : Δ.at t = .ii
        · rw [(hmerge t ht).2 hdi]; exact hs.symm
        · rw [(hmerge t ht).1 hdi]; exact (hΔr hsc t ht hdi).symm
    · -- another flagged node is untouched outside its ignored times
      rw [List.getElem?_set_ne (by omega)] at hf
      obtain ⟨e1, e2⟩ := s11 hjk
      intro t ht htE
      rw [e2 t ht htE]
      exact inv.flag j h' hf t ht (fun hm => htE (e1 hm))
  · -- the leaves
    intro j h hl
    have h' : j < nodes.length := by simpa using h
    simp only [List.getElem_mapIdx] at hl ⊢
    obtain ⟨-, -, -, s4, -, -, -, -, -, -, s11, -, -, -⟩ := summ j h'
    rw [s4] at hl
    have hjk : j ≠ k - 1 := fun e => by subst e; exact hinner hl
    obtain ⟨e1, e2⟩ := s11 hjk
    intro t ht htE
    rw [e2 t ht htE]
    exact inv.leaf j h' hl t ht (fun hm => htE (e1 hm))
  · intro h
    -- the root's entry
    have h' : 0 < nodes.length := by simpa using h
    simp only [List.getElem_mapIdx]
    -- the root: never a child, so its entry stays
    obtain ⟨r1, r2⟩ := inv.root h'
    obtain ⟨-, -, s3, -, -, -, -, -, -, -, -, -, s13, s14⟩ := summ 0 h'
    refine ⟨by rw [s3]; exact r1, ?_⟩
    by_cases hj : 0 + 1 ∈ n.children
    · exfalso
      obtain ⟨b, hb⟩ := hsucc (0 + 1) hj
      rw [hget _ hj h'] at hb
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hkp, -, -⟩ :=
        aux_child_update _ b k conc (sem 1) hb (inv.pre 0 h') hconc_pre (inv.valid 0 h')
          (inv.dag 0 h').2.2.1
      simp only [Nat.add_sub_cancel, r1, List.mem_singleton] at hkp
      omega
    · by_cases hjk : 0 = k - 1
      · rw [s14 hjk]; simp only [m, n]; simp only [← hjk]; exact r2
      · simp only [if_neg hj, if_neg hjk]; exact r2


/-- Flagging a complete node keeps the invariant. -/
private theorem aux_inv_flag (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A)
    (sem : ℕ → FourValuedSignal ℝ)
    (nodes : List (OnlineAnalyzerNode ℝ A)) (flags : List Bool) (inv : aux_Inv ψ sem nodes flags)
    (j : ℕ) (hj : j < nodes.length) (hc : aux_Complete sem nodes[j] (j + 1)) : -- --- CONCL ---
    aux_Inv ψ sem nodes (flags.set j true) := by -- --- PROOF ---
  refine ⟨by simp [inv.len], inv.dag, inv.valid, inv.sound, inv.pre, inv.guard, ?_, inv.leaf,
    inv.root⟩
  intro i hi hf
  by_cases hij : i = j
  · subst hij; exact hc
  · rw [List.getElem?_set_ne (by omega)] at hf; exact inv.flag i hi hf

/-- A node of `IsNodeOf` is a leaf of kind `true`, `false` or `ap`, or an inner node with
children. -/
private theorem aux_shape_kind (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A)
    (φ : OnlineReachSetAnalyzer.Formula ℝ A) (n : OnlineAnalyzerNode ℝ A)
    (h : OnlineReachSetAnalyzer.IsNodeOf ψ φ n) : -- --- CONCL ---
    ((n.kind = .true ∨ n.kind = .false ∨ n.kind = .ap) ∧ n.children = []) ∨
      ((n.kind ≠ .true ∧ n.kind ≠ .false ∧ n.kind ≠ .ap) ∧ n.children ≠ []) := by -- --- PROOF ---
  cases φ <;> simp only [OnlineReachSetAnalyzer.IsNodeOf] at h
  · exact Or.inl ⟨Or.inl h.1, h.2⟩
  · exact Or.inl ⟨Or.inr (Or.inl h.1), h.2⟩
  · exact Or.inl ⟨Or.inr (Or.inr h.1), h.2.1⟩
  · obtain ⟨h1, c, h2, -⟩ := h; exact Or.inr ⟨by simp [h1], by simp [h2]⟩
  · obtain ⟨h1, c, c', h2, -⟩ := h; exact Or.inr ⟨by simp [h1], by simp [h2]⟩
  · obtain ⟨h1, c, c', h2, -⟩ := h; exact Or.inr ⟨by simp [h1], by simp [h2]⟩
  · obtain ⟨h1, -, c, c', h2, -⟩ := h; exact Or.inr ⟨by simp [h1], by simp [h2]⟩

/-- `Forall₂` gives every element of the left list a partner. -/
private theorem aux_forall₂_exists {α β : Type} (R : α → β → Prop) {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') : -- --- CONCL ---
    ∀ a ∈ l, ∃ b, R a b
    := by -- --- PROOF ---
  induction h with
  | nil => simp
  | cons h _ ih =>
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, h⟩
    · exact ih a ha

/-- A `Forall₂` of `f a = some b` makes the right list the map of `f`, read with a default. -/
private theorem aux_forall₂_map {α β : Type} (f : α → Option β) (d : β) {l : List α} {l' : List β}
    (h : List.Forall₂ (fun a b => f a = some b) l l') : l' = l.map fun a => (f a).getD d := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h, ih]

/-- One step of `propagateRec` at node `k`, whose children are complete: the invariant holds after,
with node `k` flagged, and the graph is unchanged. -/
private theorem aux_step (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A) (sig : A → FourValuedSignal ℝ)
    (sem : ℕ → FourValuedSignal ℝ) (nodes : List (OnlineAnalyzerNode ℝ A)) (flags : List Bool)
    (hsem : aux_SemOk ψ sig sem nodes.length) (inv : aux_Inv ψ sem nodes flags) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k - 1 < nodes.length)
    (hch : ∀ c ∈ nodes[k - 1].children, flags[c - 1]? = some true)
    (cs : List (OnlineAnalyzerNode ℝ A))
    (hcs : nodes[k - 1].children.mapM (fun c => nodes[c - 1]?) = some cs)
    (r : OnlineAnalyzerNode ℝ A × List (OnlineAnalyzerNode ℝ A))
    (hr : nodes[k - 1].propagate 0 cs .empty = some r) : -- --- CONCL ---
    let res := (nodes[k - 1].children.zip r.2).foldl (fun ns p => ns.set (p.1 - 1) p.2)
      (nodes.set (k - 1) r.1)
    aux_Inv ψ sem res (flags.set (k - 1) true) ∧ res.length = nodes.length ∧
    ∀ j : ℕ, (res[j]?).map (fun x : OnlineAnalyzerNode ℝ A => x.children) =
      (nodes[j]?).map (fun x : OnlineAnalyzerNode ℝ A => x.children) := by -- --- PROOF ---
  intro res
  simp only [res]
  set n := nodes[k - 1] with hn
  obtain ⟨hnidx, hnshape, -, hnch⟩ := inv.dag (k - 1) hk
  have hk' : k - 1 + 1 = k := by omega
  rw [hk'] at hnidx hnshape
  have hcb : ∀ c ∈ n.children, 1 ≤ c ∧ c - 1 < nodes.length := fun c hc =>
    ⟨(hnch c hc).1, (hnch c hc).2.1⟩
  have hF := aux_mapM_forall₂ _ _ _ hcs
  -- the children's nodes
  have hcs' : cs = n.children.map fun c => nodes[c - 1]?.getD n :=
    aux_forall₂_map (fun c => nodes[c - 1]?) n hF
  rcases aux_shape_kind ψ _ n hnshape with ⟨hkind, hleaf⟩ | ⟨hkind, hinner⟩
  · -- a leaf: nothing changes but the flag
    rw [aux_propagate_leaf n cs hkind] at hr
    cases hr
    simp only [hleaf, List.zip_nil_left, List.foldl_nil]
    rw [show nodes.set (k - 1) n = nodes from List.set_getElem_self hk]
    refine ⟨aux_inv_flag ψ sem nodes flags inv (k - 1) hk ?_, rfl, fun _ => rfl⟩
    exact inv.leaf (k - 1) hk hleaf
  · obtain ⟨Δ, hΔ, hr1, hr2⟩ := aux_propagate_inner n cs r hkind hr
    -- the interval the node propagates to its children
    set ci := (n.signal.merge Δ).conclusiveInterval (OnlineAnalyzerNode.getAllProp 0 n) with hci
    rw [hcs'] at hΔ hr2
    rw [hnidx] at hr2
    have hF2 := aux_mapM_forall₂ _ _ _ hr2
    rw [List.forall₂_map_left_iff] at hF2
    have hsucc : ∀ c ∈ n.children, ∃ b, (nodes[c - 1]?.getD n).setPropagated 0 k ci = some b := by
      exact aux_forall₂_exists _ hF2
    have hmain := aux_step_inner ψ sig sem nodes flags hsem inv k hk1 hk hinner hch Δ hΔ hsucc
    -- the fold is the position-wise update
    have hfold := aux_foldl_set (fun c b => (nodes[c - 1]?.getD n).setPropagated 0 k ci = some b)
      n.children r.2 hF2 (nodes.set (k - 1) r.1) (fun c hc => by simpa using hcb c hc)
    have heq : (n.children.zip r.2).foldl (fun ns p => ns.set (p.1 - 1) p.2)
        (nodes.set (k - 1) r.1) = nodes.mapIdx fun j x => if j + 1 ∈ n.children then
          (x.setPropagated 0 k ci).getD x
          else if j = k - 1 then { n with signal := n.signal.merge Δ } else x := by
      apply List.ext_getElem?
      intro j
      by_cases hj : j < nodes.length
      · -- at a position in range: a child, the node itself, or untouched
        obtain ⟨f1, f2⟩ := hfold.2 j (by simpa using hj)
        rw [List.getElem?_mapIdx, List.getElem?_eq_getElem hj]
        simp only [Option.map_some]
        by_cases hjc : j + 1 ∈ n.children
        · obtain ⟨b, hb1, hb2⟩ := f1 hjc
          rw [hb1, if_pos hjc]
          simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem hj, Option.getD_some] at hb2
          rw [hb2]; rfl
        · rw [f2 hjc, if_neg hjc]
          by_cases hjk : j = k - 1
          · subst hjk; rw [if_pos rfl, List.getElem?_set_self hj, hr1]
          · rw [if_neg hjk, List.getElem?_set_ne (by omega), List.getElem?_eq_getElem hj]
      · rw [List.getElem?_eq_none (by rw [hfold.1]; simpa using hj),
          List.getElem?_eq_none (by simpa using hj)]
    rw [heq]
    -- the children lists are unchanged
    refine ⟨hmain, by simp, fun j => ?_⟩
    rw [List.getElem?_mapIdx]
    rcases hx : nodes[j]? with _ | x
    · rfl
    · simp only [Option.map_some]
      split_ifs with h1 h2
      · cases hb : x.setPropagated 0 k ci with
        | none => rfl
        | some b =>
          obtain ⟨-, -, -, rfl⟩ := aux_setPropagated_spec x b k _ hb
          rfl
      · subst h2
        rw [List.getElem?_eq_getElem hk] at hx
        rw [← Option.some.inj hx]
      · rfl

/-- Propagating each node of a list in turn, given that one propagation keeps the invariant and
flags its node, keeps the invariant and flags them all. -/
private theorem aux_foldl_todo {S : ℕ → Type} {d : ℕ}
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (sig : AtomicProposition S d → FourValuedSignal ℝ) (sem : ℕ → FourValuedSignal ℝ) (fuel : ℕ)
    -- one propagation keeps the invariant and flags its node
    (ih : ∀ idx (nodes : List (OnlineAnalyzerNode ℝ (AtomicProposition S d))) flags res,
      aux_SemOk ψ sig sem nodes.length → aux_Inv ψ sem nodes flags → 1 ≤ idx →
      OnlineReachSetAnalyzer.propagateRec 0 .empty fuel idx (nodes, flags) = some res →
      aux_Inv ψ sem res.1 res.2 ∧ res.1.length = nodes.length ∧
      (∀ j : ℕ, (res.1[j]?).map
          (fun x : OnlineAnalyzerNode ℝ (AtomicProposition S d) => x.children) = (nodes[j]?).map
              (fun x : OnlineAnalyzerNode ℝ (AtomicProposition S d) => x.children)) ∧
      (∀ j : ℕ, flags[j]? = some true → res.2[j]? = some true) ∧ res.2[idx - 1]? = some true) :
    -- then the fold over `L` keeps it and flags all of `L`
    ∀ (L : List ℕ) (nodes : List (OnlineAnalyzerNode ℝ (AtomicProposition S d))) flags res,
      aux_SemOk ψ sig sem nodes.length → aux_Inv ψ sem nodes flags → (∀ c ∈ L, 1 ≤ c) →
      L.foldlM (fun st c => OnlineReachSetAnalyzer.propagateRec 0 .empty fuel c st)
        (nodes, flags) = some res →
      aux_Inv ψ sem res.1 res.2 ∧ res.1.length = nodes.length ∧
      (∀ j : ℕ, (res.1[j]?).map
          (fun x : OnlineAnalyzerNode ℝ (AtomicProposition S d) => x.children) = (nodes[j]?).map
              (fun x : OnlineAnalyzerNode ℝ (AtomicProposition S d) => x.children)) ∧
      (∀ j : ℕ, flags[j]? = some true → res.2[j]? = some true) ∧ ∀ c ∈ L, res.2[c - 1]? = some true
  | [], nodes, flags, res, _, inv, _, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨inv, rfl, fun _ => rfl, fun _ h => h, by simp⟩
  | c :: L, nodes, flags, res, hsem, inv, hL, h => by
    simp only [List.foldlM_cons] at h
    -- the head, then the rest from its state
    obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih c nodes flags st hsem inv (hL c (by simp)) hst
    obtain ⟨j1, j2, j3, j4, j5⟩ := aux_foldl_todo ψ sig sem fuel ih L st.1 st.2 res
      (by rw [i2]; exact hsem) i1 (fun c' hc' => hL c' (by simp [hc'])) h
    refine ⟨j1, by rw [j2, i2], fun j => by rw [j3, i3], fun j hj => j4 j (i4 j hj), ?_⟩
    intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact j4 _ i5
    · exact j5 c' hc'

/-- `propagateRec` from node `idx` keeps the invariant, the graph and the flags set before, and
flags `idx`. -/
private theorem aux_propagateRec {S : ℕ → Type} {d : ℕ}
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (sig : AtomicProposition S d → FourValuedSignal ℝ) (sem : ℕ → FourValuedSignal ℝ) :
    ∀ fuel idx (nodes : List (OnlineAnalyzerNode ℝ (AtomicProposition S d))) flags res,
      aux_SemOk ψ sig sem nodes.length → aux_Inv ψ sem nodes flags → 1 ≤ idx →
      OnlineReachSetAnalyzer.propagateRec 0 .empty fuel idx (nodes, flags) = some res →
      aux_Inv ψ sem res.1 res.2 ∧ res.1.length = nodes.length ∧
      (∀ j : ℕ, (res.1[j]?).map
          (fun x : OnlineAnalyzerNode ℝ (AtomicProposition S d) => x.children) = (nodes[j]?).map
              (fun x : OnlineAnalyzerNode ℝ (AtomicProposition S d) => x.children)) ∧
      (∀ j : ℕ, flags[j]? = some true → res.2[j]? = some true) ∧ res.2[idx - 1]? = some true
  -- out of fuel: no result
  | 0, _, _, _, _, _, _, _, h => by simp [OnlineReachSetAnalyzer.propagateRec] at h
  | fuel + 1, idx, nodes, flags, res, hsem, inv, hidx, h => by
    simp only [OnlineReachSetAnalyzer.propagateRec] at h
    -- the node, the children's pass, the node after it, its children, the step
    obtain ⟨node, hnode, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨node2, hnode2, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨cs, hcs, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
    have hk : idx - 1 < nodes.length := (List.getElem?_eq_some_iff.1 hnode).1
    have hnode' : nodes[idx - 1] = node := (List.getElem?_eq_some_iff.1 hnode).2
    -- the children of the node, each propagated first
    have hdag := (inv.dag (idx - 1) hk).2.2.2
    rw [hnode'] at hdag
    obtain ⟨i1, i2, i3, i4, i5⟩ := aux_foldl_todo ψ sig sem fuel
      (fun idx nodes flags res => aux_propagateRec ψ sig sem fuel idx nodes flags res) _ nodes
      flags st hsem inv (fun c hc => by
        simp only [List.mem_mergeSort, List.mem_eraseDups, List.mem_filter] at hc
        exact (hdag c hc.1).1) hst
    have hk2 : idx - 1 < st.1.length := by rw [i2]; exact hk
    have hnode2' : st.1[idx - 1] = node2 := (List.getElem?_eq_some_iff.1 hnode2).2
    have hch2 : node2.children = node.children := by -- the children's pass keeps the graph
      have := i3 (idx - 1); rw [hnode2, hnode] at this; simpa using this
    have hflag : ∀ c ∈ st.1[idx - 1].children, st.2[c - 1]? = some true := by -- all flagged
      intro c hc
      rw [hnode2', hch2] at hc
      by_cases hf : flags[c - 1]? = some true
      · exact i4 _ hf
      · apply i5
        simp only [List.mem_mergeSort, List.mem_eraseDups, List.mem_filter]
        exact ⟨hc, by simpa using hf⟩
    -- the step at the node itself, its children all flagged
    rw [← hnode2'] at hcs hr
    obtain ⟨s1, s2, s3⟩ := aux_step ψ sig sem st.1 st.2 (by rw [i2]; exact hsem) i1 idx hidx hk2
      hflag cs hcs r hr
    rw [← hnode2']
    refine ⟨s1, by rw [s2, i2], fun j => by rw [s3, i3], fun j hj => ?_, ?_⟩
    · by_cases hj' : j = idx - 1
      · subst hj'; simp [List.getElem?_set_self (by rw [i1.len]; exact hk2)]
      · rw [List.getElem?_set_ne (by omega)]; exact i4 j hj
    · simp [List.getElem?_set_self (by rw [i1.len]; exact hk2)]

end core


section observe

variable {A : Type} {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]

/-- The atom signals after observing `set` on `I`: `â(set)` on `I`, the old value elsewhere. -/
private noncomputable def aux_observeAtoms (sig : AtomicProposition S d → FourValuedSignal ℝ)
    (set : S d) (I : STLInterval ℝ) (loc : ℕ) : AtomicProposition S d → FourValuedSignal ℝ :=
  fun a =>
    match OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a set loc with
    | some v => (sig a).set I (FourValued.fromKleene v)
    | none => sig a

omit [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)] in
/-- The semantics of node `i`. -/
private noncomputable def aux_sem (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (sig : AtomicProposition S d → FourValuedSignal ℝ) (i : ℕ) : FourValuedSignal ℝ :=
  ((ψ i).sat sig).getD (FourValuedSignal.uniformSignal .ii)

omit [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)] in
/-- The semantics of node `i` exists and is valid. -/
private theorem aux_sem_spec (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (sig : AtomicProposition S d → FourValuedSignal ℝ) (hv : ∀ a, (sig a).IsValid) (i : ℕ) :
    (ψ i).sat sig = some (aux_sem ψ sig i) ∧ (aux_sem ψ sig i).IsValid := by
  obtain ⟨s, hs, hsv⟩ := (ψ i).sat_spec sig hv
  exact ⟨by simp [aux_sem, hs], by simpa [aux_sem, hs] using hsv⟩

/-- Between observations: the invariant with no node propagated yet, every `AP` node a leaf, and a
propagation after each observation. -/
private structure aux_Good (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (sig : AtomicProposition S d → FourValuedSignal ℝ) (obj : OnlineReachSetAnalyzer ℝ S d) :
    Prop where
  sigv : ∀ a, (sig a).IsValid
  inv : aux_Inv ψ (aux_sem ψ sig) obj.nodes (List.replicate obj.nodes.length false)
  leaves : ∀ j, j < obj.nodes.length → ∀ l a, ψ (j + 1) = .ap l a → j + 1 ∈ obj.leaves
  freq : obj.propagationFrequency = 1

/-- Clearing the flags keeps the rest of the invariant. -/
private theorem aux_inv_reset (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A)
    (sem : ℕ → FourValuedSignal ℝ)
    (nodes : List (OnlineAnalyzerNode ℝ A)) (flags : List Bool) (inv : aux_Inv ψ sem nodes flags) :
    aux_Inv ψ sem nodes (List.replicate nodes.length false) :=
  ⟨by simp, inv.dag, inv.valid, inv.sound, inv.pre, inv.guard, fun j h hf => by simp
      [List.getElem?_replicate] at hf,
    inv.leaf, inv.root⟩

/-- Atom observations that refine the semantics, changing no node but leaves on their own new
times, keep the invariant. -/
private theorem aux_inv_update (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A)
    (sem sem' : ℕ → FourValuedSignal ℝ) (nodes nodes1 : List (OnlineAnalyzerNode ℝ A))
    (inv : aux_Inv ψ sem nodes (List.replicate nodes.length false))
    (hlen : nodes1.length = nodes.length) (hsr : ∀ i, (sem' i).Refines (sem i))
    (hnode : ∀ j (h : j < nodes.length) (h1 : j < nodes1.length), (nodes1[j] = nodes[j] ∧
      (nodes[j].children = [] → ∀ t : ℝ, 0 ≤ t → (sem' (j + 1)).at t = (sem (j + 1)).at t)) ∨
      (nodes[j].children = [] ∧ nodes1[j] = { nodes[j] with signal := nodes1[j].signal } ∧
        nodes1[j].signal.IsValid ∧ (sem' (j + 1)).Refines nodes1[j].signal ∧
        aux_Complete sem' nodes1[j] (j + 1))) : -- --- CONCL ---
    aux_Inv ψ sem' nodes1 (List.replicate nodes1.length false) := by -- --- PROOF ---
  -- every node keeps all but its signal
  have hsame : ∀ j (h : j < nodes.length) (h1 : j < nodes1.length),
      nodes1[j] = { nodes[j] with signal := nodes1[j].signal } := by
    intro j h h1
    rcases hnode j h h1 with ⟨e, -⟩ | ⟨-, e, -⟩
    · rw [e]
    · exact e
  have hl : ∀ j, j < nodes1.length → j < nodes.length := fun j h => hlen ▸ h
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, fun j h hf => by simp [List.getElem?_replicate] at hf,
    ?_, ?_⟩
  · intro j h
    have e := hsame j (hl j h) h
    obtain ⟨d1, d2, d3, d4⟩ := inv.dag j (hl j h)
    rw [e]
    -- the graph is unchanged
    refine ⟨d1, aux_shapeOf_congr ψ (ψ (j + 1)) nodes[j] _ rfl rfl rfl rfl d2, d3, fun c hc => ?_⟩
    obtain ⟨c1, c2, c3⟩ := d4 c hc
    refine ⟨c1, by rw [hlen]; exact c2, ?_⟩
    rw [hsame (c - 1) c2 (by rw [hlen]; exact c2)]; exact c3
  · intro j h
    rcases hnode j (hl j h) h with ⟨e, -⟩ | ⟨-, -, e, -⟩
    · rw [e]; exact inv.valid j (hl j h)
    · exact e
  · intro j h
    -- sound: by the refinement of the semantics, or as given for an observed leaf
    rcases hnode j (hl j h) h with ⟨e, -⟩ | ⟨-, -, -, e, -⟩
    · rw [e]; exact (hsr (j + 1)).trans (inv.sound j (hl j h))
    · exact e
  · intro j h
    rw [hsame j (hl j h) h]; exact inv.pre j (hl j h)
  · intro j h c hc hc' P hP t ht htE hii
    -- the guard: an observed leaf has no children
    rcases hnode j (hl j h) h with ⟨e, -⟩ | ⟨hch, e, -⟩
    · have hc'' : c - 1 < nodes.length := hl _ hc'
      rw [hsame (c - 1) hc'' hc'] at hP
      simp only [e] at hc htE hii
      exact inv.guard j (hl j h) c hc hc'' P hP t ht htE hii
    · rw [e] at hc; rw [hch] at hc; simp at hc
  · intro j h hch
    -- a leaf is complete: its semantics is unchanged, or as given
    rcases hnode j (hl j h) h with ⟨e, hs⟩ | ⟨-, -, -, -, e⟩
    · simp only [e] at hch ⊢
      intro t ht htE
      rw [hs hch t ht]; exact inv.leaf j (hl j h) hch t ht htE
    · exact e
  · intro h
    rw [hsame 0 (hl 0 h) h]; exact inv.root (hl 0 h)

/-- One observation and the propagation after it, on new times only, keep `aux_Good` for the
observed atom signals, and the root signal is their semantics. -/
private theorem aux_observe_step (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (sig : AtomicProposition S d → FourValuedSignal ℝ) (obj obj' : OnlineReachSetAnalyzer ℝ S d)
    (set : S d) (I : STLInterval ℝ) (loc : ℕ) (hgood : aux_Good ψ sig obj) (hI : I ≠ .empty)
    (hdisj : ∀ a t, 0 ≤ t → t ∈ I.set → (sig a).at t = .ii)
    (h : obj.observeSet (𝕋 := 𝕋) 0 set I loc = some obj') : -- --- CONCL ---
    aux_Good ψ (aux_observeAtoms (𝕋 := 𝕋) sig set I loc) obj' ∧
      obj'.nodes.length = obj.nodes.length ∧ ∀ h : 0 < obj'.nodes.length, ∀ t : ℝ, 0 ≤ t →
        obj'.nodes[0].signal.at t = (aux_sem ψ (aux_observeAtoms (𝕋 := 𝕋) sig set I loc) 1).at t
    := by -- --- PROOF ---
  set sig' := aux_observeAtoms (𝕋 := 𝕋) sig set I loc with hsig'
  have inv := hgood.inv
  set nodes := obj.nodes with hnodes
  -- the new atom signals are valid and refine the old ones
  have hv' : ∀ a, (sig' a).IsValid := by
    intro a; simp only [sig']; unfold aux_observeAtoms; split
    · exact (FourValuedSignal.set_spec _ (hgood.sigv a) _ _).1
    · exact hgood.sigv a
  have hr' : ∀ a, (sig' a).Refines (sig a) := by
    intro a t ht hne
    simp only [sig']; unfold aux_observeAtoms; split
    · rw [((FourValuedSignal.set_spec _ (hgood.sigv a) I _).2 t ht).2
        (fun hm => hne (hdisj a t ht hm))]
    · rfl
  -- so the semantics refines the old one
  have hsem' : ∀ i, (aux_sem ψ sig' i).Refines (aux_sem ψ sig i) := fun i =>
    (ψ i).sat_refines sig sig' hgood.sigv hv' hr' _ _ (aux_sem_spec ψ sig hgood.sigv i).1
      (aux_sem_spec ψ sig' hv' i).1
  -- unfold the observation
  cases I with
  | empty => exact absurd rfl hI
  | nonempty lo up lc rc p1 p2 p3 =>
  simp only [OnlineReachSetAnalyzer.observeSet, Option.isSome_none, Option.getD_none] at h
  obtain ⟨nodes1, hn1, hprop⟩ := Option.bind_eq_some_iff.1 h
  rw [if_pos (by rw [hgood.freq]; exact Nat.mod_one _)] at hprop
  set I : STLInterval ℝ := .nonempty lo up lc rc p1 p2 p3 with hIdef
  -- the observed leaves
  obtain ⟨hlen1, hobs⟩ := OnlineReachSetAnalyzer.observeLeaves_spec (𝕋 := 𝕋) obj.nodes set I loc
    inv.valid obj.leaves nodes1 hn1
  -- an `AP` node's formula, proposition and semantics
  have hap : ∀ j (h : j < nodes.length), nodes[j].kind = .ap → ∃ l a, ψ (j + 1) = .ap l a ∧
      nodes[j].ap = some a ∧ nodes[j].children = [] := by
    intro j h hk
    have hs := (inv.dag j h).2.1
    cases hψ : ψ (j + 1) <;> rw [hψ] at hs <;> simp only [OnlineReachSetAnalyzer.IsNodeOf] at hs
    all_goals first
      | exact ⟨_, _, rfl, hs.2.2, hs.2.1⟩
      | (rw [hs.1] at hk; exact absurd hk (by decide))
  -- the invariant after the leaves observed, before propagating
  have inv1 : aux_Inv ψ (aux_sem ψ sig') nodes1 (List.replicate nodes1.length false) := by
    refine aux_inv_update ψ (aux_sem ψ sig) (aux_sem ψ sig') nodes nodes1 inv hlen1 hsem' ?_
    intro j h h1
    obtain ⟨h', q1, q2⟩ := hobs j h
    by_cases hp : nodes[j].kind = .ap ∧ j + 1 ∈ obj.leaves
    · right
      obtain ⟨a, val, ha, hval, e, ev, et⟩ := q2 hp
      obtain ⟨l, a', hψ, ha', hch⟩ := hap j h hp.1
      rw [ha] at ha'; cases ha'
      have hsj : aux_sem ψ sig (j + 1) = sig a := by simp [aux_sem, hψ,
        OnlineReachSetAnalyzer.Formula.sat]
      have hsj' : aux_sem ψ sig' (j + 1) = (sig a).set I (FourValued.fromKleene val) := by
        simp [aux_sem, hψ, OnlineReachSetAnalyzer.Formula.sat, sig', aux_observeAtoms, hval]; rfl
      -- the leaf holds the new value on `I` and the old one elsewhere
      obtain ⟨-, hst⟩ := FourValuedSignal.set_spec (sig a) (hgood.sigv a) I
        (FourValued.fromKleene val)
      refine ⟨hch, e, ev, ?_, ?_⟩
      · intro t ht hne
        rw [et t ht] at hne ⊢; rw [hsj']
        split_ifs at hne ⊢ with hI
        · rw [(hst t ht).1 hI]
        · rw [(hst t ht).2 hI, ← hsj]; exact inv.sound j h t ht hne
      · intro t ht htE
        rw [e] at htE
        rw [et t ht, hsj']
        split_ifs with hI
        · rw [(hst t ht).1 hI]
        · rw [(hst t ht).2 hI, ← hsj]; exact inv.leaf j h hch t ht htE
    · left
      -- an unobserved node: a leaf of it is `true`, `false`, or an unobserved atom
      refine ⟨q1 hp, fun hch t ht => ?_⟩
      have hs := (inv.dag j h).2.1
      cases hψ : ψ (j + 1) <;> rw [hψ] at hs <;> simp only [OnlineReachSetAnalyzer.IsNodeOf] at hs
      · simp [aux_sem, hψ, OnlineReachSetAnalyzer.Formula.sat]
      · simp [aux_sem, hψ, OnlineReachSetAnalyzer.Formula.sat]
      · exact absurd ⟨hs.1, hgood.leaves j h _ _ hψ⟩ hp
      · obtain ⟨-, c, hc, -⟩ := hs; rw [hch] at hc; cases hc
      · obtain ⟨-, c, c', hc, -⟩ := hs; rw [hch] at hc; cases hc
      · obtain ⟨-, c, c', hc, -⟩ := hs; rw [hch] at hc; cases hc
      · obtain ⟨-, -, c, c', hc, -⟩ := hs; rw [hch] at hc; cases hc
  -- propagate from the root
  simp only [OnlineReachSetAnalyzer.propagate] at hprop
  obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.1 hprop
  have hsemOk : aux_SemOk ψ sig' (aux_sem ψ sig') nodes1.length :=
    fun i _ _ => aux_sem_spec ψ sig' hv' i
  obtain ⟨i1, i2, -, -, i5⟩ := aux_propagateRec ψ sig' (aux_sem ψ sig') _ 1 nodes1 _ st hsemOk
    inv1 le_rfl hst
  -- the root is flagged, and ignores no time: complete everywhere
  refine ⟨⟨hv', aux_inv_reset _ _ _ _ i1, ?_, hgood.freq⟩, by simp only; rw [i2, hlen1], ?_⟩
  · intro j hj l a hψ
    exact hgood.leaves j (by simp only at hj; rw [i2, hlen1] at hj; exact hj) l a hψ
  · intro h0 t ht
    simp only at h0 ⊢
    have hc := i1.flag 0 h0 i5
    apply hc t ht
    rw [aux_getAllProp_set _ (i1.pre 0 h0)]
    rintro ⟨-, hall⟩
    have := hall .empty (by rw [(i1.root h0).2]; simp)
    simp [STLInterval.set_empty] at this

/-- A run on observations at new, pairwise disjoint times keeps `aux_Good`, and the root signal is
the semantics of the observed atoms. -/
private theorem aux_run (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) :
    ∀ (obs : List (S d × STLInterval ℝ × ℕ)) (sig : AtomicProposition S d → FourValuedSignal ℝ)
      (obj obj' : OnlineReachSetAnalyzer ℝ S d), aux_Good ψ sig obj →
      (∀ o ∈ obs, o.2.1 ≠ .empty) →
      obs.Pairwise (fun o o' => Disjoint o.2.1.set o'.2.1.set) →
      -- what `sig` knows is not observed again
      (∀ a (t : ℝ), 0 ≤ t → (sig a).at t ≠ .ii → ∀ o ∈ obs, t ∉ o.2.1.set) →
      obs.foldlM (fun o x => o.observeSet (𝕋 := 𝕋) 0 x.1 x.2.1 x.2.2) obj = some obj' →
      aux_Good ψ (OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋) sig obs) obj' ∧ obj'.nodes.length =
          obj.nodes.length ∧
        (obs ≠ [] → ∀ h : 0 < obj'.nodes.length, ∀ t : ℝ, 0 ≤ t →
          obj'.nodes[0].signal.at t =
              (aux_sem ψ (OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋) sig obs) 1).at t)
  | [], sig, obj, obj', hgood, _, _, _, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨hgood, rfl, fun h => absurd rfl h⟩
  | o :: obs, sig, obj, obj', hgood, hne, hpw, hfresh, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨obj1, h1, h⟩ := Option.bind_eq_some_iff.1 h
    -- the first observation, on times nothing knows yet
    obtain ⟨hg1, hl1, hroot1⟩ := aux_observe_step (𝕋 := 𝕋) ψ sig obj obj1 o.1 o.2.1 o.2.2 hgood
      (hne o (by simp)) (fun a t ht hI => by
        by_contra hc; exact hfresh a t ht hc o (by simp) hI) h1
    have hpw' := List.pairwise_cons.1 hpw
    obtain ⟨-, hii⟩ := OnlineReachSetAnalyzer.observeAtoms_spec (𝕋 := 𝕋) [o] sig hgood.sigv
    -- the rest, on times the first observation left unknown
    have := aux_run ψ obs _ obj1 obj' hg1 (fun o' ho' => hne o' (by simp [ho'])) hpw'.2
      (fun a t ht hnii o' ho' hmem => by
        rcases hii a t ht hnii with h' | ⟨o'', ho'', ht''⟩
        · exact hfresh a t ht h' o' (by simp [ho']) hmem
        · simp only [List.mem_singleton] at ho''; subst ho''
          exact Set.disjoint_left.1 (hpw'.1 o' ho') ht'' hmem) h
    refine ⟨this.1, by rw [this.2.1, hl1], fun _ => ?_⟩
    by_cases hobs : obs = []
    · subst hobs
      simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
      subst h
      exact hroot1
    · exact this.2.2 hobs

end observe


section mk

variable {S : ℕ → Type} {d : ℕ}

/-- The analyzer of `φ`, with nothing observed: `aux_Good` for the inconclusive atom signals, the
root at node `1`. -/
private theorem aux_mk_good (φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (hlabel : ∀ l x y, (OnlineReachSetAnalyzer.Formula.ap l x).IsSub φ →
      (OnlineReachSetAnalyzer.Formula.ap l y).IsSub φ → x = y) (dp : Bool)
    (obj : OnlineReachSetAnalyzer ℝ S d)
    (h : OnlineReachSetAnalyzer.mk? φ 1 dp = some obj) : -- --- CONCL ---
    ∃ ψ, ψ 1 = φ ∧ aux_Good ψ (fun _ => FourValuedSignal.uniformSignal .ii) obj ∧
      0 < obj.nodes.length := by -- --- PROOF ---
  obtain ⟨ψ, hψ1, hfreq, hpos, hroot0, hn⟩ :=
    OnlineReachSetAnalyzer.mk?_nodes_spec φ hlabel 1 dp obj h
  set sig : AtomicProposition S d → FourValuedSignal ℝ :=
    fun _ => FourValuedSignal.uniformSignal .ii
  have hsig : ∀ a, (sig a).IsValid := fun _ => (FourValuedSignal.uniformSignal_spec _).1
  -- the semantics of the leaves on the inconclusive atoms
  have hsemc : ∀ i, (ψ i = .tt → ∀ t : ℝ, 0 ≤ t → (aux_sem ψ sig i).at t = .tt) ∧
      (ψ i = .ff → ∀ t : ℝ, 0 ≤ t → (aux_sem ψ sig i).at t = .ff) ∧
      (∀ l a, ψ i = .ap l a → ∀ t : ℝ, 0 ≤ t → (aux_sem ψ sig i).at t = .ii) := by
    intro i
    refine ⟨fun e t ht => ?_, fun e t ht => ?_, fun l a e t ht => ?_⟩ <;>
      simp only [aux_sem, e, OnlineReachSetAnalyzer.Formula.sat, Option.getD_some, sig] <;>
      exact (FourValuedSignal.uniformSignal_spec _).2 t ht
  refine ⟨ψ, hψ1, ⟨hsig, ?_, fun j h l a hψ => (hn j h).2.2.2.2.2.2 l a hψ, hfreq⟩, hpos⟩
  refine ⟨by simp, fun j h => ?_, fun j h => (hn j h).2.2.2.1, fun j h => ?_,
    fun j h P hP => ?_, fun j h c _ hc P hP t _ _ _ => ?_,
    fun j h hf => by simp [List.getElem?_replicate] at hf, fun j h hch => ?_, fun h => ?_⟩
  · -- the DAG
    obtain ⟨o1, o2, o7, -, -, o11, -⟩ := hn j h
    exact ⟨o1, o2, by rw [o7]; simp, o11⟩
  · -- sound: the initial value is the semantics where conclusive
    obtain ⟨-, o2, -, -, o6, -⟩ := hn j h
    intro t ht hne
    rw [o6 t ht] at hne ⊢
    cases hψ : ψ (j + 1) <;> rw [hψ] at o2 <;>
      simp only [OnlineReachSetAnalyzer.IsNodeOf] at o2 <;>
      simp [OnlineAnalyzerNode.Kind.initValue, o2.1] at hne ⊢
    · rw [(hsemc (j + 1)).1 hψ t ht]
    · rw [(hsemc (j + 1)).2.1 hψ t ht]
  · -- no interval is propagated yet
    rw [(hn j h).2.2.1] at hP; simp only [List.mem_map] at hP
    obtain ⟨_, _, rfl⟩ := hP; exact Or.inl rfl
  · rw [(hn (c - 1) hc).2.2.1] at hP
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hP)
    simp [STLInterval.set_empty]
  · -- a leaf holds its initial value, the semantics of `true`, `false` or an unobserved atom
    obtain ⟨-, o2, -, -, o6, -⟩ := hn j h
    intro t ht _
    rw [o6 t ht]
    cases hψ : ψ (j + 1) <;> rw [hψ] at o2 <;>
      simp only [OnlineReachSetAnalyzer.IsNodeOf, hch] at o2
    · rw [o2.1, (hsemc (j + 1)).1 hψ t ht]; rfl
    · rw [o2.1, (hsemc (j + 1)).2.1 hψ t ht]; rfl
    · rw [o2.1, (hsemc (j + 1)).2.2 _ _ hψ t ht]; rfl
    all_goals simp at o2
  · exact ⟨hroot0, by rw [(hn 0 h).2.2.1, hroot0]; rfl⟩

end mk


section main

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.observeSet_correct
    (φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (hlabel : ∀ l x y, (OnlineReachSetAnalyzer.Formula.ap l x).IsSub φ →
      (OnlineReachSetAnalyzer.Formula.ap l y).IsSub φ → x = y)
    (dp : Bool) (obs : List (S d × STLInterval ℝ × ℕ)) (hne : obs ≠ [])
    (hI : ∀ o ∈ obs, o.2.1 ≠ .empty)
    (hdisj : obs.Pairwise fun o o' => Disjoint o.2.1.set o'.2.1.set) : -- --- CONCL ---
    ∀ obj₀ ∈ OnlineReachSetAnalyzer.mk? φ 1 dp,
      ∀ obj ∈ obs.foldlM (fun o x => o.observeSet (𝕋 := 𝕋) 0 x.1 x.2.1 x.2.2) obj₀,
      ∃ s, φ.sat (OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋)
          (fun _ => FourValuedSignal.uniformSignal .ii) obs) = some s ∧
        ∃ root, obj.nodes[0]? = some root ∧ ∀ t : ℝ, 0 ≤ t → root.signal.at t = s.at t
    := by -- --- PROOF ---
  intro obj₀ h₀ obj hrun
  -- the nodes form the syntax DAG of `φ`
  obtain ⟨ψ, hψ, hgood, hpos⟩ := aux_mk_good φ hlabel dp obj₀ h₀
  -- the invariant through the run, then the root at node `1`
  obtain ⟨-, hlen, hroot⟩ := aux_run (𝕋 := 𝕋) ψ obs _ obj₀ obj hgood hI hdisj
    (fun a t ht hne _ _ _ => hne ((FourValuedSignal.uniformSignal_spec _).2 t ht)) hrun
  have hpos' : 0 < obj.nodes.length := by rw [hlen]; exact hpos
  obtain ⟨hsat, -⟩ := aux_sem_spec ψ
      (OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋)
        (fun _ => FourValuedSignal.uniformSignal .ii) obs)
    (OnlineReachSetAnalyzer.observeAtoms_spec (𝕋 := 𝕋) obs _
        (fun _ => (FourValuedSignal.uniformSignal_spec _).1)).1 1
  rw [hψ] at hsat
  exact ⟨_, hsat, obj.nodes[0], by simp [hpos'], hroot hne hpos'⟩

end main

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
