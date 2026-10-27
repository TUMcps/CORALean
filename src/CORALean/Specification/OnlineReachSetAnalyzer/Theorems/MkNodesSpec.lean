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
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ObserveAtomsSpec
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
# The analyzer of a formula is its syntax DAG

`mk?` parses `φ` into nodes that form the syntax DAG of `φ`, a node per subformula and one for
each repeated subformula that the cache merges [1, Alg. 1]: some `ψ` labels node `j + 1` with its
subformula, the root `1` with `φ`, so that the node is that of `ψ (j + 1)`, its children point back
to it, every atom's node is a leaf, and nothing is observed or propagated yet. The cache tells
subformulas apart by their key, which keeps the label of an atom, not the atom; so `φ` must use a
label for one atom only.

## Inputs
* `φ` – formula
* `f` – propagation frequency
* `dp` – whether to propagate down

## Hypotheses
* `hlabel` – a label names one atom in `φ`

## Conclusion
* for the analyzer of `φ`, a labelling `ψ` of its nodes with subformulas as described

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section parse

variable {S : ℕ → Type} {d : ℕ}

/-- The operands of a formula. -/
private def aux_ops {A : Type} : OnlineReachSetAnalyzer.Formula ℝ A → List
    (OnlineReachSetAnalyzer.Formula ℝ A)
  | .not a => [a]
  | .and a b => [a, b]
  | .or a b => [a, b]
  | .until _ a b => [a, b]
  | _ => []

/-- A formula is its own subformula. -/
private theorem aux_isSub_refl {A : Type} (φ : OnlineReachSetAnalyzer.Formula ℝ A) : φ.IsSub φ := by
  cases φ <;> simp [OnlineReachSetAnalyzer.Formula.IsSub]

/-- A subformula of a subformula is a subformula. -/
private theorem aux_isSub_trans {A : Type} {a b : OnlineReachSetAnalyzer.Formula ℝ A}
    (h : a.IsSub b) : -- --- CONCL ---
    ∀ {φ : OnlineReachSetAnalyzer.Formula ℝ A}, b.IsSub φ → a.IsSub φ
    := by -- --- PROOF ---
  intro φ
  induction φ with
  -- a leaf `φ` is `b` itself
  | tt => intro hb; simp only [OnlineReachSetAnalyzer.Formula.IsSub] at hb; subst hb; exact h
  | ff => intro hb; simp only [OnlineReachSetAnalyzer.Formula.IsSub] at hb; subst hb; exact h
  | ap => intro hb; simp only [OnlineReachSetAnalyzer.Formula.IsSub] at hb; subst hb; exact h
  | not c ih =>
    intro hb; simp only [OnlineReachSetAnalyzer.Formula.IsSub] at hb ⊢
    rcases hb with rfl | hb
    · simpa [OnlineReachSetAnalyzer.Formula.IsSub] using h
    · exact Or.inr (ih hb)
  -- `b` is `φ`, or inside an operand
  | and c e ih ih' =>
    intro hb; simp only [OnlineReachSetAnalyzer.Formula.IsSub] at hb ⊢
    rcases hb with rfl | hb | hb
    · simpa [OnlineReachSetAnalyzer.Formula.IsSub] using h
    · exact Or.inr (Or.inl (ih hb))
    · exact Or.inr (Or.inr (ih' hb))
  | or c e ih ih' =>
    intro hb; simp only [OnlineReachSetAnalyzer.Formula.IsSub] at hb ⊢
    rcases hb with rfl | hb | hb
    · simpa [OnlineReachSetAnalyzer.Formula.IsSub] using h
    · exact Or.inr (Or.inl (ih hb))
    · exact Or.inr (Or.inr (ih' hb))
  | «until» I c e ih ih' =>
    intro hb; simp only [OnlineReachSetAnalyzer.Formula.IsSub] at hb ⊢
    rcases hb with rfl | hb | hb
    · simpa [OnlineReachSetAnalyzer.Formula.IsSub] using h
    · exact Or.inr (Or.inl (ih hb))
    · exact Or.inr (Or.inr (ih' hb))

/-- An operand is a subformula. -/
private theorem aux_isSub_of_mem_ops {A : Type} (φ a : OnlineReachSetAnalyzer.Formula ℝ A)
    (h : a ∈ aux_ops φ) : a.IsSub φ := by
  cases φ <;> simp [aux_ops] at h <;>
    (try rcases h with rfl | rfl) <;>
    simp [OnlineReachSetAnalyzer.Formula.IsSub, aux_isSub_refl]

/-- A subformula is no larger. -/
private theorem aux_sizeOf_isSub {A : Type}
    (a φ : OnlineReachSetAnalyzer.Formula ℝ A) (h : a.IsSub φ) : -- --- CONCL ---
    sizeOf a ≤ sizeOf φ := by -- --- PROOF ---
  induction φ with
  -- `a` is `φ`, or inside an operand
  | tt => simp only [OnlineReachSetAnalyzer.Formula.IsSub] at h; subst h; rfl
  | ff => simp only [OnlineReachSetAnalyzer.Formula.IsSub] at h; subst h; rfl
  | ap => simp only [OnlineReachSetAnalyzer.Formula.IsSub] at h; subst h; rfl
  | not c ih =>
    simp only [OnlineReachSetAnalyzer.Formula.IsSub] at h
    rcases h with rfl | h
    · rfl
    · have := ih h; simp; omega
  | and c e ih ih' =>
    simp only [OnlineReachSetAnalyzer.Formula.IsSub] at h
    rcases h with rfl | h | h
    · rfl
    · have := ih h; simp; omega
    · have := ih' h; simp; omega
  -- binary operators alike
  | or c e ih ih' =>
    simp only [OnlineReachSetAnalyzer.Formula.IsSub] at h
    rcases h with rfl | h | h
    · rfl
    · have := ih h; simp; omega
    · have := ih' h; simp; omega
  | «until» I c e ih ih' =>
    simp only [OnlineReachSetAnalyzer.Formula.IsSub] at h
    rcases h with rfl | h | h
    · rfl
    · have := ih h; simp; omega
    · have := ih' h; simp; omega

/-- An operand is smaller. -/
private theorem aux_sizeOf_ops {A : Type} (φ a : OnlineReachSetAnalyzer.Formula ℝ A)
    (h : a ∈ aux_ops φ) :
    sizeOf a < sizeOf φ := by
  cases φ <;> simp [aux_ops] at h <;> (try rcases h with rfl | rfl) <;> simp <;>
      omega

/-- A node's fields, children and parents as `parse` keeps them, the node being that of
`ψ (j+1)`. -/
private def aux_NodeOk (φ0 : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (nodes : List (OnlineAnalyzerNode ℝ (AtomicProposition S d))) (j : ℕ)
    (n : OnlineAnalyzerNode ℝ (AtomicProposition S d)) : Prop :=
  n.idx = j + 1 ∧ n.kind = (ψ (j + 1)).kind ∧ n.interval = (ψ (j + 1)).interval? ∧
  n.ap = (ψ (j + 1)).ap? ∧ n.signal.IsValid ∧
  (∀ t : ℝ, 0 ≤ t → n.signal.at t = n.kind.initValue) ∧
  n.prop = n.parents.map (fun _ => STLInterval.empty) ∧ n.parents ≠ [] ∧
  n.children.length ≤ (aux_ops (ψ (j + 1))).length ∧
  (∀ i (hi : i < n.children.length), (aux_ops (ψ (j + 1)))[i]? = some (ψ n.children[i])) ∧
  (∀ c ∈ n.children, 1 ≤ c ∧ ∃ hc : c - 1 < nodes.length, j + 1 ∈ nodes[c - 1].parents) ∧
  (∀ p ∈ n.parents, p = 0 ∨ (1 ≤ p ∧ p ≤ nodes.length ∧ aux_ops (ψ p) ≠ [])) ∧
  (ψ (j + 1)).IsSub φ0

/-- The parse state is the partial syntax DAG of `φ0` labelled by `ψ`. -/
private def aux_PInv (φ0 : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (st : OnlineReachSetAnalyzer.ParseState ℝ S d)
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) : Prop :=
  (∀ j (h : j < st.nodes.length), aux_NodeOk φ0 ψ st.nodes j st.nodes[j]) ∧
  (∀ e ∈ st.cache, 1 ≤ e.2 ∧ e.2 ≤ st.nodes.length ∧ e.1 = (ψ e.2).key) ∧
  (∀ h : 0 < st.nodes.length, st.nodes[0].parents = [0] ∧ ψ 1 = φ0)

end parse


section parse2

variable {S : ℕ → Type} {d : ℕ}

/-- A node stays fine when the list grows and the parents only grow. -/
private theorem aux_nodeOk_mono (φ0 : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (nodes nodes' : List (OnlineAnalyzerNode ℝ (AtomicProposition S d))) (j : ℕ)
    (n : OnlineAnalyzerNode ℝ (AtomicProposition S d)) (hlen : nodes.length ≤ nodes'.length)
    (hpar : ∀ i (h : i < nodes.length) (h' : i < nodes'.length),
      nodes[i].parents ⊆ nodes'[i].parents)
    (h : aux_NodeOk φ0 ψ nodes j n) : -- --- CONCL ---
    aux_NodeOk φ0 ψ nodes' j n
    := by -- --- PROOF ---
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun c hc => ?_, fun p hp => ?_, h13⟩
  · obtain ⟨c1, c2, c3⟩ := h11 c hc
    exact ⟨c1, by omega, hpar _ c2 (by omega) c3⟩
  · rcases h12 p hp with h | ⟨p1, p2, p3⟩
    · exact Or.inl h
    · exact Or.inr ⟨p1, by omega, p3⟩

/-- Adding the inner node `p` as a parent of the node `c` keeps the parse invariant. -/
private theorem aux_pinv_addParent (φ0 : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (st : OnlineReachSetAnalyzer.ParseState ℝ S d) (hinv : aux_PInv φ0 st ψ) (c p : ℕ)
    (hc1 : 1 ≤ c) (hc : c - 1 < st.nodes.length) (hp1 : 1 ≤ p) (hp : p ≤ st.nodes.length)
    (hops : aux_ops (ψ p) ≠ []) (hc0 : c ≠ 1) : -- --- CONCL ---
    aux_PInv φ0 { st with nodes := st.nodes.set (c - 1) (st.nodes[c - 1].addParent p) } ψ
    := by -- --- PROOF ---
  obtain ⟨hn, hcache, hroot⟩ := hinv
  -- the parents only grow
  have hpar : ∀ i (h : i < st.nodes.length)
      (h' : i < (st.nodes.set (c - 1) (st.nodes[c - 1].addParent p)).length),
      st.nodes[i].parents ⊆ (st.nodes.set (c - 1) (st.nodes[c - 1].addParent p))[i].parents := by
    intro i h h'
    rw [List.getElem_set]
    split_ifs with hi
    · subst hi; simp [OnlineAnalyzerNode.addParent]
    · exact fun _ x => x
  refine ⟨fun j h => ?_, fun e he => by simpa using hcache e he, fun h => ?_⟩
  · simp only [List.length_set] at h
    have ok := aux_nodeOk_mono φ0 ψ st.nodes _ j st.nodes[j] (by simp) hpar (hn j h)
    simp only [List.getElem_set]
    split_ifs with hj
    · subst hj
      -- the node `c` gets the entry `∅` for the new parent `p`, an inner node
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := ok
      refine ⟨h1, h2, h3, h4, h5, h6, by simp [OnlineAnalyzerNode.addParent, h7],
        by simp [OnlineAnalyzerNode.addParent], h9, h10, h11, fun q hq => ?_, h13⟩
      simp only [OnlineAnalyzerNode.addParent, List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | rfl
      · exact h12 q hq
      · exact Or.inr ⟨hp1, by simpa using hp, hops⟩
    · exact ok
  · simp only [List.length_set] at h
    -- the root's parents are kept
    obtain ⟨r1, r2⟩ := hroot h
    refine ⟨?_, r2⟩
    rw [List.getElem_set_ne (by omega)]; exact r1

/-- Adding a child `c` for the next operand of the node `p` keeps the parse invariant. -/
private theorem aux_pinv_addChild (φ0 : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (st : OnlineReachSetAnalyzer.ParseState ℝ S d) (hinv : aux_PInv φ0 st ψ) (p c : ℕ)
    (hp1 : 1 ≤ p) (hp : p - 1 < st.nodes.length) (hc1 : 1 ≤ c) (hc : c - 1 < st.nodes.length)
    (hpc : p ∈ st.nodes[c - 1].parents)
    (hnext : (aux_ops (ψ p))[st.nodes[p - 1].children.length]? = some (ψ c)) : -- --- CONCL ---
    aux_PInv φ0 { st with nodes := st.nodes.set (p - 1) (st.nodes[p - 1].addChild c) } ψ
    := by -- --- PROOF ---
  obtain ⟨hn, hcache, hroot⟩ := hinv
  -- the parents only grow
  have hpar : ∀ i (h : i < st.nodes.length)
      (h' : i < (st.nodes.set (p - 1) (st.nodes[p - 1].addChild c)).length),
      st.nodes[i].parents ⊆ (st.nodes.set (p - 1) (st.nodes[p - 1].addChild c))[i].parents := by
    intro i h h'
    rw [List.getElem_set]
    split_ifs with hi
    · subst hi; simp [OnlineAnalyzerNode.addChild]
    · exact fun _ x => x
  refine ⟨fun j h => ?_, fun e he => by simpa using hcache e he, fun h => ?_⟩
  · simp only [List.length_set] at h
    have ok := aux_nodeOk_mono φ0 ψ st.nodes _ j st.nodes[j] (by simp) hpar (hn j h)
    simp only [List.getElem_set]
    split_ifs with hj
    · subst hj
      have hp' : p - 1 + 1 = p := by omega
      unfold aux_NodeOk at ok ⊢
      rw [hp'] at ok ⊢
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := ok
      -- the node `p` gets `c` as the child for its next operand
      have hlt := (List.getElem?_eq_some_iff.1 hnext).1
      refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_, ?_, ?_, h12, h13⟩
      · simp only [OnlineAnalyzerNode.addChild, List.length_append, List.length_singleton]
        omega
      · intro i hi
        simp only [OnlineAnalyzerNode.addChild, List.length_append, List.length_singleton] at hi
        simp only [OnlineAnalyzerNode.addChild]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · rw [List.getElem_append_left hi]; exact h10 i hi
        · subst hi; rw [List.getElem_append_right (le_refl _)]; simpa using hnext
      · -- the new child is in range and has `p` as a parent
        intro c' hc'
        simp only [OnlineAnalyzerNode.addChild, List.mem_append, List.mem_singleton] at hc'
        rcases hc' with hc' | rfl
        · exact h11 c' hc'
        · exact ⟨hc1, by simpa using hc, hpar _ hc (by simpa using hc) hpc⟩
    · exact ok
  · simp only [List.length_set] at h
    obtain ⟨r1, r2⟩ := hroot h
    refine ⟨?_, r2⟩
    rw [List.getElem_set]
    split_ifs with h0
    · simp only [OnlineAnalyzerNode.addChild, h0]; exact r1
    · exact r1

end parse2


section parse3

variable {S : ℕ → Type} {d : ℕ}

/-- `parseNew` appends the node of `φ` under `p` and keeps the parse invariant, labelling it `φ`. -/
private theorem aux_pinv_new (φ0 : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) (dp : Bool)
    (φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) (p : ℕ)
    (st st1 : OnlineReachSetAnalyzer.ParseState ℝ S d) (hinv : aux_PInv φ0 st ψ)
    (hsub : φ.IsSub φ0) (h0 : p = 0 → st.nodes.length = 0 ∧ φ = φ0)
    (hp : p ≠ 0 → ∃ hp : p - 1 < st.nodes.length, 1 ≤ p ∧
      (aux_ops (ψ p))[st.nodes[p - 1].children.length]? = some φ)
    (h : OnlineReachSetAnalyzer.parseNew dp φ p st = some st1) : -- --- CONCL ---
    aux_PInv φ0 st1 (fun i => if i = st.nodes.length + 1 then φ else ψ i) ∧
      st1.nodes.length = st.nodes.length + 1 ∧
      (∀ h : st.nodes.length < st1.nodes.length, st1.nodes[st.nodes.length].children = []) ∧
      (∀ j (h : j < st.nodes.length) (h1 : j < st1.nodes.length), j + 1 ≠ p →
        st1.nodes[j].children = st.nodes[j].children) ∧
      (p ≠ 0 → ∀ (h : p - 1 < st.nodes.length) (h1 : p - 1 < st1.nodes.length),
        st1.nodes[p - 1].children = st.nodes[p - 1].children ++ [st.nodes.length + 1])
    := by -- --- PROOF ---
  set ψ' : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d) :=
    fun i => if i = st.nodes.length + 1 then φ else ψ i with hψ'
  have hψle : ∀ i, i ≤ st.nodes.length → ψ' i = ψ i := fun i hi => by simp only [ψ']; rw
      [if_neg (by omega)]
  obtain ⟨hn, hcache, hroot⟩ := hinv
  unfold OnlineReachSetAnalyzer.parseNew at h
  -- the parent `p` is added to `c`, then `c` to `p`
  obtain ⟨nodes1, h1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨node, hnode, rfl⟩ := Option.map_eq_some_iff.1 h
  -- the new node, as `OnlineAnalyzerNode.mk?` builds it
  obtain ⟨-, hmk⟩ := OnlineAnalyzerNode.mk?_spec φ.kind (st.nodes.length + 1) [p] dp
    φ.interval? φ.ap?
  obtain ⟨k1, k2, k3, k4, -, k6, k7, k8, k9, k10⟩ := hmk node hnode
  -- the nodes before the new one: the parent gets the new child
  have hn1 : nodes1.length = st.nodes.length ∧ ∀ j (h : j < st.nodes.length)
      (h1 : j < nodes1.length),
      nodes1[j] =
        if j + 1 = p then st.nodes[j].addChild (st.nodes.length + 1) else st.nodes[j] := by
    by_cases hp0 : p ≠ 0
    · rw [if_pos hp0] at h1
      obtain ⟨-, n, n', hn', hfn, rfl⟩ :=
        (OnlineReachSetAnalyzer.updateNode_eq_some_iff _ _ _ _).1 h1
      obtain rfl := Option.some.inj hfn
      have hlt' := (List.getElem?_eq_some_iff.1 hn').1
      have hnn : st.nodes[p - 1] = n := (List.getElem?_eq_some_iff.1 hn').2
      refine ⟨by simp, fun j h h1 => ?_⟩
      rw [List.getElem_set]
      split_ifs with e1 e2 e2
      · subst e1; rw [hnn]
      · omega
      · omega
      · rfl
    · -- the root: nothing to update
      rw [if_neg hp0] at h1
      obtain rfl := Option.some.inj h1
      refine ⟨rfl, fun j h h1 => ?_⟩
      rw [if_neg (by omega)]
  obtain ⟨hl1, hn1⟩ := hn1
  -- positions, nodes and parents of the new list
  have hlen : (nodes1 ++ [node]).length = st.nodes.length + 1 := by simp [hl1]
  have hget : ∀ j (h : j < st.nodes.length) (h1 : j < (nodes1 ++ [node]).length),
      (nodes1 ++ [node])[j] = if j + 1 = p then st.nodes[j].addChild (st.nodes.length + 1) else
          st.nodes[j] := by
    intro j h h1; rw [List.getElem_append_left (by omega)]; exact hn1 j h (by omega)
  have hgetN : ∀ h1 : st.nodes.length < (nodes1 ++ [node]).length,
      (nodes1 ++ [node])[st.nodes.length] = node := by
    intro h1; rw [List.getElem_append_right (by omega)]; simp [hl1]
  have hparN : ∀ j (h : j < st.nodes.length) (h1 : j < (nodes1 ++ [node]).length),
      (nodes1 ++ [node])[j].parents = st.nodes[j].parents := by
    intro j h h1; rw [hget j h h1]; split_ifs <;> rfl
  have hops : p ≠ 0 → aux_ops (ψ p) ≠ [] := by
    intro hp0; obtain ⟨_, _, hx⟩ := hp hp0
    intro he; rw [he] at hx; simp at hx
  refine ⟨⟨fun j h => ?_, fun e he => ?_, fun h => ?_⟩, hlen, fun h => by rw [hgetN h, k4],
    fun j h h1 hjp => by rw [hget j h h1, if_neg hjp], fun hp0 h h1 => ?_⟩
  · -- every node is fine
    simp only [hlen] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · -- an old node, perhaps the parent
      obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13⟩ := hn j h
      unfold aux_NodeOk
      rw [hψle (j + 1) (by omega)]
      -- its children and parents are still in range
      have hcross : ∀ c ∈ st.nodes[j].children, 1 ≤ c ∧
          ∃ hc : c - 1 < (nodes1 ++ [node]).length, j + 1 ∈ (nodes1 ++ [node])[c - 1].parents := by
        intro c hc
        obtain ⟨c1, c2, c3⟩ := o11 c hc
        exact ⟨c1, by omega, by rw [hparN _ c2]; exact c3⟩
      have hparents : ∀ q ∈ st.nodes[j].parents, q = 0 ∨
          (1 ≤ q ∧ q ≤ (nodes1 ++ [node]).length ∧ aux_ops (ψ' q) ≠ []) := by
        intro q hq
        rcases o12 q hq with e | ⟨q1, q2, q3⟩
        · exact Or.inl e
        · exact Or.inr ⟨q1, by omega, by rw [hψle q q2]; exact q3⟩
      rw [hget j h (by omega)]
      split_ifs with hjp
      · -- the parent: one more child, the new node
        obtain ⟨_, _, hnext⟩ := hp (by omega)
        have hjp' : p - 1 = j := by omega
        subst hjp'
        simp only [show p - 1 + 1 = p by omega] at o1 o2 o3 o4 o9 o10 o13 hcross ⊢
        have hlt := (List.getElem?_eq_some_iff.1 hnext).1
        refine ⟨o1, o2, o3, o4, o5, o6, o7, o8, ?_, ?_, ?_, hparents, o13⟩
        · simp only [OnlineAnalyzerNode.addChild, List.length_append, List.length_singleton]
          omega
        · intro i hi
          simp only [OnlineAnalyzerNode.addChild, List.length_append, List.length_singleton] at hi
          simp only [OnlineAnalyzerNode.addChild]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
          · rw [List.getElem_append_left hi, hψle _ ?_]
            · exact o10 i hi
            · obtain ⟨-, c2, -⟩ := o11 _ (List.getElem_mem hi); omega
          · -- the new child is labelled with the next operand
            subst hi; rw [List.getElem_append_right (le_refl _)]
            simp only [List.getElem_singleton, ψ', if_pos rfl]; simpa using hnext
        · intro c hc
          simp only [OnlineAnalyzerNode.addChild, List.mem_append, List.mem_singleton] at hc
          rcases hc with hc | rfl
          · exact hcross c hc
          · refine ⟨by omega, by simp [hlen], ?_⟩
            simp only [show st.nodes.length + 1 - 1 = st.nodes.length by omega]
            rw [hgetN, k3]; simp
      · refine ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, fun i hi => ?_, hcross, hparents, o13⟩
        rw [hψle _ ?_]
        · exact o10 i hi
        · obtain ⟨-, c2, -⟩ := o11 _ (List.getElem_mem hi); omega
    · -- the new node
      subst h
      rw [hgetN]
      -- fresh from `mk?`: initial signal, no children, one parent `p`
      have e : ψ' (st.nodes.length + 1) = φ := by simp [ψ']
      unfold aux_NodeOk
      rw [e]
      refine ⟨k2, k1, k6, k7, k9, fun t ht => by rw [k10 t ht, k1], by rw [k8, k3], by simp [k3],
        by simp [k4], fun i hi => by simp [k4] at hi, fun c hc => by simp [k4] at hc,
        fun q hq => ?_, hsub⟩
      rw [k3] at hq; simp only [List.mem_singleton] at hq; subst hq
      -- the parent is the root's `0` or an inner node
      by_cases hq0 : q = 0
      · exact Or.inl hq0
      · obtain ⟨_, hq2, _⟩ := hp hq0
        exact Or.inr ⟨hq2, by omega, by rw [hψle q (by omega)]; exact hops hq0⟩
  · -- the cache
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨by omega, by simp [hlen], by simp [ψ']⟩
    · obtain ⟨e1, e2, e3⟩ := hcache e he
      exact ⟨e1, by simp only; rw [hlen]; omega, by rw [hψle _ e2]; exact e3⟩
  · -- the root
    by_cases hN0 : st.nodes.length = 0
    · have hp0 : p = 0 := by
        by_contra hp0; obtain ⟨hlt, _⟩ := hp hp0; omega
      obtain ⟨-, hφ⟩ := h0 hp0
      have : (nodes1 ++ [node])[0] = node := by
        have := hgetN (by omega); simp only [hN0] at this; exact this
      rw [this, k3, hp0]
      refine ⟨rfl, ?_⟩
      simp [ψ', hN0, hφ]
    · rw [hparN 0 (by omega)]
      obtain ⟨r1, r2⟩ := hroot (by omega)
      exact ⟨r1, by rw [hψle 1 (by omega)]; exact r2⟩
  · rw [hget _ h h1, if_pos (by omega)]; rfl

end parse3


section parse4

variable {S : ℕ → Type} {d : ℕ}

/-- What `parse` guarantees for the subformula `φ` under the parent `p`. -/
private def aux_Post (φ0 φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) (p : ℕ)
    (st st' : OnlineReachSetAnalyzer.ParseState ℝ S d)
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) : Prop :=
  ∃ ψ', aux_PInv φ0 st' ψ' ∧ (∀ i, 1 ≤ i → i ≤ st.nodes.length → ψ' i = ψ i) ∧
    st.nodes.length ≤ st'.nodes.length ∧ 0 < st'.nodes.length ∧
    (∀ j (h : j < st.nodes.length) (h1 : j < st'.nodes.length), j + 1 ≠ p →
      st'.nodes[j].children = st.nodes[j].children) ∧
    (p ≠ 0 → ∀ (h : p - 1 < st.nodes.length) (h1 : p - 1 < st'.nodes.length), ∃ c, ψ' c = φ ∧
      st'.nodes[p - 1].children = st.nodes[p - 1].children ++ [c]) ∧
    (∀ j (h1 : j < st'.nodes.length), st.nodes.length ≤ j →
      st'.nodes[j].children.length = (aux_ops (ψ' (j + 1))).length)

/-- What `parse` needs for the subformula `φ` under the parent `p`. -/
private def aux_Pre (φ0 φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) (p : ℕ)
    (st : OnlineReachSetAnalyzer.ParseState ℝ S d)
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) : Prop :=
  aux_PInv φ0 st ψ ∧ φ.IsSub φ0 ∧ (p = 0 → st.nodes.length = 0 ∧ φ = φ0) ∧
    (p ≠ 0 → ∃ hp : p - 1 < st.nodes.length, 1 ≤ p ∧
      (aux_ops (ψ p))[st.nodes[p - 1].children.length]? = some φ)

/-- A cache hit for `φ` reuses the node of `φ`, since keys tell the subformulas of `φ0` apart. -/
private theorem aux_parse_hit_post (φ0 : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (hkey : ∀ a b : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d), a.IsSub φ0 →
      b.IsSub φ0 → a.key.keyEqv b.key = true → a = b)
    (φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) (p : ℕ)
    (st st' : OnlineReachSetAnalyzer.ParseState ℝ S d)
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (hpre : aux_Pre φ0 φ p st ψ) (k : OnlineReachSetAnalyzer.Formula ℝ Unit) (c : ℕ)
    -- the cache hit, and the updates of the hit node and of the parent
    (hfind : st.cache.find? (fun q => q.1.keyEqv φ.key) = some (k, c))
    (h : ((OnlineReachSetAnalyzer.updateNode st.nodes c
        (fun n => some (n.addParent p))).bind fun nodes =>
          (OnlineReachSetAnalyzer.updateNode nodes p (fun n => some (n.addChild c))).map
            fun nodes => ({ st with nodes := nodes } : OnlineReachSetAnalyzer.ParseState ℝ S d)) =
      some st') : -- --- CONCL ---
    aux_Post φ0 φ p st st' ψ := by -- --- PROOF ---
  obtain ⟨hinv, hsub, h0, hp⟩ := hpre
  -- the hit node `c` has the key of `φ`, so is the node of `φ`
  have hmem := List.mem_of_find?_eq_some hfind
  have hk := List.find?_some hfind
  obtain ⟨c1, c2, c3⟩ := hinv.2.1 _ hmem
  simp only at c1 c2 c3 hk
  have hc : c - 1 < st.nodes.length := by omega
  have hψc : ψ c = φ := by
    apply hkey _ _ _ hsub
    · rw [← c3]; exact hk
    · have := (hinv.1 (c - 1) hc).2.2.2.2.2.2.2.2.2.2.2.2
      rwa [show c - 1 + 1 = c by omega] at this
  have hp0 : p ≠ 0 := fun e => by have := (h0 e).1; omega
  obtain ⟨hp', hp1, hnext⟩ := hp hp0
  have hops : aux_ops (ψ p) ≠ [] := fun e => by rw [e] at hnext; simp at hnext
  -- `φ` is below the root, so its node is not the root
  have hc1 : c ≠ 1 := by
    intro e; subst e
    have hroot := (hinv.2.2 (by omega)).2
    have hpsub := (hinv.1 (p - 1) hp').2.2.2.2.2.2.2.2.2.2.2.2
    rw [show p - 1 + 1 = p by omega] at hpsub
    have h1 := aux_sizeOf_ops _ _ (List.mem_of_getElem? hnext)
    have h2 := aux_sizeOf_isSub _ _ hpsub
    rw [hroot] at hψc; rw [hψc] at h2; omega
  obtain ⟨nodes1, h1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨nodes2, h2, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨-, n, n', hn, hfn, rfl⟩ := (OnlineReachSetAnalyzer.updateNode_eq_some_iff _ _ _ _).1 h1
  obtain rfl := Option.some.inj hfn
  have hnn : st.nodes[c - 1] = n := (List.getElem?_eq_some_iff.1 hn).2
  subst hnn
  have inv1 := aux_pinv_addParent φ0 ψ st hinv c p c1 hc hp1 (by omega) hops hc1
  obtain ⟨-, m, m', hm, hfm, rfl⟩ := (OnlineReachSetAnalyzer.updateNode_eq_some_iff _ _ _ _).1 h2
  obtain rfl := Option.some.inj hfm
  -- the children lists are those before but at `p`
  have hl1 : (st.nodes.set (c - 1) (st.nodes[c - 1].addParent p)).length = st.nodes.length := by
      simp
  have hp'' : p - 1 < (st.nodes.set (c - 1) (st.nodes[c - 1].addParent p)).length := by
    rw [hl1]; exact hp'
  have hmm : (st.nodes.set (c - 1) (st.nodes[c - 1].addParent p))[p - 1] = m :=
    (List.getElem?_eq_some_iff.1 hm).2
  subst hmm
  have hch : ∀ j (h : j < st.nodes.length)
      (h' : j < (st.nodes.set (c - 1) (st.nodes[c - 1].addParent p)).length),
      (st.nodes.set (c - 1) (st.nodes[c - 1].addParent p))[j].children = st.nodes[j].children := by
    intro j h h'; rw [List.getElem_set]; split_ifs with e
    · subst e; rfl
    · rfl
  have inv2 := aux_pinv_addChild φ0 ψ _ inv1 p c hp1 hp'' c1 (by simpa using hc)
    (by simp only [List.getElem_set_self, OnlineAnalyzerNode.addParent]; simp)
    (by rw [hch _ hp' hp'', hψc]; exact hnext)
  -- no new node: the labelling stays
  refine ⟨ψ, inv2, fun _ _ _ => rfl, by simp, by simp; omega, fun j h h1 hjp => ?_,
    fun _ h h1 => ⟨c, hψc, ?_⟩, fun j h1 hj => by simp at h1; omega⟩
  · rw [List.getElem_set_ne (by omega)]
    exact hch j h (by simpa using h)
  · simp only [List.getElem_set_self, OnlineAnalyzerNode.addChild]
    rw [hch _ hp' hp'']

end parse4


section parse5

variable {S : ℕ → Type} {d : ℕ}

/-- Midway through the operands of the new node `N + 1` for `φ`: `m` of them are parsed. -/
private def aux_Mid (φ0 φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) (p : ℕ)
    (st stk : OnlineReachSetAnalyzer.ParseState ℝ S d)
    (ψ ψk : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) (m : ℕ) : Prop :=
  aux_PInv φ0 stk ψk ∧ (∀ i, 1 ≤ i → i ≤ st.nodes.length → ψk i = ψ i) ∧
    ψk (st.nodes.length + 1) = φ ∧ st.nodes.length < stk.nodes.length ∧
    (∀ j (h : j < st.nodes.length) (h1 : j < stk.nodes.length), j + 1 ≠ p →
      stk.nodes[j].children = st.nodes[j].children) ∧
    (p ≠ 0 → ∀ (h : p - 1 < st.nodes.length) (h1 : p - 1 < stk.nodes.length),
      stk.nodes[p - 1].children = st.nodes[p - 1].children ++ [st.nodes.length + 1]) ∧
    (∀ h1 : st.nodes.length < stk.nodes.length, stk.nodes[st.nodes.length].children.length = m) ∧
    (∀ j (h1 : j < stk.nodes.length), st.nodes.length < j →
      stk.nodes[j].children.length = (aux_ops (ψk (j + 1))).length)

/-- `parseNew` starts the operands of the new node with none parsed. -/
private theorem aux_mid_init (φ0 φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (dp : Bool) (p : ℕ) (st st1 : OnlineReachSetAnalyzer.ParseState ℝ S d)
    (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (hpre : aux_Pre φ0 φ p st ψ)
        (h : OnlineReachSetAnalyzer.parseNew dp φ p st = some st1) : -- --- CONCL ---
    aux_Mid φ0 φ p st st1 ψ (fun i => if i = st.nodes.length + 1 then φ else ψ i) 0
    := by -- --- PROOF ---
  obtain ⟨hinv, hsub, h0, hp⟩ := hpre
  obtain ⟨i1, i2, i3, i4, i5⟩ := aux_pinv_new φ0 ψ dp φ p st st1 hinv hsub h0 hp h
  refine ⟨i1, fun i _ hi => by simp only; rw [if_neg (by omega)], by simp, by omega,
    fun j h h1 hjp => i4 j h h1 hjp, fun hp0 h h1 => i5 hp0 h h1, fun h1 => by rw [i3 h1]; rfl,
    fun j h1 hj => by omega⟩

/-- Midway, the next operand meets what `parse` needs. -/
private theorem aux_mid_pre (φ0 φ a : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (p : ℕ)
    (st stk : OnlineReachSetAnalyzer.ParseState ℝ S d)
    (ψ ψk : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) (m : ℕ)
    (hmid : aux_Mid φ0 φ p st stk ψ ψk m) (hsub : φ.IsSub φ0)
    (ha : (aux_ops φ)[m]? = some a) : -- --- CONCL ---
    aux_Pre φ0 a (st.nodes.length + 1) stk ψk := by -- --- PROOF ---
  obtain ⟨i1, -, i3, i4, -, -, i7, -⟩ := hmid
  refine ⟨i1, aux_isSub_trans (aux_isSub_of_mem_ops _ _ (List.mem_of_getElem? ha)) hsub,
    fun e => by omega, fun _ => ⟨by simpa using i4, by omega, ?_⟩⟩
  simp only [Nat.add_sub_cancel]
  rw [i3, i7 i4]; exact ha

/-- Parsing one more operand moves midway on by one. -/
private theorem aux_mid_step (φ0 φ a : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (p : ℕ)
    (st stk stk' : OnlineReachSetAnalyzer.ParseState ℝ S d)
    (ψ ψk : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) (m : ℕ)
    (_hp : p ≤ st.nodes.length)
    (hmid : aux_Mid φ0 φ p st stk ψ ψk m)
    (hpost : aux_Post φ0 a (st.nodes.length + 1) stk stk' ψk) : -- --- CONCL ---
    ∃ ψk', aux_Mid φ0 φ p st stk' ψ ψk' (m + 1) := by -- --- PROOF ---
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hmid
  obtain ⟨ψk', q1, q2, q3, q4, q5, q6, q7⟩ := hpost
  refine ⟨ψk', q1, fun i hi1 hi => by rw [q2 i hi1 (by omega), i2 i hi1 hi],
    by rw [q2 _ (by omega) (by omega), i3], by omega, fun j h h1 hjp => ?_, fun hp0 h h1 => ?_,
    fun h1 => ?_, fun j h1 hj => ?_⟩
  · rw [q5 j (by omega) h1 (by omega)]; exact i5 j h (by omega) hjp
  · rw [q5 _ (by omega) h1 (by omega)]; exact i6 hp0 h (by omega)
  · obtain ⟨c, -, hc⟩ := q6 (by omega) (by simpa using i4) (by simpa using h1)
    simp only [Nat.add_sub_cancel] at hc
    rw [hc, List.length_append, i7 i4]; rfl
  · by_cases hjk : j < stk.nodes.length
    · rw [q5 j hjk h1 (by omega), i8 j hjk hj, q2 _ (by omega) (by omega)]
    · exact q7 j h1 (by omega)

/-- All operands parsed is what `parse` guarantees. -/
private theorem aux_mid_final (φ0 φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (p : ℕ)
    (st st' : OnlineReachSetAnalyzer.ParseState ℝ S d)
    (ψ ψ' : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (hmid : aux_Mid φ0 φ p st st' ψ ψ' (aux_ops φ).length) : -- --- CONCL ---
    aux_Post φ0 φ p st st' ψ := by -- --- PROOF ---
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hmid
  refine ⟨ψ', i1, i2, by omega, by omega, i5, fun hp0 h h1 => ⟨_, i3, i6 hp0 h h1⟩,
    fun j h1 hj => ?_⟩
  rcases hj.lt_or_eq with hj | rfl
  · exact i8 j h1 hj
  · rw [i7 h1, i3]

end parse5


section parse6

variable {S : ℕ → Type} {d : ℕ}

/-- `parse` builds the node of every subformula under its parent, by induction on its size. -/
private theorem aux_parse_post (dp : Bool)
    (φ0 : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (hkey : ∀ a b : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d), a.IsSub φ0 →
      b.IsSub φ0 → a.key.keyEqv b.key = true → a = b) : -- --- CONCL ---
    ∀ (φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) (p : ℕ)
      (st st' : OnlineReachSetAnalyzer.ParseState ℝ S d)
      (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)),
      aux_Pre φ0 φ p st ψ → OnlineReachSetAnalyzer.parse dp φ p st = some st' →
      aux_Post φ0 φ p st st' ψ := by -- --- PROOF ---
  intro φ
  induction φ with
  -- a leaf: a cache hit, or a new node with no operands
  | tt | ff | ap =>
    intro p st st' ψ hpre h
    rw [OnlineReachSetAnalyzer.parse] at h
    split at h
    · rename_i k c hc
      exact aux_parse_hit_post φ0 hkey _ p st st' ψ hpre k c hc h
    · obtain ⟨st1, h1, h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      obtain rfl := Option.some.inj h
      exact aux_mid_final φ0 _ p st st1 ψ _ (aux_mid_init φ0 _ dp p st st1 ψ hpre h1)
  -- one operand: a hit, or a new node and its operand parsed below it
  | not a ih =>
    intro p st st' ψ hpre h
    rw [OnlineReachSetAnalyzer.parse] at h
    split at h
    · rename_i k c hc
      exact aux_parse_hit_post φ0 hkey _ p st st' ψ hpre k c hc h
    · obtain ⟨st1, h1, h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      have hp : p ≤ st.nodes.length := by
        by_cases hp0 : p = 0
        · omega
        · obtain ⟨hp', -⟩ := hpre.2.2.2 hp0; omega
      have m0 := aux_mid_init φ0 _ dp p st st1 ψ hpre h1
      have post := ih _ st1 st' _ (aux_mid_pre φ0 _ a p st st1 ψ _ 0 m0 hpre.2.1 rfl) h
      obtain ⟨ψ1, m1⟩ := aux_mid_step φ0 _ a p st st1 st' ψ _ 0 hp m0 post
      exact aux_mid_final φ0 _ p st st' ψ ψ1 m1
  -- two operands, parsed in turn below the new node
  | and a b iha ihb | or a b iha ihb | «until» _ a b iha ihb =>
    intro p st st' ψ hpre h
    rw [OnlineReachSetAnalyzer.parse] at h
    split at h
    · rename_i k c hc
      exact aux_parse_hit_post φ0 hkey _ p st st' ψ hpre k c hc h
    · obtain ⟨st1, h1, h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      obtain ⟨st2, h2, h3⟩ := Option.bind_eq_some_iff.mp h
      have hp : p ≤ st.nodes.length := by
        by_cases hp0 : p = 0
        · omega
        · obtain ⟨hp', -⟩ := hpre.2.2.2 hp0; omega
      have m0 := aux_mid_init φ0 _ dp p st st1 ψ hpre h1
      have post1 := iha _ st1 st2 _ (aux_mid_pre φ0 _ a p st st1 ψ _ 0 m0 hpre.2.1 rfl) h2
      obtain ⟨ψ1, m1⟩ := aux_mid_step φ0 _ a p st st1 st2 ψ _ 0 hp m0 post1
      -- then the second
      have post2 := ihb _ st2 st' _ (aux_mid_pre φ0 _ b p st st2 ψ _ 1 m1 hpre.2.1 rfl) h3
      obtain ⟨ψ2, m2⟩ := aux_mid_step φ0 _ b p st st2 st' ψ _ 1 hp m1 post2
      exact aux_mid_final φ0 _ p st st' ψ ψ2 m2

end parse6


section parse7

variable {S : ℕ → Type} {d : ℕ}

/-- A node fine in the parse invariant, with all its operands, is the node of its formula. -/
private theorem aux_shapeOf_of {A : Type} (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A)
    (φ : OnlineReachSetAnalyzer.Formula ℝ A) (n : OnlineAnalyzerNode ℝ A)
    (h1 : n.kind = φ.kind) (h2 : n.interval = φ.interval?) (h3 : n.ap = φ.ap?)
    (h4 : n.children.length = (aux_ops φ).length)
    (h5 : ∀ i (hi : i < n.children.length), (aux_ops φ)[i]? = some
        (ψ n.children[i])) : -- --- CONCL ---
    OnlineReachSetAnalyzer.IsNodeOf ψ φ n := by -- --- PROOF ---
  cases φ <;> simp only [OnlineReachSetAnalyzer.IsNodeOf, OnlineReachSetAnalyzer.Formula.kind,
    OnlineReachSetAnalyzer.Formula.interval?, OnlineReachSetAnalyzer.Formula.ap?, aux_ops,
    List.length_nil, List.length_cons] at h1 h2 h3 h4 h5 ⊢
  · exact ⟨h1, List.eq_nil_of_length_eq_zero h4⟩
  · exact ⟨h1, List.eq_nil_of_length_eq_zero h4⟩
  · exact ⟨h1, List.eq_nil_of_length_eq_zero h4, h3⟩
  · obtain ⟨c, hc⟩ := List.length_eq_one_iff.1 h4
    refine ⟨h1, c, hc, ?_⟩
    have := h5 0 (by omega); simp [hc] at this; exact this.symm
  · -- binary operators: the two children by position
    obtain ⟨c, c', hc⟩ := List.length_eq_two.1 h4
    have e0 := h5 0 (by omega); have e1 := h5 1 (by omega)
    simp [hc] at e0 e1
    exact ⟨h1, c, c', hc, e0.symm, e1.symm⟩
  · obtain ⟨c, c', hc⟩ := List.length_eq_two.1 h4
    have e0 := h5 0 (by omega); have e1 := h5 1 (by omega)
    simp [hc] at e0 e1
    exact ⟨h1, c, c', hc, e0.symm, e1.symm⟩
  · obtain ⟨c, c', hc⟩ := List.length_eq_two.1 h4
    have e0 := h5 0 (by omega); have e1 := h5 1 (by omega)
    simp [hc] at e0 e1
    exact ⟨h1, h2, c, c', hc, e0.symm, e1.symm⟩

end parse7


section keys

variable {S : ℕ → Type} {d : ℕ}

/-- `keyEqv` at `eps = 0` is equality of keys. -/
private theorem aux_keyEqv_eq :
    ∀ k k' : OnlineReachSetAnalyzer.Formula ℝ Unit, k.keyEqv k' = true → k = k'
  | .tt, .tt, _ => rfl
  | .ff, .ff, _ => rfl
  | .ap a _, .ap b _, h => by simp [OnlineReachSetAnalyzer.Formula.keyEqv] at h; subst h; rfl
  | .not a, .not b, h => by
    simp only [OnlineReachSetAnalyzer.Formula.keyEqv] at h; rw [aux_keyEqv_eq a b h]
  | .and a a', .and b b', h => by
    simp only [OnlineReachSetAnalyzer.Formula.keyEqv, Bool.and_eq_true] at h
    rw [aux_keyEqv_eq a b h.1, aux_keyEqv_eq a' b' h.2]
  | .or a a', .or b b', h => by
    simp only [OnlineReachSetAnalyzer.Formula.keyEqv, Bool.and_eq_true] at h
    rw [aux_keyEqv_eq a b h.1, aux_keyEqv_eq a' b' h.2]
  | .until I a a', .until J b b', h => by
    simp only [OnlineReachSetAnalyzer.Formula.keyEqv, Bool.and_eq_true] at h
    have hIJ : I = J := STLInterval.set_injective
      ((STLInterval.isequal_zero_iff I J).1 (by
        have := (STLInterval.isequalFloat_iff 0 I J).1 h.1.1; simpa using this))
    rw [hIJ, aux_keyEqv_eq a b h.1.2, aux_keyEqv_eq a' b' h.2]
  -- different constructors have different keys
  | .tt, .ff, h | .tt, .ap .., h | .tt, .not _, h | .tt, .and .., h | .tt, .or .., h
  | .tt, .until .., h => by simp [OnlineReachSetAnalyzer.Formula.keyEqv] at h
  | .ff, .tt, h | .ff, .ap .., h | .ff, .not _, h | .ff, .and .., h | .ff, .or .., h
  | .ff, .until .., h => by simp [OnlineReachSetAnalyzer.Formula.keyEqv] at h
  | .ap .., .tt, h | .ap .., .ff, h | .ap .., .not _, h | .ap .., .and .., h | .ap .., .or .., h
  | .ap .., .until .., h => by simp [OnlineReachSetAnalyzer.Formula.keyEqv] at h
  | .not _, .tt, h | .not _, .ff, h | .not _, .ap .., h | .not _, .and .., h | .not _, .or .., h
  | .not _, .until .., h => by simp [OnlineReachSetAnalyzer.Formula.keyEqv] at h
  | .and .., .tt, h | .and .., .ff, h | .and .., .ap .., h | .and .., .not _, h
  | .and .., .or .., h | .and .., .until .., h => by
    simp [OnlineReachSetAnalyzer.Formula.keyEqv] at h
  | .or .., .tt, h | .or .., .ff, h | .or .., .ap .., h | .or .., .not _, h
  | .or .., .and .., h | .or .., .until .., h => by
    simp [OnlineReachSetAnalyzer.Formula.keyEqv] at h
  | .until .., .tt, h | .until .., .ff, h | .until .., .ap .., h | .until .., .not _, h
  | .until .., .and .., h | .until .., .or .., h => by
    simp [OnlineReachSetAnalyzer.Formula.keyEqv] at h

/-- Two subformulas of `φ` with one key are equal when a label names one atom in `φ`. -/
private theorem aux_key_inj (φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (hlabel : ∀ l x y, (OnlineReachSetAnalyzer.Formula.ap l x).IsSub φ →
      (OnlineReachSetAnalyzer.Formula.ap l y).IsSub φ → x = y) : -- --- CONCL ---
    ∀ a b : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d), a.IsSub φ → b.IsSub φ →
      a.key = b.key → a = b := by -- --- PROOF ---
  intro a
  induction a with
  | tt => intro b _ _ h; cases b <;> simp [OnlineReachSetAnalyzer.Formula.key] at h ⊢
  | ff => intro b _ _ h; cases b <;> simp [OnlineReachSetAnalyzer.Formula.key] at h ⊢
  | ap l x =>
    intro b ha hb h
    cases b <;> simp [OnlineReachSetAnalyzer.Formula.key] at h ⊢
    subst h; exact ⟨rfl, hlabel _ _ _ ha hb⟩
  -- one operand: the keys of the operands agree
  | not a ih =>
    intro b ha hb h
    cases b <;> simp [OnlineReachSetAnalyzer.Formula.key] at h ⊢
    exact ih _ (aux_isSub_trans (aux_isSub_of_mem_ops (.not a) a (by simp [aux_ops])) ha)
      (aux_isSub_trans (aux_isSub_of_mem_ops (.not _) _ (by simp [aux_ops])) hb) h
  | and a a' ih ih' =>
    intro b ha hb h
    cases b <;> simp [OnlineReachSetAnalyzer.Formula.key] at h ⊢
    exact ⟨ih _ (aux_isSub_trans (aux_isSub_of_mem_ops (.and a a') a (by simp [aux_ops])) ha)
      (aux_isSub_trans (aux_isSub_of_mem_ops (.and _ _) _ (by simp [aux_ops])) hb) h.1,
      ih' _ (aux_isSub_trans (aux_isSub_of_mem_ops (.and a a') a' (by simp [aux_ops])) ha)
      (aux_isSub_trans (aux_isSub_of_mem_ops (.and _ _) _ (by simp [aux_ops])) hb) h.2⟩
  -- binary operators: both operands' keys agree
  | or a a' ih ih' =>
    intro b ha hb h
    cases b <;> simp [OnlineReachSetAnalyzer.Formula.key] at h ⊢
    exact ⟨ih _ (aux_isSub_trans (aux_isSub_of_mem_ops (.or a a') a (by simp [aux_ops])) ha)
      (aux_isSub_trans (aux_isSub_of_mem_ops (.or _ _) _ (by simp [aux_ops])) hb) h.1,
      ih' _ (aux_isSub_trans (aux_isSub_of_mem_ops (.or a a') a' (by simp [aux_ops])) ha)
      (aux_isSub_trans (aux_isSub_of_mem_ops (.or _ _) _ (by simp [aux_ops])) hb) h.2⟩
  | «until» I a a' ih ih' =>
    intro b ha hb h
    cases b <;> simp [OnlineReachSetAnalyzer.Formula.key] at h ⊢
    exact ⟨h.1,
      ih _ (aux_isSub_trans (aux_isSub_of_mem_ops (.until I a a') a (by simp [aux_ops])) ha)
      (aux_isSub_trans (aux_isSub_of_mem_ops (.until _ _ _) _ (by simp [aux_ops])) hb) h.2.1,
      ih' _ (aux_isSub_trans (aux_isSub_of_mem_ops (.until I a a') a' (by simp [aux_ops])) ha)
      (aux_isSub_trans (aux_isSub_of_mem_ops (.until _ _ _) _ (by simp [aux_ops])) hb) h.2.2⟩

end keys


section main

variable {S : ℕ → Type} {d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.mk?_nodes_spec
    (φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (hlabel : ∀ l x y, (OnlineReachSetAnalyzer.Formula.ap l x).IsSub φ →
      (OnlineReachSetAnalyzer.Formula.ap l y).IsSub φ → x = y)
    (f : ℕ) (dp : Bool) : -- --- CONCL ---
    ∀ obj ∈ OnlineReachSetAnalyzer.mk? φ f dp,
      ∃ ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d), ψ 1 = φ ∧
        obj.propagationFrequency = f ∧ ∃ h0 : 0 < obj.nodes.length, obj.nodes[0].parents = [0] ∧
        ∀ j (h : j < obj.nodes.length), obj.nodes[j].idx = j + 1 ∧
          OnlineReachSetAnalyzer.IsNodeOf ψ (ψ (j + 1)) obj.nodes[j] ∧
          obj.nodes[j].prop = obj.nodes[j].parents.map (fun _ => STLInterval.empty) ∧
          obj.nodes[j].signal.IsValid ∧
          (∀ t : ℝ, 0 ≤ t → obj.nodes[j].signal.at t = obj.nodes[j].kind.initValue) ∧
          (∀ c ∈ obj.nodes[j].children,
            1 ≤ c ∧ ∃ hc : c - 1 < obj.nodes.length, j + 1 ∈ obj.nodes[c - 1].parents) ∧
          ∀ l a, ψ (j + 1) = .ap l a → j + 1 ∈ obj.leaves := by -- --- PROOF ---
  intro obj h
  -- the cache merges only equal subformulas
  have hkey : ∀ a b : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d), a.IsSub φ →
      b.IsSub φ → a.key.keyEqv b.key = true → a = b := fun a b ha hb h =>
    aux_key_inj φ hlabel a b ha hb (aux_keyEqv_eq _ _ h)
  unfold OnlineReachSetAnalyzer.mk? at h
  obtain ⟨st, hparse, rfl⟩ := Option.map_eq_some_iff.mp h
  have hpre : aux_Pre φ φ 0 ⟨[], []⟩ (fun _ => φ) :=
    ⟨⟨fun j h => absurd h (by simp), fun e he => absurd he (by simp), fun h => absurd h (by simp)⟩,
      aux_isSub_refl φ, fun _ => ⟨rfl, rfl⟩, fun h => absurd rfl h⟩
  -- `parse` from the empty state builds the whole DAG
  obtain ⟨ψ, ⟨hn, -, hroot⟩, -, -, hpos, -, -, hcomp⟩ :=
    aux_parse_post dp φ hkey φ 0 ⟨[], []⟩ st (fun _ => φ) hpre hparse
  refine ⟨ψ, (hroot hpos).2, rfl, hpos, (hroot hpos).1, fun j h => ?_⟩
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, -, -, o10, o11, -, -⟩ := hn j h
  refine ⟨o1, aux_shapeOf_of ψ _ _ o2 o3 o4 (hcomp j h (Nat.zero_le _)) o10, o7, o5, o6, o11,
    fun l a hψ => ?_⟩
  -- every atom's node is a leaf: no node has it as a child
  simp only [List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq, List.mem_flatMap,
    not_exists, not_and]
  refine ⟨⟨j, h, rfl⟩, fun n hnm hjn => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hnm
  rcases (hn i hi).2.2.2.2.2.2.2.2.2.2.2.1 (j + 1) hjn with e | ⟨-, -, hops⟩
  · omega
  · rw [hψ] at hops; exact hops rfl

end main

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
