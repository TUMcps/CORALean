module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Parse
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ExtTrans
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ParseNewSpec

@[expose] public section

/-!
# What parsing keeps

Parsing a subformula keeps the invariant of the nodes (node `j` has index `j + 1`, every node has
the right `dropPropagated` and a first parent) and only extends them: the old nodes stay, up to
the edges added to them, and new ones are appended.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {d : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The branch of a subformula that already has a node: two edges are added. -/
theorem aux_parse_hit (dp : Bool) (st st' : OnlineReachSetAnalyzer.ParseState S d) (c parent : ℕ)
    (hinv : OnlineReachSetAnalyzer.NodesInv dp st.nodes)
    (h : ((OnlineReachSetAnalyzer.updateNode st.nodes c
        (fun n => some (n.addParent parent))).bind fun nodes =>
          (OnlineReachSetAnalyzer.updateNode nodes parent (fun n => some (n.addChild c))).map
            fun nodes => ({ st with nodes := nodes } : OnlineReachSetAnalyzer.ParseState S d)) =
      some st') :
    OnlineReachSetAnalyzer.NodesInv dp st'.nodes ∧ OnlineReachSetAnalyzer.Ext st.nodes st'.nodes ∧
      st.nodes ≠ [] := by -- --- PROOF ---
  obtain ⟨nodes1, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨nodes2, h2, rfl⟩ := Option.map_eq_some_iff.mp h
  -- a parent is added: the first one stays
  obtain ⟨e1, l1⟩ := OnlineReachSetAnalyzer.ext_updateNode _ _ _ _ h1 fun n hn n' hn' => by
    obtain rfl := Option.some.inj hn'
    obtain ⟨-, hp⟩ := hinv.2 n hn
    exact ⟨rfl, rfl, by
      cases hps : n.parents <;> simp_all [OnlineAnalyzerNode.addParent], rfl⟩
  have hinv1 := OnlineReachSetAnalyzer.nodesInv_of_ext dp _ _ l1 e1 hinv
  -- a child is added
  obtain ⟨e2, l2⟩ := OnlineReachSetAnalyzer.ext_updateNode _ _ _ _ h2 fun n hn n' hn' => by
    obtain rfl := Option.some.inj hn'
    exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨OnlineReachSetAnalyzer.nodesInv_of_ext dp _ _ l2 e2 hinv1,
    OnlineReachSetAnalyzer.ext_trans e1 e2, ?_⟩
  -- the node that was updated is in the list
  obtain ⟨-, n, n', hn, -⟩ := (OnlineReachSetAnalyzer.updateNode_eq_some_iff _ _ _ _).mp h1
  intro hnil
  simp [hnil] at hn


/-- The first node made is the root: it keeps its type and its first parent. -/
theorem aux_parse_root (st st1 st' : OnlineReachSetAnalyzer.ParseState S d) (parent : ℕ)
    (k : OnlineAnalyzerNode.Kind)
    (hnode : ∃ node, st1.nodes[st.nodes.length]? = some node ∧ node.kind = k ∧
      node.parents = [parent]) (hnil : st.nodes = [])
    (hext : OnlineReachSetAnalyzer.Ext st1.nodes st'.nodes) :
    ∃ root, st'.nodes[0]? = some root ∧ root.kind = k ∧
      root.parents.head? = some parent := by -- --- PROOF ---
  obtain ⟨node, hn, hk, hp⟩ := hnode
  rw [hnil, List.length_nil] at hn
  obtain ⟨hlt, hnode0⟩ := List.getElem?_eq_some_iff.mp hn
  have hlt' : 0 < st'.nodes.length := lt_of_lt_of_le hlt hext.1
  have hs := hext.2 0 hlt hlt'
  rw [hnode0] at hs
  exact ⟨st'.nodes[0], by simp [List.getElem?_eq_getElem hlt'], hs.2.1 ▸ hk,
    by rw [← hs.2.2.1, hp]; rfl⟩


/-- The conclusion for a subformula without operands. -/
theorem aux_parse_leaf (dp : Bool) (st st1 : OnlineReachSetAnalyzer.ParseState S d) (parent : ℕ)
    (k : OnlineAnalyzerNode.Kind) (hi1 : OnlineReachSetAnalyzer.NodesInv dp st1.nodes)
    (he1 : OnlineReachSetAnalyzer.Ext st.nodes st1.nodes)
    (hnode : ∃ node, st1.nodes[st.nodes.length]? = some node ∧ node.kind = k ∧
      node.parents = [parent]) :
    OnlineReachSetAnalyzer.NodesInv dp st1.nodes ∧ OnlineReachSetAnalyzer.Ext st.nodes st1.nodes ∧
      (st.nodes = [] → ∃ root, st1.nodes[0]? = some root ∧ root.kind = k ∧
        root.parents.head? = some parent) :=
  ⟨hi1, he1, fun hnil =>
    aux_parse_root st st1 st1 parent k hnode hnil (OnlineReachSetAnalyzer.ext_refl _)⟩


/-- The conclusion once the node and its two operands are parsed. -/
theorem aux_parse_chain (dp : Bool) (st st1 st2 st' : OnlineReachSetAnalyzer.ParseState S d)
    (parent : ℕ) (k : OnlineAnalyzerNode.Kind)
    (he1 : OnlineReachSetAnalyzer.Ext st.nodes st1.nodes)
    (hnode : ∃ node, st1.nodes[st.nodes.length]? = some node ∧ node.kind = k ∧
      node.parents = [parent])
    (he2 : OnlineReachSetAnalyzer.Ext st1.nodes st2.nodes)
    (he3 : OnlineReachSetAnalyzer.Ext st2.nodes st'.nodes)
    (hi3 : OnlineReachSetAnalyzer.NodesInv dp st'.nodes) :
    OnlineReachSetAnalyzer.NodesInv dp st'.nodes ∧ OnlineReachSetAnalyzer.Ext st.nodes st'.nodes ∧
      (st.nodes = [] → ∃ root, st'.nodes[0]? = some root ∧ root.kind = k ∧
        root.parents.head? = some parent) :=
  ⟨hi3, OnlineReachSetAnalyzer.ext_trans he1 (OnlineReachSetAnalyzer.ext_trans he2 he3),
    fun hnil => aux_parse_root st st1 st' parent k hnode hnil
      (OnlineReachSetAnalyzer.ext_trans he2 he3)⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.parse_spec (dp : Bool) :
    ∀ (φ : OnlineReachSetAnalyzer.Formula (AtomicProposition S d)) (parent : ℕ)
      (st st' : OnlineReachSetAnalyzer.ParseState S d),
      OnlineReachSetAnalyzer.NodesInv dp st.nodes →
      OnlineReachSetAnalyzer.parse dp φ parent st = some st' →
      OnlineReachSetAnalyzer.NodesInv dp st'.nodes ∧
        OnlineReachSetAnalyzer.Ext st.nodes st'.nodes ∧
        (st.nodes = [] → ∃ root, st'.nodes[0]? = some root ∧ root.kind = φ.kind ∧
          root.parents.head? = some parent) := by -- --- PROOF ---
  intro φ
  induction φ with
  | tt =>
    intro parent st st' hinv h
    rw [OnlineReachSetAnalyzer.parse] at h
    split at h
    · rename_i c hc
      obtain ⟨h1, h2, h3⟩ := aux_parse_hit dp st st' c parent hinv h
      exact ⟨h1, h2, fun hnil => absurd hnil h3⟩
    · -- a new node with no operands
      obtain ⟨st1, h1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨hi1, he1, hnode⟩ := OnlineReachSetAnalyzer.parseNew_spec dp _ _ _ _ hinv h1
      dsimp only at h
      obtain rfl := Option.some.inj h
      exact aux_parse_leaf dp st st1 parent _ hi1 he1 hnode
  | ff =>
    intro parent st st' hinv h
    rw [OnlineReachSetAnalyzer.parse] at h
    split at h
    · rename_i c hc
      obtain ⟨h1, h2, h3⟩ := aux_parse_hit dp st st' c parent hinv h
      exact ⟨h1, h2, fun hnil => absurd hnil h3⟩
    · -- a new node with no operands
      obtain ⟨st1, h1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨hi1, he1, hnode⟩ := OnlineReachSetAnalyzer.parseNew_spec dp _ _ _ _ hinv h1
      dsimp only at h
      obtain rfl := Option.some.inj h
      exact aux_parse_leaf dp st st1 parent _ hi1 he1 hnode
  | ap l a =>
    intro parent st st' hinv h
    rw [OnlineReachSetAnalyzer.parse] at h
    split at h
    · rename_i c hc
      obtain ⟨h1, h2, h3⟩ := aux_parse_hit dp st st' c parent hinv h
      exact ⟨h1, h2, fun hnil => absurd hnil h3⟩
    · -- a new node with no operands
      obtain ⟨st1, h1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨hi1, he1, hnode⟩ := OnlineReachSetAnalyzer.parseNew_spec dp _ _ _ _ hinv h1
      dsimp only at h
      obtain rfl := Option.some.inj h
      exact aux_parse_leaf dp st st1 parent _ hi1 he1 hnode
  | not a ih =>
    intro parent st st' hinv h
    rw [OnlineReachSetAnalyzer.parse] at h
    split at h
    · rename_i c hc
      obtain ⟨h1, h2, h3⟩ := aux_parse_hit dp st st' c parent hinv h
      exact ⟨h1, h2, fun hnil => absurd hnil h3⟩
    · -- a new node, then its operand
      obtain ⟨st1, h1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨hi1, he1, hnode⟩ := OnlineReachSetAnalyzer.parseNew_spec dp _ _ _ _ hinv h1
      dsimp only at h
      obtain ⟨hi2, he2, -⟩ := ih _ _ _ hi1 h
      exact ⟨hi2, OnlineReachSetAnalyzer.ext_trans he1 he2, fun hnil =>
        aux_parse_root st st1 _ parent _ hnode hnil he2⟩
  | and a b iha ihb =>
    intro parent st st' hinv h
    rw [OnlineReachSetAnalyzer.parse] at h
    split at h
    · rename_i c hc
      obtain ⟨h1, h2, h3⟩ := aux_parse_hit dp st st' c parent hinv h
      exact ⟨h1, h2, fun hnil => absurd hnil h3⟩
    · -- a new node, then its two operands
      obtain ⟨st1, h1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨hi1, he1, hnode⟩ := OnlineReachSetAnalyzer.parseNew_spec dp _ _ _ _ hinv h1
      dsimp only at h
      obtain ⟨st2, h2, h3⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨hi2, he2, -⟩ := iha _ _ _ hi1 h2
      obtain ⟨hi3, he3, -⟩ := ihb _ _ _ hi2 h3
      exact aux_parse_chain dp st st1 st2 st' parent _ he1 hnode he2 he3 hi3
  | or a b iha ihb =>
    intro parent st st' hinv h
    rw [OnlineReachSetAnalyzer.parse] at h
    split at h
    · rename_i c hc
      obtain ⟨h1, h2, h3⟩ := aux_parse_hit dp st st' c parent hinv h
      exact ⟨h1, h2, fun hnil => absurd hnil h3⟩
    · -- a new node, then its two operands
      obtain ⟨st1, h1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨hi1, he1, hnode⟩ := OnlineReachSetAnalyzer.parseNew_spec dp _ _ _ _ hinv h1
      dsimp only at h
      obtain ⟨st2, h2, h3⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨hi2, he2, -⟩ := iha _ _ _ hi1 h2
      obtain ⟨hi3, he3, -⟩ := ihb _ _ _ hi2 h3
      exact aux_parse_chain dp st st1 st2 st' parent _ he1 hnode he2 he3 hi3
  | «until» I a b iha ihb =>
    intro parent st st' hinv h
    rw [OnlineReachSetAnalyzer.parse] at h
    split at h
    · rename_i c hc
      obtain ⟨h1, h2, h3⟩ := aux_parse_hit dp st st' c parent hinv h
      exact ⟨h1, h2, fun hnil => absurd hnil h3⟩
    · -- a new node, then its two operands
      obtain ⟨st1, h1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨hi1, he1, hnode⟩ := OnlineReachSetAnalyzer.parseNew_spec dp _ _ _ _ hinv h1
      dsimp only at h
      obtain ⟨st2, h2, h3⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨hi2, he2, -⟩ := iha _ _ _ hi1 h2
      obtain ⟨hi3, he3, -⟩ := ihb _ _ _ hi2 h3
      exact aux_parse_chain dp st st1 st2 st' parent _ he1 hnode he2 he3 hi3

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
