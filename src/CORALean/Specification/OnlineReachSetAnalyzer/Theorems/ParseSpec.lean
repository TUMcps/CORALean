module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Parse
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.Basic
public import CORALean.Specification.OnlineAnalyzerNode.Theorems.MkSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ParseNew
public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.IsExt
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.UpdateNodeSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.NodesInv

@[expose] public section

/-!
# What parsing keeps

Parsing a subformula keeps the invariant of the nodes (node `j` has index `j + 1`, every node has
the right `dropPropagated` and a first parent) and only extends them: the old nodes stay, up to
the edges added to them, and new ones are appended.

## Inputs
* `dp` – drop propagated times flag

## Hypotheses
* none

## Conclusion
* parsing keeps the invariant and only extends the nodes
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {d : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {A : Type}

/-- The invariant survives a change of edges. -/
private theorem OnlineReachSetAnalyzer.aux_nodesInv_of_ext (dp : Bool)
    (nodes nodes' : List (OnlineAnalyzerNode ℝ A)) (hl : nodes'.length = nodes.length)
    (he : OnlineReachSetAnalyzer.IsExt nodes nodes')
    (h : OnlineReachSetAnalyzer.NodesInv dp nodes) : -- --- CONCL ---
    OnlineReachSetAnalyzer.NodesInv dp nodes' := by -- --- PROOF ---
  refine ⟨fun j hj => ?_, fun n hn => ?_⟩
  -- the index of a node is unchanged
  · rw [← (he.2 j (by omega) hj).1]
    exact h.1 j (by omega)
  -- and so is the rest
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hn
    have hs := he.2 j (by omega) hj
    obtain ⟨hd, hp⟩ := h.2 nodes[j] (List.getElem_mem _)
    refine ⟨hs.2.2.2.symm.trans hd, ?_⟩
    rw [← hs.2.2.1]
    exact hp

end


section
variable {A : Type}

/-- Updating a node keeps the list. -/
private theorem OnlineReachSetAnalyzer.aux_ext_updateNode (nodes : List (OnlineAnalyzerNode ℝ A))
    (i : ℕ) (f : OnlineAnalyzerNode ℝ A → Option (OnlineAnalyzerNode ℝ A))
    (hf : ∀ n ∈ nodes, ∀ n', f n = some n' → OnlineReachSetAnalyzer.IsSame n n') : -- --- CONCL ---
    ∀ nodes' ∈ OnlineReachSetAnalyzer.updateNode nodes i f,
      OnlineReachSetAnalyzer.IsExt nodes nodes' ∧ nodes'.length =
      nodes.length := by -- --- PROOF ---
  intro nodes' (h : OnlineReachSetAnalyzer.updateNode nodes i f = some nodes')
  obtain ⟨-, n, n', hn, hfn, rfl⟩ := (OnlineReachSetAnalyzer.updateNode_eq_some_iff _ _ _ _).mp h
  refine ⟨⟨by simp, fun j hj hj' => ?_⟩, by simp⟩
  -- the updated position is `IsSame`, every other one is equal
  rw [List.getElem_set]
  by_cases hji : i - 1 = j
  · rw [if_pos hji]
    have : nodes[j] = n := by subst hji; exact (List.getElem?_eq_some_iff.mp hn).2
    rw [this]
    exact hf n (List.mem_of_getElem? hn) n' hfn
  · rw [if_neg hji]
    exact OnlineReachSetAnalyzer.same_refl _

end


section
variable {A : Type}

/-- `IsExt` is transitive. -/
private theorem OnlineReachSetAnalyzer.aux_ext_trans {a b c : List (OnlineAnalyzerNode ℝ A)}
    (h1 : OnlineReachSetAnalyzer.IsExt a b) (h2 : OnlineReachSetAnalyzer.IsExt b c) :
    OnlineReachSetAnalyzer.IsExt a c :=
  ⟨h1.1.trans h2.1, fun j h h' => OnlineReachSetAnalyzer.same_trans
    (h1.2 j h (lt_of_lt_of_le h h1.1)) (h2.2 j (lt_of_lt_of_le h h1.1) h')⟩

end


section
variable {A : Type}

/-- The invariant survives a new node. -/
private theorem OnlineReachSetAnalyzer.aux_nodesInv_append (dp : Bool)
    (nodes : List (OnlineAnalyzerNode ℝ A)) (node : OnlineAnalyzerNode ℝ A)
    (h : OnlineReachSetAnalyzer.NodesInv dp nodes)
    (hidx : node.idx = nodes.length + 1) (hd : node.dropPropagated = dp)
    (hp : node.parents.head?.isSome = true) : -- --- CONCL ---
    OnlineReachSetAnalyzer.NodesInv dp (nodes ++ [node]) := by -- --- PROOF ---
  refine ⟨fun j hj => ?_, fun n hn => ?_⟩
  -- the positions of the old nodes and of the new one
  · by_cases hjl : j < nodes.length
    · rw [List.getElem_append_left hjl]
      exact h.1 j hjl
    · have : j = nodes.length := by simp at hj; omega
      subst this
      simpa [List.getElem_append_right] using hidx
  -- every node, old or new
  · rcases List.mem_append.mp hn with hn | hn
    · exact h.2 n hn
    · obtain rfl : n = node := by simpa using hn
      exact ⟨hd, hp⟩

end


/-- What a new subformula adds. -/
private theorem OnlineReachSetAnalyzer.aux_parseNew_spec (dp : Bool)
    (φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) (parent : ℕ)
    (st : OnlineReachSetAnalyzer.ParseState ℝ S d)
    (hinv : OnlineReachSetAnalyzer.NodesInv dp st.nodes) : -- --- CONCL ---
    ∀ st' ∈ OnlineReachSetAnalyzer.parseNew dp φ parent st,
      OnlineReachSetAnalyzer.NodesInv dp st'.nodes ∧
        OnlineReachSetAnalyzer.IsExt st.nodes st'.nodes ∧
        ∃ node, st'.nodes[st.nodes.length]? = some node ∧ node.kind = φ.kind ∧
          node.parents = [parent] := by -- --- PROOF ---
  intro st' (h : OnlineReachSetAnalyzer.parseNew dp φ parent st = some st')
  unfold OnlineReachSetAnalyzer.parseNew at h
  obtain ⟨nodes1, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨node, hnode, rfl⟩ := Option.map_eq_some_iff.mp h
  -- the parent gets a child: same nodes, up to edges
  have hext : OnlineReachSetAnalyzer.IsExt st.nodes nodes1 ∧ nodes1.length = st.nodes.length := by
    by_cases hp : parent ≠ 0
    · rw [if_pos hp] at h1
      exact OnlineReachSetAnalyzer.aux_ext_updateNode _ _ _ (fun n _ n' hn' =>
        by obtain rfl := Option.some.inj hn'; exact ⟨rfl, rfl, rfl, rfl⟩) _ h1
    · rw [if_neg hp] at h1
      obtain rfl := Option.some.inj h1
      exact ⟨OnlineReachSetAnalyzer.ext_refl _, rfl⟩
  have hinv1 := OnlineReachSetAnalyzer.aux_nodesInv_of_ext dp _ _ hext.2 hext.1 hinv
  -- the node made by the constructor
  obtain ⟨-, hmk⟩ := OnlineAnalyzerNode.mk?_spec φ.kind (st.nodes.length + 1) [parent] dp
    φ.interval? φ.ap?
  obtain ⟨hk, hidx, hpar, -, hdp, -⟩ := hmk node hnode
  refine ⟨?_, OnlineReachSetAnalyzer.aux_ext_trans hext.1 (OnlineReachSetAnalyzer.ext_append _
    node),
    node, ?_, hk, hpar⟩
  · refine OnlineReachSetAnalyzer.aux_nodesInv_append dp nodes1 node hinv1 (by rw [hidx, hext.2])
      hdp (by simp [hpar])
  · simp [hext.2]


/-- The branch of a subformula that already has a node: two edges are added. -/
private theorem aux_parse_hit (dp : Bool) (st st' : OnlineReachSetAnalyzer.ParseState ℝ S d)
    (c parent : ℕ) (hinv : OnlineReachSetAnalyzer.NodesInv dp st.nodes)
    (h : ((OnlineReachSetAnalyzer.updateNode st.nodes c
        (fun n => some (n.addParent parent))).bind fun nodes =>
          (OnlineReachSetAnalyzer.updateNode nodes parent (fun n => some (n.addChild c))).map
            fun nodes => ({ st with nodes := nodes } : OnlineReachSetAnalyzer.ParseState ℝ S d)) =
      some st') : -- --- CONCL ---
    OnlineReachSetAnalyzer.NodesInv dp st'.nodes ∧ OnlineReachSetAnalyzer.IsExt st.nodes st'.nodes ∧
      st.nodes ≠ [] := by -- --- PROOF ---
  obtain ⟨nodes1, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨nodes2, h2, rfl⟩ := Option.map_eq_some_iff.mp h
  -- a parent is added: the first one stays
  obtain ⟨e1, l1⟩ := OnlineReachSetAnalyzer.aux_ext_updateNode _ _ _ (fun n hn n' hn' => by
    obtain rfl := Option.some.inj hn'
    obtain ⟨-, hp⟩ := hinv.2 n hn
    exact ⟨rfl, rfl, by
      cases hps : n.parents <;> simp_all [OnlineAnalyzerNode.addParent], rfl⟩) _ h1
  have hinv1 := OnlineReachSetAnalyzer.aux_nodesInv_of_ext dp _ _ l1 e1 hinv
  -- a child is added
  obtain ⟨e2, l2⟩ := OnlineReachSetAnalyzer.aux_ext_updateNode _ _ _ (fun n hn n' hn' => by
    obtain rfl := Option.some.inj hn'
    exact ⟨rfl, rfl, rfl, rfl⟩) _ h2
  refine ⟨OnlineReachSetAnalyzer.aux_nodesInv_of_ext dp _ _ l2 e2 hinv1,
    OnlineReachSetAnalyzer.aux_ext_trans e1 e2, ?_⟩
  -- the node that was updated is in the list
  obtain ⟨-, n, n', hn, -⟩ := (OnlineReachSetAnalyzer.updateNode_eq_some_iff _ _ _ _).mp h1
  intro hnil
  simp [hnil] at hn


/-- The first node made is the root: it keeps its type and its first parent. -/
private theorem aux_parse_root (st st1 st' : OnlineReachSetAnalyzer.ParseState ℝ S d) (parent : ℕ)
    (k : OnlineAnalyzerNode.Kind)
    (hnode : ∃ node, st1.nodes[st.nodes.length]? = some node ∧ node.kind = k ∧
      node.parents = [parent]) (hnil : st.nodes = [])
    (hext : OnlineReachSetAnalyzer.IsExt st1.nodes st'.nodes) : -- --- CONCL ---
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
private theorem aux_parse_leaf (dp : Bool) (st st1 : OnlineReachSetAnalyzer.ParseState ℝ S d)
    (parent : ℕ) (k : OnlineAnalyzerNode.Kind) (hi1 : OnlineReachSetAnalyzer.NodesInv dp st1.nodes)
    (he1 : OnlineReachSetAnalyzer.IsExt st.nodes st1.nodes)
    (hnode : ∃ node, st1.nodes[st.nodes.length]? = some node ∧ node.kind = k ∧
      node.parents = [parent]) :
    OnlineReachSetAnalyzer.NodesInv dp st1.nodes ∧ OnlineReachSetAnalyzer.IsExt st.nodes st1.nodes ∧
      (st.nodes = [] → ∃ root, st1.nodes[0]? = some root ∧ root.kind = k ∧
        root.parents.head? = some parent) :=
  ⟨hi1, he1, fun hnil =>
    aux_parse_root st st1 st1 parent k hnode hnil (OnlineReachSetAnalyzer.ext_refl _)⟩


/-- The conclusion once the node and its two operands are parsed. -/
private theorem aux_parse_chain (dp : Bool)
    (st st1 st2 st' : OnlineReachSetAnalyzer.ParseState ℝ S d)
    (parent : ℕ) (k : OnlineAnalyzerNode.Kind)
    (he1 : OnlineReachSetAnalyzer.IsExt st.nodes st1.nodes)
    (hnode : ∃ node, st1.nodes[st.nodes.length]? = some node ∧ node.kind = k ∧
      node.parents = [parent])
    (he2 : OnlineReachSetAnalyzer.IsExt st1.nodes st2.nodes)
    (he3 : OnlineReachSetAnalyzer.IsExt st2.nodes st'.nodes)
    (hi3 : OnlineReachSetAnalyzer.NodesInv dp st'.nodes) :
    OnlineReachSetAnalyzer.NodesInv dp st'.nodes ∧ OnlineReachSetAnalyzer.IsExt st.nodes st'.nodes ∧
      (st.nodes = [] → ∃ root, st'.nodes[0]? = some root ∧ root.kind = k ∧
        root.parents.head? = some parent) :=
  ⟨hi3, OnlineReachSetAnalyzer.aux_ext_trans he1 (OnlineReachSetAnalyzer.aux_ext_trans he2 he3),
    fun hnil => aux_parse_root st st1 st' parent k hnode hnil
      (OnlineReachSetAnalyzer.aux_ext_trans he2 he3)⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.parse_spec (dp : Bool) : -- --- CONCL ---
    ∀ (φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d)) (parent : ℕ)
      (st st' : OnlineReachSetAnalyzer.ParseState ℝ S d),
      OnlineReachSetAnalyzer.NodesInv dp st.nodes →
      OnlineReachSetAnalyzer.parse dp φ parent st = some st' →
      OnlineReachSetAnalyzer.NodesInv dp st'.nodes ∧
        OnlineReachSetAnalyzer.IsExt st.nodes st'.nodes ∧
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
      obtain ⟨hi1, he1, hnode⟩ := OnlineReachSetAnalyzer.aux_parseNew_spec dp _ _ _ hinv _ h1
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
      obtain ⟨hi1, he1, hnode⟩ := OnlineReachSetAnalyzer.aux_parseNew_spec dp _ _ _ hinv _ h1
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
      obtain ⟨hi1, he1, hnode⟩ := OnlineReachSetAnalyzer.aux_parseNew_spec dp _ _ _ hinv _ h1
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
      obtain ⟨hi1, he1, hnode⟩ := OnlineReachSetAnalyzer.aux_parseNew_spec dp _ _ _ hinv _ h1
      dsimp only at h
      obtain ⟨hi2, he2, -⟩ := ih _ _ _ hi1 h
      exact ⟨hi2, OnlineReachSetAnalyzer.aux_ext_trans he1 he2, fun hnil =>
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
      obtain ⟨hi1, he1, hnode⟩ := OnlineReachSetAnalyzer.aux_parseNew_spec dp _ _ _ hinv _ h1
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
      obtain ⟨hi1, he1, hnode⟩ := OnlineReachSetAnalyzer.aux_parseNew_spec dp _ _ _ hinv _ h1
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
      obtain ⟨hi1, he1, hnode⟩ := OnlineReachSetAnalyzer.aux_parseNew_spec dp _ _ _ hinv _ h1
      dsimp only at h
      obtain ⟨st2, h2, h3⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨hi2, he2, -⟩ := iha _ _ _ hi1 h2
      obtain ⟨hi3, he3, -⟩ := ihb _ _ _ hi2 h3
      exact aux_parse_chain dp st st1 st2 st' parent _ he1 hnode he2 he3 hi3

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
