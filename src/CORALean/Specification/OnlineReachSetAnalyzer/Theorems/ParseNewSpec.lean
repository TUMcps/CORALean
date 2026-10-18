module

public import CORALean.Specification.OnlineAnalyzerNode.Theorems.MkSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ParseNew
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ExtTrans
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ExtUpdateNode
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.NodesInvAppend
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.NodesInvOfExt

@[expose] public section

/-!
# What a new subformula adds

Creating the node of a new subformula keeps the invariant of the nodes and extends them; the
new node is the next one: it is the node at the old length, of the subformula's type, with the
`parent` as its only parent.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.parseNew_spec (dp : Bool)
    (φ : OnlineReachSetAnalyzer.Formula (AtomicProposition S d)) (parent : ℕ)
    (st : OnlineReachSetAnalyzer.ParseState S d)
    (hinv : OnlineReachSetAnalyzer.NodesInv dp st.nodes) : -- --- STMT ---
    ∀ st' ∈ OnlineReachSetAnalyzer.parseNew dp φ parent st,
      OnlineReachSetAnalyzer.NodesInv dp st'.nodes ∧
        OnlineReachSetAnalyzer.Ext st.nodes st'.nodes ∧
        ∃ node, st'.nodes[st.nodes.length]? = some node ∧ node.kind = φ.kind ∧
          node.parents = [parent] := by -- --- PROOF ---
  intro st' (h : OnlineReachSetAnalyzer.parseNew dp φ parent st = some st')
  unfold OnlineReachSetAnalyzer.parseNew at h
  obtain ⟨nodes1, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨node, hnode, rfl⟩ := Option.map_eq_some_iff.mp h
  -- the parent gets a child: same nodes, up to edges
  have hext : OnlineReachSetAnalyzer.Ext st.nodes nodes1 ∧ nodes1.length = st.nodes.length := by
    by_cases hp : parent ≠ 0
    · rw [if_pos hp] at h1
      exact OnlineReachSetAnalyzer.ext_updateNode _ _ _ (fun n _ n' hn' =>
        by obtain rfl := Option.some.inj hn'; exact ⟨rfl, rfl, rfl, rfl⟩) _ h1
    · rw [if_neg hp] at h1
      obtain rfl := Option.some.inj h1
      exact ⟨OnlineReachSetAnalyzer.ext_refl _, rfl⟩
  have hinv1 := OnlineReachSetAnalyzer.nodesInv_of_ext dp _ _ hext.2 hext.1 hinv
  -- the node made by the constructor
  obtain ⟨-, hmk⟩ := OnlineAnalyzerNode.mk?_spec φ.kind (st.nodes.length + 1) [parent] dp
    φ.interval? φ.ap?
  obtain ⟨hk, hidx, hpar, -, hdp, -⟩ := hmk node hnode
  refine ⟨?_, OnlineReachSetAnalyzer.ext_trans hext.1 (OnlineReachSetAnalyzer.ext_append _ node),
    node, ?_, hk, hpar⟩
  · refine OnlineReachSetAnalyzer.nodesInv_append dp nodes1 node hinv1 (by rw [hidx, hext.2]) hdp
      (by simp [hpar])
  · simp [hext.2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
