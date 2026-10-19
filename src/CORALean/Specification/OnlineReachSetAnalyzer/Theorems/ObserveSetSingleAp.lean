module

public import CORALean.Specification.OnlineAnalyzerNode.Theorems.ObserveSetApSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ObserveSet
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Propagate

@[expose] public section

/-!
# An analyzer of one atomic proposition observes a set

An analyzer with one node, an `AP` node that is the leaf and root, with propagation frequency
`1`, observing a set finally in a nonempty interval: the node takes the value of its proposition on
the set (`apValue`) in its satisfaction signal, and the propagation that follows changes nothing,
the node having no children.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.observeSet_single_ap (eps : ℝ) (obj : OnlineReachSetAnalyzer S d)
    (N : OnlineAnalyzerNode (AtomicProposition S d)) (hn : obj.nodes = [N]) (hl : obj.leaves = [1])
    (hf : obj.propagationFrequency = 1) (hc : obj.numObservations = 0) (hk : N.kind = .ap)
    (hp : N.prop = [STLInterval.empty]) (hch : N.children = []) (set : S d) (loc : ℕ)
    (I : STLInterval) (hne : I ≠ .empty) (val : Kleene) : -- --- CONCL ---
    ∀ tent ∈ N.tentative,
      ∀ a ∈ N.ap,
        OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a set loc = some val →
        ∃ obj1, OnlineReachSetAnalyzer.observeSet (𝕋 := 𝕋) eps obj set I loc none = some obj1 ∧
          obj1.nodes =
            [{ N with signal := N.signal.set I (FourValued.fromKleene val) }] := by -- --- PROOF ---
  intro tent (ht : N.tentative = some tent) a (hap : N.ap = some a) hval
  -- nothing was propagated to the node, so the observation conflicts with nothing
  have hnc : OnlineAnalyzerNode.conflicts eps I.infimum.value I.infimum.closed N.prop =
      some false := by
    cases I <;> simp [OnlineAnalyzerNode.conflicts, STLInterval.supremum, hp, STLInterval.infimum]
  have hobs := (OnlineAnalyzerNode.observeSet_ap_spec (𝕋 := 𝕋) eps N set I loc hk hnc val tent
    ht a hap hval).1.1
  cases I with
  | empty => exact absurd rfl hne
  | nonempty l u lc rc p1 p2 p3 =>
    -- the leaf observes, then the propagation visits the lone node and changes nothing
    unfold OnlineReachSetAnalyzer.observeSet
    simp only [hl, hn, List.foldlM_cons, List.foldlM_nil, OnlineReachSetAnalyzer.updateNode]
    simp [hc, hf]
    rw [hobs]
    simp only [Option.map_some, Option.bind_some]
    unfold OnlineReachSetAnalyzer.propagate
    simp [OnlineReachSetAnalyzer.propagateRec, OnlineAnalyzerNode.propagate, hk, hch, ht]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
