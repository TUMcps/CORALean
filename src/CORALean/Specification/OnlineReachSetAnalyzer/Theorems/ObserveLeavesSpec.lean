module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.ObserveSet
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.UpdateNodeSpec
public import CORALean.Specification.FourValuedSignal.Theorems.SetSpec

@[expose] public section

/-!
# Observing a set at the leaves

The first half of `observeSet` at `eps = 0`, without a propagation: every leaf in `L` observes
`set` on `I` in turn [1, Alg. 1, lines 5-8]. An `AP` node among them holds the value of its
proposition on the set on `I` and its old value elsewhere; every other node is unchanged.

## Inputs
* `nodes` – nodes of the analyzer
* `set` – observed set
* `I` – observed time interval
* `loc` – location
* `L` – the leaves, by index

## Hypotheses
* `hv` – every node's signal is valid

## Conclusion
* the nodes after the leaves observed the set, if no leaf throws, as described

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


variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A node's `observeSet` at `eps = 0`: `true` and `false` stay, an `AP` node sets its value on
`I`. -/
private theorem aux_observe_node (n n' : OnlineAnalyzerNode ℝ (AtomicProposition S d)) (set : S d)
    (I : STLInterval ℝ) (loc : ℕ)
    (h : OnlineAnalyzerNode.observeSet (𝕋 := 𝕋) 0 n set I loc false = some n') : -- --- CONCL ---
    ((n.kind = .true ∨ n.kind = .false) ∧ n' = n) ∨
      (n.kind = .ap ∧ ∃ a val, n.ap = some a ∧
        OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a set loc = some val ∧
        n' = { n with signal := n.signal.set I (FourValued.fromKleene val) }) := by -- --- PROOF ---
  unfold OnlineAnalyzerNode.observeSet at h
  by_cases h1 : n.kind ≠ .true ∧ n.kind ≠ .false ∧ n.kind ≠ .ap
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  -- a leaf: by its kind, the inner kinds refused
  obtain ⟨bad, -, h⟩ := Option.bind_eq_some_iff.1 h
  cases bad
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases hk : n.kind <;> rw [hk] at h
    · cases h; exact Or.inl ⟨Or.inl rfl, rfl⟩
    · cases h; exact Or.inl ⟨Or.inr rfl, rfl⟩
    · obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨val, hval, h⟩ := Option.bind_eq_some_iff.1 h
      try simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact Or.inr ⟨rfl, a, val, ha, hval, (Option.some.inj h).symm⟩
    all_goals cases h
  · simp at h

open Classical in
/-- After observing the leaves `P`: each observed `AP` node holds the new value on `I`, every other
node is unchanged. -/
private def aux_Observed (nodes : List (OnlineAnalyzerNode ℝ (AtomicProposition S d))) (set : S d)
    (I : STLInterval ℝ) (loc : ℕ) (P : List ℕ)
    (cur : List (OnlineAnalyzerNode ℝ (AtomicProposition S d))) : Prop :=
  cur.length = nodes.length ∧ ∀ j (h : j < nodes.length), ∃ h' : j < cur.length,
    (¬ (nodes[j].kind = .ap ∧ j + 1 ∈ P) → cur[j] = nodes[j]) ∧
    (nodes[j].kind = .ap ∧ j + 1 ∈ P → ∃ a val, nodes[j].ap = some a ∧
      OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a set loc = some val ∧
      cur[j] = { nodes[j] with signal := cur[j].signal } ∧ cur[j].signal.IsValid ∧
      ∀ t : ℝ, 0 ≤ t → cur[j].signal.at t =
        if t ∈ I.set then FourValued.fromKleene val else nodes[j].signal.at t)

/-- Observing the leaves `L` one by one extends the observed list by `L`. -/
private theorem aux_observe_leaves (nodes : List (OnlineAnalyzerNode ℝ (AtomicProposition S d)))
    (set : S d) (I : STLInterval ℝ) (loc : ℕ)
    (hv : ∀ j (h : j < nodes.length), nodes[j].signal.IsValid) :
    ∀ (L P : List ℕ) (cur res : List (OnlineAnalyzerNode ℝ (AtomicProposition S d))),
      aux_Observed (𝕋 := 𝕋) nodes set I loc P cur →
      L.foldlM (fun ns l => OnlineReachSetAnalyzer.updateNode ns l fun n =>
        OnlineAnalyzerNode.observeSet (𝕋 := 𝕋) 0 n set I loc false) cur = some res →
      aux_Observed (𝕋 := 𝕋) nodes set I loc (P ++ L) res
  | [], P, cur, res, hq, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simpa using hq
  | l :: L, P, cur, res, hq, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨cur', hcur', h⟩ := Option.bind_eq_some_iff.1 h
    have := aux_observe_leaves nodes set I loc hv L (P ++ [l]) cur' res ?_ h
    · simpa using this
    -- the head leaf `l` updates position `l - 1` only
    obtain ⟨hl0, x, x', hx, hx', rfl⟩ :=
      (OnlineReachSetAnalyzer.updateNode_eq_some_iff cur l _ cur').1 hcur'
    obtain ⟨hlen, hq⟩ := hq
    have hl : l - 1 < cur.length := (List.getElem?_eq_some_iff.1 hx).1
    have hxc : cur[l - 1] = x := (List.getElem?_eq_some_iff.1 hx).2
    refine ⟨by simp [hlen], fun j hj => ?_⟩
    obtain ⟨h', q1, q2⟩ := hq j hj
    refine ⟨by simpa using h', ?_⟩
    by_cases hjl : j = l - 1
    · subst hjl
      simp only [List.getElem_set_self]
      rw [← hxc] at hx'
      rcases aux_observe_node (𝕋 := 𝕋) _ _ set I loc hx' with ⟨hk, rfl⟩ |
          ⟨hk, a, val, ha, hval, rfl⟩
      · -- `true` or `false`: unchanged
        have hk' : nodes[l - 1].kind ≠ .ap := by
          by_cases hp : nodes[l - 1].kind = .ap ∧ l - 1 + 1 ∈ P
          · obtain ⟨a, val, -, -, e, -⟩ := q2 hp; rw [e] at hk
            rcases hk with hk | hk <;> rw [hk] at hp <;> exact absurd hp.1 (by decide)
          · rw [q1 hp] at hk; rcases hk with hk | hk <;> rw [hk] <;> nofun
        exact ⟨fun _ => by
          by_cases hp : nodes[l - 1].kind = .ap ∧ l - 1 + 1 ∈ P
          · exact absurd hp.1 hk'
          · exact q1 hp, fun hp => absurd hp.1 hk'⟩
      · -- an `AP` node: the value on `I`
        have hkn : nodes[l - 1].kind = .ap := by
          by_cases hp : nodes[l - 1].kind = .ap ∧ l - 1 + 1 ∈ P
          · exact hp.1
          · rw [q1 hp] at hk; exact hk
        have hold : ∃ s, cur[l - 1] = { nodes[l - 1] with signal := s } ∧ s.IsValid ∧
            ∀ t : ℝ, 0 ≤ t → t ∉ I.set → s.at t = nodes[l - 1].signal.at t := by
          by_cases hp : nodes[l - 1].kind = .ap ∧ l - 1 + 1 ∈ P
          · obtain ⟨a', val', -, -, e, ev, et⟩ := q2 hp
            exact ⟨_, e, ev, fun t ht hI => by rw [et t ht, if_neg hI]⟩
          · exact ⟨nodes[l - 1].signal, q1 hp, hv _ hj, fun _ _ _ => rfl⟩
        -- its new signal is the old one set to the value on `I`
        obtain ⟨s0, hs0, hs0v, hs0t⟩ := hold
        have hap : nodes[l - 1].ap = some a := by rw [hs0] at ha; exact ha
        obtain ⟨hsv, hst⟩ := FourValuedSignal.set_spec s0 hs0v I (FourValued.fromKleene val)
        refine ⟨fun hp => absurd ⟨hkn, by
          simp only [List.mem_append, List.mem_singleton]; right; omega⟩ hp, fun _ =>
              ⟨a, val, hap, hval, ?_, ?_, ?_⟩⟩
        · rw [hs0]
        · rw [hs0]; exact hsv
        · intro t ht
          rw [hs0]
          split_ifs with hI
          · exact (hst t ht).1 hI
          · rw [(hst t ht).2 hI]; exact hs0t t ht hI
    · -- another position is untouched
      rw [List.getElem_set_ne (by omega)]
      have hmem : j + 1 ∈ P ++ [l] ↔ j + 1 ∈ P := by
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (h | h)
          · exact h
          · omega
        · exact Or.inl
      rw [hmem]
      exact ⟨q1, q2⟩


-- =======================================  MAIN THEOREM  ======================================= --

open Classical in
theorem OnlineReachSetAnalyzer.observeLeaves_spec
    (nodes : List (OnlineAnalyzerNode ℝ (AtomicProposition S d))) (set : S d) (I : STLInterval ℝ)
    (loc : ℕ) (hv : ∀ j (h : j < nodes.length), nodes[j].signal.IsValid)
    (L : List ℕ) : -- --- CONCL ---
    ∀ res ∈ L.foldlM (fun ns l => OnlineReachSetAnalyzer.updateNode ns l fun n =>
        OnlineAnalyzerNode.observeSet (𝕋 := 𝕋) 0 n set I loc false) nodes,
      res.length = nodes.length ∧ ∀ j (h : j < nodes.length), ∃ h' : j < res.length,
        (¬ (nodes[j].kind = .ap ∧ j + 1 ∈ L) → res[j] = nodes[j]) ∧
        (nodes[j].kind = .ap ∧ j + 1 ∈ L → ∃ a val, nodes[j].ap = some a ∧
          OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a set loc = some val ∧
          res[j] = { nodes[j] with signal := res[j].signal } ∧ res[j].signal.IsValid ∧
          ∀ t : ℝ, 0 ≤ t → res[j].signal.at t =
            if t ∈ I.set then FourValued.fromKleene val else nodes[j].signal.at t)
    := by -- --- PROOF ---
  intro res h
  have := aux_observe_leaves (𝕋 := 𝕋) nodes set I loc hv L [] nodes res
    ⟨rfl, fun j h => ⟨h, fun _ => rfl, fun hp => by simp at hp⟩⟩ h
  simp only [List.nil_append] at this
  exact this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
