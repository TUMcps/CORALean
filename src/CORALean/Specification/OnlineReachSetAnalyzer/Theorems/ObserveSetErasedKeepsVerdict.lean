module

public import CORALean.Specification.FourValuedSignal.Theorems.AtNot
public import CORALean.Specification.FourValuedSignal.Theorems.MergeSpec
public import CORALean.Specification.FourValuedSignal.Theorems.UniformSignalSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.GetVerdict
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ObserveSet
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Propagate

@[expose] public section

/-!
# An analyzer with less information can keep a verdict the exact one revises

The exact analyzer is not monotone in what its state knows. Two analyzers of `~p` have the root
`True` at every time. In the first the child `p` is `True`; in the second it is `Inconclusive`.
After one observation, which propagates, the first root is `False`: the negation of its child is
merged in. The second root stays `True`, since an inconclusive delta keeps the old value.

So "a `True` or `False` of the less informed state is that of the other" is not kept by
`observeSet`. A float analyzer is such a less informed state, where `untilFloat` rounds a time
shift. Its verdict is the exact one only if the exact run never revises a conclusive value.

## Inputs
* `eps` – machine epsilon
* `set` – observed set
* `I` – observed time interval
* `loc` – location

## Hypotheses
* `hne` – the interval is nonempty

## Conclusion
* the analyzer with the child inconclusive keeps `True`, the exact one turns `False`
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

/-- The root `~p`, `True` everywhere, over the child with index `2`. -/
private noncomputable def aux_root : OnlineAnalyzerNode ℝ (AtomicProposition S d) :=
  { kind := .not, signal := FourValuedSignal.uniformSignal .tt, prop := [],
    dropPropagated := false, idx := 1, parents := [], children := [2], interval := none,
    ap := none, tentative := none }


/-- The child `p` with signal `sig`, with nothing propagated to its parent yet. -/
private noncomputable def aux_child (sig : FourValuedSignal ℝ) :
    OnlineAnalyzerNode ℝ (AtomicProposition S d) :=
  { kind := .ap, signal := sig, prop := [STLInterval.empty], dropPropagated := false, idx := 2,
    parents := [1], children := [], interval := none, ap := none, tentative := none }


/-- The analyzer of `~p` with child signal `sig`, propagating at each observation. -/
private noncomputable def aux_obj (sig : FourValuedSignal ℝ) : OnlineReachSetAnalyzer ℝ S d :=
  { propagationFrequency := 1, nodes := [aux_root, aux_child sig], leaves := [],
    numObservations := 0, propagated := [false, false] }


omit [∀ k, ContSet (S k) (Vec ℝ k)] [∀ k, Contains (S k) (S k)] [∀ k, IsDisjoint (S k) (S k)] in
/-- Propagating an interval to a child with nothing propagated yet records it. -/
private theorem aux_setPropagated (eps : ℝ) (sig : FourValuedSignal ℝ)
    (J : STLInterval ℝ) : -- --- CONCL ---
    (aux_child (S := S) (d := d) sig).setPropagated eps 1 J =
      some { aux_child sig with prop := [J] } := by -- --- PROOF ---
  -- nothing propagated yet: the new interval is never smaller than the old
  have hJ : ¬ (¬ STLInterval.isequal eps (STLInterval.empty : STLInterval ℝ) J ∧
      STLInterval.contains_ eps (STLInterval.empty : STLInterval ℝ) J) := by
    rintro ⟨h1, h2⟩
    cases J
    · exact h1 trivial
    · exact absurd h2 (by simp [STLInterval.contains_])
  simp [OnlineAnalyzerNode.setPropagated, aux_child, hJ]


omit [∀ k, ContSet (S k) (Vec ℝ k)] [∀ k, Contains (S k) (S k)] [∀ k, IsDisjoint (S k) (S k)] in
/-- The child, a leaf with no tentative observation, propagates without change. -/
private theorem aux_propagate_child (eps : ℝ) (sig : FourValuedSignal ℝ) :
    (aux_child (S := S) (d := d) sig).propagate eps [] .empty = some (aux_child sig, []) := by
  simp [OnlineAnalyzerNode.propagate, aux_child]


omit [∀ k, ContSet (S k) (Vec ℝ k)] [∀ k, Contains (S k) (S k)] [∀ k, IsDisjoint (S k) (S k)] in
/-- The root merges the negated child and records the interval it passes on in the child. -/
private theorem aux_propagate_root (eps : ℝ) (sig : FourValuedSignal ℝ) : -- --- CONCL ---
    ∃ J, (aux_root (S := S) (d := d)).propagate eps [aux_child sig] .empty =
      some ({ aux_root (S := S) (d := d) with
          signal := (aux_root (S := S) (d := d)).signal.merge sig.not },
        [{ aux_child (S := S) (d := d) sig with prop := [J] }]) := by -- --- PROOF ---
  -- the interval the root passes on, as `propagate` computes it
  refine ⟨(((aux_root (S := S) (d := d)).signal.merge sig.not).conclusiveInterval
    (OnlineAnalyzerNode.getAllProp eps { aux_root (S := S) (d := d) with
      signal := (aux_root (S := S) (d := d)).signal.merge sig.not })), ?_⟩
  simp only [OnlineAnalyzerNode.propagate, aux_root, OnlineAnalyzerNode.combine, Option.bind_some,
    List.mapM_cons, List.mapM_nil, aux_setPropagated]
  rfl


/-- The verdict after one propagating observation: the root merged with the negated child at `0`. -/
private theorem aux_verdict (eps : ℝ) (sig : FourValuedSignal ℝ) (set : S d) (I : STLInterval ℝ)
    (hne : I ≠ .empty) (loc : ℕ) : -- --- CONCL ---
    ((aux_obj sig).observeSet (𝕋 := 𝕋) eps set I loc).bind OnlineReachSetAnalyzer.getVerdict =
      some (((FourValuedSignal.uniformSignal .tt).merge sig.not).at 0) := by -- --- PROOF ---
  cases I with
  | empty => exact absurd rfl hne
  | nonempty l u lc rc p2 p3 p4 =>
    -- no leaves to observe; one observation is a multiple of the frequency `1`, so it propagates
    simp only [OnlineReachSetAnalyzer.observeSet, aux_obj, List.foldlM_nil, Option.pure_def,
      Option.bind_some, Nat.zero_add, Nat.mod_self, if_true, OnlineReachSetAnalyzer.propagate,
      List.length_cons, List.length_nil, List.replicate]
    simp only [OnlineReachSetAnalyzer.propagateRec]
    -- the child first, unchanged, then the root over it
    obtain ⟨J, hJ⟩ := aux_propagate_root (S := S) (d := d) eps sig
    simp only [List.eraseDups_cons, List.eraseDups_nil, List.filter_cons,
      List.filter_nil, List.mergeSort_singleton, List.mergeSort_nil, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Nat.sub_self, Nat.add_one_sub_one, Option.bind_some,
      List.foldlM_cons, List.foldlM_nil, List.mapM_nil, List.mapM_cons, Option.some.injEq,
      Bool.false_eq_true, decide_false, decide_not, Bool.not_false, ↓reduceIte, List.set_cons_zero,
      List.set_cons_succ, List.zip_cons_cons, List.zip_nil_left, List.zip_nil_right,
      List.foldl_cons, List.foldl_nil, Option.map_some, Option.getD_none, Option.pure_def,
      Option.bind_eq_bind, show (aux_root (S := S) (d := d)).children = [2] from rfl,
      show (aux_child (S := S) (d := d) sig).children = [] from rfl, aux_propagate_child, hJ,
      OnlineReachSetAnalyzer.getVerdict]
    rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.observeSet_erased_keeps_verdict (eps : ℝ) (set : S d)
    (I : STLInterval ℝ) (hne : I ≠ .empty) (loc : ℕ) : -- --- CONCL ---
    ∃ (root c : OnlineAnalyzerNode ℝ (AtomicProposition S d)) (obj : OnlineReachSetAnalyzer ℝ S d),
      obj.nodes = [root, c] ∧ c.signal = FourValuedSignal.uniformSignal .tt ∧
      obj.getVerdict = some .tt ∧
      (obj.observeSet (𝕋 := 𝕋) eps set I loc).bind getVerdict = some .ff ∧
      ({ obj with nodes := [root, { c with signal := FourValuedSignal.uniformSignal .ii }] } :
          OnlineReachSetAnalyzer ℝ S d).getVerdict = some .tt ∧
      (({ obj with nodes := [root, { c with signal := FourValuedSignal.uniformSignal .ii }] } :
          OnlineReachSetAnalyzer ℝ S d).observeSet (𝕋 := 𝕋) eps set I loc).bind getVerdict =
        some .tt := by -- --- PROOF ---
  obtain ⟨vt, at_t⟩ := FourValuedSignal.uniformSignal_spec .tt
  obtain ⟨vi, at_i⟩ := FourValuedSignal.uniformSignal_spec .ii
  refine ⟨aux_root, aux_child (FourValuedSignal.uniformSignal .tt),
    aux_obj (FourValuedSignal.uniformSignal .tt),
    rfl, rfl, ?_, ?_, ?_, ?_⟩
  · -- the root is `True` before the observation
    simp [OnlineReachSetAnalyzer.getVerdict, aux_obj, aux_root, at_t 0 le_rfl]
  · -- the exact child `True`: the delta `False` is merged in
    rw [aux_verdict eps _ set I hne loc]
    have hn := FourValuedSignal.at_not _ vt 0
    rw [at_t 0 le_rfl] at hn
    rw [((FourValuedSignal.merge_spec _ _ vt (FourValuedSignal.not_isValid _ vt)).2 0 le_rfl).1
      (by rw [hn]; decide), hn]
    rfl
  · -- erasing the child leaves the root `True`
    simp [OnlineReachSetAnalyzer.getVerdict, aux_root, at_t 0 le_rfl]
  · -- the erased child: the delta is inconclusive, so the root keeps `True`
    have := aux_verdict (𝕋 := 𝕋) eps (FourValuedSignal.uniformSignal .ii) set I hne loc
    rw [show ({ aux_obj (FourValuedSignal.uniformSignal .tt) with
        nodes := [aux_root, { aux_child (FourValuedSignal.uniformSignal .tt) with
          signal := FourValuedSignal.uniformSignal .ii }] } : OnlineReachSetAnalyzer ℝ S d) =
        aux_obj (FourValuedSignal.uniformSignal .ii) from rfl, this]
    have hn := FourValuedSignal.at_not _ vi 0
    rw [at_i 0 le_rfl] at hn
    rw [((FourValuedSignal.merge_spec _ _ vt (FourValuedSignal.not_isValid _ vi)).2 0 le_rfl).2
      (by rw [hn]; rfl), at_t 0 le_rfl]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
