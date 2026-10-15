module

public import CORALean.Specification.OnlineAnalyzerNode.Theorems.ApValueSpec
public import CORALean.Specification.FourValued.Theorems.Basic
public import CORALean.Specification.FourValuedSignal.Theorems.SetSpec
public import CORALean.Specification.FourValuedSignal.Theorems.UniformSignalSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.GetVerdict
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.MkSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ObserveSetSingleAp

@[expose] public section

/-!
# The verdict on an atomic proposition

The analyzer of the formula that is one atomic proposition `a`, after a final observation of a
set in an interval that contains `0`: the verdict is the value of `a` on the set (`apValue`), so
it is `True` only if every state of the set satisfies `a` and `False` only if none does.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An analyzer of one fresh `AP` node observing a set finally. -/
theorem aux_getVerdict_single_ap (eps : ℝ) (obj : OnlineReachSetAnalyzer S d)
    (N : OnlineAnalyzerNode (AtomicProposition S d)) (a : AtomicProposition S d)
    (hn : obj.nodes = [N]) (hl : obj.leaves = [1]) (hf : obj.propagationFrequency = 1)
    (hc : obj.numObservations = 0) (hk : N.kind = .ap) (hap : N.ap = some a)
    (ht : N.tentative = some TentativeKleeneSignal.emptySignal)
    (hp : N.prop = [STLInterval.empty]) (hch : N.children = [])
    (hsig : N.signal = OnlineAnalyzerNode.initSignal .ap) (set : S d) (loc : ℕ) (val : Kleene)
    (hval : OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a set loc = some val) (I : STLInterval)
    (hne : I ≠ .empty) (hI : ∀ f, I.fieldsOf = some f → 0 ≤ f.lower) (h0 : (0 : ℝ) ∈ I.set) :
    ∃ obj1, OnlineReachSetAnalyzer.observeSet (𝕋 := 𝕋) eps obj set I loc none = some obj1 ∧
      obj1.getVerdict = some (FourValued.fromKleene val) ∧
      (val = .tt → ∀ x ∈ construct set, a.Holds x loc) ∧
      (val = .ff → ∀ x ∈ construct set, ¬ a.Holds x loc) := by -- --- PROOF ---
  obtain ⟨obj1, hobs, hnodes⟩ := OnlineReachSetAnalyzer.observeSet_single_ap (𝕋 := 𝕋) eps obj N a
    TentativeKleeneSignal.emptySignal hn hl hf hc hk hap ht hp hch set loc I hne val hval
  -- its signal is `val` at `0`
  have hsv : N.signal.IsValid := by
    rw [hsig]
    exact (FourValuedSignal.uniformSignal_spec FourValued.ii).1
  obtain ⟨hv, hat⟩ := FourValuedSignal.set_spec _ hsv I hI (FourValued.fromKleene val)
  refine ⟨obj1, hobs, ?_, ?_, ?_⟩
  · simp [OnlineReachSetAnalyzer.getVerdict, hnodes, (hat 0 le_rfl).1 h0]
  · intro h
    exact (OnlineAnalyzerNode.apValue_spec (𝕋 := 𝕋) a set loc).1 (hval ▸ h ▸ rfl)
  · intro h
    exact (OnlineAnalyzerNode.apValue_spec (𝕋 := 𝕋) a set loc).2.1 (hval ▸ h ▸ rfl)


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.getVerdict_ap (label : String) (a : AtomicProposition S d)
    (dp : Bool) (obj0 : OnlineReachSetAnalyzer S d)
    (hmk : OnlineReachSetAnalyzer.mk? (OnlineReachSetAnalyzer.Formula.ap label a) 1 dp =
      some obj0) (eps : ℝ) (set : S d) (loc : ℕ) (val : Kleene)
    (hval : OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a set loc = some val) (I : STLInterval)
    (hne : I ≠ .empty) (hI : ∀ f, I.fieldsOf = some f → 0 ≤ f.lower) (h0 : (0 : ℝ) ∈ I.set) :
    ∃ obj1, OnlineReachSetAnalyzer.observeSet (𝕋 := 𝕋) eps obj0 set I loc none = some obj1 ∧
      obj1.getVerdict = some (FourValued.fromKleene val) ∧
      (val = .tt → ∀ x ∈ construct set, a.Holds x loc) ∧
      (val = .ff → ∀ x ∈ construct set, ¬ a.Holds x loc) := by -- --- PROOF ---
  -- the analyzer of an atom is one fresh `AP` node
  simp [OnlineReachSetAnalyzer.mk?, OnlineReachSetAnalyzer.parse,
    OnlineReachSetAnalyzer.parseNew, OnlineAnalyzerNode.mk?, OnlineReachSetAnalyzer.Formula.kind,
    OnlineReachSetAnalyzer.Formula.key, OnlineReachSetAnalyzer.Formula.interval?,
    OnlineReachSetAnalyzer.Formula.ap?] at hmk
  obtain ⟨-, rfl⟩ := hmk
  exact aux_getVerdict_single_ap (𝕋 := 𝕋) eps _ _ a rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl set loc
    val hval I hne hI h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
