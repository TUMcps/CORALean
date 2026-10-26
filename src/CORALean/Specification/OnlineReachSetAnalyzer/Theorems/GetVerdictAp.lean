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

## Inputs
* `label` – proposition label
* `a` – atomic proposition
* `dp` – drop propagated times flag
* `eps` – machine epsilon
* `set` – observed set
* `loc` – location
* `I` – observed time interval

## Hypotheses
* `hne` – the interval is nonempty
* `h0` – the interval contains time zero

## Conclusion
* the verdict is the value of the proposition on the set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An analyzer of one fresh `AP` node observing a set finally. -/
private theorem aux_getVerdict_single_ap (eps : ℝ) (obj : OnlineReachSetAnalyzer ℝ S d)
    (N : OnlineAnalyzerNode ℝ (AtomicProposition S d)) (a : AtomicProposition S d)
    (hn : obj.nodes = [N]) (hl : obj.leaves = [1]) (hf : obj.propagationFrequency = 1)
    (hc : obj.numObservations = 0) (hk : N.kind = .ap) (hap : N.ap = some a)
    (ht : N.tentative = some TentativeKleeneSignal.emptySignal)
    (hp : N.prop = [STLInterval.empty]) (hch : N.children = [])
    (hsig : N.signal = OnlineAnalyzerNode.initSignal .ap) (set : S d) (loc : ℕ) (val : Kleene)
    (hval : OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a set loc = some val) (I : STLInterval ℝ)
    (hne : I ≠ .empty) (h0 : (0 : ℝ) ∈ I.set) : -- --- CONCL ---
    ∃ obj1, OnlineReachSetAnalyzer.observeSet (𝕋 := 𝕋) eps obj set I loc none = some obj1 ∧
      obj1.getVerdict = some (FourValued.fromKleene val) ∧
      (val = .tt → ∀ x ∈ construct set, a.Holds x loc) ∧
      (val = .ff → ∀ x ∈ construct set, ¬ a.Holds x loc) := by -- --- PROOF ---
  obtain ⟨obj1, hobs, hnodes⟩ := OnlineReachSetAnalyzer.observeSet_single_ap (𝕋 := 𝕋) eps obj N hn
    hl hf hc hk hp hch set loc I hne val TentativeKleeneSignal.emptySignal ht a hap hval
  -- its signal is `val` at `0`
  have hsv : N.signal.IsValid := by
    rw [hsig]
    exact (FourValuedSignal.uniformSignal_spec FourValued.ii).1
  obtain ⟨hv, hat⟩ := FourValuedSignal.set_spec _ hsv I (FourValued.fromKleene val)
  refine ⟨obj1, hobs, ?_, ?_, ?_⟩
  · simp [OnlineReachSetAnalyzer.getVerdict, hnodes, (hat 0 le_rfl).1 h0]
  · intro h
    exact (OnlineAnalyzerNode.apValue_spec (𝕋 := 𝕋) a set loc).1 (hval ▸ h ▸ rfl)
  · intro h
    exact (OnlineAnalyzerNode.apValue_spec (𝕋 := 𝕋) a set loc).2.1 (hval ▸ h ▸ rfl)


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.getVerdict_ap (label : String) (a : AtomicProposition S d)
    (dp : Bool) (eps : ℝ) (set : S d) (loc : ℕ) (I : STLInterval ℝ) (hne : I ≠ .empty)
    (h0 : (0 : ℝ) ∈ I.set) : -- --- CONCL ---
    ∀ val ∈ OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a set loc,
      ∀ obj0 ∈ OnlineReachSetAnalyzer.mk? (OnlineReachSetAnalyzer.Formula.ap label a) 1 dp,
        ∃ obj1, OnlineReachSetAnalyzer.observeSet (𝕋 := 𝕋) eps obj0 set I loc none = some obj1 ∧
          obj1.getVerdict = some (FourValued.fromKleene val) ∧
          (val = .tt → ∀ x ∈ construct set, a.Holds x loc) ∧
          (val = .ff → ∀ x ∈ construct set, ¬ a.Holds x loc) := by -- --- PROOF ---
  intro val (hval : OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a set loc = some val) obj0 (hmk :
      OnlineReachSetAnalyzer.mk? (OnlineReachSetAnalyzer.Formula.ap label a) 1 dp = some obj0)
  -- the analyzer of an atom is one fresh `AP` node
  simp [OnlineReachSetAnalyzer.mk?, OnlineReachSetAnalyzer.parse,
    OnlineReachSetAnalyzer.parseNew, OnlineAnalyzerNode.mk?, OnlineReachSetAnalyzer.Formula.kind,
    OnlineReachSetAnalyzer.Formula.key, OnlineReachSetAnalyzer.Formula.interval?,
    OnlineReachSetAnalyzer.Formula.ap?] at hmk
  obtain ⟨-, rfl⟩ := hmk
  exact aux_getVerdict_single_ap (𝕋 := 𝕋) eps _ _ a rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl set loc
    val hval I hne h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
