module

public import CORALean.Specification.FourValuedSignal.Theorems.UniformSignalSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.GetVerdict
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.MkSpec

@[expose] public section

/-!
# The verdict on `true` and `false`

The analyzer of the formula `true` has the verdict `True` and that of `false` the verdict `False`,
before anything is observed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.getVerdict_const (f : ℕ) (dp : Bool)
    (obj obj' : OnlineReachSetAnalyzer S d)
    (htt : OnlineReachSetAnalyzer.mk?
      (OnlineReachSetAnalyzer.Formula.tt : OnlineReachSetAnalyzer.Formula (AtomicProposition S d))
      f dp = some obj)
    (hff : OnlineReachSetAnalyzer.mk?
      (OnlineReachSetAnalyzer.Formula.ff : OnlineReachSetAnalyzer.Formula (AtomicProposition S d))
      f dp = some obj') : -- --- STMT ---
    obj.getVerdict = some FourValued.tt ∧
      obj'.getVerdict = some FourValued.ff := by -- --- PROOF ---
  -- each analyzer is one node, with a uniform signal
  simp [OnlineReachSetAnalyzer.mk?, OnlineReachSetAnalyzer.parse, OnlineReachSetAnalyzer.parseNew,
    OnlineAnalyzerNode.mk?, OnlineReachSetAnalyzer.Formula.kind, OnlineReachSetAnalyzer.Formula.key,
    OnlineReachSetAnalyzer.Formula.interval?, OnlineReachSetAnalyzer.Formula.ap?] at htt hff
  subst htt hff
  refine ⟨?_, ?_⟩ <;> simp [OnlineReachSetAnalyzer.getVerdict, OnlineAnalyzerNode.initSignal,
    OnlineAnalyzerNode.Kind.initValue]
  · exact (FourValuedSignal.uniformSignal_spec FourValued.tt).2 0 le_rfl
  · exact (FourValuedSignal.uniformSignal_spec FourValued.ff).2 0 le_rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
