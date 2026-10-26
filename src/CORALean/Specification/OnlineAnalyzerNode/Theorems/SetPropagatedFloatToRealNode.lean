module

public import CORALean.Specification.FourValuedSignal.Theorems.SetMapTime
public import CORALean.Specification.OnlineAnalyzerNode.Operations.SetPropagated
public import CORALean.Specification.OnlineAnalyzerNode.Operations.SetPropagatedFloat
public import CORALean.Specification.OnlineAnalyzerNode.Operations.ToRealNode
public import CORALean.Specification.OnlineAnalyzerNode.Theorems.GetAllPropFloatToRealInterval
public import CORALean.Specification.STLInterval.Theorems.ContainsFloatIff
public import CORALean.Specification.STLInterval.Theorems.IsequalFloatIff

@[expose] public section

/-!
# `setPropagatedFloat` read as reals is `setPropagated`

Over a float scalar `setPropagatedFloat` decides `isequal` and `contains_` exactly
(`isequalFloat_iff`, `containsFloat_iff`) and drops `getAllPropFloat`, which read as reals is
`getAllProp`, so the node it returns, read as reals, is the one `setPropagated` returns for the
node and the interval read as reals, and both throw together.

## Inputs
* `eps` – machine epsilon
* `n` – node
* `parent` – parent index
* `int` – propagated interval

## Hypotheses
* none

## Conclusion
* the float node read as reals is the exact one
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {A : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [ExactLe 𝕋] in
/-- `isequal` of two intervals read as reals is `isequal` of the float ones. -/
private theorem STLInterval.aux_isequal_toRealInterval (tol : ℝ) (I J : STLInterval 𝕋) :
    STLInterval.isequal tol I.toRealInterval J.toRealInterval ↔ STLInterval.isequal tol I J := by
  rcases I with _ | ⟨l₁, _ | u₁, lc₁, rc₁, _, _, _⟩ <;>
    rcases J with _ | ⟨l₂, _ | u₂, lc₂, rc₂, _, _, _⟩ <;> exact Iff.rfl


omit [ExactLe 𝕋] in
/-- `contains_` of two intervals read as reals is `contains_` of the float ones. -/
private theorem STLInterval.aux_contains_toRealInterval (tol : ℝ) (I J : STLInterval 𝕋) :
    STLInterval.contains_ tol I.toRealInterval J.toRealInterval ↔
      STLInterval.contains_ tol I J := by
  rcases I with _ | ⟨l₁, _ | u₁, lc₁, rc₁, _, _, _⟩ <;>
    rcases J with _ | ⟨l₂, _ | u₂, lc₂, rc₂, _, _, _⟩ <;>
    simp [STLInterval.contains_, STLInterval.toRealInterval]


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineAnalyzerNode.setPropagatedFloat_toRealNode (eps : 𝕋) (n : OnlineAnalyzerNode 𝕋 A)
    (parent : ℕ) (int : STLInterval 𝕋) : -- --- CONCL ---
    (n.setPropagatedFloat eps parent int).map OnlineAnalyzerNode.toRealNode =
      n.toRealNode.setPropagated (toReal eps) parent int.toRealInterval := by -- --- PROOF ---
  unfold OnlineAnalyzerNode.setPropagatedFloat OnlineAnalyzerNode.setPropagated
  have hprop : n.toRealNode.prop = n.prop.map STLInterval.toRealInterval := rfl
  have hpar : n.toRealNode.parents = n.parents := rfl
  simp only [hprop, hpar, List.getElem?_map]
  rcases n.prop[n.parents.idxOf parent]? with _ | old
  · rfl
  · -- the throw is decided alike
    simp only [Option.map_some]
    open Classical in
    by_cases hc : (!STLInterval.isequalFloat eps old int &&
        STLInterval.containsFloat eps old int) = true
    · -- a throw: the new interval is smaller than the old one, on both sides
      have hc' : ¬ STLInterval.isequal (toReal eps) old.toRealInterval int.toRealInterval ∧
          STLInterval.contains_ (toReal eps) old.toRealInterval int.toRealInterval := by
        simp only [Bool.and_eq_true, Bool.not_eq_true', STLInterval.containsFloat_iff] at hc
        refine ⟨fun h => ?_, (STLInterval.aux_contains_toRealInterval _ _ _).2 hc.2⟩
        rw [STLInterval.aux_isequal_toRealInterval, ← STLInterval.isequalFloat_iff] at h
        rw [h] at hc
        exact Bool.noConfusion hc.1
      rw [if_pos hc, if_pos hc']
      rfl
    · -- no throw on either side
      have hc' : ¬ (¬ STLInterval.isequal (toReal eps) old.toRealInterval int.toRealInterval ∧
          STLInterval.contains_ (toReal eps) old.toRealInterval int.toRealInterval) := by
        rintro ⟨h1, h2⟩
        apply hc
        simp only [Bool.and_eq_true, Bool.not_eq_true', STLInterval.containsFloat_iff,
          ← STLInterval.aux_contains_toRealInterval (toReal eps) old int]
        refine ⟨?_, h2⟩
        cases h : STLInterval.isequalFloat eps old int
        · rfl
        · exact absurd ((STLInterval.aux_isequal_toRealInterval _ _ _).2
            ((STLInterval.isequalFloat_iff _ _ _).1 h)) h1
      rw [if_neg hc, if_neg hc']
      -- the interval is recorded, and the propagated times dropped alike
      have key := OnlineAnalyzerNode.getAllPropFloat_toRealInterval eps
        ({ n with prop := n.prop.set (n.parents.idxOf parent) int } : OnlineAnalyzerNode 𝕋 A)
      simp only [OnlineAnalyzerNode.toRealNode, List.map_set] at key
      by_cases hdp : n.dropPropagated = true
      · simp only [OnlineAnalyzerNode.toRealNode, hdp, List.map_set, FourValuedSignal.set_mapTime,
          if_true, Option.map_some, Option.some.injEq, OnlineAnalyzerNode.mk.injEq, and_true,
          true_and]
        exact congrArg (FourValuedSignal.set _ · _) (by simpa [hdp] using key)
      · simp [OnlineAnalyzerNode.toRealNode, hdp, List.map_set]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
