module

public import CORALean.Specification.FourValuedSignal.Theorems.UniformSignalSpec
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Mk

@[expose] public section

/-!
# What the node constructor builds

`onlineAnalyzerNode(type,idx,parents,dropPropagated,varargin)` fails exactly when an `until` node
gets no interval or another node gets one. Otherwise the node has the given index, parents and
kind, no children, nothing propagated to any parent, and a valid signal that is `True` for a
`true` node, `False` for a `false` node and inconclusive at every time `t ≥ 0` for the others.

## Inputs
* `kind` – node kind
* `idx` – node index
* `parents` – parent indices
* `dp` – drop propagated times from the signal
* `interval` – interval of an until node
* `ap` – proposition of an atomic node

## Hypotheses
* none

## Conclusion
* fails iff the arguments do not fit, else a fresh node with the given fields
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineAnalyzerNode.mk?_spec (kind : OnlineAnalyzerNode.Kind) (idx : ℕ) (parents : List ℕ)
    (dp : Bool) (interval : Option (STLInterval ℝ)) (ap : Option A) : -- --- CONCL ---
    (OnlineAnalyzerNode.mk? kind idx parents dp interval ap = none ↔
      ¬ (decide (kind = .until) = interval.isSome ∧ decide (kind = .ap) = ap.isSome)) ∧
    ∀ n, OnlineAnalyzerNode.mk? kind idx parents dp interval ap = some n → n.kind = kind ∧
      n.idx = idx ∧ n.parents = parents ∧ n.children = [] ∧ n.dropPropagated = dp ∧
      n.interval = interval ∧ n.ap = ap ∧ n.prop = parents.map (fun _ => STLInterval.empty) ∧
      n.signal.IsValid ∧ ∀ t : ℝ, 0 ≤ t →
        n.signal.at t = kind.initValue := by -- --- PROOF ---
  unfold OnlineAnalyzerNode.mk?
  by_cases h : decide (kind = .until) = interval.isSome ∧ decide (kind = .ap) = ap.isSome
  · rw [if_pos h]
    refine ⟨by simp [h], fun n hn => ?_⟩
    obtain rfl := (Option.some.inj hn).symm
    -- the initial signal is a uniform signal
    obtain ⟨hv, hat⟩ := FourValuedSignal.uniformSignal_spec kind.initValue
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hv, hat⟩
  · rw [if_neg h]
    simp [h]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
