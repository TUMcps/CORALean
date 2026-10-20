module

public import CORALean.Specification.ReachSetAnalyzer.Definitions.Branch
public import CORALean.Specification.ReachSetAnalyzer.Operations.AnalyzeTree
public import CORALean.Specification.ReachSetAnalyzer.Theorems.MapMSpec

@[expose] public section

/-!
# Every result of `analyze` comes from a branch

Each element of `analyze(obj,R,i)` is the `signals` of the object after the entries of one branch
below `i` were analyzed, one after the other.

## Inputs
* `σ` – analyzer state type
* `α` – result type
* `children` – children of each entry
* `analyzeSingle` – analysis of one entry
* `signals` – result extracted from a state

## Hypotheses
* none

## Conclusion
* every result comes from analyzing one branch
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.analyzeTree_sound {σ α : Type} (children : ℕ → List ℕ)
    (analyzeSingle : σ → ℕ → Option σ) (signals : σ → Option α) : -- --- CONCL ---
    ∀ (fuel i : ℕ) (obj : σ) (outs : List α),
      ReachSetAnalyzer.analyzeTree children analyzeSingle signals fuel i obj = some outs →
      ∀ out ∈ outs, ∃ (w : List ℕ) (obj' : σ), ReachSetAnalyzer.Branch children i w ∧
        w.foldlM analyzeSingle obj = some obj' ∧ signals obj' = some out := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero => intro i obj outs h; simp [ReachSetAnalyzer.analyzeTree] at h
  | succ fuel ih =>
    intro i obj outs h out hout
    unfold ReachSetAnalyzer.analyzeTree at h
    -- the node's own entry, then its children
    obtain ⟨obj1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    have hself : (if i ≠ 0 then [i] else []).foldlM analyzeSingle obj = some obj1 := by
      by_cases hi : i ≠ 0 <;> simp_all
    by_cases hc : children i = []
    · -- a leaf: the signals of the object after the entry
      rw [if_pos hc] at h
      obtain ⟨s, hs, h⟩ := Option.map_eq_some_iff.mp h
      obtain rfl : outs = [s] := h.symm
      obtain rfl : out = s := by simpa using hout
      exact ⟨_, obj1, ReachSetAnalyzer.Branch.leaf i hc, hself, hs⟩
    · -- a node: the result of one of the children
      rw [if_neg hc] at h
      obtain ⟨L, hL, h⟩ := Option.map_eq_some_iff.mp h
      obtain rfl : outs = L.flatten := h.symm
      obtain ⟨r, hr, hor⟩ := List.mem_flatten.mp hout
      obtain ⟨j, hj, hfj⟩ := (mapM_option_spec _ _ _ hL).1 r hr
      obtain ⟨w, obj', hw, hf, hsig⟩ := ih j obj1 r hfj out hor
      refine ⟨(if i ≠ 0 then [i] else []) ++ w, obj', ReachSetAnalyzer.Branch.node i j w hj hw,
        ?_, hsig⟩
      rw [List.foldlM_append, hself]
      exact hf

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
