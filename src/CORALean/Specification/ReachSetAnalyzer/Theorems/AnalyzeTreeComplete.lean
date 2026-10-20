module

public import CORALean.Specification.ReachSetAnalyzer.Definitions.Branch
public import CORALean.Specification.ReachSetAnalyzer.Operations.AnalyzeTree
public import CORALean.Specification.ReachSetAnalyzer.Theorems.MapMSpec

@[expose] public section

/-!
# Every branch is analyzed

If `analyze(obj,R,i)` succeeds, every branch below `i` contributes a result: the `signals` of the
object after the entries of the branch were analyzed, one after the other.

## Inputs
* `σ` – analyzer state type
* `α` – result type
* `children` – children of each entry
* `analyzeSingle` – analysis of one entry
* `signals` – result extracted from a state

## Hypotheses
* none

## Conclusion
* every branch contributes a result
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.analyzeTree_complete {σ α : Type} (children : ℕ → List ℕ)
    (analyzeSingle : σ → ℕ → Option σ) (signals : σ → Option α) : -- --- CONCL ---
    ∀ (fuel i : ℕ) (obj : σ) (outs : List α),
      ReachSetAnalyzer.analyzeTree children analyzeSingle signals fuel i obj = some outs →
      ∀ w, ReachSetAnalyzer.Branch children i w → ∃ out ∈ outs, ∃ obj' : σ,
        w.foldlM analyzeSingle obj = some obj' ∧ signals obj' = some out := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero => intro i obj outs h; simp [ReachSetAnalyzer.analyzeTree] at h
  | succ fuel ih =>
    intro i obj outs h w hw
    unfold ReachSetAnalyzer.analyzeTree at h
    -- the node's own entry, then its children
    obtain ⟨obj1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    have hself : (if i ≠ 0 then [i] else []).foldlM analyzeSingle obj = some obj1 := by
      by_cases hi : i ≠ 0 <;> simp_all
    cases hw with
    | leaf _ hc =>
      rw [if_pos hc] at h
      obtain ⟨s, hs, h⟩ := Option.map_eq_some_iff.mp h
      obtain rfl : outs = [s] := h.symm
      exact ⟨s, List.mem_singleton_self s, obj1, hself, hs⟩
    | node _ j w' hj hw' =>
      rw [if_neg (List.ne_nil_of_mem hj)] at h
      obtain ⟨L, hL, h⟩ := Option.map_eq_some_iff.mp h
      obtain rfl : outs = L.flatten := h.symm
      obtain ⟨r, hr, hfj⟩ := (mapM_option_spec _ _ _ hL).2 j hj
      obtain ⟨out, hout, obj', hf, hsig⟩ := ih j obj1 r hfj w' hw'
      refine ⟨out, List.mem_flatten.mpr ⟨r, hr, hout⟩, obj', ?_, hsig⟩
      rw [List.foldlM_append, hself]
      exact hf

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
