module

public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.Ext
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.GetVerdict

@[expose] public section

/-!
# `OnlineReachSetAnalyzer/Theorems`: small theorems

One section per theorem, at most five code lines each; alphabetical, after the sections each one
uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {d : ℕ} {A : Type}


-- =====================  `OnlineReachSetAnalyzer.getVerdict_eq_some_iff`  ====================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The verdict is the root's satisfaction signal at time `0`. -/
theorem OnlineReachSetAnalyzer.getVerdict_eq_some_iff (obj : OnlineReachSetAnalyzer ℝ S d)
    (v : FourValued) : obj.getVerdict = some v ↔ ∃ n, obj.nodes[0]? = some n ∧ n.signal.at 0 = v :=
  by simp [OnlineReachSetAnalyzer.getVerdict, Option.map_eq_some_iff]


-- ============================  `OnlineReachSetAnalyzer.same_refl`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Same` is reflexive. -/
theorem OnlineReachSetAnalyzer.same_refl (n : OnlineAnalyzerNode ℝ A) :
    OnlineReachSetAnalyzer.Same n n := ⟨rfl, rfl, rfl, rfl⟩


-- ===========================  `OnlineReachSetAnalyzer.ext_append`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Appending a node extends the list. -/
theorem OnlineReachSetAnalyzer.ext_append (nodes : List (OnlineAnalyzerNode ℝ A))
    (node : OnlineAnalyzerNode ℝ A) : OnlineReachSetAnalyzer.Ext nodes (nodes ++ [node]) :=
  ⟨by simp, fun j h h' => by simp [List.getElem_append_left h, OnlineReachSetAnalyzer.same_refl]⟩


-- ============================  `OnlineReachSetAnalyzer.ext_refl`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Ext` is reflexive. -/
theorem OnlineReachSetAnalyzer.ext_refl (nodes : List (OnlineAnalyzerNode ℝ A)) :
    OnlineReachSetAnalyzer.Ext nodes nodes :=
  ⟨le_rfl, fun _ _ _ => OnlineReachSetAnalyzer.same_refl _⟩


-- ===========================  `OnlineReachSetAnalyzer.same_trans`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Same` is transitive. -/
theorem OnlineReachSetAnalyzer.same_trans {n m k : OnlineAnalyzerNode ℝ A}
    (h1 : OnlineReachSetAnalyzer.Same n m) (h2 : OnlineReachSetAnalyzer.Same m k) :
    OnlineReachSetAnalyzer.Same n k :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.trans h2.2.2.2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
