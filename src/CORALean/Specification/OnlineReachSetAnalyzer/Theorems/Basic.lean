module

public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.IsExt
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


-- ===========================  `OnlineReachSetAnalyzer.isSame_refl`  =========================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `IsSame` is reflexive. -/
theorem OnlineReachSetAnalyzer.isSame_refl (n : OnlineAnalyzerNode ℝ A) :
    OnlineReachSetAnalyzer.IsSame n n := ⟨rfl, rfl, rfl, rfl⟩


-- ==========================  `OnlineReachSetAnalyzer.isExt_append`  =========================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Appending a node extends the list. -/
theorem OnlineReachSetAnalyzer.isExt_append (nodes : List (OnlineAnalyzerNode ℝ A))
    (node : OnlineAnalyzerNode ℝ A) : OnlineReachSetAnalyzer.IsExt nodes (nodes ++ [node]) :=
  ⟨by simp, fun j h h' => by simp [List.getElem_append_left h, OnlineReachSetAnalyzer.isSame_refl]⟩


-- ===========================  `OnlineReachSetAnalyzer.isExt_refl`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `IsExt` is reflexive. -/
theorem OnlineReachSetAnalyzer.isExt_refl (nodes : List (OnlineAnalyzerNode ℝ A)) :
    OnlineReachSetAnalyzer.IsExt nodes nodes :=
  ⟨le_rfl, fun _ _ _ => OnlineReachSetAnalyzer.isSame_refl _⟩


-- ==========================  `OnlineReachSetAnalyzer.isSame_trans`  =========================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `IsSame` is transitive. -/
theorem OnlineReachSetAnalyzer.isSame_trans {n m k : OnlineAnalyzerNode ℝ A}
    (h1 : OnlineReachSetAnalyzer.IsSame n m) (h2 : OnlineReachSetAnalyzer.IsSame m k) :
    OnlineReachSetAnalyzer.IsSame n k :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.trans h2.2.2.2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
