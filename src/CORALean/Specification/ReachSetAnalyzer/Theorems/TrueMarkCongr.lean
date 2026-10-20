module

public import CORALean.Specification.ReachSetAnalyzer.Definitions.FalseMark
public import CORALean.Specification.ReachSetAnalyzer.Definitions.TrueMark

@[expose] public section

/-!
# The marks depend on the propositions and the masks only

`TrueMark` and `FalseMark` read the propositions and the masks of the analyzer, not its builders.

## Inputs
* `obj` – analyzer
* `obj0` – second analyzer

## Hypotheses
* `ha` – both have the same propositions
* `hm` – both have the same masks

## Conclusion
* both analyzers give the same true and false marks
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {n : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.marks_congr (obj obj0 : ReachSetAnalyzer S n)
    (ha : obj0.aps = obj.aps) (hm : obj0.masks = obj.masks) :
    obj0.TrueMark (𝕋 := 𝕋) = obj.TrueMark (𝕋 := 𝕋) ∧
      obj0.FalseMark (𝕋 := 𝕋) = obj.FalseMark (𝕋 := 𝕋) := by
  have hmask : obj0.maskOk = obj.maskOk := by
    funext k lo hi; simp [ReachSetAnalyzer.maskOk, hm]
  exact ⟨by funext k set loc lo hi d t; simp [ReachSetAnalyzer.TrueMark, ha, hmask],
    by funext k set loc lo hi d t; simp [ReachSetAnalyzer.FalseMark, ha, hmask]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
