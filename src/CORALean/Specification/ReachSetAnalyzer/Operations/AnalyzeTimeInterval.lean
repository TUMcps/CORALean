module

public import CORALean.Specification.ReachSetAnalyzer.Operations.AnalyzeKey

@[expose] public section

/-!
# One set in one time interval

`analyzeTimeInterval(obj,set,loc,int)`: iterate through all properties.
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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `analyzeTimeInterval(obj,set,loc,int)` with `int = interval(lo,hi)`: every proposition is
analyzed in turn (`analyzeKey`), the later ones on the builders the earlier ones left. `none` if
any of them throws. -/
noncomputable def ReachSetAnalyzer.analyzeTimeInterval (obj : ReachSetAnalyzer S n) (set : S n)
    (loc : ℕ) (lo hi : ℝ) : Option (ReachSetAnalyzer S n) :=
  -- iterate through all properties
  obj.aps.foldlM (fun obj p => obj.analyzeKey (𝕋 := 𝕋) set loc lo hi p) obj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
