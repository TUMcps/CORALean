module

public import CORALean.Specification.ReachSetAnalyzer.Operations.AnalyzeTimeInterval

@[expose] public section

/-!
# One reach set

`analyzeSingle(obj,R)`: analyze all time intervals of a single reachable set. CORA converts a
`zonoBundle` set to a zonotope first; that is a change of the representation `S`, which the entry
already has.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {n : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `analyzeSingle(obj,R)`. -/
noncomputable def ReachSetAnalyzer.analyzeSingle (obj : ReachSetAnalyzer S n)
    (R : ReachSetAnalyzer.Entry S n) : Option (ReachSetAnalyzer S n) :=
  -- for i = 1:length(R.timeInterval.time), with the set and the time interval of the i-th
  R.timeInterval.foldlM
    (fun obj t => obj.analyzeTimeInterval (𝕋 := 𝕋) t.set R.loc t.time.inf t.time.sup) obj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
