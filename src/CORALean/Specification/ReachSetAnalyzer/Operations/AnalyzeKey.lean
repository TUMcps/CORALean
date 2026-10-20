module

public import CORALean.Specification.AtomicProposition.Operations.CanBeFalse
public import CORALean.Specification.AtomicProposition.Operations.CanBeTrue
public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.SetPossiblyFalse
public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.SetPossiblyTrue
public import CORALean.Specification.ReachSetAnalyzer.Operations.Basic
public import CORALean.Global.ReplaceKey
public import CORALean.Specification.ReachSetAnalyzer.Operations.MaskOk

@[expose] public section

/-!
# One proposition over one set

The body of the loop of `analyzeTimeInterval`, for the proposition `k{i}`: unless a mask says the
proposition does not matter on the time interval `[lo,hi]`, its builder records the interval as one
where the proposition can be true (if `canBeTrue` of the set) and one where it can be false (if
`canBeFalse`). The mask is `max(mask,int)`, true if the mask is true anywhere in the interval.
CORA throws if the builder rejects the interval (a degenerate one) or a key has no builder; here
`none`.

## Inputs
* `obj` – analyzer
* `set` – reachable set
* `loc` – location
* `lo` – interval lower bound
* `hi` – interval upper bound
* `p` – proposition with its key

## Output
* the analyzer after marking the proposition, or none
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

/-- The loop body of `analyzeTimeInterval` for the proposition `p = (k{i}, ap)`. -/
noncomputable def ReachSetAnalyzer.analyzeKey (obj : ReachSetAnalyzer S n) (set : S n) (loc : ℕ)
    (lo hi : ℝ) (p : String × AtomicProposition S n) : Option (ReachSetAnalyzer S n) :=
  -- get objects from map
  (obj.sigBuilder.lookup p.1).bind fun builder =>
    -- check mask
    if obj.maskOk p.1 lo hi = true then
      -- can set be inside of atomic proposition?
      (if p.2.canBeTrue (𝕋 := 𝕋) set loc then builder.setPossiblyTrue? lo hi else some builder).bind
        fun builder =>
          -- can set be outside of atomic proposition?
          (if p.2.canBeFalse (𝕋 := 𝕋) set loc then builder.setPossiblyFalse? lo hi
            else some builder).map fun builder =>
              { obj with sigBuilder := replaceKey obj.sigBuilder p.1 builder }
    else some obj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
