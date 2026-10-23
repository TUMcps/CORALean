module

public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# The formula an online analyzer is made from

An `stl` formula as `onlineReachSetAnalyzer` parses it, after `desugar` (which leaves only `true`,
`false`, atoms, `~`, `&`, `|` and `until`, rewriting `finally`, `globally`, `release` and `next`):
an atom is an atomic proposition `a` named `label`, which stands both for a `variable` that holds an
`atomicProposition` and for a comparison, turned into one by `convert2set`. CORA keys its cache of
subformulas by their display text `formattedDisplayText(phi)`; here that is the formula with the
propositions erased to their labels (`Formula.key`), two atoms with one name being one node. The
time interval of an `until` is the `stlInterval` of CORA, over the time scalar `𝕋`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- An STL formula as the online analyzer parses it, after desugaring: true, false, labeled atoms,
negation, conjunction, disjunction and until. -/
inductive OnlineReachSetAnalyzer.Formula (𝕋 : Type) [Float.FloatOps 𝕋]
    [Float.SoundFloatArithmetic 𝕋] (A : Type)
  | tt
  | ff
  | ap (label : String) (a : A)
  | not (φ : Formula 𝕋 A)
  | and (φ ψ : Formula 𝕋 A)
  | or (φ ψ : Formula 𝕋 A)
  | until (I : STLInterval 𝕋) (φ ψ : Formula 𝕋 A)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
