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
time interval of an `until` is the `stlInterval` of CORA.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

inductive OnlineReachSetAnalyzer.Formula (A : Type)
  | tt
  | ff
  | ap (label : String) (a : A)
  | not (φ : Formula A)
  | and (φ ψ : Formula A)
  | or (φ ψ : Formula A)
  | until (I : STLInterval) (φ ψ : Formula A)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
