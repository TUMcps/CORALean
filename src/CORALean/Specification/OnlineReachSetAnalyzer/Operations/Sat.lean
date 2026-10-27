module

public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.Formula
public import CORALean.Specification.FourValuedSignal.Operations.And
public import CORALean.Specification.FourValuedSignal.Operations.Or
public import CORALean.Specification.FourValuedSignal.Operations.Until
public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# The four-valued satisfaction signal of a formula

`⟦φ⟧_R̃` of [1, Sec. 4.3 (satisfaction)] for the formulas the analyzer parses: `true` and `false`
are the constant signals, an atom `a` is the signal `sig a` given for it (`â(R̃(t))` where
observed, ⊣₂ elsewhere, `OnlineReachSetAnalyzer.observeAtoms`), and `¬`, `∧`, `∨`, `U_I` are the
operators of `U₂`-signals, binary as the parser builds them. As
`FourValuedSTL.Formula.fourValuedSat`, with `false` and `∨` besides; `none` where CORA's
`toBoolSignal()` throws, never for valid atoms.

Real-only, a specification: it denotes the satisfaction signal over real time.

## Inputs
* `sig` – signal of each atom

## Output
* the four-valued satisfaction signal of `φ`, or `none`

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


variable {A : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def OnlineReachSetAnalyzer.Formula.sat (sig : A → FourValuedSignal ℝ) :
    OnlineReachSetAnalyzer.Formula ℝ A → Option (FourValuedSignal ℝ)
  | .tt => some (FourValuedSignal.uniformSignal .tt)
  | .ff => some (FourValuedSignal.uniformSignal .ff)
  | .ap _ a => some (sig a)
  | .not φ => (φ.sat sig).map FourValuedSignal.not
  | .and φ ψ => (φ.sat sig).bind fun l => (ψ.sat sig).bind fun r => FourValuedSignal.and_ ![l, r]
  | .or φ ψ => (φ.sat sig).bind fun l => (ψ.sat sig).bind fun r => FourValuedSignal.or_ ![l, r]
  | .until I φ ψ => (φ.sat sig).bind fun l => (ψ.sat sig).bind fun r => l.until I r

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
