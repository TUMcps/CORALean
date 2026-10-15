module

public import CORALean.Specification.FourValuedSTL.FourValuedSTL
public import CORALean.Specification.FourValuedSignal.Operations.And
public import CORALean.Specification.FourValuedSignal.Operations.Until
public import CORALean.Specification.FourValuedSignal.Operations.Basic

@[expose] public section

/-!
# The four-valued satisfaction signal

`⟦φ⟧_R̃ : ℝ≥0 → U₂` of [1, Sec. 4.3 (satisfaction)] over a partial reachable set `R̃ : T → 2^X`:
`⟦true⟧_R̃(t) := ⊤`, `⟦a⟧_R̃(t) := â(R̃(t))` for `t ∈ T` and ⊣₂ otherwise, and `¬`, `∧`, `U_I` by
the operators of `U₂`-signals (`FourValuedSignal.not`, `and_`, `until`). `and_` and `until` return
`none` where CORA's `toBoolSignal()` throws, which `FourValuedSignal.at_and` and `until_spec` show
does not happen for valid signals.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⟦φ⟧_R̃`, with `S a` the signal of the atom `a` over `R̃`; `none` where CORA throws. -/
noncomputable def FourValuedSTL.Formula.fourValuedSat {X : Type}
    (S : (X → Prop) → FourValuedSignal ℝ) : FourValuedSTL.Formula X → Option (FourValuedSignal ℝ)
  | .tt => some (FourValuedSignal.uniformSignal .tt)
  | .atom a => some (S a)
  | .not φ => (φ.fourValuedSat S).map FourValuedSignal.not
  | .and φ ψ => (φ.fourValuedSat S).bind fun l => (ψ.fourValuedSat S).bind fun r =>
      FourValuedSignal.and_ ![l, r]
  | .until I φ ψ => (φ.fourValuedSat S).bind fun l => (ψ.fourValuedSat S).bind fun r =>
      FourValuedSignal.until l I r

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
