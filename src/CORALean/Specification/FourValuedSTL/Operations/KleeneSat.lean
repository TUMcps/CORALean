module

public import CORALean.Specification.FourValuedSTL.FourValuedSTL
public import CORALean.Specification.KleeneSignal.Operations.And
public import CORALean.Specification.KleeneSignal.Operations.Until
public import CORALean.Specification.KleeneSignal.Operations.Basic

@[expose] public section

/-!
# The three-valued satisfaction signal

`⟦φ⟧_R : ℝ≥0 → U₁` of [1, Sec. 4.2 (satisfaction)] over a reachable set `R`: `⟦true⟧_R(t) := ⊤`,
`⟦a⟧_R(t) := â(R(t))`, and `¬`, `∧`, `U_I` by the operators of `U₁`-signals (`KleeneSignal.not`,
`and_`, `until`). The signals `t ↦ â(R(t))` of the atoms are given (`S`); the operators are defined
for signals of finite variability, which `FourValuedSTL.IsAtomSignal` asks of them.

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

/-- `⟦φ⟧_R`, with `S a` the signal of the atom `a` over `R`. -/
noncomputable def FourValuedSTL.Formula.kleeneSat {X : Type}
    (S : (X → Prop) → KleeneSignal ℝ) : FourValuedSTL.Formula X → KleeneSignal ℝ
  | .tt => KleeneSignal.indicator STLInterval.empty .tt .tt
  | .atom a => S a
  | .not φ => (φ.kleeneSat S).not
  | .and φ ψ => KleeneSignal.and_ ![φ.kleeneSat S, ψ.kleeneSat S]
  | .until I _ φ ψ => (φ.kleeneSat S).until I (ψ.kleeneSat S)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
