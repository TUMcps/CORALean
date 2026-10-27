module

public import CORALean.Specification.STLInterval.Operations.Basic
public import Mathlib.Data.NNReal.Defs

@[expose] public section

/-!
# Signal temporal logic with the strict until

[1, Sec. 2.5]: `φ ::= true ∣ a ∣ ¬φ ∣ φ₁ ∧ φ₂ ∣ φ₁ U_I φ₂` over executions `ξ : ℝ≥0 → X`, with
`φ.Satisfies ξ t` for `⟦φ⟧_ξ(t) = ⊤`. The until is the strict one: `φ₁` need not hold at `t` or
`t'`, unlike the `U` of `STL.Formula` of Roehm et al. (`FourValuedSTL.Formula.sat_and_until_and`
recovers that one). `true` is syntax of its own, as excluded middle fails in the four-valued
semantics. Formulas are over states `X` with atoms `X → Prop`, as `STL.Formula`; `I` is any interval
over `ℝ≥0`, the paper's rational endpoints being unused.

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- The formulas of signal temporal logic with the strict until: true, atoms, negation, conjunction
and until over an interval. -/
inductive FourValuedSTL.Formula (X : Type)
  | tt
  | atom (a : X → Prop)
  | not (φ : Formula X)
  | and (φ ψ : Formula X)
  | until (I : STLInterval ℝ) (φ ψ : Formula X)

/-- `⟦φ⟧_ξ(t) = ⊤`, [1, Sec. 2.5]; `t' ∈ t ⊕ I` is `t' - t ∈ I`. -/
def FourValuedSTL.Formula.Satisfies : FourValuedSTL.Formula X → (ℝ≥0 → X) → ℝ≥0 → Prop
  | .tt, _, _ => True
  | .atom a, ξ, t => a (ξ t)
  | .not φ, ξ, t => ¬ φ.Satisfies ξ t
  | .and φ ψ, ξ, t => φ.Satisfies ξ t ∧ ψ.Satisfies ξ t
  | .until I φ ψ, ξ, t =>
      ∃ t' : ℝ≥0, (t' : ℝ) - t ∈ I.set ∧ ψ.Satisfies ξ t' ∧ ∀ t'' : ℝ≥0, t < t'' → t'' < t' →
          φ.Satisfies ξ t''

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
