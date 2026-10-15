module

public import CORALean.Specification.STLInterval.Operations.Basic
public import Mathlib.Data.NNReal.Defs

@[expose] public section

/-!
# Signal temporal logic with the strict until

[1, Sec. 2.5]: `φ ::= true ∣ a ∣ ¬φ ∣ φ₁ ∧ φ₂ ∣ φ₁ U_I φ₂` over executions `ξ : ℝ≥0 → X`, and the
Boolean satisfaction signal `⟦φ⟧_ξ : ℝ≥0 → B`, here `φ.Sat ξ t` for `⟦φ⟧_ξ(t) = ⊤` (and `⊥`
otherwise). The until is the strict one of [1, Sec. 2.5]: `φ₁` need not hold at `t` or at `t'`,
only strictly between; it is not the `U` of `STL.Formula`, which is that of Roehm et al., and the
two are different operators (`FourValuedSTL.Formula.sat_and_until_and` recovers the until that
holds `φ₁` at `t` and `t'` too). `true` is syntax of its own, since the law of excluded middle does
not transfer to the four-valued semantics.

A formula is over a type `X` of states with atoms predicates `X → Prop`, as `STL.Formula`, and
`I` is any interval over `ℝ≥0` (its lower bound `≥ 0`): the paper asks for rational endpoints,
which nothing here uses.

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

variable {X : Type}


-- ========================================  MAIN TYPE  ========================================= --

inductive FourValuedSTL.Formula (X : Type)
  | tt
  | atom (a : X → Prop)
  | not (φ : Formula X)
  | and (φ ψ : Formula X)
  | until (I : STLInterval) (hI : ∀ f, I.fieldsOf = some f → 0 ≤ f.lower) (φ ψ : Formula X)

/-- `⟦φ⟧_ξ(t) = ⊤`, [1, Sec. 2.5]; `t' ∈ t ⊕ I` is `t' - t ∈ I`. -/
def FourValuedSTL.Formula.Sat : FourValuedSTL.Formula X → (ℝ≥0 → X) → ℝ≥0 → Prop
  | .tt, _, _ => True
  | .atom a, ξ, t => a (ξ t)
  | .not φ, ξ, t => ¬ φ.Sat ξ t
  | .and φ ψ, ξ, t => φ.Sat ξ t ∧ ψ.Sat ξ t
  | .until I _ φ ψ, ξ, t =>
      ∃ t' : ℝ≥0, (t' : ℝ) - t ∈ I.set ∧ ψ.Sat ξ t' ∧ ∀ t'' : ℝ≥0, t < t'' → t'' < t' → φ.Sat ξ t''

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
