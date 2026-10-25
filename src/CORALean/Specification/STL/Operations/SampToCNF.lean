module

public import CORALean.Specification.STL.Operations.CNFOr
public import CORALean.Specification.STL.Operations.CNFNext
public import CORALean.Specification.STL.Operations.SampToFormula

@[expose] public section

/-!
# Sampled time formulas to normal form

[1, Sec. 4.1]: every sampled time formula has an equivalent one in conjunctive normal form `⋀ᵢ ⋁ⱼ
X_c^j (φᵢⱼ ∨ ϱᵢⱼ)`, here computed: `X_c` raises each `j`, `∧` appends, `∨` distributes, and a
negation is pushed in by `¬X_cϕ ≡ X_c¬ϕ`, `¬F(0,c)ϱ ≡ G(0,c)¬ϱ`, `¬G(0,c)ϱ ≡ F(0,c)¬ϱ`. `toCNF
true s` is `s`, `toCNF false s` is `¬s`.

## Inputs
* none

## Output
* the normal form of the sampled time formula or of its negation

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and Hybrid
      Systems". Automated Technology for Verification and Analysis, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The normal form of `s` (`pos`) or of `¬s`. -/
def STL.Samp.toCNF : Bool → STL.Samp X → STL.CNF X
  | pos, .lit ϱ => [[{ j := 0, ϱ := if pos then ϱ else .not ϱ, K := [], L := [] }]]
  | pos, .not s => s.toCNF !pos
  | true, .and s t => s.toCNF true ++ t.toCNF true
  | false, .and s t => (s.toCNF false).or (t.toCNF false)
  | true, .or s t => (s.toCNF true).or (t.toCNF true)
  | false, .or s t => s.toCNF false ++ t.toCNF false
  | pos, .next s => (s.toCNF pos).next
  | true, .fin ϱ => [[{ j := 0, ϱ := Pform.bot, K := [ϱ], L := [] }]]
  | false, .fin ϱ => [[{ j := 0, ϱ := Pform.bot, K := [], L := [.not ϱ] }]]
  | true, .glob ϱ => [[{ j := 0, ϱ := Pform.bot, K := [], L := [ϱ] }]]
  | false, .glob ϱ => [[{ j := 0, ϱ := Pform.bot, K := [.not ϱ], L := [] }]]


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
