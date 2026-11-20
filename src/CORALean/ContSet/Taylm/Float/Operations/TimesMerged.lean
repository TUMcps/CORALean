module

public import CORALean.ContSet.Taylm.Float.Operations.AccumTerms
public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Operations.PolyBoundsMono

@[expose] public section

/-!
# `Taylm.timesMerged`

The product of two Taylor models over the same variables as CORA.cpp's `Taylm::times`
computes it, `(p + r)(q + s) = pq + p s + q r + r s`: the cross terms `p s`, `q r`, `r s` by
interval products of the polynomial bounds (`Taylm.polyBoundsMono`) and the remainders, then the
products of the terms pair by pair (the first model's terms outside): those of degree at most
`N` merged into the result (`Taylm.accumTerms`), the others bounded into the remainder. The
order `N` is a parameter: CORA.cpp passes the first model's, CORA the larger of the two. The
error boxes go into the remainders first; the roundings of the kept products and of their sums
go to the error box.

## Inputs
* `N` – order the product is truncated at
* `T₁` – first factor
* `T₂` – second factor

## Output
* Taylor model of the product
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.timesMerged (N : ℕ) (T₁ T₂ : Taylm 𝕋 n) : Taylm 𝕋 n :=
  -- the remainders, with the error boxes in them
  let r := T₁.absorbRounding.rem
  let s := T₂.absorbRounding.rem
  -- the bounds of the polynomial parts
  let p := Taylm.polyBoundsMono T₁.terms
  let q := Taylm.polyBoundsMono T₂.terms
  -- the cross terms `p s + q r + r s`
  let R₀ := Taylm.sumRanges id (Taylm.timesZeroInf p s)
    [Taylm.timesZeroInf q r, Taylm.timesZeroInf r s]
  -- the pairs of terms, the first model's outside, split at the order
  let P := T₁.terms.flatMap fun a => T₂.terms.map fun b => (a, b)
  let keep := P.filter fun x => Nat.ble (Real.Taylm.degree (x.1.2 + x.2.2)) N
  let drop := P.filter fun x => !Nat.ble (Real.Taylm.degree (x.1.2 + x.2.2)) N
  -- the kept products merged into the result, with what their rounding costs
  let K := Taylm.accumTerms [] (keep.map fun x => (mulUp x.1.1 x.2.1, x.1.2 + x.2.2))
  let errK := listSumUp (keep.map fun x => subUp (mulUp x.1.1 x.2.1) (mulDown x.1.1 x.2.1))
  -- the dropped products bounded into the remainder
  let R := Taylm.sumRanges (fun x => Taylm.timesZeroInf (Taylm.monomialRange (x.1.2 + x.2.2))
    ⟨mulDown x.1.1 x.2.1, mulUp x.1.1 x.2.1⟩) R₀ drop
  let err := addUp K.2 errK
  { terms := K.1, rem := R, I_error := ⟨neg err, err⟩, maxOrder := N }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
