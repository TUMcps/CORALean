module

public import CORALean.ContSet.Taylm.Real.Operations.PolyBounds

@[expose] public section

/-!
# `Taylm.times`

CORA's `times` of two models (`aux_s_times_tt`): the product polynomial, truncated at the larger
order, the dropped terms bounded into the remainder (`priv_compress`), and the three cross terms
`B(p₁)·I₂ + B(p₂)·I₁ + I₁·I₂` added as interval products, `B` being `polyBounds`. CORA's
tolerance, moving coefficients under `1e-8` into the remainder, is a precision choice and not
done.

This is the multiplication of [1, Def. 2], with `I₁·₂ = B(Pₑ) + B(P₁)·I₂ + B(P₂)·I₁ + I₁·I₂`, as
sharp as interval evaluation, which the source demands.

## Inputs
* `T₁` – first factor
* `T₂` – second factor

## Output
* Taylor model of the product

## References

* [1] [K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics,
      2003.](../../../../../../references/2003/makino-ijpam-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.times (T₁ T₂ : Taylm n) : Taylm n :=
  let N := max T₁.maxOrder T₂.maxOrder
  let L := Taylm.mulTerms T₁.terms T₂.terms
  -- the terms above the order, bounded rather than kept
  let D := Taylm.polyBounds (L.filter fun a => !Nat.ble (Taylm.degree a.2) N)
  let P₁ := Taylm.polyBounds T₁.terms
  let P₂ := Taylm.polyBounds T₂.terms
  { terms := L.filter fun a => Nat.ble (Taylm.degree a.2) N
    rem := ⟨D.inf + Interval.mulLo P₁.inf P₁.sup T₂.rem.inf T₂.rem.sup
        + Interval.mulLo P₂.inf P₂.sup T₁.rem.inf T₁.rem.sup
        + Interval.mulLo T₁.rem.inf T₁.rem.sup T₂.rem.inf T₂.rem.sup,
      D.sup + Interval.mulHi P₁.inf P₁.sup T₂.rem.inf T₂.rem.sup
        + Interval.mulHi P₂.inf P₂.sup T₁.rem.inf T₁.rem.sup
        + Interval.mulHi T₁.rem.inf T₁.rem.sup T₂.rem.inf T₂.rem.sup⟩
    maxOrder := N }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
