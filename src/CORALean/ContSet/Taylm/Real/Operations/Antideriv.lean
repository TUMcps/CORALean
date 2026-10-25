module

public import CORALean.ContSet.Taylm.Real.Operations.IntegrateTerms
public import CORALean.ContSet.Taylm.Real.Operations.PolyBounds

@[expose] public section

/-!
# `Taylm.antideriv`

[1, Def. 3 (antiderivation)], eq. (2.7), corrected: the part `P_{n-1}` of order below `n` is
integrated, and `J = B(P - P_{n-1}) + I` is multiplied by the interval `[aᵢ - x₀ᵢ, bᵢ - x₀ᵢ]` of
signed lengths `xᵢ - x₀ᵢ`, here `[-1, 1]`, where the source multiplies by the width `bᵢ - aᵢ`.
The integral of something in `J` over a segment of signed length `ℓ` is in `ℓ·J`, which the
width alone misses whenever `J` is not symmetric and `ℓ` can be negative
(`AntiderivPrinted`).

## Inputs
* `i` – variable index
* `T` – Taylor model

## Output
* Taylor model of the antiderivative in that variable

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.antideriv (i : Fin n) (T : Taylm n) : Taylm n :=
  let N := T.maxOrder
  -- `P_{n-1}`, the terms below the order, and the rest `P - P_{n-1}`
  let Plow := T.terms.filter fun a => Nat.blt (Taylm.degree a.2) N
  let Prest := T.terms.filter fun a => !Nat.blt (Taylm.degree a.2) N
  -- `J = B(P - P_{n-1}) + I`
  let J := ((Taylm.polyBounds Prest).inf + T.rem.inf, (Taylm.polyBounds Prest).sup + T.rem.sup)
  -- `∫₀^{xᵢ} P_{n-1} dxᵢ`, and `J` times the signed lengths `[-1, 1]`
  { terms := Taylm.integrateTerms i Plow
    rem := ⟨Interval.mulLo J.1 J.2 (-1) 1, Interval.mulHi J.1 J.2 (-1) 1⟩
    maxOrder := N }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
