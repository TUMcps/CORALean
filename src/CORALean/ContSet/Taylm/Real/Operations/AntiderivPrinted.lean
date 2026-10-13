import CORALean.ContSet.Taylm.Real.Operations.IntegrateTerms
import CORALean.ContSet.Taylm.Real.Operations.PolyBounds
import CORALean.ContSet.Taylm.Real.Operations.Degree

/-!
# `Taylm.antiderivPrinted`

[1, Def. 3 (antiderivation)], eq. (2.7), as printed:
`∂ᵢ⁻¹(P, I) = (∫₀^{xᵢ} P_{n-1} dxᵢ, (B(P - P_{n-1}) + I)·(bᵢ - aᵢ))`, at the normalized domain
`[-1, 1]`, whose width is `2`. Kept to state the counterexample against; `Taylm.antideriv` is the
corrected rule.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.antiderivPrinted (i : Fin n) (T : Taylm n) : Taylm n :=
  let N := T.maxOrder
  -- `P_{n-1}`, the rest, and `J = B(P - P_{n-1}) + I`, as in `antideriv`
  let Plow := T.terms.filter fun a => Nat.blt (Taylm.degree a.2) N
  let Prest := T.terms.filter fun a => !Nat.blt (Taylm.degree a.2) N
  let J := ((Taylm.polyBounds Prest).1 + T.remInf, (Taylm.polyBounds Prest).2 + T.remSup)
  -- the remainder times the width `bᵢ - aᵢ = 2`
  { terms := Taylm.integrateTerms i Plow
    remInf := J.1 * 2
    remSup := J.2 * 2
    maxOrder := N }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
