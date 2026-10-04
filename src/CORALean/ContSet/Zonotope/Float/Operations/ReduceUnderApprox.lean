import CORALean.ContSet.Zonotope.Float.Operations.ContainsZonotope
import CORALean.ContSet.Zonotope.Float.Operations.Point

/-!
# `Zonotope.reduceUnderApprox`, over a floating-point scalar

CORA's `reduceUnderApprox(Z, 'sadraddini', order)` (Sadraddini and Tedrake, CDC'19, Cor. 6): the
solver `opt` of the bilinear program (43) proposes reduced generators `Gr`; the candidate
zonotope has `Z`'s centre, the generators `Gr` and a zero error box. It is kept only if
`Zonotope.containsZonotope`, with a right inverse `H` of `Z`'s generators the caller proposes,
certifies it inside `Z` (the float replacement of (43)'s containment row, with rounding absorbed);
else the centre alone if that is certified, else `none`. Sufficient only: `some` proves the result
inner, `none` refutes nothing; the solver's order and Hausdorff optimality are not checked.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.reduceUnderApprox
    (opt : (Z : Zonotope 𝕋 n) → Option (Σ h : ℕ, Mat 𝕋 n h))
    (Z : Zonotope 𝕋 n) (H : Mat 𝕋 Z.h n) : Option (Zonotope 𝕋 n) :=
  let centre := Zonotope.point Z.c
  match opt Z with
  | none => if Z.containsZonotope centre H then some centre else none
  | some ⟨h, Gr⟩ =>
    let reduced : Zonotope 𝕋 n := ⟨h, Z.c, Gr, Interval.origin n⟩
    if Z.containsZonotope reduced H then some reduced
    else if Z.containsZonotope centre H then some centre else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
