module

public import CORALean.Specification.SyntaxTree.Operations.NthrootFloat

@[expose] public section

/-!
# `nthroot` for an integer degree over a float scalar

`nthroot(x,e)` of MATLAB for an integer degree, enclosed by an interval of floats: the root of
`nthrootFloat` for `e ≥ 0`, and for `e < 0` its reciprocal, `[1/sup, 1/inf]` rounded outward, when
the root's interval is certified to keep away from `0` (`ltStrict`); one that may contain `0` has
no finite reciprocal enclosure, `none`. Soundness is `SyntaxTree.nthrootZFloat_contains`.

## Inputs
* `steps` – bisection steps
* `x` – number
* `e` – integer degree

## Output
* an interval of floats containing the root of that degree, or none near a zero root
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `nthroot(x,e)` for an integer degree: the reciprocal interval of the root for `e < 0`. -/
def SyntaxTree.nthrootZFloat (steps : ℕ) (x : 𝕋) (e : ℤ) : Option (Float.Interval 𝕋) :=
  if 0 ≤ e then some (SyntaxTree.nthrootFloat steps x e.toNat)
  else
    -- 1 / nthroot(x,-e), the root's interval kept away from `0`
    let I := SyntaxTree.nthrootFloat steps x (-e).toNat
    if ltStrict zero I.inf then some ⟨divDown one I.sup, divUp one I.inf⟩
    else if ltStrict I.sup zero then
      some ⟨neg (divUp one (neg I.sup)), neg (divDown one (neg I.inf))⟩
    else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
