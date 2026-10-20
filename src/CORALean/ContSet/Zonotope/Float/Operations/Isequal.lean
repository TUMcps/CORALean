module

public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.isequal`, over a floating-point scalar

The structural test at tolerance `0`, as over ℝ: the same number of generators, and the center,
the generators and the two ends of the error box equal entry by entry, each entry by the
certified `le` in both directions. Certified in one direction only: `true` is a proof, `false`
refutes nothing. Not CORA's test, which merges parallel generators and ignores their order.

## Inputs
* `Z` – first zonotope
* `S` – second zonotope

## Output
* true when all entries are certified equal
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.isequal (Z S : Zonotope (Vec 𝕋 n)) : Bool :=
  if e : Z.h = S.h then
    (List.finRange n).all (fun i =>
      (le (Z.c i) (S.c i) && le (S.c i) (Z.c i)) &&
      (le (Z.I_error.inf i) (S.I_error.inf i) && le (S.I_error.inf i) (Z.I_error.inf i)) &&
      (le (Z.I_error.sup i) (S.I_error.sup i) && le (S.I_error.sup i) (Z.I_error.sup i)) &&
      (List.finRange Z.h).all fun j =>
        le (Z.G j i) (S.G (Fin.cast e j) i) && le (S.G (Fin.cast e j) i) (Z.G j i))
  else false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
