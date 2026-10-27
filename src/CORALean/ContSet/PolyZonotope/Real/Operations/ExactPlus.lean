module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.exactPlus`

CORA's `@polyZonotope/exactPlus` and [1, Prop. 10]: the sum of two sets written over *one*
factor list. Centers add and all three blocks concatenate, and the exponent matrices
concatenate side by side, not block-diagonally, the whole difference from `plus`. Here `hp`
says the sets share factors, so the dependency the Minkowski sum would have thrown away
survives: the result is a *subset* of `plus`'s. `hp : pZ₁.p = pZ₂.p` replaces [1]'s shared
identifier vector, identity being positional, and `mergeID` is `padBack` (`PadBackExact`).

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* `hp` – both have the same factor count

## Output
* polynomial zonotope of their sum with generators concatenated

## References

* [1] [N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set Representation for
      Reachability Analysis". IEEE Transactions on Automatic Control,
      2021.](../../../../../../references/2021/kochdumper-tac-sparse-polyzonotopes.md)
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.exactPlus (pZ₁ pZ₂ : PolyZonotope α) (hp : pZ₁.p = pZ₂.p) : PolyZonotope α where
  p := pZ₁.p
  h := pZ₁.h + pZ₂.h
  q := pZ₁.q + pZ₂.q
  c := pZ₁.c + pZ₂.c
  G := Fin.append pZ₁.G pZ₂.G
  E := fun k => Fin.append (pZ₁.E k) (pZ₂.E (Fin.cast hp k))
  GI := Fin.append pZ₁.GI pZ₂.GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
