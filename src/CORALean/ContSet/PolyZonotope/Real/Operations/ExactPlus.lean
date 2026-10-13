module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.exactPlus`

CORA's `@polyZonotope/exactPlus` and [1, Prop. 10]: the sum of two sets written
over *one* factor list. Centres add and all three blocks concatenate, and the
exponent matrices concatenate too — side by side, not block-diagonally, which is
the whole difference from `plus`.

`plus` must separate the factors because nothing says the two sets were written
against the same ones; here `hp` says exactly that, so a factor that moved both
sets moves the sum, and the dependency the Minkowski sum would have thrown away
survives. The result is a *subset* of `plus`'s and never wider.

`hp : pZ₁.p = pZ₂.p` in place of [1]'s shared identifier vector, factor identity
being positional here, and `mergeID` is `padBack` — see `PadBackExact`. `pZ₂`'s
exponent rows are read at `pZ₁`'s indices through `Fin.cast`, as `bilin`'s are.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
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
