module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.mtimes`

CORA's `@conPolyZono/mtimes`: `map` at `A *ᵥ ·`, spelt with `*ᵥ` because that is
the form every caller states its matrix in.

The dimension variables are `k` and `n` rather than the usual `m` and `n`: the
structure already has a field named `m`, and reading the two in one signature is
harder than renaming one of them.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {k n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.mtimes (M : Mat ℝ k n) (cPZ : ConPolyZono (Vec ℝ n)) :
    ConPolyZono (Vec ℝ k) where
  p := cPZ.p
  h := cPZ.h
  q := cPZ.q
  m := cPZ.m
  s := cPZ.s
  c := M *ᵥ cPZ.c
  G := fun i => M *ᵥ cPZ.G i
  E := cPZ.E
  GI := fun j => M *ᵥ cPZ.GI j
  A := cPZ.A
  b := cPZ.b
  EC := cPZ.EC

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
