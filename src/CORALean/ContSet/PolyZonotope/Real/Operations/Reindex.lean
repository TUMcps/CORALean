import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.reindex`

The dependent generators and their exponent columns read in another order. A
permutation of the summation index changes nothing the set is made of, so the
centre, the independent block, `p`, `q` and `h` all stay where they are — which
is what makes it the only freedom an operation that reorders columns has.

`sort` is this at the permutation that puts the columns in lexicographic order,
and is the only caller so far; the definition asks for no property of the
permutation because nothing below it needs one.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The dependent block read through a permutation of its column index. -/
def PolyZonotope.reindex (pZ : PolyZonotope α) (σ : Equiv.Perm (Fin pZ.h)) : PolyZonotope α where
  p := pZ.p
  h := pZ.h
  q := pZ.q
  c := pZ.c
  G := fun i => pZ.G (σ i)
  E := fun k i => pZ.E k (σ i)
  GI := pZ.GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
