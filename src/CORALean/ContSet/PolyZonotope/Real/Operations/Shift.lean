import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.shift`

The set moved by a vector: the centre takes it and nothing else changes, a
translation being the one map that needs no generator. CORA writes it `pZ + v`.

`map` cannot do it — a translation is affine and not linear — and `plus`
against a one-point set would append an empty generator block and a factor
list to merge. So it is its own operation, as it is in CORA.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The set translated by `v`: the centre moves, the generators do not. -/
def PolyZonotope.shift (pZ : PolyZonotope α) (v : α) : PolyZonotope α where
  p := pZ.p
  h := pZ.h
  q := pZ.q
  c := pZ.c + v
  G := pZ.G
  E := pZ.E
  GI := pZ.GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
