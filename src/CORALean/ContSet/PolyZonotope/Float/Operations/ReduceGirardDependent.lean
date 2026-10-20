module

public import CORALean.ContSet.PolyZonotope.Float.Operations.GirardSplit
public import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceBy
public import CORALean.Global.Partition

@[expose] public section

/-!
# `PolyZonotope.reduceGirardDependent`

Split out of `Reduce.lean` (issue #62): each `reduce`-family rule now earns its
own file, as CORA gives each a file too.

The same rule with the independent block left out: cut the dependent
generators alone against `n·o` and keep every independent one. Tighter per step
and bounding nothing — the box adds `n` independent generators at every call.

## Inputs
* `pZ` – polynomial zonotope
* `o` – target order

## Output
* polynomial zonotope with dependent generators reduced by Girard's method
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- file-local: only `reduceGirardDependent` below needs it
/-- Nothing dropped: what a rule hands `reduceBy` for a block it leaves
alone. -/
def PolyZonotope.aux_keepAll (m : ℕ) : Split (Fin m) into (Fin m) ⊕ (Fin 0) :=
  (Partition.split m 0).reindex (finCongr (Nat.add_zero m).symm)


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.reduceGirardDependent (pZ : PolyZonotope (Vec 𝕋 n)) (o : ℕ) :
    PolyZonotope (Vec 𝕋 n) :=
  if o * n < pZ.h then
    pZ.reduceBy
      (PolyZonotope.girardSplit (PolyZonotope.girardMetric pZ.G) ((o - 1) * n))
      (PolyZonotope.aux_keepAll pZ.q)
  else pZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
