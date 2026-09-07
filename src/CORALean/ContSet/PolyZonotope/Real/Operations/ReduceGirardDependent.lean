import CORALean.ContSet.PolyZonotope.Real.Operations.GirardSplit
import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceBy

/-!
# `PolyZonotope.reduceGirardDependent`

Split out of `Reduce.lean` (issue #62): each `reduce`-family rule now earns its
own file, as CORA gives each a file too.

The same rule with the independent block left out: cut the dependent
generators alone against `n·o` and keep every independent one. Tighter per step
and bounding nothing — the box adds `n` independent generators at every call.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- file-local: only `reduceGirardDependent` below needs it
/-- Nothing dropped: what a rule hands `reduceBy` for a block it leaves
alone. -/
noncomputable def PolyZonotope.aux_keepAll (m : ℕ) : Split (Fin m) into (Fin m) ⊕ (Fin 0) :=
  (Partition.split m 0).reindex (finCongr (Nat.add_zero m).symm)


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def PolyZonotope.reduceGirardDependent (PZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PolyZonotope (Vec ℝ n) :=
  if o * n < PZ.h then
    PZ.reduceBy
      (PolyZonotope.girardSplit (PolyZonotope.girardMetric PZ.G) ((o - 1) * n))
      (PolyZonotope.aux_keepAll PZ.q)
  else PZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
