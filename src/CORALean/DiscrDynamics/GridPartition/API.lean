module

public import CORALean.DiscrDynamics.GridPartition.GridPartition
public import CORALean.DiscrDynamics.GridPartition.Definitions.API
public import CORALean.DiscrDynamics.GridPartition.Operations.API
public import CORALean.DiscrDynamics.GridPartition.Theorems.API

/-!
# The grid partition

CORA's `partition` (`discrDynamics/@partition`): a box cut into cells by dividers, the
cells numbered with the first dimension fastest. `Operations/` holds CORA's methods,
`Theorems/` what they guarantee: the index maps are inverse, `intersectingCells` returns every cell
meeting a set, `exactIntersectingCells` the cells sharing volume with it and the shares.
-/
