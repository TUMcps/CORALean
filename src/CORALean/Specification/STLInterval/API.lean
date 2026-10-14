module

public import CORALean.Specification.STLInterval.Definitions.API
public import CORALean.Specification.STLInterval.Operations.API
public import CORALean.Specification.STLInterval.STLInterval
public import CORALean.Specification.STLInterval.Theorems.API

/-!
# CORA's `stlInterval`, collected

Time intervals with open and closed ends for signal temporal logic: `STLInterval` is the empty
interval or bounds with two closedness flags, `STLInterval.set` the times it denotes. `Operations`
are the methods of `@stlInterval` and `Theorems` says, for each, which set of times it denotes:
exactly, with `minkDiff` taking `Inf - Inf` as `+∞`, which CORA computes as `NaN`.

Not here: the `display` and `isemptyobject` methods, and `contains_`/`representsa_` of a general set
(`contSet`), which delegate to the closed box.
-/
