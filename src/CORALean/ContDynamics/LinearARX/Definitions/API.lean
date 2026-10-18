module

public import CORALean.ContDynamics.LinearARX.Definitions.GO
public import CORALean.ContDynamics.LinearARX.Definitions.GOFloat
public import CORALean.ContDynamics.LinearARX.Definitions.ReachOutExact
public import CORALean.ContDynamics.LinearARX.Definitions.ReachWindowExact

/-!
# What the ARMAX reachable sets mean

The exact sets the algorithms of Lützow and Althoff (CDC 2023) are measured against:
`ReachOutExact` the outputs at one step, `ReachWindowExact` the window of `p` outputs at once.
-/
