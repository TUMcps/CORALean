module

public import CORALean.ContDynamics.LinearARX.Definitions.GO
public import CORALean.ContDynamics.LinearARX.Definitions.GOFloat
public import CORALean.ContDynamics.LinearARX.Definitions.ReachOut
public import CORALean.ContDynamics.LinearARX.Definitions.ReachWindow

/-!
# What the ARMAX reachable sets mean

The exact sets the algorithms of Lützow and Althoff (CDC 2023) are measured against:
`ReachOut` the outputs at one step, `ReachWindow` the window of `p` outputs at once.
-/
