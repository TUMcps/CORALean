import CORALean.ContDynamics.LinearSys.API
import CORALean.ContDynamics.LinearSysDT.API

/-!
# Systems and their reachability, collected

One directory per system class. The systems and their algorithms are written
against the `ContSet` interfaces alone, so none names a representation.

`ReachOuterZonotope` and `TimeIntervalOuterZonotope` are the exceptions, and the
only ones: a guarantee whose hypotheses a representation has to satisfy is worth
stating at one that does.
-/
