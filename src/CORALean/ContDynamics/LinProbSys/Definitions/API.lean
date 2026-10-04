import CORALean.ContDynamics.LinProbSys.Definitions.PostState

/-!
# What `LinProbSys` carries between steps

`PostState` is the four sets `post` reads from `options` and writes back: the homogeneous
solution, the deterministic particular solution as a box and the zonotope it grows by, and the
probabilistic particular solution.
-/
