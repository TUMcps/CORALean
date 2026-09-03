import CORALean.ContDynamics.LinearSys.API
import CORALean.ContDynamics.LinearSysDT.API
import CORALean.ContDynamics.NeurNetContrSys.API
import CORALean.ContDynamics.NeurNetContrSysDT.API
import CORALean.ContDynamics.NonlinearSys.API
import CORALean.ContDynamics.OutputEq.API

/-!
# Systems and their reachability, collected

One directory per system class, and `OutputEq`, which is not one. The algorithms
are written against the `ContSet` interfaces alone, so none names a
representation. The `*Zonotope` and `*ConZonotope` theorems are the exceptions:
they say what is left once a representation that does have the required
properties is substituted in.

`OutputEq` is CORA's `y = C x + D u`, kept out of the system classes so that it
applies to all of them: it is paired with a reachable set and an input set at
the point of use, which is what lets a sampled system read `u` from the set its
run was described by rather than from the one its discretization steps with.

`NonlinearSys` computes nothing of its own: conservative linearization hands a
confined run to `LinearSys`, so every reachability guarantee in the directory is
a linear one applied to a widened input set. Re-linearizing is that step
iterated with a fresh certificate each time, and the chaining is an induction on
the step count.

The two closed loops compute nothing of their own either, and are the only
directories here that reach outside `ContDynamics`: the input set is what `NN`
propagates. `NeurNetContrSysDT` alternates that with one discrete plant step, so
the controller runs at the plant's rate. `NeurNetContrSys` is the sampled
continuous loop, where the rates come apart — the controller acts every `N`
reachability steps and its input is held in between, which is two nested
recursions rather than one alternation.
-/
