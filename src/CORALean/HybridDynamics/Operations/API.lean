import CORALean.HybridDynamics.Operations.Jump

/-!
# What a hybrid automaton computes, collected

One operation: the reset propagated over a set. Everything else a step needs —
the flow enclosure, the guard intersection — is an operation of `LinearSys` or
of a representation, not of the automaton.
-/
