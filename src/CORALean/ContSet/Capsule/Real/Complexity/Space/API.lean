/-!
# What `Capsule` costs

`Capsule` carries no count at all: its fields are a centre `c`, a segment
direction `g` and a radius `r`, three plain values rather than a generator or
constraint list indexed by some `Fin k`. There is no `Operations/` directory
either — `Instances.lean` already explains why the representation has no
operations to cost.

So there is nothing here that is both non-obvious and not a scalar-operation
count, exactly `Interval`'s situation (see its own `Complexity/Space/API.lean`). This
directory accordingly holds no theorems for `Capsule`, only this paragraph
saying why.
-/
