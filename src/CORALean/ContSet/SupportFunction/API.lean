module

public import CORALean.ContSet.SupportFunction.Real.API

/-!
# Support functions

A set held as its support function `h(d) = sup {d · x | x ∈ S}`, which denotes every closed convex
set and nothing else. Over ℝ only: a function of all directions is nothing finite to store, and
what a float algorithm computes of one is a certified bound in a direction, `SupportBound`.
-/
