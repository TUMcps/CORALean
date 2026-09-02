import CORALean.ContSet.PolyZonotope.Real.API
import CORALean.ContSet.PolyZonotope.Float.API

/-!
# Sparse polynomial zonotopes

Kochdumper and Althoff (2021), and CORA's `polyZonotope`: the first
representation here that is not convex, and the one nonlinear reachability
needs. Its `quadMap` is exact, which is what no convex representation can
manage and what the whole construction is for.

The float layer refines `plus` and `mtimes`. What it does *not* have to refine
is the monomial: an exponent matrix is over ℕ and every operation on it is
exact, so the nominal set's monomials are the exact layer's and rounding is paid
in the generator entries alone — `Float/Theorems/MemGeneratorError` argues it.
-/
