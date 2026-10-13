module

public import CORALean.ContSet.PolyZonotope.Real.API
public import CORALean.ContSet.PolyZonotope.Float.API

/-!
# Sparse polynomial zonotopes

CORA's `polyZonotope` [1]: the first representation here that is not convex, and
the one nonlinear reachability needs. Its `quadMap` is exact, which is what no
convex representation can manage and what the whole construction is for.

The float layer refines `plus` and `mtimes`. What it does *not* have to refine
is the monomial: an exponent matrix is over ℕ and every operation on it is
exact, so the nominal set's monomials are the exact layer's and rounding is paid
in the generator entries alone — `Float/Theorems/MemGeneratorError` argues it.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/
