import CORALean.Global.Caratheodory
import CORALean.ContSet.ConPolyZono.Real.Theorems.ConvHullSingleConstruct

/-!
# `convHullSingle` is the convex hull of one set

`convHullSingle_construct` says the closed form denotes the weighted sums of `a`
of the set's points; Carathéodory says those are the convex hull once `a` passes
the dimension. [1] builds that bound into its definition of the hull, taking
`a = n + 1` points of a set in `ℝⁿ` — which is where the count of copies in
[1, Prop. 9] comes from, and the only thing the bound is used for.

Nothing here needs the set to be non-empty: the empty set has no weighted sums
of its points and an empty convex hull alike. `q = 0` is the representation's,
carried from `convHullSingle_construct`.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- With one copy more than the dimension, the closed form is the convex hull. -/
theorem ConPolyZono.convHullSingle_exact [FiniteDimensional ℝ α] (a : ℕ) (cPZ : ConPolyZono α)
    (hq : cPZ.q = 0) (ha : Module.finrank ℝ α + 1 ≤ a) :
    (cPZ.convHullSingle a).construct = convexHull ℝ cPZ.construct := by
  rw [ConPolyZono.convHullSingle_construct a cPZ hq, convexHull_eq_fin ha]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
