import CORALean.ContSet.LevelSet.Real.API

/-!
# Level sets

CORA's `levelSet`: `{x | ∀ i, f x i ⋈ᵢ 0}` for a function `f` and a comparison `≤`, `<` or `=`
per component. Not convex, so the set is whatever `f` makes it, and everything it is closed under
(intersection, preimage, invertible image, translation) is exact.

Real layer only: `f` is an arbitrary real function and has no machine form.
-/
