import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.split`

Splitting a zonotope along its `j`-th generator [1, Prop. 3.8]: halve that
generator and shift the centre by `∓g_j/2`, which cuts the coefficient cube at
`β_j = 0` and leaves every other coefficient alone.

A pair, as CORA's `split` returns both halves at once and neither is meaningful
without the other. The generator count does not change, so a split costs no
order; what it costs is that the halves overlap, in `Z` with `g_j` dropped.

Over any real module, like `Zonotope` itself, and `noncomputable` with it: ℝ has
no inverse that runs.

`Real` only, since `FloatOps` carries no exact halving — `half` is `Dyadic`'s
alone — so a float split rounds the centre shift and the halved generator in
opposite directions, and its halves cover only after an inflation that is a
design choice rather than a translation of this one.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       11-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two halves of `Z` along its `j`-th generator: that generator halved in
both, and the centre moved to the middle of each half. -/
noncomputable def Zonotope.split (Z : Zonotope α) (j : Fin Z.h) : Zonotope α × Zonotope α :=
  (⟨Z.h, Z.c - (2 : ℝ)⁻¹ • Z.G j, Function.update Z.G j ((2 : ℝ)⁻¹ • Z.G j)⟩,
    ⟨Z.h, Z.c + (2 : ℝ)⁻¹ • Z.G j, Function.update Z.G j ((2 : ℝ)⁻¹ • Z.G j)⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
