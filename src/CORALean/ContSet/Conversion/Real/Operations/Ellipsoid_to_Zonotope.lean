module

public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.SqNormLeMaxNormSq
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# An ellipsoid as a zonotope

CORA's default `zonotope(E)`, `'outer:box'`, is `priv_encParallelotope(E)`: `zonotope(q, sqrtm(Q))`,
the columns of the ellipsoid's own generator `E.G = Q^{1/2}`. At a degenerate `Q` CORA first
restricts to the range by an SVD and takes the generators `U(:,1:r) sqrt(Σ_r)`; here the columns
of `Q^{1/2}` stay, a parallelotope enclosing the same ellipsoid, not CORA's for `rank Q < n`. The
other modes are `zonotopeNorm` and `zonotopeInnerNorm` below (`'outer:norm'`, `'inner:norm'`).

## Inputs
* `E` – ellipsoid

## Output
* zonotope of the ellipsoid

## References

* [1] [V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". 2020 American Control Conference (ACC),
      2020.](../../../../../../references/2020/gassmann-acc-zonotope-ellipsoid.md)
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Ellipsoid.zonotope (E : Ellipsoid n) : Zonotope (Vec ℝ n) where
  h := n
  c := E.q
  G := fun j i => E.G i j

/-- [1, Thm. 2]: `Z(r^{-1/2} T⁻¹ S, ē)`, `T⁻¹` the ellipsoid's generator. -/
noncomputable def Ellipsoid.zonotopeInnerNorm (E : Ellipsoid n) {m : ℕ} (S : Fin m → Vec ℝ n)
    (r : ℝ) : Zonotope (Vec ℝ n) where
  h := m
  c := E.q
  G := fun j => (√r)⁻¹ • (E.G *ᵥ S j)

/-- [1, Thm. 4]: `Z(l^{-1/2} T⁻¹ S, ē)`, `T⁻¹` the ellipsoid's generator. -/
noncomputable def Ellipsoid.zonotopeNorm (E : Ellipsoid n) {m : ℕ} (S : Fin m → Vec ℝ n)
    (l : ℝ) : Zonotope (Vec ℝ n) where
  h := m
  c := E.q
  G := fun j => (√l)⁻¹ • (E.G *ᵥ S j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
