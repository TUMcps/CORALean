module

public import CORALean.ContSet.Ellipsoid.Real.Instances
public import CORALean.ContSet.Ellipsoid.Real.Definitions.Unchecked
public import CORALean.ContSet.InflatedContSet.InflatedContSet

@[expose] public section

/-!
# Ellipsoids over a floating-point scalar: the representation

The exact layer's shape matrix `Q` and center `q` [1, Def. 4] held in `𝕋`, plus the error box that
makes it an `InflatedContSet`. The nominal part is the stored floats read as reals, unchecked
(`Real.Ellipsoid.Unchecked`), and denotes what CORA's constructor `ellipsoid(Q, q)` makes of them
(`Real.Ellipsoid.ofShape`): the ellipsoid of `Q` when `Q` is positive semi-definite, and where
CORA's constructor refuses, the center alone. No float operation trusts
`Q` to be positive semi-definite. One that only encloses splits on it in its proof (a refused
`Q` leaves the center, which every result keeps), and its result is positive semi-definite
whenever its argument is, because rounding is paid into `Q` itself (`Operations/Inflate`). One
whose answer claims points of the set (`containsPoint`, `isBigger`, `isFullDim`) runs the check
`isPsd`, a factor `L` from an unverified Cholesky decomposition and `Q - L Lᵀ` certified
diagonally dominant in outward rounding, and answers `false` where it fails.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Ellipsoid (𝕋 : Type) (n : ℕ) where
  /-- The shape matrix, CORA's `Q`. -/
  Q : Mat 𝕋 n n
  /-- The center, CORA's `q`. -/
  q : Vec 𝕋 n
  /-- The error box, the paper's `𝓘_error`. -/
  I_error : Interval (Vec 𝕋 n)

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (Ellipsoid 𝕋 n) (CORALean.Real.Ellipsoid.Unchecked n)
      (Vec 𝕋 n) (Vec ℝ n) where
  nominal E := ⟨toRealMat E.Q, toRealVec E.q⟩
  I_error E := E.I_error

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev Ellipsoid.construct [SoundFloatArithmetic 𝕋] (E : Ellipsoid 𝕋 n) : Set (Vec ℝ n) :=
  InflatedContSet.construct E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
