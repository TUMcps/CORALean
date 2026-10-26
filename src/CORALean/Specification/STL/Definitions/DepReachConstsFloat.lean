module

public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.Specification.STL.Definitions.DepReachConsts

@[expose] public section

/-!
# The constants of line 1 of the dependency preserving reachability algorithm, over floats

[1, Alg. 1], line 1, held in floats: `ũ = B c_u` and `U₀ = B(U ⊕ (-c_u))` as float zonotopes, the
propagation matrix `T` of Eq. (14) and the interval matrices `F` and `G` of Eq. (18) as float
interval matrices, and the bloating `D` of Eq. (15). The float constants enclose the real ones when
each holds the real object in its place (`DepReachConstsFloat.Encloses`): the point `ũ` and the
matrix `T` among the points of theirs, the others as sets.

## Inputs
* `𝕋` – scalar of the stored floats
* `n` – state dimension

## Output
* the constants of line 1 in floats
## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- `ũ`, `U₀`, `T`, `F`, `G` and `D` of [1, Alg. 1], line 1, in floats. -/
structure STL.DepReachConstsFloat (𝕋 : Type) (n : ℕ) where
  ũ : Float.Zonotope (Vec 𝕋 n)
  U₀ : Float.Zonotope (Vec 𝕋 n)
  T : Float.Interval (Mat 𝕋 n n)
  F : Float.Interval (Mat 𝕋 n n)
  G : Float.Interval (Mat 𝕋 n n)
  D : Float.Zonotope (Vec 𝕋 n)

/-- The float constants hold the real ones. -/
def STL.DepReachConstsFloat.Encloses (csF : STL.DepReachConstsFloat 𝕋 n)
    (csR : STL.DepReachConsts n) : Prop :=
  csR.ũ ∈ csF.ũ.construct ∧ csR.U₀.construct ⊆ csF.U₀.construct ∧ csR.T ∈ csF.T.construct ∧
    csR.F.construct ⊆ csF.F.construct ∧ csR.G.construct ⊆ csF.G.construct ∧
    csR.D.construct ⊆ csF.D.construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
