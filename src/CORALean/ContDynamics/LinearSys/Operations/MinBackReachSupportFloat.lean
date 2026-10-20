module

public import CORALean.ContDynamics.LinearSys.Operations.MinBackReachRunFloat
public import CORALean.ContSet.ConZonotope.Float.Operations.SupportBound
public import CORALean.ContSet.HPolytope.Float.Operations.RowLin
public import CORALean.ContSet.Zonotope.Float.Operations.LowerDot

@[expose] public section

/-!
# `Alg. 2` lines 12-13 in floats: one direction's support value at a step

`aux_minBackReachSupport` computed in `𝕋`: [1, Alg. 2] lines 12-13, eq. (46): `ρ(R̂^∃(-τ_k;u_j(·)),
N_(j,·))`, the step's own support value less what the direction's input trajectory takes off it.
The first term is rounded up (`ConZonotope.boundDot`, checked in ℚ against the float values) and
the second down (`Zonotope.lowerDot`), so the difference, rounded up, is above the real one. The
exact layer takes a support oracle; here it is computed, which is why `ToRat 𝕋` is asked.

## Inputs
* `sys` – linear system
* `CZ` – target constrained zonotope
* `W₀` – initial disturbance float zonotope
* `U₀` – initial input float zonotope
* `Zw` – center trajectory contribution
* `N` – direction matrix
* `t₀` – float start time
* `Δt` – float step length
* `η` – Taylor order
* `ν` – number of squarings
* `k` – step index
* `j` – direction index

## Output
* float support value of the direction at the step, rounded up

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 12-13, eq. (46): `ρ(R̂^∃(-τ_k;u_j(·)), N_(j,·))`, rounded up. -/
def LinearSys.minBackReachSupportFloat (sys : LinearSys 𝕋 n)
    (CZ : ConZonotope 𝕋 (Vec 𝕋 n)) (W₀ U₀ : Zonotope (Vec 𝕋 n)) (Zw : 𝕋 → Zonotope (Vec 𝕋 n))
    (N : Mat 𝕋 q n)
    (t₀ Δt : 𝕋) (η ν k : ℕ) (j : Fin q) : 𝕋 :=
  let s := sys.minBackReachRunFloat CZ W₀ U₀ Zw t₀ Δt η ν k
  let ρR := (s.R.boundDot (c := rowLin N j) (N j) fun _ => rfl).val   -- ρ(R̂^∃, N_(j,·)), up
  let ρU := s.ZU₀.lowerDot (-(N j))                      -- ρ(Ẑ_{U₀}, -N_(j,·)), down
  subUp ρR ρU

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
