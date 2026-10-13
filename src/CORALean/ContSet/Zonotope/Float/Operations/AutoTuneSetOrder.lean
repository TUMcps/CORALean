import CORALean.ContSet.Zonotope.Float.Operations.ReduceBoxError
import CORALean.Global.Float.ToRat

/-!
# `Alg. 2` lines 19-22 in floats: the order to reduce `P̂^U_0` to

`Real.Zonotope.autoTuneSetOrder`, [1, Alg. 2] lines 19-22, computed in `𝕋`: the coarsest order
`ρ ≥ 1` at which `Δε^r_k(ρ)` clears the admissible share, `none` where the sweep gives out. The
comparison is in ℚ, through `ToRat`, so it is exact. Which order comes out affects how tight the
result is, never whether it is sound: every order is a `reduce`, so no theorem about the order
is owed.

A NaN `errUp` reads through `ToRat` as `1.5 · 2 ^ 1024`, fails `≤ εrτ` and keeps the sweep
going. Tightness only.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 20-22: the coarsest order `ρ ≥ 1` at which `Δε^r_k(ρ)` clears the admissible share,
`none` where the sweep reaches `Z.h + 1` without one. -/
def Zonotope.autoTuneSetOrder (Z : Zonotope (Vec 𝕋 n)) (εrτ : ℚ) : ℕ → ℕ → Option ℕ
  | _, 0 => none
  | ρ, k + 1 =>
    let ρ' := ρ + 1                                           -- 21. ρ_k ← ρ_k + 1
    let Δεr := ToRat.toRat (Z.reduceBoxError ρ')               -- 21. Δε^r_k(ρ_k), Prop. 4
    if Δεr ≤ εrτ then some ρ'                                  -- 22. until Δε^r_k(ρ_k) ≤ ε^{r,τ}_k
    else Zonotope.autoTuneSetOrder Z εrτ ρ' k

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
