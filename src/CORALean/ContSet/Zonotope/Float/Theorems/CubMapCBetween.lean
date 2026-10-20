module

public import CORALean.ContSet.Zonotope.Float.Operations.CubMapDep
public import CORALean.ContSet.Zonotope.Float.Theorems.CubFoldBracket
public import CORALean.ContSet.Zonotope.Real.Operations.CubMap

@[expose] public section

/-!
# The exact center of `cubMap` lies between the two stored roundings

The exact center `cubFold (0, 0, 0) + ½ Σⱼ cubFold (0, j, j)` on the read-back operand is bracketed
term by term (`cubFold_bracket`), the sum by `sumDown_le_sum` and `sum_le_sumUp`, and halving is
exact. The stored center is the lower end, and the gap to the upper is what the box is charged.

## Inputs
* `T` – cubic tensor
* `Z` – zonotope
* `i` – output coordinate

## Hypotheses
* none

## Conclusion
* exact center lies between the two roundings
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.cubMapC_between (T : Fin m → Fin n → Mat 𝕋 n n)
    (Z : Zonotope (Vec 𝕋 n)) (i : Fin m) : -- --- CONCL ---
    toReal (Zonotope.cubMapCDown T Z i)
        ≤ (Real.Zonotope.cubMap (fun i k => toRealMat (T i k))
            (nominal Z : Real.Zonotope (Vec ℝ n))).c i
      ∧ (Real.Zonotope.cubMap (fun i k => toRealMat (T i k))
            (nominal Z : Real.Zonotope (Vec ℝ n))).c i
        ≤ toReal (Zonotope.cubMapCUp T Z i) := by -- --- PROOF ---
  have hR : (Real.Zonotope.cubMap (fun i k => toRealMat (T i k))
        (nominal Z : Real.Zonotope (Vec ℝ n))).c i
      = Real.Zonotope.cubFold (fun i k => toRealMat (T i k))
          (nominal Z : Real.Zonotope (Vec ℝ n)) i 0 0 0
        + 1 / 2 * ∑ y : Fin Z.h, Real.Zonotope.cubFold (fun i k => toRealMat (T i k))
          (nominal Z : Real.Zonotope (Vec ℝ n)) i 0 y.succ y.succ := rfl
  rw [hR]
  -- the sum of the pure squares, from either side
  have hs1 := sumDown_le_sum fun y : Fin Z.h => Zonotope.cubFoldDown T Z i 0 y.succ y.succ
  have hs2 := sum_le_sumUp fun y : Fin Z.h => Zonotope.cubFoldUp T Z i 0 y.succ y.succ
  have hlo : ∑ y : Fin Z.h, toReal (Zonotope.cubFoldDown T Z i 0 y.succ y.succ)
      ≤ ∑ y : Fin Z.h, Real.Zonotope.cubFold (fun i k => toRealMat (T i k))
          (nominal Z : Real.Zonotope (Vec ℝ n)) i 0 y.succ y.succ :=
    Finset.sum_le_sum fun y _ => (Zonotope.cubFold_bracket T Z i 0 y.succ y.succ).1
  have hhi : ∑ y : Fin Z.h, Real.Zonotope.cubFold (fun i k => toRealMat (T i k))
          (nominal Z : Real.Zonotope (Vec ℝ n)) i 0 y.succ y.succ
      ≤ ∑ y : Fin Z.h, toReal (Zonotope.cubFoldUp T Z i 0 y.succ y.succ) :=
    Finset.sum_le_sum fun y _ => (Zonotope.cubFold_bracket T Z i 0 y.succ y.succ).2
  -- the center, rounded each way, with halving exact
  have hd := addDown_le_add (Zonotope.cubFoldDown T Z i 0 0 0)
    (half (sumDown fun y : Fin Z.h => Zonotope.cubFoldDown T Z i 0 y.succ y.succ))
  have hu := add_le_addUp (Zonotope.cubFoldUp T Z i 0 0 0)
    (half (sumUp fun y : Fin Z.h => Zonotope.cubFoldUp T Z i 0 y.succ y.succ))
  have h0 := Zonotope.cubFold_bracket T Z i 0 0 0
  simp only [Zonotope.cubMapCDown, Zonotope.cubMapCUp]
  rw [toReal_half] at hd hu
  constructor <;> linarith [h0.1, h0.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
