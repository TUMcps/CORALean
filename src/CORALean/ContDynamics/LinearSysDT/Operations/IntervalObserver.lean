module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The interval observer without coordinate transformation

[1, Eq. 36] and [1, Eq. 37]: two copies of the Luenberger observer, the upper one driven by `d̅`
and the lower one by `d̲`, where `d̅ = E⁺w̅ - E⁻w̲ + (-LF)⁺v̅ - (-LF)⁻v̲` and `d̲`, the same with
the bounds swapped, bound the disturbance term `E w - L F v` for `w̲ ≤ w ≤ w̅`, `v̲ ≤ v ≤ v̅`
[1, Lemma 2]; `M⁺ = max{0, M}`, `M⁻ = M⁺ - M`. Started from given bounds `x̲₀`, `x̅₀`; an
interval observer when `A - LC ≥ 0` [1, Thm. 4]. Real only, as the other observers are.

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real

variable {n nu ny nw nv : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.intervalObserver (A : Mat ℝ n n) (B : Mat ℝ n nu) (C : Mat ℝ ny n)
    (E : Mat ℝ n nw) (F : Mat ℝ ny nv) (L : Mat ℝ n ny) (wl wu : Vec ℝ nw) (vl vu : Vec ℝ nv)
    (xl₀ xu₀ : Vec ℝ n) (u : ℕ → Vec ℝ nu) (y : ℕ → Vec ℝ ny) : ℕ → Interval (Vec ℝ n)
  | 0 => ⟨xl₀, xu₀⟩
  | k + 1 =>
    let I := LinearSysDT.intervalObserver A B C E F L wl wu vl vu xl₀ xu₀ u y k
    let Ep := E.map (max 0)  -- `E⁺`
    let En := Ep - E  -- `E⁻`
    let Gp := (-(L * F)).map (max 0)  -- `(-LF)⁺`
    let Gn := Gp - -(L * F)  -- `(-LF)⁻`
    let du := Ep *ᵥ wu - En *ᵥ wl + Gp *ᵥ vu - Gn *ᵥ vl  -- (37), `d̅`
    let dl := Ep *ᵥ wl - En *ᵥ wu + Gp *ᵥ vl - Gn *ᵥ vu  -- (37), `d̲`
    let xu := A *ᵥ I.sup + B *ᵥ u k + L *ᵥ (y k - C *ᵥ I.sup) + du  -- (36), upper
    let xl := A *ᵥ I.inf + B *ᵥ u k + L *ᵥ (y k - C *ᵥ I.inf) + dl  -- (36), lower
    ⟨xl, xu⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
