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

## Inputs
* `sys` – system
* `L` – observer gain
* `wl` – lower disturbance bound
* `wu` – upper disturbance bound
* `vl` – lower noise bound
* `vu` – upper noise bound
* `xl₀` – lower initial bound
* `xu₀` – upper initial bound
* `u` – inputs
* `y` – measurements

## Output
* the state interval after each number of steps

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real

variable {n nu ny nw nv : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.intervalObserver (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q) (wl wu : Vec ℝ sys.r)
    (vl vu : Vec ℝ sys.s)
    (xl₀ xu₀ : Vec ℝ n) (u : ℕ → Vec ℝ sys.m) (y : ℕ → Vec ℝ sys.q) : ℕ → Interval (Vec ℝ n)
  | 0 => ⟨xl₀, xu₀⟩
  | k + 1 =>
    let I := LinearSysDT.intervalObserver sys L wl wu vl vu xl₀ xu₀ u y k
    let Ep := sys.E.map (max 0)  -- `E⁺`
    let En := Ep - sys.E  -- `E⁻`
    let Gp := (-(L * sys.F)).map (max 0)  -- `(-LF)⁺`
    let Gn := Gp - -(L * sys.F)  -- `(-LF)⁻`
    let du := Ep *ᵥ wu - En *ᵥ wl + Gp *ᵥ vu - Gn *ᵥ vl  -- (37), `d̅`
    let dl := Ep *ᵥ wl - En *ᵥ wu + Gp *ᵥ vl - Gn *ᵥ vu  -- (37), `d̲`
    let xu := sys.A *ᵥ I.sup + sys.B *ᵥ u k + L *ᵥ (y k - sys.C *ᵥ I.sup) + du  -- (36), upper
    let xl := sys.A *ᵥ I.inf + sys.B *ᵥ u k + L *ᵥ (y k - sys.C *ᵥ I.inf) + dl  -- (36), lower
    ⟨xl, xu⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
