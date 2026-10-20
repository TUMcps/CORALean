module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The interval observer in transformed coordinates

[1, Thm. 5], its Eqs. 42a-42d and 43: the interval observer [1, Eq. 36] run for `z = S x`, with
`R = S (A - LC) S⁻¹`: started at `z̲₀ = S⁺x̲₀ - S⁻x̅₀`, `z̅₀ = S⁺x̅₀ - S⁻x̲₀`, and driven by
`g̅ = (SE)⁺w̅ - (SE)⁻w̲ + (-SLF)⁺v̅ - (-SLF)⁻v̲` and `g̲`; `M⁺ = max{0, M}`, `M⁻ = M⁺ - M`.
The bounds in the original coordinates are `intervalObserverTransformed`. Real only, as the
other observers are.

## Inputs
* `sys` – system
* `L` – observer gain
* `S` – coordinate transformation
* `wl` – lower disturbance bound
* `wu` – upper disturbance bound
* `vl` – lower noise bound
* `vu` – upper noise bound
* `xl₀` – lower initial bound
* `xu₀` – upper initial bound
* `u` – inputs
* `y` – measurements

## Output
* the interval in transformed coordinates after each number of steps

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

noncomputable def LinearSysDT.intervalObserverCoord (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q)
    (S : Mat ℝ n n)
    (wl wu : Vec ℝ sys.r) (vl vu : Vec ℝ sys.s) (xl₀ xu₀ : Vec ℝ n) (u : ℕ → Vec ℝ sys.m)
    (y : ℕ → Vec ℝ sys.q) : ℕ → Interval (Vec ℝ n)
  | 0 =>
    let Sp := S.map (max 0)  -- `S⁺`
    let Sn := Sp - S  -- `S⁻`
    ⟨Sp *ᵥ xl₀ - Sn *ᵥ xu₀, Sp *ᵥ xu₀ - Sn *ᵥ xl₀⟩  -- (42a), (42b)
  | k + 1 =>
    let I := LinearSysDT.intervalObserverCoord sys L S wl wu vl vu xl₀ xu₀ u y k
    let R := S * (sys.A - L * sys.C) * S⁻¹  -- `R = S (A - LC) S⁻¹`
    let K := S * sys.E  -- `SE`
    let G := -(S * L * sys.F)  -- `-SLF`
    let gu := K.map (max 0) *ᵥ wu - (K.map (max 0) - K) *ᵥ wl + G.map (max 0) *ᵥ vu -
      (G.map (max 0) - G) *ᵥ vl  -- (43), `g̅`
    let gl := K.map (max 0) *ᵥ wl - (K.map (max 0) - K) *ᵥ wu + G.map (max 0) *ᵥ vl -
      (G.map (max 0) - G) *ᵥ vu  -- (43), `g̲`
    let zu := R *ᵥ I.sup + (S * sys.B) *ᵥ u k + (S * L) *ᵥ y k + gu  -- (42c)
    let zl := R *ᵥ I.inf + (S * sys.B) *ᵥ u k + (S * L) *ᵥ y k + gl  -- (42d)
    ⟨zl, zu⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
