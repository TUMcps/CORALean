import CORALean.Examples.Bench.RandVerifyOutZono
import CORALean.Examples.Bench.RandVerifyRatUnit

/-!
# `randverify`: the support gap of an unsafe box beyond the windows

`h(ℓ) = -ρ_S(-ℓ) - max_k ρ_{Y_k}(ℓ) = min_{s ∈ S} ℓ · s - max_k max_{y ∈ Y_k} ℓ · y` for the unit
vector `ℓ = ratUnit t`, exactly over ℚ: how far the box `S` lies beyond every window along `ℓ`.
Positive means `ℓ` separates `S` from every window, by at least `h(ℓ)`. Translating `S` by `δ ℓ`
adds exactly `δ` to it, since `‖ℓ‖₂ = 1`. `none` if there is no window.

## Inputs
* `Ys` – output windows
* `S` – unsafe box
* `t` – rational direction parameter

## Output
* support gap of the box beyond the windows
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `ρ_Y(p) = (p · c + Σ_j |p · g_j|) / den`, exactly. -/
private def aux_supportAt (Y : RandOutZono) (p : ℤ × ℤ) : ℚ :=
  let s := Y.gens.foldl (fun s (a, b) => s + (p.1 * a + p.2 * b).natAbs) (0 : ℕ)
  ((p.1 * Y.c.1 + p.2 * Y.c.2 + s : ℤ) : ℚ) / Y.den


-- =====================================  MAIN DEFINITION  ====================================== --

def supportGap (Ys : List RandOutZono) (S : Array (ℚ × ℚ)) (t : ℚ) : Option ℚ :=
  let ((p₁, p₂), q) := ratUnit t
  -- `min_{s ∈ S} p · s`, the lower bound where `p_i ≥ 0` and the upper one where not
  let b (i : ℕ) : ℚ × ℚ := S.getD i (0, 0)
  let m : ℚ := p₁ * (if 0 ≤ p₁ then (b 0).1 else (b 0).2) +
    p₂ * (if 0 ≤ p₂ then (b 1).1 else (b 1).2)
  let top := Ys.foldl (fun acc Y =>
    let r := aux_supportAt Y (p₁, p₂)
    some (acc.elim r (max r))) none
  top.map fun r => (m - r) / q

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
