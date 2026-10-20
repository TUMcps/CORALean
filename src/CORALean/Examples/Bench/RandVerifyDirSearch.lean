import CORALean.Examples.Bench.RandVerifyOutZono
import CORALean.Examples.Bench.RandVerifyQuotFloat

/-!
# `randverify`: the direction an unsafe box is farthest beyond the windows in

A search for the angle `θ` maximising the support gap `h(ℓ)` (`supportGap`) with
`ℓ = (cos θ, sin θ)`, in `Float`s: a grid of `grid` angles over the whole circle, then a local
search from the best, halving its step `iters` times. The result is the rational
`t ≈ tan(θ/2)` at `2^-40` (or `1/t` at `2^-40` where `|t| > 1`) for which `ratUnit t` is that
direction, exactly a unit vector; nothing exact depends on `ℓ` being optimal.

## Inputs
* `Ys` – output windows
* `S` – unsafe box
* `grid` – number of grid angles
* `iters` – number of refinement steps

## Output
* angle direction with the largest support gap
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A window as `Float`s: its center and generators. -/
def aux_windowFloat (Y : RandOutZono) : (Float × Float) × Array (Float × Float) :=
  ((quotFloat Y.c.1 Y.den, quotFloat Y.c.2 Y.den),
    Y.gens.map fun (a, b) => (quotFloat a Y.den, quotFloat b Y.den))

/-- `h` at angle `θ`, in `Float`s; `S` as its bounds. -/
def aux_gapFloat (Ws : Array ((Float × Float) × Array (Float × Float)))
    (S : (Float × Float) × (Float × Float)) (θ : Float) : Float :=
  let l₁ := Float.cos θ
  let l₂ := Float.sin θ
  let m := l₁ * (if 0 ≤ l₁ then S.1.1 else S.2.1) + l₂ * (if 0 ≤ l₂ then S.1.2 else S.2.2)
  let top := Ws.foldl (fun t ((c₁, c₂), gs) =>
    let r := gs.foldl (fun s (a, b) => s + (l₁ * a + l₂ * b).abs) (l₁ * c₁ + l₂ * c₂)
    if r > t then r else t) (-(1.0 / 0.0))
  m - top


-- =====================================  MAIN DEFINITION  ====================================== --

def bestDirection (Ys : List RandOutZono) (S : Array (ℚ × ℚ)) (grid iters : ℕ) : ℚ :=
  let Ws := Ys.toArray.map aux_windowFloat
  let f (q : ℚ) : Float := quotFloat q.num q.den
  let b (i : ℕ) : ℚ × ℚ := S.getD i (0, 0)
  let Sf := ((f (b 0).1, f (b 1).1), (f (b 0).2, f (b 1).2))
  let pi : Float := 3.141592653589793
  -- the grid, avoiding `θ = ±π` where `t` is infinite
  let (θ₀, h₀) := (List.range grid).foldl (fun (bθ, bh) i =>
    let θ := -pi + 2 * pi * (i.toFloat + 0.5) / grid.toFloat
    let h := aux_gapFloat Ws Sf θ
    if h > bh then (θ, h) else (bθ, bh)) (0, -(1.0 / 0.0))
  -- the local search, its step halving
  let (θ, _, _) := (List.range iters).foldl (fun (θ, h, step) _ =>
    let hm := aux_gapFloat Ws Sf (θ - step)
    let hp := aux_gapFloat Ws Sf (θ + step)
    if hp > h ∧ hp ≥ hm then (θ + step, hp, step)
    else if hm > h then (θ - step, hm, step) else (θ, h, step / 2)) (θ₀, h₀, 2 * pi / grid.toFloat)
  -- `t = tan(θ/2)` at `2^-40`, `θ` in `[-π, π]`; past `|t| = 1` through `1 / t`, which is small
  let θ := θ - 2 * pi * (θ / (2 * pi)).round
  let τ := Float.tan (θ / 2)
  let k : Float := 1099511627776.0
  if τ.abs ≤ 1 then ((τ * k).round.toInt64.toInt : ℚ) / (1099511627776 : ℚ) else
  let u : ℤ := ((1 / τ) * k).round.toInt64.toInt
  if u = 0 then (if τ > 0 then 1099511627776 else -1099511627776) else (1099511627776 : ℚ) / u

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
