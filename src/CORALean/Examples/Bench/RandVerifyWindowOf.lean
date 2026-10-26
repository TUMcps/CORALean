import CORALean.Examples.Bench.RandVerifyOutZono
import CORALean.Examples.Bench.RandVerifyQuotFloat
import CORALean.Examples.Bench.RandVerifyWindow

/-!
# `randverify`: the candidate normals of a window, and its support along each

`ρ_Y(n) = n · c + Σ_j |n · g_j|` for the zonotope `Y`, in integers over `Y.den`, at every candidate
normal: `±` the perpendicular `(-b, a)` of each generator `g = (a, b)`, and `±e₁`, `±e₂`. Each
generator is first turned into the upper half-plane and the generators sorted by angle, exactly, by
the sign of the cross product. For `n = (-b, a)` at the `j`-th, `n · g_i = g_j × g_i` is `≥ 0` for
every `i` after `j` and `≤ 0` before, so `Σ_i |n · g_i| = g_j × (T - 2 P_j - g_j)`, with `T` the
sum of all generators and `P_j` that of those before `j`: one prefix sum instead of a sum per
normal.

## Inputs
* `Y` – output window

## Output
* candidate normals with the support along each
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private def aux_cross (g h : ℤ × ℤ) : ℤ := g.1 * h.2 - g.2 * h.1

/-- `g` or `-g`, whichever lies in the upper half-plane `b > 0 ∨ (b = 0 ∧ a > 0)`. -/
private def aux_upper (g : ℤ × ℤ) : ℤ × ℤ :=
  if 0 < g.2 ∨ (g.2 = 0 ∧ 0 < g.1) then g else (-g.1, -g.2)

/-- `ρ_Y(n)` and `ρ_Y(-n)`, given `Σ_i |n · g_i|`, with the length of `n`. -/
private def aux_pushPair (den : ℕ) (acc : Array (ℤ × ℤ × ℤ × ℕ × Float)) (c : ℤ × ℤ) (n : ℤ × ℤ)
    (s : ℤ) : Array (ℤ × ℤ × ℤ × ℕ × Float) :=
  let nc := n.1 * c.1 + n.2 * c.2
  let N := (n.1 * n.1 + n.2 * n.2).toNat
  let k := Nat.log2 N / 2
  let scale := den * 2 ^ k
  let nrm := (quotFloat N (4 ^ k)).sqrt
  (acc.push (n.1, n.2, nc + s, scale, nrm)).push (-n.1, -n.2, -nc + s, scale, nrm)


-- =====================================  MAIN DEFINITION  ====================================== --

def windowOf (Y : RandOutZono) : RandWindow :=
  -- in the upper half-plane, by angle from `e₁`
  let gs := (Y.gens.map aux_upper).qsort fun g h => 0 < aux_cross g h
  let T := gs.foldl (fun (s : ℤ × ℤ) g => (s.1 + g.1, s.2 + g.2)) (0, 0)
  -- the axes: `Σ |g_i.1|` and `Σ |g_i.2|`
  let s₁ : ℤ := gs.foldl (fun s g => s + g.1.natAbs) (0 : ℕ)
  let s₂ : ℤ := gs.foldl (fun s g => s + g.2.natAbs) (0 : ℕ)
  let axes := aux_pushPair Y.den (aux_pushPair Y.den #[] Y.c (1, 0) s₁) Y.c (0, 1) s₂
  -- each generator's normal, its sum from the prefix `P` of those before it
  let (normals, _) := gs.foldl (fun (acc, P) g =>
    let r : ℤ × ℤ := (T.1 - 2 * P.1 - g.1, T.2 - 2 * P.2 - g.2)
    (aux_pushPair Y.den acc Y.c (-g.2, g.1) (aux_cross g r), (P.1 + g.1, P.2 + g.2)))
    (axes, ((0 : ℤ), (0 : ℤ)))
  let approx := normals.map fun (n₁, n₂, ρ, scale, nrm) =>
    let k := Nat.log2 (scale / Y.den)
    (quotFloat n₁ (2 ^ k) / nrm, quotFloat n₂ (2 ^ k) / nrm, quotFloat ρ scale / nrm)
  { den := Y.den, normals, approx }

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
