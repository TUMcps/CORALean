import CORALean.Examples.Bench.RandVerifyQuotFloat
import CORALean.Examples.Bench.RandVerifyWindow

/-!
# `randverify`: whether a reach set misses an unsafe box, exactly

A window `Y` and a box `S` are disjoint iff `0 ∉ Y ⊕ (-S)`, a convex polygon whose facet normals
are among the window's candidate normals (`RandWindow`); so iff some candidate `n` has
`ρ_Y(n) < min_{s ∈ S} n · s`, the separating-axis theorem in the plane. That comparison is made
in integers, exactly; `Float`s only choose which candidate to try first. The window's signed
distance is the largest `(min_S n·s - ρ_Y(n)) / ‖n‖₂` over the candidates: positive exactly when
the two are separated, and then a lower bound on their Euclidean distance. The set's distance is
the smallest over the windows, with the window attaining it.

The result is `(separated, distance, window)`: `separated` is the exact verdict (every window
separated), `distance` its value as a `Float` (`quotFloat`, sign exact) and `window` the index of
the closest window; `none` if there is no window.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `q · d` as an integer, `d` a multiple of `q.den`. -/
def aux_sepScale (d : ℕ) (q : ℚ) : ℤ := q.num * ((d / q.den : ℕ) : ℤ)

/-- `(separated, distance)` at one candidate normal, exactly; `dS` the box's denominator. -/
def aux_atNormal (den dS : ℕ) (L H : ℤ × ℤ) : ℤ × ℤ × ℤ × ℕ × Float → Bool × Float
  | (n₁, n₂, ρ, scale, nrm) =>
    -- `dS · min_S n · s`, against `dS · ρ_Y(n)`, both over `den`
    let m := n₁ * (if 0 ≤ n₁ then L.1 else H.1) + n₂ * (if 0 ≤ n₂ then L.2 else H.2)
    let gap := m * den - ρ * dS
    -- `gap / (den · dS · ‖n‖₂)`, through the window's scale so that no `Float` overflows
    (0 < gap, quotFloat gap (scale * dS) / nrm)

/-- `(separated, distance)` of one window from the box with bounds `L ≤ s ≤ H` over `dS`, `Lf`
and `Hf` the same as `Float`s. The normal the `Float`s rank first is tried exactly; only if it
does not separate are all the candidates tried, exactly. -/
def aux_windowSep (W : RandWindow) (dS : ℕ) (L H : ℤ × ℤ) (Lf Hf : Float × Float) :
    Bool × Float :=
  let (j, _) := W.approx.zipIdx.foldl (fun (bj, bv) ((n₁, n₂, ρ), j) =>
    let v := n₁ * (if 0 ≤ n₁ then Lf.1 else Hf.1) + n₂ * (if 0 ≤ n₂ then Lf.2 else Hf.2) - ρ
    if v > bv then (j, v) else (bj, bv)) (0, -(1.0 / 0.0))
  match W.normals[j]? with
  | some nj =>
    let (s, v) := aux_atNormal W.den dS L H nj
    if s then (s, v) else
    W.normals.foldl (fun (sep, best) n =>
      let (s, v) := aux_atNormal W.den dS L H n
      (sep || s, if v > best then v else best)) (false, -(1.0 / 0.0))
  | none => (false, -(1.0 / 0.0))


-- =====================================  MAIN DEFINITION  ====================================== --

def separation (ws : List RandWindow) (S : Array (ℚ × ℚ)) : Option (Bool × Float × ℕ) :=
  let b (i : ℕ) : ℚ × ℚ := S.getD i (0, 0)
  let dS := [(b 0).1, (b 0).2, (b 1).1, (b 1).2].foldl (fun d q => Nat.lcm d q.den) 1
  let L := (aux_sepScale dS (b 0).1, aux_sepScale dS (b 1).1)
  let H := (aux_sepScale dS (b 0).2, aux_sepScale dS (b 1).2)
  let Lf := (quotFloat L.1 dS, quotFloat L.2 dS)
  let Hf := (quotFloat H.1 dS, quotFloat H.2 dS)
  -- every window separated, and the closest one
  ws.zipIdx.foldl (fun acc (W, k) =>
    let (s, v) := aux_windowSep W dS L H Lf Hf
    match acc with
    | none => some (s, v, k)
    | some (s', v', k') => some (s && s', if v < v' then (v, k) else (v', k'))) none

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
