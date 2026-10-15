import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.ContDynamics.LinearSys.Operations.OfABc
import CORALean.ContSet.Interval.Float.Operations.Basic
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.HybridDynamics.Theorems.ReachFloatOuter
import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

/-!
# A bouncing ball, reached in floats

`BouncingBall`'s automaton at `Dyadic 24`, with CORA's parameters as near as a
dyadic gets: gravity `9.8125`, the velocity damped by `0.75` at each bounce,
the ball released from `1 ± 1/16` at rest `± 1/16`. The invariant is the
halfspace `p ≥ 0` and the guard `p = 0 ∧ v ≤ 0`, both float halfspace
descriptions; the state is a float zonotope.

`HybridAutomaton.reachFloat` runs to two bounces with stays of up to one
second, in steps of `1/32`. `reachFloat_outer` at this automaton says every run
of at most one second and two bounces ends in a computed set; the `#eval`s
below show what was computed: how many sets, the box they all lie in, and the
velocity the first stay meets the floor with, `-√(2 g p₀)` for `p₀` near `1`,
about `-4.4`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.BouncingBallFloat

open CORALean CORALean.Float ContSet

abbrev D := Dyadic 24

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

/-- The floor met from above: `v ≤ 0` as an inequality row, `p = 0` as an equality row. -/
def floorGuard : HPolytope D (Vec D 2) where
  m := 1
  A := ![![d 0 0, d 1 0]]
  b := ![d 0 0]
  me := 1
  Ae := ![![d 1 0, d 0 0]]
  be := ⟨![d 0 0], ![d 0 0]⟩

/-- Above the floor, `-p ≤ 0`. -/
def aboveFloor : HPolytope D (Vec D 2) where
  m := 1
  A := ![![d (-1) 0, d 0 0]]
  b := ![d 0 0]
  me := 0
  Ae := ![]
  be := ⟨![], ![]⟩

/-- The bounce: keep the position, reverse the velocity and damp it by `3/4`. -/
def bounce : Transition (fun k => HPolytope D (Vec D k)) Unit D 2 where
  guard := floorGuard
  W := !![d 1 0, d 0 0; d 0 0, d (-3) (-2)]
  w := ![d 0 0, d 0 0]
  target := ()

/-- The point `0` of one coordinate. -/
def zero1 : Zonotope (Vec D 1) := ⟨0, ![d 0 0], fun j => j.elim0, ⟨![d 0 0], ![d 0 0]⟩⟩

/-- CORA's `linearSys(A, B, c)`: `ṗ = v`, `v̇ = -g`, the gravity the offset `c = (0, -g)`, no
input (`B = 0`, `U = {0}`), no disturbance. -/
def ball : HybridAutomaton 𝒵[D] (fun k => HPolytope D (Vec D k))
    Unit D 2 where
  loc _ :=
    { inv := aboveFloor
      dynamics := LinearSys.ofABc !![d 0 0, d 1 0; d 0 0, d 0 0] (fun _ _ => d 0 0)
        ![d 0 0, d (-157) (-4)]
      U := zero1
      W := zero1
      trans := [bounce] }

/-- `(1, 0) ± 1/16` in each coordinate. -/
def R0 : Zonotope (Vec D 2) where
  h := 2
  c := ![d 1 0, d 0 0]
  G := !![d 1 (-4), d 0 0; d 0 0, d 1 (-4)]
  I_error := ⟨![d 0 0, d 0 0], ![d 0 0, d 0 0]⟩

/-- Steps of `1/32`, four Taylor terms, zonotope order `10`. -/
def options : LinearSys.ReachOptions D := ⟨d 1 (-5), 4, 10⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Two bounces, stays of up to one second each. -/
def ballReach : Option (List (Unit × Zonotope (Vec D 2))) := ball.reachFloat 1 options 2 () R0

/-- Every run of the ball from `R0` lasting at most one second, with at most two
bounces, ends in a set `ballReach` computed. -/
example {T : ℝ} {k : ℕ} {x y : Vec ℝ 2} (run : ball.RunUntil T k () x () y) (hT : T ≤ 1)
    (hk : k ≤ 2) (hx : x ∈ construct R0) {out : List (Unit × Zonotope (Vec D 2))}
    (h : ballReach = some out) : ∃ p ∈ out, y ∈ construct p.2 := by
  obtain ⟨p, hp, -, hy⟩ := ball.reachFloat_outer run (by exact_mod_cast hT) hk hx h
  exact ⟨p, hp, hy⟩

/-- The box every computed set lies in. -/
def ballHull : Option (Interval (Vec D 2)) :=
  ballReach.bind fun out => match out.map (·.2.interval) with
    | [] => none
    | I :: Is => some (Is.foldl Interval.or I)

/-- The first stay's sets cut to the floor: the state the first bounce resets. -/
def firstImpact : Option (Interval (Vec D 2)) :=
  ((ball.loc ()).reachFloat 1 options R0).bind fun Rs =>
    (ball.loc ()).guardIntersectFloat floorGuard Rs

/-- `[p_min, p_max, v_min, v_max]`, read exactly as rationals. -/
def bounds (I : Interval (Vec D 2)) : List ℚ :=
  [I.inf 0, I.sup 0, I.inf 1, I.sup 1].map ToRat.toRat

-- One `#eval` for both: a second one would run the whole reachability again.
#eval (ballReach.map List.length, ballHull.map bounds)
#eval firstImpact.map bounds

end CORALean.BouncingBallFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
