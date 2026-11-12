module

public import CORALean.Global.Float.SinCos
public import CORALean.Global.Float.InverseTrig
public import CORALean.Global.Float.Sqrt
public import CORALean.Global.Float.IntRound
public import CORALean.Global.Float.RatUp
public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs

@[expose] public section

/-!
# The Docking polytope in floats

`dockingPolytopeFloat` is `dockingPolytope` with rounded coefficients, built as CORA.cpp's
`aux_docking_polytope` of the benchmark `benchmark_neur_net_contr_reach_arch26_ainncs_b` (at the
round-to-nearest scalar it is bit for bit that function) with every rounding in the safe
direction. It adds the widths of the enclosures to the shrink, certifies `N > 0`, `c > 0`,
`n ≥ 0` and otherwise returns the empty row `0 ≤ -1`. The evaluation order is written step by
step in `experiments/oracle/README.md`; the proof that the set is in the safe set is in
`DockingPolytopeFloatSubsetSafe`.

## Inputs
* `p` – tuning of the sine, cosine and square root enclosures
* `k` – tuning of the arctangent enclosure
* `N` – number of sides
* `n` – mean motion

## Output
* the polytope in `(sx, sy, vx, vy)`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]

namespace Docking

/-- `π` from below, as `4 arctan 1`: two doublings. -/
def piDown (p k : ℕ) : 𝕋 :=
  let a : 𝕋 := atanDown p k one
  addDown (addDown a a) (addDown a a)

/-- `π` from above, as `4 arctan 1`. -/
def piUp (p k : ℕ) : 𝕋 :=
  let a : 𝕋 := atanUp p k one
  addUp (addUp a a) (addUp a a)

/-- The angle `2π j / N` from above, as `2 * pi * k / sides`: the angle row `j` uses. -/
def angleUp (pU : 𝕋) (N j : ℕ) : 𝕋 :=
  divUp (mulUp (addUp pU pU) (intUp j)) (intDown N)

/-- The angle `2π j / N` from below. -/
def angleDown (pD : 𝕋) (N j : ℕ) : 𝕋 :=
  divDown (mulDown (maximum zero (addDown pD pD)) (maximum zero (intDown j))) (intUp N)

/-- The angle `π / N` from above, as `pi / sides`. -/
def halfUp (pU : 𝕋) (N : ℕ) : 𝕋 := divUp pU (intDown N)

/-- The angle `π / N` from below. -/
def halfDown (pD : 𝕋) (N : ℕ) : 𝕋 := divDown pD (intUp N)

/-- `1 - 10⁻⁹` in `[0, 1]`, as `shrink = 1.0 - 1e-9`. -/
def shrink : 𝕋 := maximum zero (minimum one (subDown one (ratUp (1 / 1000000000))))

/-- The error of the cosine coefficient of row `j`: the width of `cos` at the angle plus the
width of the angle. -/
def cosErr (p : ℕ) (pD pU : 𝕋) (N j : ℕ) : 𝕋 :=
  addUp (subUp (cosUp p (angleUp pU N j)) (cosDown p (angleUp pU N j)))
    (subUp (angleUp pU N j) (angleDown pD N j))

/-- The error of the sine coefficient of row `j`. -/
def sinErr (p : ℕ) (pD pU : 𝕋) (N j : ℕ) : 𝕋 :=
  addUp (subUp (sinUp p (angleUp pU N j)) (sinDown p (angleUp pU N j)))
    (subUp (angleUp pU N j) (angleDown pD N j))

/-- The largest coefficient error over the rows, at least `0`. -/
def maxErr (p : ℕ) (pD pU : 𝕋) (N : ℕ) : 𝕋 :=
  maximum zero (maximumOver fun j : Fin N => maximum (cosErr p pD pU N j) (sinErr p pD pU N j))

/-- A lower bound of `cos(π/N) - √2 · maxErr`, as `cos(pi / sides)`. -/
def cosHalf (p : ℕ) (pD pU : 𝕋) (N : ℕ) : 𝕋 :=
  let e := maxErr p pD pU N
  subDown (cosDown p (halfUp pU N)) (addUp (subUp (halfUp pU N) (halfDown pD N)) (addUp e e))

/-- The radius factor `c`, as `std::cos(pi / sides) * shrink`. -/
def radius (p : ℕ) (pD pU : 𝕋) (N : ℕ) : 𝕋 := mulDown (cosHalf p pD pU N) shrink

/-- The weight `w` of `sx + sy`, as `c * 2 * n / std::sqrt(2.0) * shrink`, never negative. -/
def slope (p : ℕ) (c n : 𝕋) : 𝕋 :=
  let m1 := mulDown c (addDown one one)                     -- c * 2
  let m2 := mulDown m1 n                                    -- c * 2 * n
  let m3 := divDown m2 (sqrtUp p (addUp one one))           -- / sqrt 2
  maximum zero (mulDown m3 shrink)

/-- The right-hand side `0.2 c`, rounded down. -/
def rhs (c : 𝕋) : 𝕋 :=
  let two : 𝕋 := addUp one one
  mulDown (divDown one (addUp (addUp two two) one)) c

/-- The facts the proof rests on, tested by the scalar: `N > 0`, `c > 0`, `n ≥ 0`. -/
def certified (N : ℕ) (c n : 𝕋) : Bool :=
  ltStrict (zero : 𝕋) (intDown N) && ltStrict (zero : 𝕋) c && le (zero : 𝕋) n

end Docking


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Docking polytope: rows `(-w, -w, cos φⱼ, sin φⱼ) ≤ 0.2 c`, or the empty row if the
tests fail. -/
def dockingPolytopeFloat (p k N : ℕ) (n : 𝕋) : HPolytope 𝕋 (Vec 𝕋 4) :=
  let pD := Docking.piDown p k
  let pU := Docking.piUp p k
  let c := Docking.radius p pD pU N
  let w := Docking.slope p c n
  let β := Docking.rhs c
  if Docking.certified N c n then
    HPolytope.ineqs
      (fun j : Fin N => ![neg w, neg w, cosDown p (Docking.angleUp pU N j),
        sinDown p (Docking.angleUp pU N j)]) (fun _ => β)
  else HPolytope.ineqs (fun (_ : Fin 1) _ => zero) (fun _ => neg one)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
