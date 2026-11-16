module

public import CORALean.ContSet.PolyZonotope.Real.Definitions.PowerRow
public import CORALean.ContSet.PolyZonotope.Real.Operations.Basic
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `PolyZonotope.evalPowersList`

CORA's `evaluatePolyZonotopeNeuron` after the fit, `p(x) = Σ aᵢ xⁱ` on a row `c + G + GI`, step
for step as CORA.cpp's `priv_eval_poly` computes it, in any `PowerOps`. The power `xⁱ` is the
product of `x^(i/2)` and `x^((i+1)/2)` and keeps their generators (`PolyZonotope.powerExt`). A
square of an independent generator `g β` is `g²/2 + (g²/2) β'`, its half shifting the center. The
cross term of a dependent and an independent generator is the full product, twice in a square:
CORA halves it where the exponents are all even, which is unsound (`x = a² + b`, CORA.cpp's
`docs/cora-differences.md`). The powers are weighted by their coefficients, and the generators a
power took from its factors are added back into the factors', from the highest power down.

## Inputs
* `o` – arithmetic
* `as` – coefficients, lowest degree first
* `x` – row

## Output
* the row of `p(x)`: center, own generators of the powers `1, …, k`, `k = max 1 (|as| - 1)`
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- A power times itself (CORA's `calcSquared` of equal factors): the squares of the independent
generators halved, their halves added to the center. -/
@[step_of PolyZonotope.evalPowersList]
def PolyZonotope.step_square (o : PowerOps α) (x : PowerRow α) : PowerRow α :=
  let sq := x.GI.map fun g => o.mul (o.mul g g) o.half
  { c := sq.foldl o.add (o.mul x.c x.c)
    G := x.G.map (o.mul x.c) ++ x.G.map (o.mul x.c) ++ x.G.map (fun g => o.mul g g)
      ++ PolyZonotope.pairsWith (fun a b => o.mul (o.mul o.two a) b) x.G
    GI := x.GI.map (o.mul x.c) ++ x.GI.map (o.mul x.c) ++ sq
      ++ PolyZonotope.pairsWith (fun a b => o.mul (o.mul o.two a) b) x.GI
      ++ (PolyZonotope.crossWith o.mul x.GI x.G).map (o.mul o.two) }

/-- The product of two different powers (CORA's `calcSquared`): every product, the dependent
with the independent generators in both orders. -/
@[step_of PolyZonotope.evalPowersList]
def PolyZonotope.step_times (o : PowerOps α) (x y : PowerRow α) : PowerRow α :=
  { c := o.mul x.c y.c
    G := x.G.map (o.mul y.c) ++ y.G.map (o.mul x.c) ++ PolyZonotope.crossWith o.mul x.G y.G
    GI := x.GI.map (o.mul y.c) ++ y.GI.map (o.mul x.c) ++ PolyZonotope.crossWith o.mul x.GI y.GI
      ++ PolyZonotope.crossWith o.mul x.G y.GI ++ PolyZonotope.crossWith o.mul x.GI y.G }

/-- The power `i` of the row with the generators of its factors, `x` itself below `2`. -/
@[step_of PolyZonotope.evalPowersList]
def PolyZonotope.step_power (o : PowerOps α) (x : PowerRow α) (i : ℕ) : PowerRow α :=
  if i < 2 then x else
    if i % 2 = 0 then PolyZonotope.step_square o (PolyZonotope.step_power o x (i / 2))
    else PolyZonotope.step_times o (PolyZonotope.step_power o x (i / 2))
      (PolyZonotope.step_power o x ((i + 1) / 2))
termination_by i
decreasing_by all_goals omega

/-- A power times its coefficient, every entry on the left. -/
@[step_of PolyZonotope.evalPowersList]
def PolyZonotope.step_weigh (o : PowerOps α) (a : α) (x : PowerRow α) : PowerRow α :=
  ⟨o.mul x.c a, x.G.map (o.mul · a), x.GI.map (o.mul · a)⟩

/-- The power `i`'s generators taken from its factors added to the factors' own: the first
`len (i/2)` to the power `i/2`, the next `len ((i+1)/2)` to the power `(i+1)/2`. -/
@[step_of PolyZonotope.evalPowersList]
def PolyZonotope.step_foldAt (o : PowerOps α) (len : ℕ → ℕ) (W : ℕ → List α) (i : ℕ) :
    ℕ → List α :=
  let P1 := (W i).take (len (i / 2))
  let P2 := ((W i).drop (len (i / 2))).take (len ((i + 1) / 2))
  let W1 := Function.update W (i / 2) (List.zipWith o.add (W (i / 2)) P1)
  Function.update W1 ((i + 1) / 2) (List.zipWith o.add (W1 ((i + 1) / 2)) P2)

/-- `step_foldAt` at the powers `k, k-1, …, 2`. -/
@[step_of PolyZonotope.evalPowersList]
def PolyZonotope.step_foldDown (o : PowerOps α) (len : ℕ → ℕ) :
    (ℕ → List α) → ℕ → (ℕ → List α)
  | W, 0 => W
  | W, 1 => W
  | W, k + 2 => PolyZonotope.step_foldDown o len (PolyZonotope.step_foldAt o len W (k + 2)) (k + 1)


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.evalPowersList (o : PowerOps α) (as : List α) (x : PowerRow α) : PowerRow α :=
  let k := max 1 (as.length - 1)
  -- 1. the powers, each with the generators of its factors
  let X := PolyZonotope.step_power o x
  -- 2. each times its coefficient
  let W := fun i => PolyZonotope.step_weigh o (as.getD i o.zero) (X i)
  -- 3. the generators of the factors added back, from the highest power down
  let lenG := fun i => (X i).G.length
  let lenGI := fun i => (X i).GI.length
  -- 4. the centers summed, from the first power up, then the constant
  { c := o.add ((List.range' 1 k).foldl (fun acc i => o.add acc (W i).c) o.zero)
      (as.getD 0 o.zero)
    G := PolyZonotope.powerParts lenG (PolyZonotope.step_foldDown o lenG (fun i => (W i).G) k) k
    GI := PolyZonotope.powerParts lenGI
      (PolyZonotope.step_foldDown o lenGI (fun i => (W i).GI) k) k }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
