module

public import CORALean.NN.Definitions.GraphNetFloat
public import CORALean.NN.Layers.Operations.ProductLine
public import CORALean.NN.Layers.Operations.RelaxationBox
public import CORALean.ContSet.Zonotope.Float.Operations.Materialise
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.NN.Operations.GraphEnvCons
public import CORALean.ContSet.Zonotope.Float.Operations.CenterResidual
public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Interval.Float.Operations.Materialise
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `GraphNet.evaluateGraph`

CORA.cpp's `ZonoNet::forward` on a graph network: one zonotope per output, all generators a prefix
of one list of factors, an interval center's radii as the error box. Per layer, in CORA.cpp's
order: the source through `W` plus `b`, padded with zero generators to the factors so far
(`aux_rows_to`); each residual through its map, its generators on the first ones (`aux_add_rows`);
the activation as "middle and reach" (CORA.cpp's comment), its errors one generator per neuron
(`slots`) or in the error box. The product of the halves takes its slope `[c_b, c_a]` and its
error from `productLine` on the set. The first cut of CORA.cpp's options: slots all or none, no
splits, alpha slopes or source ranges. Sound by `GraphNet.evaluateGraph_encloses`.

## Inputs
* `k` – the output dimension
* `net` – the network after its input
* `X` – the input set

## Output
* the zonotope of the last output
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `Z` with zero generators up to `rows` (CORA.cpp's `aux_rows_to`). -/
@[step_of GraphNet.evaluateGraph]
def GraphNet.step_padRows (Z : Zonotope (Vec 𝕋 n)) (rows : ℕ) : Zonotope (Vec 𝕋 n) where
  h := Z.h + (rows - Z.h)
  c := Z.c
  G := fun j i => if hj : j.1 < Z.h then Z.G ⟨j.1, hj⟩ i else zero
  I_error := Z.I_error

/-- The box `I` without generators: its center, and the error box of its radius. -/
@[step_of GraphNet.evaluateGraph]
def GraphNet.step_errorBox (I : Interval (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) where
  h := 0
  c := I.center
  G := fun j => j.elim0
  I_error := ⟨-I.radiusFrom, I.radiusFrom⟩

/-- `Z₂`'s generators added to the first ones of `Z₁` (CORA.cpp's `aux_add_rows`), the sums
rounded down with their gaps and `Z₂`'s box in the box: `Zonotope.exactPlus` at `Z₂.h` when
`Z₂.h ≤ Z₁.h`, which a graph network's residual always has. -/
@[step_of GraphNet.evaluateGraph]
def GraphNet.step_addRows (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  let G := fun (j : Fin Z₁.h) i =>
    if hj : j.1 < Z₂.h then addDown (Z₁.G j i) (Z₂.G ⟨j.1, hj⟩ i) else Z₁.G j i
  let gap : Mat 𝕋 n Z₁.h := fun i j =>
    if hj : j.1 < Z₂.h then subUp (addUp (Z₁.G j i) (Z₂.G ⟨j.1, hj⟩ i))
      (addDown (Z₁.G j i) (Z₂.G ⟨j.1, hj⟩ i)) else zero
  { h := Z₁.h
    c := fun i => addDown (Z₁.c i) (Z₂.c i)
    G := G
    I_error := ((Z₁.I_error.plus Z₂.I_error).plus (Zonotope.centerResidual Z₁.c Z₂.c)).plus
      (Zonotope.generatorError gap) }

/-- The errors of a layer, the box `I`: a generator per neuron with `slots`, else the error box. -/
@[step_of GraphNet.evaluateGraph]
def GraphNet.step_errors (slots : Bool) (I : Interval (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  if slots then I.zonotope else GraphNet.step_errorBox I

/-- The linear part of layer `L` on the outputs `E`, `rows` the factors so far. -/
@[step_of GraphNet.evaluateGraph]
def GraphNet.step_linear {Γ : List ℕ} {m : ℕ} (L : GraphLayer 𝕋 Γ m)
    (E : GraphEnv 𝒵[𝕋] Γ) (rows : ℕ) : Zonotope (Vec 𝕋 m) :=
  -- 1. the source through W, plus b, padded to the factors so far
  let Z := GraphNet.step_padRows ((Zonotope.mtimes L.W (E L.src)).plus
    (Zonotope.point L.b)).materialise rows
  -- 2. the residuals, on the first factors
  L.residuals.foldl (fun Z r =>
    (GraphNet.step_addRows Z (Zonotope.mtimes r.R (E r.src))).materialise) Z

/-- The slope of the product of the halves at the center `c`: `[diag c_b, diag c_a; 0, 0]`. -/
@[step_of GraphNet.evaluateGraph]
def GraphNet.step_productSlope (c : Vec 𝕋 (n + n)) : Mat 𝕋 (n + n) (n + n) :=
  fun i k => Fin.addCases (fun i' => if k = Fin.castAdd n i' then c (Fin.natAdd n i')
    else if k = Fin.natAdd n i' then c (Fin.castAdd n i') else zero) (fun _ => zero) i

/-- The lines of the product of the halves on `Z` (`productLine` per pair, the box radii `ρ`). -/
@[step_of GraphNet.evaluateGraph]
def GraphNet.step_productLines (p : ℕ) (τ w₂ : 𝕋) (w₁ : ℕ → 𝕋) (Z : Zonotope (Vec 𝕋 (n + n))) :
    Fin n → 𝕋 × 𝕋 :=
  let ρ := fun i => maximum (Z.I_error.sup i) (neg (Z.I_error.inf i))
  fun i => productLine p τ (w₁ Z.h) w₂ (Z.c (Fin.castAdd n i)) (Z.c (Fin.natAdd n i))
    (fun j => Z.G j (Fin.castAdd n i)) (fun j => Z.G j (Fin.natAdd n i)) (ρ (Fin.castAdd n i))
    (ρ (Fin.natAdd n i))

/-- The box `[offset - error, offset + error]` of the first half's lines, `0` on the second. -/
@[step_of GraphNet.evaluateGraph]
def GraphNet.step_productBox (line : Fin n → 𝕋 × 𝕋) : Interval (Vec 𝕋 (n + n)) :=
  ⟨Fin.addCases (fun i => subDown (line i).1 (line i).2) (fun _ => zero),
   Fin.addCases (fun i => addUp (line i).1 (line i).2) (fun _ => zero)⟩

/-- The activation on the layer's input set `Z`. -/
@[step_of GraphNet.evaluateGraph]
def GraphNet.step_activate : {m : ℕ} → GraphAct 𝕋 m → Zonotope (Vec 𝕋 m) → Zonotope (Vec 𝕋 m)
  | _, .identity, Z => Z
  | _, .elementwise R slots, Z =>
    -- the box of the set, the slopes, and the box of the errors
    let I := Z.interval.materialise
    let D := diagonalBlock fun i => R.slope (I.inf i) (I.sup i)
    ((Zonotope.mtimes D Z).plus (GraphNet.step_errors slots (R.box I).materialise)).materialise
  | _, .product _ p τ w₂ w₁ slots, Z =>
    -- the lines from the set itself
    let line := GraphNet.step_productLines p τ w₂ w₁ Z
    let B := (GraphNet.step_productBox line).materialise
    ((Zonotope.mtimes (GraphNet.step_productSlope Z.c) Z).plus
      (GraphNet.step_errors slots B)).materialise

/-- The layers after the outputs `E`, `rows` the factors so far: the last output's zonotope. -/
@[step_of GraphNet.evaluateGraph]
def GraphNet.step_run : {Γ : List ℕ} → {k : ℕ} → GraphNet 𝕋 Γ k →
    GraphEnv 𝒵[𝕋] Γ → ℕ → Zonotope (Vec 𝕋 k)
  | _, _, .done, E, _ => E ⟨0, Nat.succ_pos _⟩
  | _, _, .layer L rest, E, rows =>
    let Z := GraphNet.step_activate L.act (GraphNet.step_linear L E rows)
    rest.step_run (GraphEnv.cons Z E) Z.h


-- =====================================  MAIN DEFINITION  ====================================== --

def GraphNet.evaluateGraph {k : ℕ} (net : GraphNet 𝕋 [n] k) (X : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 k) :=
  net.step_run (GraphEnv.cons X fun i => i.elim0) X.h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
