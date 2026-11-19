module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyGridStep
public import CORALean.ContDynamics.LinearSys.Definitions.VerifyZonoState
public import CORALean.ContDynamics.LinearSys.Operations.VerifyGirardReduceFloat
public import CORALean.ContDynamics.LinearSys.Operations.VerifySpecHoldsFloat
public import CORALean.ContDynamics.LinearSys.Definitions.VerifyInputSolution
public import CORALean.ContDynamics.LinearSys.Operations.VerifyInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpBallFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.VerifyCorrectionInputFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.VerifyCorrectionStateFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.BalanceScalesFloat
public import CORALean.ContSet.Interval.Float.Operations.MagnitudeMat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.CarryMinFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.LyapunovCertificateFloat
public import CORALean.Global.Float.Exp
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `LinearSys.verifyZonotopePassFloat`, one pass of CORA's `priv_verifyRA_zonotope`, made sound

The steps of `priv_reach_adaptive` for `ẋ = Ax + Bu` on a given grid (CORA's tuning, not
checked). CORA's point `expm(AΔt)` becomes a ball (`MatExp.expBallFloat`), `e^{A t_k}` a product
`Φ` with a scaled error `φ`, the carried zonotope gets a scaled error `h`, and the varying input
keeps the remainder CORA drops. A full step's set is CORA's `linComb` with `F ⟨c, G⟩` and `G u_c`
as boxes plus the error ball, mapped by `C`, and each specification is checked on it. The
Gershgorin carry grows like `e^{t μ_S}` (`μ_S` the balanced log norm, large for a non-normal `A`);
with a Lyapunov certificate `(P, L, a)` of `A` the errors are also carried in its weight, by
`e^{μΔt}` per step, and `h`, `φ` are the smaller of the two carries.

## Inputs
* `A` – float system matrix
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `Bm` – float input matrix
* `uc` – float center of the input set
* `GU` – float generators of the input set
* `C` – float output matrix
* `specs` – float safe and unsafe sets in the output space
* `cert` – Lyapunov certificate `(P, L, a)` of `A`, if any
* `grid` – the steps, from CORA's tuning

## Output
* per step, for a step computed in full, its output set and which specifications hold on it (a
  flag `false` is undecided: no certificate, never read as disjoint); none if a step's enclosures
  are not computed, the scales are not positive or a step leaves the weight's range
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   19-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m k p q : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `max(0, maxᵢ xᵢ / sᵢ)`, rounded up: `≥ ‖S⁻¹ x‖_∞` for `x ≥ |y|`. -/
@[step_of LinearSys.verifyZonotopePassFloat]
def LinearSys.step_verifyScaledVecFloat (s x : Vec 𝕋 n) : 𝕋 :=
  maximum zero (maximumOver fun i => divUp (x i) (s i))

/-- The midpoint of a box and the half-width about it. -/
@[step_of LinearSys.verifyZonotopePassFloat]
def LinearSys.step_verifyMidFloat (I : Interval (Vec 𝕋 n)) : Vec 𝕋 n × Vec 𝕋 n :=
  let mid := (Interval.point fun i =>
    addUp (I.inf i) (half (subUp (I.sup i) (I.inf i)))).materialise.sup
  (mid, (Interval.point fun i =>
    maximum (subUp (I.sup i) (mid i)) (subUp (mid i) (I.inf i))).materialise.sup)

/-- The product `M x` as a box, its midpoint and half-width. -/
@[step_of LinearSys.verifyZonotopePassFloat]
def LinearSys.step_verifyMulVecFloat (M : Mat 𝕋 q n) (x : Vec 𝕋 n) : Vec 𝕋 q × Vec 𝕋 q :=
  let P := Interval.matMul (Interval.point M) (Interval.point fun l (_ : Fin 1) => x l)
  LinearSys.step_verifyMidFloat ⟨fun l => P.inf l 0, fun l => P.sup l 0⟩

/-- A zonotope from a box of centers and boxes of generators: the midpoints, then the generators
`P`, the half-widths added to the box `rad`. -/
@[step_of LinearSys.verifyZonotopePassFloat]
def LinearSys.step_verifyZonoOfBoxesFloat (cen : Interval (Vec 𝕋 n))
    (cols : List (Interval (Vec 𝕋 n))) (P : List (Vec 𝕋 n)) (rad : Vec 𝕋 n) :
    LinearSys.VerifyZono 𝕋 n :=
  let cm := LinearSys.step_verifyMidFloat cen
  let gm := cols.map LinearSys.step_verifyMidFloat
  ⟨cm.1, gm.map Prod.fst ++ P, (Interval.point fun l => addUp (addUp (rad l) (cm.2 l))
    (gm.foldl (fun acc x => addUp acc (x.2 l)) zero)).materialise.sup⟩

/-- The image `C T` of a zonotope with a box, as CORA maps it: the center and the generators by
`C`, the box as the generators `C eᵢ rᵢ`; the half-widths of the products form the new box. -/
@[step_of LinearSys.verifyZonotopePassFloat]
def LinearSys.step_verifyZonoMapFloat (C : Mat 𝕋 q n) (T : LinearSys.VerifyZono 𝕋 n) :
    LinearSys.VerifyZono 𝕋 q :=
  let cm := LinearSys.step_verifyMulVecFloat C T.c
  let gm := T.G.map (LinearSys.step_verifyMulVecFloat C)
  let bm := (List.finRange n).map fun i =>                               -- C eᵢ rᵢ
    LinearSys.step_verifyMulVecFloat C fun l => if l = i then T.r i else zero
  ⟨cm.1, (gm ++ bm).map Prod.fst, (Interval.point fun l =>
    addUp (cm.2 l) ((gm ++ bm).foldl (fun acc x => addUp acc (x.2 l)) zero)).materialise.sup⟩

/-- `max 0 (maxⱼ Σₖ |m_jk| s_k / s_j)`, every operation rounded up: `≥ ‖S⁻¹ M S‖`. -/
@[step_of LinearSys.verifyZonotopePassFloat]
def LinearSys.step_verifyScaledNormFloat (s : Vec 𝕋 n) (M : Mat 𝕋 n n) : 𝕋 :=
  maximum zero (maximumOver fun j => sumUp fun k => divUp (mulUp (absolute (M j k)) (s k)) (s j))

/-- The input's boxes at `Δt`: none without an input, else `LinearSys.verifyInputSolutionFloat`,
and the box of `G u₀` (none without a constant input). -/
@[step_of LinearSys.verifyZonotopePassFloat]
def LinearSys.step_verifyZonoInputFloat (A : Mat 𝕋 n n) (s : Vec 𝕋 n) (Δt : 𝕋)
    (u₀ : Interval (Mat 𝕋 n 1)) (MU : Interval (Mat 𝕋 n p)) :
    Option (LinearSys.VerifyInputSolution 𝕋 n p × Interval (Mat 𝕋 n 1)) :=
  let isZero := fun x : 𝕋 => le x zero && le zero x
  let hasU := !(List.finRange n).all fun l => isZero (u₀.inf l 0) && isZero (u₀.sup l 0)
  let hasM := !(List.finRange n).all fun l => (List.finRange p).all fun c =>
    isZero (MU.inf l c) && isZero (MU.sup l c)
  let I := if hasU || hasM then LinearSys.verifyInputSolutionFloat A s Δt u₀ MU
    else some ⟨Interval.point fun _ _ => zero, [], Interval.point fun _ _ => zero, fun _ => zero⟩
  let g := if hasU then (MatExp.verifyCorrectionInputFloat A s Δt).map fun G =>
      (Interval.matMul G.2 u₀).materialiseMat
    else some (Interval.point fun _ _ => zero)
  match I, g with
  | some I, some g => some (I, g)
  | _, _ => none

/-- `|c| + Σⱼ |gⱼ|`, rounded up: the magnitude of the carried zonotope. -/
@[step_of LinearSys.verifyZonotopePassFloat]
def LinearSys.step_verifyZonoMagFloat (st : LinearSys.VerifyZonoState 𝕋 n m) : Vec 𝕋 n :=
  (Interval.point fun l => addUp (absolute (st.c l))
    (sumUp fun j => absolute (st.G l j))).materialise.sup

/-- The zonotope carried to `t_{k+1}`, `⟨D c + w, D G⟩` with its scaled error, and `D Φ` with its
scaled error; the input's parts of the state are kept. -/
@[step_of LinearSys.verifyZonotopePassFloat]
def LinearSys.step_verifyZonoCarryFloat (s : Vec 𝕋 n) (D : Mat 𝕋 n n) (r : 𝕋)
    (w : Interval (Mat 𝕋 n 1)) (st : LinearSys.VerifyZonoState 𝕋 n m) :
    LinearSys.VerifyZonoState 𝕋 n m :=
  let scaled := LinearSys.step_verifyScaledVecFloat s
  let norm := LinearSys.step_verifyScaledNormFloat s
  let nE := addUp (norm D) r                                             -- ≥ ‖e^{AΔt}‖
  let wm := LinearSys.step_verifyMidFloat ⟨fun l => w.inf l 0, fun l => w.sup l 0⟩
  let Dc := Interval.matMul (Interval.point D) (Interval.point fun l (_ : Fin 1) => st.c l)
  let c' := (⟨fun l => addDown (Dc.inf l 0) (wm.1 l), fun l => addUp (Dc.sup l 0) (wm.1 l)⟩ :
    Interval (Vec 𝕋 n)).materialise
  let G' := (Interval.matMul (Interval.point D) (Interval.point st.G)).materialiseMat
  let gap := scaled fun l => addUp (addUp (subUp (c'.sup l) (c'.inf l))
    (sumUp fun j => subUp (G'.sup l j) (G'.inf l j))) (wm.2 l)
  let h' := addUp (addUp (mulUp nE st.h) (mulUp r (scaled (LinearSys.step_verifyZonoMagFloat st))))
    gap                                                                  -- the error at t_{k+1}
  let Φ' := (Interval.matMul (Interval.point D) (Interval.point st.Φ)).materialiseMat
  let φ' := addUp (addUp (mulUp nE st.φ) (mulUp r (norm st.Φ)))
    (norm fun j l => subUp (Φ'.sup j l) (Φ'.inf j l))
  { st with c := c'.sup, G := G'.sup, h := h', Φ := Φ'.sup, φ := φ' }

/-- The local errors of a carried step in the scales: `r ‖S⁻¹ z‖ + gap` of the zonotope and
`r ‖S⁻¹ Φ S‖ + width` of `Φ`, the terms of `step_verifyZonoCarryFloat` that do not carry. -/
@[step_of LinearSys.verifyZonotopePassFloat]
def LinearSys.step_verifyZonoLocalFloat (s : Vec 𝕋 n) (D : Mat 𝕋 n n) (r : 𝕋)
    (w : Interval (Mat 𝕋 n 1)) (st : LinearSys.VerifyZonoState 𝕋 n m) : 𝕋 × 𝕋 :=
  let scaled := LinearSys.step_verifyScaledVecFloat s
  let norm := LinearSys.step_verifyScaledNormFloat s
  let wm := LinearSys.step_verifyMidFloat ⟨fun l => w.inf l 0, fun l => w.sup l 0⟩
  let Dc := Interval.matMul (Interval.point D) (Interval.point fun l (_ : Fin 1) => st.c l)
  let c' := (⟨fun l => addDown (Dc.inf l 0) (wm.1 l), fun l => addUp (Dc.sup l 0) (wm.1 l)⟩ :
    Interval (Vec 𝕋 n)).materialise
  let G' := (Interval.matMul (Interval.point D) (Interval.point st.G)).materialiseMat
  let gap := scaled fun l => addUp (addUp (subUp (c'.sup l) (c'.inf l))
    (sumUp fun j => subUp (G'.sup l j) (G'.inf l j))) (wm.2 l)
  let Φ' := (Interval.matMul (Interval.point D) (Interval.point st.Φ)).materialiseMat
  (addUp (mulUp r (scaled (LinearSys.step_verifyZonoMagFloat st))) gap,       -- the zonotope's
    addUp (mulUp r (norm st.Φ)) (norm fun j l => subUp (Φ'.sup j l) (Φ'.inf j l)))  -- `Φ`'s

/-- The errors carried in the Lyapunov weight `c` of `A` from `st` to `st'` over `Δt`: `β' = e^{μΔt}
β + √b √n max s · loc` (the same for `ψ`), back in the scales by `1/(√a min s)`; `h` and `φ` the
smaller of these and the Gershgorin carry (`Krylov.carryMinFloat`). -/
@[step_of LinearSys.verifyZonotopePassFloat]
def LinearSys.step_verifyZonoWeightFloat (c : Krylov.LyapunovCertificateFloat 𝕋) (s : Vec 𝕋 n)
    (Δt : 𝕋) (loc : 𝕋 × 𝕋) (st st' : LinearSys.VerifyZonoState 𝕋 n m) :
    LinearSys.VerifyZonoState 𝕋 n m :=
  let g := expUp 30 (mulUp c.rate Δt)                                     -- ≥ e^{μΔt}
  let kn := mulUp (mulUp (sqrtUp 30 c.upper) (sqrtUp 30 (nsmulUp n one)))  -- ≥ √b √n max s
    (maximumOver s)
  let back := mulUp (sqrtUp 30 (divUp one c.lower))                       -- ≥ 1/(√a min s)
    (maximumOver fun i => divUp one (s i))
  let β' := addUp (mulUp g st.β) (mulUp kn loc.1)
  let ψ' := addUp (mulUp g st.ψ) (mulUp kn loc.2)
  let hL := Krylov.carryMinFloat st'.h (mulUp β' back)
  let φL := Krylov.carryMinFloat st'.φ (mulUp ψ' back)
  { st' with h := hL, φ := φL, β := β', ψ := ψ' }

/-- The state at `t_{k+1}` with an accepted weight's carry, if any: none if `μΔt` leaves the range
of the exponential. -/
@[step_of LinearSys.verifyZonotopePassFloat]
def LinearSys.step_verifyZonoWeightedFloat (cert : Option (Krylov.LyapunovCertificateFloat 𝕋))
    (s : Vec 𝕋 n) (Δt : 𝕋) (D : Mat 𝕋 n n) (r : 𝕋) (w : Interval (Mat 𝕋 n 1))
    (st st₁ : LinearSys.VerifyZonoState 𝕋 n m) : Option (LinearSys.VerifyZonoState 𝕋 n m) :=
  match cert.filter fun c => c.ok with
  | none => some st₁
  | some c => if le (mulUp c.rate Δt) ((fun x => addDown x x)^[29] one) then
      some (LinearSys.step_verifyZonoWeightFloat c s Δt
        (LinearSys.step_verifyZonoLocalFloat s D r w st) st st₁)
    else none

/-- The orders of the input's solution carried by `Φ`: the first order's columns as generators,
its widths and the later orders' magnitudes as a box. -/
@[step_of LinearSys.verifyZonotopePassFloat]
def LinearSys.step_verifyZonoOrdersFloat (Φ : Mat 𝕋 n n) (V : List (Interval (Mat 𝕋 n p))) :
    List (Vec 𝕋 n) × Vec 𝕋 n :=
  match V.map fun X => (Interval.matMul (Interval.point Φ) X).materialiseMat with
  | [] => ([], fun _ => zero)
  | X :: rest =>
    (List.ofFn fun j : Fin p => (Interval.point fun l => X.sup l j).materialise.sup,
      (Interval.point fun l => addUp (sumUp fun j => subUp (X.sup l j) (X.inf l j))
        (rest.foldl (fun acc X => addUp acc (sumUp fun j => X.magnitudeMat l j)) zero)
        ).materialise.sup)

/-- The varying input over the step carried by `Φ ≈ e^{A t_k}`: the orders, the remainder into
the box, the error `φ βU`; then CORA's reduction. -/
@[step_of LinearSys.verifyZonotopePassFloat]
def LinearSys.step_verifyZonoInputStepFloat (s : Vec 𝕋 n) (I : LinearSys.VerifyInputSolution 𝕋 n p)
    (budget : 𝕋) (st : LinearSys.VerifyZonoState 𝕋 n m) : List (Vec 𝕋 n) × Vec 𝕋 n × 𝕋 :=
  let ord := LinearSys.step_verifyZonoOrdersFloat st.Φ I.V
  let box := (Interval.point fun l => addUp (addUp (st.b l) (ord.2 l))
    (sumUp fun j => mulUp (absolute (st.Φ l j)) (I.ρ j))).materialise.sup  -- the remainder
  let βU := LinearSys.step_verifyScaledVecFloat s fun l => addUp (I.V.foldl (fun acc X =>
    addUp acc (sumUp fun j => X.magnitudeMat l j)) zero) (I.ρ l)        -- ≥ ‖S⁻¹ PU(Δt)‖
  let red := LinearSys.verifyGirardReduceFloat st.P ord.1 box budget
  (red.1, red.2, addUp st.ρ (mulUp st.φ βU))

/-- The time-interval set over `[t_k, t_{k+1}]` in the state space, from the states `st` at `t_k`
and `st'` at `t_{k+1}`: CORA's `linComb` of the two zonotopes, `F ⟨c, G⟩` and `G u₀` as boxes, the
input's generators and box at `t_{k+1}`, and the scaled error `h' + γ h + ρ'`. -/
@[step_of LinearSys.verifyZonotopePassFloat]
def LinearSys.step_verifyZonoIntervalFloat (s : Vec 𝕋 n) (F : Interval (Mat 𝕋 n n))
    (gu : Interval (Mat 𝕋 n 1)) (st st' : LinearSys.VerifyZonoState 𝕋 n m) :
    LinearSys.VerifyZono 𝕋 n :=
  let norm := LinearSys.step_verifyScaledNormFloat s
  let Fc := (Interval.point fun j l =>                                   -- F's center
    addUp (F.inf j l) (half (subUp (F.sup j l) (F.inf j l)))).materialiseMat.sup
  let Fr := (Interval.point fun j l =>                                   -- F's radius about it
    maximum (subUp (F.sup j l) (Fc j l)) (subUp (Fc j l) (F.inf j l))).materialiseMat.sup
  let wc := Interval.matMul (Interval.point Fc) (Interval.point fun l (_ : Fin 1) => st.c l)
  let WG := (Interval.matMul (Interval.point Fc) (Interval.point st.G)).materialiseMat
  let wr := (Interval.point (mulVecUp Fr (LinearSys.step_verifyZonoMagFloat st))).materialise.sup
  let γ := addUp one (norm fun j l => addUp (absolute (Fc j l)) (Fr j l)) -- ≥ ‖(1−λ)I + F_τ‖
  let e := addUp (addUp st'.h (mulUp γ st.h)) st'.ρ                     -- the scaled error
  let cen : Interval (Vec 𝕋 n) :=                                        -- (c + c')/2 + F_c c + G u
    ⟨fun l => addDown (addDown (half (addDown (st.c l) (st'.c l))) (wc.inf l 0)) (gu.inf l 0),
      fun l => addUp (addUp (half (addUp (st.c l) (st'.c l))) (wc.sup l 0)) (gu.sup l 0)⟩
  let cols : List (Interval (Vec 𝕋 n)) :=                                -- CORA's linComb
    List.ofFn (fun j : Fin m => ⟨fun l => half (addDown (st.G l j) (st'.G l j)),
      fun l => half (addUp (st.G l j) (st'.G l j))⟩) ++
    List.ofFn (fun j : Fin m => ⟨fun l => half (subDown (st.G l j) (st'.G l j)),
      fun l => half (subUp (st.G l j) (st'.G l j))⟩) ++
    [⟨fun l => half (subDown (st.c l) (st'.c l)), fun l => half (subUp (st.c l) (st'.c l))⟩]
  let rad := fun l => addUp (addUp (addUp (st'.b l) (sumUp fun j => WG.magnitudeMat l j)) (wr l))
    (mulUp (s l) e)
  LinearSys.step_verifyZonoOfBoxesFloat cen cols st'.P rad

/-- One step: the state at `t_{k+1}`, and for a step computed in full its output set with the
flags of the specifications. -/
@[step_of LinearSys.verifyZonotopePassFloat]
def LinearSys.step_verifyZonoStepFloat (A : Mat 𝕋 n n) (s : Vec 𝕋 n) (u₀ : Interval (Mat 𝕋 n 1))
    (MU : Interval (Mat 𝕋 n p)) (C : Mat 𝕋 q n) (specs : List (LinearSys.VerifySpecSet 𝕋 q))
    (cert : Option (Krylov.LyapunovCertificateFloat 𝕋))
    (st : LinearSys.VerifyZonoState 𝕋 n m) (g : LinearSys.VerifyGridStep 𝕋) :
    Option (Option (LinearSys.VerifyZono 𝕋 q × List Bool) × LinearSys.VerifyZonoState 𝕋 n m) :=
  if !ltStrict zero g.Δt then none else
  match MatExp.expBallFloat A s g.Δt with                               -- e^{AΔt} ∈ D ± r
  | none => none
  | some (D, r) =>
  match LinearSys.step_verifyZonoInputFloat A s g.Δt u₀ MU with         -- the input's boxes
  | none => none
  | some (I, gu) =>
  let inp := LinearSys.step_verifyZonoInputStepFloat s I g.budget st    -- the varying input
  let st₁ := { LinearSys.step_verifyZonoCarryFloat s D r I.w st with
    P := inp.1, b := inp.2.1, ρ := inp.2.2 }
  match LinearSys.step_verifyZonoWeightedFloat cert s g.Δt D r I.w st st₁ with  -- the weight
  | none => none
  | some st' =>
  if !g.full then some (none, st') else
  match MatExp.verifyCorrectionStateFloat A s g.Δt with                 -- F
  | none => none
  | some (_, F) =>
  let Y := LinearSys.step_verifyZonoMapFloat C                           -- in the output space
    (LinearSys.step_verifyZonoIntervalFloat s F gu st st')
  some (some (Y, specs.map (LinearSys.verifySpecHoldsFloat Y)), st')

/-- The steps of the grid in order, the outputs so far in `acc` (latest first). -/
@[step_of LinearSys.verifyZonotopePassFloat]
def LinearSys.step_verifyZonoStepsFloat (A : Mat 𝕋 n n) (s : Vec 𝕋 n)
    (u₀ : Interval (Mat 𝕋 n 1)) (MU : Interval (Mat 𝕋 n p)) (C : Mat 𝕋 q n)
    (specs : List (LinearSys.VerifySpecSet 𝕋 q))
    (cert : Option (Krylov.LyapunovCertificateFloat 𝕋)) :
    LinearSys.VerifyZonoState 𝕋 n m → List (LinearSys.VerifyGridStep 𝕋) →
      List (Option (LinearSys.VerifyZono 𝕋 q × List Bool)) →
      Option (List (Option (LinearSys.VerifyZono 𝕋 q × List Bool)))
  | _, [], acc => some acc.reverse
  | st, g :: gs, acc =>
    match LinearSys.step_verifyZonoStepFloat A s u₀ MU C specs cert st g with
    | none => none
    | some (o, st') => LinearSys.step_verifyZonoStepsFloat A s u₀ MU C specs cert st' gs (o :: acc)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The pass: the scales, the input boxes `[B u_c]` and `[B G_U]`, then the steps of the grid from
`⟨c, G⟩` at `t = 0` with `Φ = I`. -/
def LinearSys.verifyZonotopePassFloat (A : Mat 𝕋 n n) (c : Vec 𝕋 n) (G : Mat 𝕋 n m)
    (Bm : Mat 𝕋 n k) (uc : Vec 𝕋 k) (GU : Mat 𝕋 k p) (C : Mat 𝕋 q n)
    (specs : List (LinearSys.VerifySpecSet 𝕋 q)) (cert : Option (Mat 𝕋 n n × Mat 𝕋 n n × 𝕋))
    (grid : List (LinearSys.VerifyGridStep 𝕋)) :
    Option (List (Option (LinearSys.VerifyZono 𝕋 q × List Bool))) :=
  let s := MatExp.balanceScalesFloat A                                   -- the scales
  let wt := cert.map fun (P, L, a) => Krylov.lyapunovCertificateFloat A P L a  -- `A`'s weight
  let u₀ : Interval (Mat 𝕋 n 1) :=                                       -- [B u_c]
    (⟨matMulDown Bm fun j _ => uc j, matMulUp Bm fun j _ => uc j⟩ : Interval _).materialiseMat
  let MU : Interval (Mat 𝕋 n p) := (⟨matMulDown Bm GU, matMulUp Bm GU⟩ : Interval _).materialiseMat
  if !(List.finRange n).all fun i => ltStrict zero (s i) then none else
  LinearSys.step_verifyZonoStepsFloat A s u₀ MU C specs wt
    ⟨c, G, zero, fun i j => if i = j then one else zero, zero, [], fun _ => zero, zero, zero,
      zero⟩ grid []

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
