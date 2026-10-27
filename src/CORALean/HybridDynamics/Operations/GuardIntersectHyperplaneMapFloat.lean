module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
public import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplaneIntervalFloat
public import CORALean.ContSet.Conversion.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Operations.HalfspaceRange
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Operations.QuadMapMatZono
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirard
public import CORALean.Global.Float.Sqrt
public import CORALean.HybridDynamics.Operations.InputSetFloat
public import CORALean.HybridDynamics.Operations.AbstractionErrorFloat
public import CORALean.HybridDynamics.Operations.HitHessianMatZonoFloat
public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.Recip
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InvFactorialBoundsFloat
public import CORALean.ContSet.Interval.Float.Operations.MatPow
public import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.ContSet.Interval.Float.Operations.SumTermsMat
public import CORALean.Global.Float.PowDown
public import CORALean.Global.Float.PowUp
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Location.guardIntersectHyperplaneMapFloat`, the guard mapping at floats

`Location.guardIntersectHyperplaneMap`, CORA's `guardIntersect_hyperplaneMap` [1], at float
zonotopes, one `let` per line: `k ⊕ L(R₀ ⊖ ξ) ⊕ ½[φ̲, φ̄] R_quad ⊕ I (AR₀ ⊕ b) ⊕ E` of [2, Sec.
5.4]. What rounds is an interval, and what an interval cannot stand in for is charged to a set (`b`
is the lower end of `GuardMap.step_sdcInputFloat`, the rest added to the error). `none` when a float
test fails: `Λ`, `nᵀ(Ax + b)`, `Λ²` or `‖n‖` not certified away from `0`, the float `‖tmax A‖` above
`(η + 2)/2`, or `k`, `L` not computed.

## Inputs
* `ℓ` – location
* `nv` – guard normal
* `d` – guard offset
* `R₀` – initial zonotope
* `tmax` – final time
* `η` – Taylor order
* `guardOrder` – order of the guard mapping
* `zonotopeOrder` – order of the result
* `p` – precision of the square roots

## Output
* float zonotope on the guard, none if a test fails

## References

* [1] `hybridDynamics/@location/guardIntersect_hyperplaneMap.m`
* [2] [M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control,
      2012.](../../../../references/2012/althoff-hscc-avoiding-intersection.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {G : ℕ → Type}
  [∀ n, ContSet (G n) (Vec ℝ n)] {L : Type} {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

section
variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- [1, Prop. 1]: a box holding `b = Θ(t)x₀ + Γ*(t)u_c`. -/
@[step_of Location.guardIntersectHyperplaneMapFloat]
def GuardMap.step_sdcInputFloat (A : Mat 𝕋 n n) (uc : Vec 𝕋 n) (t : 𝕋) (η : ℕ) (x₀ : Vec 𝕋 n) :
    Interval (Vec 𝕋 n) :=
  let Apow : ℕ → Interval (Mat 𝕋 n n) := fun i =>                -- `Aⁱ`, bracketed
    Interval.matPow (Interval.point A) i
  let coefLo : ℕ → ℕ → 𝕋 := fun p q =>                           -- `tᵖ/q!`, down
    Interval.mulLo (powDown t p) (powUp t p) (MatExp.invFactorialBounds q).inf
      (MatExp.invFactorialBounds q).sup
  let coefHi : ℕ → ℕ → 𝕋 := fun p q =>                           -- and up
    Interval.mulHi (powDown t p) (powUp t p) (MatExp.invFactorialBounds q).inf
      (MatExp.invFactorialBounds q).sup
  let Θ := Interval.sumTermsMat (fun k =>                         -- `Θ = ∑ᵢ₌₂^η tⁱ⁻¹/i! Aⁱ`
    Interval.smul (coefLo (k + 1) (k + 2)) (coefHi (k + 1) (k + 2)) (Apow (k + 2))) (η - 1)
  let Γstar := Interval.sumTermsMat (fun k =>                     -- `Γ* = ∑ᵢ₌₀^η tⁱ/(i+1)! Aⁱ`
    Interval.smul (coefLo k (k + 1)) (coefHi k (k + 1)) (Apow k)) (η + 1)
  (Interval.mtimesIntervalMat Θ (Interval.point x₀)).plus        -- `Θx₀ + Γ*u_c`
    (Interval.mtimesIntervalMat Γstar (Interval.point uc))

end


section
variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- A box holding `y_h(x₀) = x₀ + (Ax₀ + b)(d − nᵀx₀)/Λ`, `none` if `0` may be in `Λ`'s box. -/
@[step_of Location.guardIntersectHyperplaneMapFloat]
def GuardMap.step_hitPointFloat (A : Mat 𝕋 n n) (b nv : Vec 𝕋 n) (d : 𝕋) (x₀ : Vec 𝕋 n) :
    Option (Interval (Vec 𝕋 n)) :=
  let y : Interval (Vec 𝕋 n) :=                                       -- `Ax₀ + b`
    ⟨fun i => addDown (dotDown (A i) x₀) (b i), fun i => addUp (dotUp (A i) x₀) (b i)⟩
  let ΛLo := sumDown fun i => Interval.mulLo (nv i) (nv i) (y.inf i) (y.sup i)  -- `Λ = nᵀy`
  let ΛHi := sumUp fun i => Interval.mulHi (nv i) (nv i) (y.inf i) (y.sup i)
  let Λinv := Interval.recip (⟨fun _ => ΛLo, fun _ => ΛHi⟩ : Interval (Vec 𝕋 1))  -- `1/Λ`
  let numLo := subDown d (dotUp nv x₀)                                 -- `d − nᵀx₀`
  let numHi := subUp d (dotDown nv x₀)
  let τLo := Interval.mulLo numLo numHi (Λinv.inf 0) (Λinv.sup 0)     -- `(d − nᵀx₀)/Λ`
  let τHi := Interval.mulHi numLo numHi (Λinv.inf 0) (Λinv.sup 0)
  if ltStrict zero ΛLo || ltStrict ΛHi zero then                       -- `Λ ≠ 0`, certified
    some ⟨fun i => addDown (x₀ i) (Interval.mulLo τLo τHi (y.inf i) (y.sup i)),
      fun i => addUp (x₀ i) (Interval.mulHi τLo τHi (y.inf i) (y.sup i))⟩
  else none

end


section
variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- [1, Prop. 2]: an interval matrix holding `L(x₀)`, `none` if `0` may be in `Λ`'s box. -/
@[step_of Location.guardIntersectHyperplaneMapFloat]
def GuardMap.step_hitJacobianFloat (A : Mat 𝕋 n n) (b nv : Vec 𝕋 n) (d : 𝕋) (x₀ : Vec 𝕋 n) :
    Option (Interval (Mat 𝕋 n n)) :=
  let y : Interval (Vec 𝕋 n) :=                                       -- `Ax₀ + b`
    ⟨fun i => addDown (dotDown (A i) x₀) (b i), fun i => addUp (dotUp (A i) x₀) (b i)⟩
  let ΛLo := sumDown fun i => Interval.mulLo (nv i) (nv i) (y.inf i) (y.sup i)  -- `Λ = nᵀy`
  let ΛHi := sumUp fun i => Interval.mulHi (nv i) (nv i) (y.inf i) (y.sup i)
  let Λinv := Interval.recip (⟨fun _ => ΛLo, fun _ => ΛHi⟩ : Interval (Vec 𝕋 1))  -- `1/Λ`
  let Λinv2Lo := Interval.mulLo (Λinv.inf 0) (Λinv.sup 0) (Λinv.inf 0) (Λinv.sup 0)  -- `1/Λ²`
  let Λinv2Hi := Interval.mulHi (Λinv.inf 0) (Λinv.sup 0) (Λinv.inf 0) (Λinv.sup 0)
  let numLo := subDown d (dotUp nv x₀)                                 -- `d − nᵀx₀`
  let numHi := subUp d (dotDown nv x₀)
  let τLo := Interval.mulLo numLo numHi (Λinv.inf 0) (Λinv.sup 0)     -- `(d − nᵀx₀)/Λ`
  let τHi := Interval.mulHi numLo numHi (Λinv.inf 0) (Λinv.sup 0)
  let ΥLo : Vec 𝕋 n := fun l => dotDown nv fun j => A j l             -- `Υ = nᵀA`
  let ΥHi : Vec 𝕋 n := fun l => dotUp nv fun j => A j l
  let ΘLo : Vec 𝕋 n := fun l =>                                       -- `Θ = −nΛ − (d − nᵀx₀)Υ`
    subDown (neg (Interval.mulHi ΛLo ΛHi (nv l) (nv l)))
      (Interval.mulHi numLo numHi (ΥLo l) (ΥHi l))
  let ΘHi : Vec 𝕋 n := fun l =>
    subUp (neg (Interval.mulLo ΛLo ΛHi (nv l) (nv l)))
      (Interval.mulLo numLo numHi (ΥLo l) (ΥHi l))
  let yΘLo : Mat 𝕋 n n := fun i l => Interval.mulLo (y.inf i) (y.sup i) (ΘLo l) (ΘHi l)  -- `yᵢΘ_l`
  let yΘHi : Mat 𝕋 n n := fun i l => Interval.mulHi (y.inf i) (y.sup i) (ΘLo l) (ΘHi l)
  if ltStrict zero ΛLo || ltStrict ΛHi zero then                       -- `Λ ≠ 0`, certified
    some ⟨fun i l => addDown (addDown (if i = l then one else zero)  -- `I + Aτ + yΘ/Λ²`
        (Interval.mulLo (A i l) (A i l) τLo τHi))
        (Interval.mulLo (yΘLo i l) (yΘHi i l) Λinv2Lo Λinv2Hi),
      fun i l => addUp (addUp (if i = l then one else zero)
        (Interval.mulHi (A i l) (A i l) τLo τHi))
        (Interval.mulHi (yΘLo i l) (yΘHi i l) Λinv2Lo Λinv2Hi)⟩
  else none

end


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `R = guardIntersect_hyperplaneMap(loc,guard,R0,params,options)` at floats, at the refined
`R₀` and `tmax`, `η = options.η`, `p` the precision of the square root of `nᵀn`. -/
def Location.guardIntersectHyperplaneMapFloat (ℓ : Location 𝒵[𝕋] G L 𝕋 n)
    (nv : Vec 𝕋 n)
    (d : 𝕋) (R₀ : Zonotope (Vec 𝕋 n)) (tmax : 𝕋) (η guardOrder zonotopeOrder p : ℕ) :
    Option (Zonotope (Vec 𝕋 n)) :=
  -- `[a, b] * Z` of a float interval and a zonotope, as the interval matrix `[a, b] I`
  let mulI : 𝕋 → 𝕋 → Interval (Mat 𝕋 n n) := fun a b =>
    Interval.smul a b (Interval.point (diagonalBlock fun _ => one))
  -- `1/[lo, hi]`, for an interval certified to exclude `0`
  let recipI : 𝕋 → 𝕋 → Interval (Vec 𝕋 1) := fun lo hi => Interval.recip ⟨fun _ => lo, fun _ => hi⟩
  let A : Mat 𝕋 n n := ℓ.dynamics.A                                -- [A,U] = aux_systemParams
  let U : Zonotope (Vec 𝕋 n) := ℓ.inputSetFloat                    -- U = B*U + c, and E*W
  let th : 𝕋 := half tmax                                           -- th = tmax/2
  let bI := GuardMap.step_sdcInputFloat A U.c th η R₀.c                  -- b = aux_constantFlow
  let b : Vec 𝕋 n := bI.inf                                         -- its lower end
  let R0red := R₀.reduceGirard guardOrder                           -- R0red = reduce(R0,..)
  let R0red_ := R0red.recenter                                      -- R0red_ = R0red - c
  let R0_ := R₀.recenter                                            -- R0_ = R0 - center(R0)
  let err := (GuardMap.abstractionErrorFloat A U R0red th tmax η).plus  -- aux_abstractionError
    (⟨fun i => Interval.mulLo zero tmax zero (subUp (bI.sup i) (b i)),  -- + [0, tmax](b - b_lo)
      fun i => Interval.mulHi zero tmax zero (subUp (bI.sup i) (b i))⟩ :
        Interval (Vec 𝕋 n)).zonotope |>.materialise
  -- `aux_taylorSeriesParam(guard,A,b,R0red)`
  let x0 := R0red.c                                                 -- x0 = center(R0)
  let R0hull := R0red_.plus (Zonotope.point x0)                     -- R0red and x0
  let flowRed := (Zonotope.mtimes A R0hull).plus (Zonotope.point b) -- A*R0 + b
  let Λint := flowRed.halfspaceRange nv zero                        -- Lambda_int
  let dint := R0hull.halfspaceRange nv d                            -- interval(n'*R0 - d)
  let Λinv := recipI Λint.inf Λint.sup                                  -- 1/Lambda_int
  let τlo := Interval.mulLo (neg dint.sup) (neg dint.inf) (Λinv.inf 0) (Λinv.sup 0)  -- tau
  let τhi := Interval.mulHi (neg dint.sup) (neg dint.inf) (Λinv.inf 0) (Λinv.sup 0)
  let τc := half (addUp τlo τhi)                                    -- its center
  let τg := maximum (subUp τhi τc) (subUp τc τlo)                   -- and radius
  let Λmin := minimum (absolute Λint.inf) (absolute Λint.sup)
  let Λmax := maximum (absolute Λint.inf) (absolute Λint.sup)
  let φlo := divDown one (mulUp Λmax Λmax)                          -- phi = 1/Lambda_int^2
  let φhi := divUp one (mulDown Λmin Λmin)
  let Q := fun i => GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i  -- Q{i}
  -- `Q{i}`'s centers with error boxes as interval matrices, and generators, each stored once
  let Dv : Vector (Interval (Mat 𝕋 n n)) n := Vector.ofFn fun i =>
    (⟨fun l m => addDown ((Q i).c l m) ((Q i).I_error.inf l m),
      fun l m => addUp ((Q i).c l m) ((Q i).I_error.sup l m)⟩ : Interval (Mat 𝕋 n n)).materialiseMat
  let Kv : Vector (Vector (Vector (Vector 𝕋 n) n) n) (1 + R0red.h + R0red.h) :=
    Vector.ofFn fun j => Vector.ofFn fun i => Vector.ofFn fun l => Vector.ofFn fun m =>
      (Q i).G j l m
  let Rquad := (Zonotope.quadMapMatZono (fun i => Dv[i.val]'i.isLt)  -- quadMap(R0red_,Q)
    (fun (j : Fin (1 + R0red.h + R0red.h)) i l m =>
      (((Kv[j.val]'j.isLt)[i.val]'i.isLt)[l.val]'l.isLt)[m.val]'m.isLt) R0red_).materialise
  -- `res2 = aux_mappedSetError(guard,R0,A,b,err)`
  let flowSet := (Zonotope.mtimes A R₀).plus (Zonotope.point b)    -- flowSet = A*R0 + b
  let numInt := err.halfspaceRange (-nv) zero       -- interval(-n*err)
  let denInt := flowSet.halfspaceRange nv zero                      -- interval(n*flowSet)
  let denInv := recipI denInt.inf denInt.sup
  let Ilo := Interval.mulLo numInt.inf numInt.sup (denInv.inf 0) (denInv.sup 0)  -- I = num/den
  let Ihi := Interval.mulHi numInt.inf numInt.sup (denInv.inf 0) (denInv.sup 0)
  let res2 :=                                                      -- I*flowSet + err
    ((Zonotope.mtimesIntervalMat (mulI Ilo Ihi) flowSet).plus err).materialise
  -- `normalizeConstraints`: `n/‖n‖` and `d/‖n‖` as boxes
  let nrmLo := sqrtDown p (dotDown nv nv)
  let nrmHi := sqrtUp p (dotUp nv nv)
  let rLo := divDown one nrmHi                                      -- `1/‖n‖`
  let rHi := divUp one nrmLo
  let cI : Interval (Vec 𝕋 n) :=
    ⟨fun i => Interval.mulLo (nv i) (nv i) rLo rHi, fun i => Interval.mulHi (nv i) (nv i) rLo rHi⟩
  let nrmA := MatExp.normUpperBound (Interval.smul tmax tmax (Interval.point A))  -- `‖tmax A‖`
  match GuardMap.step_hitPointFloat A b nv d x0, GuardMap.step_hitJacobianFloat A b nv d x0 with
  | some k, some Lk =>                                               -- k, L
    -- `res1 = k + L*R0_ + 0.5*phi*quadMap(R0red_,Q)`
    let res1 := ((k.zonotope.plus (Zonotope.mtimesIntervalMat Lk R0_)).plus
      (Zonotope.mtimesIntervalMat (mulI (half φlo) (half φhi)) Rquad)).materialise
    let R := ((res1.plus res2).reduceGirard zonotopeOrder).materialise  -- R = reduce(res1 + res2)
    if (ltStrict zero Λint.inf || ltStrict Λint.sup zero) && (ltStrict zero denInt.inf ||
        ltStrict denInt.sup zero) && ltStrict zero (mulDown Λmin Λmin) && ltStrict zero nrmLo &&
        le nrmA (half (nsmulDown (η + 2) one)) then
      some (ContSet.projectOnHyperplaneIntervalFloat (S := 𝒵[𝕋]) R cI
        (Interval.mulLo d d rLo rHi) (Interval.mulHi d d rLo rHi))
    else none
  | _, _ => none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
