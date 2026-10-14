module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
public import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplaneIntervalFloat
public import CORALean.ContSet.Conversion.Float.Interval_to_ContSet
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Operations.HalfspaceRange
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Operations.QuadMapMatZono
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirard
public import CORALean.Global.Float.Sqrt
public import CORALean.HybridDynamics.Definitions.Location
public import CORALean.HybridDynamics.Operations.AbstractionErrorFloat
public import CORALean.HybridDynamics.Operations.HitHessianMatZonoFloat
public import CORALean.HybridDynamics.Operations.HitJacobianFloat
public import CORALean.HybridDynamics.Operations.HitPointFloat
public import CORALean.HybridDynamics.Operations.SdcInputFloat

@[expose] public section

/-!
# `Location.guardIntersectHyperplaneMapFloat`, the guard mapping at floats

`Location.guardIntersectHyperplaneMap`, CORA's `guardIntersect_hyperplaneMap` [1], at float
zonotopes, one `let` per line of the code: `k ⊕ L(R₀ ⊖ ξ) ⊕ ½[φ̲, φ̄] R_quad ⊕ I (AR₀ ⊕ b) ⊕ E`
of [2, Sec. 5.4], reduced and projected. What rounds is an interval, and what an interval
cannot stand in for is charged to a set: `b` is the lower end of the box
`GuardMap.sdcInputFloat`, the rest `t(b − b̲)` added to the error; `k`, `L` are a box and an
interval matrix; `Q⁽ⁱ⁾` is taken at the centre `τ_c` and radius `τ_g` of `τ`'s interval and
`R_quad` at interval centres; `Λ` and `nᵀx − d` range over `R₀red ⊖ ξ ⊕ ξ`, which holds the stored
centre `ξ` even when the error box of `R₀red` does not hold `0`; `n/‖n‖` and `d/‖n‖` are boxes
(`sqrtDown`/`sqrtUp` at precision `p`) for `projectOnHyperplaneIntervalFloat`. `none` when a
float test fails: `Λ`, `nᵀ(Ax + b)`, `Λ²` or `‖n‖` not certified away from `0`, the float
`‖tmax A‖` above `(η + 2)/2`, or `k`, `L` not computed.

## References

* [1] `hybridDynamics/@location/guardIntersect_hyperplaneMap.m`
* [2] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {G : ℕ → Type}
  [∀ n, ContSet (G n) (Vec ℝ n)] {L : Type} {n : ℕ}


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
  let U : Zonotope (Vec 𝕋 n) := ℓ.U
  let th : 𝕋 := half tmax                                           -- th = tmax/2
  let bI := GuardMap.sdcInputFloat A U.c th η R₀.c                  -- b = aux_constantFlow, a box
  let b : Vec 𝕋 n := bI.inf                                         -- its lower end
  let R0red := R₀.reduceGirard guardOrder                           -- R0red = reduce(R0,..)
  let R0red_ := R0red.recentre                                      -- R0red_ = R0red - c
  let R0_ := R₀.recentre                                            -- R0_ = R0 - center(R0)
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
  let Λinv := recipI Λint.1 Λint.2                                  -- 1/Lambda_int
  let τlo := Interval.mulLo (neg dint.2) (neg dint.1) (Λinv.inf 0) (Λinv.sup 0)  -- tau
  let τhi := Interval.mulHi (neg dint.2) (neg dint.1) (Λinv.inf 0) (Λinv.sup 0)
  let τc := half (addUp τlo τhi)                                    -- its centre
  let τg := maximum (subUp τhi τc) (subUp τc τlo)                   -- and radius
  let Λmin := minimum (absolute Λint.1) (absolute Λint.2)
  let Λmax := maximum (absolute Λint.1) (absolute Λint.2)
  let φlo := divDown one (mulUp Λmax Λmax)                          -- phi = 1/Lambda_int^2
  let φhi := divUp one (mulDown Λmin Λmin)
  let Q := fun i => GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i  -- Q{i}
  -- `Q{i}`'s centres with error boxes as interval matrices, and generators, each stored once
  let Dv : Vector (Interval (Mat 𝕋 n n)) n := Vector.ofFn fun i =>
    (⟨fun l m => addDown ((Q i).c l m) ((Q i).E.inf l m),
      fun l m => addUp ((Q i).c l m) ((Q i).E.sup l m)⟩ : Interval (Mat 𝕋 n n)).materialiseMat
  let Kv : Vector (Vector (Vector (Vector 𝕋 n) n) n) (1 + R0red.h + R0red.h) :=
    Vector.ofFn fun j => Vector.ofFn fun i => Vector.ofFn fun l => Vector.ofFn fun m =>
      (Q i).G j l m
  let Rquad := (Zonotope.quadMapMatZono (fun i => Dv[i.val]'i.isLt)  -- quadMap(R0red_,Q)
    (fun (j : Fin (1 + R0red.h + R0red.h)) i l m =>
      (((Kv[j.val]'j.isLt)[i.val]'i.isLt)[l.val]'l.isLt)[m.val]'m.isLt) R0red_).materialise
  -- `res2 = aux_mappedSetError(guard,R0,A,b,err)`
  let flowSet := (Zonotope.mtimes A R₀).plus (Zonotope.point b)    -- flowSet = A*R0 + b
  let numInt := err.halfspaceRange (fun i => neg (nv i)) zero       -- interval(-n*err)
  let denInt := flowSet.halfspaceRange nv zero                      -- interval(n*flowSet)
  let denInv := recipI denInt.1 denInt.2
  let Ilo := Interval.mulLo numInt.1 numInt.2 (denInv.inf 0) (denInv.sup 0)  -- I = num/den
  let Ihi := Interval.mulHi numInt.1 numInt.2 (denInv.inf 0) (denInv.sup 0)
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
  match GuardMap.hitPointFloat A b nv d x0, GuardMap.hitJacobianFloat A b nv d x0 with
  | some k, some Lk =>                                               -- k, L
    -- `res1 = k + L*R0_ + 0.5*phi*quadMap(R0red_,Q)`
    let res1 := ((k.zonotope.plus (Zonotope.mtimesIntervalMat Lk R0_)).plus
      (Zonotope.mtimesIntervalMat (mulI (half φlo) (half φhi)) Rquad)).materialise
    let R := ((res1.plus res2).reduceGirard zonotopeOrder).materialise  -- R = reduce(res1 + res2)
    if (ltStrict zero Λint.1 || ltStrict Λint.2 zero) && (ltStrict zero denInt.1 ||
        ltStrict denInt.2 zero) && ltStrict zero (mulDown Λmin Λmin) && ltStrict zero nrmLo &&
        le nrmA (half (nsmulDown (η + 2) one)) then
      some (ContSet.projectOnHyperplaneIntervalFloat (S := 𝒵[𝕋]) R cI
        (Interval.mulLo d d rLo rHi) (Interval.mulHi d d rLo rHi))
    else none
  | _, _ => none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
