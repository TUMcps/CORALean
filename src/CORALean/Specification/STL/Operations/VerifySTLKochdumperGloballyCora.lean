module

public import CORALean.Specification.STL.Operations.EvaluatePredicateUnionPolytopeCora
public import CORALean.Specification.STL.Operations.SafeToUnsafeCora

@[expose] public section

/-!
# `verifySTLKochdumperGloballyCora`, CORA's STL verifier on `ẋ = 0` and `G_[0,T] (∨ clauses)`

The first loop iteration of CORA's `priv_verifySTL_kochdumper` (`@linearSys/private/`, l. 1-96), the
verifier of [1], up to its first `res = true; return` (l. 221), on the one path this model fixes: `A
= 0`, `B = 0`, `U = {0}`, no `params.u`, `R0 = c₀ + G₀·[-1,1]^p`, and `spec.set = globally(φ,
[0,T])` with `φ` non-temporal, the disjunction of the polytopes `clauses` (two or more, so `sets{1}`
is the union of unsafe sets `aux_safe2unsafe` builds). Then `params.tFinal = T` (l. 52), `dt = T/2`
(l. 1000; `A = 0` ends both step-size loops at once), `t = 0:dt:T+dt` has four entries (l. 110), and
with `eAdt = I`, `T·u = 0`, `P_U = err = C = 0` every reachable set (l. 154-163) is `R0` up to zero
generators, which add nothing to any sum of `aux_evaluatePredicate`; `p_u = 0` makes every `index`
the `p` columns of `G₀`. `aux_modelCheckReachSet` (l. 176-221), one `let` per step: the interval
codes, their copy into `predPoint` (l. 198-205), the point codes, `3 → 0`, and `sampledTime` on
`globally(φ,[0,2])`, whose `evalPredicates` (l. 85-92) reads `predInt(1,1:2)` and
`predPoint(1,1:3)`. `some true` is `res = true` (l. 221); `none` is any other way on, which the
model leaves (`stl(false)` halves `dt`, an unchanged `φ` goes to the factor constraints).

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `priv_verifySTL_kochdumper` on `ẋ = 0` from `R0 = c₀ + G₀·[-1,1]^p` against
`globally(φ,[0,T])`, `φ` the disjunction of `clauses`: `some true` when its first iteration
returns `res = true`, else `none`. -/
noncomputable def STL.verifySTLKochdumperGloballyCora {n p : ℕ}
    (isIntersecting : Set (Fin n → ℝ) → Set (Fin n → ℝ) → Bool) (eps : ℝ)
    (c₀ : Fin n → ℝ) (G₀ : Fin n → Fin p → ℝ) (T : ℝ)
    (clauses : List (List ((Fin n → ℝ) × ℝ))) : Option Bool :=
  let tFinal := T                                             -- params.tFinal = maximumTime(...)
  let _dt := tFinal / 2                                       -- dt = params.tFinal/2
  let sets := STL.safeToUnsafeCora isIntersecting eps clauses -- [phi,sets] = aux_preprocess...
  -- [R,ind] = aux_compReachSet(linsys,params,dt), length(t) = 4
  let H : Fin 4 → (Fin n → ℝ) × (Fin n → Fin p → ℝ) :=
    fun _ => (c₀, G₀)                                         -- H{i+1} = eAdt*H{i} + T*(...)
  let Rpoint := H                                             -- Rpoint.set{i+1} = H{i+1} + ...
  let Rint : Fin 3 → (Fin n → ℝ) × (Fin n → Fin p → ℝ) :=
    fun i => H i.castSucc                                     -- Rint.set{i} = enclose(...) + ...
  let index : Finset (Fin p) := Finset.univ                   -- ind.point{i}, ind.int{i}
  -- [res,~,elem,pred] = aux_modelCheckReachSet(phi,R,ind,dt,sets,pred,false)
  let predInt : Fin 3 → ℕ := fun _ => 2                       -- predInt = 2*ones(...)
  let predPoint : Fin 4 → ℕ := fun _ => 2                     -- predPoint = 2*ones(...)
  let predInt := fun i => if predInt i = 2 then STL.evaluatePredicateUnionPolytopeCora
    isIntersecting (Rint i).1 (Rint i).2 index sets else predInt i  -- pred.int = aux_evaluate...
  let predPoint := (List.finRange 3).foldl (fun pp j => if predInt j < 2 then
    Function.update (Function.update pp j.castSucc (predInt j)) j.succ (predInt j)
    else pp) predPoint                                        -- if pred.int(i,j) < 2 ...
  let predPoint := fun i => if predPoint i = 2 then STL.evaluatePredicateUnionPolytopeCora
    isIntersecting (Rpoint i).1 (Rpoint i).2 index sets else predPoint i  -- pred.point = ...
  let predInt := fun i => if predInt i = 3 then 0 else predInt i      -- predInt(predInt == 3) = 0
  let predPoint := fun i => if predPoint i = 3 then 0 else predPoint i -- predPoint(...) = 0
  -- phi = sampledTime(phi,dt,true,predInt,predPoint): globally(φ,[0,tFinal/dt]) = [0,2]
  let timeInt := [predInt 0, predInt 1]                       -- pred.timeInt(id,1:2)
  let timePoint := [predPoint 0, predPoint 1, predPoint 2]    -- pred.timePoint(id,1:3)
  let phi : Option Bool :=
    if timeInt.all (· = 1) then some true                     -- all(timeInt == 1): stl(true)
    else if timeInt.any (· = 0) || timePoint.any (· = 0) then some false  -- stl(false)
    else none                                                 -- φ unchanged
  if phi = some true then some true                           -- strcmp(phi.type,'true'): res = true
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
