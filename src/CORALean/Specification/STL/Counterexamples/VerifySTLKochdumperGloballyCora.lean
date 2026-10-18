module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

/-!
# `evaluatePredicateUnionPolytopeCora`, the union branch of `aux_evaluatePredicate` on polytopes

The `else` branch (`% union of unsafe sets`) of `aux_evaluatePredicate` in CORA's
`@linearSys/private/priv_verifySTL_kochdumper.m` (l. 916-956, the program of [1]) for unsafe sets
that are polytopes `{x | Aᵢx ≤ bᵢ}`, the only kind `aux_safe2unsafe` builds (`polytope(list{k}) &
polytope(...)`, l. 849), one `let` per MATLAB step: `c = set{i}.A·R.c`, `G = set{i}.A·R.G`, `G =
abs(G)`, `rad = sum(G,2)`, the quick checks (`any(c - rad > d)`: `1`; `all(c + rad <= d)`: `0`,
returning at once; `all(c + sum(G(:,index),2) <= d)`: `3`), else `2`, lowered to `1` when
`~isIntersecting(R,set{i})`, then `list(i) = res`; the branch ends `res = max(list(i))`, the last
set's code. A polytope is the list of its rows `(Aⱼ, bⱼ)`; `isIntersecting` is a parameter, on the
zonotope `R = Rc + Rg·[-1,1]^m` and the polytope as sets. The halfspace arm, which skips
`isIntersecting`, is `STL.evaluatePredicateUnionCora`.

# `safeToUnsafeCora`, CORA's complement of a union of safe polytopes

`aux_safe2unsafe` with `aux_reverseHalfspaceConstraints` in CORA's
`@linearSys/private/priv_verifySTL_kochdumper.m` (l. 827-870, the program of [1]), the union of
unsafe sets that `aux_preprocessTemporalLogic` (l. 959-991) makes of a predicate whose disjunctive
normal form has two or more clauses, one `let` per MATLAB step. A polytope is the list of its rows
`(Aⱼ, bⱼ)`, `{x | Aⱼx ≤ bⱼ}`. Each row is reversed by `polytope/not` to the one-row polytope `(-Aⱼ,
-bⱼ - eps)`; the list starts with the reversed rows of the first clause, and each further clause
replaces it by `list{k} & reversed{j}` (rows of `list{k}`, then the reversed row) for every reversed
row `j` (outer loop) and every `k` (inner loop) with `isIntersecting(list{k}, reversed{j})`.
`isIntersecting` is a parameter on the two polytopes as sets; `eps` is MATLAB's.

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

# CORA's STL verifier returns `verified` for a violated `G_[0,1] ((-1 ≤ x ≤ 1) ∨ x ≥ 10)`

`linearSys/verify` with `options.verifyAlg = 'stl:kochdumper'` ([1]) on `ẋ = 0` (`A = 0`, `B = 0`,
`U = zonotope(0)`, as in CORA's `test_linearSys_verify_01_temporalLogic`), `R0 = zonotope(-1,1)
= [-2, 0]`, `tFinal = 1` and `globally((x(1) >= -1 & x(1) <= 1) | x(1) >= 10, interval(0,1))`.
The run `x ≡ -2` starts in `R0` and violates the formula at every time. The two clauses make
`sets{1}` a union of unsafe polytopes (`aux_safe2unsafe`, reversed rows shifted by `eps`):
`x ≤ -1 - eps ∧ x ≤ 10 - eps` and then `x ≥ 1 + eps ∧ x ≤ 10 - eps`. The reachable set `[-2, 0]`
meets the first (code `2`; the quick checks fail, `isIntersecting` is true) but `any(c - rad > d)`
holds for the second (`0 > -1 - eps`), so `res = max(list(i))` (l. 955) is `1` on every time
interval and point; `evalPredicates` turns `globally(φ,[0,2])` into `stl(true)` and
`aux_modelCheckReachSet` returns `res = true` (l. 221): CORA reports the specification verified.
`isIntersecting` is any test returning `true` on sets that meet (CORA's exact test does); `ε` is
any shift in `[0, 1)`, CORA's `eps` among them; real arithmetic, every comparison by margin `≥ 1`.

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


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's union branch of `aux_evaluatePredicate` for `R = Rc + Rg·[-1,1]^m` and unsafe
polytopes given by their rows: `0` when some set contains `R` (checked in order), else the code of
the last set. -/
noncomputable def STL.evaluatePredicateUnionPolytopeCora {n m : ℕ}
    (isIntersecting : Set (Fin n → ℝ) → Set (Fin n → ℝ) → Bool) (Rc : Fin n → ℝ)
    (Rg : Fin n → Fin m → ℝ) (index : Finset (Fin m)) :
    List (List ((Fin n → ℝ) × ℝ)) → ℕ
  | [] => 0
  | P :: rest =>
    let c := fun r : (Fin n → ℝ) × ℝ => ∑ j, r.1 j * Rc j          -- c = set{i}.A * R.c
    let G := fun (r : (Fin n → ℝ) × ℝ) k => ∑ j, r.1 j * Rg j k     -- G = set{i}.A * R.G
    let G := fun r k => |G r k|                                     -- G = abs(G)
    let rad := fun r => ∑ k, G r k                                  -- rad = sum(G,2)
    let R : Set (Fin n → ℝ) := {x | ∃ a : Fin m → ℝ, (∀ k, a k ∈ Set.Icc (-1 : ℝ) 1) ∧
      x = fun j => Rc j + ∑ k, Rg j k * a k}                         -- R
    let S : Set (Fin n → ℝ) := {x | ∀ r ∈ P, ∑ j, r.1 j * x j ≤ r.2}  -- set{i}
    let res : ℕ :=
      if ∃ r ∈ P, c r - rad r > r.2 then 1                          -- any(c - rad > d): res = 1
      else if ∀ r ∈ P, c r + rad r ≤ r.2 then 0                     -- all(c + rad <= d): res = 0
      else if ∀ r ∈ P, c r + ∑ k ∈ index, G r k ≤ r.2 then 3       -- all(c + sum(G(:,index),2)...)
      else if isIntersecting R S = false then 1                     -- ~isIntersecting(R,set{i})
      else 2                                                        -- res = 2
    if res = 0 then 0                                               -- res = 0; return
    else if rest = [] then res                                      -- res = max(list(i)), i = last
    else STL.evaluatePredicateUnionPolytopeCora isIntersecting Rc Rg index rest


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `aux_safe2unsafe` on the safe polytopes `clauses`: the unsafe polytopes whose union is
the complement of their union (up to `eps`), in CORA's order. -/
noncomputable def STL.safeToUnsafeCora {n : ℕ}
    (isIntersecting : Set (Fin n → ℝ) → Set (Fin n → ℝ) → Bool) (eps : ℝ) :
    List (List ((Fin n → ℝ) × ℝ)) → List (List ((Fin n → ℝ) × ℝ))
  | [] => []
  | S₁ :: rest =>
    let poly := fun P : List ((Fin n → ℝ) × ℝ) =>
      {x : Fin n → ℝ | ∀ r ∈ P, ∑ j, r.1 j * x j ≤ r.2}             -- polytope(P)
    let reverse := fun P : List ((Fin n → ℝ) × ℝ) =>
      P.map fun r => [(-r.1, -r.2 - eps)]                           -- ~polytope(P.A(i,:),P.b(i))
    let list := reverse S₁                                          -- list = aux_reverse...
    rest.foldl (fun list Sᵢ =>                                      -- for i = 2:length(sets)
      let reversed := reverse Sᵢ                                    -- reversedHalfspaces
      reversed.flatMap fun h =>                                     -- for j
        list.filterMap fun L =>                                     -- for k
          if isIntersecting (poly L) (poly h) then some (L ++ h)    -- list_{end+1} = ... & ...
          else none) list                                           -- list = list_


-- The model: CORA's code as printed, kept only to be refuted.
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.verifySTLKochdumperGloballyCora_unionLastOnly_counterexample
    (isIntersecting : Set (Fin 1 → ℝ) → Set (Fin 1 → ℝ) → Bool)
    (hsound : ∀ S T, (S ∩ T).Nonempty → isIntersecting S T = true)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1) : -- --- STMT ---
    let c₀ : Fin 1 → ℝ := fun _ => -1                          -- R0 = zonotope(-1,1)
    let G₀ : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
    let S₁ : List ((Fin 1 → ℝ) × ℝ) := [(fun _ => -1, 1), (fun _ => 1, 1)]  -- x >= -1 & x <= 1
    let S₂ : List ((Fin 1 → ℝ) × ℝ) := [(fun _ => -1, -10)]                 -- x >= 10
    let φ : ℝ → Prop := fun x => (x ≥ -1 ∧ x ≤ 1) ∨ x ≥ 10
    -- `convert2set`'s clauses are `φ`
    (∀ x : Fin 1 → ℝ, φ (x 0) ↔ ∃ S ∈ [S₁, S₂], ∀ r ∈ S, ∑ j, r.1 j * x j ≤ r.2) ∧
    -- a run of `ẋ = 0` from `R0` violates `G_[0,1] φ`
    (∃ x : ℝ → ℝ, (∃ a ∈ Set.Icc (-1 : ℝ) 1, x 0 = c₀ 0 + G₀ 0 0 * a) ∧
      (∀ t, HasDerivAt x 0 t) ∧ ∃ t ∈ Set.Icc (0 : ℝ) 1, ¬ φ (x t)) ∧
    -- CORA returns `res = true`: verified
    STL.verifySTLKochdumperGloballyCora isIntersecting ε c₀ G₀ 1 [S₁, S₂] =
      some true := by -- --- PROOF ---
  intro c₀ G₀ S₁ S₂ φ
  refine ⟨?_, ⟨fun _ => -2, ⟨-1, by norm_num, by simp [c₀, G₀]; norm_num⟩,
    fun t => hasDerivAt_const t _, 0, by norm_num, by simp [φ]; norm_num⟩, ?_⟩
  · intro x
    simp only [φ, S₁, S₂, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, forall_eq_or_imp, forall_eq, Fin.sum_univ_one]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · left; constructor <;> linarith
      · right; linarith
    · rintro (⟨h1, h2⟩ | h)
      · left; constructor <;> linarith
      · right; linarith
  · -- `aux_safe2unsafe`: both pairs meet, so both intersections are kept
    simp only [STL.verifySTLKochdumperGloballyCora, STL.safeToUnsafeCora, S₁, S₂, List.foldl,
      List.map, List.flatMap, List.filterMap]
    rw [if_pos (hsound _ _ ?h1), if_pos (hsound _ _ ?h2)]
    case h1 => exact ⟨fun _ => -2, by simp; linarith, by simp; linarith⟩
    case h2 => exact ⟨fun _ => 2, by simp; linarith, by simp; linarith⟩
    simp only [List.nil_append, List.cons_append]
    -- `R0` meets the first unsafe set (code `2`), the second is disjoint (code `1`)
    have hE : STL.evaluatePredicateUnionPolytopeCora isIntersecting c₀ G₀ Finset.univ
        [[(-fun _ => -1, -1 - ε), (-fun _ => -1, - -10 - ε)],
          [(-fun _ => 1, -1 - ε), (-fun _ => -1, - -10 - ε)]] = 1 := by
      have hI : isIntersecting {x | ∃ a : Fin 1 → ℝ, (-1 ≤ a 0 ∧ a 0 ≤ 1) ∧ x = fun _ => -1 + a 0}
          {x | x 0 ≤ -1 - ε ∧ x 0 ≤ 10 - ε} = true :=
        hsound _ _ ⟨fun _ => -2, ⟨fun _ => -1, by norm_num, by funext; norm_num⟩, by
          simp only [Set.mem_setOf_eq]; constructor <;> linarith⟩
      have h1 : ¬ (1 < ε ∨ 10 - ε < -1 - 1) := by
        rintro (h | h) <;> linarith
      have h2 : ¬ (ε ≤ -1 ∧ ε ≤ 10) := by
        rintro ⟨h, -⟩; linarith
      have h3 : -1 < ε ∨ 10 - ε < -1 - 1 := Or.inl (by linarith)
      simp [STL.evaluatePredicateUnionPolytopeCora, c₀, G₀, hI, h1, h2, h3]
    -- every code is `1`, so `evalPredicates` gives `stl(true)`
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [hE]
    simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
