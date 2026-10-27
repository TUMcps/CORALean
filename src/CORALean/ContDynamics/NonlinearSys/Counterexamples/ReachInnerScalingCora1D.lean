module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Order.Basic

@[expose] public section

/-!
# `reachInnerScalingCora1D`, CORA's `'scale'` inner approximation in one dimension

CORA's `@nonlinearSys/private/priv_reachInnerScaling.m` (`reachInner`, `algInner = 'scale'`) at one
time point, without inputs, line by line from the outer approximation
`R = c + Σᵢ Gᵢ α^Eᵢ + Σₖ GIₖ βₖ` that `reach` returned. `getSubset(R,1,±1)` evaluates the dependent
part at `α = ±1`. `fmincon` returns a point `(α, γ)`, `isEmptyContract` is
`isempty(contract(...))`: both are arguments. `scaleFac = none` is `'auto'`: start at `0.99`, on a
failed contraction subtract `0.01` and restart the boundary loop; the `while` stops at
`factor ≤ 0`, with `I` as it is. `fuel` bounds the passes. The result is `getSubset(R,1:n,I)`
without `GI`. The paper's Step 4, the backward simulation (14), is not in the code and not here.

# CORA's `'scale'` returns an "inner approximation" of unreachable states

`ẋ = 0` on `ℝ`, `X₀ = [-1, 1]`, `t = 1`, so the reachable set is `[-1, 1]`. The outer
approximation `R = 2 + α + 2β` holds the run from each `α ∈ X₀` ([1, (6)]), and the pieces of the
boundary enclosure, `[1, 5]` and `[-1, 3]`, hold `∂R = {±1}`. At the default `scaleFac = 'auto'`,
`priv_reachInnerScaling` asks `fmincon` for a point of the first piece and contracts
`[-1, factor·val] × [-1, 1]`. Every point `fmincon` may return lies in the box, so `(-1, -1)` solves
the constraint in that box: no contractor that [1, Def. 3] admits proves it empty. Each pass lowers
`factor`, `I` is still `[-1, 1]`, and CORA returns `2 + [-1, 1] = [1, 3]`: `3` is in it and
unreachable, and the center `2` fails [1]'s Step 4, (14), which the code never runs.

## Inputs
* `fmincon` – optimizer
* `isEmptyContract` – contractor emptiness test
* `fuel` – iteration bound

## Hypotheses
* `hopt` – the optimizer returns a feasible point
* `hcontract` – the contractor is sound

## Conclusion
* the returned inner approximation holds a state no run reaches

## References

* [1] [N. Kochdumper and M. Althoff. "Computing Non-Convex Inner-Approximations of Reachable Sets
      for Nonlinear Continuous Systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../../../references/2020/kochdumper-cdc-nonconvex-inner.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `'scale'` inner approximation of `R = c + Σᵢ Gᵢ α^Eᵢ + Σₖ GIₖ βₖ` in one dimension, at
the optimizer `fmincon` and the contractor's verdict `isEmptyContract`; `none` when CORA errors
or the step is not modelled. -/
noncomputable def NonlinearSys.reachInnerScalingCora1D {h q : ℕ} (c : ℝ) (G : Fin h → ℝ)
    (E : Fin h → ℕ) (GI : Fin q → ℝ) (orderInner : ℕ) (scaleFac : Option ℝ)
    (fmincon : (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (isEmptyContract : (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ × ℝ → Bool) (fuel : ℕ) : Option (Set ℝ) :=
  -- Step 1: aux_removeAddGens is the identity at one factor; aux_reduceOrderDep only if m ≤ n*order
  if orderInner < h then none else
  let pR : ℝ → ℝ := fun a => c + ∑ i, G i * a ^ E i      -- R.c + R.G * α^R.E
  -- Step 2: B{1} = getSubset(R,1,1), B{2} = getSubset(R,1,-1), each aux_reduceOrderInd
  let cB1 := pR 1                                         -- B{1}.c
  let cB2 := pR (-1)                                      -- B{2}.c
  let rB := ∑ k, |GI k|                                   -- B{j}.GI = rad(interval(B'*Z))
  -- conFun = aux_constraintIntersection(R,B{j}): b + [R.G, -B.G, -B.GI] * x^E, no R.GI
  let conFun1 : ℝ × ℝ → ℝ := fun x => pR x.1 - (cB1 + rB * x.2)
  let conFun2 : ℝ × ℝ → ℝ := fun x => pR x.1 - (cB2 + rB * x.2)
  -- Step 3: factor = 0.99 ('auto') or options.scaleFac
  let factor0 := scaleFac.getD (99 / 100)
  -- one pass of `for j = 1:length(B)`: (I, loop), `none` for `I = []` or an error
  let pass : ℝ → Real.Interval ℝ → Option (Option (Real.Interval ℝ) × Bool) := fun factor I =>
    -- j = 1, type 1: [~,val] = fmincon(@(x) x(1), ...), val = factor*val
    let x1 := fmincon (fun x => x.1) conFun1 (I.inf, -1) (I.sup, 1)
    let val1 := factor * x1.1
    if val1 < I.inf then none else                          -- interval(infimum(I0(1)),val)
    if isEmptyContract conFun1 (I.inf, -1) (val1, 1) then
      let I1 : Real.Interval ℝ := ⟨I.inf, val1⟩                            -- I = project(Itemp,1:n)
      -- j = 2, type -1: [~,val] = fmincon(@(x) -x(1), ...), val = factor*val
      let x2 := fmincon (fun x => -x.1) conFun2 (I1.inf, -1) (I1.sup, 1)
      let val2 := factor * -x2.1
      if I1.sup < -val2 then none else                      -- interval(-val,supremum(I0(1)))
      if isEmptyContract conFun2 (-val2, -1) (I1.sup, 1) then
        some (some ⟨-val2, I1.sup⟩, false)                  -- I = project(Itemp,1:n)
      else if scaleFac.isNone then some (some I1, true)   -- factor = factor - 0.01; loop = 1
      else some (none, false)                             -- I = []
    else if scaleFac.isNone then some (some I, true)      -- factor = factor - 0.01; loop = 1
    else some (none, false)                               -- I = []
  -- while factor > 0 && loop
  let loop : ℕ → ℝ → Real.Interval ℝ → Option (Option (Real.Interval ℝ)) :=
    Nat.rec (fun _ I => some (some I)) fun _ next factor I =>
      if 0 < factor then
        match pass factor I with
        | some (some I', true) => next (factor - 1 / 100) I'
        | some (I', _) => some I'
        | none => none
      else some (some I)
  match loop fuel factor0 ⟨-1, 1⟩ with
  | some (some I) => some {y | ∃ a ∈ Set.Icc I.inf I.sup, y = pR a}  -- polyZonotope(R.c,R.G,[],R.E)
  | some none => some ∅                                   -- R = []
  | none => none


open Set


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A function with zero derivative on `[0, 1]` is constant there. -/
private theorem aux_const {x : ℝ → ℝ} (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x 0 (Icc 0 1) s) :
    x 1 = x 0 :=
  constant_of_has_deriv_right_zero (fun s hs => (hd s hs).continuousWithinAt)
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1))) 1
    ⟨zero_le_one, le_rfl⟩

/-- CORA's loop on `R = 2 + α + 2β`: every pass fails on the first piece, and the result is
`[1, 3]`, for every `fmincon` that returns a feasible point in its box and every sound
contractor. -/
private theorem aux_reachInnerScalingCora1D_eq
    (fmincon : (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (isEmptyContract : (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ × ℝ → Bool) (fuel : ℕ)
    (hopt : ∀ f con lb ub, (∃ x, lb ≤ x ∧ x ≤ ub ∧ con x = 0) →
      lb ≤ fmincon f con lb ub ∧ fmincon f con lb ub ≤ ub ∧ con (fmincon f con lb ub) = 0)
    (hcontract : ∀ con lb ub, isEmptyContract con lb ub = true →
      ∀ x, lb ≤ x → x ≤ ub → con x ≠ 0) : -- --- CONCL ---
    NonlinearSys.reachInnerScalingCora1D 2 ![1] ![1] ![2] 5 none fmincon isEmptyContract fuel =
      some (Icc 1 3) := by -- --- PROOF ---
  simp only [NonlinearSys.reachInnerScalingCora1D]
  rw [if_neg (by norm_num)]
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, pow_one, one_mul, abs_two,
    Option.getD_none, Option.isNone_none, ite_true]
  -- the end set: the dependent part `2 + α` over `α ∈ [-1, 1]`
  have hend : {y : ℝ | ∃ a, (a ∈ Icc (-1 : ℝ) 1) ∧ y = 2 + a} = Icc 1 3 := by
    ext y
    constructor
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      exact ⟨y - 2, ⟨by linarith, by linarith⟩, by ring⟩
  generalize hf : (99 / 100 : ℝ) = f0
  have hf1 : f0 ≤ 1 := by rw [← hf]; norm_num
  clear hf
  induction fuel generalizing f0 with
  | zero => simpa using hend
  | succ n ih =>
    by_cases h0 : 0 < f0
    · -- fmincon's point lies in the box, so `val ≥ -factor ≥ -1`
      have hx := hopt (fun x => x.1) (fun x => 2 + x.1 - (2 + 1 + 2 * x.2)) (-1, -1) (1, 1)
        ⟨(1, 0), by simp [Prod.le_def], by simp [Prod.le_def], by norm_num⟩
      set x1 := fmincon (fun x => x.1) (fun x => 2 + x.1 - (2 + 1 + 2 * x.2)) (-1, -1) (1, 1)
      have hlo : -1 ≤ x1.1 := hx.1.1
      have hhi : x1.1 ≤ 1 := hx.2.1.1
      have hval : -1 ≤ f0 * x1.1 := by nlinarith
      -- `(-1, -1)` solves the constraint in the box, so no contractor proves it empty
      have hce : isEmptyContract (fun x => 2 + x.1 - (2 + 1 + 2 * x.2)) (-1, -1) (f0 * x1.1, 1) =
          false := by
        by_contra hne
        exact hcontract _ _ _ (by simpa using hne) (-1, -1) le_rfl
          (by simp [Prod.le_def, hval]) (by norm_num)
      simp only [h0, ite_true]
      rw [if_neg (not_lt.mpr hval)]
      rw [if_neg (by simpa using hce)]
      refine ih _ ?_
      linarith
    · simp [h0]
      simpa using hend


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `'scale'` at `ẋ = 0` from `[-1, 1]`, outer approximation `2 + α + 2β`, returns `[1, 3]`
for every `fmincon` that returns a feasible point and every sound contractor: `3` is not
reachable, and the center `2` fails (14). -/
theorem NonlinearSys.reachInnerScalingCora1D_counterexample
    (fmincon : (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (isEmptyContract : (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ × ℝ → Bool) (fuel : ℕ)
    (hopt : ∀ f con lb ub, (∃ x, lb ≤ x ∧ x ≤ ub ∧ con x = 0) →
      lb ≤ fmincon f con lb ub ∧ fmincon f con lb ub ≤ ub ∧ con (fmincon f con lb ub) = 0)
    (hcontract : ∀ con lb ub, isEmptyContract con lb ub = true →
      ∀ x, lb ≤ x → x ≤ ub → con x ≠ 0) : -- --- CONCL ---
    let X₀ : Set ℝ := Icc (-1) 1
    let runs : Set (ℝ → ℝ) := {x | ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x 0 (Icc 0 1) t}
    let R : Set ℝ := {y | ∃ x ∈ runs, x 0 ∈ X₀ ∧ x 1 = y}
    (∀ x ∈ runs, x 0 ∈ X₀ → ∃ b ∈ Icc (-1 : ℝ) 1, x 1 = 2 + x 0 + 2 * b) ∧
      frontier R ⊆ {y | ∃ b ∈ Icc (-1 : ℝ) 1, y = 3 + 2 * b ∨ y = 1 + 2 * b} ∧
      NonlinearSys.reachInnerScalingCora1D 2 ![1] ![1] ![2] 5 none fmincon isEmptyContract fuel =
        some (Icc 1 3) ∧
      (3 : ℝ) ∉ R ∧ ∀ x ∈ runs, x 0 = 2 → x 1 ∉ X₀ := by -- --- PROOF ---
  intro X₀ runs R
  -- the reachable set at `t = 1` is `X₀`
  have hR : R = X₀ := by
    ext y
    constructor
    · rintro ⟨x, hx, hx0, rfl⟩
      rwa [aux_const hx]
    · intro hy
      exact ⟨fun _ => y, fun t _ => hasDerivWithinAt_const _ _ _, hy, rfl⟩
  refine ⟨?_, ?_, aux_reachInnerScalingCora1D_eq fmincon isEmptyContract fuel hopt hcontract,
    ?_, ?_⟩
  · -- [1, (6)]: the run from `α` stays at `α = 2 + α + 2·(-1)`
    intro x hx _
    exact ⟨-1, by norm_num, by rw [aux_const hx]; ring⟩
  · -- `∂R = {-1, 1}`: `1 = 3 + 2·(-1)` is in the first piece, `-1 = 1 + 2·(-1)` in the second
    rw [hR]
    show frontier (Icc (-1 : ℝ) 1) ⊆ _
    rw [frontier_Icc (by norm_num)]
    rintro y (rfl | rfl)
    · exact ⟨-1, by norm_num, Or.inr (by norm_num)⟩
    · exact ⟨-1, by norm_num, Or.inl (by norm_num)⟩
  · -- `3 ∉ [-1, 1]`
    rw [hR]
    norm_num [X₀]
  · -- (14): the time-inverted run from the center `2` stays at `2 ∉ X₀`
    intro x hx hx0
    rw [aux_const hx, hx0]
    norm_num [X₀]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
