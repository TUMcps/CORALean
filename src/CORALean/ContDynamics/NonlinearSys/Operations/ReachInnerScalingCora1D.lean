module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Defs

@[expose] public section

/-!
# `reachInnerScalingCora1D`, CORA's `'scale'` inner approximation in one dimension

CORA's `@nonlinearSys/private/priv_reachInnerScaling.m` (`reachInner`, `algInner = 'scale'`) at
one time point, without inputs, line by line from the outer approximation
`R = c + Σᵢ Gᵢ α^Eᵢ + Σₖ GIₖ βₖ` that `reach` returned. With one state, `aux_removeAddGens` has
nothing to remove; `aux_reduceOrderDep` is modelled only when it does nothing (else `none`).
`getSubset(R,1,±1)` evaluates the dependent part at `α = ±1`; `aux_reduceOrderInd` is the
interval hull of `GI`, radius `Σ|GIₖ|`. `aux_constraintIntersection` is `R.G`'s polynomial minus
the piece, `R.GI` left out (line 217). `fmincon` returns a point `(α, γ)`, `val` its objective;
`isEmptyContract` is `isempty(contract(...))`. Both are arguments: their theorems quantify over
them. `scaleFac = none` is `'auto'`: start at `0.99`, on a failed contraction subtract `0.01`
and restart the boundary loop, keeping `I`; the `while` stops at `factor ≤ 0`, with `I` as it is
(lines 111, 137-139). `fuel` bounds the passes, ending as `factor ≤ 0` does. The result is
`getSubset(R,1:n,I)` without `GI` (lines 151-152); `none` also marks `interval`'s error at
`lower > upper`.

The paper's Step 4, the backward simulation (14), is not in the code and not here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

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
  let pass : ℝ → ℝ × ℝ → Option (Option (ℝ × ℝ) × Bool) := fun factor I =>
    -- j = 1, type 1: [~,val] = fmincon(@(x) x(1), ...), val = factor*val
    let x1 := fmincon (fun x => x.1) conFun1 (I.1, -1) (I.2, 1)
    let val1 := factor * x1.1
    if val1 < I.1 then none else                          -- interval(infimum(I0(1)),val)
    if isEmptyContract conFun1 (I.1, -1) (val1, 1) then
      let I1 := (I.1, val1)                               -- I = project(Itemp,1:n)
      -- j = 2, type -1: [~,val] = fmincon(@(x) -x(1), ...), val = factor*val
      let x2 := fmincon (fun x => -x.1) conFun2 (I1.1, -1) (I1.2, 1)
      let val2 := factor * -x2.1
      if I1.2 < -val2 then none else                      -- interval(-val,supremum(I0(1)))
      if isEmptyContract conFun2 (-val2, -1) (I1.2, 1) then
        some (some (-val2, I1.2), false)                  -- I = project(Itemp,1:n)
      else if scaleFac.isNone then some (some I1, true)   -- factor = factor - 0.01; loop = 1
      else some (none, false)                             -- I = []
    else if scaleFac.isNone then some (some I, true)      -- factor = factor - 0.01; loop = 1
    else some (none, false)                               -- I = []
  -- while factor > 0 && loop
  let loop : ℕ → ℝ → ℝ × ℝ → Option (Option (ℝ × ℝ)) :=
    Nat.rec (fun _ I => some (some I)) fun _ next factor I =>
      if 0 < factor then
        match pass factor I with
        | some (some I', true) => next (factor - 1 / 100) I'
        | some (I', _) => some I'
        | none => none
      else some (some I)
  match loop fuel factor0 (-1, 1) with
  | some (some I) => some {y | ∃ a ∈ Set.Icc I.1 I.2, y = pR a}  -- polyZonotope(R.c,R.G,[],R.E)
  | some none => some ∅                                   -- R = []
  | none => none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
