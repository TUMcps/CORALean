module

public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard

@[expose] public section

/-!
# `LinearSysDT.reachLTVCora`, CORA's `reach` for a time-varying `linearSysDT`

The loop of `@linearSysDT/reach.m` [1] at the default `linAlg = 'standard'` for a time-varying
system (cells `A`, `B`, MATLAB's `A{i}` here `A i`), after `postProcessing` has split the input
into `U` and `uTrans` (or `uTransVec`). `EW` is `params.W = E*W` (l. 55). Entry `i` is
`(Rnext.tp, Uadd)` after `i` passes: `Uadd` is built once from `B{1}` (l. 75-76) and rebuilt
(l. 140-145) only when there is a `uTransVec`, and then from `B{i}` with `uTransVec(:,i+1)`, the
input of pass `i + 1`. `reduce` is `'girard'` at order `o`; the output set is not modelled.

# CORA's time-varying `linearSysDT` `reach` applies `B{1}` where `B{2}` acts

`linearSysDT({1,1,1}, {0,1,1}, [], {1,1,1}, {0,0,0}, 1)` (cells: `A{i} = 1`, `B{1} = 0`,
`B{2} = B{3} = 1`, `C{i} = 1`, `D{i} = 0`, `c`, `k`, `E`, `F` empty as the constructor demands for
cells), `R0 = {0}`, `tFinal = 2`, with `U = {1}` (`postProcessing` makes it `U = {0}`,
`uTrans = 1`) or with `U = {0}` and an input trajectory whose first two columns are `1`
(`uTransVec`). CORA's own `simulate` steps `x(i+1) = A{i} x(i) + B{i} u(i)`, so the run under
`u ≡ 1` is `0, 0, 1`. `reach` builds `Uadd` from `B{1}` and, without `uTransVec`, never again;
with it, it rebuilds `Uadd` after pass `i` from `B{i}`, so pass `2` again uses `B{1} = 0`. Either
way `LinearSysDT.reachLTVCora` reaches `{0}` at step `2` (all sets are points, so `reduce` at any
order is the identity), and `x(2) = 1` is missed; `C = 1`, `D = 0` make it the output too.
The hypothesis on `uTransVec` only makes `u ≡ 1` the user's input: `B{1} = 0` gives `{0}` for any.

## References

* [1] `contDynamics/@linearSysDT/reach.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `(Rnext.tp, Uadd)` after `i` passes of `reach`'s loop for the cells `A`, `B`, offset
`c`, `params.W = EW`, `R0`, `params.U = U`, and `params.uTrans` or `params.uTransVec`. -/
noncomputable def LinearSysDT.reachLTVCora (A : ℕ → Mat ℝ n n) (B : ℕ → Mat ℝ n m)
    (c : Vec ℝ n) (EW R0 : Zonotope (Vec ℝ n)) (U : Zonotope (Vec ℝ m)) (uTrans : Vec ℝ m)
    (uTransVec : Option (ℕ → Vec ℝ m)) (o : ℕ) : ℕ → Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n)
  | 0 =>
    let uTrans₁ := uTransVec.elim uTrans (· 1)          -- params.uTrans = params.uTransVec(:,1)
    let Uadd := (U.plus (Zonotope.ofPoint uTrans₁)).mtimes (B 1)  -- Uadd = B{1}*(U+uTrans)
    let Rnext := R0                                     -- Rnext.tp = params.X₀
    (Rnext, Uadd)
  | i + 1 =>
    let prev := LinearSysDT.reachLTVCora A B c EW R0 U uTrans uTransVec o i
    let Uadd := prev.2
    -- pass `i + 1`: Rnext.tp = A{i}*Rnext.tp + Uadd + linsysDT.c + params.W, then reduce
    let Rnext := (((prev.1.mtimes (A (i + 1))).plus Uadd).plus (Zonotope.ofPoint c)).plus EW
    let Rnext := Rnext.reduceGirard o
    -- if isfield(params,'uTransVec'): uTrans = uTransVec(:,i+1); Uadd = B{i}*(U + uTrans)
    let Uadd := uTransVec.elim Uadd fun v =>
      (U.plus (Zonotope.ofPoint (v (i + 2)))).mtimes (B (i + 1))
    (Rnext, Uadd)

end CORALean.Real

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The run `0, 0, 1` of `x(i+1) = A{i} x(i) + B{i}·1` is at `1` at step `2`, outside CORA's set
there, with `uTrans = 1` or any `uTransVec` whose first two columns are `1`, at any order `o`. -/
theorem LinearSysDT.reachLTVCora_counterexample (o : ℕ) (uTransVec : Option (ℕ → Vec ℝ 1))
    (hu : ∀ v, uTransVec = some v → v 1 = (fun _ => 1) ∧ v 2 = fun _ => 1) :
    let A : ℕ → Mat ℝ 1 1 := fun _ => 1
    let B : ℕ → Mat ℝ 1 1 := fun i => if i = 1 then 0 else 1
    let x : ℕ → Vec ℝ 1 := fun i => if i ≤ 1 then 0 else fun _ => 1
    let u : Vec ℝ 1 := fun _ => 1
    (x 0 = 0 ∧ ∀ i < 2, x (i + 1) = A (i + 1) *ᵥ x i + B (i + 1) *ᵥ u) ∧
      x 2 ∉ (LinearSysDT.reachLTVCora A B 0 (Zonotope.ofPoint 0) (Zonotope.ofPoint 0)
        (Zonotope.ofPoint 0) u uTransVec o 2).1.construct := by -- --- PROOF ---
  intro A B x u
  refine ⟨⟨rfl, fun i hi => ?_⟩, ?_⟩
  -- the run: `x(1) = 1·0 + 0·1`, `x(2) = 1·0 + 1·1`
  · rcases i with _ | _ | i
    · funext j
      simp [x, A, B, u]
    · funext j
      simp [x, A, B, u]
    · omega
  -- CORA's set at step `2` is the point `0`
  rintro ⟨β, -, hx⟩
  have h0 := congrFun hx 0
  -- `B{1} = 0` annihilates whichever input `Uadd` carries
  cases uTransVec <;>
    simp [x, A, B, u, LinearSysDT.reachLTVCora, Zonotope.reduceGirard, Zonotope.plus,
      Zonotope.mtimes, Zonotope.ofPoint] at h0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
