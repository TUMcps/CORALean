import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
import CORALean.ContSet.Zonotope.Real.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard

/-!
# `LinearSysDT.reachLTVCora`, CORA's `reach` for a time-varying `linearSysDT`

The loop of `@linearSysDT/reach.m` [1] at the default `linAlg = 'standard'` for a time-varying
system (cells `A`, `B`, MATLAB's `A{i}` here `A i`), after `postProcessing` has split the input
into `U` and `uTrans` (or `uTransVec`). `EW` is `params.W = E*W` (l. 55). Entry `i` is
`(Rnext.tp, Uadd)` after `i` passes: `Uadd` is built once from `B{1}` (l. 75-76) and rebuilt
(l. 140-145) only when there is a `uTransVec`, and then from `B{i}` with `uTransVec(:,i+1)`, the
input of pass `i + 1`. `reduce` is `'girard'` at order `o`; the output set is not modelled.

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


-- =====================================  MAIN DEFINITION  ====================================== --

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


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
