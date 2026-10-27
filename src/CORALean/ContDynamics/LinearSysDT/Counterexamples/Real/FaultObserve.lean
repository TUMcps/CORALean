module

public import CORALean.ContSet.Zonotope.Real.Operations.FaultObserve
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# With a sensor fault the observer zonotope misses the state

[1, Eq. 10] bounds `x_{k+1}` of the system [1, Eq. 3], whose output carries the sensor fault
`E f_k`. The fault enters the center through `y_k` and is accounted for nowhere else, so the
enclosure needs `f_k = 0` (`LinearSysDT.faultObserve_outer`). In one dimension with `A = B = 0`,
`C = L = E = 1`, no disturbance or noise, `X̂_k = {0}` and `x_k = 0`, a fault `f_k = 1` gives
`y_k = 1` and `X̂_{k+1} = {1}`, which misses `x_{k+1} = 0`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the observer zonotope misses the state under a sensor fault

## References

* [1] [Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer with
      H₋ Performance". 2017 36th Chinese Control Conference (CCC),
      2017.](../../../../../../references/2017/wang-ccc-fault-detection-observer.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.faultObserve_counterexample : -- --- CONCL ---
    let A : Mat ℝ 1 1 := 0
    let B : Mat ℝ 1 1 := 0
    let C : Mat ℝ 1 1 := 1
    let L : Mat ℝ 1 1 := 1
    let E : Mat ℝ 1 1 := 1
    let Dx : Mat ℝ 1 0 := 0
    let Hw : Mat ℝ 0 0 := 0
    let Dy : Mat ℝ 1 0 := 0
    let Hv : Mat ℝ 0 0 := 0
    let X : Zonotope (Vec ℝ 1) := ⟨0, 0, Fin.elim0⟩       -- `X̂_k = {0}`
    let x : Vec ℝ 1 := 0
    let f : Vec ℝ 1 := 1                                  -- the sensor fault
    let y := C *ᵥ x + E *ᵥ f                              -- Eq. 3b, no noise
    x ∈ X.construct ∧ A *ᵥ x + B *ᵥ 0 ∉
      (X.faultObserve A B C L Dx Hw Dy Hv 0 y).construct := by -- --- PROOF ---
  intro A B C L E Dx Hw Dy Hv X x f y
  refine ⟨⟨Fin.elim0, fun j => j.elim0, by simp [X, x]⟩, ?_⟩
  -- the zonotope has no generators and center `1`
  rintro ⟨b, -, hb⟩
  have := congrFun hb 0
  simp [Zonotope.faultObserve, A, B, C, L, E, X, x, f, y] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
