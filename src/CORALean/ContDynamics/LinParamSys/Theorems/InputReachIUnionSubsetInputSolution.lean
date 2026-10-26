module

public import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContSet.ContSet.Definitions.Interfaces
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# `inputSolution` holds the particulate reachable set of a whole interval matrix

[1, Prop. 2] in its corrected form, `R̄([0, r]) ⊆ ⊕ᵢ 𝒜ⁱr^{i+1}/(i+1)! V ⊕ E(r)·r·V`, each order
applied to `V` on its own. The left side ranges over every member `A ∈ 𝒜` and every `t ∈ [0, r]`:
at `t = r` it is `inputReach_subset_inputSolution`, and `0 ∈ V` brings every earlier time up to `r`
(`inputReach_mono`). The powers are `Interval.matPow`, formed as `𝒜·𝒜ᵏ`, where [1, Sec. III-B]
multiplies from left to right; both enclose `Aⁱ`, and the theorem is stated at the former.

## Inputs
* `sys` – system
* `r` – step length
* `η` – Taylor order
* `U` – input set

## Hypotheses
* `hr` – step length positive
* `hε` – order admissible at the interval matrix
* `h0` – origin in the input set

## Conclusion
* every input's contribution, at every member and every time of the step, lies in the enclosure

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control, 2007.
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.inputReach_iUnion_subset_inputSolution
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]
    (sys : LinParamSys ℐ n) {r : ℝ} (hr : 0 < r) (η : ℕ)
    (hε : ‖(Interval.smul r sys.A).absMax‖ / ((η : ℝ) + 2) < 1) {U : S n}
    (h0 : (0 : Vec ℝ n) ∈ construct U) : -- --- CONCL ---
    (⋃ A ∈ construct sys.A, ⋃ t ∈ Set.Icc (0:ℝ) r,
        (LinearSys.canonical A : LinearSys ℝ n).inputReach U t)
      ⊆ construct (sys.inputSolution r η U) := by -- --- PROOF ---
  simp only [Set.iUnion_subset_iff]
  intro A hA t ht
  have hbdd := CompactSet.isBounded_construct U
  -- `0 ∈ U`: what the input reaches by `t` it can still reach by `r`
  refine ((LinearSys.canonical A : LinearSys ℝ n).inputReach_mono hbdd h0 ht.1 ht.2).trans ?_
  -- the time point `r` at the member `A`, inside the box's enclosure
  exact sys.inputReach_subset_inputSolution hr η hε hA (ConvexSet.convex_construct U)
    (CompactSet.isClosed_construct U) hbdd (ConvexSet.convex_construct _)
    (CompactSet.isClosed_construct _) (CompactSet.isBounded_construct _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
