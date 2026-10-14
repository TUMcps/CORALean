module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# `distancePolyPointCora`: CORA's `aux_distancePolyPoint` as printed

CORA's `aux_distancePolyPoint(C,d,p)` (`specification/@specification/robustness.m`, l. 189-224)
gives the distance of a point `p` outside the polytope `C x ≤ d` (rows normalized by
`normalizeConstraints`), under the comment "compute the norm 1 distance". It has three branches
on `ind = find(C*p - d > 0)`, the violated rows:

* one violated row: the value `C(i,:)*p - d(i)`, the Euclidean distance to that hyperplane;
* `n` violated rows: `v = linsolve(C(ind,:),d(ind))` and `sqrt(sum((v-p).^2))`, the Euclidean
  distance to the vertex `v` of the violated hyperplanes;
* otherwise the linear program `min sum(u+w) s.t. x + u - w = p, C x ≤ d, u, w ≥ 0`, which is
  `min ‖p - x‖₁ s.t. C x ≤ d`, the norm 1 distance.

Points are functions `Fin n → ℝ`. `linsolve` is modelled by a solution of the square system when
one exists (an arbitrary vector otherwise, the case MATLAB warns about), and the program by the
infimum of `‖p - x‖₁` over the polytope. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- CORA's `d` returned by `aux_distancePolyPoint(C,d,p)`, for `m` rows in dimension `n`. -/
noncomputable def Specification.distancePolyPointCora {m n : ℕ} (C : Fin m → Fin n → ℝ)
    (d : Fin m → ℝ) (p : Fin n → ℝ) : ℝ :=
  let halfspaceVals : Fin m → ℝ := fun i => (∑ j, C i j * p j) - d i  -- C*p - d
  let ind : Finset (Fin m) := Finset.univ.filter fun i => 0 < halfspaceVals i
  if ind.card = 1 then
    ∑ i ∈ ind, halfspaceVals i                                       -- halfspaceVals(ind(1))
  else if ind.card = n then
    let v : Fin n → ℝ :=                                             -- linsolve(C(ind,:),d(ind))
      Classical.epsilon fun v : Fin n → ℝ => ∀ i ∈ ind, ∑ j, C i j * v j = d i
    Real.sqrt (∑ j, (v j - p j) ^ 2)                                 -- sqrt(sum((v-p).^2))
  else
    sInf ((fun x : Fin n → ℝ => ∑ j, |p j - x j|) ''                 -- CORAlinprog: min ‖p-x‖₁
      {x | ∀ i, ∑ j, C i j * x j ≤ d i})

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
