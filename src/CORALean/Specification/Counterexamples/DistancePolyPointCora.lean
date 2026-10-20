module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# `distancePolyPointCora`: CORA's `aux_distancePolyPoint` as printed

CORA's `aux_distancePolyPoint(C,d,p)` (`specification/@specification/robustness.m`, l. 189-224)
gives the distance of a point `p` outside the polytope `C x ≤ d`, "the norm 1 distance". It
branches on the violated rows `ind = find(C*p - d > 0)`: one row, the Euclidean distance to that
hyperplane; `n` rows, the Euclidean distance to the vertex `linsolve(C(ind,:),d(ind))`; otherwise
the linear program `min ‖p - x‖₁ s.t. C x ≤ d`. `linsolve` is a solution of the square system when
one exists, the program the infimum of `‖p - x‖₁`. Read from the source, not run.

# CORA's `aux_distancePolyPoint` mixes the Euclidean norm and the norm 1

On the unit cube `[0,1]³`, `p = (2,2,½)` violates two rows, so the norm-1 program returns `2`,
though `(1,1,½)` of the cube is at Euclidean distance `√2 < 2`. `p' = (2,2,2)` violates three rows
and gets the Euclidean `√3` to the vertex `(1,1,1)`, smaller although `p'` is further out. The
`robustness` of a safe set negates the value, so the sign is right and the magnitude wrong.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the distance is the norm 1 for one point but Euclidean for a farther one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The six normalized rows `±e_j` of the unit cube. -/
def Specification.aux_cubeRows : Fin 6 → Fin 3 → ℝ :=
  fun i j => if i.val = j.val then 1 else if i.val = j.val + 3 then -1 else 0

/-- The offsets of the unit cube `[0,1]³`. -/
def Specification.aux_cubeOffsets : Fin 6 → ℝ := fun i => if i.val < 3 then 1 else 0


-- =======================================  MAIN THEOREM  ======================================= --

theorem Specification.distancePolyPointCora_norm_counterexample : -- --- CONCL ---
    Specification.distancePolyPointCora Specification.aux_cubeRows Specification.aux_cubeOffsets
        ![2, 2, 1 / 2] = 2 ∧
      Specification.distancePolyPointCora Specification.aux_cubeRows Specification.aux_cubeOffsets
        ![2, 2, 2] = Real.sqrt 3 ∧
      Real.sqrt 3 < 2 ∧
      Real.sqrt ((1 - 2) ^ 2 + (1 - 2) ^ 2 + (1 / 2 - 1 / 2) ^ 2) < 2 := by -- --- PROOF ---
  -- The violated rows of `p = (2,2,½)` are the first two, those of `p' = (2,2,2)` the first three.
  have h1 : Finset.univ.filter (fun i : Fin 6 =>
      0 < (∑ j, Specification.aux_cubeRows i j * (![2, 2, 1 / 2] : Fin 3 → ℝ) j) -
        Specification.aux_cubeOffsets i) = {0, 1} := by
    ext i
    fin_cases i <;>
      simp [Specification.aux_cubeRows, Specification.aux_cubeOffsets, Fin.sum_univ_succ]
    all_goals norm_num
  have h2 : Finset.univ.filter (fun i : Fin 6 =>
      0 < (∑ j, Specification.aux_cubeRows i j * (![2, 2, 2] : Fin 3 → ℝ) j) -
        Specification.aux_cubeOffsets i) = {0, 1, 2} := by
    ext i
    fin_cases i <;>
      simp [Specification.aux_cubeRows, Specification.aux_cubeOffsets, Fin.sum_univ_succ]
  refine ⟨?_, ?_, ?_, ?_⟩
  -- Two violated rows: the program, whose optimum is the vertex `(1,1,½)` at norm 1 distance 2.
  · unfold Specification.distancePolyPointCora
    simp only [h1]
    rw [if_neg (by decide), if_neg (by decide)]
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨![1, 1, 1 / 2], ?_, ?_⟩
      · intro i
        fin_cases i <;> norm_num [Specification.aux_cubeRows, Specification.aux_cubeOffsets,
          Fin.sum_univ_succ]
      · simp [Fin.sum_univ_succ]; norm_num
    -- Lower bound: `x 0 ≤ 1` and `x 1 ≤ 1` cost one each.
    · rintro _ ⟨x, hx, rfl⟩
      have a := hx 0
      have b := hx 1
      simp [Specification.aux_cubeRows, Specification.aux_cubeOffsets, Fin.sum_univ_succ] at a b
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
      simp
      have c0 : 1 ≤ |2 - x 0| := by rw [abs_of_nonneg (by linarith)]; linarith
      have c1 : 1 ≤ |2 - x 1| := by rw [abs_of_nonneg (by linarith)]; linarith
      have c2 := abs_nonneg (1 / 2 - x 2)
      linarith
  -- Three violated rows: the vertex `(1,1,1)` of the violated hyperplanes, at distance `√3`.
  · unfold Specification.distancePolyPointCora
    simp only [h2]
    rw [if_neg (by decide), if_pos (by decide)]
    have hex : ∃ v : Fin 3 → ℝ, ∀ i ∈ ({0, 1, 2} : Finset (Fin 6)),
        ∑ j, Specification.aux_cubeRows i j * v j = Specification.aux_cubeOffsets i :=
      ⟨![1, 1, 1], by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl <;>
          simp [Specification.aux_cubeRows, Specification.aux_cubeOffsets, Fin.sum_univ_succ]⟩
    -- The square system of the three violated rows has the single solution `(1,1,1)`.
    have key : ∀ v : Fin 3 → ℝ, (∀ i ∈ ({0, 1, 2} : Finset (Fin 6)),
        ∑ j, Specification.aux_cubeRows i j * v j = Specification.aux_cubeOffsets i) →
          v = ![1, 1, 1] := by
      intro v hs
      have e0 := hs 0 (by simp)
      have e1 := hs 1 (by simp)
      have e2 := hs 2 (by simp)
      simp [Specification.aux_cubeRows, Specification.aux_cubeOffsets, Fin.sum_univ_succ]
        at e0 e1 e2
      ext j
      fin_cases j <;> simp [e0, e1, e2]
    have hv := key _ (Classical.epsilon_spec hex)
    rw [hv]
    congr 1
    simp [Fin.sum_univ_succ]
    norm_num
  -- The two numeric comparisons.
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
