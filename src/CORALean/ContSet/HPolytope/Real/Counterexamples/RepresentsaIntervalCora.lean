module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `HPolytope.representsaIntervalCora`: the `'interval'` test as CORA's code computes it

`@polytope/representsa_.m`, branch `'interval'` (`aux_isInterval`, l. 236-312), builds the
interval `I = [lb, ub]` from the axis-aligned rows, then walks the other rows `a x ≤ b`:
`supportFunc_(I, a, 'upper') <= b` makes the row redundant, `supportFunc_(I, a, 'lower') > b`
returns `true` with the empty interval, and otherwise ("cuts through the interval... only hope
now is that the polytope is empty") it returns `representsa_(P, 'emptySet')`.

This models that walk for one non-axis-aligned row `(a, b)` over the box `[lb, ub]`, with the
two support-function values in their closed form for a box. `True` stands for `res = true`
(either `true` return, or the loop ending with every row redundant). Read from the source,
not run.

# CORA's `polytope/representsa_(P, 'interval')` rejects the point `{0}`

`P = {0 ≤ x ≤ 2, 0 ≤ y ≤ 2, x + y ≤ 0}` is the point `(0, 0)`, the degenerate interval
`[0, 0]²`. CORA builds `I = [0, 2]²` from the axis-aligned rows; the row `x + y ≤ 0` has upper
support value `4 > 0` and lower value `0 ≤ 0`, so it "cuts through" and CORA returns
`representsa_(P, 'emptySet')`, which is `false` since `P` is nonempty. A false negative, not
unsound. Read from the source, not run.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the polytope is the interval `[0, 0]²`, yet CORA does not accept it as an interval
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's answer for `representsa_(P, 'interval')` when the axis-aligned rows give the box
`[lb, ub]` and `(a, b)` is the only non-axis-aligned row. -/
noncomputable def HPolytope.representsaIntervalCora (P : HPolytope (Fin n → ℝ))
    (lb ub a : Fin n → ℝ) (b : ℝ) : Prop :=
  let upper := ∑ i, if 0 ≤ a i then a i * ub i else a i * lb i  -- supportFunc_(I,a,'upper')
  let lower := ∑ i, if 0 ≤ a i then a i * lb i else a i * ub i  -- supportFunc_(I,a,'lower')
  if upper ≤ b then True                 -- constraint is redundant
  else if b < lower then True            -- empty: `res = true; I = interval.empty(n)`
  else P.construct = ∅                   -- `res = representsa_(P,'emptySet',tol)`

end CORALean.Real

namespace CORALean.Real


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The square `[0, 2]²` cut by the row `x + y ≤ 0`. -/
@[step_of HPolytope.representsa_interval_cora_counterexample]
def HPolytope.step_squareCut : HPolytope (Fin 2 → ℝ) where
  m := 5
  A := let p0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
    let p1 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 1
    ![p0, -p0, p1, -p1, p0 + p1]
  b := ![2, 0, 2, 0, 0]
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0


-- =======================================  MAIN THEOREM  ======================================= --

/-- The polytope is the interval `[0, 0]²`, yet CORA does not accept it as an interval. -/
theorem HPolytope.representsa_interval_cora_counterexample : -- --- CONCL ---
    HPolytope.step_squareCut.construct = Set.Icc (0 : Fin 2 → ℝ) 0 ∧
      ¬ HPolytope.step_squareCut.representsaIntervalCora 0 (fun _ => 2) ![1, 1]
        0 := by -- --- PROOF ---
  -- the five rows pin both coordinates to `0`
  have hc : HPolytope.step_squareCut.construct = Set.Icc (0 : Fin 2 → ℝ) 0 := by
    ext x
    constructor
    · rintro ⟨h, -⟩
      have h0 := h (0 : Fin 5)
      have h1 := h (1 : Fin 5)
      have h2 := h (2 : Fin 5)
      have h3 := h (3 : Fin 5)
      have h4 := h (4 : Fin 5)
      simp [HPolytope.step_squareCut] at h0 h1 h2 h3 h4
      refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simp <;> linarith
    · rintro ⟨h0, h1⟩
      have a0 : x 0 = 0 := le_antisymm (h1 0) (h0 0)
      have a1 : x 1 = 0 := le_antisymm (h1 1) (h0 1)
      refine ⟨fun (i : Fin 5) => ?_, fun i => i.elim0⟩
      fin_cases i <;> simp [HPolytope.step_squareCut, a0, a1]
  -- the cut row is neither redundant nor excluding, so CORA asks for emptiness; `0` is a point
  refine ⟨hc, fun h => ?_⟩
  have h0 : (0 : Fin 2 → ℝ) ∈ HPolytope.step_squareCut.construct := by
    rw [hc]; exact ⟨le_rfl, le_rfl⟩
  unfold HPolytope.representsaIntervalCora at h
  simp [Fin.sum_univ_two] at h
  rw [h] at h0
  exact h0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
