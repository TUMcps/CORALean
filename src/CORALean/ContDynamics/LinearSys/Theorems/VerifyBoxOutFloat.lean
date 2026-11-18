module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyZonoGenSet
public import CORALean.ContDynamics.LinearSys.Operations.VerifyBoxOutFloat
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List

@[expose] public section

/-!
# `LinearSys.verifyBoxOutFloat` encloses what it was given

A point spanned by the generators plus a point of the box `b` is a point spanned by the generators
that stay plus a point of the new box: `β g` with `|β| ≤ 1` lies in the box `|g|`, and the box's
radius `b + Σ |g|` over the generators that leave is rounded up.

## Inputs
* `L` – float generators with their flags
* `b` – float radius of the box
* `y` – point spanned by the generators
* `e` – point of the box

## Hypotheses
* `hy` – `y` is spanned by the generators
* `he` – `e` lies in the box

## Conclusion
* `y + e` is a point spanned by the generators that stay plus a point of the new box
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A left fold of upward additions is at least its seed plus the sum of the terms. -/
private theorem LinearSys.aux_le_foldl_addUp'' {α : Type} (f : α → 𝕋) : -- --- CONCL ---
    ∀ (L : List α) (a : 𝕋),
      toReal a + (L.map fun x => toReal (f x)).sum
        ≤ toReal (L.foldl (fun acc x => addUp acc (f x)) a) := by -- --- PROOF ---
  intro L
  induction L with
  | nil => intro a; simp
  | cons x L ih =>
    intro a
    simp only [List.map_cons, List.sum_cons, List.foldl_cons]
    have := ih (addUp a (f x))
    linarith [add_le_addUp a (f x)]

/-- The span splits into the span of the kept generators and a point within the magnitudes of the
others. -/
private theorem LinearSys.aux_split : -- --- CONCL ---
    ∀ (L : List (Vec 𝕋 n × Bool)) {y : Vec ℝ n},
      y ∈ LinearSys.verifyZonoGenSet ((L.map Prod.fst).map toRealVec) →
      ∃ y' ∈ LinearSys.verifyZonoGenSet
          (((L.filter fun g => g.2).map Prod.fst).map toRealVec),
        ∃ d : Vec ℝ n, (∀ i, |d i| ≤ ((L.filter fun g => !g.2).map fun g =>
          |toReal (g.1 i)|).sum) ∧ y = y' + d := by -- --- PROOF ---
  intro L
  induction L with
  | nil =>
    intro y hy
    exact ⟨y, by simpa using hy, 0, fun i => by simp, by simp⟩
  | cons g L ih =>
    intro y hy
    obtain ⟨β, hβ, z, hz, rfl⟩ := hy
    obtain ⟨z', hz', d, hd, rfl⟩ := ih hz
    have hbg : ∀ i, |(β • toRealVec g.1) i| ≤ |toReal (g.1 i)| := fun i => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, toRealVec]
      exact le_trans (mul_le_mul_of_nonneg_right hβ (abs_nonneg _)) (by simp)
    cases hg : g.2
    · -- `g` leaves: `β g` joins the rest
      refine ⟨z', by simpa [List.filter_cons, hg] using hz', β • toRealVec g.1 + d, fun i => ?_,
        by abel⟩
      simp only [List.filter_cons, hg, Bool.not_false, if_true, List.map_cons, List.sum_cons,
        Pi.add_apply]
      exact le_trans (abs_add_le _ _) (add_le_add (hbg i) (hd i))
    · -- `g` stays
      refine ⟨β • toRealVec g.1 + z', ?_, d, fun i => ?_, by abel⟩
      · simp only [List.filter_cons, hg, if_true, List.map_cons]
        exact ⟨β, hβ, z', hz', rfl⟩
      · simpa [List.filter_cons, hg] using hd i


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.mem_verifyBoxOutFloat (L : List (Vec 𝕋 n × Bool)) (b : Vec 𝕋 n)
    {y e : Vec ℝ n} (hy : y ∈ LinearSys.verifyZonoGenSet ((L.map Prod.fst).map toRealVec))
    (he : ∀ i, |e i| ≤ toReal (b i)) : -- --- CONCL ---
    ∃ y' ∈ LinearSys.verifyZonoGenSet ((LinearSys.verifyBoxOutFloat L b).1.map toRealVec),
      ∃ e' : Vec ℝ n, (∀ i, |e' i| ≤ toReal ((LinearSys.verifyBoxOutFloat L b).2 i)) ∧
        y + e = y' + e' := by -- --- PROOF ---
  obtain ⟨y', hy', d, hd, rfl⟩ := LinearSys.aux_split L hy
  refine ⟨y', hy', d + e, fun i => ?_, by abel⟩
  simp only [LinearSys.verifyBoxOutFloat, Interval.materialise_eq, Pi.add_apply]
  have hf := LinearSys.aux_le_foldl_addUp'' (fun g : Vec 𝕋 n × Bool => absolute (g.1 i))
    (L.filter fun g => !g.2) zero
  rw [toReal_zero, zero_add] at hf
  have hsum : ((L.filter fun g => !g.2).map fun g => |toReal (g.1 i)|).sum
      = ((L.filter fun g => !g.2).map fun g => toReal (absolute (g.1 i))).sum := by
    congr 1; apply List.map_congr_left; intro g _; rw [toReal_absolute]
  have hadd := add_le_addUp (b i) ((L.filter fun g => !g.2).foldl (fun acc g =>
    addUp acc (absolute (g.1 i))) zero)
  have := abs_add_le (d i) (e i)
  change |d i + e i| ≤ toReal (addUp (b i) _)
  linarith [hd i, he i]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
