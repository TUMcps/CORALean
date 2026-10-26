module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.Global.Tensor
public import Mathlib.Data.Finset.Fold
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# A halfspace description's shadow is one

Fourier–Motzkin elimination: the projection of `{(x, y) | rows}` onto `x`, `y ∈ ℝᵏ`, is again
the solution set of finitely many inequalities in `x`. One variable at a time, the rows that do
not mention it are kept, and each row bounding it from above is added to each row bounding it
from below, scaled so it cancels. Equalities enter as two inequalities each.

What [1, Thm. 1]'s "clearly, every constrained zonotope is a convex polytope" rests on: a
constrained zonotope is the shadow of the polytope `{(x, ξ) | x = c + Gξ, ‖ξ‖∞ ≤ 1, ξ ∈ P}`.
An existence theorem, not an algorithm: the elimination squares the row count per variable.

## Inputs
* `α` – type
* `k` – natural number
* `P` – H-polytope

## Hypotheses
* none

## Conclusion
* A halfspace description's shadow is one

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

open Classical in
/-- Fourier–Motzkin, one variable: the rows not involving `t`, and every row bounding `t` from
above against every row bounding it from below. -/
private theorem aux_fm {β ι : Type} [AddCommGroup β] [Module ℝ β] [Fintype ι]
    (F : ι → (β × ℝ →ₗ[ℝ] ℝ)) (c : ι → ℝ) : -- --- CONCL ---
    ∃ (κ : Type) (_ : Fintype κ) (A : κ → (β →ₗ[ℝ] ℝ)) (b : κ → ℝ),
      ∀ x, (∀ k, A k x ≤ b k) ↔ ∃ t : ℝ, ∀ i, F i (x, t) ≤ c i := by -- --- PROOF ---
  -- each row as `g x + a t`
  set g : ι → (β →ₗ[ℝ] ℝ) := fun i => (F i).comp (LinearMap.inl ℝ β ℝ)
  set a : ι → ℝ := fun i => F i (0, 1)
  have hsplit : ∀ i x t, F i (x, t) = g i x + a i * t := by
    intro i x t
    have : (x, t) = LinearMap.inl ℝ β ℝ x + t • ((0 : β), (1 : ℝ)) := by simp
    rw [this, map_add, map_smul, smul_eq_mul]; simp [g, a, mul_comm]
  -- rows free of `t`, and every positive row against every negative one
  refine ⟨ι ⊕ (ι × ι), inferInstance,
    fun k => match k with
      | Sum.inl i => if a i = 0 then g i else 0
      | Sum.inr (i, j) => if 0 < a i ∧ a j < 0 then (-a j) • g i + a i • g j else 0,
    fun k => match k with
      | Sum.inl i => if a i = 0 then c i else 0
      | Sum.inr (i, j) => if 0 < a i ∧ a j < 0 then (-a j) * c i + a i * c j else 0, ?_⟩
  intro x
  constructor
  · intro h
    set u : ι → ℝ := fun i => (c i - g i x) / a i
    set pos := Finset.univ.filter fun i => 0 < a i
    set neg := Finset.univ.filter fun j => a j < 0
    set t := neg.fold max (pos.fold min 0 u) u
    -- each lower bound under each upper bound
    have hpair : ∀ i ∈ pos, ∀ j ∈ neg, u j ≤ u i := by
      intro i hi j hj
      simp only [pos, neg, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      have := h (Sum.inr (i, j))
      simp only [hi, hj, and_self, if_true, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul] at this
      simp only [u]
      rw [div_le_iff_of_neg hj, div_mul_eq_mul_div, div_le_iff₀ hi]
      nlinarith
    refine ⟨t, fun i => ?_⟩
    rw [hsplit]
    rcases lt_trichotomy (a i) 0 with hneg | hzero | hpos
    · -- a lower bound: `t` is at least it
      have hti : u i ≤ t := (Finset.le_fold_max _).mpr
        (Or.inr ⟨i, by simp [neg, hneg], le_rfl⟩)
      have : a i * t ≤ a i * u i := mul_le_mul_of_nonpos_left hti hneg.le
      have hau : a i * u i = c i - g i x := by simp only [u]; field_simp [hneg.ne]
      linarith
    · have := h (Sum.inl i)
      simp only [hzero, if_true] at this
      rw [hzero, zero_mul, add_zero]; exact this
    · -- an upper bound: `t` is at most it
      have hipos : i ∈ pos := by simp [pos, hpos]
      have hti : t ≤ u i := (Finset.fold_max_le _).mpr
        ⟨(Finset.fold_min_le _).mpr (Or.inr ⟨i, hipos, le_rfl⟩),
          fun j hj => hpair i hipos j hj⟩
      have : a i * t ≤ a i * u i := mul_le_mul_of_nonneg_left hti hpos.le
      have hau : a i * u i = c i - g i x := by simp only [u]; field_simp [hpos.ne']
      linarith
  · rintro ⟨t, ht⟩ k
    rcases k with i | ⟨i, j⟩
    · simp only
      split_ifs with h0
      · have := ht i; rw [hsplit, h0, zero_mul, add_zero] at this; exact this
      · simp
    · simp only
      split_ifs with hij
      · have hi := ht i; have hj := ht j
        rw [hsplit] at hi hj
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
        nlinarith [hij.1, hij.2]
      · simp

/-- Fourier–Motzkin, `k` variables, one at a time. -/
private theorem aux_fm_vec (k : ℕ) : -- --- CONCL ---
    ∀ {β ι : Type} [AddCommGroup β] [Module ℝ β] [Fintype ι]
    (F : ι → (β × (Fin k → ℝ) →ₗ[ℝ] ℝ)) (c : ι → ℝ),
    ∃ (κ : Type) (_ : Fintype κ) (A : κ → (β →ₗ[ℝ] ℝ)) (b : κ → ℝ),
      ∀ x, (∀ j, A j x ≤ b j) ↔ ∃ y : Fin k → ℝ, ∀ i, F i (x, y) ≤ c i := by -- --- PROOF ---
  induction k with
  | zero =>
    intro β ι _ _ _ F c
    refine ⟨ι, inferInstance, fun i => (F i).comp (LinearMap.inl ℝ β (Fin 0 → ℝ)), c, fun x => ?_⟩
    have h0 : ∀ y : Fin 0 → ℝ, y = 0 := fun y => funext fun j => j.elim0
    constructor
    · intro h; exact ⟨0, fun i => by simpa using h i⟩
    · rintro ⟨y, hy⟩ i; rw [h0 y] at hy; simpa using hy i
  | succ k ih =>
    intro β ι _ _ _ F c
    -- `((x, y'), t) ↦ (x, t :: y')`, linear
    let V : (β × (Fin k → ℝ)) × ℝ →ₗ[ℝ] (Fin (k + 1) → ℝ) :=
      { toFun := fun p => Fin.cons p.2 p.1.2
        map_add' := fun p q => by
          funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp
        map_smul' := fun a p => by
          funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp }
    let L : (β × (Fin k → ℝ)) × ℝ →ₗ[ℝ] β × (Fin (k + 1) → ℝ) :=
      ((LinearMap.fst ℝ β (Fin k → ℝ)).comp (LinearMap.fst ℝ _ ℝ)).prod V
    -- eliminate the first coordinate, then the other `k` by induction
    obtain ⟨κ₁, _, A₁, b₁, h₁⟩ := aux_fm (fun i => (F i).comp L) c
    obtain ⟨κ₂, _, A₂, b₂, h₂⟩ := ih A₁ b₁
    refine ⟨κ₂, inferInstance, A₂, b₂, fun x => (h₂ x).trans ?_⟩
    constructor
    · rintro ⟨y', hy'⟩
      obtain ⟨t, ht⟩ := (h₁ (x, y')).mp hy'
      exact ⟨Fin.cons t y', fun i => ht i⟩
    · rintro ⟨y, hy⟩
      refine ⟨Fin.tail y, (h₁ (x, Fin.tail y)).mpr ⟨y 0, fun i => ?_⟩⟩
      have : L ((x, Fin.tail y), y 0) = (x, y) := by
        show ((x, Fin.tail y).1, (Fin.cons (y 0) (Fin.tail y) : Fin (k + 1) → ℝ)) = (x, y)
        rw [Fin.cons_self_tail]
      show F i (L ((x, Fin.tail y), y 0)) ≤ c i
      rw [this]; exact hy i


-- =======================================  MAIN THEOREM  ======================================= --

/-- The projection of a halfspace description onto its first factor is a halfspace
description, by Fourier–Motzkin elimination of the `k` coordinates of the second. -/
theorem HPolytope.exists_construct_eq_image_fst {α : Type} [AddCommGroup α] [Module ℝ α]
    {k : ℕ} (P : HPolytope (α × Vec ℝ k)) : -- --- CONCL ---
    ∃ Q : HPolytope α, Q.construct = Prod.fst '' P.construct := by -- --- PROOF ---
  -- the rows, and each equality as two inequalities
  let F : Fin P.m ⊕ (Bool × Fin P.me) → (α × (Fin k → ℝ) →ₗ[ℝ] ℝ) := fun r => match r with
    | Sum.inl i => P.A i
    | Sum.inr (true, i) => P.Ae i
    | Sum.inr (false, i) => -P.Ae i
  let c : Fin P.m ⊕ (Bool × Fin P.me) → ℝ := fun r => match r with
    | Sum.inl i => P.b i
    | Sum.inr (true, i) => P.be i
    | Sum.inr (false, i) => -P.be i
  -- membership is the rows, the equalities read as two inequalities each
  have hF : ∀ y, y ∈ P.construct ↔ ∀ r, F r y ≤ c r := by
    intro y
    constructor
    · rintro ⟨h1, h2⟩ r
      rcases r with i | ⟨_ | _, i⟩
      · exact h1 i
      · simp [F, c, h2 i]
      · exact le_of_eq (h2 i)
    · intro h
      refine ⟨fun i => h (Sum.inl i), fun i => le_antisymm (h (Sum.inr (true, i))) ?_⟩
      have := h (Sum.inr (false, i))
      simp only [F, c, LinearMap.neg_apply, neg_le_neg_iff] at this
      exact this
  obtain ⟨κ, _, A, b, hAb⟩ := aux_fm_vec k F c
  -- the shadow, its rows numbered
  refine ⟨⟨Fintype.card κ, fun i => A ((Fintype.equivFin κ).symm i),
    fun i => b ((Fintype.equivFin κ).symm i), 0, Fin.elim0, Fin.elim0⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨h1, -⟩
    obtain ⟨y, hy⟩ := (hAb x).mp fun j => by
      simpa using h1 (Fintype.equivFin κ j)
    exact ⟨(x, y), (hF _).mpr hy, rfl⟩
  · rintro ⟨⟨_, y⟩, hy, rfl⟩
    refine ⟨fun i => (hAb _).mpr ⟨y, (hF _).mp hy⟩ _, fun i => i.elim0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
