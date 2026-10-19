module

public import CORALean.Global.LinProg.Duality
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.LinearAlgebra.Prod

@[expose] public section

/-!
# Strong duality: Farkas' lemma

`Duality` proves the easy half: nonnegative weights bound every objective they
assemble. This is the other half — a bound that holds on a nonempty polyhedron
*has* such weights — which is what turns an LP encoding of a containment into an
equivalence rather than a sufficient condition.

The homogeneous form is Bartl's purely algebraic induction on the number of
rows: either the last row is not needed, or a point violating the reduced
system lets the last row be eliminated from all the others. Nothing about the
space is used, not even finite dimension. The affine form follows by
homogenizing over `E × ℝ`, and needs the polyhedron nonempty: `∅` satisfies
every bound, and is not always cut out by weights that assemble it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {E : Type} [AddCommGroup E] [Module ℝ E]

/-- Homogeneous Farkas: a functional nonnegative wherever the rows are is a
nonnegative combination of the rows. -/
theorem exists_nonneg_comb_of_forall_nonneg :
    ∀ (m : ℕ) (a : Fin m → (E →ₗ[ℝ] ℝ)) (c : E →ₗ[ℝ] ℝ),
      (∀ x, (∀ i, 0 ≤ a i x) → 0 ≤ c x) →
        ∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i) ∧ c = ∑ i, y i • a i := by -- --- PROOF ---
  intro m
  induction m with
  | zero =>
    intro a c h
    refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
    ext x
    have h1 := h x (fun i => i.elim0)
    have h2 := h (-x) (fun i => i.elim0)
    simp only [map_neg, Left.nonneg_neg_iff] at h2
    simp only [Finset.univ_eq_empty, Finset.sum_empty, LinearMap.zero_apply]
    linarith
  | succ m ih =>
    intro a c h
    let a' : Fin m → (E →ₗ[ℝ] ℝ) := fun i => a i.castSucc
    let l := a (Fin.last m)
    by_cases hcase : ∀ x, (∀ i, 0 ≤ a' i x) → 0 ≤ c x
    -- the last row is not needed: weight zero on it
    · obtain ⟨y, hy, hc⟩ := ih a' c hcase
      refine ⟨Fin.snoc y 0, fun i => ?_, ?_⟩
      · refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simpa using hy j
      · rw [Fin.sum_univ_castSucc, hc]
        simp [a']
    -- a point violating the reduced system eliminates the last row
    · push Not at hcase
      obtain ⟨x0, hx0, hcx0⟩ := hcase
      have ht : l x0 < 0 := by
        by_contra hge
        push Not at hge
        have := h x0 (fun i => Fin.lastCases hge (fun j => by simpa [a'] using hx0 j) i)
        linarith
      set t := l x0 with htdef
      let a'' : Fin m → (E →ₗ[ℝ] ℝ) := fun i => a' i - (a' i x0 / t) • l
      let c'' : E →ₗ[ℝ] ℝ := c - (c x0 / t) • l
      have hred : ∀ x, (∀ i, 0 ≤ a'' i x) → 0 ≤ c'' x := by
        intro x hx
        -- shift `x` along `x0` onto the kernel of the last row
        let x' := x - (l x / t) • x0
        have hl : l x' = 0 := by
          simp only [x', map_sub, map_smul, smul_eq_mul]
          rw [← htdef, div_mul_cancel₀ _ ht.ne, sub_self]
        have ha : ∀ i, a' i x' = a'' i x := by
          intro i
          simp only [x', a'', map_sub, map_smul, smul_eq_mul, LinearMap.sub_apply,
            LinearMap.smul_apply]
          ring
        have hall : ∀ i, 0 ≤ a i x' := fun i =>
          Fin.lastCases (by rw [hl]) (fun j => by
            have := hx j; rw [← ha j] at this; simpa [a'] using this) i
        have hc := h x' hall
        have : c x' = c'' x := by
          simp only [x', c'', map_sub, map_smul, smul_eq_mul, LinearMap.sub_apply,
            LinearMap.smul_apply]
          ring
        linarith
      obtain ⟨y, hy, hc⟩ := ih a'' c'' hred
      -- the weight the last row takes back, positive as a ratio of two negatives
      let μ := (c x0 - ∑ i, y i * a' i x0) / t
      have hnum : c x0 - ∑ i, y i * a' i x0 < 0 := by
        have : 0 ≤ ∑ i, y i * a' i x0 :=
          Finset.sum_nonneg fun i _ => mul_nonneg (hy i) (hx0 i)
        linarith
      have hμ : 0 ≤ μ := le_of_lt (div_pos_of_neg_of_neg hnum ht)
      refine ⟨Fin.snoc y μ, fun i => ?_, ?_⟩
      · refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hμ
        · simpa using hy j
      -- `c = c'' + (c x₀ / t) l` regroups into the old rows plus `μ` on the last
      · ext x
        have hcx := congrArg (fun f : E →ₗ[ℝ] ℝ => f x) hc
        simp only [c'', a'', LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
          LinearMap.sum_apply] at hcx
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, LinearMap.add_apply, LinearMap.sum_apply,
          LinearMap.smul_apply, smul_eq_mul]
        show c x = ∑ i, y i * a' i x + μ * l x
        have hsplit : ∑ i, y i * (a' i x - a' i x0 / t * l x)
            = ∑ i, y i * a' i x - (∑ i, y i * a' i x0) / t * l x := by
          rw [Finset.sum_div, Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        have hμl : μ * l x = c x0 / t * l x - (∑ i, y i * a' i x0) / t * l x := by
          simp only [μ]; ring
        rw [hsplit] at hcx
        linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- Affine Farkas: a bound `c x ≤ d` holding on a nonempty `{x | A x ≤ b}` is
assembled by nonnegative weights on the rows. -/
theorem exists_dual_of_forall_le {m : ℕ} (A : Fin m → (E →ₗ[ℝ] ℝ)) (b : Fin m → ℝ)
    (c : E →ₗ[ℝ] ℝ) (d : ℝ) (hne : ∃ x0, ∀ i, A i x0 ≤ b i)
    (h : ∀ x, (∀ i, A i x ≤ b i) → c x ≤ d) : -- --- CONCL ---
    ∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i) ∧ c = ∑ i, y i • A i ∧
      ∑ i, y i * b i ≤ d := by -- --- PROOF ---
  obtain ⟨x0, hx0⟩ := hne
  -- homogenize: `(x, t)` stands for `x / t`, the extra row being `t ≥ 0`
  let fst : E × ℝ →ₗ[ℝ] E := LinearMap.fst ℝ E ℝ
  let snd : E × ℝ →ₗ[ℝ] ℝ := LinearMap.snd ℝ E ℝ
  let a : Fin (m + 1) → (E × ℝ →ₗ[ℝ] ℝ) :=
    Fin.snoc (fun i => b i • snd - (A i).comp fst) snd
  let c' : E × ℝ →ₗ[ℝ] ℝ := d • snd - c.comp fst
  have hhom : ∀ p, (∀ i, 0 ≤ a i p) → 0 ≤ c' p := by
    rintro ⟨x, t⟩ hp
    have ht : 0 ≤ t := by simpa [a, snd] using hp (Fin.last m)
    have hrow : ∀ i, A i x ≤ b i * t := fun i => by
      have := hp i.castSucc
      simp only [a, Fin.snoc_castSucc, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, smul_eq_mul, fst, snd, LinearMap.fst_apply,
        LinearMap.snd_apply] at this
      linarith
    simp only [c', LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      smul_eq_mul, fst, snd, LinearMap.fst_apply, LinearMap.snd_apply]
    rcases ht.lt_or_eq with htpos | ht0
    -- `t > 0`: `x / t` is feasible
    · have hfeas : ∀ i, A i (t⁻¹ • x) ≤ b i := fun i => by
        rw [map_smul, smul_eq_mul]
        have := hrow i
        rw [inv_mul_le_iff₀ htpos]
        linarith
      have := h _ hfeas
      rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ htpos] at this
      linarith
    -- `t = 0`: `x` is a recession direction, so `c x > 0` would make `c` unbounded
    · subst ht0
      have hA : ∀ i, A i x ≤ 0 := fun i => by simpa using hrow i
      by_contra hneg
      push Not at hneg
      have hcx : 0 < c x := by linarith
      have hd : c x0 ≤ d := h x0 hx0
      set s := (d - c x0 + 1) / c x with hs
      have hs0 : 0 ≤ s := div_nonneg (by linarith) hcx.le
      have hfeas : ∀ i, A i (x0 + s • x) ≤ b i := fun i => by
        rw [map_add, map_smul, smul_eq_mul]
        nlinarith [hx0 i, hA i]
      have := h _ hfeas
      rw [map_add, map_smul, smul_eq_mul, hs, div_mul_cancel₀ _ hcx.ne'] at this
      linarith
  obtain ⟨y, hy, hc⟩ := exists_nonneg_comb_of_forall_nonneg (m + 1) a c' hhom
  refine ⟨fun i => y i.castSucc, fun i => hy _, ?_, ?_⟩
  -- read the combination off at `(x, 0)` and at `(0, 1)`
  · ext x
    have := congrArg (fun f : E × ℝ →ₗ[ℝ] ℝ => f (x, 0)) hc
    simp only [c', a, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, fst, snd,
      LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.add_apply, LinearMap.sum_apply,
      mul_zero, zero_sub] at this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    have h2 : ∑ i : Fin m, y i.castSucc * -(A i) x = -∑ i : Fin m, y i.castSucc * A i x := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2] at this
    linarith
  · have := congrArg (fun f : E × ℝ →ₗ[ℝ] ℝ => f (0, 1)) hc
    simp only [c', a, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, fst, snd,
      LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.add_apply, LinearMap.sum_apply,
      map_zero, sub_zero, mul_one] at this
    have := hy (Fin.last m)
    linarith

/-- The same over any finite index of rows, by renumbering them. -/
theorem exists_dual_of_forall_le_fintype {ι : Type} [Fintype ι] (A : ι → (E →ₗ[ℝ] ℝ))
    (b : ι → ℝ) (c : E →ₗ[ℝ] ℝ) (d : ℝ) (hne : ∃ x0, ∀ i, A i x0 ≤ b i)
    (h : ∀ x, (∀ i, A i x ≤ b i) → c x ≤ d) : -- --- CONCL ---
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ c = ∑ i, y i • A i ∧
      ∑ i, y i * b i ≤ d := by -- --- PROOF ---
  let e := Fintype.equivFin ι
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨y, hy, hc, hb⟩ := exists_dual_of_forall_le (fun k => A (e.symm k)) (fun k => b (e.symm k))
    c d ⟨x0, fun k => hx0 _⟩ (fun x hx => h x fun i => by simpa using hx (e i))
  refine ⟨fun i => y (e i), fun i => hy _, ?_, ?_⟩
  · rw [hc]
    exact Fintype.sum_equiv e.symm _ _ fun k => by simp
  · calc ∑ i, y (e i) * b i = ∑ k, y k * b (e.symm k) :=
          Fintype.sum_equiv e _ _ fun i => by simp
      _ ≤ d := hb

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
