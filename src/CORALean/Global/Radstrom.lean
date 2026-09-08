import CORALean.Global.Mathlib

/-!
# Rådström's cancellation law

`X + E ⊆ Y + E` gives `X ⊆ Y` once `E` is nonempty and bounded and `Y` is
convex and closed. It is the one tool an *inner* approximation needs: an outer
approximation is a sum, and cancellation is what takes the error term back off
again.

Here rather than under `ContSet/`, because nothing in it mentions a
representation, a `construct` or even a Minkowski difference — it is a statement
about a normed space, on a par with `Global/EuclideanNorm.lean`.

Mathlib has no form of this result, so the proof is written out: iterate
`a + eₖ = yₖ + eₖ₊₁`, telescope to `n • a + e₀ = ∑ yₖ + eₙ`, and read `a` as the
average of `y₁ … yₙ` — in `Y` by convexity — displaced by `(eₙ - e₀)/n`, which
boundedness sends to `0`. Closedness collects the limit.

Boundedness and not compactness of `E`: only `‖eₙ - e₀‖ ≤ 2M` is ever used.

## References

* [1] H. Rådström. "An embedding theorem for spaces of convex sets".
      Proc. Amer. Math. Soc. 3 (1952), pp. 165-169.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [NormedSpace ℝ α] in
/-- The two sequences the argument runs on: a point of `Y` and a fresh point of
`E` at every step, chosen once and iterated, so the recursion is `Function.iterate`
on the `E` component alone. -/
theorem aux_radstrom_seq {a e₀ : α} {Y E : Set α} (he₀ : e₀ ∈ E)
    (hstep : ∀ u ∈ E, ∃ v ∈ Y, ∃ w ∈ E, a + u = v + w) :
    ∃ y e : ℕ → α, e 0 = e₀ ∧ (∀ k, e k ∈ E) ∧ (∀ k, y k ∈ Y) ∧
      ∀ k, a + e k = y k + e (k + 1) := by -- --- PROOF ---
  -- the step, as a function on the subtypes, so that choice runs once
  have hpair : ∀ u : E, ∃ p : Y × E, a + (u : α) = (p.1 : α) + (p.2 : α) := by
    intro u
    obtain ⟨v, hv, w, hw, hvw⟩ := hstep u u.2
    exact ⟨(⟨v, hv⟩, ⟨w, hw⟩), hvw⟩
  choose F hF using hpair
  -- named pointwise rather than as a lambda, so no unfolding is needed below
  obtain ⟨step, hstepdef⟩ : ∃ s : E → E, ∀ u, s u = (F u).2 :=
    ⟨fun u => (F u).2, fun _ => rfl⟩
  refine ⟨fun k => ((F (step^[k] ⟨e₀, he₀⟩)).1 : α),
    fun k => ((step^[k] (⟨e₀, he₀⟩ : E)) : α), rfl,
    fun k => (step^[k] (⟨e₀, he₀⟩ : E)).2, fun k => (F (step^[k] ⟨e₀, he₀⟩)).1.2, fun k => ?_⟩
  -- one more iterate is one more application of `step`, which is `F`'s second component
  simp only [Function.iterate_succ_apply', hstepdef]
  exact hF _

/-- Summing `a + eₖ = yₖ + eₖ₊₁` over `k < n`: every `eₖ` in between cancels and
`n • a + e₀ = ∑ yₖ + eₙ` is left. -/
theorem aux_radstrom_telescope {a : α} {y e : ℕ → α}
    (hrec : ∀ k, a + e k = y k + e (k + 1)) (n : ℕ) :
    (n : ℝ) • a + e 0 = (∑ k ∈ Finset.range n, y k) + e n := by -- --- PROOF ---
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Nat.cast_succ, add_smul, one_smul]
      -- move the extra `a` next to `eₙ`, where the recursion step rewrites it
      calc (n : ℝ) • a + a + e 0
          = ((n : ℝ) • a + e 0) + a := by abel
        _ = ((∑ k ∈ Finset.range n, y k) + e n) + a := by rw [ih]
        _ = (∑ k ∈ Finset.range n, y k) + (a + e n) := by abel
        _ = (∑ k ∈ Finset.range n, y k) + (y n + e (n + 1)) := by rw [hrec n]
        _ = (∑ k ∈ Finset.range n, y k) + y n + e (n + 1) := by abel


-- =======================================  MAIN THEOREM  ======================================= --

/-- Rådström's cancellation law [1]: a bounded nonempty summand cancels against
a convex closed set. Neither convexity of `X` nor closedness of `E` is used. -/
theorem radstrom_cancel {X Y E : Set α} (hE : E.Nonempty) (hEb : Bornology.IsBounded E)
    (hYconv : Convex ℝ Y) (hYcl : IsClosed Y) (h : X + E ⊆ Y + E) : X ⊆ Y := by -- --- PROOF ---
  intro a ha
  obtain ⟨e₀, he₀⟩ := hE
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hEb
  -- every `a + e` with `e ∈ E` lands in `Y + E`, which is exactly the step to iterate
  obtain ⟨y, e, he0, heE, hyY, hrec⟩ := aux_radstrom_seq (a := a) he₀ fun u hu => by
    obtain ⟨v, hv, w, hw, hvw⟩ := Set.mem_add.mp (h (Set.add_mem_add ha hu))
    exact ⟨v, hv, w, hw, hvw.symm⟩
  -- the running average of the first `n + 1` points of `Y`, indexed so `n = 0` is already one
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → α, c = fun n : ℕ =>
      ((n : ℝ) + 1)⁻¹ • ∑ k ∈ Finset.range (n + 1), y k := ⟨_, rfl⟩
  have hcY : ∀ n : ℕ, c n ∈ Y := by
    intro n
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hsum : c n = ∑ k ∈ Finset.range (n + 1), ((n : ℝ) + 1)⁻¹ • y k := by
      simp only [hcdef, Finset.smul_sum]
    rw [hsum]
    refine hYconv.sum_mem (fun i _ => by positivity) ?_ fun i _ => hyY i
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    field_simp
  -- the telescope, divided by `n + 1`: the average misses `a` by the error term alone
  have hdiff : ∀ n : ℕ, c n - a = ((n : ℝ) + 1)⁻¹ • (e 0 - e (n + 1)) := by
    intro n
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    have ht := aux_radstrom_telescope hrec (n + 1)
    push_cast at ht
    have hS : (∑ k ∈ Finset.range (n + 1), y k) = ((n : ℝ) + 1) • a + e 0 - e (n + 1) := by
      rw [ht]; abel
    simp only [hcdef, hS]
    rw [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hne, one_smul, smul_sub]
    abel
  -- `‖e 0 - e (n + 1)‖ ≤ 2M` is the only thing boundedness is asked for
  have hnb : ∀ n : ℕ, ‖c n - a‖ ≤ ((n : ℝ) + 1)⁻¹ * (2 * M) := by
    intro n
    have hpos : (0:ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
    rw [hdiff n, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ‖e 0 - e (n + 1)‖
        ≤ ‖e 0‖ + ‖e (n + 1)‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hM _ (heE 0)) (hM _ (heE (n + 1)))
      _ = 2 * M := by ring
  -- the bound tends to zero, so the averages tend to `a`, and `Y` is closed
  have hzero : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * (2 * M)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using h1.mul_const (2 * M)
  have htend : Filter.Tendsto (fun n : ℕ => c n - a) Filter.atTop (nhds 0) :=
    squeeze_zero_norm hnb hzero
  exact hYcl.mem_of_tendsto (by simpa using htend.add_const a) (Filter.Eventually.of_forall hcY)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
