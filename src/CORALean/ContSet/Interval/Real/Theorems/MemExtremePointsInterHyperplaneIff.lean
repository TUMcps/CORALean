module

public import CORALean.ContSet.Interval.Real.Definitions.BoxPlane
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# The vertices of a box cut by a hyperplane lie on its edges

[1, Sec. 1]: the vertices of the polygon `B ∩ P` lie on the edges of `B`, perhaps at a vertex.
Exactly so: for a hyperplane `Σᵢ aᵢxᵢ = α` with every `aᵢ ≠ 0` — the paper's `Σᵢ xᵢ = α`, or a
scaled one of [1, Sec. 6.3 (scaling)] — the extreme points of `B ∩ P` are its points with at
most one coordinate strictly inside. Two such coordinates `i`, `j` leave the direction
`aⱼeᵢ - aᵢeⱼ` free inside `B ∩ P`; with one, `P` fixes it once the others are at their bounds.

## Inputs
* `I` – interval box
* `a` – normal vector of the plane
* `α` – level of the plane
* `x` – candidate vertex

## Hypotheses
* `ha` – normal entries nonzero

## Conclusion
* `x` is a vertex of the cut iff it lies in the cut and on an edge of the box

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection
      Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.mem_extremePoints_inter_hyperplane_iff {I : Interval (Vec ℝ n)} {a : Vec ℝ n}
    (ha : ∀ i, a i ≠ 0) {α : ℝ} {x : Vec ℝ n} : -- --- CONCL ---
    x ∈ Set.extremePoints ℝ (I.construct ∩ Interval.hyperplane a α) ↔
      x ∈ I.construct ∩ Interval.hyperplane a α ∧ I.IsOnEdge x := by -- --- PROOF ---
  constructor
  · -- two coordinates strictly inside: `x ± ε(aⱼeᵢ - aᵢeⱼ)` stay in `B ∩ P`
    intro hx
    refine ⟨hx.1, fun i j hij => ?_⟩
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨⟨hi1, hi2⟩, ⟨hj1, hj2⟩⟩ := hcon
    have hxI : ∀ k, I.inf k ≤ x k ∧ x k ≤ I.sup k := hx.1.1
    have hil : I.inf i < x i := lt_of_le_of_ne (hxI i).1 (Ne.symm hi1)
    have hiu : x i < I.sup i := lt_of_le_of_ne (hxI i).2 hi2
    have hjl : I.inf j < x j := lt_of_le_of_ne (hxI j).1 (Ne.symm hj1)
    have hju : x j < I.sup j := lt_of_le_of_ne (hxI j).2 hj2
    have hai : 0 < |a i| := abs_pos.mpr (ha i)
    have haj : 0 < |a j| := abs_pos.mpr (ha j)
    -- a step small enough for both coordinates
    set ε := min (min (x i - I.inf i) (I.sup i - x i) / |a j|)
      (min (x j - I.inf j) (I.sup j - x j) / |a i|) with hεdef
    have hε : 0 < ε := lt_min (div_pos (lt_min (by linarith) (by linarith)) haj)
      (div_pos (lt_min (by linarith) (by linarith)) hai)
    have hεi : ε * |a j| ≤ min (x i - I.inf i) (I.sup i - x i) :=
      (le_div_iff₀ haj).mp (min_le_left _ _)
    have hεj : ε * |a i| ≤ min (x j - I.inf j) (I.sup j - x j) :=
      (le_div_iff₀ hai).mp (min_le_right _ _)
    let d : Vec ℝ n := fun k => a j * (if k = i then 1 else 0) - a i * (if k = j then 1 else 0)
    have hd : ∑ k, a k * d k = 0 := by
      simp only [d, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    -- `x + s • d` for `|s| ≤ ε` is in `B ∩ P`
    have hmem : ∀ s : ℝ, |s| ≤ ε → x + s • d ∈ I.construct ∩ Interval.hyperplane a α := by
      intro s hs
      refine ⟨fun k => ?_, ?_⟩
      · change I.inf k ≤ x k + s * d k ∧ x k + s * d k ≤ I.sup k
        by_cases hki : k = i
        · subst hki
          have hdk : d k = a j := by simp [d, hij]
          rw [hdk]
          have h1 : |s * a j| ≤ ε * |a j| := by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
          have h2 := abs_le.mp (h1.trans hεi)
          constructor <;> linarith [min_le_left (x k - I.inf k) (I.sup k - x k),
            min_le_right (x k - I.inf k) (I.sup k - x k)]
        -- coordinate `j` moves by `-s aᵢ`, within its slack as well
        by_cases hkj : k = j
        · subst hkj
          have hdk : d k = -a i := by simp [d, hki]
          rw [hdk]
          have h1 : |s * -a i| ≤ ε * |a i| := by
            rw [abs_mul, abs_neg]; exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
          have h2 := abs_le.mp (h1.trans hεj)
          constructor <;> linarith [min_le_left (x k - I.inf k) (I.sup k - x k),
            min_le_right (x k - I.inf k) (I.sup k - x k)]
        · have hdk : d k = 0 := by simp [d, hki, hkj]
          rw [hdk, mul_zero, add_zero]
          exact hxI k
      -- on the plane: the direction `d` is orthogonal to `a`
      · have hxP : ∑ k, a k * x k = α := hx.1.2
        change ∑ k, a k * (x k + s * d k) = α
        simp only [mul_add, Finset.sum_add_distrib, hxP]
        have : ∑ k, a k * (s * d k) = s * ∑ k, a k * d k := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        rw [this, hd, mul_zero, add_zero]
    -- `x` is the midpoint of `x + εd` and `x - εd`, which differ from it
    have hseg : x ∈ openSegment ℝ (x + ε • d) (x + (-ε) • d) :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
        funext k; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring⟩
    have heq := (mem_extremePoints.mp hx).2 _ (hmem ε (by rw [abs_of_pos hε]))
      _ (hmem (-ε) (by rw [abs_neg, abs_of_pos hε])) hseg
    have hdi : (x + ε • d) i = x i := congrFun heq.1 i
    have hdi' : d i = a j := by simp [d, hij]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hdi', add_eq_left] at hdi
    exact (mul_ne_zero hε.ne' (ha j)) hdi
  · -- on an edge: a convex combination fixes every coordinate at a bound, and `P` the other
    rintro ⟨hxA, hedge⟩
    refine mem_extremePoints_iff_left.mpr ⟨hxA, fun y hy z hz hseg => ?_⟩
    obtain ⟨θ, η, hθ, hη, hθη, hxe⟩ := hseg
    -- coordinatewise, `x` is the convex combination of `y` and `z`
    have hcomb : ∀ k, θ * y k + η * z k = x k := fun k => by
      have := congrFun hxe k
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
    have hbound : ∀ k, (x k = I.inf k ∨ x k = I.sup k) → y k = x k := by
      intro k hk
      have hyk : I.inf k ≤ y k ∧ y k ≤ I.sup k := hy.1 k
      have hzk : I.inf k ≤ z k ∧ z k ≤ I.sup k := hz.1 k
      have hc := hcomb k
      -- a combination of two points of `[aₖ, bₖ]` reaches a bound only if both do
      rcases hk with h | h
      · rw [h] at hc ⊢
        have h1 : θ * (y k - I.inf k) + η * (z k - I.inf k) = 0 := by
          linear_combination hc - I.inf k * hθη
        have h2 : 0 ≤ η * (z k - I.inf k) := mul_nonneg hη.le (by linarith)
        by_contra hne
        have h3 : 0 < θ * (y k - I.inf k) :=
          mul_pos hθ (lt_of_le_of_ne (by linarith) fun h' => hne (by linarith))
        linarith
      · rw [h] at hc ⊢
        have h1 : θ * (I.sup k - y k) + η * (I.sup k - z k) = 0 := by
          linear_combination I.sup k * hθη - hc
        have h2 : 0 ≤ η * (I.sup k - z k) := mul_nonneg hη.le (by linarith)
        by_contra hne
        have h3 : 0 < θ * (I.sup k - y k) :=
          mul_pos hθ (lt_of_le_of_ne (by linarith) fun h' => hne (by linarith))
        linarith
    -- all at a bound: `y = x`; one inside: the plane fixes it too
    by_cases hall : ∀ k, x k = I.inf k ∨ x k = I.sup k
    · exact funext fun k => hbound k (hall k)
    · simp only [not_forall, not_or] at hall
      obtain ⟨m, hm1, hm2⟩ := hall
      have hother : ∀ k, k ≠ m → y k = x k := fun k hk =>
        hbound k ((hedge k m hk).resolve_right (by simp [hm1, hm2]))
      -- the hyperplane fixes the remaining coordinate
      have hyP : ∑ k, a k * y k = α := hy.2
      have hxP : ∑ k, a k * x k = α := hxA.2
      have hrest : ∑ k ∈ Finset.univ.erase m, a k * y k = ∑ k ∈ Finset.univ.erase m, a k * x k :=
        Finset.sum_congr rfl fun k hk => by rw [hother k (Finset.ne_of_mem_erase hk)]
      have hsplit := Finset.add_sum_erase Finset.univ (fun k => a k * y k) (Finset.mem_univ m)
      have hsplit' := Finset.add_sum_erase Finset.univ (fun k => a k * x k) (Finset.mem_univ m)
      have hm : a m * y m = a m * x m := by linarith
      funext k
      by_cases hkm : k = m
      · subst hkm; exact mul_left_cancel₀ (ha k) hm
      · exact hother k hkm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
