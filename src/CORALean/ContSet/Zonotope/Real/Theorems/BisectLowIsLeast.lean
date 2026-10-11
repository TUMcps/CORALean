import CORALean.ContSet.Zonotope.Real.Operations.BisectLow
import CORALean.ContSet.Zonotope.Real.Theorems.BisectInvStep
import CORALean.ContSet.Zonotope.Real.Theorems.EdgePointLeast
import CORALean.ContSet.Zonotope.Real.Theorems.CrossNonnegOfHorizontal
import CORALean.ContSet.Zonotope.Real.Theorems.CornerEqBottomAdd
import CORALean.ContSet.Zonotope.Real.Theorems.CornerBottomLe
import CORALean.ContSet.Zonotope.Real.Theorems.ReachLe
import CORALean.ContSet.Zonotope.Real.Theorems.ConstructPointUp
import CORALean.ContSet.Zonotope.Real.Theorems.PointUpHalfPlane

/-!
# The bisection of [1, Alg. 4] finds the lowest point of the section

For `Z ∩ L_γ` nonempty, `bisectLow` is the least `y` with `(γ, y) ∈ Z`. The loop keeps
`BisectInv` (`bisectInv_step`) from the start, with `B = ∅` and `G` all the generators along the
side searched, whose reach contains the line since the zonogon meets it; `|G| ≤ r` and it shrinks
each pass, so after `r` passes one generator `a` is left. Then `[P; P + 2 g_a]` is an edge with the
zonogon on one side (`edge_point_least`), and its point on the line is the lowest of the section.
With no generator left the line passes through the lowest vertex.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The passes keep the invariant and have shrunk `G` to at most one generator after `r` of them. -/
theorem Zonotope.aux_iterate (Z : Zonotope (Vec ℝ 2))
    (hH : ∀ j, 0 ≤ Z.G j 1 ∧ (0 < Z.G j 1 ∨ 0 ≤ Z.G j 0)) (γ : ℝ) (right : Bool) {σ : ℝ}
    (hσ : σ = if right then 1 else -1) (st : Vec ℝ 2 × Finset (Fin Z.h) × Vec ℝ 2)
    (hinv : Z.BisectInv γ σ st) (n : ℕ) :
    Z.BisectInv γ σ ((Z.bisectStep γ right)^[n] st) ∧
      ((Z.bisectStep γ right)^[n] st).2.1.card ≤ max 1 (st.2.1.card - n) := by -- --- PROOF ---
  induction n with
  | zero => exact ⟨hinv, by simp⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨hi, hc⟩ := ih
    obtain ⟨h1, h2, h3⟩ := Zonotope.bisectInv_step Z hH γ right hσ _ hi
    refine ⟨h1, ?_⟩
    by_cases h : 1 < ((Z.bisectStep γ right)^[n] st).2.1.card
    · have := h2 h
      omega
    · rw [h3 (not_lt.mp h)]
      omega

/-- With at most one generator left, the point of the last edge on the line is the lowest. -/
theorem Zonotope.aux_bisect_final (Z : Zonotope (Vec ℝ 2))
    (hH : ∀ j, 0 ≤ Z.G j 1 ∧ (0 < Z.G j 1 ∨ 0 ≤ Z.G j 0)) (γ : ℝ) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (st : Vec ℝ 2 × Finset (Fin Z.h) × Vec ℝ 2)
    (hinv : Z.BisectInv γ σ st) (hcard : st.2.1.card ≤ 1) :
    IsLeast {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ Z.construct}
      (sInf {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ segment ℝ st.1 (st.1 + st.2.2)}) := by -- --- PROOF ---
  classical
  obtain ⟨P, G, s⟩ := st
  obtain ⟨B, hBG, hBA, hGA, hP, hs, hc, hd, he, hf⟩ := hinv
  simp only at hBG hBA hGA hP hs hc hd he hf hcard ⊢
  -- the corner of the walk after passing exactly the generators of `B`
  have hcorner : Z.corner (fun j => decide (j ∈ B))
      = (Z.c - ∑ j, Z.G j) + ∑ i ∈ B, (2 : ℝ) • Z.G i := by
    rw [Zonotope.corner_eq_bottom_add, ← Finset.smul_sum]
    congr 2
    simp only [decide_eq_true_eq]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rcases G.eq_empty_or_nonempty with hG | hG
  · -- nothing left to pass: the line goes through the lowest vertex
    subst hG
    have hB : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun h => by simpa using hf h
    subst hB
    simp only [Finset.sum_empty, add_zero] at hP hs
    subst hs
    -- then `P` is the lowest corner
    have hPc : P = Z.corner (fun _ => false) := by
      rw [Zonotope.corner_eq_bottom_add, hP]; simp
    simp only [add_zero, min_self, max_self] at he
    have hγ : P 0 = γ := le_antisymm he.2 he.1 |>.symm ▸ rfl
    -- the segment `[P; P]` is the point `P`
    have hY : {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ segment ℝ P P} = {P 1} := by
      ext y
      simp only [segment_same, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro h; simpa using congrFun h 1
      · rintro rfl
        ext k; fin_cases k
        · exact hγ.symm
        · rfl
    simp only [add_zero]
    rw [hY, csInf_singleton]
    -- the point is in the zonogon, and nothing in the section is lower
    refine ⟨?_, fun y hy => ?_⟩
    · have : (![γ, P 1] : Vec ℝ 2) = P := by
        ext k; fin_cases k
        · exact hγ.symm
        · rfl
      rw [Set.mem_setOf_eq, this, hPc]
      exact Z.corner_mem_construct _
    · rw [hPc]
      exact Z.corner_bottom_le (fun j => (hH j).1) hy
  · -- one generator left: its edge is where the line is
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (le_antisymm hcard (Finset.card_pos.mpr hG))
    have haB : a ∉ B := fun h => Finset.disjoint_left.mp hBG h (Finset.mem_singleton_self a)
    simp only [Finset.sum_singleton] at hs
    subst hs
    obtain ⟨z, hz, hzx⟩ := (Zonotope.segment_meets_vline_iff P (P + (2 : ℝ) • Z.G a) γ).mpr he
    rw [← hcorner] at hP
    subst hP
    have hE := fun w (hw : w ∈ segment ℝ (Z.corner fun j => decide (j ∈ B))
        (Z.corner (fun j => decide (j ∈ B)) + (2 : ℝ) • Z.G a)) =>
      Z.edge_point_least σ (fun j => decide (j ∈ B)) a (by simp [haB])
        (fun b hb => hc b (by simpa using hb) a (Finset.mem_singleton_self a))
        (fun c' hc' hca => by
          have hcB : c' ∉ B := by simpa using hc'
          have hcG : c' ∉ ({a} : Finset (Fin Z.h)) := by simpa using hca
          by_cases hpos : 0 < σ * Z.G c' 0
          · exact hd a (Finset.mem_singleton_self a) c' hpos hcB hcG
          · exact Zonotope.cross_nonneg_of_horizontal hσ (hH a) (hH c')
              (hGA a (Finset.mem_singleton_self a)) (not_lt.mp hpos))
        (hGA a (Finset.mem_singleton_self a)) hw
    obtain ⟨hzZ, hzmin⟩ := hE z hz
    -- the section's points on the edge are all that point
    have hz' : (![γ, z 1] : Vec ℝ 2) = z := by
      ext k; fin_cases k
      · exact hzx.symm
      · rfl
    have hleast : IsLeast {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ Z.construct} (z 1) :=
      ⟨by rw [Set.mem_setOf_eq, hz']; exact hzZ,
        fun y hy => hzmin y (by rw [hzx]; exact hy)⟩
    have hY : IsLeast {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ segment ℝ (Z.corner fun j => decide (j ∈ B))
        (Z.corner (fun j => decide (j ∈ B)) + (2 : ℝ) • Z.G a)} (z 1) := by
      refine ⟨by rw [Set.mem_setOf_eq, hz']; exact hz, fun y hy => hleast.2 ?_⟩
      exact (hE _ hy).1
    rw [hY.csInf_eq]
    exact hleast

/-- The whole search, from the state `lines 1-14` leave to the one after `r` passes. -/
theorem Zonotope.aux_bisect_least (Z : Zonotope (Vec ℝ 2))
    (hH : ∀ j, 0 ≤ Z.G j 1 ∧ (0 < Z.G j 1 ∨ 0 ≤ Z.G j 0)) (γ : ℝ)
    (hne : ∃ y, (![γ, y] : Vec ℝ 2) ∈ Z.construct) (P : Vec ℝ 2) (hP : P = Z.c - ∑ i, Z.G i)
    (right : Bool) (hright : right = decide (P 0 < γ)) (G : Finset (Fin Z.h))
    (hG : G = if right then Finset.univ.filter (fun i => 0 < Z.G i 0)
      else Finset.univ.filter (fun i => Z.G i 0 < 0)) (s : Vec ℝ 2)
    (hs : s = ∑ i ∈ G, (2 : ℝ) • Z.G i) (loop : Vec ℝ 2 × Finset (Fin Z.h) × Vec ℝ 2)
    (hloop : (Z.bisectStep γ right)^[Z.h] (P, G, s) = loop) :
    IsLeast {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ Z.construct}
      (sInf {y : ℝ | (![γ, y] : Vec ℝ 2) ∈
        segment ℝ loop.1 (loop.1 + loop.2.2)}) := by -- --- PROOF ---
  classical
  obtain ⟨y₀, hy₀⟩ := hne
  -- the direction searched, and the generators pointing that way
  set σ : ℝ := if right then 1 else -1 with hσ
  have hσ' : σ = 1 ∨ σ = -1 := by cases right <;> simp [hσ]
  have hGσ : ∀ i, i ∈ G ↔ 0 < σ * Z.G i 0 := fun i => by
    rw [hG]; cases right <;> simp [hσ]
  have hPc : Z.corner (fun _ => false) = P := by
    rw [Zonotope.corner_eq_bottom_add, hP]; simp
  -- the sum of `G`, along `σ`, is the total reach of the generators pointing that way
  have hreach : ∑ j, 2 * max (σ * Z.G j 0) 0 = σ * s 0 := by
    have e : ∀ j, 2 * max (σ * Z.G j 0) 0 = if j ∈ G then 2 * (σ * Z.G j 0) else 0 := fun j => by
      by_cases h : j ∈ G
      · rw [if_pos h, max_eq_left ((hGσ j).mp h).le]
      · rw [if_neg h, max_eq_right (not_lt.mp (mt (hGσ j).mpr h))]; ring
    have e2 : σ * s 0 = ∑ i ∈ G, 2 * (σ * Z.G i 0) := by
      rw [hs]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [e]
    rw [Finset.sum_ite_mem, Finset.univ_inter, e2]
  have hr := Z.reach_le σ hy₀
  rw [hPc, hreach] at hr
  have hs0 : 0 ≤ σ * s 0 := hreach ▸ Finset.sum_nonneg fun j _ => by
    have := le_max_right (σ * Z.G j 0) 0; linarith
  -- the line is between the abscissae of `P` and `P + s`, since the zonogon meets it
  have hstr : min (P 0) ((P + s) 0) ≤ γ ∧ γ ≤ max (P 0) ((P + s) 0) := by
    simp only [Pi.add_apply]
    have h0 : (![γ, y₀] : Vec ℝ 2) 0 = γ := rfl
    rw [h0] at hr
    cases hrt : right
    · have hσm : σ = -1 := by simp [hσ, hrt]
      have : ¬ P 0 < γ := by simpa [hrt] using hright
      rw [hσm] at hr hs0
      exact ⟨min_le_of_right_le (by linarith), le_max_of_le_left (not_lt.mp this)⟩
    · have hσp : σ = 1 := by simp [hσ, hrt]
      have : P 0 < γ := by simpa [hrt] using hright
      rw [hσp] at hr hs0
      exact ⟨min_le_of_left_le this.le, le_max_of_le_right (by linarith)⟩
  -- the search keeps its invariant from the start
  have hinit : Z.BisectInv γ σ (P, G, s) :=
    ⟨∅, Finset.disjoint_empty_left _, by simp, fun i hi => (hGσ i).mp hi, by simp [hP], hs,
      by simp, fun i _ r hr' _ hrG => absurd ((hGσ r).mpr hr') hrG, hstr, by simp⟩
  obtain ⟨hI, hC⟩ := Zonotope.aux_iterate Z hH γ right hσ _ hinit Z.h
  rw [hloop] at hI hC
  have hGc : G.card ≤ Z.h := by simpa using Finset.card_le_univ G
  exact Zonotope.aux_bisect_final Z hH γ hσ' loop hI (by simp at hC; omega)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.bisectLow_isLeast (Z : Zonotope (Vec ℝ 2)) (γ : ℝ)
    (hne : ∃ y, (![γ, y] : Vec ℝ 2) ∈ Z.construct) :
    IsLeast {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ Z.construct} (Z.bisectLow γ) := by -- --- PROOF ---
  have hne' : ∃ y, (![γ, y] : Vec ℝ 2) ∈ Z.pointUp.construct := by
    rwa [Z.construct_pointUp]
  rw [← Z.construct_pointUp]
  exact Zonotope.aux_bisect_least Z.pointUp (Z.pointUp_half_plane) γ hne' _ rfl _ rfl _ rfl _ rfl
    _ rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
