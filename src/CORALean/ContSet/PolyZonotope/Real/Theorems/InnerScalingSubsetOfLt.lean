import CORALean.ContSet.PolyZonotope.Real.Operations.InnerScaling
import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
import CORALean.ContSet.Interval.Real.Definitions.IsBoundsContractor
import CORALean.Global.SubsetOfIsPreconnectedOfDisjointFrontier
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# The scaled outer approximation is inside a closed set when its factor box is not flat

[1, Thm. 3], corrected: `C = C(α̲, ᾱ)` from [1, Alg. 1] is inside `R` when `R` is closed, `B`
encloses `∂R`, the contractor is one [1, Def. 3] admits, the centre is in `R` — what (14) of
[1, Thm. 3] establishes — and the final box is not flat, `α̲ < ᾱ`. Line 6 stores [1, Prop. 3]'s
half-open slab closed, so `C` can meet `B` on the face it shares with the contraction, and
[1, Thm. 1] is applied to the image of the open box instead, which every pass keeps away from
every `PZₖ`; the closed box is its closure, inside `R` as `R` is closed. A reachable set from a
compact `X₀` is. Without `α̲ < ᾱ` the statement is false, `innerScaling_counterexample`.

## References

* [1] N. Kochdumper and M. Althoff. "Computing Non-Convex Inner-Approximations of Reachable Sets
      for Nonlinear Continuous Systems". In Proc. of the 59th IEEE Conference on Decision and
      Control (CDC), pp. 2130-2137, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Set

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `boxDiffBounds` stays inside `[l₁, u₁]` and its open box misses `[l₂, u₂]`. -/
private theorem aux_boxDiffBounds {n : ℕ} (hn : 0 < n) {l₁ u₁ l₂ u₂ : Fin n → ℝ} (h1 : l₁ ≤ l₂)
    (h2 : l₂ ≤ u₂) (h3 : u₂ ≤ u₁) :
    l₁ ≤ (boxDiffBounds l₁ u₁ l₂ u₂).1 ∧
      (boxDiffBounds l₁ u₁ l₂ u₂).1 ≤ (boxDiffBounds l₁ u₁ l₂ u₂).2 ∧
      (boxDiffBounds l₁ u₁ l₂ u₂).2 ≤ u₁ ∧
      ∀ a : Fin n → ℝ, (∀ i, (boxDiffBounds l₁ u₁ l₂ u₂).1 i < a i ∧
        a i < (boxDiffBounds l₁ u₁ l₂ u₂).2 i) → a ∉ Icc l₂ u₂ := by -- --- PROOF ---
  simp only [boxDiffBounds]
  -- an axis exists, so `argmax` picks one
  rcases harg : (List.finRange n).argmax (fun i => max ((l₂ - l₁) i) ((u₁ - u₂) i)) with _ | i
  · rw [List.argmax_eq_none] at harg
    exact absurd harg (List.ne_nil_of_length_pos (by simpa using hn))
  · simp only
    -- the side `Î` is on: the upper bound moves to `l₂(i*)`, or the lower one to `u₂(i*)`
    split_ifs with hle
    · refine ⟨le_rfl, fun j => ?_, fun j => ?_, fun a ha hmem => ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · simpa using h1 j |>.trans (le_refl _)
        · simpa [Function.update_of_ne hj] using (h1 j).trans ((h2 j).trans (h3 j))
      · rcases eq_or_ne j i with rfl | hj
        · simpa using (h2 j).trans (h3 j)
        · simp [Function.update_of_ne hj]
      · have := (ha i).2
        simp only [Function.update_self] at this
        exact absurd (hmem.1 i) (not_le.mpr this)
    · -- the mirror image: the lower bound moves up to `u₂(i*)`
      refine ⟨fun j => ?_, fun j => ?_, le_rfl, fun a ha hmem => ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · simpa using (h1 j).trans (h2 j)
        · simp [Function.update_of_ne hj]
      · rcases eq_or_ne j i with rfl | hj
        · simpa using h3 j
        · simpa [Function.update_of_ne hj] using (h1 j).trans ((h2 j).trans (h3 j))
      · have := (ha i).1
        simp only [Function.update_self] at this
        exact absurd (hmem.2 i) (not_le.mpr this)

/-- `point` is a polynomial in the factors, so continuous. -/
private theorem aux_point_continuous (pZ : PolyZonotope V) : Continuous pZ.point := by
  unfold PolyZonotope.point PolyZonotope.monomial
  fun_prop

/-- The invariant of [1, Alg. 1]'s loop: the box shrinks, stays a box, and the points of its
open part miss every piece passed. -/
private theorem aux_foldl (pZ : PolyZonotope V) (hp : 0 < pZ.p)
    (contract : ∀ m : ℕ, ((Fin m → ℝ) → V) → (Fin m → ℝ) × (Fin m → ℝ) →
      (Fin m → ℝ) × (Fin m → ℝ)) (hcon : ∀ m c, IsBoundsContractor c (contract m c)) :
    ∀ (L : List (PolyZonotope V)) (b : (Fin pZ.p → ℝ) × (Fin pZ.p → ℝ)), b.1 ≤ b.2 →
      let step := fun (bounds : (Fin pZ.p → ℝ) × (Fin pZ.p → ℝ)) (PZk : PolyZonotope V) =>
        let c := fun x : Fin (pZ.p + PZk.p) → ℝ =>
          pZ.point (fun i => x (Fin.castAdd PZk.p i)) - PZk.point (fun j => x (Fin.natAdd pZ.p j))
        let I := contract (pZ.p + PZk.p) c (Fin.append bounds.1 (-1), Fin.append bounds.2 1)
        let Iproj := (fun i => I.1 (Fin.castAdd PZk.p i), fun i => I.2 (Fin.castAdd PZk.p i))
        boxDiffBounds bounds.1 bounds.2 Iproj.1 Iproj.2
      b.1 ≤ (L.foldl step b).1 ∧ (L.foldl step b).1 ≤ (L.foldl step b).2 ∧
        (L.foldl step b).2 ≤ b.2 ∧
        ∀ PZk ∈ L, ∀ a, (∀ i, (L.foldl step b).1 i < a i ∧ a i < (L.foldl step b).2 i) →
          ∀ β, (∀ j, |β j| ≤ 1) → pZ.point a ≠ PZk.point β := by -- --- PROOF ---
  intro L
  induction L with
  | nil => intro b hb; simp [hb]
  | cons PZk L ih =>
    intro b hb step
    -- one pass of lines 3-6
    have hl : Fin.append b.1 (-1 : Fin PZk.p → ℝ) ≤ Fin.append b.2 1 := by
      intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa using hb i
      · simp
    set c := fun x : Fin (pZ.p + PZk.p) → ℝ =>
      pZ.point (fun i => x (Fin.castAdd PZk.p i)) - PZk.point (fun j => x (Fin.natAdd pZ.p j))
    obtain ⟨⟨hI1, hI2, hI3⟩, hzero⟩ := hcon (pZ.p + PZk.p) c _ _ hl
    set I := contract (pZ.p + PZk.p) c (Fin.append b.1 (-1), Fin.append b.2 1) with hIdef
    have hs1 : b.1 ≤ fun i => I.1 (Fin.castAdd PZk.p i) := fun i => by
      simpa using hI1 (Fin.castAdd PZk.p i)
    have hs2 : (fun i => I.1 (Fin.castAdd PZk.p i)) ≤ fun i => I.2 (Fin.castAdd PZk.p i) :=
      fun i => hI2 (Fin.castAdd PZk.p i)
    have hs3 : (fun i => I.2 (Fin.castAdd PZk.p i)) ≤ b.2 := fun i => by
      simpa using hI3 (Fin.castAdd PZk.p i)
    -- the projected contraction lies in the box, so line 6 keeps a box inside it
    obtain ⟨h1, h2, h3, hmiss⟩ := aux_boxDiffBounds hp hs1 hs2 hs3
    have hstep : step b PZk = boxDiffBounds b.1 b.2 (fun i => I.1 (Fin.castAdd PZk.p i))
        (fun i => I.2 (Fin.castAdd PZk.p i)) := rfl
    obtain ⟨k1, k2, k3, kmiss⟩ := ih (step b PZk) (hstep ▸ h2)
    rw [List.foldl_cons]
    refine ⟨le_trans (hstep ▸ h1) k1, k2, le_trans k3 (hstep ▸ h3), ?_⟩
    intro Q hQ a ha β hβ hab
    rcases List.mem_cons.mp hQ with rfl | hQ
    · -- the open box of the end lies in the open box after this step
      have ha' : ∀ i, (step b Q).1 i < a i ∧ a i < (step b Q).2 i :=
        fun i => ⟨lt_of_le_of_lt (k1 i) (ha i).1, lt_of_lt_of_le (ha i).2 (k3 i)⟩
      rw [hstep] at ha'
      refine hmiss a ha' ?_
      -- `(a, β)` is a zero of `c` in the appended box, so it survives the contraction
      have hx : Fin.append a β ∈ Icc (Fin.append b.1 (-1)) (Fin.append b.2 1) := by
        constructor <;> intro j <;> refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simpa using (h1 i).trans (ha' i).1.le
        · simpa using (abs_le.mp (hβ i)).1
        · simpa using (ha' i).2.le.trans (h3 i)
        · simpa using (abs_le.mp (hβ i)).2
      have hc : c (Fin.append a β) = 0 := by simp [c, hab]
      have hmem := hzero _ hx hc
      exact ⟨fun i => by simpa using hmem.1 (Fin.castAdd Q.p i),
        fun i => by simpa using hmem.2 (Fin.castAdd Q.p i)⟩
    · exact kmiss Q hQ a ha β hβ hab


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 3], corrected: with `R` closed, `∂R ⊆ B`, the centre in `R` and `α̲ < ᾱ`, the set
`C(α̲, ᾱ)` of [1, Alg. 1] is inside `R`. -/
theorem PolyZonotope.innerScaling_subset_of_lt (pZ : PolyZonotope V) (B : List (PolyZonotope V))
    (contract : ∀ m : ℕ, ((Fin m → ℝ) → V) → (Fin m → ℝ) × (Fin m → ℝ) →
      (Fin m → ℝ) × (Fin m → ℝ)) (hcon : ∀ m c, IsBoundsContractor c (contract m c)) {R : Set V}
    (hR : IsClosed R) (hB : frontier R ⊆ ⋃ PZk ∈ B, PZk.subsetAt {b | ∀ j, |b j| ≤ 1})
    (hlt : ∀ i, (pZ.innerScaling B contract).1 i < (pZ.innerScaling B contract).2 i)
    (h14 : pZ.point (fun i => ((pZ.innerScaling B contract).1 i +
      (pZ.innerScaling B contract).2 i) / 2) ∈ R) :
    pZ.subsetAt (Icc (pZ.innerScaling B contract).1 (pZ.innerScaling B contract).2) ⊆
      R := by -- --- PROOF ---
  set lo := (pZ.innerScaling B contract).1
  set hi := (pZ.innerScaling B contract).2
  set mid : Fin pZ.p → ℝ := fun i => (lo i + hi i) / 2
  rcases Nat.eq_zero_or_pos pZ.p with hp | hp
  · -- no factors: `C` is the centre alone
    rintro _ ⟨a, -, rfl⟩
    have : a = mid := funext fun i => absurd i.2 (by omega)
    rwa [this]
  obtain ⟨-, -, -, hmiss⟩ := aux_foldl pZ hp contract hcon B (-1, 1) (fun _ => by norm_num)
  set O : Set (Fin pZ.p → ℝ) := pi univ fun i => Ioo (lo i) (hi i)
  have hmidO : mid ∈ O := fun i _ => ⟨by simp only [mid]; linarith [hlt i],
    by simp only [mid]; linarith [hlt i]⟩
  -- [1, Thm. 1] on the image of the open box
  have hcont := aux_point_continuous pZ
  have hOR : pZ.point '' O ⊆ R := by
    refine CORALean.subset_of_isPreconnected_of_disjoint_frontier hB
      (((convex_pi fun i _ => convex_Ioo (lo i) (hi i)).isPreconnected).image _
        hcont.continuousOn) ?_ ⟨_, ⟨mid, hmidO, rfl⟩, h14⟩
    refine eq_empty_iff_forall_notMem.mpr ?_
    rintro _ ⟨⟨a, ha, rfl⟩, hy⟩
    simp only [mem_iUnion] at hy
    obtain ⟨PZk, hk, β, hβ, hβa⟩ := hy
    exact hmiss PZk hk a (fun i => ha i (mem_univ i)) β hβ hβa.symm
  -- the closed box is the closure of the open one
  have hcl : Icc lo hi = closure O := by
    rw [closure_pi_set, ← pi_univ_Icc]
    congr 1
    funext i
    exact (closure_Ioo (hlt i).ne).symm
  rintro _ ⟨a, ha, rfl⟩
  rw [hcl] at ha
  exact hR.closure_subset_iff.mpr hOR (image_closure_subset_closure_image hcont ⟨a, ha, rfl⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
