module

public import CORALean.ContSet.PolyZonotope.Real.Operations.InnerScaling
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SubsetAtUnitBox
public import CORALean.ContSet.Interval.Real.Definitions.IsBoundsContractor
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Order.Basic

@[expose] public section

/-!
# [1, Thm. 3] fails: the scaled set can leave the reachable set

`ẋ = 0` on `ℝ`, `X₀ = [-1, 1]`, `t = 1`, so `R_{X₀}(1) = X₀`. The outer approximation
`x = α₁ + α₂/2` has the initial-state factor `α₁` and one more, as [1]'s Example 2 does, and `B` is
[1, Eq. 8]'s, the reach-subsets of the faces `α₁ = ±1`. The contractor is the identity, which
[1, Def. 3] admits. Each contraction is then the whole box, all margins of [1, Prop. 3] are `0`,
its slab `[l₁(1), l₂(1)[` is empty, and line 6 stores it closed as the face `α₁ = -1`. So
`C = {-1 + α₂/2} = [-3/2, -1/2]`: its centre `-1` passes (14), and `-3/2 ∈ C` is not reachable.
It is in the second piece of `B` too, so the answer is not feasible for [1]'s (10) either.
`PolyZonotope.innerScaling_subset_of_lt` is the statement corrected, at a box that is not flat.

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

namespace CORALean

open Set CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A box minus itself, by [1, Prop. 3] as line 6 stores it: the face `α₁ = l₁`. -/
private theorem aux_boxDiffBounds_self (l u : Fin 2 → ℝ) :
    boxDiffBounds l u l u = (l, Function.update u 0 (l 0)) := by -- --- PROOF ---
  have harg : ((List.finRange 2).argmax fun i => max ((l - l) i) ((u - u) i)) = some 0 := by
    simp [List.argmax, List.finRange_succ, List.argAux]
  simp only [boxDiffBounds]
  rw [harg]
  simp

/-- A function with zero derivative on `[0, 1]` is constant there. -/
private theorem aux_const {x : ℝ → ℝ} (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x 0 (Icc 0 1) s) :
    x 1 = x 0 :=
  constant_of_has_deriv_right_zero (fun s hs => (hd s hs).continuousWithinAt)
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1))) 1
    ⟨zero_le_one, le_rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 3] is false: every hypothesis holds for `ẋ = 0` from `[-1, 1]` with the identity
contractor, and `C(α̲, ᾱ) = [-3/2, -1/2]` is not inside `R(1) = [-1, 1]`. -/
theorem innerScaling_counterexample :
    let pZ : PolyZonotope ℝ := ⟨2, 2, 0, 0, ![1, 1 / 2], fun k i => if k = i then 1 else 0,
      Fin.elim0⟩
    let B : List (PolyZonotope ℝ) := [⟨1, 1, 0, 1, ![1 / 2], fun _ _ => 1, Fin.elim0⟩,
      ⟨1, 1, 0, -1, ![1 / 2], fun _ _ => 1, Fin.elim0⟩]
    let contract : ∀ m : ℕ, ((Fin m → ℝ) → ℝ) → (Fin m → ℝ) × (Fin m → ℝ) →
      (Fin m → ℝ) × (Fin m → ℝ) := fun _ _ I => I
    let X₀ : Set ℝ := Icc (-1) 1
    let runs : Set (ℝ → ℝ) := {x | ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x 0 (Icc 0 1) t}
    let R : Set ℝ := {y | ∃ x ∈ runs, x 0 ∈ X₀ ∧ x 1 = y}
    let lo := (pZ.innerScaling B contract).1
    let hi := (pZ.innerScaling B contract).2
    (∀ m c, IsBoundsContractor c (contract m c)) ∧ R = X₀ ∧ R ⊆ pZ.construct ∧
      B.map (fun PZk => PZk.construct) = [pZ.subsetAt {a | (∀ k, |a k| ≤ 1) ∧ a 0 = 1},
        pZ.subsetAt {a | (∀ k, |a k| ≤ 1) ∧ a 0 = -1}] ∧
      frontier R ⊆ ⋃ PZk ∈ B, PZk.subsetAt {b | ∀ j, |b j| ≤ 1} ∧
      (∀ y ∈ runs, y 0 = pZ.point (fun i => (lo i + hi i) / 2) → y 1 ∈ X₀) ∧
      (pZ.subsetAt (Icc lo hi) ∩ ⋃ PZk ∈ B, PZk.subsetAt {b | ∀ j, |b j| ≤ 1}).Nonempty ∧
      ¬ pZ.subsetAt (Icc lo hi) ⊆ R := by -- --- PROOF ---
  intro pZ B contract X₀ runs R lo hi
  have hpt : ∀ a : Fin 2 → ℝ, pZ.point a = a 0 + a 1 / 2 := fun a => by
    simp [pZ, PolyZonotope.point, PolyZonotope.monomial, Fin.sum_univ_two]
    ring
  have hpt1 : ∀ (s : ℝ) (b : Fin 1 → ℝ),
      (⟨1, 1, 0, s, ![1 / 2], fun _ _ => 1, Fin.elim0⟩ : PolyZonotope ℝ).point b = s + b 0 / 2 :=
    fun s b => by simp [PolyZonotope.point, PolyZonotope.monomial]; ring
  -- the loop: both passes cut the box down to the face `α₁ = -1`
  have hb : pZ.innerScaling B contract =
      ((-1 : Fin 2 → ℝ), Function.update (1 : Fin 2 → ℝ) 0 (-1)) := by
    simp only [PolyZonotope.innerScaling, B, contract, List.foldl_cons, List.foldl_nil,
      Fin.append_left]
    erw [aux_boxDiffBounds_self, aux_boxDiffBounds_self]
    simp
  have hlo : lo = -1 := by simp only [lo, hb]
  have hhi : hi = Function.update (1 : Fin 2 → ℝ) 0 (-1) := by simp only [hi, hb]
  -- the reachable set at `t = 1` is `X₀`
  have hR : R = X₀ := by
    ext y
    constructor
    · rintro ⟨x, hx, hx0, rfl⟩
      rwa [aux_const hx]
    · intro hy
      exact ⟨fun _ => y, fun t _ => hasDerivWithinAt_const _ _ _, hy, rfl⟩
  -- `(-1, -1)` is in the final box
  have hcorner : (![-1, -1] : Fin 2 → ℝ) ∈ Icc lo hi := by
    rw [hlo, hhi]
    constructor <;> intro k <;> fin_cases k <;> simp
  refine ⟨fun m c l u hlu => ⟨⟨le_rfl, hlu, le_rfl⟩, fun x hx _ => hx⟩, hR, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · -- outer approximation: `y = y + 0/2`
    rw [hR, ← pZ.subsetAt_unitBox rfl]
    intro y hy
    refine ⟨![y, 0], fun k => ?_, by simp [hpt]⟩
    fin_cases k
    · simp only [X₀, mem_Icc] at hy
      simpa [abs_le] using hy
    · simp
  · -- `B`'s pieces are the reach-subsets of the two faces
    simp only [B, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    constructor <;>
    · rw [← PolyZonotope.subsetAt_unitBox _ rfl]
      ext y
      constructor
      · rintro ⟨b, hb, rfl⟩
        refine ⟨![_, b 0], ⟨fun k => ?_, rfl⟩, ?_⟩
        · fin_cases k
          · norm_num
          · simpa using hb 0
        · rw [hpt, hpt1]; simp
      · rintro ⟨a, ⟨ha, ha0⟩, rfl⟩
        refine ⟨![a 1], fun k => ?_, ?_⟩
        · fin_cases k; simpa using ha 1
        · rw [hpt, hpt1, ha0]; simp
  · -- `∂R = {-1, 1}`, the centres of the two pieces
    rw [hR, frontier_Icc (by norm_num)]
    rintro y (rfl | rfl) <;> simp only [mem_iUnion]
    · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, fun _ => by simp, ?_⟩
      simp [PolyZonotope.point, PolyZonotope.monomial]
    · refine ⟨_, List.mem_cons_self, 0, fun _ => by simp, ?_⟩
      simp [PolyZonotope.point, PolyZonotope.monomial]
  · -- (14): the centre `(-1, 0)` is `-1`, and the time-inverted run stays there
    intro y hy hy0
    rw [aux_const hy, hy0, hpt, hlo, hhi]
    norm_num [X₀]
  · -- `C` meets `B` at `-3/2`, the corner of the second piece: not feasible for (10)
    refine ⟨pZ.point ![-1, -1], ⟨_, hcorner, rfl⟩, ?_⟩
    simp only [mem_iUnion]
    refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ => -1, fun _ => by simp, ?_⟩
    rw [hpt1, hpt]
    norm_num
  · -- `(-1, -1)` reaches `-3/2`, outside `R(1)`
    intro hsub
    have hmem : pZ.point ![-1, -1] ∈ R := hsub ⟨![-1, -1], hcorner, rfl⟩
    rw [hR, hpt] at hmem
    norm_num [X₀] at hmem

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
