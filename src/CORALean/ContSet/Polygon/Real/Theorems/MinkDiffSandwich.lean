module

public import CORALean.ContSet.Polygon.Real.Operations.MinkDiff
public import CORALean.ContSet.Polygon.Real.Theorems.IsCompact
public import CORALean.ContSet.Polygon.Real.Theorems.LinCombOuter
public import CORALean.ContSet.Polygon.Real.Theorems.MinusExact
public import CORALean.ContSet.Polygon.Real.Theorems.PlusExact
public import CORALean.ContSet.Polygon.Real.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Operations.ConstructPoint
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.VPolytope.Real.Theorems.VertexMem
public import Mathlib.Analysis.Convex.PathConnected

@[expose] public section

/-!
# `Polygon.minkDiff` is the Minkowski difference up to its boundary

For a convex subtrahend whose center lies in it, and a vertex loop `V` that runs along the
boundary of the shifted minuend, the region swept by the mirrored subtrahend along the loop is
exactly the mirror plus the boundary. So the points of the shifted minuend off that region are
those whose translate of the subtrahend does not meet the boundary, and a convex set that meets
no boundary and starts inside stays inside. Hence `Polygon.minkDiff` lies in the Minkowski
difference `{x | x + B ⊆ A}` and contains its interior: an inner approximation as it stands.
A non-convex subtrahend is not covered: `linComb` then also fills its gaps
(`references/coverage/contSet/polygon.md`, row `minkDiff`).

## Inputs
* `A` – polygon
* `B` – polygon
* `V` – `List (Vec ℝ 2)`

## Hypotheses
* `hB` – `B` is convex
* `hc` – the center of `B` lies in `B`
* `hV` – the edges of `V` form the boundary of the shifted `A`

## Conclusion
* `Polygon.minkDiff` is the Minkowski difference up to its boundary
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Pointwise


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The region of a point is that point. -/
theorem Polygon.aux_construct_ofPoint (v : Vec ℝ 2) :
    ContSet.construct (OfPoint.ofPoint v : Polygon) = {v} := by -- --- PROOF ---
  ext x
  show x ∈ SetUnion.construct _ ↔ _
  simp only [SetUnion.construct, OfPoint.ofPoint, List.mem_singleton, Set.iUnion_iUnion_eq_left]
  change x ∈ (VPolytope.point v).construct ↔ _
  rw [VPolytope.construct_point]

/-- A hull of two pieces lies in any convex set holding both. -/
theorem Polygon.aux_linComb_subset {p q : VPolytope (Vec ℝ 2)} {C : Set (Vec ℝ 2)}
    (hC : Convex ℝ C) (hp : p.construct ⊆ C) (hq : q.construct ⊆ C) :
    (p.linComb q).construct ⊆ C := by -- --- PROOF ---
  rw [VPolytope.construct_eq_convexHull]
  refine convexHull_min ?_ hC
  rintro _ ⟨i, rfl⟩
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · show Fin.append p.V q.V (Fin.castAdd q.k j) ∈ C
    rw [Fin.append_left]
    exact hp (VPolytope.vertex_mem p j)
  · show Fin.append p.V q.V (Fin.natAdd p.k j) ∈ C
    rw [Fin.append_right]
    exact hq (VPolytope.vertex_mem q j)

/-- The mirrored subtrahend about the center is the points `c - b`. -/
theorem Polygon.aux_construct_mirror (B : Polygon) (c : Vec ℝ 2) :
    ContSet.construct (Polygon.times (-1) (B.minus c))
      = (fun b => c - b) '' ContSet.construct B := by -- --- PROOF ---
  -- `times (-1)` negates and `minus c` subtracts `c`
  rw [← Polygon.times_exact, ← Polygon.minus_exact, Set.image_image]
  refine Set.image_congr fun b _ => ?_
  funext i
  simp [Matrix.mulVec_diagonal]

/-- The mirror of a convex set is convex. -/
theorem Polygon.aux_convex_mirror {B : Set (Vec ℝ 2)} (hB : Convex ℝ B) (c : Vec ℝ 2) :
    Convex ℝ ((fun b => c - b) '' B) := by
  rintro _ ⟨b₁, hb₁, rfl⟩ _ ⟨b₂, hb₂, rfl⟩ a b ha hb hab
  refine ⟨a • b₁ + b • b₂, hB hb₁ hb₂ ha hb hab, ?_⟩
  calc c - (a • b₁ + b • b₂) = (a + b) • c - (a • b₁ + b • b₂) := by rw [hab, one_smul]
    _ = a • (c - b₁) + b • (c - b₂) := by module

/-- The `linComb` of two shifts of the mirror sweeps the mirror along the segment. -/
theorem Polygon.aux_edge (B : Polygon) (c : Vec ℝ 2) (hB : Convex ℝ (ContSet.construct B))
    (u v : Vec ℝ 2) : -- --- CONCL ---
    ContSet.construct (Polygon.linComb
        (Polygon.plus (Polygon.times (-1) (B.minus c)) (OfPoint.ofPoint u))
        (Polygon.plus (Polygon.times (-1) (B.minus c)) (OfPoint.ofPoint v)))
      = (fun b => c - b) '' ContSet.construct B + segment ℝ u v := by -- --- PROOF ---
  have hK := Polygon.aux_convex_mirror hB c
  -- each shift is the mirror plus a point
  have hshift : ∀ w : Vec ℝ 2, ContSet.construct
      (Polygon.plus (Polygon.times (-1) (B.minus c)) (OfPoint.ofPoint w))
        = (fun b => c - b) '' ContSet.construct B + {w} := fun w => by
    rw [← Polygon.plus_exact, Polygon.aux_construct_mirror, Polygon.aux_construct_ofPoint]
  apply Set.Subset.antisymm
  · -- the sweep lies in the convex set `mirror + segment`
    intro z hz
    obtain ⟨t, ht, hzt⟩ := SetUnion.mem_construct.mp hz
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hp, hq⟩ := List.mem_product.mp hpq
    refine Polygon.aux_linComb_subset (hK.add (convex_segment u v)) ?_ ?_ hzt
    · intro y hy
      have hy' := SetUnion.mem_construct.mpr ⟨p, hp, hy⟩
      rw [hshift] at hy'
      exact Set.add_subset_add_left (Set.singleton_subset_iff.mpr (left_mem_segment ℝ u v)) hy'
    · intro y hy
      have hy' := SetUnion.mem_construct.mpr ⟨q, hq, hy⟩
      rw [hshift] at hy'
      exact Set.add_subset_add_left (Set.singleton_subset_iff.mpr (right_mem_segment ℝ u v)) hy'
  · -- a mirror point plus a point of the segment is a segment between two shifts
    rintro _ ⟨k, hk, s, ⟨a, b, ha, hb, hab, rfl⟩, rfl⟩
    refine Polygon.linComb_outer _ _ ⟨k + u, ?_, k + v, ?_, a, ⟨ha, by linarith⟩, ?_⟩
    · rw [hshift]; exact ⟨k, hk, u, rfl, rfl⟩
    · rw [hshift]; exact ⟨k, hk, v, rfl, rfl⟩
    · have hb' : 1 - a = b := by linarith
      rw [hb']
      calc k + (a • u + b • v) = (a + b) • k + (a • u + b • v) := by rw [hab, one_smul]
        _ = a • (k + u) + b • (k + v) := by module

/-- Inside the shifted minuend and off the swept region, the subtrahend stays in the minuend. -/
theorem Polygon.aux_minkDiff_inner {A B : Set (Vec ℝ 2)} {c : Vec ℝ 2} (hB : Convex ℝ B)
    (hc : c ∈ B) {x : Vec ℝ 2} (hx : x ∈ interior ((fun a => a - c) '' A))
    (hS : x ∉ (fun b => c - b) '' B + frontier ((fun a => a - c) '' A)) :
    ∀ b ∈ B, x + b ∈ A := by -- --- PROOF ---
  intro b hb
  set A₀ : Set (Vec ℝ 2) := (fun a => a - c) '' A with hA₀
  -- the segment from `x` to `x + (b - c)`, which is connected
  set Γ : Set (Vec ℝ 2) := (fun t : ℝ => x + t • (b - c)) '' Set.Icc (0 : ℝ) 1 with hΓ
  have hpre : IsPreconnected Γ :=
    isPreconnected_Icc.image _ (by fun_prop : Continuous fun t : ℝ => x + t • (b - c)).continuousOn
  have hxΓ : x ∈ Γ := ⟨0, by simp, by simp⟩
  -- it meets no boundary point, else `x` would be swept
  have hfree : ∀ z ∈ Γ, z ∉ frontier A₀ := by
    rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩ hz
    refine hS ⟨c - (c + t • (b - c)), ⟨c + t • (b - c), hB.add_smul_sub_mem hc hb ⟨ht0, ht1⟩, rfl⟩,
      x + t • (b - c), hz, ?_⟩
    module
  -- so it stays on one side of the boundary: the inside
  have hsub : Γ ⊆ interior A₀ ∪ (closure A₀)ᶜ := by
    intro z hz
    by_cases hi : z ∈ interior A₀
    · exact Or.inl hi
    · refine Or.inr fun hcl => hfree z hz ⟨hcl, hi⟩
  have hdisj : Disjoint (interior A₀) (closure A₀)ᶜ :=
    Set.disjoint_compl_right_iff_subset.mpr (interior_subset.trans subset_closure)
  have hin : Γ ⊆ interior A₀ := by
    rcases hpre.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl hdisj hsub with h | h
    · exact h
    · exact absurd (h hxΓ) (fun h' => h' (interior_subset.trans subset_closure hx))
  -- the end point `x + (b - c)` is in the shifted minuend
  have hend : x + (1 : ℝ) • (b - c) ∈ Γ := ⟨1, by simp, rfl⟩
  obtain ⟨a, ha, hae⟩ := interior_subset (hin hend)
  have hae' : a - c = x + (1 : ℝ) • (b - c) := hae
  have : x + b = a := by
    calc x + b = (x + (1 : ℝ) • (b - c)) + c := by module
      _ = (a - c) + c := by rw [hae']
      _ = a := sub_add_cancel a c
  rwa [this]

/-- An interior point of the Minkowski difference is inside the shifted minuend and unswept. -/
theorem Polygon.aux_minkDiff_outer {A B : Set (Vec ℝ 2)} {c : Vec ℝ 2} (hc : c ∈ B)
    {x : Vec ℝ 2} (hx : x ∈ interior {x | ∀ b ∈ B, x + b ∈ A}) :
    x ∈ interior ((fun a => a - c) '' A) ∧
      x ∉ (fun b => c - b) '' B + frontier ((fun a => a - c) '' A) := by -- --- PROOF ---
  set M : Set (Vec ℝ 2) := {x | ∀ b ∈ B, x + b ∈ A} with hM
  constructor
  · -- the interior of `M` is open and lies in the shifted minuend
    refine interior_maximal (fun y hy => ?_) isOpen_interior hx
    exact ⟨y + c, interior_subset hy c hc, add_sub_cancel_right y c⟩
  · -- every translate `x + b` is an interior point of `A`
    rintro ⟨_, ⟨b, hb, rfl⟩, f, hf, hxf⟩
    obtain ⟨U, hUM, hUo, hxU⟩ := mem_interior.mp hx
    have hxb : x + b ∈ interior A := by
      refine interior_maximal (t := (fun u => u + b) '' U) ?_ ?_ ⟨x, hxU, rfl⟩
      · rintro _ ⟨u, hu, rfl⟩
        exact hUM hu b hb
      · exact (Homeomorph.addRight b).isOpenMap U hUo
    -- so `f = x + b - c` is an interior point of the shifted minuend, not a boundary point
    have hfi : f ∈ interior ((fun a => a - c) '' A) := by
      have hxf' : c - b + f = x := hxf
      have hf' : f = (x + b) - c := by
        rw [← hxf']; module
      refine interior_maximal (t := (fun a => a - c) '' interior A)
        (Set.image_mono interior_subset) ?_ ⟨x + b, hxb, hf'.symm⟩
      exact (Homeomorph.subRight c).isOpenMap _ isOpen_interior
    exact hf.2 hfi


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.minkDiff_sandwich (A B : Polygon) (V : List (Vec ℝ 2))
    (hB : Convex ℝ (ContSet.construct B)) (hc : Polygon.center B ∈ ContSet.construct B)
    (hV : (⋃ e ∈ V.zip (V.rotate 1), segment ℝ e.1 e.2)
      = frontier ((fun x => x - Polygon.center B) '' ContSet.construct A)) : -- --- CONCL ---
    interior {x | ∀ b ∈ ContSet.construct B, x + b ∈ ContSet.construct A}
        ⊆ Polygon.minkDiff A B V ∧
      Polygon.minkDiff A B V ⊆
        {x | ∀ b ∈ ContSet.construct B, x + b ∈ ContSet.construct A} := by -- --- PROOF ---
  -- the swept region is the mirror plus the boundary
  have hdiff : ContSet.construct (⟨(V.zip (V.rotate 1)).flatMap fun e => (Polygon.linComb
      (Polygon.plus (Polygon.times (-1) (B.minus (Polygon.center B))) (OfPoint.ofPoint e.1))
      (Polygon.plus (Polygon.times (-1) (B.minus (Polygon.center B))) (OfPoint.ofPoint e.2))).sets⟩
        : Polygon)
      = (fun b => Polygon.center B - b) '' ContSet.construct B
        + frontier ((fun x => x - Polygon.center B) '' ContSet.construct A) := by
    rw [← hV]
    ext z
    constructor
    · -- a point of the union lies in one edge's sweep, mirror plus segment
      intro hz
      obtain ⟨t, ht, hzt⟩ := SetUnion.mem_construct.mp hz
      obtain ⟨e, he, hte⟩ := List.mem_flatMap.mp ht
      have h := Polygon.aux_edge B (Polygon.center B) hB e.1 e.2
      have hzE : z ∈ ContSet.construct (Polygon.linComb
          (Polygon.plus (Polygon.times (-1) (B.minus (Polygon.center B))) (OfPoint.ofPoint e.1))
          (Polygon.plus (Polygon.times (-1) (B.minus (Polygon.center B)))
            (OfPoint.ofPoint e.2))) :=
        SetUnion.mem_construct.mpr ⟨t, hte, hzt⟩
      rw [h] at hzE
      obtain ⟨k, hk, s, hs, rfl⟩ := hzE
      exact ⟨k, hk, s, Set.mem_biUnion he hs, rfl⟩
    · -- a mirror point plus a boundary point is in the sweep of an edge holding it
      rintro ⟨k, hk, s, hs, rfl⟩
      obtain ⟨e, he, hse⟩ := Set.mem_iUnion₂.mp hs
      have h := Polygon.aux_edge B (Polygon.center B) hB e.1 e.2
      have hzE : k + s ∈ (fun b => Polygon.center B - b) '' ContSet.construct B
          + segment ℝ e.1 e.2 := ⟨k, hk, s, hse, rfl⟩
      rw [← h] at hzE
      obtain ⟨t, ht, hzt⟩ := SetUnion.mem_construct.mp hzE
      exact SetUnion.mem_construct.mpr ⟨t, List.mem_flatMap.mpr ⟨e, he, ht⟩, hzt⟩
  -- the shifted minuend, and the minuend closed
  have hA : ContSet.construct (A.minus (Polygon.center B))
      = (fun x => x - Polygon.center B) '' ContSet.construct A :=
    (Polygon.minus_exact A _).symm
  have hAcl : IsClosed (ContSet.construct A) := (Polygon.isCompact_construct A).isClosed
  -- the result is the closure of the shifted minuend's interior off the sweep
  unfold Polygon.minkDiff Polygon.subtract
  simp only
  rw [hdiff, hA]
  constructor
  · -- an interior point of the difference is a point of the closure
    intro x hx
    obtain ⟨h1, h2⟩ := Polygon.aux_minkDiff_outer hc hx
    exact subset_closure ⟨h1, h2⟩
  · -- the closure stays in the closed Minkowski difference
    refine closure_minimal ?_ ?_
    · rintro x ⟨h1, h2⟩
      exact Polygon.aux_minkDiff_inner hB hc h1 h2
    · have : {x | ∀ b ∈ ContSet.construct B, x + b ∈ ContSet.construct A}
          = ⋂ b ∈ ContSet.construct B, (fun x => x + b) ⁻¹' ContSet.construct A := by
        ext x; simp
      rw [this]
      exact isClosed_biInter fun b _ => hAcl.preimage (by fun_prop)


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
