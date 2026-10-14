module

public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.IsLPCentre
public import CORALean.ContSet.HPolytope.Real.Theorems.MemIffRows
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.EnclosePointsOuter
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.VPolytope.Real.Theorems.VertexMem
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusIntervalExact
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import Mathlib.Tactic.Linarith
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_ZonoBundle
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# A halfspace description as a bundle of one
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Exact: the bundle of the rows' bounding zonotopes is the polytope. -/
theorem HPolytope.zonoBundleRows_exact [NeZero n] (P : HPolytope (Vec ℝ n))
    (V : VPolytope (Vec ℝ n)) [NeZero V.k] (B : Fin (P.m + (P.me + P.me)) → Mat ℝ n n)
    (hV : V.construct = P.construct) (hB : ∀ i, B i * (B i)ᵀ = 1)
    (hrow : ∀ i x, P.rows i x = HPolytope.rowNorm (P.rows i) * ((B i)ᵀ *ᵥ x) 0) :
    (P.zonoBundleRows V B).construct = P.construct := by -- --- PROOF ---
  have hBB : ∀ i, (B i)ᵀ * B i = 1 := fun i => by
    have := hB i
    rw [mul_eq_one_comm] at this
    simpa using this
  -- the box of the vertices in row `i`'s coordinates, its bounds, and the vertices inside it
  have hbox : ∀ (i : Fin (P.m + (P.me + P.me))) (j : Fin V.k),
      (B i)ᵀ *ᵥ V.V j ∈ (Interval.enclosePoints fun j => (B i)ᵀ *ᵥ V.V j).construct :=
    fun i j => Interval.enclosePoints_outer _ j
  have hne : ∀ i, (Interval.enclosePoints fun j => (B i)ᵀ *ᵥ V.V j).IsNonempty (ι := Fin n) :=
    fun i c => by
      obtain ⟨j⟩ : Nonempty (Fin V.k) := inferInstance
      exact ((hbox i j) c).1.trans ((hbox i j) c).2
  ext x
  constructor
  · -- inside every zonotope: inside every halfspace
    intro hx
    rw [HPolytope.mem_construct_iff_rows]
    intro i
    have hxi := Set.mem_iInter.mp hx i
    obtain ⟨y, hy, rfl⟩ : ∃ y ∈
        (Interval.enclosePoints fun j => (B i)ᵀ *ᵥ V.V j).zonotope.construct,
        B i *ᵥ y = x := by
      have : x ∈ (Zonotope.mtimes (B i)
          (Interval.enclosePoints fun j => (B i)ᵀ *ᵥ V.V j).zonotope).construct := hxi
      rw [← Zonotope.mtimes_exact] at this
      exact this
    have hy' := Interval.zonotope_subset_of_isNonempty (hne i) hy
    -- the first coordinate of `Bᵀ x` is the first coordinate of `y`, at most the largest vertex's
    have hfirst : ((B i)ᵀ *ᵥ (B i *ᵥ y)) 0 = y 0 := by
      rw [Matrix.mulVec_mulVec, hBB, Matrix.one_mulVec]
    have hy0 : y 0 ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun j => ((B i)ᵀ *ᵥ V.V j) 0) := by
      have h2 := (hy' 0).2
      simp only [Interval.enclosePoints, Entrywise.entry_ofEntry] at h2
      exact h2
    obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun j => ((B i)ᵀ *ᵥ V.V j) 0)
    have hVj : V.V j₀ ∈ P.construct := hV ▸ V.vertex_mem j₀
    have hrowj := HPolytope.mem_construct_iff_rows.mp hVj i
    have hnorm : 0 ≤ HPolytope.rowNorm (P.rows i) := _root_.Real.sqrt_nonneg _
    rw [hrow i, hfirst]
    calc HPolytope.rowNorm (P.rows i) * y 0
        ≤ HPolytope.rowNorm (P.rows i) * ((B i)ᵀ *ᵥ V.V j₀) 0 := by
          rw [← hj₀]; exact mul_le_mul_of_nonneg_left hy0 hnorm
      _ = P.rows i (V.V j₀) := (hrow i _).symm
      _ ≤ P.rowsRhs i := hrowj
  · -- the polytope is the hull of its vertices, and every zonotope is convex and holds them
    intro hx
    refine Set.mem_iInter.mpr fun i => ?_
    rw [← hV, VPolytope.construct_eq_convexHull] at hx
    refine convexHull_min ?_ (Zonotope.convex_construct _) hx
    rintro _ ⟨j, rfl⟩
    show V.V j ∈ (Zonotope.mtimes (B i)
      (Interval.enclosePoints fun j => (B i)ᵀ *ᵥ V.V j).zonotope).construct
    rw [← Zonotope.mtimes_exact]
    refine ⟨(B i)ᵀ *ᵥ V.V j, Interval.zonotope_contains _ (hbox i j), ?_⟩
    show B i *ᵥ ((B i)ᵀ *ᵥ V.V j) = V.V j
    rw [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
