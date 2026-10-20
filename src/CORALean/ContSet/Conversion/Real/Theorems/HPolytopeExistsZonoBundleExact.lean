module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.ConstructEqIInter
public import CORALean.ContSet.ConZonotope.Real.Theorems.ExistsConstructEqIffHPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeVPolytopeExact
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeZonoBundleRowsExact
public import CORALean.ContSet.ConZonotope.Real.Operations.MemDomainIff
public import CORALean.ContSet.VPolytope.Real.Theorems.KEqZeroOfConstructEqEmpty
public import CORALean.Global.OrthogonalFirstColumn

@[expose] public section

/-!
# Every bounded halfspace description is a zonotope bundle

CORA's bundle of one zonotope per row (`HPolytope.zonoBundleRows`) is exact given an orthogonal
basis for each row, whose first axis is the row's normal, and a vertex list of the polytope. Both
exist: the vertices by the constrained zonotope a bounded polytope is
(`ConZonotope.exists_construct_eq_iff_hPolytope`), and the basis by the Householder reflection
carrying the first axis to the normal (`exists_orthogonal_firstCol`). An empty polytope is the
bundle of two distinct points; the dimension is positive. This is the equivalence of polytopes and
zonotope bundles of [1, Fig. 1 (Polytopes ↔ Zonotope Bundles)].

## Inputs
* `P` – halfspace polytope

## Hypotheses
* `hbd` – polytope bounded

## Conclusion
* some zonotope bundle equals the polytope

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An orthogonal matrix whose first column is the row's normal direction: the row is its norm
times the first coordinate of `Bᵀ x`. -/
theorem HPolytope.aux_exists_orthogonal_row [NeZero n] (f : Vec ℝ n →ₗ[ℝ] ℝ) :
    ∃ B : Mat ℝ n n, B * Bᵀ = 1 ∧
      ∀ x, f x = HPolytope.rowNorm f * ((Bᵀ *ᵥ x) 0) := by -- --- PROOF ---
  -- the coefficients of the functional, and the functional as their dot product
  set a : Vec ℝ n := fun j => f (Pi.single j (1 : ℝ)) with ha
  have hf : ∀ x : Vec ℝ n, f x = a ⬝ᵥ x := fun x => by
    rw [LinearMap.pi_apply_eq_sum_univ f x, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 :=
      funext fun j => by simp [Pi.single_apply, eq_comm]
    rw [this, smul_eq_mul, mul_comm]
  have hnorm : HPolytope.rowNorm f = Real.sqrt (a ⬝ᵥ a) := by
    simp [HPolytope.rowNorm, ha, dotProduct, sq]
  by_cases h0 : a ⬝ᵥ a = 0
  · -- a zero functional: any orthogonal matrix will do
    have : a = 0 := dotProduct_self_eq_zero.mp h0
    refine ⟨1, by simp, fun x => ?_⟩
    rw [hf, this, hnorm, h0]
    simp
  · -- the unit vector `a / ‖a‖`, as the first column of an orthogonal matrix
    have hpos : 0 < a ⬝ᵥ a :=
      lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg _) (Ne.symm h0)
    set r := Real.sqrt (a ⬝ᵥ a) with hr
    have hr0 : 0 < r := Real.sqrt_pos.mpr hpos
    have hrr : r * r = a ⬝ᵥ a := Real.mul_self_sqrt hpos.le
    have hu : (r⁻¹ • a) ⬝ᵥ (r⁻¹ • a) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← hrr]
      field_simp
    obtain ⟨B, hB, hcol⟩ := exists_orthogonal_firstCol (r⁻¹ • a) hu
    refine ⟨B, hB, fun x => ?_⟩
    have : ((Bᵀ *ᵥ x) 0) = r⁻¹ * (a ⬝ᵥ x) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hcol, Pi.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, hf, hnorm]
    field_simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.exists_zonoBundle_exact [NeZero n] (P : HPolytope (Vec ℝ n))
    (hbd : Bornology.IsBounded P.construct) :
    ∃ zB : ZonoBundle (Vec ℝ n), zB.construct = P.construct := by -- --- PROOF ---
  by_cases hne : P.construct.Nonempty
  · -- a vertex form of the polytope, through the constrained zonotope it is
    obtain ⟨cZ, hcZ⟩ := ConZonotope.exists_construct_eq_iff_hPolytope.mpr ⟨P, rfl, hbd⟩
    obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨β, hβ, hβP, -⟩ := hcZ ▸ hx₀
    let V := cZ.vPolytope ⟨β, ConZonotope.mem_domain_iff.mpr ⟨hβ, hβP⟩⟩
    have hV : V.construct = P.construct :=
      (ConZonotope.vPolytope_exact cZ _).trans hcZ
    -- the vertex list is nonempty, the polytope being so
    have hk : NeZero V.k := ⟨fun h0 => by
      obtain ⟨γ, -, hsum, -⟩ : x₀ ∈ V.construct := hV ▸ hx₀
      haveI : IsEmpty (Fin V.k) := ⟨fun j => by have := j.2; omega⟩
      simp at hsum⟩
    -- an orthogonal basis for each row
    choose B hB hrow using fun i => HPolytope.aux_exists_orthogonal_row (P.rows i)
    exact ⟨P.zonoBundleRows V B, HPolytope.zonoBundleRows_exact P V B hV hB hrow⟩
  · -- the empty polytope is the bundle of two distinct points
    rw [Set.not_nonempty_iff_eq_empty] at hne
    refine ⟨⟨2, ![⟨0, 0, Fin.elim0⟩, ⟨0, fun j => if j = 0 then 1 else 0, Fin.elim0⟩]⟩, ?_⟩
    rw [hne]
    ext x
    simp only [ZonoBundle.construct_eq_iInter, Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro h
    have h0 := h 0
    have h1 := h 1
    obtain ⟨β₀, -, e0⟩ := h0
    obtain ⟨β₁, -, e1⟩ := h1
    have := congrFun (e0.symm.trans e1) 0
    simp at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
