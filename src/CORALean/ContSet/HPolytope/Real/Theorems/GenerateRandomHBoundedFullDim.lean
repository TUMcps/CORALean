module

public import CORALean.ContSet.HPolytope.Real.Operations.GenerateRandomH
public import CORALean.ContSet.HPolytope.Real.Theorems.ImageIneqsOfInvertible
public import CORALean.ContSet.HPolytope.Real.Theorems.IsBoundedIffSimplexSupportFunc
public import CORALean.ContSet.HPolytope.Real.Theorems.InteriorNonemptyIffChebyshev
public import CORALean.ContSet.ContSet.Theorems.ImageLinearMapProperties

@[expose] public section

/-!
# What `HPolytope.generateRandomH` returns

[1, Alg. 3]: a bounded, non-degenerate polytope, for any directions inside the unit ball and
any invertible `M`. The simplex rows bound every coordinate from both sides, so the base polytope
is bounded whatever is appended; every row has length at most `1` with offset `1`, so the unit
ball stays inside; an invertible affine map keeps both. Line 3 samples from the unit ball, and
this is the guarantee at that reading; non-redundancy of the appended rows is a separate matter
(`ineqs_unit_rows_minimal`, `simplexRows_redundant_counterexample`).

## Inputs
* `ℓ` – vectors indexed by `Fin m`
* `M` – `n × n` matrix
* `z` – point of length `n`

## Hypotheses
* `hn` – `0 < n`
* `hM` – `IsUnit M.det`
* `hℓ` – `∀ j, ‖ℓ j‖₂ ≤ 1`

## Conclusion
* what `HPolytope.generateRandomH` returns

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_row_coord (ℓ : Fin m → Vec ℝ n) (i : Fin n) :
    HPolytope.simplexRows ℓ (Fin.castAdd m (Fin.castAdd 1 i)) = Pi.single i 1 := by
  show Fin.append (Fin.append (fun i => (Pi.single i 1 : Vec ℝ n)) ![fun _ => -(1 / √(n : ℝ))]) ℓ
    (Fin.castAdd m (Fin.castAdd 1 i)) = _
  rw [Fin.append_left, Fin.append_left]

theorem aux_row_sum (ℓ : Fin m → Vec ℝ n) :
    HPolytope.simplexRows ℓ (Fin.castAdd m (Fin.natAdd n 0)) = fun _ => -(1 / √n) := by
  show Fin.append (Fin.append (fun i => (Pi.single i 1 : Vec ℝ n)) ![fun _ => -(1 / √(n : ℝ))]) ℓ
    (Fin.castAdd m (Fin.natAdd n 0)) = _
  rw [Fin.append_left, Fin.append_right]
  rfl

theorem aux_row_dir (ℓ : Fin m → Vec ℝ n) (j : Fin m) :
    HPolytope.simplexRows ℓ (Fin.natAdd (n + 1) j) = ℓ j := by
  show Fin.append (Fin.append (fun i => (Pi.single i 1 : Vec ℝ n)) ![fun _ => -(1 / √(n : ℝ))]) ℓ
    (Fin.natAdd (n + 1) j) = _
  rw [Fin.append_right]

/-- Every row has Euclidean length at most one. -/
theorem aux_rows_le (ℓ : Fin m → Vec ℝ n) (hn : 0 < n) (hℓ : ∀ j, ‖ℓ j‖₂ ≤ 1)
    (r : Fin (n + 1 + m)) : -- --- CONCL ---
    ‖HPolytope.simplexRows ℓ r‖₂ ≤ 1 := by -- --- PROOF ---
  refine Fin.addCases (fun r₀ => ?_) (fun j => ?_) r
  · refine Fin.addCases (fun i => ?_) (fun k => ?_) r₀
    · rw [aux_row_coord]
      simp [norm₂, Pi.single_apply]
    · obtain rfl : k = 0 := Fin.ext (by omega)
      rw [aux_row_sum]
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [norm₂, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [neg_sq, div_pow, one_pow, Real.sq_sqrt hn'.le, mul_one_div_cancel hn'.ne',
        Real.sqrt_one]
  · rw [aux_row_dir]
    exact hℓ j


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.generateRandomH_isBounded_interior (ℓ : Fin m → Vec ℝ n) (M : Mat ℝ n n)
    (z : Vec ℝ n) (hn : 0 < n) (hM : IsUnit M.det) (hℓ : ∀ j, ‖ℓ j‖₂ ≤ 1) : -- --- CONCL ---
    Bornology.IsBounded (HPolytope.generateRandomH ℓ M z).construct ∧
      (interior (HPolytope.generateRandomH ℓ M z).construct).Nonempty := by -- --- PROOF ---
  set Q := (HPolytope.ineqs (HPolytope.simplexRows ℓ) 1).construct with hQ
  -- the output is `M Q + z`
  have himg : (HPolytope.generateRandomH ℓ M z).construct = (· + z) '' ((M *ᵥ ·) '' Q) := by
    rw [hQ, HPolytope.image_ineqs_of_invertible _ _ M hM, show HPolytope.generateRandomH ℓ M z =
      HPolytope.ineqs (HPolytope.simplexRows ℓ * M⁻¹)
        (1 + (HPolytope.simplexRows ℓ * M⁻¹) *ᵥ z) from rfl]
    ext x
    rw [Set.mem_image]
    constructor
    · intro h
      refine ⟨x - z, HPolytope.mem_ineqs_iff.mpr fun i => ?_, sub_add_cancel x z⟩
      have := HPolytope.mem_ineqs_iff.mp h i
      rw [Matrix.mulVec_sub, Pi.sub_apply]
      rw [Pi.add_apply] at this
      linarith
    · rintro ⟨y, hy, rfl⟩
      refine HPolytope.mem_ineqs_iff.mpr fun i => ?_
      have := HPolytope.mem_ineqs_iff.mp hy i
      rw [Matrix.mulVec_add, Pi.add_apply, Pi.add_apply]
      linarith
  -- the base polytope: bounded by the simplex rows
  have hbQ : Bornology.IsBounded Q := by
    rw [hQ, HPolytope.isBounded_iff_supportFunc_simplex]
    simp only [supportFunc_le_coe_iff]
    refine ⟨fun i => ⟨1, fun x hx => ?_⟩, ⟨√n, fun x hx => ?_⟩⟩
    · have := HPolytope.mem_ineqs_iff.mp hx (Fin.castAdd m (Fin.castAdd 1 i))
      have hrow : (HPolytope.simplexRows ℓ *ᵥ x) (Fin.castAdd m (Fin.castAdd 1 i)) = x i := by
        show HPolytope.simplexRows ℓ (Fin.castAdd m (Fin.castAdd 1 i)) ⬝ᵥ x = x i
        rw [aux_row_coord, single_one_dotProduct]
      rw [hrow] at this
      simpa using this
    -- the last simplex row: `-(1/√n) ∑ xᵢ ≤ 1`
    · have := HPolytope.mem_ineqs_iff.mp hx (Fin.castAdd m (Fin.natAdd n 0))
      have hrow : (HPolytope.simplexRows ℓ *ᵥ x) (Fin.castAdd m (Fin.natAdd n 0)) =
          -(1 / √n) * ∑ i, x i := by
        show HPolytope.simplexRows ℓ (Fin.castAdd m (Fin.natAdd n 0)) ⬝ᵥ x = _
        rw [aux_row_sum]
        simp [dotProduct, Finset.mul_sum]
      rw [hrow, Pi.one_apply] at this
      have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
      have key : -(1 / √(n : ℝ)) * ∑ i, x i = (-∑ i, x i) / √n := by ring
      rw [key, div_le_iff₀ hs, one_mul] at this
      simp only [LinearMap.neg_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_proj,
        Function.eval]
      exact this
  -- the unit ball fits inside: every row is at most a unit vector
  have hiQ : (interior Q).Nonempty := by
    rw [hQ, HPolytope.ineqs_interior_nonempty_iff]
    exact ⟨0, 1, one_pos, fun r => by
      rw [Matrix.mulVec_zero, Pi.zero_apply, zero_add, one_mul]
      exact aux_rows_le ℓ hn hℓ r⟩
  -- an invertible linear map, then a translation
  have hbij : Function.Bijective (Matrix.mulVecLin M) := by
    refine ⟨fun x y h => ?_, fun y => ⟨M⁻¹ *ᵥ y, ?_⟩⟩
    · have h' : M⁻¹ *ᵥ (M *ᵥ x) = M⁻¹ *ᵥ (M *ᵥ y) := congrArg (M⁻¹ *ᵥ ·) h
      rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM,
        Matrix.one_mulVec, Matrix.one_mulVec] at h'
    · show M *ᵥ (M⁻¹ *ᵥ y) = y
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM, Matrix.one_mulVec]
  have hprops := image_linearMap_properties (Matrix.mulVecLin M) Q
  have hMQb : Bornology.IsBounded ((M *ᵥ ·) '' Q) := hprops.2.2.1 hbQ
  have hMQi : (interior ((M *ᵥ ·) '' Q)).Nonempty := (hprops.2.2.2.1 hbij).2.1 hiQ
  rw [himg]
  refine ⟨?_, ?_⟩
  · have : (· + z) '' ((M *ᵥ ·) '' Q) ⊆ (M *ᵥ ·) '' Q + ({z} : Set (Vec ℝ n)) := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hy, z, rfl, rfl⟩
    exact (hMQb.add Bornology.isBounded_singleton).subset this
  · have hh : (· + z) '' ((M *ᵥ ·) '' Q) = (Homeomorph.addRight z) '' ((M *ᵥ ·) '' Q) := rfl
    rw [hh, ← (Homeomorph.addRight z).image_interior]
    exact hMQi.image _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
