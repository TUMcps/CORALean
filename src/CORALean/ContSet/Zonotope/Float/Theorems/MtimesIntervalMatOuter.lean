import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemMatResidual
import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul

/-!
# `Zonotope.mtimesIntervalMat` over-approximates every matrix in the box

A member `A` of the box acts on `z + e`, `z` in the nominal zonotope and `e` in
the error box, as `mid(M)(z + e) + (A - mid(M)) z + (A - mid(M)) e`. `mtimes_outer`
covers the first; the third is the box-times-box product
`Interval.mtimesIntervalMat_outer` encloses; the second is at most
`|A - mid(M)| (|c| + Σ|G|)` per coordinate, which is the rounded-up radius of
the new diagonal generators, so a coefficient in `[-1, 1]` reaches it
(`Real.Zonotope.coefficient`).
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   25-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `A` splits into its action through the centre matrix and the leftover. -/
theorem Zonotope.aux_mulVec_split (IM : Interval (Mat 𝕋 m n)) (A : Mat ℝ m n) (x : Vec ℝ n) :
    A *ᵥ x = toRealMat (Interval.centreMat IM) *ᵥ x
      + (fun i j => A i j - toReal (Interval.centreMat IM i j)) *ᵥ x := by -- --- PROOF ---
  rw [← Matrix.add_mulVec]
  congr 1
  funext i j
  show A i j = toReal (Interval.centreMat IM i j) + (A i j - toReal (Interval.centreMat IM i j))
  ring

/-- A point of the nominal zonotope reaches no further than `|c| + Σ|G|`, rounded up. -/
theorem Zonotope.aux_abs_le_nominal {Z : Zonotope 𝕋 n} {z : Vec ℝ n}
    (hz : z ∈ nominalSet Z) (j : Fin n) :
    |z j| ≤ toReal (addUp (absolute (Z.c j)) (radius Z.G j)) := by -- --- PROOF ---
  obtain ⟨β, hβ, hzβ⟩ := Zonotope.mem_nominalSet_iff.mp hz
  have hgen := abs_sum_le_radius (d := Z.G) (Δ := fun i j => toReal (Z.G i j))
    (fun _ _ => le_refl _) hβ j
  have hup := add_le_addUp (absolute (Z.c j)) (radius Z.G j)
  rw [toReal_absolute] at hup
  rw [hzβ j]
  exact le_trans (le_trans (abs_add_le _ _) (by linarith)) hup

/-- What the residual does to the nominal part stays within the new generators' radius. -/
theorem Zonotope.aux_abs_residual_le (IM : Interval (Mat 𝕋 m n)) {Z : Zonotope 𝕋 n}
    {R : Mat ℝ m n}
    (hR : R ∈ (Interval.matResidual IM.inf IM.sup (Interval.centreMat IM)).construct)
    {z : Vec ℝ n} (hz : z ∈ nominalSet Z) (i : Fin m) :
    |(R *ᵥ z) i| ≤ toReal (sumUp fun j =>
      mulUp (maximum (absolute ((Interval.matResidual IM.inf IM.sup
          (Interval.centreMat IM)).inf i j))
        (absolute ((Interval.matResidual IM.inf IM.sup (Interval.centreMat IM)).sup i j)))
      (addUp (absolute (Z.c j)) (radius Z.G j))) := by -- --- PROOF ---
  set Rs := Interval.matResidual IM.inf IM.sup (Interval.centreMat IM)
  show |∑ j, R i j * z j| ≤ _
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ (sum_le_sumUp _))
  refine Finset.sum_le_sum fun j _ => ?_
  -- each entry of the residual below the larger magnitude of its bounds
  have hRij := hR (i, j)
  simp only [Entrywise.entry_mat] at hRij
  have hab : |R i j| ≤ toReal (maximum (absolute (Rs.inf i j)) (absolute (Rs.sup i j))) := by
    rw [toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs hRij.1 hRij.2
  rw [abs_mul]
  exact le_trans (mul_le_mul hab (Zonotope.aux_abs_le_nominal hz j) (abs_nonneg _)
    (le_trans (abs_nonneg _) hab)) (mul_le_mulUp _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mtimesIntervalMat_outer (IM : Interval (Mat 𝕋 m n)) (Z : Zonotope 𝕋 n) :
    (⋃ A ∈ IM.construct, (A *ᵥ ·) '' Z.construct) ⊆
      (Zonotope.mtimesIntervalMat IM Z).construct := by -- --- PROOF ---
  rintro y hy
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
  obtain ⟨A, hA, x, hxmem, rfl⟩ := hy
  obtain ⟨z, hz, e, he, rfl⟩ := hxmem
  set C := Interval.centreMat IM
  set Rs := Interval.matResidual IM.inf IM.sup C
  set R : Mat ℝ m n := fun i j => A i j - toReal (C i j)
  -- the centre matrix acts through `mtimes`, already proven sound
  obtain ⟨t₀, ht₀, e₀, he₀, hsum⟩ := Zonotope.mtimes_outer C Z ⟨z + e, ⟨z, hz, e, he, rfl⟩, rfl⟩
  have hsum' : t₀ + e₀ = toRealMat C *ᵥ (z + e) := hsum
  -- `A` known only to within `matResidual` of the centre matrix
  have hR : R ∈ Rs.construct := Interval.sub_mem_matResidual fun i j => hA (i, j)
  -- the residual on the error box, box times box
  have hRe : R *ᵥ e ∈ (Interval.mtimesIntervalMat Rs Z.E).construct :=
    Interval.mtimesIntervalMat_outer _ _ (Set.mem_biUnion hR ⟨e, he, rfl⟩)
  -- the residual on the nominal part, within the new generators
  have hbound := Zonotope.aux_abs_residual_le IM hR hz
  obtain ⟨γ, hγ, ht₀γ⟩ := Zonotope.mem_nominalSet_iff.mp ht₀
  set b : Vec 𝕋 m := fun i => sumUp fun j =>
    mulUp (maximum (absolute (Rs.inf i j)) (absolute (Rs.sup i j)))
      (addUp (absolute (Z.c j)) (radius Z.G j))
  have hb0 : ∀ i, 0 ≤ toReal (b i) := fun i => le_trans (abs_nonneg _) (hbound i)
  refine ⟨t₀ + R *ᵥ z, ?_, e₀ + R *ᵥ e, Interval.plus_outer _ _ (Set.add_mem_add he₀ hRe), ?_⟩
  · -- the witness: `mid(M) Z`'s coefficients, then one per coordinate scaled to the radius
    refine Zonotope.mem_nominalSet_iff.mpr
      ⟨Fin.append γ (fun i => Real.Zonotope.coefficient (toReal (b i)) ((R *ᵥ z) i)), ?_,
        fun i => ?_⟩
    · refine Fin.addCases (fun l => ?_) (fun i => ?_)
      · simpa using hγ l
      · simp only [Fin.append_right]
        exact Real.Zonotope.abs_coefficient_le_one (hb0 i) (hbound i)
    · show t₀ i + (R *ᵥ z) i = toReal (mulVecDown C Z.c i)
        + ∑ j : Fin (Z.h + m), toReal (Fin.append (matMulDown C Z.G i)
          (diagonalBlock b i) j) * Fin.append (m := Z.h) γ
            (fun i => Real.Zonotope.coefficient (toReal (b i)) ((R *ᵥ z) i)) j
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, toReal_diagonalBlock]
      rw [Real.Zonotope.sum_diagonal_mul, toRealVec, Real.Zonotope.mul_coefficient (hbound i),
        ht₀γ i, add_assoc]
      rfl
  · show t₀ + R *ᵥ z + (e₀ + R *ᵥ e) = A *ᵥ (z + e)
    rw [Zonotope.aux_mulVec_split IM A (z + e), ← hsum', Matrix.mulVec_add]
    abel

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
