module

public import CORALean.Global.JacobiSliceExistence
public import CORALean.ContSet.Interval.Float.Theorems.LeSound
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.MinusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.RecipOuter
public import CORALean.ContSet.PolyZonotope.Float.Operations.InnerStep
public import CORALean.ContSet.PolyZonotope.Float.Operations.JacobianBox
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MonoBoxOuter
public import CORALean.ContSet.PolyZonotope.Real.Operations.Basic
public import CORALean.Global.JacobiSlice
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import CORALean.ContSet.PolyZonotope.Real.Theorems.HasFDerivAtPoint

@[expose] public section

/-!
# An accepted `innerStep` proves an inner box

Where `innerStep` returns `t` with `u1_ + t ⊆ U1_ ⊆ U1` and `u1_ ∈ U1_`, every point of `Y` is
the dependent point at some factor vector of `X`: every real Jacobi step of
`exists_jacobiSlice_eq_of_jacobi` lies in `u1_ + t`, the Jacobian on the slice in
`C·jacobianBox` (`aux_jacobianBox_outer`, `matMul_outer`), `C(y - f(x_))` in `b` (a hypothesis), the
step's interval operations outward (`recip_outer`, `times_outer`, `mtimesIntervalMat_outer`), and
`J₂(U2_ - u2_) ∋ 0`; the slice lies in `X` because `U1_ ⊆ U1` and `x_` is in `X` off `ind`.

## Inputs
* `pZ` – polynomial zonotope
* `X` – factor box
* `X₀` – inner factor box
* `Y` – target box
* `ind` – selected factor indices
* `C` – approximate inverse Jacobian
* `xc` – center of the factor box
* `b` – residual box
* `U` – candidate enclosure box

## Hypotheses
* `hC` – the matrix is injective
* `hxc` – center lies in the box outside the selected factors
* `hb` – the box covers the residuals
* `hU` – candidate lies in the selected factor box
* `hmem` – center lies in the candidate

## Conclusion
* an accepted step shows the target box lies in the image
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open Matrix
variable {m n : ℕ}

/-- A selected coordinate reads `v`. -/
private theorem _root_.CORALean.aux_jacobiSlice_apply_ind (xc : Fin m → ℝ) {ind : Fin n → Fin m}
    (hind : Function.Injective ind) (v : Fin n → ℝ) (i : Fin n) :
    jacobiSlice xc ind v (ind i) = v i := by
  simp only [jacobiSlice, Pi.add_apply, mulVec, dotProduct, of_apply, Pi.sub_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (fun h => hj (hind h)), zero_mul])
    (fun h => absurd (Finset.mem_univ i) h), if_pos rfl, one_mul]
  ring


/-- A coordinate not selected reads `xc`. -/
private theorem _root_.CORALean.aux_jacobiSlice_apply_of_ne (xc : Fin m → ℝ) {ind : Fin n → Fin m}
    (v : Fin n → ℝ)
    {k : Fin m} (hk : ∀ i, ind i ≠ k) : jacobiSlice xc ind v k = xc k := by
  simp [jacobiSlice, mulVec, dotProduct, hk]

end


/-- `jacobianBox` encloses the Jacobian. -/
private theorem PolyZonotope.aux_jacobianBox_outer (pZ : PolyZonotope (Vec 𝕋 n))
    (X : Interval (Vec 𝕋 pZ.p)) {a : Vec ℝ pZ.p} (ha : a ∈ X.construct) : -- --- CONCL ---
    Real.PolyZonotope.jacobianMat (PolyZonotope.nominal pZ) a ∈
      (PolyZonotope.jacobianBox pZ X).construct := by -- --- PROOF ---
  rw [PolyZonotope.jacobianBox, Interval.materialiseMat_eq]
  refine Interval.mem_mat_iff.mpr fun i k => ?_
  -- the lowered monomials, and the exact coefficients between their roundings
  have hm := PolyZonotope.monoBox_outer
    (fun k' l => if k' = k then pZ.E k l - 1 else pZ.E k' l) X ha
  have hC : (fun i l => (pZ.E k l : ℝ) * toReal (pZ.G l i)) ∈
      (⟨fun i l => nsmulDown (pZ.E k l) (pZ.G l i), fun i l => nsmulUp (pZ.E k l) (pZ.G l i)⟩ :
        Interval (Mat 𝕋 n pZ.h)).construct :=
    Interval.mem_mat_iff.mpr fun i l => ⟨nsmulDown_le _ _, le_nsmulUp _ _⟩
  have h := Interval.mtimesIntervalMat_outer _ _ (Set.mem_biUnion hC ⟨_, hm, rfl⟩) i
  -- the column's point is that product, coordinate `i`
  have e : Real.PolyZonotope.jacobianMat (PolyZonotope.nominal pZ) a i k
      = Matrix.mulVec (fun i l => (pZ.E k l : ℝ) * toReal (pZ.G l i))
        (fun l => Real.PolyZonotope.monomial
          (fun k' l => if k' = k then pZ.E k l - 1 else pZ.E k' l) a l) i := by
    simp [Real.PolyZonotope.jacobianMat, Real.PolyZonotope.jacobian, Real.PolyZonotope.point,
      Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rfl
  rw [e]
  exact h


section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p : ℕ}

/-- The slice through a point lies in `step_sliceBox`. -/
private theorem PolyZonotope.aux_jacobiSlice_mem_sliceBox (X₀ : Interval (Vec 𝕋 p))
    {ind : Fin n → Fin p}
    (hind : Function.Injective ind) (U : Interval (Vec 𝕋 n)) {xc : Vec ℝ p} {v : Vec ℝ n}
    (hv : v ∈ U.construct)
    (hxc : ∀ k, (∀ i, ind i ≠ k) → toReal (X₀.inf k) ≤ xc k ∧ xc k ≤ toReal (X₀.sup k))
    : -- --- CONCL ---
    jacobiSlice xc ind v ∈ (PolyZonotope.step_sliceBox X₀ ind U).construct := by -- --- PROOF ---
  intro k
  show toReal ((PolyZonotope.step_sliceBox X₀ ind U).inf k) ≤ jacobiSlice xc ind v k ∧
    jacobiSlice xc ind v k ≤ toReal ((PolyZonotope.step_sliceBox X₀ ind U).sup k)
  simp only [PolyZonotope.step_sliceBox]
  cases h : (List.finRange n).find? fun i => decide (ind i = k) with
  | some i =>
    -- `k` is `ind i`, where the slice reads `v`
    have hik : ind i = k := of_decide_eq_true (List.find?_some (p := fun i => decide (ind i = k)) h)
    rw [← hik, aux_jacobiSlice_apply_ind xc hind v i]
    exact hv i
  | none =>
    -- no coordinate of `U` sits at `k`, so the slice reads `xc`
    have hk : ∀ i, ind i ≠ k := fun i hi =>
      absurd (decide_eq_true hi) (List.find?_eq_none.mp h i (List.mem_finRange i))
    rw [aux_jacobiSlice_apply_of_ne xc v hk]
    exact hxc k hk

end


/-- The dependent point map is a polynomial, so `C¹`. -/
private theorem PolyZonotope.aux_contDiff_point (pZ : CORALean.Real.PolyZonotope (Vec ℝ n)) :
    ContDiff ℝ 1 pZ.point := by
  unfold CORALean.Real.PolyZonotope.point CORALean.Real.PolyZonotope.monomial
  refine contDiff_const.add (ContDiff.sum fun l _ => ?_)
  exact (contDiff_prod fun k _ => (contDiff_apply ℝ ℝ k).pow _).smul contDiff_const


-- =======================================  MAIN THEOREM  ======================================= --

/-- Where `u1_ + t ⊆ U1_ ⊆ U1` and `u1_ ∈ U1_`, `Y` is inside `f(X)`. -/
theorem PolyZonotope.innerStep_subset_image (pZ : PolyZonotope (Vec 𝕋 n))
    (X X₀ : Interval (Vec 𝕋 pZ.p)) (Y : Interval (Vec 𝕋 n)) (ind : Fin n ↪ Fin pZ.p) (C : Mat 𝕋 n n)
    (hC : Function.Injective (toRealMat C).mulVec) (xc : Vec 𝕋 pZ.p)
    (hxc : ∀ k, (∀ i, ind i ≠ k) → (toReal (X.inf k) ≤ toReal (xc k) ∧
      toReal (xc k) ≤ toReal (X.sup k)) ∧ (toReal (X₀.inf k) ≤ toReal (xc k) ∧
      toReal (xc k) ≤ toReal (X₀.sup k))) (b : Interval (Vec 𝕋 n))
    (hb : ∀ y ∈ Y.construct, Matrix.mulVec (toRealMat C)
      (y - (PolyZonotope.nominal pZ).point (toRealVec xc)) ∈ b.construct) (U : Interval (Vec 𝕋 n))
    (hU : U.construct ⊆ (⟨fun i => X.inf (ind i), fun i => X.sup (ind i)⟩ :
      Interval (Vec 𝕋 n)).construct)
    (hmem : (Interval.point fun i => xc (ind i)).le U = true) : -- --- CONCL ---
    ∀ t ∈ PolyZonotope.innerStep pZ X₀ ind C xc b U,
      (((Interval.point fun i => xc (ind i)).plus t).le U = true) →
      Y.construct ⊆ (PolyZonotope.nominal pZ).point '' X.construct := by -- --- PROOF ---
  intro t (h : PolyZonotope.innerStep pZ X₀ ind C xc b U = some t) hcand
  unfold PolyZonotope.innerStep at h
  dsimp only at h
  split at h
  case isFalse => cases h
  rename_i hD
  cases h
  simp only [Interval.materialiseMat_eq, Interval.materialise_eq] at hD hcand
  set CJ := Interval.matMul (Interval.point C) (PolyZonotope.jacobianBox pZ
    (PolyZonotope.step_sliceBox X₀ ind U))
  -- the Jacobian on the slice lies in `C·jacobianBox`
  have hCJ : ∀ z ∈ (PolyZonotope.step_sliceBox X₀ ind U).construct,
      toRealMat C * Real.PolyZonotope.jacobianMat (PolyZonotope.nominal pZ) z ∈
        CJ.construct := fun z hz =>
    Interval.matMul_outer _ _ (Interval.mem_point C) (PolyZonotope.aux_jacobianBox_outer pZ _ hz)
  intro y hy
  have hsel : ∀ k, (List.finRange n).any (fun i => decide (ind i = k)) = false →
      ∀ i, ind i ≠ k := fun k hk i hi =>
    (List.any_eq_false.mp hk) i (List.mem_finRange i) (decide_eq_true hi)
  -- `u1_` in `U1_`
  have hu : (fun i => toRealVec xc (ind i)) ∈ Set.Icc (toRealVec U.inf) (toRealVec U.sup) := by
    have h := Interval.le_subset hmem (Interval.mem_point fun i => xc (ind i))
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  -- the Jacobian of the slice in `CJ`
  have hJ : ∀ v ∈ Set.Icc (toRealVec U.inf) (toRealVec U.sup), ∀ i j,
      (toRealMat C * Real.PolyZonotope.jacobianMat (PolyZonotope.nominal pZ)
        (jacobiSlice (toRealVec xc) ind v)) i (ind j) ∈
          Set.Icc (toReal (CJ.inf i (ind j))) (toReal (CJ.sup i (ind j))) := by
    intro v hv i j
    have hz := PolyZonotope.aux_jacobiSlice_mem_sliceBox X₀ ind.injective U
      (fun i => ⟨hv.1 i, hv.2 i⟩) fun k hk => (hxc k hk).2
    exact Interval.mem_mat_iff.mp (hCJ _ hz) i (ind j)
  refine Exists.elim (exists_jacobiSlice_eq_of_jacobi
    (PolyZonotope.aux_contDiff_point (PolyZonotope.nominal pZ))
    (fun z => Real.PolyZonotope.hasFDerivAt_point (PolyZonotope.nominal pZ) z)
    (toRealVec xc) hC hu hJ y ?_) fun v hvf => ?_
  rotate_left
  · -- the slice is in `X`: `v` at `ind`, `xc` elsewhere
    obtain ⟨hv, hfv⟩ := hvf
    refine ⟨_, fun k => ?_, hfv⟩
    show toReal (X.inf k) ≤ jacobiSlice (toRealVec xc) ind v k ∧
      jacobiSlice (toRealVec xc) ind v k ≤ toReal (X.sup k)
    by_cases hk : ∃ i, ind i = k
    · obtain ⟨i, rfl⟩ := hk
      rw [aux_jacobiSlice_apply_ind _ ind.injective]
      exact hU (fun i => ⟨hv.1 i, hv.2 i⟩) i
    · rw [aux_jacobiSlice_apply_of_ne _ _ fun i hi => hk ⟨i, hi⟩]
      exact (hxc k fun i hi => hk ⟨i, hi⟩).1
  · intro A hA v hv i
    have hvU : v ∈ U.construct := fun i => ⟨hv.1 i, hv.2 i⟩
    -- the diagonal is bounded away from `0`
    have hDi := List.all_eq_true.mp hD i (List.mem_finRange i)
    simp only [Bool.or_eq_true] at hDi
    have hAii : A i i ≠ 0 := by
      rcases hDi with h | h
      · exact ne_of_gt (lt_of_lt_of_le (lt_of_eq_of_lt (toReal_zero (𝕋 := 𝕋)).symm
          (toReal_lt_of_ltStrict h)) (hA i i).1)
      · exact ne_of_lt (lt_of_le_of_lt (hA i i).2 (lt_of_lt_of_eq (toReal_lt_of_ltStrict h)
          (toReal_zero (𝕋 := 𝕋))))
    refine ⟨hAii, ?_⟩
    -- every interval operation of `t`, at the real values
    set A' : Mat ℝ n n := fun i j => if i = j then 0 else A i j
    have hA' : A' ∈ (⟨fun i j => if i = j then zero else CJ.inf i (ind j),
        fun i j => if i = j then zero else CJ.sup i (ind j)⟩ :
          Interval (Mat 𝕋 n n)).construct := by
      refine Interval.mem_mat_iff.mpr fun i j => ?_
      by_cases hij : i = j
      · simp only [A', if_pos hij, toReal_zero, le_refl, and_self]
      · simp only [A', if_neg hij]
        exact hA i j
    have hw := Interval.minus_outer U (Interval.point fun i => xc (ind i))
      (Set.sub_mem_sub hvU (Interval.mem_point _))
    have hoff := Interval.mtimesIntervalMat_outer _ _ (Set.mem_biUnion hA' ⟨_, hw, rfl⟩)
    have hr := Interval.minus_outer _ _ (Set.sub_mem_sub (hb y hy) hoff)
    have hdiag : (fun i => A i i) ∈ (⟨fun i => CJ.inf i (ind i), fun i => CJ.sup i (ind i)⟩ :
        Interval (Vec 𝕋 n)).construct := fun i => hA i i
    have hrec := Interval.recip_outer _ (fun i => by
      have h := List.all_eq_true.mp hD i (List.mem_finRange i)
      simpa only [Bool.or_eq_true] using h) ⟨_, hdiag, rfl⟩
    have ht₁ := Interval.times_outer _ _ ⟨_, hrec, _, hr, rfl⟩
    -- `J₂(U2_ - u2_)` holds `0`: a real matrix in `J₂` times the zero vector
    have hz := PolyZonotope.aux_jacobiSlice_mem_sliceBox X₀ ind.injective U hvU
      fun k hk => (hxc k hk).2
    -- the matrix: `C Df` on the slice off `u₁`, `0` on it
    have hJ2 : (fun i k => if (List.finRange n).any (fun i => decide (ind i = k)) then 0
        else (toRealMat C * Real.PolyZonotope.jacobianMat (PolyZonotope.nominal pZ)
          (jacobiSlice (toRealVec xc) ind v)) i k) ∈ (⟨fun i k =>
            if (List.finRange n).any (fun i => decide (ind i = k)) then zero else CJ.inf i k,
          fun i k => if (List.finRange n).any (fun i => decide (ind i = k)) then zero
            else CJ.sup i k⟩ : Interval (Mat 𝕋 n pZ.p)).construct := by
      refine Interval.mem_mat_iff.mpr fun i k => ?_
      by_cases hk : ((List.finRange n).any fun i => decide (ind i = k)) = true
      · simp only [hk, ↓reduceIte, toReal_zero, le_refl, and_self]
      · simp only [hk]
        exact Interval.mem_mat_iff.mp (hCJ _ hz) i k
    -- the vector: `0`, which `U2_ - u2_` holds as `x_` lies in `X_` off `u₁`
    have hW2 : (0 : Vec ℝ pZ.p) ∈ (⟨fun k => if (List.finRange n).any
          (fun i => decide (ind i = k)) then zero else subDown (X₀.inf k) (xc k),
        fun k => if (List.finRange n).any (fun i => decide (ind i = k)) then zero
          else subUp (X₀.sup k) (xc k)⟩ : Interval (Vec 𝕋 pZ.p)).construct := by
      intro k
      show toReal (if _ then _ else _) ≤ 0 ∧ 0 ≤ toReal (if _ then _ else _)
      by_cases hk : ((List.finRange n).any fun i => decide (ind i = k)) = true
      · simp only [hk, ↓reduceIte, toReal_zero, le_refl, and_self]
      · simp only [hk]
        have h := (hxc k (hsel k (Bool.eq_false_iff.mpr hk))).2
        exact ⟨le_trans (subDown_le_sub _ _) (by linarith),
          le_trans (by linarith) (sub_le_subUp _ _)⟩
    have h0 := Interval.mtimesIntervalMat_outer _ _ (Set.mem_biUnion hJ2 ⟨_, hW2, rfl⟩)
    simp only [Matrix.mulVec_zero] at h0
    have ht := Interval.minus_outer _ _ (Set.sub_mem_sub ht₁ h0)
    have hc := Interval.le_subset hcand
      (Interval.plus_outer _ _ (Set.add_mem_add (Interval.mem_point _) ht)) i
    -- the real step is that point's coordinate `i`
    have hsum : (Matrix.mulVec A' (v - RealImage.realImage fun i => xc (ind i))) i
        = ∑ j ∈ Finset.univ.erase i, A i j * (v j - toRealVec xc (ind j)) := by
      simp only [Matrix.mulVec, dotProduct, A']
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl, zero_mul, zero_add]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hj))]
      rfl
    have e : toRealVec xc (ind i) + ((Matrix.mulVec (toRealMat C)
          (y - (PolyZonotope.nominal pZ).point (toRealVec xc))) i
          - ∑ j ∈ Finset.univ.erase i, A i j * (v j - toRealVec xc (ind j))) / A i i
        = (RealImage.realImage (fun i => xc (ind i)) + ((fun i => (A i i)⁻¹ *
          ((Matrix.mulVec (toRealMat C) (y - (PolyZonotope.nominal pZ).point
            (toRealVec xc))) - Matrix.mulVec A' (v - RealImage.realImage fun i => xc (ind i)))
              i) - 0)) i := by
      simp only [Pi.add_apply, Pi.sub_apply, sub_zero, hsum, div_eq_inv_mul]
      rfl
    rw [e]
    exact ⟨hc.1, hc.2⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
