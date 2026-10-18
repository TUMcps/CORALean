module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Plus
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AddSubMemNominalSet
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AbsSubLeBoxRadius
public import CORALean.ContSet.Ellipsoid.Float.Theorems.InflateSubPosSemidef
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsPsdSound
public import CORALean.ContSet.Ellipsoid.Real.Theorems.PlusOuter
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.InflatedContSet.Theorems.PlusSubset

@[expose] public section

/-!
# `Ellipsoid.plus` encloses the Minkowski sum

`InflatedContSet.plus_subset` reduces this to the nominal parts and the box. A certified operand's
nominal part is the ellipsoid of its `Q`; an uncertified one's lies in its box about its center
(`abs_sub_le_boxRadius`), so it is its center plus a point of that box. The exact layer's
`plus_outer` puts the sum of the two ellipsoids (an uncertified one taken as its center) in the
ellipsoid of `s₁² Q₁ + s₂² Q₂`, whose stored rounding dominates it (`inflate_sub_posSemidef`), so
the sum about the stored center lies in the nominal part (`add_sub_mem_nominalSet`); the center's
rounding and the two boxes are what the error box adds.

The scalings are non-zero because the hypothesis gives their reciprocals a finite sum, so the
caller states that separately — `1/0` is `0` in Lean and would otherwise satisfy the bound
vacuously.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of the nominal part: a point of a real ellipsoid about the stored center, of shape `Q`
where `isPsd` certifies it and `0` where not, plus a point of the operand's box in `plus`. -/
theorem Ellipsoid.aux_plus_split (E : Ellipsoid 𝕋 n) {x : Vec ℝ n}
    (hx : x ∈ nominalSet E) : -- --- STMT ---
    ∃ A : Real.Ellipsoid n, A.q = toRealVec E.q
      ∧ A.Q = (if Ellipsoid.isPsd E.Q = true then toRealMat E.Q else 0)
      ∧ ∃ y ∈ A.construct, x - y ∈ (if Ellipsoid.isPsd E.Q = true then Interval.origin n
          else Interval.symmetric (Ellipsoid.boxRadius 64 E)).construct := by -- --- PROOF ---
  by_cases hc : Ellipsoid.isPsd E.Q = true
  · -- certified: the nominal ellipsoid itself, nothing left over
    have hpsd := Ellipsoid.posSemidef_of_isPsd hc
    refine ⟨(nominal E).ellipsoid, E.nominal_q,
      by rw [if_pos hc, Ellipsoid.nominal_of_psd hpsd], x, hx, ?_⟩
    rw [if_pos hc, sub_self, Interval.origin_exact]
    rfl
  · -- uncertified: the center, and the offset in the box
    refine ⟨Real.Ellipsoid.ofPoint (toRealVec E.q), rfl, by rw [if_neg hc]; rfl,
      toRealVec E.q, Real.Ellipsoid.mem_ofPoint _, ?_⟩
    rw [if_neg hc, Interval.mem_vec_iff]
    intro i
    have h := Ellipsoid.abs_sub_le_boxRadius hx 64 i
    simp only [Interval.symmetric, Pi.neg_apply, toReal_neg', Pi.sub_apply, toRealVec]
    exact abs_le.mp h

/-- The nominal parts: their sum, less the center's rounding and the two boxes. -/
theorem Ellipsoid.aux_plus_nominal (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n)
    (hne₁ : toReal s₁ ≠ 0) (hne₂ : toReal s₂ ≠ 0)
    (hs : 1 / toReal s₁ ^ 2 + 1 / toReal s₂ ^ 2 ≤ 1) : -- --- STMT ---
    nominalSet E₁ + nominalSet E₂ ⊆ nominalSet (Ellipsoid.plus s₁ s₂ E₁ E₂)
      + ((Ellipsoid.centerResidual E₁.q E₂.q).construct
        + (if Ellipsoid.isPsd E₁.Q = true then Interval.origin n
            else Interval.symmetric (Ellipsoid.boxRadius 64 E₁)).construct
        + (if Ellipsoid.isPsd E₂.Q = true then Interval.origin n
            else Interval.symmetric (Ellipsoid.boxRadius 64 E₂)).construct) := by -- --- PROOF ---
  rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩
  obtain ⟨A₁, hq₁, hQ₁, y₁, hy₁, hr₁⟩ := Ellipsoid.aux_plus_split E₁ hx₁
  obtain ⟨A₂, hq₂, hQ₂, y₂, hy₂, hr₂⟩ := Ellipsoid.aux_plus_split E₂ hx₂
  -- the exact layer's enclosure of the two real ellipsoids
  set F := Real.Ellipsoid.plus (toReal s₁) (toReal s₂) A₁ A₂ with hFdef
  have hyF : y₁ + y₂ ∈ F.construct :=
    Real.Ellipsoid.plus_outer _ _ A₁ A₂ hne₁ hne₂ hs ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  -- the interval matrix holds `F.Q`, which is symmetric
  have hterm : ∀ (s : 𝕋) (A : Real.Ellipsoid n) (E : Ellipsoid 𝕋 n),
      A.Q = (if Ellipsoid.isPsd E.Q = true then toRealMat E.Q else 0) →
      toReal s ^ 2 • A.Q ∈ (if Ellipsoid.isPsd E.Q = true then
        Interval.smul (mulDown s s) (mulUp s s) (Interval.point E.Q)
        else Interval.point fun _ _ => (zero : 𝕋)).construct := by
    intro s A E hA
    -- `s² Q` where certified, `0` where not
    by_cases hc : Ellipsoid.isPsd E.Q = true
    · rw [if_pos hc, hA, if_pos hc]
      exact Interval.smul_outer (by rw [sq]; exact mulDown_le_mul s s)
        (by rw [sq]; exact mul_le_mulUp s s) _ (Interval.mem_point E.Q)
    · rw [if_neg hc, hA, if_neg hc, smul_zero]
      have hm := Interval.mem_point (α := Mat 𝕋 n n) (β := Mat ℝ n n) (ι := Fin n × Fin n)
        fun _ _ => (zero : 𝕋)
      have h0 : RealImage.realImage (α := Mat 𝕋 n n) (β := Mat ℝ n n) (fun _ _ => (zero : 𝕋))
          = 0 := funext fun _ => funext fun _ => toReal_zero
      rwa [h0] at hm
  have hX : F.Q ∈ (Interval.matPlus _ _).construct :=
    Interval.matPlus_outer _ _ (hterm s₁ A₁ E₁ hQ₁) (hterm s₂ A₂ E₂ hQ₂)
  -- the inflated sum dominates `F.Q`, so `F` lies in the nominal part
  have hsym : ∀ i j, F.Q i j = F.Q j i := fun i j => by
    have h := F.psd.isHermitian.eq
    simp only [conjTranspose_eq_transpose_of_trivial] at h
    exact (congrFun (congrFun h i) j).symm
  have hdom : (toRealMat (Ellipsoid.plus s₁ s₂ E₁ E₂).Q - F.Q).PosSemidef :=
    Ellipsoid.inflate_sub_posSemidef (Interval.mem_mat_iff.mp hX) hsym
  have hmem := Ellipsoid.add_sub_mem_nominalSet (Or.inr hdom) hyF
  -- the center's rounding
  have hres : (fun i => toReal (E₁.q i) + toReal (E₂.q i) - toReal (addDown (E₁.q i) (E₂.q i)))
      ∈ (Ellipsoid.centerResidual E₁.q E₂.q).construct :=
    Interval.sub_mem_residual fun _ => ⟨addDown_le_add _ _, add_le_addUp _ _⟩
  refine ⟨_, hmem, _, ⟨_, ⟨_, hres, _, hr₁, rfl⟩, _, hr₂, rfl⟩, ?_⟩
  have hFq : F.q = toRealVec E₁.q + toRealVec E₂.q := by
    show A₁.q + A₂.q = _
    rw [hq₁, hq₂]
  funext i
  rw [hFq]
  simp only [Pi.add_apply, Pi.sub_apply, toRealVec, Ellipsoid.plus]
  ring

/-- The two boxes, the center's rounding and the two fallback boxes, summed. -/
theorem Ellipsoid.aux_plus_error (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n) : -- --- STMT ---
    (I_error E₁).construct + (I_error E₂).construct
      + ((Ellipsoid.centerResidual E₁.q E₂.q).construct
        + (if Ellipsoid.isPsd E₁.Q = true then Interval.origin n
            else Interval.symmetric (Ellipsoid.boxRadius 64 E₁)).construct
        + (if Ellipsoid.isPsd E₂.Q = true then Interval.origin n
            else Interval.symmetric (Ellipsoid.boxRadius 64 E₂)).construct)
      ⊆ (I_error (Ellipsoid.plus s₁ s₂ E₁ E₂)).construct := by -- --- PROOF ---
  rintro _ ⟨_, ⟨e₁, he₁, e₂, he₂, rfl⟩, _, ⟨_, ⟨r, hr, b₁, hb₁, rfl⟩, b₂, hb₂, rfl⟩, rfl⟩
  have h := Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _
    ⟨_, Interval.plus_outer _ _ ⟨e₁, he₁, e₂, he₂, rfl⟩, r, hr, rfl⟩, b₁, hb₁, rfl⟩, b₂, hb₂, rfl⟩
  have heq : e₁ + e₂ + (r + b₁ + b₂) = e₁ + e₂ + r + b₁ + b₂ := by abel
  show e₁ + e₂ + (r + b₁ + b₂) ∈ _
  rw [heq]
  exact h


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.plus_outer (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n)
    (hne₁ : toReal s₁ ≠ 0) (hne₂ : toReal s₂ ≠ 0)
    (hs : 1 / toReal s₁ ^ 2 + 1 / toReal s₂ ^ 2 ≤ 1) :
    E₁.construct + E₂.construct ⊆ (Ellipsoid.plus s₁ s₂ E₁ E₂).construct :=
  InflatedContSet.plus_subset (Ellipsoid.aux_plus_nominal s₁ s₂ E₁ E₂ hne₁ hne₂ hs)
    (Ellipsoid.aux_plus_error s₁ s₂ E₁ E₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
