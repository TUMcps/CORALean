module

public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.Specification.STL.Operations.DepBoxFloat
public import CORALean.Specification.STL.Theorems.ZonotopeExtremes

@[expose] public section

/-!
# `interval(Z)` over floats encloses the real one

`STL.depBoxFloat` holds the box zonotope `STL.depBox` of every real zonotope inside the float one.
The real box reaches in each coordinate exactly the extremes of its zonotope, which are points of
the float zonotope, and the float one holds every point of the float coordinates range: its radius
rounds the row sum up and its error box is the one of `Z`.

## Inputs
* `Zr` – real zonotope
* `Zf` – float zonotope

## Hypotheses
* `h` – the real zonotope lies inside the float one

## Conclusion
* the real box lies inside the float one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of a float zonotope stays within the stored center, the rounded-up radius and the error
box in each coordinate. -/
theorem STL.aux_depBoxFloat_bounds {Z : Float.Zonotope (Vec 𝕋 n)} {x : Vec ℝ n}
    (hx : x ∈ Z.construct) (i : Fin n) : -- --- CONCL ---
    toReal (Z.c i) - toReal (sumUp (fun j => absolute (Z.G j i))) + toReal (Z.I_error.inf i) ≤ x i ∧
      x i ≤ toReal (Z.c i) + toReal (sumUp (fun j => absolute (Z.G j i))) +
        toReal (Z.I_error.sup i) := by -- --- PROOF ---
  obtain ⟨z, hz, e, he, rfl⟩ := hx
  obtain ⟨β, hβ, hzβ⟩ := Float.Zonotope.mem_nominalSet_iff.1 hz
  have he' : toReal (Z.I_error.inf i) ≤ e i ∧ e i ≤ toReal (Z.I_error.sup i) :=
    Float.Interval.mem_vec_iff.1 he i
  -- the weighted generators stay within the sum of their absolute values
  have hsum : |∑ j, toReal (Z.G j i) * β j| ≤ toReal (sumUp (fun j => absolute (Z.G j i))) :=
    calc |∑ j, toReal (Z.G j i) * β j| ≤ ∑ j, |toReal (Z.G j i) * β j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, toReal (absolute (Z.G j i)) := Finset.sum_le_sum fun j _ => by
          rw [toReal_absolute, abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hβ j)
      _ ≤ _ := sum_le_sumUp _
  have hzi := hzβ i
  have hb := abs_le.1 hsum
  simp only [Pi.add_apply]
  constructor <;> linarith [he'.1, he'.2, hb.1, hb.2]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `interval(Z)` over floats holds the real `interval(Z)` of every real zonotope inside `Z`. -/
theorem STL.depBoxFloat_outer {Zr : Real.Zonotope (Vec ℝ n)} {Zf : Float.Zonotope (Vec 𝕋 n)}
    (h : Zr.construct ⊆ Zf.construct) : -- --- CONCL ---
    (STL.depBox Zr).construct ⊆ (STL.depBoxFloat Zf).construct := by -- --- PROOF ---
  intro y hy
  obtain ⟨γ, hγ, hy⟩ := Real.Zonotope.mem_construct_iff.1 hy
  -- the coordinates of `y` lie between the extremes of the real zonotope
  have hrange : ∀ i, toReal (Zf.c i) - toReal (sumUp (fun j => absolute (Zf.G j i))) +
        toReal (Zf.I_error.inf i) ≤ y i ∧ y i ≤ toReal (Zf.c i) +
        toReal (sumUp (fun j => absolute (Zf.G j i))) + toReal (Zf.I_error.sup i) := by
    intro i
    obtain ⟨⟨x₁, hx₁, e₁⟩, ⟨x₂, hx₂, e₂⟩⟩ := STL.zonotope_extremes Zr i
    have b₁ := STL.aux_depBoxFloat_bounds (h hx₁) i
    have b₂ := STL.aux_depBoxFloat_bounds (h hx₂) i
    have hy' : y i = Zr.c i + (∑ l, |Zr.G l i|) * γ i := by
      rw [hy i]
      simp [STL.depBox, Matrix.diagonal_apply]
    have hr0 : 0 ≤ ∑ l, |Zr.G l i| := Finset.sum_nonneg fun l _ => abs_nonneg _
    have hγi := abs_le.1 (hγ i)
    constructor <;> nlinarith [b₁.1, b₁.2, b₂.1, b₂.2]
  -- the error box of the float zonotope is nonempty, as it holds a point of the center
  have hne : ∀ i, toReal (Zf.I_error.inf i) ≤ toReal (Zf.I_error.sup i) := fun i => by
    obtain ⟨z, -, e, he, -⟩ := h (Real.Zonotope.center_mem_construct Zr)
    have he' : toReal (Zf.I_error.inf i) ≤ e i ∧ e i ≤ toReal (Zf.I_error.sup i) :=
      Float.Interval.mem_vec_iff.1 he i
    exact he'.1.trans he'.2
  -- the radius takes what the error box cannot
  set r : Fin n → ℝ := fun i => toReal (sumUp (fun j => absolute (Zf.G j i))) with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => by
    have := sum_le_sumUp (fun j => absolute (Zf.G j i))
    refine le_trans (Finset.sum_nonneg fun j _ => ?_) this
    rw [toReal_absolute]; exact abs_nonneg _
  -- `y` less the center, its clamp `e` into the error box, and the coefficient of the rest
  let d : Fin n → ℝ := fun i => y i - toReal (Zf.c i)
  let e : Vec ℝ n := fun i =>
    max (toReal (Zf.I_error.inf i)) (min (toReal (Zf.I_error.sup i)) (d i))
  let β : Vec ℝ n := fun i => if r i = 0 then 0 else (d i - e i) / r i
  -- what the error box cannot take is within the radius
  have hdr : ∀ i, |d i - e i| ≤ r i := fun i => by
    have h1 := (hrange i).1
    have h2 := (hrange i).2
    have h3 := hne i
    have h4 := hr0 i
    simp only [e, d, hr] at *
    rw [abs_le]
    rcases le_total (toReal (Zf.I_error.sup i)) (y i - toReal (Zf.c i)) with hs | hs
    · rw [min_eq_left hs, max_eq_right h3]; constructor <;> linarith
    · rw [min_eq_right hs]
      rcases le_total (toReal (Zf.I_error.inf i)) (y i - toReal (Zf.c i)) with hi | hi
      · rw [max_eq_right hi]; constructor <;> linarith
      · rw [max_eq_left hi]; constructor <;> linarith
  -- the coefficient scales the radius back to that rest
  have hre : ∀ i, r i * β i = d i - e i := fun i => by
    by_cases h0 : r i = 0
    · have := abs_le.1 (hdr i)
      simp only [β, h0, if_true, mul_zero]
      rw [h0] at this
      linarith [this.1, this.2]
    · simp only [β, h0, if_false]
      field_simp
  -- the clamp lies in the error box by construction
  have hmem : e ∈ Zf.I_error.construct := Float.Interval.mem_vec_iff.2 fun i => by
    refine ⟨le_max_left _ _, max_le (hne i) (min_le_left _ _)⟩
  refine ⟨fun i => toReal (Zf.c i) + r i * β i, ?_, e, hmem, ?_⟩
  · refine Float.Zonotope.mem_nominalSet_iff.2 ⟨β, fun i => ?_, fun i => ?_⟩
    · by_cases h0 : r i = 0
      · simp [β, h0]
      · simp only [β, h0, if_false, abs_div]
        have hpos := lt_of_le_of_ne (hr0 i) (Ne.symm h0)
        rw [abs_of_pos hpos, div_le_one hpos]
        exact hdr i
    · -- only the generator along coordinate `i` reaches it
      show toReal (Zf.c i) + r i * β i = toReal (Zf.c i) +
        ∑ j : Fin n, toReal (if i = j then sumUp (fun q => absolute (Zf.G q j)) else zero) * β j
      congr 1
      rw [Finset.sum_eq_single i]
      · simp [hr]
      · intro j _ hj
        simp [Ne.symm hj, toReal_zero]
      · simp
  · funext i
    show toReal (Zf.c i) + r i * β i + e i = y i
    rw [hre i]
    simp only [d]
    ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
