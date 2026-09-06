import CORALean.ContSet.Ellipsoid.Float.Operations.CenterResidual
import CORALean.ContSet.Ellipsoid.Float.Operations.Plus
import CORALean.ContSet.Ellipsoid.Float.Operations.PlusG
import CORALean.ContSet.Ellipsoid.Float.Operations.PlusGap
import CORALean.ContSet.Ellipsoid.Float.Theorems.MemGeneratorError
import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
import CORALean.ContSet.InflatedContSet.Theorems.PlusSubset
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual

/-!
# `Ellipsoid.plus` encloses the Minkowski sum

`InflatedContSet.plus_subset` reduces this to two obligations: the nominal parts
spill only by the centre rounding and the two scalings, and the box absorbs that
spill along with the two incoming boxes.

The nominal obligation is the exact argument. The point of the enclosure's ball
that reproduces `G₁u₁ + G₂u₂` is `(u₁/s₁, u₂/s₂)`, whose squared length is at
most `1/s₁² + 1/s₂²` — which is exactly the hypothesis, and exactly what
Kurzhanski and Varaiya's `l` makes equal to one. Nothing else about the two
scalings is used, which is why they are the parameter rather than `l`.

Division appears in that ball point and only there: it is a real number in a
proof, never a computed float. The scalings are non-zero because the hypothesis
gives their reciprocals a finite sum, so the caller states that separately —
`1/0` is `0` in Lean and would otherwise satisfy the bound vacuously.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `plus`'s generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem Ellipsoid.aux_sum_univ_plus {s₁ s₂ : 𝕋} {E₁ E₂ : Ellipsoid 𝕋 n}
    (f : Fin (E₁.k + E₂.k) → ℝ) :
    ∑ j : Fin (Ellipsoid.plus s₁ s₂ E₁ E₂).k, f j
      = ∑ j, f (Fin.castAdd E₂.k j) + ∑ j, f (Fin.natAdd E₁.k j) :=
  Fin.sum_univ_add f

/-- A unit-ball point scaled coordinatewise by a common divisor, squared and
summed. -/
theorem Ellipsoid.aux_sum_div_sq {k : ℕ} (u : Vec ℝ k) (t : ℝ) :
    ∑ j, (u j / t) ^ 2 = (∑ j, u j ^ 2) * (t ^ 2)⁻¹ := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [div_pow, div_eq_mul_inv]

/-- The squared length of a unit-ball point, which is what the two summands
contribute. -/
theorem Ellipsoid.aux_sum_sq_le_one {k : ℕ} {u : Vec ℝ k} (hu : ‖u‖₂ ≤ 1) :
    ∑ j, u j ^ 2 ≤ 1 := by
  rw [← norm₂_sq, pow_two]
  calc ‖u‖₂ * ‖u‖₂ ≤ 1 * 1 := mul_le_mul hu hu (norm₂_nonneg u) zero_le_one
    _ = 1 := one_mul 1

/-- The stored generators are off by at most the gap between the two directed
scalings. -/
theorem Ellipsoid.aux_plusGap (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n) (i : Fin n)
    (j : Fin (E₁.k + E₂.k)) :
    |Fin.append (fun j => toReal s₁ * toReal (E₁.G i j) - toReal (mulDown s₁ (E₁.G i j)))
        (fun j => toReal s₂ * toReal (E₂.G i j) - toReal (mulDown s₂ (E₂.G i j))) j|
      ≤ toReal (Ellipsoid.plusGap s₁ s₂ E₁ E₂ i j) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Fin.append_left]
    show _ ≤ toReal (Fin.append _ _ (Fin.castAdd E₂.k j))
    rw [Fin.append_left, abs_le]
    have hlo := mulDown_le_mul s₁ (E₁.G i j)
    have hhi := mul_le_mulUp s₁ (E₁.G i j)
    have hgap := sub_le_subUp (mulUp s₁ (E₁.G i j)) (mulDown s₁ (E₁.G i j))
    constructor <;> linarith
  · rw [Fin.append_right]
    show _ ≤ toReal (Fin.append _ _ (Fin.natAdd E₁.k j))
    rw [Fin.append_right, abs_le]
    have hlo := mulDown_le_mul s₂ (E₂.G i j)
    have hhi := mul_le_mulUp s₂ (E₂.G i j)
    have hgap := sub_le_subUp (mulUp s₂ (E₂.G i j)) (mulDown s₂ (E₂.G i j))
    constructor <;> linarith

-- the norm bound is rebuilt over the appended generator block, one `calc` chain per half
set_option maxHeartbeats 400000 in
theorem Ellipsoid.aux_plus_nominal (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n)
    (hne₁ : toReal s₁ ≠ 0) (hne₂ : toReal s₂ ≠ 0)
    (hs : 1 / toReal s₁ ^ 2 + 1 / toReal s₂ ^ 2 ≤ 1) :
    nominalSet E₁ + nominalSet E₂ ⊆
      nominalSet (Ellipsoid.plus s₁ s₂ E₁ E₂)
        + ((Ellipsoid.centerResidual E₁.q E₂.q).construct
            + (Ellipsoid.generatorError (Ellipsoid.plusGap s₁ s₂ E₁ E₂)).construct) := by
  rintro _ ⟨x₁, hx₁', x₂, hx₂', rfl⟩
  obtain ⟨u₁, hu₁, hx₁⟩ := Ellipsoid.mem_nominalSet_iff.mp hx₁'
  obtain ⟨u₂, hu₂, hx₂⟩ := Ellipsoid.mem_nominalSet_iff.mp hx₂'
  set w : Vec ℝ (E₁.k + E₂.k) :=
    Fin.append (fun j => u₁ j / toReal s₁) (fun j => u₂ j / toReal s₂) with hwdef
  -- the appended coefficient stays in the unit ball, which is what `hs` buys
  have hw : ‖w‖₂ ≤ 1 := by
    have hsum : ∑ j, w j ^ 2 ≤ 1 := by
      rw [hwdef, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [Ellipsoid.aux_sum_div_sq u₁ (toReal s₁), Ellipsoid.aux_sum_div_sq u₂ (toReal s₂)]
      have hsq₁ : (0:ℝ) < toReal s₁ ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne₁))
      have hsq₂ : (0:ℝ) < toReal s₂ ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne₂))
      have hp₁ : (0:ℝ) ≤ (toReal s₁ ^ 2)⁻¹ := le_of_lt (inv_pos.mpr hsq₁)
      have hp₂ : (0:ℝ) ≤ (toReal s₂ ^ 2)⁻¹ := le_of_lt (inv_pos.mpr hsq₂)
      have hinv : (toReal s₁ ^ 2)⁻¹ + (toReal s₂ ^ 2)⁻¹ ≤ 1 := by
        rw [← one_div, ← one_div]
        exact hs
      -- each half's squared sum is at most one, so the two reciprocals bound the total
      calc (∑ j, u₁ j ^ 2) * (toReal s₁ ^ 2)⁻¹ + (∑ j, u₂ j ^ 2) * (toReal s₂ ^ 2)⁻¹
          ≤ 1 * (toReal s₁ ^ 2)⁻¹ + 1 * (toReal s₂ ^ 2)⁻¹ :=
            add_le_add (mul_le_mul_of_nonneg_right (Ellipsoid.aux_sum_sq_le_one hu₁) hp₁)
              (mul_le_mul_of_nonneg_right (Ellipsoid.aux_sum_sq_le_one hu₂) hp₂)
        _ ≤ 1 := by rw [one_mul, one_mul]; exact hinv
    calc ‖w‖₂ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hsum
      _ = 1 := Real.sqrt_one
  -- the witness: stored centre and generators at `w`, both shortfalls charged
  have hgen := Ellipsoid.mem_generatorError (Ellipsoid.aux_plusGap s₁ s₂ E₁ E₂) hw
  refine ⟨fun i => toReal ((Ellipsoid.plus s₁ s₂ E₁ E₂).q i)
            + ∑ j, toReal ((Ellipsoid.plus s₁ s₂ E₁ E₂).G i j) * w j,
          Ellipsoid.mem_nominalSet_iff.mpr ⟨w, hw, fun _ => rfl⟩,
          _, ⟨_, Interval.sub_mem_residual
                (fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩), _, hgen, rfl⟩, ?_⟩
  funext i
  -- stored generator plus error is the exact scaling, which cancels the division in `w`
  have hblk₁ : (∑ j, toReal (mulDown s₁ (E₁.G i j)) * (u₁ j / toReal s₁))
      + ∑ j, (toReal s₁ * toReal (E₁.G i j) - toReal (mulDown s₁ (E₁.G i j)))
          * (u₁ j / toReal s₁)
      = ∑ j, toReal (E₁.G i j) * u₁ j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by field_simp; ring
  have hblk₂ : (∑ j, toReal (mulDown s₂ (E₂.G i j)) * (u₂ j / toReal s₂))
      + ∑ j, (toReal s₂ * toReal (E₂.G i j) - toReal (mulDown s₂ (E₂.G i j)))
          * (u₂ j / toReal s₂)
      = ∑ j, toReal (E₂.G i j) * u₂ j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by field_simp; ring
  -- the goal spelled out, so the two block identities line up with it
  show toReal ((Ellipsoid.plus s₁ s₂ E₁ E₂).q i)
        + (∑ j, toReal ((Ellipsoid.plus s₁ s₂ E₁ E₂).G i j) * w j)
      + ((toReal (E₁.q i) + toReal (E₂.q i)
            - toReal (addDown (E₁.q i) (E₂.q i)))
        + ∑ j, Fin.append
            (fun j => toReal s₁ * toReal (E₁.G i j) - toReal (mulDown s₁ (E₁.G i j)))
            (fun j => toReal s₂ * toReal (E₂.G i j) - toReal (mulDown s₂ (E₂.G i j))) j
              * w j)
    = x₁ i + x₂ i
  rw [Ellipsoid.aux_sum_univ_plus (s₁ := s₁) (s₂ := s₂)
      (fun j => toReal ((Ellipsoid.plus s₁ s₂ E₁ E₂).G i j) * w j),
    Fin.sum_univ_add (f := fun j => Fin.append
      (fun j => toReal s₁ * toReal (E₁.G i j) - toReal (mulDown s₁ (E₁.G i j)))
      (fun j => toReal s₂ * toReal (E₂.G i j) - toReal (mulDown s₂ (E₂.G i j))) j * w j),
    hx₁ i, hx₂ i]
  simp only [Ellipsoid.plus, Ellipsoid.plusG, hwdef, Fin.append_left, Fin.append_right]
  linarith [hblk₁, hblk₂]

/-- The box absorbs the two incoming boxes, the centre rounding and the
scalings. -/
theorem Ellipsoid.aux_plus_error (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n) :
    E₁.err.construct + E₂.err.construct
        + ((Ellipsoid.centerResidual E₁.q E₂.q).construct
            + (Ellipsoid.generatorError (Ellipsoid.plusGap s₁ s₂ E₁ E₂)).construct) ⊆
      (Ellipsoid.plus s₁ s₂ E₁ E₂).err.construct :=
  subset_trans
    (Set.add_subset_add (Interval.plus_outer E₁.err E₂.err) (Interval.plus_outer _ _))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.plus_outer (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n)
    (hne₁ : toReal s₁ ≠ 0) (hne₂ : toReal s₂ ≠ 0)
    (hs : 1 / toReal s₁ ^ 2 + 1 / toReal s₂ ^ 2 ≤ 1) :
    E₁.construct + E₂.construct ⊆ (Ellipsoid.plus s₁ s₂ E₁ E₂).construct :=
  InflatedContSet.plus_subset (Ellipsoid.aux_plus_nominal s₁ s₂ E₁ E₂ hne₁ hne₂ hs)
    (Ellipsoid.aux_plus_error s₁ s₂ E₁ E₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
