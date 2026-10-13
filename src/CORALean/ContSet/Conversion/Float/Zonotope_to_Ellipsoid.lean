module

public import CORALean.ContSet.Conversion.Float.Interval_to_Ellipsoid
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A zonotope as an ellipsoid, over a floating-point scalar

The exact layer scales the generators by `√h` and the cube `‖β‖∞ ≤ 1` then sits
inside the unit ball. This layer has no square root, so, as for the box, the caller
proposes `σ` and the check `h ≤ σ·σ` is all that is used of it: the classical `√h`
is the tightest admissible value rather than a required one.

What differs from the exact layer is the rounding. A generator `σ·G` cannot be
stored exactly, and unlike a box's diagonal the rounded generators are shared by
several coordinates, so the ball point `β/σ` no longer reproduces the point
exactly. The generators round up, and the residual `Σⱼ (σ Gᵢⱼ - G'ᵢⱼ) βⱼ / σ` is
bounded by the width of each product's rounding bracket, summed by `radius`, divided
by `σ` upward and added to the error box. It is a few ulps and nothing a caller has
to supply.

CORA's `ellipsoid(zonotope)` is the minimum-volume or minimum-trace enclosure, an
optimisation, and is not what this is: this is the `√h` ball, as over ℝ.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The generators scaled by the proposed `√h`, rounded up. -/
def Zonotope.ellipsoidG (Z : Zonotope (Vec 𝕋 n)) (σ : 𝕋) : Mat 𝕋 n Z.h :=
  fun i j => mulUp σ (Z.G j i)

/-- The width of each scaled generator's rounding bracket. -/
def Zonotope.ellipsoidGap (Z : Zonotope (Vec 𝕋 n)) (σ : 𝕋) : Mat 𝕋 n Z.h :=
  fun i j => subUp (mulUp σ (Z.G j i)) (mulDown σ (Z.G j i))

/-- What the rounding of the generators can move a point by, rounded up. -/
def Zonotope.ellipsoidSlack (Z : Zonotope (Vec 𝕋 n)) (σ : 𝕋) : Vec 𝕋 n :=
  fun i => divUp (radius (Z.ellipsoidGap σ) i) σ

def Zonotope.ellipsoid (Z : Zonotope (Vec 𝕋 n)) (σ : 𝕋) : Ellipsoid 𝕋 n where
  k := Z.h
  q := Z.c
  G := Z.ellipsoidG σ
  err := ⟨fun i => subDown (Z.E.inf i) (Z.ellipsoidSlack σ i),
          fun i => addUp (Z.E.sup i) (Z.ellipsoidSlack σ i)⟩

open Pointwise SoundFloatArithmetic InflatedContSet

variable [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The rounding of a generator, against the bracket that stores it. -/
theorem Zonotope.aux_ellipsoid_round_le (Z : Zonotope (Vec 𝕋 n)) (σ : 𝕋) (i : Fin n) (j : Fin Z.h) :
    |toReal σ * toReal (Z.G j i) - toReal (Z.ellipsoidG σ i j)|
      ≤ |toReal (Z.ellipsoidGap σ i j)| := by -- --- PROOF ---
  have h1 := mul_le_mulUp σ (Z.G j i)
  have h2 := mulDown_le_mul σ (Z.G j i)
  have h3 := sub_le_subUp (mulUp σ (Z.G j i)) (mulDown σ (Z.G j i))
  have hG : toReal (Z.ellipsoidG σ i j) = toReal (mulUp σ (Z.G j i)) := rfl
  have hgap : toReal (Z.ellipsoidGap σ i j)
      ≥ toReal (mulUp σ (Z.G j i)) - toReal (mulDown σ (Z.G j i)) := h3
  rw [hG]
  refine le_trans ?_ (le_abs_self _)
  rw [abs_le]
  constructor <;> linarith

/-- The residual the rounding leaves, at most the slack. -/
theorem Zonotope.aux_ellipsoid_slack (Z : Zonotope (Vec 𝕋 n)) (σ : 𝕋) (hσ : 0 < toReal σ)
    {β : Vec ℝ Z.h} (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) :
    |(∑ j, (toReal σ * toReal (Z.G j i) - toReal (Z.ellipsoidG σ i j)) * β j) / toReal σ|
      ≤ toReal (Z.ellipsoidSlack σ i) := by -- --- PROOF ---
  have hS := abs_sum_le_radius (d := Z.ellipsoidGap σ)
    (Δ := fun i j => toReal σ * toReal (Z.G j i) - toReal (Z.ellipsoidG σ i j))
    (fun i j => Z.aux_ellipsoid_round_le σ i j) hβ i
  rw [abs_div, abs_of_pos hσ, div_le_iff₀ hσ]
  refine le_trans hS ?_
  have hd := div_le_divUp (radius (Z.ellipsoidGap σ) i) σ hσ
  have := (div_le_iff₀ hσ).mp hd
  exact this


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.ellipsoid_contains (Z : Zonotope (Vec 𝕋 n)) (σ : 𝕋) (hσ : 0 < toReal σ)
    (hh : (Z.h : ℝ) ≤ toReal (mulDown σ σ)) :
    Z.construct ⊆ (Z.ellipsoid σ).construct := by -- --- PROOF ---
  rintro _ ⟨z, hzmem, e, he, rfl⟩
  obtain ⟨β, hβ, hz⟩ := Zonotope.mem_nominalSet_iff.mp hzmem
  have hne : toReal σ ≠ 0 := ne_of_gt hσ
  -- the ball point: each coefficient is at most `1/σ`, and there are `h` of them
  have hnorm : ‖fun j => β j / toReal σ‖₂ ≤ 1 := by
    have hσ2 : toReal σ ^ 2 ≥ (Z.h : ℝ) := by
      rw [pow_two]
      exact le_trans hh (mulDown_le_mul σ σ)
    have hσ2p : (0:ℝ) < toReal σ ^ 2 := by positivity
    have hterm : ∀ j : Fin Z.h, (β j / toReal σ) ^ 2 ≤ 1 / toReal σ ^ 2 := fun j => by
      rw [div_pow]
      refine div_le_div_of_nonneg_right ?_ (le_of_lt hσ2p)
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) (hβ j)
    have hsum : ∑ j : Fin Z.h, (β j / toReal σ) ^ 2 ≤ 1 := by
      calc ∑ j : Fin Z.h, (β j / toReal σ) ^ 2
          ≤ ∑ _j : Fin Z.h, 1 / toReal σ ^ 2 := Finset.sum_le_sum fun j _ => hterm j
        _ = (Z.h : ℝ) * (1 / toReal σ ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ 1 := by
            rw [mul_one_div, div_le_one hσ2p]
            exact hσ2
    calc ‖fun j => β j / toReal σ‖₂ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hsum
      _ = 1 := Real.sqrt_one
  -- what the rounded generators leave over
  set S : Vec ℝ n := fun i => (∑ j, (toReal σ * toReal (Z.G j i)
      - toReal (Z.ellipsoidG σ i j)) * β j) / toReal σ with hSdef
  have hSle : ∀ i, |S i| ≤ toReal (Z.ellipsoidSlack σ i) := fun i =>
    Z.aux_ellipsoid_slack σ hσ hβ i
  have hres : ∀ i, z i - (toReal (Z.c i) + ∑ j, toReal (Z.ellipsoidG σ i j) * (β j / toReal σ))
      = S i := fun i => by
    rw [hz i]
    show _ - (_ + ∑ j, toReal (Z.ellipsoidG σ i j) * (β j / toReal σ))
      = (∑ j, (toReal σ * toReal (Z.G j i) - toReal (Z.ellipsoidG σ i j)) * β j) / toReal σ
    rw [Finset.sum_div, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  -- the witness: the ball point `β/σ`, and the box point that absorbs `S`
  refine ⟨fun i => toReal (Z.c i) + ∑ j, toReal (Z.ellipsoidG σ i j) * (β j / toReal σ),
    Ellipsoid.mem_nominalSet_iff.mpr ⟨fun j => β j / toReal σ, hnorm, fun i => rfl⟩,
    fun i => e i + S i, fun i => ?_, funext fun i => ?_⟩
  -- the shifted error stays in the widened box
  · have h1 := subDown_le_sub (Z.E.inf i) (Z.ellipsoidSlack σ i)
    have h2 := add_le_addUp (Z.E.sup i) (Z.ellipsoidSlack σ i)
    have h3 : toReal (Z.E.inf i) ≤ e i := (he i).1
    have h4 : e i ≤ toReal (Z.E.sup i) := (he i).2
    have h5 := abs_le.mp (hSle i)
    constructor
    · show toReal (subDown (Z.E.inf i) (Z.ellipsoidSlack σ i)) ≤ e i + S i
      linarith
    · show e i + S i ≤ toReal (addUp (Z.E.sup i) (Z.ellipsoidSlack σ i))
      linarith
  · show _ + (e i + S i) = z i + e i
    have := hres i
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
