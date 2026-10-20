module

public import CORALean.ContSet.Interval.Float.Operations.Atan2
public import CORALean.ContSet.Interval.Float.Theorems.Atan2LoLe
public import CORALean.ContSet.Interval.Float.Theorems.Atan2HiLe
public import CORALean.ContSet.Interval.Real.Theorems.Atan2EnclosureOfPosInfX
public import CORALean.ContSet.Interval.Real.Theorems.Atan2EnclosureOfPosInfY
public import CORALean.ContSet.Interval.Real.Theorems.Atan2EnclosureOfNegSupY

@[expose] public section

/-!
# `Interval.atan2` encloses

Outer, for every box: `Complex.arg ⟨x, y⟩` lies in the result for each `x` in the `x` operand and
`y` in the `y` operand. For a coordinate in a certified half-plane the exact layer's corner-hull
enclosure applies (`atan2_enclosure_of_pos_inf_x`, `_of_pos_inf_y`, `_of_neg_sup_y`, at that
coordinate alone) and each float corner value lies beyond its exact one; elsewhere the result is
`[-π, π]`, which holds every argument. Not exact, and not CORA's corner hull across the branch
cut, which is no enclosure there.

## Inputs
* `p` – halving count
* `k` – bisection and Newton steps
* `I₁` – first interval box
* `I₂` – second interval box
* `y` – ordinate point of `I₁`
* `x` – abscissa point of `I₂`

## Hypotheses
* `hy` – `y` lies in `I₁`
* `hx` – `x` lies in `I₂`

## Conclusion
* the vector of arguments lies in the result box
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.atan2_outer (p k : ℕ) (I₁ I₂ : Interval (Vec 𝕋 n)) {y x : Vec ℝ n}
    (hy : y ∈ I₁.construct) (hx : x ∈ I₂.construct) : -- --- CONCL ---
    (fun i => Complex.arg ⟨x i, y i⟩) ∈ (Interval.atan2 p k I₁ I₂).construct := by -- --- PROOF ---
  intro i
  show toReal ((Interval.atan2 p k I₁ I₂).inf i) ≤ Complex.arg ⟨x i, y i⟩ ∧
    Complex.arg ⟨x i, y i⟩ ≤ toReal ((Interval.atan2 p k I₁ I₂).sup i)
  have hy₁ : toReal (I₁.inf i) ≤ y i ∧ y i ≤ toReal (I₁.sup i) := hy i
  have hx₁ : toReal (I₂.inf i) ≤ x i ∧ x i ≤ toReal (I₂.sup i) := hx i
  have hpp : Real.pi / 2 ≤ toReal (acosUp p k (zero : 𝕋)) := by
    have := le_acosUp p k (zero : 𝕋)
    rwa [toReal_zero, Real.arccos_zero] at this
  have h4 := add_le_addUp (acosUp p k (zero : 𝕋)) (acosUp p k (zero : 𝕋))
  have hnp := Complex.neg_pi_lt_arg (⟨x i, y i⟩ : ℂ)
  have hap := Complex.arg_le_pi (⟨x i, y i⟩ : ℂ)
  by_cases hreg : (ltStrict zero (I₂.inf i) || ltStrict zero (I₁.inf i) ||
      ltStrict (I₁.sup i) zero) = true
  swap
  · -- no half-plane certified: `[-π, π]`
    simp only [Interval.atan2, if_neg hreg, toReal_neg]
    constructor <;> linarith
  -- the box of this coordinate alone, as an exact one-dimensional box
  let J₁ : Real.Interval (Vec ℝ 1) := ⟨fun _ => toReal (I₁.inf i), fun _ => toReal (I₁.sup i)⟩
  let J₂ : Real.Interval (Vec ℝ 1) := ⟨fun _ => toReal (I₂.inf i), fun _ => toReal (I₂.sup i)⟩
  have hyJ : (fun _ => y i : Vec ℝ 1) ∈ J₁.construct := fun _ => hy₁
  have hxJ : (fun _ => x i : Vec ℝ 1) ∈ J₂.construct := fun _ => hx₁
  -- the exact corner hull holds the argument
  have hex : (fun _ => Complex.arg ⟨x i, y i⟩ : Vec ℝ 1) ∈ (J₁.atan2 J₂).construct := by
    rcases Bool.or_eq_true_iff.1 hreg with h | h
    · rcases Bool.or_eq_true_iff.1 h with h | h
      · have : 0 < toReal (I₂.inf i) := by simpa [toReal_zero] using toReal_lt_of_ltStrict h
        exact Real.Interval.atan2_enclosure_of_pos_inf_x (fun _ => this) hyJ hxJ
      · have : 0 < toReal (I₁.inf i) := by simpa [toReal_zero] using toReal_lt_of_ltStrict h
        exact Real.Interval.atan2_enclosure_of_pos_inf_y (fun _ => this) hyJ hxJ
    · have : toReal (I₁.sup i) < 0 := by simpa [toReal_zero] using toReal_lt_of_ltStrict h
      exact Real.Interval.atan2_enclosure_of_neg_sup_y (fun _ => this) hyJ hxJ
  have hex0 : (J₁.atan2 J₂).inf 0 ≤ Complex.arg ⟨x i, y i⟩ ∧
      Complex.arg ⟨x i, y i⟩ ≤ (J₁.atan2 J₂).sup 0 := hex 0
  -- each float corner is beyond the exact one
  simp only [Interval.atan2, if_pos hreg, toReal_minimum, toReal_maximum]
  refine ⟨le_trans ?_ hex0.1, le_trans hex0.2 ?_⟩
  · exact min_le_min (min_le_min (Interval.atan2Lo_le p k _ _) (Interval.atan2Lo_le p k _ _))
      (min_le_min (Interval.atan2Lo_le p k _ _) (Interval.atan2Lo_le p k _ _))
  · exact max_le_max (max_le_max (Interval.le_atan2Hi p k _ _) (Interval.le_atan2Hi p k _ _))
      (max_le_max (Interval.le_atan2Hi p k _ _) (Interval.le_atan2Hi p k _ _))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
