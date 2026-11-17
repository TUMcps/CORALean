module

public import CORALean.ContDynamics.LinearSys.Operations.VerifySupportDownFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsDotProductLeWeightedSum
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `LinearSys.verifySupportDownFloat` is reached by a point of the initial set

The point `c + G b` with `bⱼ` the sign of `ℓ' gⱼ` attains the support `ℓ'c + Σⱼ |ℓ' gⱼ|` along the
exact direction `ℓ`. That is at least `ℓ̃'c + Σⱼ |ℓ̃' gⱼ|` less `|(ℓ − ℓ̃)'c| + Σⱼ |(ℓ − ℓ̃)' gⱼ|`,
which is at most `Σᵢ |ℓ − ℓ̃|ᵢ (|cᵢ| + Σⱼ |gᵢⱼ|) ≤ E β`; each `|ℓ̃' gⱼ|` is at least the float
mignitude of its sums rounded down and up.

## Inputs
* `c` – float center
* `G` – float generators
* `β` – float scaled bound of the initial set
* `s` – float scales
* `ℓ` – float direction
* `E` – float error of the direction
* `ℓr` – exact direction

## Hypotheses
* `hβ0` – `β` is nonnegative
* `hβ` – every `|cᵢ| + Σⱼ |gᵢⱼ|` is at most `β sᵢ`
* `hE` – the weighted error of `ℓ̃` is at most `E`

## Conclusion
* a point of the initial set whose value along `ℓ` is at least the float bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.exists_le_dotProduct_verifySupportDownFloat (c : Vec 𝕋 n) (G : Mat 𝕋 n m)
    {β : 𝕋} {s : Vec 𝕋 n} (hβ0 : 0 ≤ toReal β)
    (hβ : ∀ i, |toReal (c i)| + ∑ j, |toReal (G i j)| ≤ toReal β * toReal (s i))
    (ℓ : Vec 𝕋 n) {E : 𝕋} {ℓr : Vec ℝ n}
    (hE : ∑ i, |ℓr i - toReal (ℓ i)| * toReal (s i) ≤ toReal E) : -- --- CONCL ---
    ∃ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) ∧
      toReal (LinearSys.verifySupportDownFloat c G β ℓ E)
        ≤ ℓr ⬝ᵥ (toRealVec c + toRealMat G *ᵥ b) := by -- --- PROOF ---
  set e : Vec ℝ n := ℓr - toRealVec ℓ with he
  set w : Fin m → ℝ := ℓr ᵥ* toRealMat G with hw
  refine ⟨fun j => if 0 ≤ w j then 1 else -1, fun j => by dsimp only; split_ifs <;> simp, ?_⟩
  set g : Fin m → 𝕋 := fun j => maximum zero (maximum (dotDown ℓ fun i => G i j)
    (neg (dotUp ℓ fun i => G i j))) with hg
  -- the value is the support: `ℓ'c + Σⱼ |ℓ' gⱼ|`
  have hval : ℓr ⬝ᵥ (toRealVec c + toRealMat G *ᵥ fun j => if 0 ≤ w j then 1 else -1)
      = ℓr ⬝ᵥ toRealVec c + ∑ j, |w j| := by
    rw [dotProduct_add, dotProduct_mulVec]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    show w j * (if 0 ≤ w j then 1 else -1) = |w j|
    split_ifs with h
    · rw [mul_one, abs_of_nonneg h]
    · rw [mul_neg_one, abs_of_neg (lt_of_not_ge h)]
  rw [hval]
  -- the error of the center and of each generator, together at most `E β`
  have hec : |e ⬝ᵥ toRealVec c| ≤ ∑ i, |e i| * |toReal (c i)| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => by rw [abs_mul]; rfl
  have heg : ∀ j, |∑ i, e i * toReal (G i j)| ≤ ∑ i, |e i| * |toReal (G i j)| := fun j =>
    le_trans (Finset.abs_sum_le_sum_abs _ _)
      (le_of_eq (Finset.sum_congr rfl fun i _ => abs_mul _ _))
  -- together at most `E β`, by the weighted bound of `|c| + Σⱼ |gⱼ|`
  have htot : ∑ i, |e i| * |toReal (c i)| + ∑ j, ∑ i, |e i| * |toReal (G i j)|
      ≤ toReal (mulUp E β) := by
    have h := Real.MatExp.abs_dotProduct_le_weightedSum (fun i => |e i|)
      (fun i => |toReal (c i)| + ∑ j, |toReal (G i j)|) (toRealVec s) (β := toReal β)
      fun i => by
        rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _))]
        exact hβ i
    have hsum : ∑ i, |e i| * |toReal (c i)| + ∑ j, ∑ i, |e i| * |toReal (G i j)|
        = (fun i => |e i|) ⬝ᵥ (fun i => |toReal (c i)| + ∑ j, |toReal (G i j)|) := by
      simp only [dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hsum]
    refine le_trans (le_abs_self _) (le_trans h (le_trans ?_ (mul_le_mulUp _ _)))
    simp only [abs_abs, toRealVec]
    exact mul_le_mul_of_nonneg_right hE hβ0
  -- the center: `ℓ'c ≥ ℓ̃'c - |e'c|`
  have hc : toReal (dotDown ℓ c) - |e ⬝ᵥ toRealVec c| ≤ ℓr ⬝ᵥ toRealVec c := by
    have h1 := dotDown_le ℓ c
    have h2 : ℓr ⬝ᵥ toRealVec c = toRealVec ℓ ⬝ᵥ toRealVec c + e ⬝ᵥ toRealVec c := by
      rw [he, ← add_dotProduct, add_sub_cancel]
    have h3 := neg_abs_le (e ⬝ᵥ toRealVec c)
    have h4 : toRealVec ℓ ⬝ᵥ toRealVec c = ∑ k, toReal (ℓ k) * toReal (c k) := rfl
    linarith
  -- a generator: `|ℓ' gⱼ| ≥ mig - |e' gⱼ|`
  have hgj : ∀ j, toReal (g j) - |∑ i, e i * toReal (G i j)| ≤ |w j| := by
    intro j
    have h1 := dotDown_le ℓ fun i => G i j
    have h2 := le_dotUp ℓ fun i => G i j
    have hwj : w j = ∑ i, toReal (ℓ i) * toReal (G i j) + ∑ i, e i * toReal (G i j) := by
      show ∑ i, ℓr i * toRealMat G i j = _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [he, Pi.sub_apply, toRealVec, toRealMat]
      ring
    have hmig : toReal (g j) ≤ |∑ i, toReal (ℓ i) * toReal (G i j)| := by
      simp only [hg, toReal_maximum, toReal_zero, toReal_neg]
      refine max_le (abs_nonneg _) (max_le ?_ ?_)
      · exact le_trans h1 (le_abs_self _)
      · exact le_trans (neg_le_neg h2) (neg_le_abs _)
    rw [hwj]
    have := abs_add_le (∑ i, toReal (ℓ i) * toReal (G i j) + ∑ i, e i * toReal (G i j))
      (-∑ i, e i * toReal (G i j))
    rw [add_neg_cancel_right, abs_neg] at this
    linarith
  -- together
  unfold LinearSys.verifySupportDownFloat
  simp only [← hg]
  have hsd := sumDown_le_sum g
  have had := addDown_le_add (dotDown ℓ c) (sumDown g)
  have hsub := subDown_le_sub (addDown (dotDown ℓ c) (sumDown g)) (mulUp E β)
  have hgs : ∑ j, toReal (g j) - ∑ j, |∑ i, e i * toReal (G i j)| ≤ ∑ j, |w j| := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_le_sum fun j _ => hgj j
  have hegs : ∑ j, |∑ i, e i * toReal (G i j)| ≤ ∑ j, ∑ i, |e i| * |toReal (G i j)| :=
    Finset.sum_le_sum fun j _ => heg j
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
