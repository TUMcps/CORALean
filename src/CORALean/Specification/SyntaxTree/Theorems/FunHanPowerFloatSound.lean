module

public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanPowerFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat
public import CORALean.Specification.SyntaxTree.Theorems.NthrootFloatContains
public import CORALean.Specification.SyntaxTree.Theorems.SignedRootsFloatContains

@[expose] public section

/-!
# `aux_power_` over floats is sound

`SyntaxTree.funHanPowerFloat` keeps every solution of `s ^ k ∈ int`: for an odd exponent `s` is the
root of its power, and the root is increasing; for an even one `|s|` is, between the roots of the
bounds, and `signedRootsFloat_contains` gives the sign. The rounded roots of `nthrootFloat` enclose
the real ones.

## Inputs
* `steps` – bisection steps of the roots
* `k` – exponent
* `prev` – previous interval
* `v` – value interval

## Hypotheses
* none

## Conclusion
* the float inverse of the power keeps every solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The root of a power of a nonnegative number. -/
theorem SyntaxTree.aux_nthroot_pow_nonneg {k : ℕ} (hk : k ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    nthroot (x ^ k) k = x := by
  have h0 : 0 ≤ x ^ k := pow_nonneg hx k
  simp only [nthroot, h0, if_true, one_div]
  exact Real.pow_rpow_inv_natCast hx hk

/-- The root of an odd power. -/
theorem SyntaxTree.aux_nthroot_pow_odd {k : ℕ} (hk : k % 2 = 1) (x : ℝ) : -- --- CONCL ---
    nthroot (x ^ k) k = x := by -- --- PROOF ---
  have hodd : Odd k := Nat.odd_iff.2 hk
  have hk0 : k ≠ 0 := fun h => by simp [h] at hk
  by_cases hx : 0 ≤ x
  · exact SyntaxTree.aux_nthroot_pow_nonneg hk0 hx
  · have hx' : 0 ≤ -x := by linarith [not_le.1 hx]
    have h1 : x ^ k < 0 := hodd.pow_neg (not_le.1 hx)
    have e : -(x ^ k) = (-x) ^ k := (hodd.neg_pow x).symm ▸ rfl
    simp only [nthroot, not_le.2 h1, if_false, e, one_div]
    rw [Real.pow_rpow_inv_natCast hx' hk0]
    ring

/-- The root is monotone on the nonnegative numbers. -/
theorem SyntaxTree.aux_nthroot_mono_nonneg (k : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    nthroot a k ≤ nthroot b k := by
  have hz : (0 : ℝ) ≤ 1 / k := by positivity
  simp only [nthroot, ha, ha.trans hab, if_true]
  exact Real.rpow_le_rpow ha hab hz

/-- The root is monotone. -/
theorem SyntaxTree.aux_nthroot_mono (k : ℕ) {a b : ℝ} (hab : a ≤ b) : -- --- CONCL ---
    nthroot a k ≤ nthroot b k := by -- --- PROOF ---
  have hz : (0 : ℝ) ≤ 1 / k := by positivity
  by_cases ha : 0 ≤ a
  · exact SyntaxTree.aux_nthroot_mono_nonneg k ha hab
  · by_cases hb : 0 ≤ b
    · simp only [nthroot, ha, hb, if_true, if_false]
      exact (neg_nonpos.2 (Real.rpow_nonneg (by linarith [not_le.1 ha]) _)).trans
        (Real.rpow_nonneg hb _)
    · simp only [nthroot, ha, hb, if_false, neg_le_neg_iff]
      exact Real.rpow_le_rpow (by linarith [not_le.1 hb]) (by linarith) hz

/-- The root of an even power is the absolute value. -/
theorem SyntaxTree.aux_nthroot_pow_even {k : ℕ} (hk : k % 2 = 0) (hk0 : k ≠ 0) (x : ℝ) :
    nthroot (x ^ k) k = |x| := by
  have h : x ^ k = |x| ^ k := ((Nat.even_iff.2 hk).pow_abs x).symm
  rw [h]
  exact SyntaxTree.aux_nthroot_pow_nonneg hk0 (abs_nonneg x)


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aux_power_` over floats is sound for `x^k`. -/
theorem SyntaxTree.funHanPowerFloat_sound (steps k : ℕ)
    (prev v : Float.SyntaxTree.Dom 𝕋) : -- --- CONCL ---
    SyntaxTree.IsUnarySoundFloat (SyntaxTree.Unary.power k).fn prev v
      (SyntaxTree.funHanPowerFloat steps k) := by -- --- PROOF ---
  intro int _ s hs hi
  have h : toReal (int.inf 0) ≤ s ^ k ∧ s ^ k ≤ toReal (int.sup 0) := hi
  unfold SyntaxTree.funHanPowerFloat
  by_cases hk0 : k = 0
  · simp only [hk0, if_true]
    exact ⟨_, rfl, hs, le_rfl, le_rfl⟩
  by_cases hev : k % 2 = 0
  · -- an even power: the root `|s|`, with the sign of `intPrev`
    have hpos : 0 ≤ s ^ k := (Nat.even_iff.2 hev).pow_nonneg s
    have hnd : ¬ ltStrict (int.sup 0) zero = true := fun hc => by
      have := toReal_lt_of_ltStrict hc
      rw [toReal_zero] at this
      linarith [h.2]
    have hr : SyntaxTree.nthroot (s ^ k) k = |s| := SyntaxTree.aux_nthroot_pow_even hev hk0 s
    have l₂ : |s| ≤ SyntaxTree.nthroot (toReal (int.sup 0)) k :=
      hr ▸ SyntaxTree.aux_nthroot_mono_nonneg k hpos h.2
    have l₁ : SyntaxTree.nthroot (toReal (maximum (int.inf 0) zero)) k ≤ |s| := by
      rw [toReal_maximum, toReal_zero]
      exact hr ▸ SyntaxTree.aux_nthroot_mono_nonneg k (le_max_right _ _) (max_le h.1 hpos)
    have c₁ := (SyntaxTree.nthrootFloat_contains steps (maximum (int.inf 0) zero) k).1
    have c₂ := (SyntaxTree.nthrootFloat_contains steps (int.sup 0) k).2
    simp only [hk0, hev, hnd, if_true, if_false]
    exact ⟨_, rfl, SyntaxTree.meet_containsFloat hs
      (SyntaxTree.signedRootsFloat_contains hs (c₁.trans l₁) (l₂.trans c₂))⟩
  · -- an odd power: the root is increasing
    simp only [hk0, hev, if_false]
    have hodd : s = SyntaxTree.nthroot (s ^ k) k :=
      (SyntaxTree.aux_nthroot_pow_odd (by omega) s).symm
    have l₁ : SyntaxTree.nthroot (toReal (int.inf 0)) k ≤ s := by
      rw [hodd]; exact SyntaxTree.aux_nthroot_mono k h.1
    have l₂ : s ≤ SyntaxTree.nthroot (toReal (int.sup 0)) k := by
      rw [hodd]; exact SyntaxTree.aux_nthroot_mono k h.2
    have c₁ := (SyntaxTree.nthrootFloat_contains steps (int.inf 0) k).1
    have c₂ := (SyntaxTree.nthrootFloat_contains steps (int.sup 0) k).2
    exact ⟨_, rfl, SyntaxTree.meet_containsFloat hs ⟨c₁.trans l₁, l₂.trans c₂⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
