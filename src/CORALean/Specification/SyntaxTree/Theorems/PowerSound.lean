module

public import CORALean.ContSet.Interval.Real.Operations.Power
public import CORALean.Specification.SyntaxTree.Definitions.UnarySound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.AuxSignedSpec
public import CORALean.Specification.SyntaxTree.Theorems.MeetContains
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `aux_power_` is sound

`aux_power_` keeps every solution of `s^k ∈ int`: for an odd `k` the root is increasing, for an
even `k`
it is `|s|`, whose sign `intPrev` fixes (`aux_signed_`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The root of a power of a nonnegative number. -/
private theorem SyntaxTree.nthroot_pow_nonneg {k : ℕ} (hk : k ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    nthroot (x ^ k) k = x := by
  have h0 : 0 ≤ x ^ k := pow_nonneg hx k
  simp only [nthroot, h0, if_true, one_div]
  exact Real.pow_rpow_inv_natCast hx hk

/-- The root of an odd power. -/
private theorem SyntaxTree.nthroot_pow_odd {k : ℕ} (hk : k % 2 = 1) (x : ℝ) :
    nthroot (x ^ k) k = x := by -- --- PROOF ---
  have hodd : Odd k := Nat.odd_iff.2 hk
  have hk0 : k ≠ 0 := fun h => by simp [h] at hk
  by_cases hx : 0 ≤ x
  · exact nthroot_pow_nonneg hk0 hx
  · have hx' : 0 ≤ -x := by linarith [not_le.1 hx]
    have h1 : x ^ k < 0 := hodd.pow_neg (not_le.1 hx)
    have e : -(x ^ k) = (-x) ^ k := (hodd.neg_pow x).symm ▸ rfl
    simp only [nthroot, not_le.2 h1, if_false, e, one_div]
    rw [Real.pow_rpow_inv_natCast hx' hk0]
    ring

/-- The root is monotone on the nonnegative numbers. -/
private theorem SyntaxTree.nthroot_mono_nonneg (k : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    nthroot a k ≤ nthroot b k := by
  have hz : (0 : ℝ) ≤ 1 / k := by positivity
  simp only [nthroot, ha, ha.trans hab, if_true]
  exact Real.rpow_le_rpow ha hab hz

/-- The root is monotone. -/
private theorem SyntaxTree.nthroot_mono (k : ℕ) {a b : ℝ} (hab : a ≤ b) :
    nthroot a k ≤ nthroot b k := by -- --- PROOF ---
  have hz : (0 : ℝ) ≤ 1 / k := by positivity
  by_cases ha : 0 ≤ a
  · exact nthroot_mono_nonneg k ha hab
  · by_cases hb : 0 ≤ b
    · simp only [nthroot, ha, hb, if_true, if_false]
      exact (neg_nonpos.2 (Real.rpow_nonneg (by linarith [not_le.1 ha]) _)).trans
        (Real.rpow_nonneg hb _)
    · simp only [nthroot, ha, hb, if_false, neg_le_neg_iff]
      exact Real.rpow_le_rpow (by linarith [not_le.1 hb]) (by linarith) hz

/-- The root of an even power is the absolute value. -/
private theorem SyntaxTree.nthroot_pow_even {k : ℕ} (hk : k % 2 = 0) (hk0 : k ≠ 0) (x : ℝ) :
    nthroot (x ^ k) k = |x| := by
  have h : x ^ k = |x| ^ k := ((Nat.even_iff.2 hk).pow_abs x).symm
  rw [h]
  exact nthroot_pow_nonneg hk0 (abs_nonneg x)

/-- `aux_power_` is sound for `x^k`. -/
theorem SyntaxTree.power_sound (k : ℕ) (prev : Dom) :
    UnarySound (Unary.power k).fn prev (Real.Interval.power prev k) (funHanPower
      k) := by -- --- PROOF ---
  intro int _ s hs hi
  have h : int.inf 0 ≤ s ^ k ∧ s ^ k ≤ int.sup 0 := hi
  unfold funHanPower
  by_cases hk0 : k = 0
  · simp only [hk0, if_true]
    exact ⟨_, rfl, hs, le_rfl, le_rfl⟩
  by_cases hev : k % 2 = 0
  · -- an even power: the root `|s|`, with the sign of `intPrev`
    have hpos : 0 ≤ s ^ k := (Nat.even_iff.2 hev).pow_nonneg s
    have hnd : ¬ int.sup 0 < 0 := not_lt.2 (hpos.trans h.2)
    have hr : nthroot (s ^ k) k = |s| := nthroot_pow_even hev hk0 s
    have l₂ : |s| ≤ nthroot (int.sup 0) k := hr ▸ nthroot_mono_nonneg k hpos h.2
    simp only [hk0, hev, hnd, if_true, if_false]
    by_cases hl : int.inf 0 < 0
    · simp only [hl, if_true, interval]
      have l₁ : nthroot 0 k ≤ |s| := hr ▸ nthroot_mono_nonneg k le_rfl hpos
      obtain ⟨lo, hi', e, c₁, c₂⟩ := signedRoots_spec hs l₁ l₂
      obtain ⟨m₁, m₂⟩ := meet_contains hs c₁ c₂
      exact ⟨_, by rw [e], m₁, m₂⟩
    · simp only [hl, if_false]
      have l₁ : nthroot (int.inf 0) k ≤ |s| :=
        hr ▸ nthroot_mono_nonneg k (not_lt.1 hl) h.1
      obtain ⟨lo, hi', e, c₁, c₂⟩ := signedRoots_spec hs l₁ l₂
      obtain ⟨m₁, m₂⟩ := meet_contains hs c₁ c₂
      exact ⟨_, by rw [e], m₁, m₂⟩
  · -- an odd power: the root is increasing
    simp only [hk0, hev, if_false]
    have hodd : s = nthroot (s ^ k) k := (nthroot_pow_odd (by omega) s).symm
    have l₁ : nthroot (int.inf 0) k ≤ s := by
      rw [hodd]; exact nthroot_mono k h.1
    have l₂ : s ≤ nthroot (int.sup 0) k := by
      rw [hodd]; exact nthroot_mono k h.2
    obtain ⟨m₁, m₂⟩ := meet_contains hs ((min_le_left _ _).trans l₁) (l₂.trans (le_max_right _ _))
    exact ⟨_, rfl, m₁, m₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
