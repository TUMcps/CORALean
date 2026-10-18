module

public import CORALean.ContSet.Interval.Float.Operations.BoundaryPoint
public import CORALean.ContSet.Interval.Float.Theorems.BoundaryRatioBounds
public import CORALean.ContSet.Interval.Float.Theorems.BoundaryRatioAtMem
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.ContSet.Interval.Real.Theorems.BoundaryRatioIsGreatest

@[expose] public section

/-!
# `Interval.boundaryPoint` encloses the exact boundary point

Outer: when the start point lies in the box, every coordinate of `dir` with a nonzero value is
certified nonzero (`ltStrict`) and some coordinate is, the exact layer's boundary point of the
nominal box (`start + ratio * dir`, the ratio the greatest `s` with `start + s * dir` in the box)
lies in the result. The clamped lower end of the ratio interval lies in the box on the ray, so it
is at most the greatest ratio; each coordinate's upper bound is at least it. The exact point is on
the box's boundary; the float result is a box around it, not a point of the boundary.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.boundaryPoint_outer (I : Interval (Vec 𝕋 n)) (dir start : Vec 𝕋 n)
    (hs : toRealVec start ∈ I.construct) (hex : ∃ i, toReal (dir i) ≠ 0)
    (hcert : ∀ i, toReal (dir i) ≠ 0 →
      ltStrict zero (dir i) = true ∨ ltStrict (dir i) zero = true) : -- --- STMT ---
    ∃ J, I.boundaryPoint dir start = some J ∧
      Real.Interval.boundaryPoint I.nominal (toRealVec dir) (toRealVec start) hex ∈
        J.construct := by -- --- PROOF ---
  have hs' : ∀ i, toReal (I.inf i) ≤ toReal (start i) ∧ toReal (start i) ≤ toReal (I.sup i) :=
    fun i => hs i
  -- the exact ratio, the greatest on the ray
  have hG := Real.Interval.boundaryRatio_isGreatest I.nominal (toRealVec dir) (toRealVec start)
    hex hs
  set g := Real.Interval.boundaryRatio I.nominal (toRealVec dir) (toRealVec start) hex with hg
  obtain ⟨hne, hsome⟩ := Interval.boundaryRatio_bounds I dir start
  -- a certified coordinate has a ratio
  have hrat : ∀ i, toReal (dir i) ≠ 0 → ∃ x, Interval.boundaryRatioAt I dir start i = some x := by
    intro i hi
    by_cases h' : ltStrict zero (dir i) = true
    · simp only [Interval.boundaryRatioAt, if_pos h']; exact ⟨_, rfl⟩
    · have h'' : ltStrict (dir i) zero = true := (hcert i hi).resolve_left h'
      simp only [Interval.boundaryRatioAt, if_neg h', if_pos h'']; exact ⟨_, rfl⟩
  obtain ⟨i₀, hi₀⟩ := hex
  have hsome' : ∃ a, Interval.boundaryRatio I dir start = some a := by
    rcases hr : Interval.boundaryRatio I dir start with _ | a
    · exfalso
      obtain ⟨x, hx⟩ := hrat i₀ hi₀
      have := (hne.1 hr) i₀
      rw [hx] at this; exact absurd this (by simp)
    · exact ⟨a, rfl⟩
  obtain ⟨a, ha⟩ := hsome'
  obtain ⟨hlow, hup⟩ := hsome a ha
  have hlo : toReal (maximum zero a.inf) = max 0 (toReal a.inf) := by
    rw [toReal_maximum, toReal_zero]
  -- the clamped lower ratio is on the ray inside the box, so at most the greatest ratio
  have hA : max 0 (toReal a.inf) ≤ g := by
    refine hG.2 ?_
    intro i
    show toReal (I.inf i) ≤ max 0 (toReal a.inf) * toReal (dir i) + toReal (start i) ∧
      max 0 (toReal a.inf) * toReal (dir i) + toReal (start i) ≤ toReal (I.sup i)
    by_cases hc : toReal (dir i) = 0
    · rw [hc, mul_zero, zero_add]; exact hs' i
    obtain ⟨x, hx⟩ := hrat i hc
    have h1 := (hlow i x hx).1
    have hm0 : 0 ≤ max 0 (toReal a.inf) := le_max_left _ _
    rcases Interval.boundaryRatioAt_mem _ hx with ⟨hd, hx1, -⟩ | ⟨hd, hx1, -⟩
    · -- positive direction
      have h2 : toReal a.inf * toReal (dir i) ≤ toReal (I.sup i) - toReal (start i) :=
        (le_div_iff₀ hd).1 (le_trans h1 hx1)
      have h3 : 0 ≤ max 0 (toReal a.inf) * toReal (dir i) := mul_nonneg hm0 hd.le
      refine ⟨by linarith [(hs' i).1], ?_⟩
      rcases le_total 0 (toReal a.inf) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith [(hs' i).2]
    · -- negative direction
      have h2 : toReal a.inf * -toReal (dir i) ≤ toReal (start i) - toReal (I.inf i) :=
        (le_div_iff₀ (by linarith)).1 (le_trans h1 hx1)
      have h3 : max 0 (toReal a.inf) * toReal (dir i) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hm0 hd.le
      refine ⟨?_, by linarith [(hs' i).2]⟩
      rcases le_total 0 (toReal a.inf) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith [(hs' i).1]
  -- the greatest ratio is below each coordinate's upper bound, so below the result's
  have hB : g ≤ toReal a.sup := by
    refine hup g fun i x hx => ?_
    have hgi := hG.1 i
    have hgi' : toReal (I.inf i) ≤ g * toReal (dir i) + toReal (start i) ∧
        g * toReal (dir i) + toReal (start i) ≤ toReal (I.sup i) := hgi
    rcases Interval.boundaryRatioAt_mem _ hx with ⟨hd, -, hx2⟩ | ⟨hd, -, hx2⟩
    · have : g ≤ (toReal (I.sup i) - toReal (start i)) / toReal (dir i) :=
        (le_div_iff₀ hd).2 (by linarith [hgi'.2])
      linarith
    · have : g ≤ (toReal (start i) - toReal (I.inf i)) / -toReal (dir i) :=
        (le_div_iff₀ (by linarith)).2 (by linarith [hgi'.1])
      linarith
  -- the box swept by the ratio bounds holds the point
  refine ⟨⟨fun i => addDown (Interval.mulLo (maximum zero a.inf) a.sup (dir i) (dir i)) (start i),
    fun i => addUp (Interval.mulHi (maximum zero a.inf) a.sup (dir i) (dir i)) (start i)⟩,
    by simp [Interval.boundaryPoint, ha], ?_⟩
  intro i
  have hmc := Interval.mul_between_corners (a := maximum zero a.inf) (b := a.sup) (c := dir i)
    (d := dir i) (y := g) (x := toReal (dir i)) (by rw [hlo]; exact hA)
    hB le_rfl le_rfl
  show toReal (addDown (Interval.mulLo (maximum zero a.inf) a.sup (dir i) (dir i)) (start i)) ≤
      g * toReal (dir i) + toReal (start i) ∧
    g * toReal (dir i) + toReal (start i) ≤
      toReal (addUp (Interval.mulHi (maximum zero a.inf) a.sup (dir i) (dir i)) (start i))
  exact ⟨le_trans (addDown_le_add _ _) (by linarith [hmc.1]),
    le_trans (by linarith [hmc.2]) (add_le_addUp _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
