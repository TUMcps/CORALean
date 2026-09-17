import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.NN.Layers.PolySampling

/-!
# The error a fit leaves, bounded by sampling in floating point

CORA's `nnHelper/minMaxDiffOrder` [1] with every step rounded outward. The
argument is the exact one — a grid of spacing `dx`, a bound `M` on `|g'|`, and
`min ys - M·dx ≤ g t ≤ max ys + M·dx` by the mean value theorem — and what the
float layer adds is that the slack `M·dx` is rounded *up* while the sampled ends
are rounded apart, so the bracket only ever widens.

The grid is not computed, it is *checked*. Rounding is constrained in one
direction per operation, so no float expression can be proved to step by a
bounded amount: `addUp l s` may land anywhere above `l + s`. So a caller
proposes the samples and `gridChecked` certifies them with `le` alone — the
pattern `norm₂_le_of_sq_le` uses for a square root — and a grid that fails the
check yields no bracket rather than a wrong one.

Values at the samples arrive already bracketed, since `g` is `σ` minus a fit and
neither is a float operation; `PolyEval` is where the fit's half comes from.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N : ℕ}

/-- Every index passing its own check, as a fold rather than a `Finset`. -/
private def allOver : {k : ℕ} → (Fin k → Bool) → Bool
  | 0, _ => true
  | _ + 1, f => f 0 && allOver fun i => f i.succ

/-- The same conjunction as a loop. It gives up the early exit on the first
`false`, which only a grid that fails the check would have reached. -/
private def allOverImpl {k : ℕ} (f : Fin k → Bool) : Bool :=
  Fin.foldr k (fun i acc => f i && acc) true

@[csimp] private theorem allOver_eq_impl : @allOver = @allOverImpl := by -- --- PROOF ---
  funext k
  induction k with
  | zero => funext f; rw [allOverImpl, Fin.foldr_zero]; rfl
  | succ k ih =>
    funext f
    rw [allOverImpl, Fin.foldr_succ, ← allOverImpl, ← congrFun ih fun i => f i.succ]
    rfl

private theorem allOver_apply : ∀ {k : ℕ} (f : Fin k → Bool),
    allOver f = true → ∀ i, f i = true := by -- --- PROOF ---
  intro k
  induction k with
  | zero => exact fun _ _ i => absurd i.isLt (Nat.not_lt_zero _)
  | succ m ih =>
    intro f h i
    rw [allOver, Bool.and_eq_true] at h
    exact Fin.cases h.1 (fun j => ih (fun i' => f i'.succ) h.2 j) i

/-- What a proposed grid must pass: the left end reached, every gap and the
right end within `dx`, and every sample inside the box. -/
def gridChecked (p : Fin (N + 1) → 𝕋) (l u dx : 𝕋) : Bool :=
  le (p 0) l && allOver (fun j : Fin N => le (subUp (p j.succ) (p j.castSucc)) dx)
    && le (subUp u (p (Fin.last N))) dx
    && allOver fun i : Fin (N + 1) => le l (p i) && le (p i) u

/-- A checked grid samples inside the box, which is what the mean value theorem
between a sample and a point of the box needs. -/
theorem grid_mem_of_checked {p : Fin (N + 1) → 𝕋} {l u dx : 𝕋}
    (h : gridChecked p l u dx = true) (i : Fin (N + 1)) :
    toReal l ≤ toReal (p i) ∧ toReal (p i) ≤ toReal u := by
  simp only [gridChecked, Bool.and_eq_true] at h
  have hi := allOver_apply _ h.2 i
  rw [Bool.and_eq_true] at hi
  exact ⟨toReal_le_of_le hi.1, toReal_le_of_le hi.2⟩

/-- And every point of the box is within one spacing of a sample, which is what
lets the sampled range speak for the whole box. -/
theorem exists_grid_close {p : Fin (N + 1) → 𝕋} {l u dx : 𝕋} {t : ℝ}
    (h : gridChecked p l u dx = true) (hl : toReal l ≤ t) (hu : t ≤ toReal u) :
    ∃ i, |t - toReal (p i)| ≤ toReal dx := by -- --- PROOF ---
  simp only [gridChecked, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, hgap⟩, hend⟩, -⟩ := h
  have hgapr : ∀ j : Fin N, toReal (p j.succ) - toReal (p j.castSucc) ≤ toReal dx :=
    fun j => le_trans (sub_le_subUp _ _) (toReal_le_of_le (allOver_apply _ hgap j))
  have hendr : toReal u - toReal (p (Fin.last N)) ≤ toReal dx :=
    le_trans (sub_le_subUp _ _) (toReal_le_of_le hend)
  -- walk right from the left end until the next sample overshoots `t`
  have key : ∀ d k : ℕ, k + d = N → ∀ hk : k < N + 1, toReal (p ⟨k, hk⟩) ≤ t →
      ∃ i : Fin (N + 1), toReal (p i) ≤ t ∧ t - toReal (p i) ≤ toReal dx := by
    intro d
    induction d with
    | zero =>
      intro k hkN hk hpk
      have hkN0 : k = N := by omega
      have hlast : (⟨k, hk⟩ : Fin (N + 1)) = Fin.last N := Fin.ext hkN0
      refine ⟨⟨k, hk⟩, hpk, ?_⟩
      rw [hlast]
      linarith
    | succ d ih =>
      intro k hkN hk hpk
      have hkN' : k < N := by omega
      by_cases hnext : toReal (p ⟨k + 1, by omega⟩) ≤ t
      · exact ih (k + 1) (by omega) (by omega) hnext
      · -- the next sample is past `t`, so `t` sits inside this gap
        refine ⟨⟨k, hk⟩, hpk, ?_⟩
        have hj := hgapr ⟨k, hkN'⟩
        have hs : (⟨k, hkN'⟩ : Fin N).succ = (⟨k + 1, by omega⟩ : Fin (N + 1)) := rfl
        have hc : (⟨k, hkN'⟩ : Fin N).castSucc = (⟨k, hk⟩ : Fin (N + 1)) := rfl
        rw [hs, hc] at hj
        linarith [not_le.mp hnext]
  have hz : (⟨0, Nat.succ_pos N⟩ : Fin (N + 1)) = 0 := Fin.ext rfl
  obtain ⟨i, hple, hi⟩ := key N 0 (by omega) (Nat.succ_pos N)
    (by rw [hz]; exact le_trans (toReal_le_of_le h0) hl)
  exact ⟨i, by rw [abs_le]; exact ⟨by linarith, by linarith⟩⟩

/-- The least sampled value, dropped by the slack rounded *up*: the one place
this bound rounds, and it rounds outward. -/
def sampleLo (gLo : Fin (N + 1) → 𝕋) (M dx : 𝕋) : 𝕋 := subDown (minimumOver gLo) (mulUp M dx)

/-- The greatest sampled value, raised by that same slack. -/
def sampleHi (gUp : Fin (N + 1) → 𝕋) (M dx : 𝕋) : 𝕋 := addUp (maximumOver gUp) (mulUp M dx)


/-- The sampled range, padded by the Lipschitz slack, brackets `g` on the whole
box — at any samples inside it leaving no point of it further off than `dx`. -/
theorem sample_bounds_of_cover {g g' : ℝ → ℝ} {l u M dx : 𝕋}
    {p gLo gUp : Fin (N + 1) → 𝕋} {t : ℝ} (hd : ∀ x, HasDerivAt g (g' x) x)
    (hM : ∀ x, toReal l ≤ x → x ≤ toReal u → |g' x| ≤ toReal M)
    (hp : ∀ i, toReal l ≤ toReal (p i) ∧ toReal (p i) ≤ toReal u)
    (hcov : ∀ y : ℝ, toReal l ≤ y → y ≤ toReal u → ∃ i, |y - toReal (p i)| ≤ toReal dx)
    (hlo : ∀ i, toReal (gLo i) ≤ g (toReal (p i)))
    (hup : ∀ i, g (toReal (p i)) ≤ toReal (gUp i)) (hl : toReal l ≤ t) (hu : t ≤ toReal u) :
    toReal (sampleLo gLo M dx) ≤ g t
      ∧ g t ≤ toReal (sampleHi gUp M dx) := by -- --- PROOF ---
  have hM0 : 0 ≤ toReal M := le_trans (abs_nonneg _) (hM t hl hu)
  obtain ⟨i, hi⟩ := hcov t hl hu
  obtain ⟨hgl, hgu⟩ := hp i
  -- the mean value theorem between `t` and the sample it is nearest to
  have hlip : |g t - g (toReal (p i))| ≤ toReal M * |t - toReal (p i)| := by
    have hbound : ∀ x ∈ Set.Icc (toReal l) (toReal u), ‖g' x‖ ≤ toReal M := fun x hx => by
      rw [Real.norm_eq_abs]; exact hM x hx.1 hx.2
    have hmv := (convex_Icc (toReal l) (toReal u)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x _ => (hd x).hasDerivWithinAt) hbound ⟨hgl, hgu⟩ ⟨hl, hu⟩
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  have hslack : toReal M * |t - toReal (p i)| ≤ toReal (mulUp M dx) :=
    le_trans (mul_le_mul_of_nonneg_left hi hM0) (mul_le_mulUp M dx)
  have habs := abs_le.mp (hlip.trans hslack)
  have hmin := minimumOver_le gLo i
  have hmax := le_maximumOver gUp i
  have hsub := subDown_le_sub (minimumOver gLo) (mulUp M dx)
  have hadd := add_le_addUp (maximumOver gUp) (mulUp M dx)
  exact ⟨by rw [sampleLo]; linarith [hlo i], by rw [sampleHi]; linarith [hup i]⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same bracket at a grid that passed its checks, which is the form a
caller reaches: sound at every such grid, and tighter as `dx` shrinks. -/
theorem sample_bounds_of_deriv {g g' : ℝ → ℝ} {l u M dx : 𝕋}
    {p gLo gUp : Fin (N + 1) → 𝕋} {t : ℝ} (hd : ∀ x, HasDerivAt g (g' x) x)
    (hM : ∀ x, toReal l ≤ x → x ≤ toReal u → |g' x| ≤ toReal M)
    (hchk : gridChecked p l u dx = true) (hlo : ∀ i, toReal (gLo i) ≤ g (toReal (p i)))
    (hup : ∀ i, g (toReal (p i)) ≤ toReal (gUp i)) (hl : toReal l ≤ t) (hu : t ≤ toReal u) :
    toReal (sampleLo gLo M dx) ≤ g t ∧ g t ≤ toReal (sampleHi gUp M dx) :=
  sample_bounds_of_cover hd hM (grid_mem_of_checked hchk)
    (fun _ hy hy' => exists_grid_close hchk hy hy') hlo hup hl hu

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
