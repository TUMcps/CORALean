import CORALean.ContDynamics.NonlinearSys.Operations.GainDim
import CORALean.ContDynamics.NonlinearSys.Operations.GainOrderDim

/-!
# The gain is under `δ^{q+1}` while the coefficients hold still

`[1, (42)]`, the second half of `[1, Prop. 2]`: if every `Q⁽ᵖ⁾ᵢ` is constant on `[0,h]`,
then `φᵢ(t;δ) ≤ δ^{qᵢ+1}` for every `t` in it. `[1, Prop. 1]` and `[1, Lemma 3]` put the
width in the shape asked here, `e p` standing for `p + q⁽ᵖ⁾ᵢ` and `Q p` for the constant
value of `Q⁽ᵖ⁾ᵢ`; `hQ0` is `[1, Lemma 3]`'s convention that a vanishing coefficient has
`a⁽ᵖ⁾ᵢ = 0`, and `hsum` is the majorant `boxDiameter_abstrSolInf` already builds.

Proved directly rather than by `[1]`'s argument from `(41)`: shrinking the span to `δt`
multiplies the `p`-th term by `δ^{e p+1}`, and `e p ≥ qᵢ` for every term that survives —
which is `[1, (40)]` read as a minimum, as `gainOrderDim` has it — so `δ ≤ 1` pulls
`δ^{qᵢ+1}` out of the whole series at once. No continuity, no monotonicity and no
contradiction are needed, and the bound holds on all of `[0,h]`, not only near `0`.

`(41)`, the derivative half, is not proved here: it asks for `dφᵢ/dh` and nothing in the
tree yet says `φᵢ` is differentiable. `(43)`, the inequality `(41)` is used to reach, is
this theorem. Where the width vanishes Lean's `x / 0 = 0` makes `φᵢ` zero, which is under
the bound too, so no positivity hypothesis joins the ones above.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A coefficient that survives sits at an order of at least `qᵢ`, the infimum
`gainOrderDim` takes. -/
theorem aux_le_of_gainOrderDim {q : ℕ → Fin n → ℕ∞} {a : ℕ → Fin n → Vec ℝ m} {i : Fin n}
    {e : ℕ → ℕ} {qi : ℕ} (hqi : gainOrderDim q a i = (qi : ℕ∞))
    (he : ∀ p, a p i ≠ 0 → ((e p : ℕ∞) = (p : ℕ∞) + q p i)) {p : ℕ} (hp : a p i ≠ 0) :
    qi ≤ e p := by -- --- PROOF ---
  have hmem : ((e p : ℕ) : ℕ∞) ∈ {j : ℕ∞ | ∃ p : ℕ, (p : ℕ∞) + q p i = j ∧ a p i ≠ 0} :=
    ⟨p, (he p hp).symm, hp⟩
  -- the order of this coefficient is one of the orders the infimum ranges over
  have h0 : gainOrderDim q a i ≤ ((e p : ℕ) : ℕ∞) := sInf_le hmem
  rw [hqi] at h0
  exact_mod_cast h0


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, (42)]`: with every `Q⁽ᵖ⁾ᵢ` held constant over `[0,h]`, no span in it
keeps more than `δ^{qᵢ+1}` of dimension `i`'s width. -/
theorem gainDim_le_pow (A : ℝ → Mat ℝ n n) (Ψ : ℝ → Set (Vec ℝ n)) (i : Fin n)
    {q : ℕ → Fin n → ℕ∞} {a : ℕ → Fin n → Vec ℝ m} {e : ℕ → ℕ} {Q : ℕ → ℝ} {qi : ℕ} {h δ : ℝ}
    (hqi : gainOrderDim q a i = (qi : ℕ∞))
    (he : ∀ p, a p i ≠ 0 → ((e p : ℕ∞) = (p : ℕ∞) + q p i))
    (hQ0 : ∀ p, a p i = 0 → Q p = 0) (hQnn : ∀ p, 0 ≤ Q p) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hsum : ∀ t ∈ Set.Icc (0:ℝ) h,
      Summable (fun p : ℕ => t ^ (e p + 1) / (Nat.factorial (p + 1) : ℝ) * Q p))
    (hexp : ∀ t ∈ Set.Icc (0:ℝ) h, boxDiameter (abstrSolInf A Ψ t) i
      = 2 * ∑' p : ℕ, t ^ (e p + 1) / (Nat.factorial (p + 1) : ℝ) * Q p) :
    ∀ t ∈ Set.Icc (0:ℝ) h, gainDim A Ψ t δ i ≤ δ ^ (qi + 1) := by -- --- PROOF ---
  rintro t ⟨ht0, hth⟩
  have hδt : δ * t ∈ Set.Icc (0:ℝ) h :=
    ⟨mul_nonneg hδ0 ht0, (mul_le_of_le_one_left ht0 hδ1).trans hth⟩
  -- every surviving coefficient sits at an order of at least `qᵢ`, so `δ` is raised higher
  have hterm : ∀ p : ℕ, (δ * t) ^ (e p + 1) / (Nat.factorial (p + 1) : ℝ) * Q p
      ≤ δ ^ (qi + 1) * (t ^ (e p + 1) / (Nat.factorial (p + 1) : ℝ) * Q p) := by
    intro p
    have hrest : 0 ≤ t ^ (e p + 1) / (Nat.factorial (p + 1) : ℝ) * Q p :=
      mul_nonneg (div_nonneg (pow_nonneg ht0 _) (Nat.cast_nonneg _)) (hQnn p)
    by_cases hQp : Q p = 0
    · simp [hQp]
    · have hle : qi + 1 ≤ e p + 1 :=
        Nat.succ_le_succ (aux_le_of_gainOrderDim hqi he (fun hc => hQp (hQ0 p hc)))
      have hpow : δ ^ (e p + 1) ≤ δ ^ (qi + 1) := pow_le_pow_of_le_one hδ0 hδ1 hle
      calc (δ * t) ^ (e p + 1) / (Nat.factorial (p + 1) : ℝ) * Q p
          = δ ^ (e p + 1) * (t ^ (e p + 1) / (Nat.factorial (p + 1) : ℝ) * Q p) := by
            rw [mul_pow]; ring
        _ ≤ δ ^ (qi + 1) * (t ^ (e p + 1) / (Nat.factorial (p + 1) : ℝ) * Q p) :=
            mul_le_mul_of_nonneg_right hpow hrest
  -- so the whole expansion shrinks by at least `δ^{qᵢ+1}`
  have hD : boxDiameter (abstrSolInf A Ψ (δ * t)) i
      ≤ δ ^ (qi + 1) * boxDiameter (abstrSolInf A Ψ t) i := by
    rw [hexp _ hδt, hexp _ ⟨ht0, hth⟩]
    have hs2 := (hsum t ⟨ht0, hth⟩).mul_left (δ ^ (qi + 1))
    have hle := Summable.tsum_le_tsum hterm (hsum _ hδt) hs2
    rw [tsum_mul_left] at hle
    linarith
  -- the width itself is a series of non-negative terms
  have hDnn : 0 ≤ boxDiameter (abstrSolInf A Ψ t) i := by
    rw [hexp _ ⟨ht0, hth⟩]
    refine mul_nonneg (by norm_num) (tsum_nonneg fun p => ?_)
    exact mul_nonneg (div_nonneg (pow_nonneg ht0 _) (Nat.cast_nonneg _)) (hQnn p)
  -- a vanishing denominator leaves Lean's `x / 0 = 0`, which is under the bound anyway
  rcases eq_or_lt_of_le hDnn with hz | hpos
  · rw [gainDim, ← hz, div_zero]
    exact pow_nonneg hδ0 _
  · rw [gainDim, div_le_iff₀ hpos]
    exact hD

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
