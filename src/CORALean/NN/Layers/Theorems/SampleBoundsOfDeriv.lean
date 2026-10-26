module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.NN.Layers.Operations.GridChecked
public import CORALean.NN.Layers.Operations.AllOver
public import CORALean.NN.Layers.Theorems.SampleBoundsOfCover

@[expose] public section

/-!
# A checked grid's sampled range brackets a function

`sample_bounds_of_cover` at a grid that passed its checks, which is the form a caller reaches:
sound at every such grid, and tighter as `dx` shrinks.

## Inputs
* `g` – function
* `g'` – its derivative
* `l` – lower end of the box
* `u` – upper end of the box
* `M` – bound on the derivative
* `dx` – maximal gap between samples
* `p` – sample points
* `gLo` – lower bounds at the sample points
* `gUp` – upper bounds at the sample points
* `t` – point in the box

## Hypotheses
* `hd` – the function has the given derivative
* `hM` – derivative is bounded on the box
* `hchk` – the grid is checked
* `hlo` – lower bounds hold at the samples
* `hup` – upper bounds hold at the samples
* `hl` – point is above the lower end
* `hu` – point is below the upper end

## Conclusion
* the function at the point lies within the sampled range widened by the slack
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A passed conjunction passes at every index. -/
private theorem aux_allOver_apply : -- --- CONCL ---
    ∀ {k : ℕ} (f : Fin k → Bool),
    allOver f = true → ∀ i, f i = true := by -- --- PROOF ---
  intro k
  induction k with
  | zero => exact fun _ _ i => absurd i.isLt (Nat.not_lt_zero _)
  | succ m ih =>
    intro f h i
    rw [allOver, Bool.and_eq_true] at h
    exact Fin.cases h.1 (fun j => ih (fun i' => f i'.succ) h.2 j) i


/-- A checked grid samples inside the box. -/
private theorem aux_grid_mem_of_checked {p : Fin (N + 1) → 𝕋} {l u dx : 𝕋}
    (h : gridChecked p l u dx) (i : Fin (N + 1)) :
    toReal l ≤ toReal (p i) ∧ toReal (p i) ≤ toReal u := by
  simp only [gridChecked, Bool.and_eq_true] at h
  have hi := aux_allOver_apply _ h.2 i
  rw [Bool.and_eq_true] at hi
  exact ⟨toReal_le_of_le hi.1, toReal_le_of_le hi.2⟩


/-- Every point of the box is near a checked sample. -/
private theorem aux_exists_grid_close {p : Fin (N + 1) → 𝕋} {l u dx : 𝕋} {t : ℝ}
    (h : gridChecked p l u dx) (hl : toReal l ≤ t) (hu : t ≤ toReal u) : -- --- CONCL ---
    ∃ i, |t - toReal (p i)| ≤ toReal dx := by -- --- PROOF ---
  simp only [gridChecked, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, hgap⟩, hend⟩, -⟩ := h
  have hgapr : ∀ j : Fin N, toReal (p j.succ) - toReal (p j.castSucc) ≤ toReal dx :=
    fun j => le_trans (sub_le_subUp _ _) (toReal_le_of_le (aux_allOver_apply _ hgap j))
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem sample_bounds_of_deriv {g g' : ℝ → ℝ} {l u M dx : 𝕋}
    {p gLo gUp : Fin (N + 1) → 𝕋} {t : ℝ} (hd : ∀ x, HasDerivAt g (g' x) x)
    (hM : ∀ x, toReal l ≤ x → x ≤ toReal u → |g' x| ≤ toReal M)
    (hchk : gridChecked p l u dx) (hlo : ∀ i, toReal (gLo i) ≤ g (toReal (p i)))
    (hup : ∀ i, g (toReal (p i)) ≤ toReal (gUp i)) (hl : toReal l ≤ t)
    (hu : t ≤ toReal u) :
    toReal (sampleLo gLo M dx) ≤ g t ∧ g t ≤ toReal (sampleHi gUp M dx) :=
  sample_bounds_of_cover hd hM (aux_grid_mem_of_checked hchk)
    (fun _ hy hy' => aux_exists_grid_close hchk hy hy') hlo hup hl hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
