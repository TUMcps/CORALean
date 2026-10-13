module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.NN.Layers.Operations.GridChecked
public import CORALean.NN.Layers.Theorems.AllOverApply

@[expose] public section

/-!
# Every point of the box is near a checked sample

Within one spacing, which is what lets the sampled range speak for the whole box: walk right
from the left end until the next sample overshoots the point.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem exists_grid_close {p : Fin (N + 1) → 𝕋} {l u dx : 𝕋} {t : ℝ}
    (h : gridChecked p l u dx) (hl : toReal l ≤ t) (hu : t ≤ toReal u) :
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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
