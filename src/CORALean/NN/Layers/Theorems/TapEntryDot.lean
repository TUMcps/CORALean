module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.NN.Layers.Theorems.TapEntryEqZero

@[expose] public section

/-!
# A stencil row against a vector is the weighted sum over its taps

Which makes `tapMat` the matrix of a stencil. Injectivity is what a window reading one input
twice would break: the matrix holds one weight per entry, the sum two.

## Inputs
* `n` – number of inputs

## Hypotheses
* none

## Conclusion
* a stencil row against a vector is the weighted sum over its taps
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem tapEntry_dot {n : ℕ} :
    ∀ {k : ℕ} (t : Fin k → Fin n) (v : Fin k → 𝕋) (x : Vec ℝ n), Function.Injective t →
      ∑ i, toReal (tapEntry t v i) * x i = ∑ l, toReal (v l) * x (t l) := by -- --- PROOF ---
  intro k
  induction k with
  | zero =>
    intro t v x _
    have h0 : ∀ i : Fin n, toReal (tapEntry t v i) * x i = 0 := fun i => by
      show toReal (zero : 𝕋) * x i = 0
      rw [toReal_zero, zero_mul]
    rw [Finset.sum_congr rfl fun i _ => h0 i, Finset.sum_const_zero, Fin.sum_univ_zero]
  | succ k ih =>
    intro t v x ht
    -- injectivity is what makes the first tap's entry vanish from the rest
    have hz : tapEntry (fun l => t l.succ) (fun l => v l.succ) (t 0) = zero :=
      tapEntry_eq_zero _ _ _ fun l hl => Fin.succ_ne_zero l (ht hl)
    have key : ∀ i, toReal (tapEntry t v i) * x i
        = (if t 0 = i then toReal (v 0) * x i else 0)
          + toReal (tapEntry (fun l => t l.succ) (fun l => v l.succ) i) * x i := by
      intro i
      show toReal (if t 0 = i then v 0 else tapEntry (fun l => t l.succ) (fun l => v l.succ) i)
          * x i = _
      by_cases hi : t 0 = i
      · rw [if_pos hi, if_pos hi, ← hi, hz, toReal_zero]
        ring
      · rw [if_neg hi, if_neg hi]
        ring
    rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib,
      Finset.sum_ite_eq Finset.univ (t 0) fun i => toReal (v 0) * x i,
      if_pos (Finset.mem_univ (t 0)), ih _ _ x (fun a b hab => Fin.succ_injective k (ht hab)),
      Fin.sum_univ_succ (f := fun l => toReal (v l) * x (t l))]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
