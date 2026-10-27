module

public import CORALean.NN.Layers.Operations.TapMat
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.NN.Layers.Operations.TapEntry
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# A stencil matrix times a vector

Row `j` of the product is the weighted sum over output `j`'s taps, the weights read into ℝ:
`aux_tapEntry_dot` at that row, which is why the taps of every row must be injective. At a
convolution's stencil this is [1, Sec. II (Conv to CAT)]: Appendix A's `W^F`, whose entries are
`Σ W_{i'j'k'} [l = idx(i', j', k')]`, times `x` is the convolution, at any injective stencil.

## Inputs
* `tap` – input index of every kernel position
* `w` – weight of every kernel position
* `x` – input vector
* `j` – output coordinate

## Hypotheses
* `htap` – the taps of an output are distinct

## Conclusion
* the stencil matrix gives the weighted sum over the taps

## References

* [1] [T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2: Safety
      and Robustness Certification of Neural Networks with Abstract Interpretation". 2018 IEEE
      Symposium on Security and Privacy (SP), 2018.](../../../../../references/2018/gehr-sp-ai2.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Float Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open Float.FloatOps
variable {𝕋 : Type} [FloatOps 𝕋]

/-- An input no tap reads gets weight zero. -/
private theorem aux_tapEntry_eq_zero {n : ℕ} : -- --- CONCL ---
    ∀ {k : ℕ} (t : Fin k → Fin n) (v : Fin k → 𝕋) (i : Fin n),
      (∀ l, t l ≠ i) → tapEntry t v i = FloatOps.zero := by -- --- PROOF ---
  intro k
  induction k with
  | zero => intro _ _ _ _; rfl
  | succ k ih =>
    intro t v i h
    show (if t 0 = i then v 0 else tapEntry (fun l => t l.succ) (fun l => v l.succ) i) =
      FloatOps.zero
    rw [if_neg (h 0)]
    exact ih _ _ _ fun l => h l.succ

end


section
open Float.FloatOps
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- A stencil row against a vector is the weighted sum over its taps. -/
private theorem aux_tapEntry_dot {n : ℕ} : -- --- CONCL ---
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
    have hz : tapEntry (fun l => t l.succ) (fun l => v l.succ) (t 0) = FloatOps.zero :=
      aux_tapEntry_eq_zero _ _ _ fun l hl => Fin.succ_ne_zero l (ht hl)
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

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem tapMat_mulVec (tap : Fin m → Fin k → Fin n) (w : Fin m → Fin k → 𝕋)
    (htap : ∀ j, Function.Injective (tap j)) (x : Vec ℝ n) (j : Fin m) :
    (toRealMat (tapMat tap w) *ᵥ x) j = ∑ l, toReal (w j l) * x (tap j l) := by
  show ∑ i, toReal (tapEntry (tap j) (w j) i) * x i = _
  exact aux_tapEntry_dot (tap j) (w j) x (htap j)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
