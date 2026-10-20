module

public import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledRight
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.MemStackRowsConstructIff
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLast
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecPadRight
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# What a point of `halfScaledRight` says about its second block

The converse of `smul_mem_halfScaledRight`: a coefficient vector in the weighted polytope has its
last block meeting `P`'s rows at the weight `(1 - t) / 2` its trailing coordinate names, an
inequality's bound and an equality's right-hand side both scaled by it.

## Inputs
* `P` – H-polytope
* `z` – point of length `n₁`
* `y` – vector of length `n₂`
* `t` – real number

## Hypotheses
* `h` – the point `(z, y, t)` lies in `halfScaledRight`

## Conclusion
* what a point of `halfScaledRight` says about its second block
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_halfScaledRight {P : HPolytope 𝕋 (Vec 𝕋 n₂)} {z : Vec ℝ n₁}
    {y : Vec ℝ n₂} {t : ℝ}
    (h : Fin.append (Fin.append z y) (fun _ : Fin 1 => t)
      ∈ (HPolytope.halfScaledRight n₁ P).construct) : -- --- CONCL ---
    (∀ i, (toRealMat P.A *ᵥ y) i ≤ (1 - t) / 2 * toReal (P.b i) + |toReal (P.b_error i)|) ∧
      ∀ i, |(toRealMat P.Ae *ᵥ y) i - (1 - t) / 2 * toReal (P.be i)|
        ≤ |toReal (P.be_error i)| := by -- --- PROOF ---
  have hneg : toRealMat (fun i => -P.Ae i) = -toRealMat P.Ae := toRealMat_neg P.Ae
  -- the three row groups of the weighted polytope, each with its slack
  rw [HPolytope.halfScaledRight, HPolytope.mem_stackRows_iff,
    HPolytope.mem_stackRows_nominal_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  have h1 := (HPolytope.mem_nominal_iff.mp h1).1
  have h2 := (HPolytope.mem_nominal_iff.mp h2).1
  have h3 := (HPolytope.mem_nominal_iff.mp h3).1
  -- each read on the block it came from
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have : (toRealMat (fun i => Fin.append (Fin.append (fun _ : Fin n₁ => FloatOps.zero) (P.A i))
        fun _ : Fin 1 => half (P.b i)) *ᵥ _) i
          ≤ toReal (half (P.b i)) + |toReal (P.b_error i)| := h1 i
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padRight, blockRight_append] at this
    simp only [toReal_half] at this
    linarith
  · have h2' : (toRealMat (fun i =>
        Fin.append (Fin.append (fun _ : Fin n₁ => FloatOps.zero) (P.Ae i))
          fun _ : Fin 1 => half (P.be i)) *ᵥ _) i
          ≤ toReal (half (P.be i)) + |toReal (P.be_error i)| := h2 i
    -- the equality's lower edge, read through its negated row
    have h3' : (toRealMat (fun i =>
        Fin.append (Fin.append (fun _ : Fin n₁ => FloatOps.zero) (-(P.Ae i)))
          fun _ : Fin 1 => half (neg (P.be i))) *ᵥ _) i
          ≤ toReal (half (neg (P.be i))) + |toReal (P.be_error i)| := h3 i
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padRight, blockRight_append] at h2'
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padRight, blockRight_append, hneg,
      Matrix.neg_mulVec] at h3'
    simp only [Pi.neg_apply, toReal_neg, toReal_half] at h2' h3'
    rw [abs_le]
    constructor <;> linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
