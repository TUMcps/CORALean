module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Zonotope.Real.Operations.FacetNormal
public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffApprox
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

/-!
# `Zonotope.minkDiffApprox` is not inner

CORA's default `'approx'` [1] solves `|C G| α = Δd` by `pinv`. Where the system is inconsistent
the least-squares `α` trades one halfspace against another, and the scaled minuend can cross a
shifted halfspace. In `ℝ³` the minuend `Z_m = (0, [g₁ g₂ g₃ g₄])`, `g₁ = (0, 1, -1)`,
`g₂ = (0, 1, 1)`, `g₃ = (2, 0, -1)`, `g₄ = (2, 0, 1)`, has six facet directions, and the
subtrahend is the segment `Z_s = (0, (0, 0, ½))`. Then `Δd = (4, 7/3, 7/3, 7/3, 7/3, 2)` and
`α = (25/29, 25/29, 28/29, 28/29)`, all positive. The point `p = (25/29) g₂ + (28/29) g₄` of the
result, plus `(0, 0, ½) ∈ Z_s`, has `x₁ + 2x₂ + 2x₃ = 241/29`, while `Z_m` has
`x₁ + 2x₂ + 2x₃ ≤ 8 = 232/29`. The difference itself is nonempty: it holds `0`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the approximation can leave a nonempty Minkowski difference

## References

* [1] `contSet/@zonotope/minkDiff.m`, CORA, ll. 78, 114-138, 291-307.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The minuend, four generators in `ℝ³`. -/
def aux_Am : Zonotope (Vec ℝ 3) := ⟨4, 0, ![![0, 1, -1], ![0, 1, 1], ![2, 0, -1], ![2, 0, 1]]⟩

/-- The subtrahend, a segment along the third axis. -/
noncomputable def aux_As : Zonotope (Vec ℝ 3) := ⟨1, 0, ![![0, 0, 1 / 2]]⟩

/-- The six normals `polytope.m` builds, in `combinator`'s order. -/
noncomputable def aux_AC : Mat ℝ 6 3 :=
  !![1, 0, 0; -1/3, -2/3, -2/3; 1/3, -2/3, -2/3; -1/3, 2/3, -2/3; 1/3, 2/3, -2/3; 0, -1, 0]

/-- The pairs of generators behind them. -/
def aux_AS : Fin 6 → Fin 2 → Fin 4 := ![![0, 1], ![0, 2], ![0, 3], ![1, 2], ![1, 3], ![2, 3]]

/-- `|C G|`. -/
noncomputable def aux_AA : Mat ℝ 6 4 :=
  !![0, 0, 2, 2; 0, 4/3, 0, 4/3; 0, 4/3, 4/3, 0; 4/3, 0, 0, 4/3; 4/3, 0, 4/3, 0; 1, 1, 0, 0]

/-- `(|C G|ᵀ |C G|)⁻¹`. -/
noncomputable def aux_AMinv : Mat ℝ 4 4 :=
  !![469/1856, -53/1856, -1/29, -1/29; -53/1856, 469/1856, -1/29, -1/29;
    -1/29, -1/29, 361/1856, -161/1856; -1/29, -1/29, -161/1856, 361/1856]

/-- Each pair is listed in increasing order. -/
theorem aux_S_strictMono (i : Fin 6) : StrictMono (aux_AS i) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro j
  fin_cases i <;> fin_cases j <;> simp [aux_AS, Fin.lt_def]

/-- No pair twice, so the six are all of `combinator(4, 2, 'c')`. -/
theorem aux_S_injective : Function.Injective aux_AS := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases a <;> fin_cases b <;> simp_all [aux_AS]

/-- The cross products behind them, unnormalised. -/
noncomputable def aux_AV : Fin 6 → Vec ℝ 3 :=
  ![![2, 0, 0], ![-1, -2, -2], ![1, -2, -2], ![-1, 2, -2], ![1, 2, -2], ![0, -4, 0]]

/-- `ndimCross` at each pair. -/
theorem aux_facetNormal_eq (i : Fin 6) :
    aux_Am.facetNormal (aux_AS i) = aux_AV i := by -- --- PROOF ---
  have h21 : Fin.succAbove (2 : Fin 3) 1 = 1 := rfl
  ext k
  fin_cases i <;> fin_cases k <;>
    simp [aux_Am, aux_AS, aux_AV, Zonotope.facetNormal, nCross, Matrix.det_fin_two, h21] <;>
    norm_num

/-- The rows of `C` are those cross products over their Euclidean lengths `2, 3, 3, 3, 3, 4`. -/
theorem aux_C_eq (i : Fin 6) :
    aux_AC i = (√(aux_Am.facetNormal (aux_AS i) ⬝ᵥ aux_Am.facetNormal (aux_AS i)))⁻¹
      • aux_Am.facetNormal (aux_AS i) := by
  rw [aux_facetNormal_eq]
  ext k
  fin_cases i <;> fin_cases k <;>
    simp [aux_AC, aux_AV, dotProduct, Fin.sum_univ_three] <;> norm_num

/-- `A_abs = |C G|`. -/
theorem aux_A_eq : (Matrix.of fun i j => |aux_AC i ⬝ᵥ aux_Am.G j| : Mat ℝ 6 4) = aux_AA := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aux_AC, aux_Am, aux_AA, dotProduct, Fin.sum_univ_three]
    <;> norm_num [abs_of_nonneg, abs_of_nonpos]

/-- The Gram matrix of `|C G|` is invertible, so `pinv` is `(AᵀA)⁻¹Aᵀ`. -/
theorem aux_inv : (aux_AAᵀ * aux_AA)⁻¹ = aux_AMinv := by
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aux_AA, aux_AMinv, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

/-- A sum over the minuend's generators, at `Fin 4`. -/
theorem aux_sum_univ_Zm {M : Type} [AddCommMonoid M] (f : Fin aux_Am.h → M) :
    ∑ j, f j = f (0 : Fin 4) + f (1 : Fin 4) + f (2 : Fin 4) + f (3 : Fin 4) :=
  Fin.sum_univ_four f

/-- A sum over the subtrahend's generator, at `Fin 1`. -/
theorem aux_sum_univ_Zs {M : Type} [AddCommMonoid M] (f : Fin aux_As.h → M) :
    ∑ j, f j = f (0 : Fin 1) :=
  Fin.sum_univ_one f

/-- `Δd`. -/
noncomputable def aux_Add : Vec ℝ 6 := ![4, 7/3, 7/3, 7/3, 7/3, 2]

/-- `delta_d = d - C c⁽ᵐ⁾ + C c⁽ˢ⁾`, the centers being `0`. -/
theorem aux_dd_eq :
    (fun i => aux_AC i ⬝ᵥ aux_Am.c + ∑ j : Fin 4, |aux_AC i ⬝ᵥ aux_Am.G j|
      - (aux_AC i ⬝ᵥ aux_As.c + ∑ k : Fin 1, |aux_AC i ⬝ᵥ aux_As.G k|)
      - aux_AC i ⬝ᵥ aux_Am.c + aux_AC i ⬝ᵥ aux_As.c : Vec ℝ 6) = aux_Add := by
  ext i
  fin_cases i <;>
    simp [aux_AC, aux_Am, aux_As, aux_Add, dotProduct, Fin.sum_univ_succ] <;>
    norm_num [abs_of_nonneg, abs_of_nonpos]

/-- The least-squares solution. -/
theorem aux_alpha_eq :
    (aux_AAᵀ * aux_AA)⁻¹ *ᵥ (aux_AAᵀ *ᵥ aux_Add) = ![25/29, 25/29, 28/29, 28/29] := by
  rw [aux_inv]
  ext i
  fin_cases i <;> simp [aux_AA, aux_AMinv, aux_Add, mulVec, dotProduct, Fin.sum_univ_succ] <;>
    norm_num

/-- CORA's `α`: `pinv(|C G|) Δd = (25/29, 25/29, 28/29, 28/29)`. -/
theorem aux_minkDiffApprox :
    aux_Am.minkDiffApprox aux_As aux_AC
      = aux_Am.minkDiffStretch aux_As ![25/29, 25/29, 28/29, 28/29] := by -- --- PROOF ---
  -- the matrix and the right-hand side, at `Fin 4` rather than `Fin aux_Am.h`
  have key : ∀ (A : Mat ℝ 6 4) (dd : Vec ℝ 6), A = aux_AA → dd = aux_Add →
      (Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ dd) = ![25/29, 25/29, 28/29, 28/29] := by
    rintro A dd rfl rfl
    exact aux_alpha_eq
  simp only [Zonotope.minkDiffApprox]
  congr 1
  exact key _ _ aux_A_eq aux_dd_eq


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `'approx'`, at a minuend's own normalised facet normals, can leave the Minkowski
difference while that difference is nonempty. -/
theorem Zonotope.minkDiffApprox_not_inner : -- --- CONCL ---
    ∃ (Z₁ Z₂ : Zonotope (Vec ℝ 3)) (C : Mat ℝ 6 3) (S : Fin 6 → Fin 2 → Fin Z₁.h),
      (∀ i, StrictMono (S i)) ∧ Function.Injective S ∧
      (∀ i, C i = (√(Z₁.facetNormal (S i) ⬝ᵥ Z₁.facetNormal (S i)))⁻¹
        • Z₁.facetNormal (S i)) ∧
      (0 : Vec ℝ 3) ∈ minkowskiDiff Z₁.construct Z₂.construct ∧
      ¬ (Z₁.minkDiffApprox Z₂ C).construct
          ⊆ minkowskiDiff Z₁.construct Z₂.construct := by -- --- PROOF ---
  refine ⟨aux_Am, aux_As, aux_AC, aux_AS, aux_S_strictMono, aux_S_injective, aux_C_eq, ?_, ?_⟩
  -- `0` is in the difference: `(0, 0, t/2) = (t/4) (g₂ - g₁)`
  · rintro y ⟨β, hβ, rfl⟩
    have hb : |β (0 : Fin 1)| ≤ 1 := hβ (0 : Fin 1)
    have hβ' :
        ∀ j : Fin 4, |(![-(β (0 : Fin 1)) / 4, β (0 : Fin 1) / 4, 0, 0] : Fin 4 → ℝ) j| ≤ 1 := by
      intro j
      fin_cases j <;> simp [abs_div] <;> linarith
    refine ⟨_, hβ', ?_⟩
    rw [aux_sum_univ_Zm, aux_sum_univ_Zs]
    ext k
    fin_cases k <;> simp [aux_Am, aux_As] <;> ring
  -- `p = (25/29) g₂ + (28/29) g₄` plus `(0, 0, ½)` crosses `x₁ + 2x₂ + 2x₃ ≤ 8`
  · intro hsub
    rw [aux_minkDiffApprox] at hsub
    have hp : (![56/29, 25/29, 53/29] : Vec ℝ 3)
        ∈ (aux_Am.minkDiffStretch aux_As ![25/29, 25/29, 28/29, 28/29]).construct := by
      have hb : ∀ j : Fin 4, |(![0, 1, 0, 1] : Fin 4 → ℝ) j| ≤ 1 := by
        intro j
        fin_cases j <;> simp
      refine ⟨_, hb, ?_⟩
      show _ = aux_Am.c - aux_As.c + ∑ j : Fin 4,
        (![0, 1, 0, 1] : Fin 4 → ℝ) j • ((![25/29, 25/29, 28/29, 28/29] : Fin 4 → ℝ) j • aux_Am.G j)
      rw [Fin.sum_univ_four]
      ext k
      fin_cases k <;> simp [aux_Am, aux_As] <;>
        norm_num
    -- `s = (0, 0, ½)`, at coefficient `1`
    have hs : (![0, 0, 1/2] : Vec ℝ 3) ∈ aux_As.construct :=
      ⟨fun _ => 1, fun _ => by simp, by ext k; fin_cases k <;> simp [aux_As]⟩
    obtain ⟨β, hβ, hx⟩ := hsub hp _ hs
    rw [aux_sum_univ_Zm] at hx
    have h0 := congrFun hx 0
    have h1 := congrFun hx 1
    have h2 := congrFun hx 2
    simp [aux_Am] at h0 h1 h2
    have hb1 := abs_le.mp (hβ (1 : Fin 4))
    have hb3 := abs_le.mp (hβ (3 : Fin 4))
    linarith [hb1.2, hb3.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
