module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqSqrt
public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructOfFactor

@[expose] public section

/-!
# An ellipsoid cut by a hyperplane is an ellipsoid

[1, Sec. II (hyperplane intersection)]: if nonempty, `E(q, Q) ∩ H(v, c)` is an ellipsoid. With `E =
q + G B`, `G = Q^(1/2)`, the cut is `q + G S` for the slice `S = {u ∈ B | wᵀ u = t}`, `w = Gᵀ v`, `t
= c - vᵀ q`, of the unit ball; a slice of a ball is a ball of the hyperplane, centered at `u₀ = (t /
‖w‖²) w` with radius `√(1 - ‖u₀‖²)`, the image of the unit ball under the projection `P = I - w wᵀ /
‖w‖²` scaled by that radius: the ellipsoid of shape `r² G P (G P)ᵀ`. When `w = 0` the hyperplane
contains all of `E` or none of it.

## Inputs
* `E` – ellipsoid
* `v` – hyperplane normal
* `c` – hyperplane offset

## Hypotheses
* `hne` – the intersection is nonempty

## Conclusion
* the intersection with the hyperplane is an ellipsoid

## References

* [1] A. A. Kurzhanskiy and P. Varaiya. "Ellipsoidal Toolbox (ET)". Proceedings of the 45th IEEE
      Conference on Decision and Control, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Inside the unit ball, by the squared length. -/
private theorem aux_norm₂_le_one_iff {k : ℕ} (u : Vec ℝ k) : ‖u‖₂ ≤ 1 ↔ u ⬝ᵥ u ≤ 1 := by
  rw [dotProduct_self, pow_le_one_iff_of_nonneg (norm₂_nonneg u) two_ne_zero]

/-- The projection `I - w wᵀ / s` applied. -/
private theorem aux_proj_mulVec {k : ℕ} (w z : Vec ℝ k) (s : ℝ) : -- --- CONCL ---
    ((1 : Mat ℝ k k) - s⁻¹ • vecMulVec w w) *ᵥ z = z - (s⁻¹ * (w ⬝ᵥ z)) • w := by -- --- PROOF ---
  funext i
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    vecMulVec_apply, Finset.mul_sum, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.inter_hyperplane_eq (E : Ellipsoid n) (v : Vec ℝ n) (c : ℝ)
    (hne : (E.construct ∩ {x | v ⬝ᵥ x = c}).Nonempty) : -- --- CONCL ---
    ∃ E' : Ellipsoid n, E.construct ∩ {x | v ⬝ᵥ x = c} = E'.construct := by -- --- PROOF ---
  obtain ⟨w, hw⟩ : ∃ w : Vec ℝ n, w = E.Gᵀ *ᵥ v := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = c - v ⬝ᵥ E.q := ⟨_, rfl⟩
  -- the hyperplane, read in coefficient space
  have hvG : ∀ u, v ⬝ᵥ (E.q + E.G *ᵥ u) = v ⬝ᵥ E.q + w ⬝ᵥ u := fun u => by
    rw [dotProduct_add, Matrix.dotProduct_mulVec, hw, Matrix.mulVec_transpose]
  have hmem : ∀ x, x ∈ E.construct ∩ {x | v ⬝ᵥ x = c} ↔
      ∃ u : Vec ℝ n, u ⬝ᵥ u ≤ 1 ∧ x = E.q + E.G *ᵥ u ∧ w ⬝ᵥ u = t := fun x => by
    rw [E.construct_eq_sqrt]
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hx⟩
      refine ⟨u, (aux_norm₂_le_one_iff u).mp hu, rfl, ?_⟩
      have : v ⬝ᵥ (E.q + E.G *ᵥ u) = c := hx
      rw [hvG] at this
      rw [ht]
      linarith
    · rintro ⟨u, hu, rfl, hwu⟩
      refine ⟨⟨u, (aux_norm₂_le_one_iff u).mpr hu, rfl⟩, ?_⟩
      show v ⬝ᵥ (E.q + E.G *ᵥ u) = c
      rw [hvG, hwu, ht]
      ring
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = w ⬝ᵥ w := ⟨_, rfl⟩
  rcases (show 0 ≤ s by rw [hs]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _).eq_or_lt
    with hs0 | hspos
  -- `w = 0`: the hyperplane holds on all of `E` or nowhere
  · have hw0 : w = 0 := dotProduct_self_eq_zero.mp (hs ▸ hs0.symm)
    obtain ⟨x, hx⟩ := hne
    obtain ⟨u, -, -, hwu⟩ := (hmem x).mp hx
    rw [hw0, zero_dotProduct] at hwu
    refine ⟨E, Set.ext fun y => ⟨fun hy => hy.1, fun hy => ?_⟩⟩
    rw [E.construct_eq_sqrt] at hy
    obtain ⟨u', hu', rfl⟩ := hy
    exact (hmem _).mpr ⟨u', (aux_norm₂_le_one_iff u').mp hu', rfl,
      by rw [hw0, zero_dotProduct, hwu]⟩
  -- otherwise the slice of the ball is a ball of the hyperplane
  · obtain ⟨u₀, hu₀⟩ : ∃ u₀ : Vec ℝ n, u₀ = (t / s) • w := ⟨_, rfl⟩
    have hwu₀ : w ⬝ᵥ u₀ = t := by
      rw [hu₀, dotProduct_smul, smul_eq_mul, ← hs]
      field_simp
    have hu₀u₀ : u₀ ⬝ᵥ u₀ = t ^ 2 / s := by
      rw [hu₀, smul_dotProduct, dotProduct_smul, ← hs, smul_eq_mul, smul_eq_mul]
      field_simp
    -- a point of the cut bounds `t² ≤ s`, by Cauchy–Schwarz
    have hρ : 0 ≤ 1 - u₀ ⬝ᵥ u₀ := by
      obtain ⟨x, hx⟩ := hne
      obtain ⟨u, hu, -, hwu⟩ := (hmem x).mp hx
      have hcs : (w ⬝ᵥ u) ^ 2 ≤ s * (u ⬝ᵥ u) := by
        have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w u
        simpa [dotProduct, sq, hs] using this
      rw [hu₀u₀, sub_nonneg, div_le_one hspos]
      rw [hwu] at hcs
      nlinarith
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = √(1 - u₀ ⬝ᵥ u₀) := ⟨_, rfl⟩
    have hr2 : r ^ 2 = 1 - u₀ ⬝ᵥ u₀ := by rw [hr]; exact Real.sq_sqrt hρ
    have hr0' : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
    obtain ⟨P, hP⟩ : ∃ P : Mat ℝ n n, P = 1 - s⁻¹ • vecMulVec w w := ⟨_, rfl⟩
    refine ⟨Ellipsoid.ofFactor (r • (E.G * P)) (E.q + E.G *ᵥ u₀), Set.ext fun x => ?_⟩
    rw [hmem, Ellipsoid.construct_ofFactor]
    constructor
    · rintro ⟨u, hu, rfl, hwu⟩
      -- `u = u₀ + d` with `d ⊥ w`, so `P d = d` and `‖d‖² = ‖u‖² - ‖u₀‖² ≤ r²`
      obtain ⟨d, hd⟩ : ∃ d : Vec ℝ n, d = u - u₀ := ⟨_, rfl⟩
      have hwd : w ⬝ᵥ d = 0 := by rw [hd, dotProduct_sub, hwu, hwu₀, sub_self]
      have hPd : P *ᵥ d = d := by rw [hP, aux_proj_mulVec, hwd, mul_zero, zero_smul, sub_zero]
      have hu₀d : u₀ ⬝ᵥ d = 0 := by rw [hu₀, smul_dotProduct, hwd, smul_zero]
      have hdd : d ⬝ᵥ d ≤ r ^ 2 := by
        rw [hr2]
        have : u ⬝ᵥ u = u₀ ⬝ᵥ u₀ + d ⬝ᵥ d := by
          rw [show u = u₀ + d by rw [hd]; abel, add_dotProduct, dotProduct_add, dotProduct_add,
            dotProduct_comm d u₀, hu₀d]
          ring
        linarith
      rcases hr0'.eq_or_lt with hr0 | hrpos
      · -- `r = 0`: the cut is the single point `q + G u₀`
        have hd0 : d = 0 := by
          rw [← hr0] at hdd
          exact dotProduct_self_eq_zero.mp (le_antisymm (by simpa using hdd)
            (Finset.sum_nonneg fun i _ => mul_self_nonneg _))
        refine ⟨0, (aux_norm₂_le_one_iff _).mpr (by simp), ?_⟩
        show E.q + E.G *ᵥ u = E.q + E.G *ᵥ u₀ + (r • (E.G * P)) *ᵥ 0
        rw [Matrix.mulVec_zero, add_zero, show u = u₀ + d by rw [hd]; abel, hd0, add_zero]
      · refine ⟨r⁻¹ • d, (aux_norm₂_le_one_iff _).mpr ?_, ?_⟩
        · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
            ← sq, inv_pow]
          exact (inv_mul_le_one₀ (pow_pos hrpos 2)).mpr hdd
        · have key : (r • (E.G * P)) *ᵥ (r⁻¹ • d) = E.G *ᵥ d := by
            rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hrpos.ne',
              one_smul, ← Matrix.mulVec_mulVec, hPd]
          show E.q + E.G *ᵥ u = E.q + E.G *ᵥ u₀ + (r • (E.G * P)) *ᵥ (r⁻¹ • d)
          rw [key, add_assoc, ← Matrix.mulVec_add, show u₀ + d = u by rw [hd]; abel]
    · rintro ⟨z, hz, rfl⟩
      -- the point `u₀ + r P z` of coefficient space
      have hz' := (aux_norm₂_le_one_iff z).mp hz
      have hPz : P *ᵥ z = z - (s⁻¹ * (w ⬝ᵥ z)) • w := by rw [hP, aux_proj_mulVec]
      have hwPz : w ⬝ᵥ (P *ᵥ z) = 0 := by
        rw [hPz, dotProduct_sub, dotProduct_smul, smul_eq_mul, ← hs]
        field_simp
        ring
      have hPzPz : (P *ᵥ z) ⬝ᵥ (P *ᵥ z) ≤ 1 := by
        have h1 : (P *ᵥ z) ⬝ᵥ (P *ᵥ z) = z ⬝ᵥ z - (w ⬝ᵥ z) ^ 2 / s := by
          rw [hPz, sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct,
            dotProduct_smul, smul_dotProduct, dotProduct_smul, ← hs, dotProduct_comm z w]
          simp only [smul_eq_mul]
          field_simp
          ring
        rw [h1]
        have : 0 ≤ (w ⬝ᵥ z) ^ 2 / s := by positivity
        linarith
      -- in the ball, mapped to the point, and on the hyperplane
      refine ⟨u₀ + r • (P *ᵥ z), ?_, ?_, ?_⟩
      · have hu₀Pz : u₀ ⬝ᵥ (P *ᵥ z) = 0 := by rw [hu₀, smul_dotProduct, hwPz, smul_zero]
        rw [add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct, dotProduct_smul,
          dotProduct_smul, smul_dotProduct, dotProduct_comm (P *ᵥ z) u₀, hu₀Pz]
        simp only [smul_eq_mul, mul_zero, add_zero, zero_add]
        have hr2' : r * (r * ((P *ᵥ z) ⬝ᵥ (P *ᵥ z))) ≤ r ^ 2 := by
          rw [← mul_assoc, ← sq]
          exact mul_le_of_le_one_right (sq_nonneg r) hPzPz
        rw [hr2] at hr2'
        linarith
      · show E.q + E.G *ᵥ u₀ + (r • (E.G * P)) *ᵥ z = E.q + E.G *ᵥ (u₀ + r • (P *ᵥ z))
        rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
          add_assoc]
      · rw [dotProduct_add, dotProduct_smul, hwPz, smul_zero, add_zero, hwu₀]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
