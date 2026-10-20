module

public import CORALean.ContSet.Zonotope.Real.Theorems.HRepLinSubset
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic

@[expose] public section

/-!
# A zonotope with stretched generators, cut out by its template's halfspaces

`⟨c, G diag(α)⟩`, `α ≥ 0`, is the set the cross products of the *template* `G` cut out at offsets
`∑ⱼ |n·gⱼ| αⱼ`, linear in `α` — which makes reachset-conformant identification a linear program
[1, Thm. 1]. For `α > 0` the stretched zonotope's own normals are positive multiples of the
template's, and [2, Thm. 7] applies directly. At `αⱼ = 0` a generator vanishes and every normal
through it with it; the statement holds all the same, by closure: the point lies in every stretch
by `α + ε`, and these shrink onto the closed `⟨c, G diag(α)⟩`. The template must span, as in
[2, Thm. 7]. `N` may be any family carrying both signs of every template normal up to a positive
factor — the printed normalized rows among them, and zero rows wherever generators are dependent.

## Inputs
* `n` – dimension minus one
* `κ` – index type
* `Z` – zonotope
* `N` – template directions
* `α` – generator scalings
* `y` – point

## Hypotheses
* `hspan` – generators span the space
* `hN` – template carries both signs of every normal
* `hα` – scalings nonnegative

## Conclusion
* membership in the scaled zonotope is a template halfspace condition

## References

* [1] S. B. Liu, B. Schürmann and M. Althoff. "Guarantees for Real Robotic Systems:
      Unifying Formal Controller Synthesis and Reachset-Conformant Identification". IEEE
      Transactions on Robotics, 39(5):3776-3790, 2023.
* [2] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid Systems Using a
      Combination of Zonotopes and Polytopes". Nonlinear Analysis: Hybrid Systems,
      4(2):233-249, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Scaling column `j` by `d j` scales the cross product by `∏ d`. -/
theorem aux_nCross_scale {n : ℕ} (H : Mat ℝ (n + 1) n) (d : Fin n → ℝ) :
    nCross (Matrix.of fun i j => d j * H i j) = (∏ j, d j) • nCross H := by -- --- PROOF ---
  funext i
  have hsub : (Matrix.of fun i j => d j * H i j).submatrix i.succAbove id
      = H.submatrix i.succAbove id * Matrix.diagonal d := by
    ext a b
    simp [Matrix.mul_diagonal, mul_comm]
  simp only [nCross, Pi.smul_apply, smul_eq_mul]
  rw [hsub, Matrix.det_mul, Matrix.det_diagonal]
  ring

/-- Pairing with `v`, as the linear form `hRep_lin_subset` takes. -/
noncomputable def aux_dotLin {n : ℕ} (v : Vec ℝ n) : Vec ℝ n →ₗ[ℝ] ℝ where
  toFun y := v ⬝ᵥ y
  map_add' y z := dotProduct_add v y z
  map_smul' r y := dotProduct_smul r v y

/-- Every stretch by `ε > 0` of a point the template halfspaces admit contains it. -/
theorem aux_mem_stretch {n : ℕ} {κ : Type} (Z : Zonotope (Vec ℝ (n + 1)))
    (hspan : Submodule.span ℝ (Set.range Z.G) = ⊤) (N : κ → Vec ℝ (n + 1))
    (hN : ∀ S : Fin n → Fin Z.h, ∃ (i₁ i₂ : κ) (lam : ℝ), 0 < lam ∧
      N i₁ = lam • Z.facetNormal S ∧ N i₂ = -(lam • Z.facetNormal S))
    (α : Fin Z.h → ℝ) (hα : ∀ j, 0 ≤ α j) (y : Vec ℝ (n + 1))
    (hy : ∀ i, N i ⬝ᵥ (y - Z.c) ≤ ∑ j, |N i ⬝ᵥ Z.G j| * α j) (ε : ℝ) (hε : 0 < ε) : -- --- CONCL ---
    ∃ β : Fin Z.h → ℝ, (∀ j, |β j| ≤ 1) ∧
      y = Z.c + ∑ j, β j • (α j + ε) • Z.G j := by -- --- PROOF ---
  let Zε : Zonotope (Vec ℝ (n + 1)) := ⟨Z.h, Z.c, fun j => (α j + ε) • Z.G j⟩
  have hpos : ∀ j, 0 < α j + ε := fun j => by linarith [hα j]
  -- the stretch spans: each template generator is a multiple of a stretched one
  have hspanε : Submodule.span ℝ (Set.range Zε.G) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    have hj : Z.G j = (α j + ε)⁻¹ • Zε.G j := by
      simp only [Zε, smul_smul, inv_mul_cancel₀ (hpos j).ne', one_smul]
    rw [hj]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  -- its normals are the template's, times a positive factor
  have hnorm : ∀ S : Fin n → Fin Z.h,
      Zε.facetNormal S = (∏ b, (α (S b) + ε)) • Z.facetNormal S := fun S =>
    aux_nCross_scale (Matrix.of fun i j => Z.G (S j) i) (fun b => α (S b) + ε)
  have hC : ∀ S : Fin n → Fin Zε.h, ∃ (i₁ i₂ : κ) (lam : ℝ), 0 < lam ∧
      (∀ x, aux_dotLin (N i₁) x = lam * (Zε.facetNormal S ⬝ᵥ x)) ∧
      (∀ x, aux_dotLin (N i₂) x = -(lam * (Zε.facetNormal S ⬝ᵥ x))) := by
    intro S
    obtain ⟨i₁, i₂, lam, hlam, h₁, h₂⟩ := hN S
    have hP : 0 < ∏ b, (α (S b) + ε) := Finset.prod_pos fun b _ => hpos (S b)
    refine ⟨i₁, i₂, lam / ∏ b, (α (S b) + ε), div_pos hlam hP, fun x => ?_, fun x => ?_⟩
    · simp only [aux_dotLin, LinearMap.coe_mk, AddHom.coe_mk, h₁, hnorm S, smul_dotProduct,
        smul_eq_mul]
      field_simp
    · simp only [aux_dotLin, LinearMap.coe_mk, AddHom.coe_mk, h₂, hnorm S, neg_dotProduct,
        smul_dotProduct, smul_eq_mul]
      field_simp
  -- the stretched offsets only grow, so `y` meets every stretched halfspace
  have hyε : y ∈ {x | ∀ i, aux_dotLin (N i) (x - Zε.c) ≤ ∑ υ, |aux_dotLin (N i) (Zε.G υ)|} := by
    intro i
    simp only [aux_dotLin, LinearMap.coe_mk, AddHom.coe_mk, Zε, dotProduct_smul, smul_eq_mul,
      abs_mul, abs_of_pos (hpos _)]
    refine le_trans (hy i) (Finset.sum_le_sum fun j _ => ?_)
    nlinarith [abs_nonneg (N i ⬝ᵥ Z.G j)]
  obtain ⟨β, hβ, hyβ⟩ := Zε.hRep_lin_subset (fun i => aux_dotLin (N i)) hspanε hC hyε
  exact ⟨β, hβ, hyβ⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- `⟨c, G diag(α)⟩`, `α ≥ 0`, is exactly the template's halfspaces at offsets linear
in `α` [1, Thm. 1], the template spanning as in [2, Thm. 7]. -/
theorem Zonotope.mem_scale_iff {n : ℕ} {κ : Type} (Z : Zonotope (Vec ℝ (n + 1)))
    (hspan : Submodule.span ℝ (Set.range Z.G) = ⊤) (N : κ → Vec ℝ (n + 1))
    (hN : ∀ S : Fin n → Fin Z.h, ∃ (i₁ i₂ : κ) (lam : ℝ), 0 < lam ∧
      N i₁ = lam • Z.facetNormal S ∧ N i₂ = -(lam • Z.facetNormal S))
    (α : Fin Z.h → ℝ) (hα : ∀ j, 0 ≤ α j) (y : Vec ℝ (n + 1)) : -- --- CONCL ---
    y ∈ (⟨Z.h, Z.c, fun j => α j • Z.G j⟩ : Zonotope (Vec ℝ (n + 1))).construct ↔
      ∀ i, N i ⬝ᵥ (y - Z.c) ≤ ∑ j, |N i ⬝ᵥ Z.G j| * α j := by -- --- PROOF ---
  constructor
  · -- every point of the stretched zonotope meets the stretched offsets
    rintro ⟨β, hβ, rfl⟩ i
    have hsub : Z.c + ∑ j, β j • α j • Z.G j - Z.c = ∑ j, β j • α j • Z.G j := by abel
    rw [hsub, dotProduct_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    calc β j * (α j * (N i ⬝ᵥ Z.G j)) ≤ |β j * (α j * (N i ⬝ᵥ Z.G j))| := le_abs_self _
      _ = |β j| * (α j * |N i ⬝ᵥ Z.G j|) := by rw [abs_mul, abs_mul, abs_of_nonneg (hα j)]
      _ ≤ 1 * (α j * |N i ⬝ᵥ Z.G j|) :=
          mul_le_mul_of_nonneg_right (hβ j) (mul_nonneg (hα j) (abs_nonneg _))
      _ = |N i ⬝ᵥ Z.G j| * α j := by ring
  · -- the converse by closure: `y` is a limit of points of the stretched zonotope
    intro hy
    let Zα : Zonotope (Vec ℝ (n + 1)) := ⟨Z.h, Z.c, fun j => α j • Z.G j⟩
    rw [← Zα.isClosed_construct.closure_eq, Metric.mem_closure_iff]
    intro δ hδ
    set K : ℝ := ∑ j, ‖Z.G j‖ + 1 with hKdef
    have hK : 0 < K := by
      have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => norm_nonneg (Z.G j)
      linarith
    have hε : 0 < δ / (2 * K) := by positivity
    obtain ⟨β, hβ, hyβ⟩ := aux_mem_stretch Z hspan N hN α hα y hy _ hε
    refine ⟨Z.c + ∑ j, β j • α j • Z.G j, ⟨β, hβ, rfl⟩, ?_⟩
    -- the distance is `ε ‖∑ βⱼ gⱼ‖ ≤ ε K`
    have hdiff : y - (Z.c + ∑ j, β j • α j • Z.G j)
        = (δ / (2 * K)) • ∑ j, β j • Z.G j := by
      rw [hyβ, Finset.smul_sum]
      have : ∀ j, β j • (α j + δ / (2 * K)) • Z.G j - β j • α j • Z.G j
          = (δ / (2 * K)) • β j • Z.G j := fun j => by
        rw [smul_comm (δ / (2 * K)) (β j), add_smul, smul_add, add_sub_cancel_left]
      rw [← Finset.sum_congr rfl fun j _ => this j, Finset.sum_sub_distrib]
      abel
    rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    have hsum : ‖∑ j, β j • Z.G j‖ ≤ K := by
      refine le_trans (norm_sum_le _ _) ?_
      rw [hKdef]
      refine le_trans (Finset.sum_le_sum fun j _ => ?_) (le_add_of_nonneg_right zero_le_one)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hβ j)
    calc δ / (2 * K) * ‖∑ j, β j • Z.G j‖ ≤ δ / (2 * K) * K :=
          mul_le_mul_of_nonneg_left hsum hε.le
      _ = δ / 2 := by field_simp
      _ < δ := by linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
