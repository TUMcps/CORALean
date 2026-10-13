module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Vertices
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A one-dimensional float ellipsoid lies in the hull of its vertices

`x = q + G₀ u + e` with `|G₀ u| ≤ ‖G₀‖₂ ‖u‖₂ ≤ ρ` (Cauchy-Schwarz) and `e` in the error box: so `x`
is between the two rounded ends, which is a point of the segment joining them. Outer only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.vertices_outer (k : ℕ) (E : Ellipsoid 𝕋 1) :
    E.construct ⊆ convexHull ℝ {y | ∃ v ∈ E.vertices k, toRealVec v = y} := by -- --- PROOF ---
  rintro _ ⟨y, hy, e, he, rfl⟩
  show y + e ∈ _
  obtain ⟨u, hu, hyu⟩ := Ellipsoid.mem_nominalSet_iff.mp hy
  -- Cauchy-Schwarz bounds the generator row's contribution by the rounded-up length
  set ρ := normUp k fun j => E.G 0 j with hρ
  have hρ' : ‖fun j => toReal (E.G 0 j)‖₂ ≤ toReal ρ := norm₂_le_normUp k fun j => le_refl _
  have hcs : |∑ j, toReal (E.G 0 j) * u j| ≤ toReal ρ := by
    have := abs_dotProduct_le_norm₂_mul_norm₂ (fun j => toReal (E.G 0 j)) u
    have h2 : ‖fun j => toReal (E.G 0 j)‖₂ * ‖u‖₂ ≤ toReal ρ :=
      le_trans (mul_le_of_le_one_right (norm₂_nonneg _) hu) hρ'
    exact le_trans this h2
  rw [abs_le] at hcs
  -- the two ends, each rounded in the outward direction
  have he0 : toReal (E.err.inf 0) ≤ e 0 ∧ e 0 ≤ toReal (E.err.sup 0) := he 0
  have hy0 := hyu 0
  have h1 := addDown_le_add (subDown (E.q 0) ρ) (E.err.inf 0)
  have h2 := subDown_le_sub (E.q 0) ρ
  have h3 := add_le_addUp (addUp (E.q 0) ρ) (E.err.sup 0)
  have h4 := add_le_addUp (E.q 0) ρ
  set lo := toReal (addDown (subDown (E.q 0) ρ) (E.err.inf 0)) with hlo
  set hi := toReal (addUp (addUp (E.q 0) ρ) (E.err.sup 0)) with hhi
  have hl : lo ≤ (y + e) 0 := by
    simp only [Pi.add_apply]; linarith [he0.1]
  have hh : (y + e) 0 ≤ hi := by
    simp only [Pi.add_apply]; linarith [he0.2]
  -- both ends are vertices, and the point lies between them
  have ha : (fun _ => lo : Vec ℝ 1) ∈ {y | ∃ v ∈ E.vertices k, toRealVec v = y} :=
    ⟨_, List.mem_cons_self, rfl⟩
  have hb : (fun _ => hi : Vec ℝ 1) ∈ {y | ∃ v ∈ E.vertices k, toRealVec v = y} :=
    ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self), rfl⟩
  have hx : y + e = fun _ => (y + e) 0 := funext fun i => by rw [Fin.fin_one_eq_zero i]
  by_cases hlt : lo = hi
  · have : (y + e) 0 = lo := by linarith
    rw [hx, this]; exact subset_convexHull ℝ _ ha
  · have hlt : lo < hi := lt_of_le_of_ne (le_trans hl hh) hlt
    refine segment_subset_convexHull ha hb ?_
    refine ⟨(hi - (y + e) 0) / (hi - lo), ((y + e) 0 - lo) / (hi - lo), ?_, ?_, ?_, ?_⟩
    · exact div_nonneg (by linarith) (by linarith)
    · exact div_nonneg (by linarith) (by linarith)
    · field_simp; ring
    · funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Fin.fin_one_eq_zero i]
      field_simp; ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
