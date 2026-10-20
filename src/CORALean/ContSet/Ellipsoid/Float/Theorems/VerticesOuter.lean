module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Vertices
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AbsSubLeBoxRadius

@[expose] public section

/-!
# A one-dimensional float ellipsoid lies in the hull of its vertices

`x = y + e` with `|y - q| ≤ ρ` (`abs_sub_le_boxRadius`) and `e` in the error box: so `x` is
between the two rounded ends, which is a point of the segment joining them. Outer only.

## Inputs
* `k` – Newton steps of the root
* `E` – one-dimensional ellipsoid

## Hypotheses
* none

## Conclusion
* `E` lies in the convex hull of its vertices
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.vertices_outer (k : ℕ) (E : Ellipsoid 𝕋 1) : -- --- CONCL ---
    E.construct ⊆ convexHull ℝ {y | ∃ v ∈ E.vertices k, toRealVec v = y} := by -- --- PROOF ---
  rintro _ ⟨y, hy, e, he, rfl⟩
  show y + e ∈ _
  -- the nominal point is within the rounded-up half-width of the center
  set ρ := Ellipsoid.boxRadius k E 0 with hρ
  have hcs := abs_le.mp (Ellipsoid.abs_sub_le_boxRadius hy k 0)
  -- the two ends, each rounded in the outward direction
  have he0 : toReal (E.I_error.inf 0) ≤ e 0 ∧ e 0 ≤ toReal (E.I_error.sup 0) := he 0
  have h1 := addDown_le_add (subDown (E.q 0) ρ) (E.I_error.inf 0)
  have h2 := subDown_le_sub (E.q 0) ρ
  have h3 := add_le_addUp (addUp (E.q 0) ρ) (E.I_error.sup 0)
  have h4 := add_le_addUp (E.q 0) ρ
  set lo := toReal (addDown (subDown (E.q 0) ρ) (E.I_error.inf 0)) with hlo
  set hi := toReal (addUp (addUp (E.q 0) ρ) (E.I_error.sup 0)) with hhi
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
