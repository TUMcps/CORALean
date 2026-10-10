import CORALean.ContSet.ContSet.Definitions.IsFullDim
import CORALean.ContSet.Polygon.Float.Operations.IsFullDim
import CORALean.ContSet.Polygon.Float.Theorems.OrientBoundsLe
import CORALean.ContSet.VPolytope.Real.Theorems.IsFullDimIff
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# A `true` from `Polygon.isFullDim` proves an interior point

The certified cross product (`Polygon.orientBounds_le`), read as reals, is the determinant of
`(b - a, c - a)`, so these two differences span the plane (Cramer's rule), the vertices' affine
span is everything, and the nominal piece has an interior point
(`CORALean.Real.VPolytope.isFullDim_iff`). The piece's error box holds its lower corner, which
moves that point into the piece, and the piece into the region.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Three points of the plane with a nonzero cross product span it affinely. -/
theorem Polygon.aux_affineSpan_eq_top {k : ℕ} (V : Fin k → Vec ℝ 2) (a b c : Fin k)
    (hD : (V b 0 - V a 0) * (V c 1 - V a 1) - (V b 1 - V a 1) * (V c 0 - V a 0) ≠ 0) :
    affineSpan ℝ (Set.range V) = ⊤ := by -- --- PROOF ---
  set u : Vec ℝ 2 := V b - V a
  set w : Vec ℝ 2 := V c - V a
  set D := u 0 * w 1 - u 1 * w 0
  have hD' : D ≠ 0 := by simpa [D, u, w] using hD
  -- both differences lie in the direction of the span
  have hu : u ∈ vectorSpan ℝ (Set.range V) := vsub_mem_vectorSpan ℝ ⟨b, rfl⟩ ⟨a, rfl⟩
  have hw : w ∈ vectorSpan ℝ (Set.range V) := vsub_mem_vectorSpan ℝ ⟨c, rfl⟩ ⟨a, rfl⟩
  -- every point is a combination of them, by Cramer's rule
  have htop : vectorSpan ℝ (Set.range V) = ⊤ := by
    refine (Submodule.eq_top_iff').mpr fun x => ?_
    have hx : x = ((x 0 * w 1 - x 1 * w 0) / D) • u + ((u 0 * x 1 - u 1 * x 0) / D) • w := by
      funext i
      fin_cases i <;> simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> field_simp <;> ring
    rw [hx]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hw)
  rw [← AffineSubspace.direction_eq_top_iff_of_nonempty
    ((affineSpan_nonempty (k := ℝ) (s := Set.range V)).mpr ⟨V a, a, rfl⟩), direction_affineSpan]
  exact htop

/-- The certified cross product is the real one, so it is not zero. -/
theorem Polygon.aux_cross_ne_zero {p : VPolytope 𝕋 2} {a b c : Fin p.k}
    (h : Polygon.crossCertified p a b c = true) :
    (toReal (p.V b 0) - toReal (p.V a 0)) * (toReal (p.V c 1) - toReal (p.V a 1))
      - (toReal (p.V b 1) - toReal (p.V a 1)) * (toReal (p.V c 0) - toReal (p.V a 0))
      ≠ 0 := by -- --- PROOF ---
  simp only [Polygon.crossCertified, Bool.or_eq_true] at h
  have hb := Polygon.orientBounds_le (p.V a) (p.V b) (p.V c)
  -- one certified side of zero, read as reals
  rcases h with h | h
  · have := toReal_lt_of_ltStrict h
    rw [toReal_zero] at this
    exact ne_of_gt (lt_of_lt_of_le this hb.1)
  · have := toReal_lt_of_ltStrict h
    rw [toReal_zero] at this
    exact ne_of_lt (lt_of_le_of_lt hb.2 this)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.isFullDim_sound {P : Polygon 𝕋} (h : Polygon.isFullDim P = true) :
    ContSet.IsFullDim P := by -- --- PROOF ---
  simp only [Polygon.isFullDim, List.any_eq_true, Bool.and_eq_true, List.all_eq_true,
    List.mem_finRange, true_and, forall_const] at h
  obtain ⟨p, hp, hbox, a, b, c, hc⟩ := h
  -- the nominal piece has an interior point
  have hspan := Polygon.aux_affineSpan_eq_top (fun l i => toReal (p.V l i)) a b c
    (Polygon.aux_cross_ne_zero hc)
  obtain ⟨x, hx⟩ := (CORALean.Real.VPolytope.isFullDim_iff (nominal p)).mpr hspan
  -- moved by the box's lower corner, it is interior to the piece, so to the region
  have he : (fun i => toReal (p.E.inf i)) ∈ p.E.construct := fun i =>
    ⟨le_refl _, toReal_le_of_le (hbox i)⟩
  have hin : x + (fun i => toReal (p.E.inf i)) ∈ interior (VPolytope.construct p) :=
    subset_interior_add_left (Set.add_mem_add hx he)
  refine ⟨_, interior_mono (fun y hy => ?_) hin⟩
  exact SetUnion.mem_construct.mpr ⟨p, hp, hy⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
