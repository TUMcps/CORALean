module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Contracting
public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# A perturbed image, inner-approximated by a fixed point

`Ē '' X` minus a set `B` covering what the perturbation moves, `Ē x - E x`, lies
inside `E '' X` once `x ↦ x - P (E x)` contracts, where `P` is an injective
additive left inverse of `Ē` (`Ē⁻¹` for a matrix). A point `y` of the difference
keeps `y + (Ē x - E x)` in `Ē '' X` for every `x ∈ X`, so `T x = P (y + Ē x - E x)`
maps `X` into itself; it is `P y + (x - P (E x))`, a contraction, and Banach's
theorem gives a fixed point, which is `y = E x`.

`X` need only be complete, not convex, and `E` need not be linear. The
contraction is what the missing convexity costs: for `X = {0, 1}`, `Ē = 1`,
`E = 2` and `B = {0, -1}`, `y = 1` is in the difference and not in `E '' X`,
at the contraction constant `1`. Convex closed images need no smallness at all
(`minkowskiDiff_image_subset_image_of_convex`).

`B` covers `Ē x - E x`, which for `E = Ē + Δ` is `-Δ x`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Function Set

variable {V W : Type} [NormedAddCommGroup V] [AddCommGroup W] [Module ℝ W]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Ē '' X ⊖ B ⊆ E '' X` when `B` covers `Ē x - E x` on `X`, `X` is complete and nonempty,
`P` is an injective additive left inverse of `Ē`, and `x ↦ x - P (E x)` is `K`-Lipschitz
with `K < 1`. -/
theorem minkowskiDiff_image_subset_image_of_contracting (P : W →+ V) (hP : Injective P)
    (Ē E : V → W) (hĒ : ∀ x, P (Ē x) = x) {K : NNReal} (hK : K < 1)
    (hLip : LipschitzWith K fun x => x - P (E x)) {X : Set V} (hX : IsComplete X)
    (hXne : X.Nonempty) {B : Set W} (hB : ∀ x ∈ X, Ē x - E x ∈ B) : -- --- STMT ---
    minkowskiDiff (Ē '' X) B ⊆ E '' X := by -- --- PROOF ---
  intro y hy
  -- the map whose fixed points solve `y = E x`
  set T : V → V := fun x => P (y + (Ē x - E x)) with hTdef
  have hT : ∀ x, T x = P y + (x - P (E x)) := fun x => by
    show P (y + (Ē x - E x)) = _
    rw [map_add, map_sub, hĒ]
  -- `y + (Ē x - E x)` is `Ē x'` for some `x' ∈ X`, and `P` takes it back to `x'`
  have hmaps : MapsTo T X X := by
    intro x hx
    obtain ⟨x', hx', hx'eq⟩ := hy _ (hB x hx)
    show P (y + (Ē x - E x)) ∈ X
    rw [← hx'eq, hĒ]
    exact hx'
  -- translating by `P y` keeps the Lipschitz constant
  have hcon : ContractingWith K (hmaps.restrict T X X) := by
    refine ⟨hK, fun a b => ?_⟩
    show edist (T a) (T b) ≤ K * edist (a : V) b
    have h := hLip a b
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm] at h
    rw [hT, hT, edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub]
    exact h
  obtain ⟨x₀, hx₀⟩ := hXne
  obtain ⟨x, hx, hfix, -⟩ := hcon.exists_fixedPoint' hX hmaps hx₀ (edist_ne_top _ _)
  refine ⟨x, hx, hP ?_⟩
  -- `P y + (x - P (E x)) = x` leaves `P (E x) = P y`
  have h : T x = x := hfix
  rw [hT] at h
  calc P (E x) = P y - (P y + (x - P (E x)) - x) := by abel
    _ = P y := by rw [h, sub_self, sub_zero]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
