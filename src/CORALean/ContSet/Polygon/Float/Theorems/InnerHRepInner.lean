module

public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Polygon.Float.Operations.InnerHRep
public import CORALean.ContSet.Polygon.Float.Theorems.OrientBoundsLe
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# The edge halfspaces of `Polygon.innerHRep` lie inside the piece

A point `x` left of every edge `vᵢ → vᵢ₊₁` lies in a triangle of the fan from `v₀`. The
orientations `sᵢ = (vᵢ - v₀) × (x - v₀)` start nonnegative (`x` is left of the first edge) and
end nonpositive (it is left of the closing edge `vₖ₋₁ → v₀`), so some `i` has `sᵢ ≥ 0 ≥ sᵢ₊₁`;
with the edge `vᵢ → vᵢ₊₁` these are the three edge orientations of `x` in the triangle
`v₀ vᵢ vᵢ₊₁`, all nonnegative, and that triangle is certified counterclockwise, so they are
barycentric coordinates. No convex position is needed: for vertices out of convex position the
halfspaces cut out less, never more.

The certified checks read as reals: each stored edge difference equals the real one (rounded
down, and no larger rounded up), so the stored normal is the real one, and the stored bound is
at most `aᵀvᵢ`, so a point of the halfspace is left of the edge. The hull of the stored vertices
lies in the piece since its error box holds `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The orientation `(b - a) × (c - a)` of three real points of the plane. -/
def Polygon.aux_orient (a b c : Vec ℝ 2) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

/-- Three nonnegative edge orientations in a counterclockwise triangle are barycentric
coordinates, up to the triangle's orientation. -/
theorem Polygon.aux_barycentric {a b c x : Vec ℝ 2} (hD : 0 < Polygon.aux_orient a b c)
    (ha : 0 ≤ Polygon.aux_orient b c x) (hb : 0 ≤ Polygon.aux_orient c a x)
    (hc : 0 ≤ Polygon.aux_orient a b x) : -- --- STMT ---
    ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
      x = α • a + β • b + γ • c := by -- --- PROOF ---
  have hD0 : Polygon.aux_orient a b c ≠ 0 := ne_of_gt hD
  refine ⟨Polygon.aux_orient b c x / Polygon.aux_orient a b c,
    Polygon.aux_orient c a x / Polygon.aux_orient a b c,
    Polygon.aux_orient a b x / Polygon.aux_orient a b c,
    div_nonneg ha hD.le, div_nonneg hb hD.le, div_nonneg hc hD.le, ?_, ?_⟩
  · -- the three edge orientations add up to the triangle's
    field_simp
    simp only [Polygon.aux_orient]
    ring
  · -- and they combine the corners to the point, coordinate by coordinate
    simp only [Polygon.aux_orient] at hD0 ⊢
    funext i
    fin_cases i <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one] <;>
      field_simp <;> ring

/-- A sequence that starts nonnegative and ends nonpositive crosses over between neighbours. -/
theorem Polygon.aux_crossing (f : ℕ → ℝ) (N : ℕ) :
    ∀ d j, j + d + 1 = N → 0 ≤ f j → f N ≤ 0 →
      ∃ i, j ≤ i ∧ i + 1 ≤ N ∧ 0 ≤ f i ∧ f (i + 1) ≤ 0 := by -- --- PROOF ---
  intro d
  induction d with
  | zero =>
    intro j hj h0 hN
    exact ⟨j, le_rfl, by omega, h0, by rw [show j + 1 = N by omega]; exact hN⟩
  | succ d ih =>
    intro j hj h0 hN
    by_cases h1 : f (j + 1) ≤ 0
    · exact ⟨j, le_rfl, by omega, h0, h1⟩
    · obtain ⟨i, hi, hiN, hi0, hi1⟩ := ih (j + 1) (by omega) (le_of_lt (not_le.mp h1)) hN
      exact ⟨i, by omega, hiN, hi0, hi1⟩

/-- A point left of every edge of a loop whose fan from the first vertex turns left lies in a
fan triangle. -/
theorem Polygon.aux_fan {k : ℕ} (u : Fin k → Vec ℝ 2) (x : Vec ℝ 2) (hk : 3 ≤ k)
    (hfan : ∀ i : Fin k, i.val ≠ 0 → i.val + 1 ≠ k →
      0 < Polygon.aux_orient (u ⟨0, i.pos⟩) (u i) (u (finRotate k i)))
    (hedge : ∀ i : Fin k, 0 ≤ Polygon.aux_orient (u i) (u (finRotate k i)) x) : -- --- STMT ---
    ∃ a b c : Fin k, ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
      x = α • u a + β • u b + γ • u c := by -- --- PROOF ---
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  -- the loop read along `ℕ`, and its successor away from the last vertex
  let g : ℕ → Fin (m + 1) := fun n => ⟨min n m, by omega⟩
  have hsucc : ∀ n, n < m → finRotate (m + 1) (g n) = g (n + 1) := fun n hn => by
    apply Fin.ext
    rw [coe_finRotate_of_ne_last (fun h => by simp [g, Fin.ext_iff] at h; omega)]
    simp only [g]
    omega
  have hlast : finRotate (m + 1) (g m) = g 0 := by
    have : g m = Fin.last m := Fin.ext (by simp [g])
    rw [this, finRotate_last]
    rfl
  -- the fan orientations of `x`, nonnegative at the first edge, nonpositive at the last
  let s : ℕ → ℝ := fun n => Polygon.aux_orient (u (g 0)) (u (g n)) x
  have hs1 : 0 ≤ s 1 := by
    have := hedge (g 0)
    rwa [hsucc 0 (by omega)] at this
  have hsm : s m ≤ 0 := by
    have := hedge (g m)
    rw [hlast] at this
    simp only [s, Polygon.aux_orient] at this ⊢
    linarith
  obtain ⟨i, hi1, him, hsi, hsi1⟩ := Polygon.aux_crossing s m (m - 2) 1 (by omega) hs1 hsm
  -- the triangle `v₀ vᵢ vᵢ₊₁` holds `x`
  have hD := hfan (g i) (by simp [g]; omega) (by simp [g]; omega)
  have he := hedge (g i)
  rw [hsucc i (by omega)] at hD he
  have hD' : 0 < Polygon.aux_orient (u (g 0)) (u (g i)) (u (g (i + 1))) := by
    have : (⟨0, (g i).pos⟩ : Fin (m + 1)) = g 0 := Fin.ext (by simp [g])
    rwa [this] at hD
  have hb : 0 ≤ Polygon.aux_orient (u (g (i + 1))) (u (g 0)) x := by
    simp only [s, Polygon.aux_orient] at hsi1 ⊢
    linarith
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hx⟩ := Polygon.aux_barycentric hD' he hb hsi
  exact ⟨g 0, g i, g (i + 1), α, β, γ, hα, hβ, hγ, hsum, hx⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.innerHRep_inner {p : VPolytope (Vec 𝕋 2)} :
    ∀ H ∈ Polygon.innerHRep p,
      H.construct ⊆ p.construct := by -- --- PROOF ---
  intro H (h : Polygon.innerHRep p = some H)
  simp only [Polygon.innerHRep] at h
  split_ifs at h with hc
  obtain ⟨hk, hex, hfan, horig⟩ := hc
  cases h
  simp only [List.all_eq_true, List.mem_finRange, forall_const, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq] at hex hfan horig
  intro x hx
  obtain ⟨hle, -⟩ := (HPolytope.mem_construct_iff (HPolytope.errFree_of_origin rfl rfl rfl)).mp hx
  -- every stored edge difference is the real one
  have hd : ∀ i j, toReal (subDown (p.V (finRotate p.k i) j) (p.V i j))
      = toReal (p.V (finRotate p.k i) j) - toReal (p.V i j) := fun i j =>
    le_antisymm (subDown_le_sub _ _) ((sub_le_subUp _ _).trans (toReal_le_of_le (hex i j)))
  -- so `x` is left of every edge
  have hedge : ∀ i, 0 ≤ Polygon.aux_orient (toRealVec (p.V i))
      (toRealVec (p.V (finRotate p.k i))) x := by
    intro i
    have h1 := hle i
    have h2 := dotDown_le ![subDown (p.V (finRotate p.k i) 1) (p.V i 1),
      neg (subDown (p.V (finRotate p.k i) 0) (p.V i 0))] (p.V i)
    simp only [toRealMat, HPolytope.ineqs, mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, toReal_neg, hd] at h1 h2
    simp only [Polygon.aux_orient, toRealVec]
    linarith
  -- and in a fan triangle of the stored vertices, which the error box's origin keeps
  have hfan' : ∀ i : Fin p.k, i.val ≠ 0 → i.val + 1 ≠ p.k →
      0 < Polygon.aux_orient (toRealVec (p.V ⟨0, i.pos⟩)) (toRealVec (p.V i))
        (toRealVec (p.V (finRotate p.k i))) := fun i h0 h1 => by
    have hf := (hfan i).resolve_left (not_or.mpr ⟨h0, h1⟩)
    exact lt_of_lt_of_le (toReal_zero.symm.trans_lt (toReal_lt_of_ltStrict hf))
      (Polygon.orientBounds_le _ _ _).1
  obtain ⟨a, b, c, α, β, γ, hα, hβ, hγ, hsum, hxe⟩ :=
    Polygon.aux_fan (fun l => toRealVec (p.V l)) x hk hfan' hedge
  have h0 : (0 : Vec ℝ 2) ∈ p.I_error.construct := fun i =>
    ⟨(toReal_le_of_le (horig i).1).trans_eq toReal_zero,
      toReal_zero.symm.trans_le (toReal_le_of_le (horig i).2)⟩
  refine ⟨x, ?_, 0, h0, add_zero _⟩
  -- the weights, on the three corners
  let w : Fin p.k → ℝ := fun j =>
    (if j = a then α else 0) + (if j = b then β else 0) + (if j = c then γ else 0)
  refine ⟨w, fun j => ?_, ?_, ?_⟩
  · simp only [w]
    split_ifs <;> linarith
  · simp only [w, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hsum
  · rw [hxe]
    simp only [w, add_smul, ite_smul, zero_smul, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
