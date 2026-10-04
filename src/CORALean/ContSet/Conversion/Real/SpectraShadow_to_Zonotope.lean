import CORALean.ContSet.Conversion.Real.SpectraShadow_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope

/-!
# A spectrahedral shadow as a zonotope

CORA's `zonotope(SpS)`: the interval hull `I` of the base spectrahedron `{β | A₀ + Σ βᵢ Aᵢ ⪰ 0}`
(`spectraShadow(SpS.A)`, the shadow with `G = I` and `c = 0`), as a zonotope `Z`, and then
`G Z + c`. The image of a box that contains the base spectrahedron contains the shadow, and
nothing more is claimed: the shadow is generally not a zonotope, so this is an outer
approximation (`SpectraShadow.zonotope_contains`), for a bounded base. CORA's
`zonotope.empty` for an empty set is not needed for the statement: an empty shadow is in any
zonotope.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


/-- `spectraShadow(SpS.A)`: the base spectrahedron, in the space of the variables `β`. -/
def SpectraShadow.base (S : SpectraShadow α) : SpectraShadow (Vec ℝ S.m) :=
  ⟨S.k, S.m, S.A₀, S.A, 0, fun i => Pi.single i (1 : ℝ)⟩

/-- `G Z + c`, `Z` the box of the base spectrahedron as a zonotope. -/
noncomputable def SpectraShadow.zonotope (S : SpectraShadow α) : Zonotope α where
  h := S.m
  c := S.c + ∑ i, ((S.base.interval.inf i + S.base.interval.sup i) / 2) • S.G i
  G := fun j => ((S.base.interval.sup j - S.base.interval.inf j) / 2) • S.G j


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem SpectraShadow.aux_sum_single {m : ℕ} (γ : Fin m → ℝ) :
    (0 + ∑ i, γ i • (Pi.single i (1 : ℝ) : Vec ℝ m) : Vec ℝ m) = γ := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

omit [AddCommGroup α] [Module ℝ α] in
theorem SpectraShadow.aux_mem_base_iff (S : SpectraShadow α) (β : Vec ℝ S.m) :
    β ∈ S.base.construct ↔ (S.A₀ + ∑ i, β i • S.A i).PosSemidef := by -- --- PROOF ---
  constructor
  · rintro ⟨γ, hγ, hx⟩
    have hx' : β = γ := hx.trans (SpectraShadow.aux_sum_single (m := S.m) γ)
    rw [hx']
    exact hγ
  · intro h
    exact ⟨β, h, (SpectraShadow.aux_sum_single (m := S.m) β).symm⟩

/-- The coordinates of the zonotope of a box. -/
theorem Interval.aux_zonotope_coord {n : ℕ} (I : Interval (Vec ℝ n)) (γ : Fin n → ℝ) (i : Fin n) :
    (I.zonotope.c + ∑ j : Fin n, γ j • I.zonotope.G j) i
      = (I.inf i + I.sup i) / 2 + γ i * ((I.sup i - I.inf i) / 2) := by -- --- PROOF ---
  have hsum : (∑ j : Fin n, γ j • I.zonotope.G j) i = γ i * ((I.sup i - I.inf i) / 2) := by
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp [Interval.zonotope]
    · intro j _ hj
      simp [Interval.zonotope, Ne.symm hj]
    · intro hc
      exact absurd (Finset.mem_univ i) hc
  rw [Pi.add_apply, hsum]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.zonotope_contains (S : SpectraShadow α) (hb : S.base.isBounded) :
    S.construct ⊆ S.zonotope.construct := by -- --- PROOF ---
  -- a variable vector `β` of the shadow's point lies in the base spectrahedron
  rintro _ ⟨β, hβ, rfl⟩
  have hβb : β ∈ S.base.construct := (S.aux_mem_base_iff β).mpr hβ
  -- hence in its interval hull, which is the zonotope `I.zonotope`
  have hI := S.base.interval_contains hb hβb
  obtain ⟨γ, hγ, hγeq⟩ : ∃ γ : Fin S.m → ℝ, (∀ j, |γ j| ≤ 1)
      ∧ β = S.base.interval.zonotope.c + ∑ j, γ j • S.base.interval.zonotope.G j :=
    S.base.interval.zonotope_contains hI
  have hcoord : ∀ i, β i = (S.base.interval.inf i + S.base.interval.sup i) / 2
      + γ i * ((S.base.interval.sup i - S.base.interval.inf i) / 2) := fun i =>
    (congrFun hγeq i).trans (S.base.interval.aux_zonotope_coord γ i)
  -- the same coefficients `γ` generate the point, coordinate by coordinate
  refine ⟨γ, hγ, ?_⟩
  show S.c + ∑ i, β i • S.G i
    = S.c + ∑ i, ((S.base.interval.inf i + S.base.interval.sup i) / 2) • S.G i
      + ∑ j, γ j • (((S.base.interval.sup j - S.base.interval.inf j) / 2) • S.G j)
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hcoord i, add_smul, mul_smul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
