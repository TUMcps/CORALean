import CORALean.ContSet.PolyZonotope.Float.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
import CORALean.ContSet.Zonotope.Real.Theorems.Coefficient

/-!
# `dependent` empties the box without losing a point

Stated against the *nominal* set of the result rather than against its
`construct`, which is the whole point: the result's box is `[0, 0]`, so its
nominal set is everything it denotes, and a caller may treat it as an exact-layer
polynomial zonotope from here on.

The witness is `Fin.append a (Fin.append β γ)`: the old factors, the old
independent coefficients now dependent, and one coefficient per coordinate
placing that coordinate's error in its new generator. `coefficient` supplies the
last, and `errorBound` rounds nothing, so it always fits.

`dependent_outer` is the same statement read back through `ContSet`, for a
caller that only wants the inclusion.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem PolyZonotope.dependent_q (PZ : PolyZonotope 𝕋 n) : PZ.dependent.q = 0 := rfl

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `dependent`'s generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem PolyZonotope.aux_sum_univ_dependent {PZ : PolyZonotope 𝕋 n}
    (f : Fin (PZ.h + (PZ.q + n)) → ℝ) :
    ∑ l : Fin PZ.dependent.h, f l
      = ∑ l, f (Fin.castAdd (PZ.q + n) l) + ∑ l, f (Fin.natAdd PZ.h l) :=
  Fin.sum_univ_add f

/-- The result's box denotes the origin alone, so nothing is left outside its
nominal set. -/
theorem PolyZonotope.zero_mem_dependent_err (PZ : PolyZonotope 𝕋 n) :
    (0 : Vec ℝ n) ∈ (PZ.dependent.err).construct := fun i =>
  ⟨le_of_eq (by rw [PolyZonotope.dependent]; exact toReal_zero),
   le_of_eq (by rw [PolyZonotope.dependent]; exact toReal_zero.symm)⟩

/-- One generator per coordinate reaches every point of the box. -/
theorem PolyZonotope.abs_le_errorBound {I : Interval 𝕋 n} {e : Vec ℝ n}
    (he : e ∈ I.construct) (i : Fin n) : |e i| ≤ toReal (PolyZonotope.errorBound I i) := by
  have hlo : toReal (I.inf i) ≤ e i := (he i).1
  have hhi : e i ≤ toReal (I.sup i) := (he i).2
  have hmax : toReal (PolyZonotope.errorBound I i)
      = max |toReal (I.inf i)| |toReal (I.sup i)| := by
    rw [PolyZonotope.errorBound, toReal_maximum, toReal_absolute, toReal_absolute]
  rw [hmax, abs_le]
  constructor
  · exact le_trans (neg_le_neg (le_max_left _ _)) (le_trans (neg_abs_le _) hlo)
  · exact le_trans hhi (le_trans (le_abs_self _) (le_max_right _ _))

-- the error box is freed into `n` fresh factors, one per coordinate
theorem PolyZonotope.dependent_nominal (PZ : PolyZonotope 𝕋 n) :
    PZ.construct ⊆ nominalSet PZ.dependent := by
  rintro _ ⟨z, hz', e, he, rfl⟩
  obtain ⟨a, β, ha, hβ, hz⟩ := PolyZonotope.mem_nominalSet_iff.mp hz'
  have hbound : ∀ i, |e i| ≤ toReal (PolyZonotope.errorBound PZ.err i) :=
    fun i => PolyZonotope.abs_le_errorBound he i
  refine PolyZonotope.mem_nominalSet_iff.mpr
    ⟨Fin.append a (Fin.append β
        (fun i => Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound PZ.err i)) (e i))),
      Fin.elim0, ?_, fun j => j.elim0, fun i => ?_⟩
  · refine Fin.addCases (fun k => ?_) (Fin.addCases (fun j => ?_) (fun j => ?_))
    · simpa using ha k
    · simpa only [Fin.append_left, Fin.append_right] using hβ j
    · simp only [Fin.append_right]
      exact Real.Zonotope.abs_coefficient_le_one
        ((abs_nonneg _).trans (hbound j)) (hbound j)
  -- and the diagonal block reproduces `e` exactly, coordinate by coordinate
  · have hd : ∑ l, Matrix.diagonal (toRealVec (PolyZonotope.errorBound PZ.err)) i l
        * Real.Zonotope.coefficient (toReal (PolyZonotope.errorBound PZ.err l)) (e l)
          = e i := by
      rw [Real.Zonotope.sum_diagonal_mul]
      exact Real.Zonotope.mul_coefficient (hbound i)
    show z i + e i = _
    rw [PolyZonotope.aux_sum_univ_dependent]
    simp only [PolyZonotope.dependent, Real.PolyZonotope.monomial_plusE_left,
      Real.PolyZonotope.monomial_plusE_right, Real.PolyZonotope.monomial_identE,
      Fin.append_left, Fin.append_right, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, toReal_diagonalBlock]
    rw [hd, hz i]
    ring

theorem PolyZonotope.dependent_outer (PZ : PolyZonotope 𝕋 n) :
    PZ.construct ⊆ PZ.dependent.construct := fun x hx =>
  ⟨x, PolyZonotope.dependent_nominal PZ hx, 0,
    PolyZonotope.zero_mem_dependent_err PZ, add_zero x⟩

end CORALean.Float
