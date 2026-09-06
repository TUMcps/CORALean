import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
import CORALean.ContSet.ConZonotope.Real.ConZonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE

/-!
# A constrained zonotope as a constrained polynomial zonotope

Exact, and it is the interval right-hand side that makes it so. Our
`ConZonotope` carries an `HPolytope` over its coefficients, so it admits
inequalities, and with `A μ(α) ∈ b` an inequality is a row whose interval is
open at one end, with nothing added to `p`.

Open at one end is not something an interval can be, so a lower bound has to be
supplied — and one is free: every factor lies in `[-1,1]`, so a row cannot fall
below minus the sum of its absolute coefficients. That bound cuts nothing, which
is why the conversion is exact rather than enclosing.

The factors are the coefficients themselves, one each and to the first power, so
generators and constraint columns read off the same identity exponent matrix. A
constrained zonotope is exactly the linear fragment of the representation.

`aux_coeffs` is the converse of `HPolytope.rowLin`: a constraint there is a
functional, here a matrix row, and a functional is its values on the unit vectors.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The coefficients of a linear functional on a coordinate space. -/
def ConZonotope.aux_coeffs {h : ℕ} (f : Vec ℝ h →ₗ[ℝ] ℝ) : Vec ℝ h :=
  fun j => f (Pi.single j 1)

theorem ConZonotope.aux_apply_eq_sum {h : ℕ} (f : Vec ℝ h →ₗ[ℝ] ℝ) (β : Vec ℝ h) :
    f β = ∑ j, ConZonotope.aux_coeffs f j * β j := by -- --- PROOF ---
  have hsingle : ∀ j k : Fin h, (Pi.single j (1:ℝ) : Vec ℝ h) k = if k = j then 1 else 0 :=
    fun j k => Pi.single_apply j (1:ℝ) k
  have hβ : β = ∑ j, β j • (Pi.single j (1:ℝ) : Vec ℝ h) := by
    funext k
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · rw [Pi.smul_apply, smul_eq_mul, hsingle, if_pos rfl, mul_one]
    · intro j _ hj
      rw [Pi.smul_apply, smul_eq_mul, hsingle, if_neg (Ne.symm hj), mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  conv_lhs => rw [hβ]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [map_smul, smul_eq_mul, ConZonotope.aux_coeffs, mul_comm]

/-- What a row can reach over the unit cube, which is what the supplied lower
bound has to clear. -/
theorem ConZonotope.aux_abs_sum_le {h : ℕ} (c β : Vec ℝ h) (hβ : ∀ j, |β j| ≤ 1) :
    |∑ j, c j * β j| ≤ ∑ j, |c j| :=
  calc |∑ j, c j * β j| ≤ ∑ j, |c j * β j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |c j| := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hβ j)

/-- The inequality rows, then the equality rows, each read off as coefficients
over the coefficient space. -/
def ConZonotope.conA (C : ConZonotope (Vec ℝ n)) : Mat ℝ (C.P.m + C.P.me) C.h :=
  Fin.append (fun i => ConZonotope.aux_coeffs (C.P.A i))
    fun i => ConZonotope.aux_coeffs (C.P.Ae i)

/-- An inequality gets the free lower bound; an equality is the degenerate
interval. -/
def ConZonotope.conB (C : ConZonotope (Vec ℝ n)) : Interval (Vec ℝ (C.P.m + C.P.me)) :=
  ⟨Fin.append (fun i => -∑ j, |ConZonotope.aux_coeffs (C.P.A i) j|) C.P.be,
   Fin.append C.P.b C.P.be⟩

def ConZonotope.conPolyZono (C : ConZonotope (Vec ℝ n)) : ConPolyZono (Vec ℝ n) where
  p := C.h
  h := C.h
  q := 0
  m := C.P.m + C.P.me
  s := C.h
  c := C.c
  G := C.G
  E := PolyZonotope.identE C.h
  GI := Fin.elim0
  A := ConZonotope.conA C
  b := ConZonotope.conB C
  EC := PolyZonotope.identE C.h

-- identity exponents make the monomial vector the factor vector itself
theorem ConZonotope.aux_mulVec_conA (C : ConZonotope (Vec ℝ n)) (β : Vec ℝ C.h) :
    ∀ i, (ConZonotope.conA C *ᵥ PolyZonotope.monomial (PolyZonotope.identE C.h) β) i
      = (ConZonotope.conA C *ᵥ β) i := by -- --- PROOF ---
  have hm : PolyZonotope.monomial (PolyZonotope.identE C.h) β = β :=
    funext fun j => PolyZonotope.monomial_identE β j
  rw [hm]
  exact fun _ => rfl

/-- The constraint system says of the factors exactly what the coefficient
polytope said of the coefficients — the lower bounds being free. -/
theorem ConZonotope.satisfies_conPolyZono_iff (C : ConZonotope (Vec ℝ n)) (β : Vec ℝ C.h)
    (hβ : ∀ j, |β j| ≤ 1) :
    C.conPolyZono.satisfies β ↔ β ∈ C.P.construct := by -- --- PROOF ---
  have hlin : ∀ i : Fin C.P.m, (ConZonotope.conA C *ᵥ β) (Fin.castAdd C.P.me i)
      = C.P.A i β := by
    intro i
    show ∑ j, ConZonotope.conA C (Fin.castAdd C.P.me i) j * β j = _
    rw [ConZonotope.aux_apply_eq_sum (C.P.A i) β]
    exact Finset.sum_congr rfl fun j _ => by
      rw [ConZonotope.conA, Fin.append_left]
  have heq : ∀ i : Fin C.P.me, (ConZonotope.conA C *ᵥ β) (Fin.natAdd C.P.m i)
      = C.P.Ae i β := by
    intro i
    show ∑ j, ConZonotope.conA C (Fin.natAdd C.P.m i) j * β j = _
    rw [ConZonotope.aux_apply_eq_sum (C.P.Ae i) β]
    exact Finset.sum_congr rfl fun j _ => by
      rw [ConZonotope.conA, Fin.append_right]
  -- the free lower bound: no row falls below minus its own absolute row sum
  have hfree : ∀ i : Fin C.P.m,
      -∑ j, |ConZonotope.aux_coeffs (C.P.A i) j| ≤ C.P.A i β := by
    intro i
    rw [ConZonotope.aux_apply_eq_sum (C.P.A i) β]
    have h := ConZonotope.aux_abs_sum_le (ConZonotope.aux_coeffs (C.P.A i)) β hβ
    rw [abs_le] at h
    exact h.1
  constructor
  · intro hsat'
    have hsat : ConPolyZono.holds (ConZonotope.conA C) (ConZonotope.conB C)
        (PolyZonotope.identE C.h) β := hsat'
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have h := (hsat (Fin.castAdd C.P.me i)).2
      rw [ConZonotope.aux_mulVec_conA C β, hlin i] at h
      simpa only [ConZonotope.conB, Fin.append_left] using h
    · have h := hsat (Fin.natAdd C.P.m i)
      rw [ConZonotope.aux_mulVec_conA C β, heq i] at h
      simp only [ConZonotope.conB, Fin.append_right] at h
      exact le_antisymm h.2 h.1
  -- back: an inequality needs only its upper bound, an equality both ends at once
  · rintro ⟨hle, hE⟩
    show ConPolyZono.holds (ConZonotope.conA C) (ConZonotope.conB C)
      (PolyZonotope.identE C.h) β
    refine Fin.addCases (fun i => ?_) fun i => ?_ <;>
      rw [ConZonotope.aux_mulVec_conA C β]
    · rw [hlin i]
      simpa only [ConZonotope.conB, Fin.append_left] using ⟨hfree i, hle i⟩
    · rw [heq i]
      simp only [ConZonotope.conB, Fin.append_right]
      exact ⟨(hE i).ge, (hE i).le⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.conPolyZono_exact (C : ConZonotope (Vec ℝ n)) :
    C.construct = C.conPolyZono.construct := by -- --- PROOF ---
  have hvalue : ∀ β : Vec ℝ C.h,
      C.c + ∑ j, β j • C.G j
        = C.c + (∑ i, PolyZonotope.monomial (PolyZonotope.identE C.h) β i • C.G i)
          + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : Vec ℝ n) := by
    intro β
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      PolyZonotope.monomial_identE]
  -- and the point is unchanged, the independent block being empty
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨β, hβ, hP, rfl⟩
    exact ⟨β, fun _ => 0, hβ, fun j => j.elim0,
      (ConZonotope.satisfies_conPolyZono_iff C β hβ).mpr hP, hvalue β⟩
  · rintro _ ⟨β, γ, hβ, -, hsat, rfl⟩
    refine ⟨β, hβ, (ConZonotope.satisfies_conPolyZono_iff C β hβ).mp hsat, ?_⟩
    show C.c + (∑ i, PolyZonotope.monomial (PolyZonotope.identE C.h) β i • C.G i)
        + (∑ j : Fin 0, γ j • (Fin.elim0 j : Vec ℝ n))
      = C.c + ∑ j, β j • C.G j
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      PolyZonotope.monomial_identE]
    rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
