module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialPadE
public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEqUnit
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialIdentE
public import CORALean.ContSet.Interval.Real.Operations.Point
public import CORALean.Global.EuclideanNorm
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_ConPolyZono
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq

@[expose] public section

/-!
# An ellipsoid's factor form as a constrained polynomial zonotope

The construction is [1, Prop. 3] for any square factor `G` of the shape matrix: `G`'s own columns
are the CPZ's dependent generators, read exactly as `G *ᵥ u` reads them. [1] takes `G = V √Λ`
from the eigendecomposition `Q = VΛVᵀ`; any factor would do (`construct_eq_of_factor`).

What is left is [1]'s actual device: one further factor absorbs the unit
ball's `‖u‖₂ ≤ 1` into a single polynomial equality
`-0.5 α_{k+1} + α_1² + ⋯ + α_k² = 0.5`, since `α_{k+1} ∈ [-1,1]` ranges exactly
over the slack the inequality leaves. Exact, both directions.

## Inputs
* `G` – factor matrix
* `q` – center

## Hypotheses
* none

## Conclusion
* constrained polynomial zonotope of the factor is the image of the unit ball

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       12-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `G u` read as a generator sum over the columns of `G`. -/
theorem Ellipsoid.aux_mulVec_eq_sum {m q : ℕ} (G : Mat ℝ m q) (u : Vec ℝ q) :
    G *ᵥ u = ∑ l, u l • ConPolyZono.consCol G l := by
  funext i
  show (∑ l, G i l * u l) = (∑ l, u l • ConPolyZono.consCol G l) i
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- A diagonal exponent matrix's monomial is its one nonzero factor, to the
diagonal's own power. -/
theorem Ellipsoid.aux_monomial_conPolyZonoR {k : ℕ} (a : Fin (k + 1) → ℝ)
    (j : Fin (k + 1)) : -- --- CONCL ---
    PolyZonotope.monomial (Ellipsoid.conPolyZonoR k) a j
      = a j ^ (if j.val < k then 2 else 1) := by -- --- PROOF ---
  rw [PolyZonotope.monomial, Finset.prod_eq_single j]
  · rw [Ellipsoid.conPolyZonoR, if_pos rfl]
  · intro r _ hrj
    rw [Ellipsoid.conPolyZonoR, if_neg hrj, pow_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h


-- =======================================  MAIN THEOREM  ======================================= --

/-- The CPZ of a factor `G` is the set `{q + G u | ‖u‖₂ ≤ 1}`, both directions. -/
theorem Ellipsoid.conPolyZonoOfFactor_construct (G : Mat ℝ n n) (q : Vec ℝ n) : -- --- CONCL ---
    {x | ∃ u : Vec ℝ n, ‖u‖₂ ≤ 1 ∧ x = q + G *ᵥ u} =
      (Ellipsoid.conPolyZonoOfFactor G q).construct := by -- --- PROOF ---
  set P := Ellipsoid.conPolyZonoOfFactor G q with hP
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨u, hu, rfl⟩
    have hsumsq : ∑ i, u i ^ 2 ≤ 1 := by
      rw [← norm₂_sq, pow_two]
      calc ‖u‖₂ * ‖u‖₂ ≤ 1 * 1 := mul_le_mul hu hu (norm₂_nonneg u) zero_le_one
        _ = 1 := one_mul 1
    set t : ℝ := 2 * ‖u‖₂ ^ 2 - 1 with ht
    have htbound : |t| ≤ 1 := by
      rw [ht, abs_le]
      refine ⟨by nlinarith [sq_nonneg ‖u‖₂], by nlinarith [norm₂_sq u, hsumsq]⟩
    refine ⟨Fin.append u fun _ : Fin 1 => t, Fin.elim0, fun j => j.elim0,
      (PolyLevelSet.mem_construct_iff_of_eq_unit P.cons_eq P.cons_dom).mpr ⟨Fin.addCases
        (fun i => by simpa [Fin.append_left] using le_trans (abs_le_norm₂ u i) hu)
        (fun j => by simpa [Fin.append_right] using htbound), ?_⟩, ?_⟩
    · -- the ball's radius equation, read as `Σ u_i² - 0.5 t = 0.5`
      intro i
      have heqn : (P.cons.A *ᵥ
          PolyZonotope.monomial P.cons.R (Fin.append u fun _ : Fin 1 => t)) i
            = (1 / 2 : ℝ) := by
        show (∑ j : Fin (n + 1), P.cons.A i j *
            PolyZonotope.monomial P.cons.R (Fin.append u fun _ : Fin 1 => t) j)
          = (1 / 2 : ℝ)
        rw [Fin.sum_univ_add]
        -- each square term contributes `u_k²`, read off `P.cons.A` and the diagonal `R`
        have hleft : ∀ k : Fin n, P.cons.A i (Fin.castAdd 1 k) *
            PolyZonotope.monomial P.cons.R (Fin.append u fun _ : Fin 1 => t)
              (Fin.castAdd 1 k) = u k ^ 2 := by
          intro k
          have h1 : P.cons.A i (Fin.castAdd 1 k) = 1 := by
            show (if (Fin.castAdd 1 k).val < n then (1:ℝ) else -(1/2)) = 1
            rw [if_pos (by simp)]
          have h2 : PolyZonotope.monomial P.cons.R
              (Fin.append u fun _ : Fin 1 => t) (Fin.castAdd 1 k) = u k ^ 2 := by
            show PolyZonotope.monomial (Ellipsoid.conPolyZonoR n)
                (Fin.append u fun _ : Fin 1 => t) (Fin.castAdd 1 k) = u k ^ 2
            rw [Ellipsoid.aux_monomial_conPolyZonoR,
              if_pos (show (Fin.castAdd 1 k).val < n by simp),
              Fin.append_left]
          rw [h1, h2, one_mul]
        -- the one slack term contributes `-0.5 t`
        have hright : ∀ l : Fin 1, P.cons.A i (Fin.natAdd n l) *
            PolyZonotope.monomial P.cons.R (Fin.append u fun _ : Fin 1 => t)
              (Fin.natAdd n l) = -(1 / 2) * t := by
          intro l
          have hval : ¬ (Fin.natAdd n l).val < n := by simp
          have h1 : P.cons.A i (Fin.natAdd n l) = -(1 / 2) := by
            show (if (Fin.natAdd n l).val < n then (1:ℝ) else -(1/2)) = -(1/2)
            rw [if_neg hval]
          have h2 : PolyZonotope.monomial P.cons.R
              (Fin.append u fun _ : Fin 1 => t) (Fin.natAdd n l) = t := by
            show PolyZonotope.monomial (Ellipsoid.conPolyZonoR n)
                (Fin.append u fun _ : Fin 1 => t) (Fin.natAdd n l) = t
            rw [Ellipsoid.aux_monomial_conPolyZonoR, if_neg hval, pow_one, Fin.append_right]
          rw [h1, h2]
        -- `Σ u_k² - 0.5 t = 0.5` since `t = 2‖u‖₂² - 1` and `‖u‖₂² = Σ u_k²`
        rw [Finset.sum_congr rfl fun k _ => hleft k, Finset.sum_congr rfl fun l _ => hright l,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, ht]
        rw [← norm₂_sq]
        ring
      rw [heqn]
      rfl
    · -- the point equation: `qI + Gu` read back as the CPZ's own generator sum
      show q + G *ᵥ u
          = P.c + ∑ i, PolyZonotope.monomial P.E
              (Fin.append u fun _ : Fin 1 => t) i • P.G i
            + ∑ j : Fin 0, (Fin.elim0 j : ℝ) • (Fin.elim0 j : Vec ℝ n)
      have hmono : ∀ i : Fin n, PolyZonotope.monomial P.E
          (Fin.append u fun _ : Fin 1 => t) i = u i := by
        intro i
        show PolyZonotope.monomial (ConPolyZono.padE (PolyZonotope.identE n) 1)
            (Fin.append u fun _ : Fin 1 => t) i = u i
        rw [ConPolyZono.monomial_padE, PolyZonotope.monomial_identE, Fin.append_left]
      rw [Finset.sum_congr rfl fun i _ => by rw [hmono i]]
      show q + G *ᵥ u = q + ∑ i, u i • ConPolyZono.consCol G i + 0
      rw [add_zero, ← Ellipsoid.aux_mulVec_eq_sum]
  -- back: the constraint pins `u`'s square-sum, and the generator sum reads off `G` again
  · rintro x ⟨a, β, _, hsat, rfl⟩
    have ha := ((PolyLevelSet.mem_construct_iff_of_eq_unit P.cons_eq P.cons_dom).mp hsat).1
    set u : Vec ℝ n := fun i => a (Fin.castAdd 1 i) with hu
    have i0 : Fin P.cons.m := ⟨0, Nat.one_pos⟩
    have hR : ∀ j : Fin (n + 1), PolyZonotope.monomial P.cons.R a j
        = a j ^ (if j.val < n then 2 else 1) :=
      Ellipsoid.aux_monomial_conPolyZonoR a
    -- the constraint read back as `Σ u_k² - 0.5 a(last) = 0.5`
    have heqn : (∑ k, u k ^ 2) - (1 / 2) * a (Fin.natAdd n (0 : Fin 1)) = (1 / 2 : ℝ) := by
      have hval : (P.cons.A *ᵥ PolyZonotope.monomial P.cons.R a) i0
          = (1 / 2 : ℝ) := ((PolyLevelSet.mem_construct_iff_of_eq P.cons_eq).mp hsat).2 i0
      have hexpand : (P.cons.A *ᵥ PolyZonotope.monomial P.cons.R a) i0
          = (∑ k, u k ^ 2) - (1 / 2) * a (Fin.natAdd n (0 : Fin 1)) := by
        show (∑ j : Fin (n + 1), P.cons.A i0 j *
            PolyZonotope.monomial P.cons.R a j)
          = (∑ k, u k ^ 2) - (1 / 2) * a (Fin.natAdd n (0 : Fin 1))
        rw [Fin.sum_univ_add]
        -- the square terms, `P.cons.A`'s first block against `R`'s diagonal
        have hleft : ∀ k : Fin n, P.cons.A i0 (Fin.castAdd 1 k) *
            PolyZonotope.monomial P.cons.R a (Fin.castAdd 1 k) = u k ^ 2 := by
          intro k
          have h1 : P.cons.A i0 (Fin.castAdd 1 k) = 1 := by
            show (if (Fin.castAdd 1 k).val < n then (1:ℝ) else -(1/2)) = 1
            rw [if_pos (by simp)]
          have h2 : PolyZonotope.monomial P.cons.R a (Fin.castAdd 1 k) = u k ^ 2 := by
            rw [hR, if_pos (show (Fin.castAdd 1 k).val < n by simp)]
          rw [h1, h2, one_mul]
        -- the one slack term
        have hright : ∀ l : Fin 1, P.cons.A i0 (Fin.natAdd n l) *
            PolyZonotope.monomial P.cons.R a (Fin.natAdd n l)
              = -(1 / 2) * a (Fin.natAdd n (0 : Fin 1)) := by
          intro l
          have hl0 : l = (0 : Fin 1) := Subsingleton.elim l 0
          have hval2 : ¬ (Fin.natAdd n l).val < n := by simp
          have h1 : P.cons.A i0 (Fin.natAdd n l) = -(1 / 2) := by
            show (if (Fin.natAdd n l).val < n then (1:ℝ) else -(1/2)) = -(1/2)
            rw [if_neg hval2]
          have h2 : PolyZonotope.monomial P.cons.R a (Fin.natAdd n l)
              = a (Fin.natAdd n (0 : Fin 1)) := by
            rw [hR, if_neg hval2, pow_one, hl0]
          rw [h1, h2]
        rw [Finset.sum_congr rfl fun k _ => hleft k, Finset.sum_congr rfl fun l _ => hright l,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
        ring
      rw [← hexpand, hval]
    -- `a(last) ≤ 1` bounds `Σ u_k²` at `1`, which bounds `‖u‖₂` at `1`
    have hu1 : |a (Fin.natAdd n (0 : Fin 1))| ≤ 1 := ha _
    have hnsq : ∑ k, u k ^ 2 ≤ 1 := by
      have := (abs_le.mp hu1).2
      linarith [heqn]
    have hnorm : ‖u‖₂ ≤ 1 := by
      show Real.sqrt (∑ k, u k ^ 2) ≤ 1
      calc Real.sqrt (∑ k, u k ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hnsq
        _ = 1 := Real.sqrt_one
    refine ⟨u, hnorm, ?_⟩
    -- and `u`'s own point is `G *ᵥ u`, read off the generator sum the same way as forward
    have hmono : ∀ i : Fin n, PolyZonotope.monomial P.E a i = u i := by
      intro i
      show PolyZonotope.monomial (ConPolyZono.padE (PolyZonotope.identE n) 1) a i = u i
      rw [ConPolyZono.monomial_padE, PolyZonotope.monomial_identE]
    show P.c + ∑ i, PolyZonotope.monomial P.E a i • P.G i
        + ∑ j : Fin 0, β j • P.GI j
      = q + G *ᵥ u
    rw [Finset.sum_congr rfl fun i _ => by rw [hmono i]]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    show q + ∑ i, u i • ConPolyZono.consCol G i = q + G *ᵥ u
    rw [Ellipsoid.aux_mulVec_eq_sum]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
