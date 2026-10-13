module

public import CORALean.ContSet.Zonotope.Real.Operations.QuadTaylor
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# `quadTaylor` encloses the second-order Taylor sum of every matrix a zonotope denotes

[1, Prop. 3]: `{I + At + ½(At)² | A ∈ A_Z}` is enclosed by `quadTaylor`'s explicit matrix
zonotope. `aux_quadTaylor_sq` is `A`'s own square expanded — `(c + Σ p i • G i)²` — via
`Finset.sum_mul_sum`/`smul_mul_smul_comm`, `bilin_outer`'s own cross-block combinatorics.
`aux_quadTaylor_diagpair` folds that expansion's diagonal and its `i ≠ j` half together into a
single generator per unordered pair, and `aux_quadTaylor_diagfold` folds `p i²` into `q i := 2(p
i)² - 1` and a constant half that joins the centre — both exactly what [1]'s own proof does to
the same expansion. The witness is `A`'s own coefficients `p`, plus `q` on the diagonal block
and `p i * p j` on the pair block — [1]'s printed `L^(0)`, `L^(j)` and `L^(2κ+l)` are double
these, a real erratum the page's own `## Findings` records and these coefficients do not repeat.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `(c + Σ p i • G i)²` expanded: the constant part, the linear-cross part sharing `p i` with
the linear term, and the pair part at every ordered `(i, j)`. -/
theorem Zonotope.aux_quadTaylor_sq {n h : ℕ} (c : Mat ℝ n n) (G : Fin h → Mat ℝ n n)
    (p : Fin h → ℝ) :
    (c + ∑ i, p i • G i) * (c + ∑ i, p i • G i)
      = c * c + (∑ i, p i • (c * G i + G i * c))
        + ∑ i, ∑ j, (p i * p j) • (G i * G j) := by -- --- PROOF ---
  have hL : c * (∑ i, p i • G i) = ∑ i, p i • (c * G i) :=
    (Finset.mul_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _)
  have hR : (∑ i, p i • G i) * c = ∑ i, p i • (G i * c) :=
    (Finset.sum_mul _ _ _).trans (Finset.sum_congr rfl fun i _ => smul_mul_assoc _ _ _)
  have hLR : c * (∑ i, p i • G i) + (∑ i, p i • G i) * c = ∑ i, p i • (c * G i + G i * c) := by
    rw [hL, hR, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (smul_add _ _ _).symm
  have hM : (∑ i, p i • G i) * (∑ j, p j • G j) = ∑ i, ∑ j, (p i * p j) • (G i * G j) :=
    (Finset.sum_mul_sum _ _ _ _).trans (Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => smul_mul_smul_comm _ _ _ _)
  have hkey : (c + ∑ i, p i • G i) * (c + ∑ i, p i • G i)
      = c * c + (c * (∑ i, p i • G i) + (∑ i, p i • G i) * c)
        + (∑ i, p i • G i) * (∑ j, p j • G j) := by
    rw [add_mul, mul_add, mul_add]; abel
  rw [hkey, hLR, hM]

/-- The linear-cross block, in aggregate: `t` and `½t²` pulled out of the sum over `i`. -/
theorem Zonotope.aux_quadTaylor_lin {n h : ℕ} (c : Mat ℝ n n) (G : Fin h → Mat ℝ n n)
    (p : Fin h → ℝ) (t : ℝ) :
    ∑ i, p i • (t • G i + (t ^ 2 / 2) • (c * G i + G i * c))
      = t • (∑ i, p i • G i)
        + (t ^ 2 / 2) • ∑ i, p i • (c * G i + G i * c) := by -- --- PROOF ---
  have step : ∀ i, p i • (t • G i + (t ^ 2 / 2) • (c * G i + G i * c))
      = t • (p i • G i) + (t ^ 2 / 2) • (p i • (c * G i + G i * c)) := fun i => by
    rw [smul_add, smul_smul, smul_smul, mul_comm (p i) t, mul_comm (p i) (t ^ 2 / 2),
      ← smul_smul, ← smul_smul]
  rw [Finset.sum_congr rfl fun i _ => step i, Finset.sum_add_distrib, Finset.smul_sum,
    Finset.smul_sum]

/-- The full pair sum splits into the diagonal and a single generator per *unordered* pair:
swapping `(i, j)` is a bijection of `Fin h × Fin h`, so the `i > j` half of the off-diagonal
reads exactly as the `i < j` half with its factors swapped. -/
theorem Zonotope.aux_quadTaylor_diagpair {n h : ℕ} (G : Fin h → Mat ℝ n n) (p : Fin h → ℝ) :
    ∑ i, ∑ j, (p i * p j) • (G i * G j)
      = ∑ i, (p i * p i) • (G i * G i)
        + ∑ i, ∑ j,
            (if i < j then (p i * p j) • (G i * G j + G j * G i) else 0) := by -- --- PROOF ---
  -- the `i > j` half, read back through the swap that took it to `i < j`
  have hswap : ∑ i : Fin h, ∑ j, (if i < j then (p i * p j) • (G j * G i) else 0)
      = ∑ i : Fin h, ∑ j, (if j < i then (p i * p j) • (G i * G j) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (p j) (p i)]
  have hite : ∀ i j : Fin h, (if i < j then (p i * p j) • (G i * G j + G j * G i) else 0)
      = (if i < j then (p i * p j) • (G i * G j) else 0)
        + (if i < j then (p i * p j) • (G j * G i) else 0) := fun i j => by
    split_ifs with h
    · rw [smul_add]
    · rw [add_zero]
  simp only [hite, Finset.sum_add_distrib, hswap]
  -- every `(i, j)` is diagonal, `i < j`, or `i > j`, exactly once
  have hdiag : ∀ i j : Fin h, (p i * p j) • (G i * G j)
      = (if i = j then (p i * p j) • (G i * G j) else 0)
        + (if i < j then (p i * p j) • (G i * G j) else 0)
        + (if j < i then (p i * p j) • (G i * G j) else 0) := fun i j => by
    rcases lt_trichotomy i j with h | h | h
    · rw [if_neg h.ne, if_pos h, if_neg (asymm h)]; abel
    · subst h; rw [if_pos rfl, if_neg (lt_irrefl i)]; abel
    · rw [if_neg h.ne', if_neg (asymm h), if_pos h]; abel
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hdiag i j]
  simp only [Finset.sum_add_distrib]
  -- the diagonal collapses to a single sum over `i`, `j = i` the only survivor
  rw [show (∑ i : Fin h, ∑ j, (if i = j then (p i * p j) • (G i * G j) else 0))
      = ∑ i, (p i * p i) • (G i * G i) from
    Finset.sum_congr rfl fun i _ =>
      (Finset.sum_eq_single i (fun j _ hj => if_neg (Ne.symm hj))
        (fun h => absurd (Finset.mem_univ i) h)).trans (if_pos rfl)]
  abel

/-- The diagonal sum, folded: `p i * p i` is read as `(1 + (2(p i)² - 1)) / 2`, the constant
half going into the centre and the rest onto the diagonal block's own generator. -/
theorem Zonotope.aux_quadTaylor_diagfold {n h : ℕ} (G : Fin h → Mat ℝ n n) (p : Fin h → ℝ)
    (t : ℝ) :
    (t ^ 2 / 2) • ∑ i, (p i * p i) • (G i * G i)
      = (t ^ 2 / 4) • ∑ i, G i * G i
        + ∑ i, (2 * (p i) ^ 2 - 1) • ((t ^ 2 / 4) • (G i * G i)) := by -- --- PROOF ---
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, smul_smul, ← add_smul]
  congr 1
  ring

/-- The pair block, reindexed from `Fin (h * h)` to `Fin h × Fin h` via `finProdFinEquiv`; the
`i < j` guard survives the reindex unchanged, so nothing here needs `aux_quadTaylor_diagpair`'s
own swap argument again. -/
theorem Zonotope.aux_quadTaylor_pairblock {n h : ℕ} (G : Fin h → Mat ℝ n n) (p : Fin h → ℝ)
    (t : ℝ) :
    ∑ k, (p (finProdFinEquiv.symm k).1 * p (finProdFinEquiv.symm k).2) •
        (if (finProdFinEquiv.symm k).1 < (finProdFinEquiv.symm k).2 then
            (t ^ 2 / 2) • (G (finProdFinEquiv.symm k).1 * G (finProdFinEquiv.symm k).2
              + G (finProdFinEquiv.symm k).2 * G (finProdFinEquiv.symm k).1)
          else 0)
      = (t ^ 2 / 2) • ∑ i, ∑ j,
          (if i < j then (p i * p j) • (G i * G j + G j * G i) else 0) := by -- --- PROOF ---
  -- pull the shared `t²/2` in front, leaving a plain reindex to do
  have hstep : ∀ k : Fin (h * h),
      (p (finProdFinEquiv.symm k).1 * p (finProdFinEquiv.symm k).2) •
          (if (finProdFinEquiv.symm k).1 < (finProdFinEquiv.symm k).2 then
              (t ^ 2 / 2) • (G (finProdFinEquiv.symm k).1 * G (finProdFinEquiv.symm k).2
                + G (finProdFinEquiv.symm k).2 * G (finProdFinEquiv.symm k).1)
            else 0)
        = (t ^ 2 / 2) • (if (finProdFinEquiv.symm k).1 < (finProdFinEquiv.symm k).2 then
              (p (finProdFinEquiv.symm k).1 * p (finProdFinEquiv.symm k).2) •
                (G (finProdFinEquiv.symm k).1 * G (finProdFinEquiv.symm k).2
                  + G (finProdFinEquiv.symm k).2 * G (finProdFinEquiv.symm k).1)
            else 0) := fun k => by
    split_ifs with h
    · exact smul_comm _ _ _
    · simp
  rw [Finset.sum_congr rfl fun k _ => hstep k, ← Finset.smul_sum]
  congr 1
  -- `finProdFinEquiv.symm` is exactly the reindex `Fin (h * h) ≃ Fin h × Fin h` needs
  rw [Fintype.sum_equiv finProdFinEquiv.symm
    (fun k => if (finProdFinEquiv.symm k).1 < (finProdFinEquiv.symm k).2 then
        (p (finProdFinEquiv.symm k).1 * p (finProdFinEquiv.symm k).2) •
          (G (finProdFinEquiv.symm k).1 * G (finProdFinEquiv.symm k).2
            + G (finProdFinEquiv.symm k).2 * G (finProdFinEquiv.symm k).1)
      else 0)
    (fun ij : Fin h × Fin h => if ij.1 < ij.2 then
        (p ij.1 * p ij.2) • (G ij.1 * G ij.2 + G ij.2 * G ij.1)
      else 0)
    fun _ => rfl]
  exact Fintype.sum_prod_type ..


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.quadTaylor_outer {n : ℕ} (A_Z : Zonotope (Mat ℝ n n)) (t : ℝ) :
    (fun A => (1 : Mat ℝ n n) + t • A + (t ^ 2 / 2) • (A * A)) '' A_Z.construct
      ⊆ (A_Z.quadTaylor t).construct := by -- --- PROOF ---
  rintro _ ⟨A, ⟨p, hp, rfl⟩, rfl⟩
  -- `q i := 2(p i)² - 1`, the diagonal block's own coefficient, `p i²`'s image of `[-1,1]`
  have hq : ∀ i, |2 * (p i) ^ 2 - 1| ≤ 1 := fun i => by
    have h1 := abs_le.mp (hp i)
    rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2]
  have hpq : ∀ i2 : Fin (A_Z.h + A_Z.h),
      |Fin.append p (fun i => 2 * (p i) ^ 2 - 1) i2| ≤ 1 :=
    Fin.addCases (fun i => by simp only [Fin.append_left]; exact hp i)
      (fun j => by simp only [Fin.append_right]; exact hq j)
  refine ⟨Fin.append (Fin.append p (fun i => 2 * (p i) ^ 2 - 1))
      (fun k => p (finProdFinEquiv.symm k).1 * p (finProdFinEquiv.symm k).2),
    Fin.addCases (fun i2 => by rw [Fin.append_left]; exact hpq i2)
      (fun k => by
        simp only [Fin.append_right, abs_mul]
        exact mul_le_one₀ (hp _) (abs_nonneg _) (hp _)), ?_⟩
  show (1 : Mat ℝ n n) + t • (A_Z.c + ∑ i, p i • A_Z.G i)
      + (t ^ 2 / 2) • ((A_Z.c + ∑ i, p i • A_Z.G i) * (A_Z.c + ∑ i, p i • A_Z.G i))
    = (A_Z.quadTaylor t).c
        + ∑ j, (Fin.append (Fin.append p (fun i => 2 * (p i) ^ 2 - 1))
            (fun k => p (finProdFinEquiv.symm k).1 * p (finProdFinEquiv.symm k).2)) j
          • (A_Z.quadTaylor t).G j
  -- expand the square, split the diagonal off the pair sum, then fold both centrewards
  rw [Zonotope.aux_quadTaylor_sq, Zonotope.aux_quadTaylor_diagpair, smul_add, smul_add, smul_add,
    smul_add, Zonotope.aux_quadTaylor_diagfold, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Zonotope.quadTaylor, Fin.append_left, Fin.append_right]
  rw [Zonotope.aux_quadTaylor_lin, Zonotope.aux_quadTaylor_pairblock]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
