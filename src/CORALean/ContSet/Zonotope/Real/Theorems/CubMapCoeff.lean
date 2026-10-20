module

public import CORALean.ContSet.Zonotope.Real.Operations.CubMap
public import CORALean.ContSet.PolyZonotope.Real.Operations.CubEval
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The coefficients of `Zonotope.cubMap`

The point `x = c + Σⱼ pⱼ g⁽ʲ⁾` of a zonotope, with extended factors `β = (1, p₁, ..., p_h)`, is
`x = Σₐ βₐ [c,G]ₐ`, so the `i`-th coordinate of `(xᵀ T x) * x` is the cubic polynomial
`Σ_c Σₐ Σ_b β_c βₐ β_b t(a, b, c)`. CORA collects it over the sorted triples (`cubFold`), the
pure squares `β_k²` carried as `0.5 + 0.5 (2 β_k² - 1)`. The coefficients of the generators are
`βₓ β_y β_z`, `2β_y² - 1` at `(0, y, y)`: all in `[-1, 1]`, the only place the enclosure is lost.
`aux_cubMap_regroup` is the combinatorial step: the ordered triples `(c; a ≤ b)` and the sorted
triples `x ≤ y ≤ z` are the same sum.

## Inputs
* `T` – cubic tensor
* `Z` – zonotope
* `p` – generator coefficients

## Hypotheses
* `hp` – coefficients within the unit box

## Conclusion
* the cubic image has coefficients in the unit box
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The ordered pairs split into the diagonal and one term per unordered pair `a < b`. -/
theorem Zonotope.aux_cubMap_pairs {N : ℕ} (g : Fin N → Fin N → ℝ) : -- --- CONCL ---
    ∑ a, ∑ b, g a b
      = ∑ a, ∑ b,
          (if a < b then g a b + g b a else if a = b then g a a else 0) := by -- --- PROOF ---
  -- every pair is above, on or below the diagonal
  have h1 : ∀ a b : Fin N, g a b = (if a < b then g a b else 0) + (if a = b then g a b else 0)
      + (if b < a then g a b else 0) := fun a b => by
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.mpr h.le]
  -- the pairs below the diagonal are the transposed pairs above it
  have hswap : ∑ a : Fin N, ∑ b : Fin N, (if b < a then g a b else 0)
      = ∑ a : Fin N, ∑ b : Fin N, (if a < b then g b a else 0) := Finset.sum_comm
  -- the folded summand, split into the same three parts
  have h2 : ∀ a b : Fin N, (if a < b then g a b + g b a else if a = b then g a a else 0)
      = (if a < b then g a b else 0) + (if a = b then g a b else 0)
        + (if a < b then g b a else 0) := fun a b => by
    by_cases h : a < b
    · simp [h, h.ne]
    · by_cases h' : a = b
      · subst h'; simp
      · simp [h, h']
  simp only [h2, Finset.sum_add_distrib, ← hswap]
  conv_lhs => enter [2, a, 2, b]; rw [h1 a b]
  simp only [Finset.sum_add_distrib]

/-- The ordered triples `(c; a, b)` of a cubic polynomial whose coefficient `L c a b` vanishes
below the diagonal, and the sorted triples `x ≤ y ≤ z`: `c ≤ a` stays, `a < c ≤ b` and `b < c`
move `c` into its place. -/
theorem Zonotope.aux_cubMap_regroup {N : ℕ} (β : Fin N → ℝ) (L : Fin N → Fin N → Fin N → ℝ)
    (hL : ∀ c a b, b < a → L c a b = 0) : -- --- CONCL ---
    ∑ c, ∑ a, ∑ b, β c * β a * β b * L c a b
      = ∑ x, ∑ y, ∑ z, (if x ≤ y ∧ y ≤ z then β x * β y * β z *
          (L x y z + (if x < z then L z x y else 0)
            + (if x < y ∧ y < z then L y x z else 0)) else 0) := by -- --- PROOF ---
  -- every ordered triple lies in exactly one of four regions
  have step1 : ∀ c a b : Fin N, β c * β a * β b * L c a b
      = (if c ≤ a ∧ a ≤ b then β c * β a * β b * L c a b else 0)
        + (if a < c ∧ c < b then β c * β a * β b * L c a b else 0)
        + (if a < c ∧ c = b then β c * β a * β b * L c a b else 0)
        + (if a ≤ b ∧ b < c then β c * β a * β b * L c a b else 0) := fun c a b => by
    -- below the diagonal the coefficient vanishes; above it `c` is placed against `a` and `b`
    by_cases hab : a ≤ b
    · rcases lt_trichotomy c a with h | h | h
      · have : ¬ (a < c) := by omega
        simp [h.le, hab, this, show ¬ (b < c) by omega]
      · subst h
        simp [hab, show ¬ (b < c) by omega]
      · rcases lt_trichotomy c b with h' | h' | h'
        · simp [h, h', hab, not_le.mpr h, not_lt.mpr h'.le, h'.ne]
        · subst h'
          simp [h, hab, show ¬ (c ≤ a) by omega]
        · simp [h, hab, h', not_le.mpr h, show ¬ (c < b) by omega, show ¬ (c = b) by omega]
    · have h0 : L c a b = 0 := hL c a b (not_le.mp hab)
      simp [h0]
  have rhs1 : ∀ x y z : Fin N, (if x ≤ y ∧ y ≤ z then β x * β y * β z *
          (L x y z + (if x < z then L z x y else 0)
            + (if x < y ∧ y < z then L y x z else 0)) else 0)
      = (if x ≤ y ∧ y ≤ z then β x * β y * β z * L x y z else 0)
        + (if x ≤ y ∧ y < z then β x * β y * β z * L z x y else 0)
        + (if x < y ∧ y = z then β x * β y * β z * L z x y else 0)
        + (if x < y ∧ y < z then β x * β y * β z * L y x z else 0) := fun x y z => by
    -- on a sorted triple `y < z` or `y = z`, and `x < y` or `x = y`
    by_cases h1 : x ≤ y ∧ y ≤ z
    · rcases lt_or_eq_of_le h1.2 with h2 | h2
      · by_cases h3 : x < y
        · simp [h1, h2, h3, show x < z by omega, ne_of_lt h2]
          ring
        · have : x = y := by omega
          subst this
          simp [h1, h2, ne_of_lt h2]
          ring
      · subst h2
        by_cases h3 : x < y
        · simp [h1, h3]
          ring
        · simp [h1, h3]
    -- an unsorted triple lies in none of the four
    · have : ¬ (x ≤ y ∧ y < z) := fun h => h1 ⟨h.1, h.2.le⟩
      have h4 : ¬ (x < y ∧ y = z) := fun h => h1 ⟨h.1.le, h.2.le⟩
      have h5 : ¬ (x < y ∧ y < z) := fun h => h1 ⟨h.1.le, h.2.le⟩
      simp [h1, this, h4, h5]
  -- the left side as four sums over the regions, the right side likewise
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => step1 c a b]
  simp only [rhs1, Finset.sum_add_distrib]
  -- the regions, renamed: `c ≤ a` is already sorted
  have e2a : ∑ c, ∑ a, ∑ b, (if a < c ∧ c < b then β c * β a * β b * L c a b else 0)
      = ∑ x, ∑ y, ∑ z, (if x < y ∧ y < z then β x * β y * β z * L y x z else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun z _ => ?_
    split_ifs <;> ring
  -- `a < c = b` lands on the sorted triple `(a, b, b)`
  have e2b : ∑ c, ∑ a, ∑ b, (if a < c ∧ c = b then β c * β a * β b * L c a b else 0)
      = ∑ x, ∑ y, ∑ z, (if x < y ∧ y = z then β x * β y * β z * L z x y else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun z _ => ?_
    by_cases hyz : y = z
    · subst hyz; split_ifs <;> ring
    · simp [hyz]
  -- `b < c` lands on `(a, b, c)`
  have e3 : ∑ c, ∑ a, ∑ b, (if a ≤ b ∧ b < c then β c * β a * β b * L c a b else 0)
      = ∑ x, ∑ y, ∑ z, (if x ≤ y ∧ y < z then β x * β y * β z * L z x y else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    split_ifs <;> ring
  rw [e2a, e2b, e3]
  ring

/-- The quadratic form of a combination of the extended columns. -/
theorem Zonotope.aux_cubMap_dot {N : ℕ} (A : Mat ℝ n n) (β : Fin N → ℝ)
    (u : Fin N → Vec ℝ n) : -- --- CONCL ---
    (∑ a, β a • u a) ⬝ᵥ (A *ᵥ ∑ b, β b • u b)
      = ∑ a, ∑ b, β a * β b * (u a ⬝ᵥ (A *ᵥ u b)) := by -- --- PROOF ---
  simp only [sum_dotProduct, mulVec_sum, dotProduct_sum, smul_dotProduct, mulVec_smul,
    dotProduct_smul, smul_eq_mul, mul_assoc]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- The cubic map of a combination of the extended columns, as a sum over the ordered triples. -/
theorem Zonotope.aux_cubMap_expand (T : Fin m → Fin n → Mat ℝ n n) {N : ℕ} (β : Fin N → ℝ)
    (u : Fin N → Vec ℝ n) (i : Fin m) : -- --- CONCL ---
    PolyZonotope.cubEval T (∑ a, β a • u a) i
      = ∑ c, ∑ a, ∑ b, β c * β a * β b * ∑ k, (u a ⬝ᵥ (T i k *ᵥ u b)) * u c k := by -- --- PROOF ---
  unfold PolyZonotope.cubEval
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Zonotope.aux_cubMap_dot (T i _)]
  simp only [Finset.sum_mul, Finset.mul_sum]
  -- the outermost sum over `k` moves innermost and the one over `c` outermost
  have e : ∀ f : Fin n → Fin N → Fin N → Fin N → ℝ,
      ∑ k, ∑ a, ∑ b, ∑ c, f k a b c = ∑ c, ∑ a, ∑ b, ∑ k, f k a b c := fun f => by
    calc ∑ k, ∑ a, ∑ b, ∑ c, f k a b c
        = ∑ k, ∑ a, ∑ c, ∑ b, f k a b c :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ k, ∑ c, ∑ a, ∑ b, f k a b c :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ c, ∑ k, ∑ a, ∑ b, f k a b c := Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ k, ∑ b, f k a b c :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ b, ∑ k, f k a b c :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [e]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring

/-- The sorted triples as the center, the halved squares and the generators of `cubMap`. -/
theorem Zonotope.aux_cubMap_assemble (h : ℕ) (β : Fin (h + 1) → ℝ) (hβ : β 0 = 1)
    (F : Fin (h + 1) → Fin (h + 1) → Fin (h + 1) → ℝ) : -- --- CONCL ---
    ∑ x, ∑ y, ∑ z, (if x ≤ y ∧ y ≤ z then β x * β y * β z * F x y z else 0)
      = (F 0 0 0 + 1 / 2 * ∑ y : Fin h, F 0 y.succ y.succ)
        + ∑ x, ∑ y, ∑ z, (if x = 0 ∧ y = z then 2 * β y ^ 2 - 1 else β x * β y * β z)
          * (if x ≤ y ∧ y ≤ z ∧ ¬(x = 0 ∧ y = 0 ∧ z = 0) then
              (if x = 0 ∧ y = z then 1 / 2 else 1) * F x y z else 0) := by -- --- PROOF ---
  -- pointwise: the `(0, 0, 0)` term, the squares `β_y² = 0.5 + 0.5 (2 β_y² - 1)`, the rest
  have key : ∀ x y z : Fin (h + 1),
      (if x ≤ y ∧ y ≤ z then β x * β y * β z * F x y z else 0)
      = (if x = 0 ∧ y = 0 ∧ z = 0 then F x y z else 0)
        + (if x = 0 ∧ y = z ∧ y ≠ 0 then 1 / 2 * F x y z else 0)
        + (if x = 0 ∧ y = z then 2 * β y ^ 2 - 1 else β x * β y * β z)
          * (if x ≤ y ∧ y ≤ z ∧ ¬(x = 0 ∧ y = 0 ∧ z = 0) then
              (if x = 0 ∧ y = z then 1 / 2 else 1) * F x y z else 0) := fun x y z => by
    by_cases hx : x = 0
    · subst hx
      -- `(0, y, y)` is a square, `(0, y, z)` with `y ≠ z` an ordinary monomial
      by_cases hyz : y = z
      · subst hyz
        by_cases hy : y = 0
        · subst hy; simp [hβ]
        · have : (0 : Fin (h + 1)) ≤ y := Fin.zero_le y
          simp [hy, hβ]
          ring
      · by_cases hs : y ≤ z
        · have hz : ¬ (y = 0 ∧ z = 0) := fun ⟨a, b⟩ => hyz (a.trans b.symm)
          have hz' : y = 0 → ¬ z = 0 := fun a b => hz ⟨a, b⟩
          simp [hyz, hs, hβ, hz]
        · have hz' : y = 0 → z = 0 → False := fun a b => hyz (a.trans b.symm)
          simp [hyz, hs]
          exact fun a b => (hz' a b).elim
    · by_cases hs : x ≤ y ∧ y ≤ z
      · simp [hx, hs]
      · simp [hx, hs]
  -- the sum of the pieces: the `(0, 0, 0)` term, the halved squares, the generators
  simp only [key, Finset.sum_add_distrib]
  congr 1
  congr 1
  · simp [ite_and]
  · simp [ite_and]
    rw [Fin.sum_univ_succ]
    simp [Finset.mul_sum]

/-- `cubFold` over the pair coefficients `L c a b = listQuad{c}(a, b)`. -/
theorem Zonotope.aux_cubMap_fold (T : Fin m → Fin n → Mat ℝ n n) (Z : Zonotope (Vec ℝ n))
    (i : Fin m) (Zext : Fin (Z.h + 1) → Vec ℝ n) (hZ : Zext = Fin.cons Z.c Z.G)
    (L : Fin (Z.h + 1) → Fin (Z.h + 1) → Fin (Z.h + 1) → ℝ)
    (hL : ∀ c a b, L c a b
      = if a < b then
          (∑ k, (Zext a ⬝ᵥ
              (T i k *ᵥ Zext b))
            * Zext c k)
          + ∑ k, (Zext b ⬝ᵥ
              (T i k *ᵥ Zext a))
            * Zext c k
        else if a = b then
          ∑ k, (Zext a ⬝ᵥ
              (T i k *ᵥ Zext a))
            * Zext c k
        else 0)
    (x y z : Fin (Z.h + 1)) : -- --- CONCL ---
    Z.cubFold T i x y z
      = L x y z + (if x < z then L z x y else 0)
        + (if x < y ∧ y < z then L y x z else 0) := by -- --- PROOF ---
  -- `listQuad{c}(a, b)`, the pair coefficient, is `L c a b`
  have hlist : ∀ c a b, (∑ k, (if a < b then
        Zext a ⬝ᵥ
            (T i k *ᵥ Zext b)
          + Zext b ⬝ᵥ
            (T i k *ᵥ Zext a)
        else if a = b then Zext a ⬝ᵥ
            (T i k *ᵥ Zext a) else 0)
        * Zext c k) = L c a b := fun c a b => by
    rw [hL]
    by_cases h1 : a < b
    · simp [h1, add_mul, Finset.sum_add_distrib]
    · by_cases h2 : a = b
      · simp [h2]
      · simp [h1, h2]
  unfold Zonotope.cubFold
  simp only [← hZ, hlist]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The cubic image of the point `c + Σ pⱼ g⁽ʲ⁾` is the center plus the generators of `Z.cubMap T`
at coefficients in `[-1, 1]`, those of the linear generators `(0, 0, j)` being the `pⱼ`. -/
theorem Zonotope.cubMap_coeff (T : Fin m → Fin n → Mat ℝ n n) (Z : Zonotope (Vec ℝ n))
    (p : Fin Z.h → ℝ) (hp : ∀ j, |p j| ≤ 1) : -- --- CONCL ---
    ∃ γ : Fin (Z.cubMap T).h → ℝ, (∀ l, |γ l| ≤ 1)
      ∧ (∀ j : Fin Z.h,
          γ ((Zonotope.cubIdx (Z.h + 1) (Z.h + 1) (Z.h + 1)).symm ((0, 0), j.succ)) = p j)
      ∧ PolyZonotope.cubEval T (Z.c + ∑ j, p j • Z.G j)
          = (Z.cubMap T).c + ∑ l, γ l • (Z.cubMap T).G l := by -- --- PROOF ---
  -- the extended columns `[c, G]` and factors `(1, p)`
  obtain ⟨Zext, hZ⟩ : ∃ Zext : Fin (Z.h + 1) → Vec ℝ n, Zext = Fin.cons Z.c Z.G := ⟨_, rfl⟩
  set idx := Zonotope.cubIdx (Z.h + 1) (Z.h + 1) (Z.h + 1) with hidx
  set β : Fin (Z.h + 1) → ℝ := Fin.cons 1 p with hβ
  have hβ0 : β 0 = 1 := rfl
  have hβ1 : ∀ a, |β a| ≤ 1 := fun a => by
    refine Fin.cases ?_ (fun j => ?_) a
    · simp [hβ0]
    · simpa [hβ] using hp j
  -- the coefficients: `2 β_y² - 1` at `(0, y, y)`, the product of the three factors elsewhere
  refine ⟨fun l =>
    if (idx l).1.1 = 0 ∧ (idx l).1.2 = (idx l).2 then 2 * β (idx l).1.2 ^ 2 - 1
    else β (idx l).1.1 * β (idx l).1.2 * β (idx l).2, ?_, ?_, ?_⟩
  -- all of them lie in `[-1, 1]`
  · intro l
    dsimp only
    split_ifs
    · have h1 := abs_le.mp (hβ1 (idx l).1.2)
      rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2]
    · rw [abs_mul, abs_mul]
      exact mul_le_one₀ (mul_le_one₀ (hβ1 _) (abs_nonneg _) (hβ1 _)) (abs_nonneg _) (hβ1 _)
  -- the linear generators carry the point's own coefficients
  · intro j
    simp [hβ, hidx, Ne.symm (Fin.succ_ne_zero j)]
  · funext i
    -- the point as a combination of the extended columns
    have hx : Z.c + ∑ j, p j • Z.G j = ∑ a, β a • Zext a := by
      rw [hZ, Fin.sum_univ_succ]
      simp [hβ]
    rw [hx, Zonotope.aux_cubMap_expand]
    -- the pair coefficients `L c a b = listQuad{c}(a, b)`
    set Lc : Fin (Z.h + 1) → Fin (Z.h + 1) → Fin (Z.h + 1) → ℝ := fun c a b =>
      if a < b then
          (∑ k, (Zext a ⬝ᵥ
              (T i k *ᵥ Zext b))
            * Zext c k)
          + ∑ k, (Zext b ⬝ᵥ
              (T i k *ᵥ Zext a))
            * Zext c k
        else if a = b then
          ∑ k, (Zext a ⬝ᵥ
              (T i k *ᵥ Zext a))
            * Zext c k
        else 0 with hLc
    -- folding onto the upper triangle, per `c`
    have hupper : ∀ c : Fin (Z.h + 1), ∑ a, ∑ b, β c * β a * β b * ∑ k,
          (Zext a ⬝ᵥ
            (T i k *ᵥ Zext b))
          * Zext c k
        = ∑ a, ∑ b, β c * β a * β b * Lc c a b := fun c => by
      have h1 := Zonotope.aux_cubMap_pairs (fun a b => β c * β a * β b * ∑ k,
          (Zext a ⬝ᵥ
            (T i k *ᵥ Zext b))
          * Zext c k)
      rw [h1]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : a < b
      · simp only [hLc, if_pos hab]; ring
      · by_cases hab' : a = b
        · subst hab'; simp [hLc]
        · simp only [hLc, if_neg hab, if_neg hab']; ring
    rw [Finset.sum_congr rfl fun c _ => hupper c]
    rw [Zonotope.aux_cubMap_regroup β Lc (fun c a b hba => by
      simp [hLc, not_lt.mpr hba.le, hba.ne'])]
    -- every sorted coefficient is `cubFold`
    simp only [← Zonotope.aux_cubMap_fold T Z i Zext hZ Lc (fun c a b => rfl)]
    rw [Zonotope.aux_cubMap_assemble Z.h β hβ0 (fun x y z => Z.cubFold T i x y z)]
    -- the generators of `cubMap`, a sum over the ordered triples
    rw [Pi.add_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    refine congrArg₂ _ rfl ?_
    symm
    refine (Fintype.sum_equiv idx _
      (fun t : (Fin (Z.h + 1) × Fin (Z.h + 1)) × Fin (Z.h + 1) =>
        (if t.1.1 = 0 ∧ t.1.2 = t.2 then 2 * β t.1.2 ^ 2 - 1 else β t.1.1 * β t.1.2 * β t.2)
          * (if t.1.1 ≤ t.1.2 ∧ t.1.2 ≤ t.2 ∧ ¬(t.1.1 = 0 ∧ t.1.2 = 0 ∧ t.2 = 0) then
              (if t.1.1 = 0 ∧ t.1.2 = t.2 then 1 / 2 else 1) * Z.cubFold T i t.1.1 t.1.2 t.2
            else 0)) fun l => rfl).trans ?_
    simp only [Fintype.sum_prod_type]


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
