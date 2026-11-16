module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolyReal
public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPowersList
public import CORALean.ContSet.PolyZonotope.Real.Operations.PowerOut
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# `PolyZonotope.evalPowersList` over ℝ is the polynomial at every point of the row

At the values `M` of the monomials and `N` of the independent factors, all in `[-1, 1]`, the
row's point is `c + G·M + GI·N`. The result's point at the monomials of the powers
(`PolyZonotope.powerOut`) and at new independent values `N'` in `[-1, 1]` is the polynomial at
that point. `N'` are products of the old values (the square of an independent factor `β` is `2β² -
1`), and depend on `M`, `N` and the order only, so all rows of a set share them.

## Inputs
* `M` – values of the monomials
* `N` – values of the independent factors
* `k` – order

## Hypotheses
* `hM` – the monomial values lie in `[-1, 1]`
* `hN` – the independent values lie in `[-1, 1]`

## Conclusion
* independent values `N'` in `[-1, 1]` at which every row of matching lengths and every
  coefficient list of order `k` gives the polynomial
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ δ : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The number of pairs of a list. -/
private theorem aux_length_pairsWith {f : α → α → γ} {g : β → β → δ} {a : List α} {b : List β}
    (h : a.length = b.length) : -- --- CONCL ---
    (PolyZonotope.pairsWith f a).length = (PolyZonotope.pairsWith g b).length := by -- --- PROOF ---
  induction a generalizing b with
  | nil => cases b <;> simp_all [PolyZonotope.pairsWith]
  | cons x a ih => cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp [PolyZonotope.pairsWith, ih h, h]

/-- The number of products of two lists. -/
private theorem aux_length_crossWith {f : α → α → γ} {g : β → β → δ} {a a' : List α} {b b' : List β}
    (h : a.length = b.length) (h' : a'.length = b'.length) : -- --- CONCL ---
    (PolyZonotope.crossWith f a a').length =
        (PolyZonotope.crossWith g b b').length := by -- --- PROOF ---
  simp only [PolyZonotope.crossWith, List.length_flatMap, List.length_map]
  induction a' generalizing b' with
  | nil => cases b' <;> simp_all
  | cons x a' ih => cases b' with
    | nil => simp at h'
    | cons y b' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h'
      simp [h, h']

/-- The number of dependent generators of a power. -/
private theorem aux_length_power_G (o : PowerOps α) (f : β → β → β) {x : PowerRow α} {M : List β}
    (hM : x.G.length = M.length) (i : ℕ) : -- --- CONCL ---
    (PolyZonotope.step_power o x i).G.length =
        (PolyZonotope.powerExt f M i).length := by -- --- PROOF ---
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [PolyZonotope.step_power.eq_1, PolyZonotope.powerExt.eq_1]
    split_ifs with h1 h2
    · exact hM
    · have := ih (i / 2) (by omega)
      simp only [PolyZonotope.step_square, List.length_append, List.length_map, this]
      rw [aux_length_pairsWith (g := f) this]
    · have h3 := ih (i / 2) (by omega)
      have h4 := ih ((i + 1) / 2) (by omega)
      simp only [PolyZonotope.step_times, List.length_append, List.length_map, h3, h4]
      rw [aux_length_crossWith (g := f) h3 h4]


/-- The dot product of two real lists. -/
private def aux_dot (a b : List ℝ) : ℝ := (List.zipWith (· * ·) a b).sum

/-- The value of a row at the factors `M` and `N`. -/
private def aux_val (x : PowerRow ℝ) (M N : List ℝ) : ℝ := x.c + aux_dot x.G M + aux_dot x.GI N

/-- The dot product with the empty list. -/
private theorem aux_dot_nil_left (b : List ℝ) : aux_dot [] b = 0 := by simp [aux_dot]
/-- The dot product of two lists with a head each. -/
private theorem aux_dot_cons (a A : ℝ) (b B : List ℝ) : aux_dot (a :: b) (A :: B) = a * A + aux_dot
    b B := by
  simp [aux_dot]

/-- The dot product splits at an append of equal-length prefixes. -/
private theorem aux_dot_append {a A b B : List ℝ} (h : a.length = A.length) :
    aux_dot (a ++ b) (A ++ B) = aux_dot a A + aux_dot b B := by
  simp [aux_dot, List.zipWith_append h]

/-- Scaling the first list scales the dot product. -/
private theorem aux_dot_map_left (c : ℝ) (a A : List ℝ) : -- --- CONCL ---
    aux_dot (a.map (c * ·)) A = c * aux_dot a A := by -- --- PROOF ---
  induction a generalizing A with
  | nil => simp [aux_dot]
  | cons x a ih => cases A with
    | nil => simp [aux_dot]
    | cons y A => rw [List.map_cons, aux_dot_cons, aux_dot_cons, ih]; ring

/-- Scaling the second list scales the dot product. -/
private theorem aux_dot_map_right (c : ℝ) (a A : List ℝ) : -- --- CONCL ---
    aux_dot (a.map (· * c)) A = aux_dot a A * c := by -- --- PROOF ---
  induction a generalizing A with
  | nil => simp [aux_dot]
  | cons x a ih => cases A with
    | nil => simp [aux_dot]
    | cons y A => rw [List.map_cons, aux_dot_cons, aux_dot_cons, ih]; ring

/-- Scaling both lists scales the dot product by the product. -/
private theorem aux_dot_map_map (c d : ℝ) (a A : List ℝ) : -- --- CONCL ---
    aux_dot (a.map (· * c)) (A.map (· * d)) = aux_dot a A * (c * d) := by -- --- PROOF ---
  induction a generalizing A with
  | nil => simp [aux_dot]
  | cons x a ih => cases A with
    | nil => simp [aux_dot]
    | cons y A => rw [List.map_cons, List.map_cons, aux_dot_cons, aux_dot_cons, ih]; ring

/-- The products of two lists against the products of their factors. -/
private theorem aux_dot_cross {a A b B : List ℝ} (ha : a.length = A.length) (hb : b.length =
    B.length) : -- --- CONCL ---
    aux_dot (PolyZonotope.crossWith (· * ·) a b) (PolyZonotope.crossWith (· * ·) A B) = aux_dot a A
        * aux_dot b B := by -- --- PROOF ---
  induction b generalizing B with
  | nil => cases B <;> simp_all [PolyZonotope.crossWith, aux_dot]
  | cons y b ih => cases B with
    | nil => simp at hb
    | cons Y B =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hb
      have := ih hb
      simp only [PolyZonotope.crossWith, List.flatMap_cons] at this ⊢
      rw [aux_dot_append (by simp [ha]), aux_dot_map_map, this, aux_dot_cons]; ring

/-- A square as the squares and the doubled pairs. -/
private theorem aux_dot_sq_pairs {a A : List ℝ} (h : a.length = A.length) : -- --- CONCL ---
    aux_dot (a.map fun g => g * g) (A.map fun m => m * m)
      + aux_dot (PolyZonotope.pairsWith (fun u v => 2 * u * v) a) (PolyZonotope.pairsWith (· * ·)
          A) = aux_dot a A ^ 2 := by -- --- PROOF ---
  induction a generalizing A with
  | nil => simp [aux_dot, PolyZonotope.pairsWith]
  | cons x a ih => cases A with
    | nil => simp at h
    | cons y A =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have e1 : aux_dot (a.map ((fun u v => 2 * u * v) x)) (A.map ((· * ·) y)) = 2 * x * y *
          aux_dot a A := by
        clear ih
        induction a generalizing A with
        | nil => simp [aux_dot]
        | cons u a ih2 => cases A with
          | nil => simp at h
          | cons U A =>
            simp only [List.length_cons, Nat.add_right_cancel_iff] at h
            rw [List.map_cons, List.map_cons, aux_dot_cons, aux_dot_cons, ih2 A h]; ring
      simp only [PolyZonotope.pairsWith, List.map_cons, aux_dot_cons]
      rw [aux_dot_append (by simp [h]), e1]
      have := ih h
      nlinarith [this]


/-- A left sum with an initial value. -/
private theorem aux_foldl_add_eq (c : ℝ) (l : List ℝ) : l.foldl (· + ·) c = c + l.sum := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.sum_cons]; ring

/-- A square through the pseudo-variable `2β² - 1`. -/
private theorem aux_dot_half_shift {a N : List ℝ} (h : a.length = N.length) : -- --- CONCL ---
    aux_dot (a.map fun g => g * g * (1 / 2)) (N.map fun ν => 2 * ν ^ 2 - 1)
      = aux_dot (a.map fun g => g * g) (N.map fun ν => ν * ν) - (a.map fun g => g * g * (1 /
          2)).sum := by -- --- PROOF ---
  induction a generalizing N with
  | nil => simp [aux_dot]
  | cons x a ih => cases N with
    | nil => simp at h
    | cons y N =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.map_cons, aux_dot_cons, List.sum_cons, ih h]; ring

/-- The value of the square row is the square of the value. -/
private theorem aux_val_square {x : PowerRow ℝ} {M N : List ℝ} (hM : x.G.length = M.length)
    (hN : x.GI.length = N.length) : -- --- CONCL ---
    aux_val (PolyZonotope.step_square PowerOps.real x) (M ++ M ++ M.map (fun m => m * m) ++
        PolyZonotope.pairsWith (· * ·) M)
      (N ++ N ++ N.map (fun ν => 2 * ν ^ 2 - 1) ++ PolyZonotope.pairsWith (· * ·) N ++
          PolyZonotope.crossWith (· * ·) N M)
      = aux_val x M N ^ 2 := by -- --- PROOF ---
  have hG := aux_dot_sq_pairs hM
  have hGI := aux_dot_sq_pairs hN
  have hsh := aux_dot_half_shift hN
  have hcr := aux_dot_cross hN hM
  have hcr2 : aux_dot ((PolyZonotope.crossWith (· * ·) x.GI x.G).map ((2 : ℝ) * ·))
      (PolyZonotope.crossWith (· * ·) N M)
      = 2 * (aux_dot x.GI N * aux_dot x.G M) := by rw [aux_dot_map_left, hcr]
  simp only [PolyZonotope.step_square, PowerOps.real, aux_val]
  rw [aux_foldl_add_eq, aux_dot_append (by simp [hM]),
    aux_dot_append (by simp [hM]), aux_dot_append (by simp [hM]),
    aux_dot_append (by simp [hN, aux_length_pairsWith (g := (· * ·)) hN]),
    aux_dot_append (by simp [hN]), aux_dot_append (by simp [hN]), aux_dot_append (by simp [hN])]
  simp only [aux_dot_map_left]
  have e : aux_dot (List.map (fun g => g * g * (1 / 2)) x.GI) (List.map (fun ν => 2 * ν ^ 2 - 1) N)
      + (List.map (fun g => g * g * (1 / 2)) x.GI).sum
      = aux_dot (x.GI.map fun g => g * g) (N.map fun ν => ν * ν) := by rw [hsh]; ring
  linear_combination hG + hGI + e + 2 * hcr


/-- The value of the product row is the product of the values. -/
private theorem aux_val_times {x y : PowerRow ℝ} {M1 N1 M2 N2 : List ℝ} (hM1 : x.G.length =
    M1.length)
    (hN1 : x.GI.length = N1.length) (hM2 : y.G.length = M2.length)
    (hN2 : y.GI.length = N2.length) : -- --- CONCL ---
    aux_val (PolyZonotope.step_times PowerOps.real x y) (M1 ++ M2 ++ PolyZonotope.crossWith (· * ·)
        M1 M2)
      (N1 ++ N2 ++ PolyZonotope.crossWith (· * ·) N1 N2 ++ PolyZonotope.crossWith (· * ·) M1 N2 ++
          PolyZonotope.crossWith (· * ·) N1 M2)
      = aux_val x M1 N1 * aux_val y M2 N2 := by -- --- PROOF ---
  simp only [PolyZonotope.step_times, PowerOps.real, aux_val]
  rw [aux_dot_append (by simp [hM1, hM2]), aux_dot_append (by simp [hM1]),
    aux_dot_append (by simp [hN1, hN2, aux_length_crossWith (g := (· * ·)) hM1 hN2,
      aux_length_crossWith (g := (· * ·)) hN1 hN2]),
    aux_dot_append (by simp [hN1, hN2, aux_length_crossWith (g := (· * ·)) hN1 hN2]),
    aux_dot_append (by simp [hN1, hN2]), aux_dot_append (by simp [hN1]),
    aux_dot_cross hM1 hM2, aux_dot_cross hN1 hN2, aux_dot_cross hM1 hN2, aux_dot_cross hN1 hM2]
  simp only [aux_dot_map_left]
  ring


/-- The pseudo-variables of the next power. -/
private noncomputable def aux_next (M N : List ℝ) (i : ℕ) : List ℝ :=
  if i < 2 then N else
    if i % 2 = 0 then
      aux_next M N (i / 2) ++ aux_next M N (i / 2)
        ++ (aux_next M N (i / 2)).map (fun ν => 2 * ν ^ 2 - 1)
        ++ PolyZonotope.pairsWith (· * ·) (aux_next M N (i / 2))
        ++ PolyZonotope.crossWith (· * ·) (aux_next M N (i / 2)) (PolyZonotope.powerExt (· * ·) M
            (i / 2))
    else aux_next M N (i / 2) ++ aux_next M N ((i + 1) / 2)
      ++ PolyZonotope.crossWith (· * ·) (aux_next M N (i / 2)) (aux_next M N ((i + 1) / 2))
      ++ PolyZonotope.crossWith (· * ·) (PolyZonotope.powerExt (· * ·) M (i / 2)) (aux_next M N ((i
          + 1) / 2))
      ++ PolyZonotope.crossWith (· * ·) (aux_next M N (i / 2)) (PolyZonotope.powerExt (· * ·) M ((i
          + 1) / 2))
termination_by i
decreasing_by all_goals omega

/-- The number of independent generators of a power. -/
private theorem aux_length_power_GI (o : PowerOps α) {x : PowerRow α} {M N : List ℝ}
    (hM : x.G.length = M.length) (hN : x.GI.length = N.length) (i : ℕ) : -- --- CONCL ---
    (PolyZonotope.step_power o x i).GI.length = (aux_next M N i).length := by -- --- PROOF ---
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [PolyZonotope.step_power.eq_1, aux_next.eq_1]
    split_ifs with h1 h2
    · exact hN
    · have h3 := ih (i / 2) (by omega)
      have hg := aux_length_power_G o (· * ·) hM (i / 2)
      simp only [PolyZonotope.step_square, List.length_append, List.length_map, h3]
      rw [aux_length_pairsWith (g := (· * ·)) h3, aux_length_crossWith (g := (· * ·)) h3 hg]
    · have h3 := ih (i / 2) (by omega)
      have h4 := ih ((i + 1) / 2) (by omega)
      have hg3 := aux_length_power_G o (· * ·) hM (i / 2)
      have hg4 := aux_length_power_G o (· * ·) hM ((i + 1) / 2)
      simp only [PolyZonotope.step_times, List.length_append, List.length_map, h3, h4]
      rw [aux_length_crossWith (g := (· * ·)) h3 h4, aux_length_crossWith (g := (· * ·)) hg3 h4,
        aux_length_crossWith (g := (· * ·)) h3 hg4]

/-- The value of every power row is the power of the value. -/
private theorem aux_val_power {x : PowerRow ℝ} {M N : List ℝ} (hM : x.G.length = M.length)
    (hN : x.GI.length = N.length) (i : ℕ) (hi : 1 ≤ i) : -- --- CONCL ---
    aux_val (PolyZonotope.step_power PowerOps.real x i) (PolyZonotope.powerExt (· * ·) M i)
        (aux_next M N i) = aux_val x M N ^ i := by -- --- PROOF ---
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [PolyZonotope.step_power.eq_1, PolyZonotope.powerExt.eq_1, aux_next.eq_1]
    split_ifs with h1 h2
    · have : i = 1 := by omega
      subst this; simp
    · have h3 := ih (i / 2) (by omega) (by omega)
      rw [aux_val_square (aux_length_power_G _ _ hM _) (aux_length_power_GI _ hM hN _), h3,
          ← pow_mul]
      congr 1; omega
    · have h3 := ih (i / 2) (by omega) (by omega)
      have h4 := ih ((i + 1) / 2) (by omega) (by omega)
      rw [aux_val_times (aux_length_power_G _ _ hM _) (aux_length_power_GI _ hM hN _)
        (aux_length_power_G _ _ hM _) (aux_length_power_GI _ hM hN _), h3, h4, ← pow_add]
      congr 1; omega


/-- Folding a power leaves the powers above it unchanged. -/
private theorem aux_foldAt_of_ge (o : PowerOps α) (len : ℕ → ℕ) (W : ℕ → List α) {i j : ℕ} (hi : 2
    ≤ i)
    (hj : i ≤ j) : PolyZonotope.step_foldAt o len W i j = W j := by
  simp only [PolyZonotope.step_foldAt, Function.update_apply]
  rw [if_neg (by omega), if_neg (by omega)]

/-- Folding down leaves the powers above the start unchanged. -/
private theorem aux_foldDown_of_ge (o : PowerOps α) (len : ℕ → ℕ) (k : ℕ) : -- --- CONCL ---
    ∀ (W : ℕ → List α) (j : ℕ), k ≤ j → PolyZonotope.step_foldDown o len W k j = W
        j := by -- --- PROOF ---
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro W j hj
    match k with
    | 0 => rfl
    | 1 => rfl
    | k + 2 =>
      simp only [PolyZonotope.step_foldDown]
      rw [ih (k + 1) (by omega) _ j (by omega), aux_foldAt_of_ge o len W (by omega) hj]

/-- Folding a power keeps the lengths. -/
private theorem aux_length_foldAt (o : PowerOps α) {len : ℕ → ℕ} {W : ℕ → List α}
    (hlen : ∀ j, (W j).length = len j) {i : ℕ} (hw : len (i / 2) + len ((i + 1) / 2) ≤ len i) :
    ∀ j, (PolyZonotope.step_foldAt o len W i j).length = len j := by
  intro j
  simp only [PolyZonotope.step_foldAt, Function.update_apply]
  split_ifs <;> simp_all <;> omega

/-- Folding down keeps the lengths. -/
private theorem aux_length_foldDown (o : PowerOps α) {len : ℕ → ℕ}
    (hw : ∀ i, 2 ≤ i → len (i / 2) + len ((i + 1) / 2) ≤ len i) (k : ℕ) : -- --- CONCL ---
    ∀ {W : ℕ → List α}, (∀ j, (W j).length = len j) →
      ∀ j, (PolyZonotope.step_foldDown o len W k j).length = len j := by -- --- PROOF ---
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro W hW
    match k with
    | 0 => exact hW
    | 1 => exact hW
    | k + 2 =>
      simp only [PolyZonotope.step_foldDown]
      exact ih (k + 1) (by omega) (aux_length_foldAt o hW (hw (k + 2) (by omega)))

/-- The dot product of a sum of lists. -/
private theorem aux_dot_zipWith_add {u P m : List ℝ} (h1 : u.length = m.length) (h2 : P.length =
    m.length) : -- --- CONCL ---
    aux_dot (List.zipWith (· + ·) u P) m = aux_dot u m + aux_dot P m := by -- --- PROOF ---
  induction u generalizing P m with
  | nil => cases m <;> simp_all [aux_dot]
  | cons x u ih => cases m with
    | nil => simp at h1
    | cons y m => cases P with
      | nil => simp at h2
      | cons z P =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
        simp only [List.zipWith_cons_cons, aux_dot_cons, ih h1 h2]; ring

/-- A sum after updating one summand. -/
private theorem aux_sum_update {W : ℕ → List ℝ} {mons : ℕ → List ℝ} {s : Finset ℕ} {a : ℕ}
    (ha : a ∈ s)
    (v : List ℝ) : -- --- CONCL ---
    ∑ i ∈ s, aux_dot (Function.update W a v i) (mons i)
      = ∑ i ∈ s, aux_dot (W i) (mons i) - aux_dot (W a) (mons a) + aux_dot v
          (mons a) := by -- --- PROOF ---
  have : (fun i => aux_dot (Function.update W a v i) (mons i))
      = Function.update (fun i => aux_dot (W i) (mons i)) a (aux_dot v (mons a)) := by
    funext i; by_cases h : i = a <;> simp [h]
  rw [this, Finset.sum_update_of_mem ha, ← Finset.add_sum_erase s _ ha,
      Finset.sdiff_singleton_eq_erase]
  ring


/-- The own parts up to `k + 1` are those up to `k` and the last one. -/
private theorem aux_own_succ (len : ℕ → ℕ) (F : ℕ → List α) (k : ℕ) : -- --- CONCL ---
    PolyZonotope.powerParts len F (k + 2) = PolyZonotope.powerParts len F (k + 1)
      ++ (F (k + 2)).drop (len ((k + 2) / 2) + len ((k + 3) / 2)) := by -- --- PROOF ---
  have e : ∀ f : ℕ → List α, (List.range' 2 (k + 1)).flatMap f
      = (List.range' 2 k).flatMap f ++ f (k + 2) := by
    intro f
    rw [List.range'_concat, List.flatMap_append, List.flatMap_singleton]
    congr 2; omega
  simp only [PolyZonotope.powerParts, show k + 2 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega,
      e,
    List.append_assoc]

/-- The length of the own parts. -/
private theorem aux_length_own {len : ℕ → ℕ} {F : ℕ → List α} {F' : ℕ → List β} (h : ∀ j, (F
    j).length = (F' j).length)
    (k : ℕ) : (PolyZonotope.powerParts len F k).length = (PolyZonotope.powerParts len F'
        k).length := by
  simp only [PolyZonotope.powerParts, List.length_append, List.length_flatMap, List.length_drop, h]

/-- Folding down keeps the value of all powers. -/
private theorem aux_dot_fold {len : ℕ → ℕ} {W mons : ℕ → List ℝ} (hW : ∀ j, (W j).length = len j)
    (hm : ∀ j, (mons j).length = len j)
    (hpre : ∀ j, 2 ≤ j → mons j = mons (j / 2) ++ mons ((j + 1) / 2)
      ++ (mons j).drop (len (j / 2) + len ((j + 1) / 2))) (k : ℕ) (hk : 1 ≤ k) : -- --- CONCL ---
    aux_dot (PolyZonotope.powerParts len (PolyZonotope.step_foldDown PowerOps.real len W k) k)
        (PolyZonotope.powerParts len mons k)
      = ∑ i ∈ Finset.Icc 1 k, aux_dot (W i) (mons i) := by -- --- PROOF ---
  have hw : ∀ i, 2 ≤ i → len (i / 2) + len ((i + 1) / 2) ≤ len i := by
    intro i hi
    have := congrArg List.length (hpre i hi)
    simp only [List.length_append, hm] at this
    omega
  induction k using Nat.strong_induction_on generalizing W with
  | _ k ih =>
    match k, hk with
    | 1, _ => simp [PolyZonotope.powerParts, PolyZonotope.step_foldDown, aux_dot]
    | k + 2, _ =>
      have hwk : len ((k + 2) / 2) + len ((k + 3) / 2) ≤ len (k + 2) := hw (k + 2) (by omega)
      have hW' := aux_length_foldAt PowerOps.real hW hwk
      have hF := aux_length_foldDown PowerOps.real hw (k + 1) hW'
      simp only [PolyZonotope.step_foldDown]
      rw [aux_own_succ, aux_own_succ, aux_dot_append (by rw [aux_length_own (fun j => (hF j).trans
          (hm j).symm)]),
        ih (k + 1) (by omega) hW' (by omega),
        aux_foldDown_of_ge PowerOps.real len (k + 1) _ (k + 2) (by omega),
        aux_foldAt_of_ge PowerOps.real len W (by omega) le_rfl]
      -- the sums: the two updates, then the last power
      have hs1 : (k + 2) / 2 ∈ Finset.Icc 1 (k + 1) := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have hs2 : (k + 3) / 2 ∈ Finset.Icc 1 (k + 1) := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have hP1 : ((W (k + 2)).take (len ((k + 2) / 2))).length = len ((k + 2) / 2) := by
        rw [List.length_take, hW]; omega
      have hP2 : (((W (k + 2)).drop (len ((k + 2) / 2))).take (len ((k + 3) / 2))).length
          = len ((k + 3) / 2) := by
        rw [List.length_take, List.length_drop, hW]; omega
      have hz1 := aux_dot_zipWith_add ((hW ((k + 2) / 2)).trans (hm _).symm) (hP1.trans (hm _).symm)
      have hW1 : ∀ j, (Function.update W ((k + 2) / 2)
          (List.zipWith (· + ·) (W ((k + 2) / 2)) ((W (k + 2)).take (len ((k + 2) / 2)))) j).length
            = len j := by
        intro j; simp only [Function.update_apply]; split_ifs with h
        · subst h; rw [List.length_zipWith, hW, hP1, min_self]
        · exact hW j
      have hz2 := aux_dot_zipWith_add ((hW1 ((k + 3) / 2)).trans (hm _).symm)
        (hP2.trans (hm _).symm)
      simp only [PolyZonotope.step_foldAt, PowerOps.real]
      rw [aux_sum_update hs2, aux_sum_update hs1, hz2]
      -- the last power's own dot product, split at its factors
      have hsplit : W (k + 2) = (W (k + 2)).take (len ((k + 2) / 2))
          ++ ((W (k + 2)).drop (len ((k + 2) / 2))).take (len ((k + 3) / 2))
          ++ (W (k + 2)).drop (len ((k + 2) / 2) + len ((k + 3) / 2)) := by
        rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
      have hlast : aux_dot (W (k + 2)) (mons (k + 2))
          = aux_dot ((W (k + 2)).take (len ((k + 2) / 2))) (mons ((k + 2) / 2))
            + aux_dot (((W (k + 2)).drop (len ((k + 2) / 2))).take (len ((k + 3) / 2)))
                (mons ((k + 3) / 2))
            + aux_dot ((W (k + 2)).drop (len ((k + 2) / 2) + len ((k + 3) / 2)))
                ((mons (k + 2)).drop (len ((k + 2) / 2) + len ((k + 3) / 2))) := by
        conv_lhs => rw [hsplit, hpre (k + 2) (by omega)]
        rw [aux_dot_append (by simp only [List.length_append, hP1, hP2, hm]),
          aux_dot_append (by rw [hP1, hm])]
      rw [Finset.sum_Icc_succ_top (a := 1) (b := k + 1) (by omega), hlast]
      by_cases heq : (k + 3) / 2 = (k + 2) / 2
      · rw [heq, Function.update_self, hz1] at *
        ring
      · rw [Function.update_of_ne heq, hz1]
        ring


/-- A sum over `1..k` as a sum over `range k`. -/
private theorem aux_sum_Icc_eq_range (f : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ Finset.Icc 1 k, f i = ∑ i ∈ Finset.range k, f (i + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- The polynomial as a sum of its terms, padded to `k + 1`. -/
private theorem aux_evalPolyReal_eq_range (v : ℝ) : -- --- CONCL ---
    ∀ (as : List ℝ) (k : ℕ), as.length ≤ k + 1 →
    PolyZonotope.evalPolyReal as v = ∑ i ∈ Finset.range (k + 1), as.getD i 0 * v ^
        i := by -- --- PROOF ---
  intro as
  induction as with
  | nil => intro k _; simp [PolyZonotope.evalPolyReal]
  | cons a rest ih =>
    intro k hk
    match k with
    | 0 =>
      have : rest.length = 0 := by simp only [List.length_cons] at hk; omega
      rw [List.length_eq_zero_iff] at this
      subst this; simp [PolyZonotope.evalPolyReal]
    | k + 1 =>
      have h1 := ih k (by simp only [List.length_cons] at hk; omega)
      rw [PolyZonotope.evalPolyReal, h1, Finset.sum_range_succ' _ (k + 1), Finset.mul_sum]
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
      rw [add_comm]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring

/-- The polynomial as a sum of its terms. -/
private theorem aux_evalPolyReal_eq (v : ℝ) (as : List ℝ) (k : ℕ) (hk : as.length ≤ k + 1) :
    PolyZonotope.evalPolyReal as v = as.getD 0 0 + ∑ i ∈ Finset.Icc 1 k, as.getD i 0 * v ^ i := by
  rw [aux_evalPolyReal_eq_range v as k hk, Finset.sum_range_succ', aux_sum_Icc_eq_range]
  simp [add_comm]

/-- A left sum over `range` as a `Finset` sum. -/
private theorem aux_foldl_range_eq (f : ℕ → ℝ) (k : ℕ) : -- --- CONCL ---
    (List.range' 1 k).foldl (fun acc i => acc + f i) 0 = ∑ i ∈ Finset.Icc 1 k, f
        i := by -- --- PROOF ---
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range'_concat, List.foldl_append, ih, Finset.sum_Icc_succ_top (by omega)]
    simp [add_comm 1 k]

/-- A power starts with the generators of its factors. -/
private theorem aux_pre_powerExt (f : β → β → β) (M : List β) (j : ℕ) (hj : 2 ≤ j)
    : -- --- CONCL ---
    PolyZonotope.powerExt f M j = PolyZonotope.powerExt f M (j / 2) ++ PolyZonotope.powerExt f M
        ((j + 1) / 2)
      ++ (PolyZonotope.powerExt f M j).drop ((PolyZonotope.powerExt f M (j / 2)).length
        + (PolyZonotope.powerExt f M ((j + 1) / 2)).length) := by -- --- PROOF ---
  conv_lhs => rw [PolyZonotope.powerExt.eq_1]
  rw [if_neg (by omega)]
  split_ifs with h
  · have e : (j + 1) / 2 = j / 2 := by omega
    rw [e, PolyZonotope.powerExt.eq_1 f M j, if_neg (by omega), if_pos h]
    simp [List.append_assoc]
  · rw [PolyZonotope.powerExt.eq_1 f M j, if_neg (by omega), if_neg h]
    simp [List.append_assoc]

/-- The pseudo-variables of a power start with those of its factors. -/
private theorem aux_pre_next (M N : List ℝ) (j : ℕ) (hj : 2 ≤ j) : -- --- CONCL ---
    aux_next M N j = aux_next M N (j / 2) ++ aux_next M N ((j + 1) / 2)
      ++ (aux_next M N j).drop ((aux_next M N (j / 2)).length
        + (aux_next M N ((j + 1) / 2)).length) := by -- --- PROOF ---
  conv_lhs => rw [aux_next.eq_1]
  rw [if_neg (by omega)]
  split_ifs with h
  · have e : (j + 1) / 2 = j / 2 := by omega
    rw [e, aux_next.eq_1 M N j, if_neg (by omega), if_pos h]
    simp [List.append_assoc]
  · rw [aux_next.eq_1 M N j, if_neg (by omega), if_neg h]
    simp [List.append_assoc]


/-- Scaled factors stay within `[-1, 1]`. -/
private theorem aux_bound_map {l : List ℝ} (hl : ∀ m ∈ l, |m| ≤ 1) {f : ℝ → ℝ}
    (hf : ∀ m, |m| ≤ 1 → |f m| ≤ 1) : ∀ m ∈ l.map f, |m| ≤ 1 := by
  intro m hm
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hm
  exact hf a (hl a ha)

/-- Products of factors stay within `[-1, 1]`. -/
private theorem aux_bound_mul {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a * b| ≤ 1 := by
  rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg b]

/-- The products of two lists of factors stay within `[-1, 1]`. -/
private theorem aux_bound_cross {a b : List ℝ} (ha : ∀ m ∈ a, |m| ≤ 1) (hb : ∀ m ∈ b, |m| ≤ 1) :
    ∀ m ∈ PolyZonotope.crossWith (· * ·) a b, |m| ≤ 1 := by
  intro m hm
  simp only [PolyZonotope.crossWith, List.mem_flatMap, List.mem_map] at hm
  obtain ⟨y, hy, x, hx, rfl⟩ := hm
  exact aux_bound_mul (ha x hx) (hb y hy)

/-- The pairs of factors stay within `[-1, 1]`. -/
private theorem aux_bound_pairs {a : List ℝ} (ha : ∀ m ∈ a, |m| ≤ 1) : -- --- CONCL ---
    ∀ m ∈ PolyZonotope.pairsWith (· * ·) a, |m| ≤ 1 := by -- --- PROOF ---
  induction a with
  | nil => simp [PolyZonotope.pairsWith]
  | cons x r ih =>
    intro m hm
    simp only [PolyZonotope.pairsWith, List.mem_append, List.mem_map] at hm
    rcases hm with ⟨y, hy, rfl⟩ | hm
    · exact aux_bound_mul (ha x (by simp)) (ha y (by simp [hy]))
    · exact ih (fun m hm => ha m (by simp [hm])) m hm

/-- The monomials of every power stay within `[-1, 1]`. -/
private theorem aux_bound_powerExt {M : List ℝ} (hM : ∀ m ∈ M, |m| ≤ 1) (i : ℕ) : -- --- CONCL ---
    ∀ m ∈ PolyZonotope.powerExt (· * ·) M i, |m| ≤ 1 := by -- --- PROOF ---
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [PolyZonotope.powerExt.eq_1]
    split_ifs with h1 h2
    · exact hM
    · have hA := ih (i / 2) (by omega)
      intro m hm
      simp only [List.mem_append] at hm
      rcases hm with ((hm | hm) | hm) | hm
      · exact hA m hm
      · exact hA m hm
      · exact aux_bound_map hA (fun a ha => aux_bound_mul ha ha) m hm
      · exact aux_bound_pairs hA m hm
    -- an odd power: the factors and their products
    · have hA := ih (i / 2) (by omega)
      have hB := ih ((i + 1) / 2) (by omega)
      intro m hm
      simp only [List.mem_append] at hm
      rcases hm with (hm | hm) | hm
      · exact hA m hm
      · exact hB m hm
      · exact aux_bound_cross hA hB m hm

/-- The pseudo-variables stay within `[-1, 1]`. -/
private theorem aux_bound_next {M N : List ℝ} (hM : ∀ m ∈ M, |m| ≤ 1) (hN : ∀ m ∈ N, |m| ≤ 1)
    (i : ℕ) : -- --- CONCL ---
    ∀ m ∈ aux_next M N i, |m| ≤ 1 := by -- --- PROOF ---
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [aux_next.eq_1]
    split_ifs with h1 h2
    · exact hN
    · have hA := ih (i / 2) (by omega)
      have hAM := aux_bound_powerExt hM (i / 2)
      intro m hm
      simp only [List.mem_append] at hm
      rcases hm with (((hm | hm) | hm) | hm) | hm
      · exact hA m hm
      · exact hA m hm
      -- `2β² - 1` of a factor in `[-1, 1]`
      · refine aux_bound_map hA (fun a ha => ?_) m hm
        rw [abs_le] at ha ⊢
        constructor <;> nlinarith
      · exact aux_bound_pairs hA m hm
      · exact aux_bound_cross hA hAM m hm
    -- an odd power: the factors and the products of the two halves
    · have hA := ih (i / 2) (by omega)
      have hB := ih ((i + 1) / 2) (by omega)
      have hAM := aux_bound_powerExt hM (i / 2)
      have hBM := aux_bound_powerExt hM ((i + 1) / 2)
      intro m hm
      simp only [List.mem_append] at hm
      rcases hm with ((((hm | hm) | hm) | hm) | hm)
      · exact hA m hm
      · exact hB m hm
      · exact aux_bound_cross hA hB m hm
      · exact aux_bound_cross hAM hB m hm
      · exact aux_bound_cross hA hBM m hm

/-- The own monomials stay within `[-1, 1]`. -/
private theorem aux_bound_own {F : ℕ → List ℝ} (hF : ∀ j, ∀ m ∈ F j, |m| ≤ 1) (len : ℕ → ℕ)
    (k : ℕ) : -- --- CONCL ---
    ∀ m ∈ PolyZonotope.powerParts len F k, |m| ≤ 1 := by -- --- PROOF ---
  intro m hm
  simp only [PolyZonotope.powerParts, List.mem_append, List.mem_flatMap] at hm
  rcases hm with hm | ⟨i, _, hm⟩
  · exact hF 1 m hm
  · exact hF i m (List.mem_of_mem_drop hm)


/-- The addition of the real operations. -/
@[simp] private theorem aux_realOps_add (a b : ℝ) : PowerOps.real.add a b = a + b := rfl
/-- The multiplication of the real operations. -/
@[simp] private theorem aux_realOps_mul (a b : ℝ) : PowerOps.real.mul a b = a * b := rfl
/-- The zero of the real operations. -/
@[simp] private theorem aux_realOps_zero : PowerOps.real.zero = 0 := rfl

/-- Weighing the generators by a coefficient scales the dot product. -/
private theorem aux_dot_map_mul_right (c : ℝ) (a A : List ℝ) :
    aux_dot (a.map (· * c)) A = aux_dot a A * c :=
  aux_dot_map_right c a A

/-- The value of the run, with the pseudo-variables named. -/
private theorem aux_evalPowersList_value {M N : List ℝ} (hM : ∀ m ∈ M, |m| ≤ 1)
    (hN : ∀ m ∈ N, |m| ≤ 1) (k : ℕ) : -- --- CONCL ---
    ∃ N' : List ℝ, (∀ m ∈ N', |m| ≤ 1) ∧ ∀ as : List ℝ, max 1 (as.length - 1) = k →
      ∀ x : PowerRow ℝ, x.G.length = M.length → x.GI.length = N.length →
      (PolyZonotope.evalPowersList PowerOps.real as x).GI.length = N'.length ∧
      aux_val (PolyZonotope.evalPowersList PowerOps.real as x)
          (PolyZonotope.powerOut (· * ·) M k) N'
        = PolyZonotope.evalPolyReal as (aux_val x M N) := by -- --- PROOF ---
  refine ⟨PolyZonotope.powerParts (fun i => (aux_next M N i).length) (aux_next M N) k,
    aux_bound_own (aux_bound_next hM hN) _ _, fun as hk x hxM hxN => ?_⟩
  subst hk
  set k := max 1 (as.length - 1) with hk
  -- the lengths of the powers and of the weighed powers
  have hlG : (fun i => (PolyZonotope.step_power PowerOps.real x i).G.length) =
      fun i => (PolyZonotope.powerExt (· * ·) M i).length :=
    funext (aux_length_power_G PowerOps.real (· * ·) hxM)
  have hlGI : (fun i => (PolyZonotope.step_power PowerOps.real x i).GI.length) =
      fun i => (aux_next M N i).length :=
    funext (aux_length_power_GI PowerOps.real hxM hxN)
  have hwG : ∀ j, ((PolyZonotope.step_weigh PowerOps.real (as.getD j PowerOps.real.zero)
      (PolyZonotope.step_power PowerOps.real x j)).G).length
      = (PolyZonotope.powerExt (· * ·) M j).length := fun j => by
    simp [PolyZonotope.step_weigh, aux_length_power_G PowerOps.real (· * ·) hxM j]
  have hwGI : ∀ j, ((PolyZonotope.step_weigh PowerOps.real (as.getD j PowerOps.real.zero)
      (PolyZonotope.step_power PowerOps.real x j)).GI).length
      = (aux_next M N j).length := fun j => by
    simp [PolyZonotope.step_weigh, aux_length_power_GI PowerOps.real hxM hxN j]
  have hk1 : 1 ≤ k := le_max_left _ _
  -- the number of independent generators, then the value
  constructor
  · simp only [PolyZonotope.evalPowersList, ← hk, hlGI]
    exact aux_length_own (aux_length_foldDown PowerOps.real
      (fun i hi => by have := congrArg List.length (aux_pre_next M N i hi); simp at this; omega)
      k hwGI) k
  · simp only [PolyZonotope.evalPowersList, ← hk, hlG, hlGI, aux_val, PolyZonotope.powerOut]
    rw [aux_dot_fold hwG (fun _ => rfl) (fun j hj => aux_pre_powerExt _ M j hj) k hk1,
      aux_dot_fold hwGI (fun _ => rfl) (fun j hj => aux_pre_next M N j hj) k hk1,
      aux_evalPolyReal_eq _ as k (by omega)]
    simp only [aux_realOps_add, aux_realOps_zero]
    rw [aux_foldl_range_eq]
    simp only [PolyZonotope.step_weigh, aux_realOps_mul, aux_dot_map_mul_right]
    -- every term of the polynomial is the value of its weighed power
    have hv : ∀ i ∈ Finset.Icc 1 k, as.getD i 0 * (x.c + aux_dot x.G M + aux_dot x.GI N) ^ i
        = (PolyZonotope.step_power PowerOps.real x i).c * as.getD i 0
          + aux_dot (PolyZonotope.step_power PowerOps.real x i).G
              (PolyZonotope.powerExt (· * ·) M i) * as.getD i 0
          + aux_dot (PolyZonotope.step_power PowerOps.real x i).GI (aux_next M N i)
              * as.getD i 0 := by
      intro i hi
      have := aux_val_power hxM hxN i (Finset.mem_Icc.1 hi).1
      simp only [aux_val] at this
      rw [← this]; ring
    rw [Finset.sum_congr rfl hv, Finset.sum_add_distrib, Finset.sum_add_distrib]
    ring


/-- The number of dependent generators of the run. -/
private theorem aux_length_evalPowersList_G (o : PowerOps α) (f : β → β → β) {as : List α}
    {x : PowerRow α} {M : List β} (hM : x.G.length = M.length) : -- --- CONCL ---
    (PolyZonotope.evalPowersList o as x).G.length = (PolyZonotope.powerOut f M (max 1 (as.length -
        1))).length := by -- --- PROOF ---
  have hlG : (fun i => (PolyZonotope.step_power o x i).G.length) = fun i => (PolyZonotope.powerExt
      f M i).length :=
    funext (aux_length_power_G o f hM)
  simp only [PolyZonotope.evalPowersList, hlG, PolyZonotope.powerOut]
  refine aux_length_own (F' := PolyZonotope.powerExt f M) (fun j => ?_) _
  refine aux_length_foldDown o (fun i hi => ?_) _ (fun j => ?_) j
  · have := congrArg List.length (aux_pre_powerExt f M i hi); simp at this; omega
  · simp [PolyZonotope.step_weigh, aux_length_power_G o f hM j]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.evalPowersList_value {M N : List ℝ} (hM : ∀ m ∈ M, |m| ≤ 1)
    (hN : ∀ m ∈ N, |m| ≤ 1) (k : ℕ) : -- --- CONCL ---
    ∃ N' : List ℝ, (∀ m ∈ N', |m| ≤ 1) ∧ ∀ as : List ℝ, max 1 (as.length - 1) = k →
      ∀ x : PowerRow ℝ, x.G.length = M.length → x.GI.length = N.length →
      (PolyZonotope.evalPowersList PowerOps.real as x).G.length
          = (PolyZonotope.powerOut (· * ·) M k).length
        ∧ (PolyZonotope.evalPowersList PowerOps.real as x).GI.length = N'.length
        ∧ (PolyZonotope.evalPowersList PowerOps.real as x).c
            + (List.zipWith (· * ·) (PolyZonotope.evalPowersList PowerOps.real as x).G
              (PolyZonotope.powerOut (· * ·) M k)).sum
            + (List.zipWith (· * ·) (PolyZonotope.evalPowersList PowerOps.real as x).GI N').sum
          = PolyZonotope.evalPolyReal as
            (x.c + (List.zipWith (· * ·) x.G M).sum +
                (List.zipWith (· * ·) x.GI N).sum) := by -- --- PROOF ---
  obtain ⟨N', hN'b, hN'⟩ := aux_evalPowersList_value hM hN k
  refine ⟨N', hN'b, fun as hk x hxM hxN => ?_⟩
  obtain ⟨hlen, hval⟩ := hN' as hk x hxM hxN
  refine ⟨?_, hlen, hval⟩
  rw [aux_length_evalPowersList_G PowerOps.real (· * ·) hxM, hk]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
