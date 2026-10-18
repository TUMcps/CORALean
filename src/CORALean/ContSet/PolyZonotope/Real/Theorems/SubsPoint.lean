module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Subs
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialReplaceId
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Pi
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialSplit

@[expose] public section

/-!
# `subs` is the substitution

`subs_point`: the result evaluated at the factors `a` is `pZ` evaluated at the factor vector in
which each replaced factor `idu ii` takes the value of output `ii` of `pZin` (at `pZin`'s factors
read off `a` through `subsFactor`) and every other factor keeps its value. The expansion into terms
is only bookkeeping: a sum of terms evaluates to the product of the evaluations
(`aux_evalTerms_subsMul`), a power to the power, and the factors' exponents of a shared identifier
add (`ReplaceIdPoint`). `subs_construct` is the set equality; the independent block is `pZ`'s.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The value of a sum of monomials at `β`. -/
noncomputable def PolyZonotope.aux_evalTerms {p : ℕ} (l : List (ℝ × (Fin p → ℕ))) (β : Fin p → ℝ) :
    ℝ :=
  (l.map fun t => t.1 * ∏ j, β j ^ t.2 j).sum

/-- The value of a product of sums of monomials is the product of the values. -/
theorem PolyZonotope.aux_evalTerms_subsMul {p : ℕ} (A B : List (ℝ × (Fin p → ℕ))) (β : Fin p → ℝ) :
    PolyZonotope.aux_evalTerms (PolyZonotope.subsMul A B) β
      = PolyZonotope.aux_evalTerms A β * PolyZonotope.aux_evalTerms B β := by -- --- PROOF ---
  -- induction on the first factor, one term at a time
  unfold PolyZonotope.aux_evalTerms PolyZonotope.subsMul
  induction A with
  | nil => simp
  | cons s A ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons,
      add_mul]
    congr 1
    rw [List.map_map]
    have h1 : B.map ((fun t : ℝ × (Fin p → ℕ) => t.1 * ∏ j, β j ^ t.2 j)
          ∘ fun t => (s.1 * t.1, s.2 + t.2))
        = B.map (fun t => (s.1 * ∏ j, β j ^ s.2 j) * (t.1 * ∏ j, β j ^ t.2 j)) :=
      List.map_congr_left fun t _ => by
        simp only [Function.comp, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
        ring
    rw [h1, List.sum_map_mul_left, mul_comm]

/-- The value of a power of a sum of monomials is the power of the value. -/
theorem PolyZonotope.aux_evalTerms_subsPow {p : ℕ} (A : List (ℝ × (Fin p → ℕ))) (β : Fin p → ℝ)
    (d : ℕ) : PolyZonotope.aux_evalTerms (PolyZonotope.subsPow A d) β
      = PolyZonotope.aux_evalTerms A β ^ d := by
  induction d with
  | zero => simp [PolyZonotope.subsPow, PolyZonotope.aux_evalTerms]
  | succ d ih => rw [PolyZonotope.subsPow, PolyZonotope.aux_evalTerms_subsMul, ih, pow_succ']

/-- The value of output `ii`'s polynomial is `pZin`'s point there. -/
theorem PolyZonotope.aux_evalTerms_subsPoly {nu : ℕ} (pZin : PolyZonotope (Vec ℝ nu))
    (β : Fin pZin.p → ℝ) (ii : Fin nu) :
    PolyZonotope.aux_evalTerms (pZin.subsPoly ii) β = pZin.point β ii := by -- --- PROOF ---
  -- the center term, then the generators one by one
  unfold PolyZonotope.aux_evalTerms PolyZonotope.subsPoly PolyZonotope.point
  rw [List.map_cons, List.sum_cons, List.map_map, Pi.add_apply, Finset.sum_apply]
  simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one, mul_one]
  congr 1
  rw [Fin.sum_univ_def]
  refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
  simp only [Function.comp, Pi.smul_apply, smul_eq_mul, PolyZonotope.monomial]
  ring

/-- The value of the fold over the outputs is the product of the powers' values. -/
theorem PolyZonotope.aux_evalTerms_foldl {nu p : ℕ} (Pol : Fin nu → List (ℝ × (Fin p → ℕ)))
    (e : Fin nu → ℕ) (β : Fin p → ℝ) (L : List (Fin nu))
    (acc : List (ℝ × (Fin p → ℕ))) : -- --- STMT ---
    PolyZonotope.aux_evalTerms
        (L.foldl (fun acc ii => PolyZonotope.subsMul acc (PolyZonotope.subsPow (Pol ii) (e ii)))
          acc) β
      = PolyZonotope.aux_evalTerms acc β
        * (L.map fun ii => PolyZonotope.aux_evalTerms (Pol ii) β ^ e ii).prod := by -- --- PROOF ---
  induction L generalizing acc with
  | nil => simp
  | cons ii L ih =>
    rw [List.foldl_cons, ih, PolyZonotope.aux_evalTerms_subsMul,
      PolyZonotope.aux_evalTerms_subsPow, List.map_cons, List.prod_cons, mul_assoc]

omit [AddCommGroup α] [Module ℝ α] in
/-- The value of generator `i`'s `Xprod` is the product of the outputs' powers. -/
theorem PolyZonotope.aux_evalTerms_subsXprod (pZ : PolyZonotope α) {nu : ℕ}
    (pZin : PolyZonotope (Vec ℝ nu)) (idu : Fin nu → Fin pZ.p) (β : Fin pZin.p → ℝ)
    (i : Fin pZ.h) : -- --- STMT ---
    PolyZonotope.aux_evalTerms (pZ.subsXprod pZin idu i) β
      = ∏ ii, pZin.point β ii ^ pZ.E (idu ii) i := by -- --- PROOF ---
  -- the fold, then the `Xprod`'s start and the outputs' polynomials
  unfold PolyZonotope.subsXprod
  rw [PolyZonotope.aux_evalTerms_foldl (fun ii => pZin.subsPoly ii) (fun ii => pZ.E (idu ii) i),
    Fin.prod_univ_def]
  simp only [PolyZonotope.aux_evalTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Pi.zero_apply, pow_zero, Finset.prod_const_one, mul_one, add_zero, one_mul]
  refine congrArg List.prod (List.map_congr_left fun ii _ => ?_)
  rw [← PolyZonotope.aux_evalTerms_subsPoly]
  rfl

/-- The sum over the terms is the sum over the generators of the sums over their `Xprod`. -/
theorem PolyZonotope.aux_sum_flatMap {h : ℕ} {γ β : Type} [AddCommMonoid β] (T : Fin h → List γ)
    (L : List (Fin h)) (F : Fin h × γ → β) :
    ((L.flatMap fun i => (T i).map fun t => (i, t)).map F).sum
      = (L.map fun i => ((T i).map fun t => F (i, t)).sum).sum := by
  induction L with
  | nil => simp
  | cons i L ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_map,
      List.map_cons, List.sum_cons]; rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- `subs` is the substitution: at a factor vector `a`, the result is `pZ` at the factors in which
each replaced `idu ii` has the value of output `ii` of `pZin` at `pZin`'s factors, read off `a`
through `subsFactor`. -/
theorem PolyZonotope.subs_point (pZ : PolyZonotope α) {nu : ℕ} (pZin : PolyZonotope (Vec ℝ nu))
    (idu : Fin nu → Fin pZ.p) (share : Fin pZin.p → Option (Fin pZ.p))
    (hidu : Function.Injective idu) (a : Fin (pZ.subs pZin idu share).p → ℝ) : -- --- STMT ---
    (pZ.subs pZin idu share).point a
      = pZ.point (Function.extend idu
          (fun ii => pZin.point (fun j => a (pZ.subsFactor pZin share j)) ii)
          (fun k => a (Fin.castAdd pZin.p k))) := by -- --- PROOF ---
  classical
  set β : Fin pZin.p → ℝ := fun j => a (pZ.subsFactor pZin share j) with hβ
  set S : Finset (Fin pZ.p) := Finset.univ.image idu with hS
  set T := pZ.subsTerms pZin idu with hT
  -- the monomial of a term: the factors of `pZ` outside the replaced ones, and those of `pZin`
  have hmon : ∀ l : Fin T.length, PolyZonotope.monomial (pZ.subs pZin idu share).E a l
      = (∏ k, a (Fin.castAdd pZin.p k) ^ (if k ∈ S then 0 else pZ.E k (T.get l).1))
        * ∏ j, β j ^ (T.get l).2.2 j := by
    intro l
    unfold PolyZonotope.monomial
    have hE : ∀ r : Fin (pZ.p + pZin.p), (pZ.subs pZin idu share).E r l
        = Fin.addCases (fun k => if k ∈ S then 0 else pZ.E k (T.get l).1) (fun _ => 0) r
          + ∑ j ∈ Finset.univ.filter (fun j => pZ.subsFactor pZin share j = r), (T.get l).2.2 j :=
      fun r => rfl
    simp_rw [hE, pow_add, Finset.prod_mul_distrib]
    congr 1
    · refine (Fin.prod_univ_add (fun r : Fin (pZ.p + pZin.p) => a r ^
        (Fin.addCases (fun k => if k ∈ S then 0 else pZ.E k (T.get l).1) (fun _ => 0) r))).trans ?_
      simp
    · have := PolyZonotope.monomial_replaceId (fun j (_ : Fin 1) => (T.get l).2.2 j)
        (pZ.subsFactor pZin share) a 0
      unfold PolyZonotope.monomial at this
      exact this
  -- the monomial of `pZ` at the substituted factors
  set ã := Function.extend idu (fun ii => pZin.point β ii) (fun k => a (Fin.castAdd pZin.p k))
    with hã
  have hP : ∀ i, PolyZonotope.monomial pZ.E ã i
      = (∏ k, a (Fin.castAdd pZin.p k) ^ (if k ∈ S then 0 else pZ.E k i))
        * ∏ ii, pZin.point β ii ^ pZ.E (idu ii) i := by
    intro i
    rw [PolyZonotope.monomial_split pZ.E S ã i]
    congr 1
    · refine Finset.prod_congr rfl fun k _ => ?_
      by_cases hk : k ∈ S
      · simp [hk]
      · have hk' : ¬ ∃ ii, idu ii = k := fun ⟨ii, h⟩ =>
          hk (Finset.mem_image.mpr ⟨ii, Finset.mem_univ _, h⟩)
        rw [hã, Function.extend_apply' _ _ _ hk']
    · rw [hS, Finset.prod_image (fun x _ y _ h => hidu h)]
      exact Finset.prod_congr rfl fun ii _ => by rw [hã, hidu.extend_apply]
  unfold PolyZonotope.point
  congr 1
  -- the summand of a term
  let F : Fin pZ.h × (ℝ × (Fin pZin.p → ℕ)) → α := fun x =>
    ((∏ k, a (Fin.castAdd pZin.p k) ^ (if k ∈ S then 0 else pZ.E k x.1))
      * (x.2.1 * ∏ j, β j ^ x.2.2 j)) • pZ.G x.1
  -- a term's contribution is its coefficient times the monomials, scaling the original generator
  have hG : ∀ l : Fin T.length, PolyZonotope.monomial (pZ.subs pZin idu share).E a l
      • (pZ.subs pZin idu share).G l = F (T.get l) := by
    intro l
    rw [hmon l]
    show _ • ((T.get l).2.1 • pZ.G (T.get l).1) = _
    rw [smul_smul]
    exact congrArg (fun c => c • pZ.G (T.get l).1) (by ring)
  -- the sum over the terms is the sum over the generators of the sums over their `Xprod`
  have hsum : ∑ l : Fin T.length, PolyZonotope.monomial (pZ.subs pZin idu share).E a l
      • (pZ.subs pZin idu share).G l = ∑ i, PolyZonotope.monomial pZ.E ã i • pZ.G i := by
    rw [Finset.sum_congr rfl fun l _ => hG l]
    have h1 := Fin.sum_univ_fun_getElem T F
    have h2 : ∑ l : Fin T.length, F (T.get l) = (T.map F).sum := h1
    rw [h2, hT, PolyZonotope.subsTerms, PolyZonotope.aux_sum_flatMap, Fin.sum_univ_def]
    refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
    -- the generator's terms sum to the monomial in the replaced factors, by `aux_evalTerms`
    rw [hP i, ← PolyZonotope.aux_evalTerms_subsXprod pZ pZin idu β i]
    have hsm : ∀ (L : List ℝ) (g : α), (L.map fun c => c • g).sum = L.sum • g := by
      intro L g
      induction L with
      | nil => simp
      | cons c L ih => simp [ih, add_smul]
    calc ((pZ.subsXprod pZin idu i).map fun t => F (i, t)).sum
        = (((pZ.subsXprod pZin idu i).map fun t =>
            (∏ k, a (Fin.castAdd pZin.p k) ^ (if k ∈ S then 0 else pZ.E k i))
              * (t.1 * ∏ j, β j ^ t.2 j)).sum) • pZ.G i := by
          rw [← hsm, List.map_map]
          rfl
      _ = ((∏ k, a (Fin.castAdd pZin.p k) ^ (if k ∈ S then 0 else pZ.E k i))
            * PolyZonotope.aux_evalTerms (pZ.subsXprod pZin idu i) β) • pZ.G i := by
          rw [List.sum_map_mul_left]
          rfl
  exact hsum

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
