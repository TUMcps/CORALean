import CORALean.ContSet.ConPolyZono.Real.Operations.Rescale
import CORALean.ContSet.ConPolyZono.Real.Theorems.GetSubsetSatisfies
import Mathlib.Tactic.FieldSimp

/-!
# `rescale` does not change the set

Re-parametrizing the factors onto a box that holds every solution of the constraints
loses no point and adds none: the denoted set is the same, [1, Prop. 14] applied factor
by factor. The one assumption is the contractor's: the box it returns lies in the box
it was given, keeps every factor vector that satisfies the constraints, and is not empty
(CORA throws `CORA:emptySet` otherwise).

The proof follows the substitution through the first `n` factors. After them the set
is described by the original constraints and generators read at the factor vector
`αₖ ↦ cenₖ + radₖ·αₖ` on those factors, which is an invariant of `rescaleStep`
and the content of `getSubset_construct`'s two halves. Factor vectors are
`ℕ`-indexed there, so that sets with different but equal factor counts compare
without casts.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The factor vector after the first `n` factors have been sent to `cen ± rad`. -/
def ConPolyZono.aux_rescaleSub (cen rad : ℕ → ℝ) (n : ℕ) (a : ℕ → ℝ) : ℕ → ℝ :=
  fun k => if k < n then cen k + rad k * a k else a k

/-- What `n` steps of `rescaleStep` leave: the factor counts, the independent block, and
the constraints and generators as the original's, read at `rescaleSub`. -/
def ConPolyZono.aux_RescaleInv (cPZ acc : ConPolyZono α) (cen rad : ℕ → ℝ) (n : ℕ) : Prop :=
  acc.p = cPZ.p ∧ acc.q = cPZ.q
  ∧ (∀ β : ℕ → ℝ, ∑ j : Fin acc.q, β j • acc.GI j = ∑ j : Fin cPZ.q, β j • cPZ.GI j)
  ∧ (∀ a : ℕ → ℝ, acc.satisfies (fun k : Fin acc.p => a k)
      ↔ cPZ.satisfies (fun k : Fin cPZ.p => ConPolyZono.aux_rescaleSub cen rad n a k))
  ∧ (∀ a : ℕ → ℝ, acc.c + ∑ i, PolyZonotope.monomial acc.E (fun k : Fin acc.p => a k) i • acc.G i
      = cPZ.c + ∑ i, PolyZonotope.monomial cPZ.E
          (fun k : Fin cPZ.p => ConPolyZono.aux_rescaleSub cen rad n a k) i • cPZ.G i)

theorem ConPolyZono.aux_rescaleSub_succ (cen rad : ℕ → ℝ) (n : ℕ) (a : ℕ → ℝ) :
    ConPolyZono.aux_rescaleSub cen rad (n + 1) a
      = ConPolyZono.aux_rescaleSub cen rad n
          (Function.update a n (cen n + rad n * a n)) := by -- --- PROOF ---
  -- compare the two sides at `k` below, at, and above `n`
  funext k
  simp only [ConPolyZono.aux_rescaleSub]
  rcases lt_trichotomy k n with hk | hk | hk
  · rw [if_pos (by omega), if_pos hk, Function.update_of_ne (by omega)]
  · subst hk
    rw [if_pos (by omega), if_neg (by omega), Function.update_self]
  · rw [if_neg (by omega), if_neg (by omega), Function.update_of_ne (by omega)]

theorem ConPolyZono.aux_fin_update {m n : ℕ} (h : n < m) (a : ℕ → ℝ) (y : ℝ) :
    (fun k : Fin m => Function.update a n y (k : ℕ))
      = Function.update (fun k : Fin m => a k) ⟨n, h⟩ y := by -- --- PROOF ---
  -- the coordinate `n` is the updated one, the others are read off `a`
  funext k
  by_cases hk : k = ⟨n, h⟩
  · subst hk; simp
  · rw [Function.update_of_ne hk, Function.update_of_ne]
    intro h'
    exact hk (Fin.ext h')

theorem ConPolyZono.aux_rescaleInv_zero (cPZ : ConPolyZono α) (cen rad : ℕ → ℝ) :
    ConPolyZono.aux_RescaleInv cPZ cPZ cen rad 0 := by
  -- nothing has been substituted yet: the invariant's substitution is the identity
  refine ⟨rfl, rfl, fun _ => rfl, fun a => ?_, fun a => ?_⟩
  · simp [ConPolyZono.aux_rescaleSub]
  · simp [ConPolyZono.aux_rescaleSub]

theorem ConPolyZono.aux_rescaleInv_succ (cPZ acc : ConPolyZono α) (cen rad : ℕ → ℝ) (n : ℕ)
    (hn : n < cPZ.p) (hinv : ConPolyZono.aux_RescaleInv cPZ acc cen rad n) :
    ConPolyZono.aux_RescaleInv cPZ (ConPolyZono.rescaleStep cen rad acc n) cen rad
      (n + 1) := by -- --- PROOF ---
  obtain ⟨hp, hq, hGI, hsat, hpt⟩ := hinv
  have h : n < acc.p := hp ▸ hn
  unfold ConPolyZono.rescaleStep
  rw [dif_pos h]
  -- the counts and the independent block are untouched; the constraints and the point follow
  refine ⟨hp, hq, fun β => hGI β, fun a => ?_, fun a => ?_⟩
  · -- the constraints: `getSubset_satisfies` then the invariant at the updated vector
    rw [ConPolyZono.aux_rescaleSub_succ]
    have h1 := ConPolyZono.getSubset_satisfies acc ⟨n, h⟩ (cen n) (rad n) (fun k => a k)
    have h2 := hsat (Function.update a n (cen n + rad n * a n))
    rw [ConPolyZono.aux_fin_update h] at h2
    exact h1.trans (by simpa using h2)
  · -- the point: `getSubset_point` then the invariant at the updated vector
    rw [ConPolyZono.aux_rescaleSub_succ]
    have h1 := PolyZonotope.getSubset_point acc.toPolyZonotope ⟨n, h⟩ (cen n) (rad n)
      (fun k => a k)
    have h2 := hpt (Function.update a n (cen n + rad n * a n))
    rw [ConPolyZono.aux_fin_update h] at h2
    exact h1.trans h2

theorem ConPolyZono.aux_rescaleInv_fold (cPZ : ConPolyZono α) (cen rad : ℕ → ℝ) (n : ℕ)
    (hn : n ≤ cPZ.p) :
    ConPolyZono.aux_RescaleInv cPZ ((List.range n).foldl (ConPolyZono.rescaleStep cen rad) cPZ)
      cen rad n := by -- --- PROOF ---
  induction n with
  | zero => exact ConPolyZono.aux_rescaleInv_zero cPZ cen rad
  | succ n ih =>
    -- the `n + 1`-st step is `rescaleStep` at `n`
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact ConPolyZono.aux_rescaleInv_succ cPZ _ cen rad n (by omega) (ih (by omega))

/-- Membership, with factor vectors on `ℕ` so that the counts need no casts. -/
theorem ConPolyZono.aux_mem_construct_nat (acc : ConPolyZono α) (x : α) :
    x ∈ acc.construct ↔ ∃ a β : ℕ → ℝ, (∀ k, k < acc.p → |a k| ≤ 1)
      ∧ (∀ j, j < acc.q → |β j| ≤ 1) ∧ acc.satisfies (fun k : Fin acc.p => a k)
      ∧ x = acc.c + ∑ i, PolyZonotope.monomial acc.E (fun k : Fin acc.p => a k) i • acc.G i
          + ∑ j : Fin acc.q, β j • acc.GI j := by -- --- PROOF ---
  constructor
  · rintro ⟨a, β, ha, hβ, hs, hx⟩
    refine ⟨fun n => if h : n < acc.p then a ⟨n, h⟩ else 0,
      fun n => if h : n < acc.q then β ⟨n, h⟩ else 0, ?_, ?_, ?_, ?_⟩
    · intro k hk; simpa [hk] using ha ⟨k, hk⟩
    · intro j hj; simpa [hj] using hβ ⟨j, hj⟩
    · simpa using hs
    · simpa using hx
  · rintro ⟨a, β, ha, hβ, hs, hx⟩
    exact ⟨fun k => a k, fun j => β j, fun k => ha k k.2, fun j => hβ j j.2, hs, hx⟩

/-- Any box `dom` inside `[-1,1]ᵖ` that keeps every factor vector satisfying the constraints
leaves the set unchanged when the factors are rescaled onto it. -/
theorem ConPolyZono.aux_rescale_exact_of_box (cPZ : ConPolyZono α)
    (dom : Interval (Vec ℝ cPZ.p))
    (hb : ∀ k, -1 ≤ dom.inf k ∧ dom.inf k ≤ dom.sup k ∧ dom.sup k ≤ 1)
    (hk : ∀ a : Fin cPZ.p → ℝ, (∀ k, |a k| ≤ 1) → cPZ.satisfies a →
      ∀ k, dom.inf k ≤ a k ∧ a k ≤ dom.sup k) :
    ((List.range cPZ.p).foldl (ConPolyZono.rescaleStep
        (fun r => if h : r < cPZ.p then (dom.inf ⟨r, h⟩ + dom.sup ⟨r, h⟩) / 2 else 0)
        (fun r => if h : r < cPZ.p then (dom.sup ⟨r, h⟩ - dom.inf ⟨r, h⟩) / 2 else 0))
      cPZ).construct
      = cPZ.construct := by -- --- PROOF ---
  -- the centre and radius of the box, and the invariant after all `p` steps
  set cen : ℕ → ℝ := fun r => if h : r < cPZ.p then (dom.inf ⟨r, h⟩ + dom.sup ⟨r, h⟩) / 2 else 0
    with hcen
  set rad : ℕ → ℝ := fun r => if h : r < cPZ.p then (dom.sup ⟨r, h⟩ - dom.inf ⟨r, h⟩) / 2 else 0
    with hrad
  obtain ⟨hp, hq, hGI, hsat, hpt⟩ := ConPolyZono.aux_rescaleInv_fold cPZ cen rad cPZ.p le_rfl
  set acc := (List.range cPZ.p).foldl (ConPolyZono.rescaleStep cen rad) cPZ with hacc
  have hcen' : ∀ k : Fin cPZ.p, cen k = (dom.inf k + dom.sup k) / 2 := fun k => by
    simp [hcen, k.2]
  have hrad' : ∀ k : Fin cPZ.p, rad k = (dom.sup k - dom.inf k) / 2 := fun k => by
    simp [hrad, k.2]
  have hsub : ∀ (a : ℕ → ℝ) (k : Fin cPZ.p),
      ConPolyZono.aux_rescaleSub cen rad cPZ.p a k = cen k + rad k * a k := fun a k => by
    simp [ConPolyZono.aux_rescaleSub, k.2]
  -- both sets in the `ℕ`-indexed form, so that the two factor counts need no cast
  ext x
  rw [ConPolyZono.aux_mem_construct_nat, ConPolyZono.aux_mem_construct_nat]
  constructor
  · -- a point of the rescaled set is the original's at the substituted factors
    rintro ⟨a, β, ha, hβ, hs, hx⟩
    refine ⟨ConPolyZono.aux_rescaleSub cen rad cPZ.p a, β, ?_, fun j hj => hβ j (by omega), ?_, ?_⟩
    · -- the substituted factor stays in `[-1,1]`, the box lying inside it
      intro k hk
      have hb' := hb ⟨k, hk⟩
      have h1 := ha k (by omega)
      rw [ConPolyZono.aux_rescaleSub, if_pos hk]
      have := hsub a ⟨k, hk⟩
      rw [ConPolyZono.aux_rescaleSub, if_pos hk] at this
      rw [this, hcen', hrad', abs_le]
      rw [abs_le] at h1
      constructor <;> nlinarith [h1.1, h1.2, hb'.1, hb'.2.1, hb'.2.2]
    · -- the constraints and the point, by the invariant
      exact (hsat a).mp hs
    · rw [hx, ← hGI β, ← hpt a]
  · rintro ⟨a, β, ha, hβ, hs, hx⟩
    -- the factor `k` of the original sits at `cen + rad · t` for a `t` in `[-1,1]`
    let t : ℕ → ℝ := fun n =>
      if h : n < cPZ.p then (if rad n = 0 then 0 else (a n - cen n) / rad n) else 0
    -- `t` substituted back gives the original's factor `k`: `cen + rad · t = a k`
    have ht : ∀ k : Fin cPZ.p,
        ConPolyZono.aux_rescaleSub cen rad cPZ.p t k = a k := by
      intro k
      have hk' := hk (fun j => a j) (fun j => ha j j.2) hs k
      have htk : t k = if rad k = 0 then 0 else (a k - cen k) / rad k := by
        simp [t, k.2]
      rw [hsub, htk]
      by_cases h0 : rad k = 0
      · rw [if_pos h0, h0]
        have e1 := hrad' k
        have e2 := hcen' k
        linarith [hk'.1, hk'.2]
      · rw [if_neg h0]
        field_simp
        ring
    refine ⟨t, β, ?_, fun j hj => hβ j (by omega), ?_, ?_⟩
    · -- `t k` lies in `[-1,1]`: `a k` is in the box, `cen ± rad`
      intro k hk0
      have hk' : k < cPZ.p := by omega
      have hk'' := hk (fun j => a j) (fun j => ha j j.2) hs ⟨k, hk'⟩
      have hr : 0 ≤ rad k := by
        have := hrad' ⟨k, hk'⟩
        have hb' := hb ⟨k, hk'⟩
        simp only at this
        rw [this]; linarith [hb'.2.1]
      simp only [t, dif_pos hk']
      by_cases h0 : rad k = 0
      · rw [if_pos h0]; simp
      · rw [if_neg h0, abs_div, abs_of_pos (lt_of_le_of_ne hr (Ne.symm h0)), div_le_one
          (lt_of_le_of_ne hr (Ne.symm h0)), abs_le]
        have e1 := hcen' ⟨k, hk'⟩
        have e2 := hrad' ⟨k, hk'⟩
        simp only at e1 e2
        constructor <;> linarith [hk''.1, hk''.2]
    · -- the constraints at `t` are the original's at `a`
      have hfun : (fun k : Fin cPZ.p => ConPolyZono.aux_rescaleSub cen rad cPZ.p t k)
          = (fun k : Fin cPZ.p => a k) := by
        funext k; exact ht k
      rw [hsat t, hfun]
      exact hs
    · -- and so is the point
      have hfun : (fun k : Fin cPZ.p => ConPolyZono.aux_rescaleSub cen rad cPZ.p t k)
          = (fun k : Fin cPZ.p => a k) := by
        funext k; exact ht k
      rw [hx, hpt t, hfun, hGI β]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `rescale` returns the same set, for any contractor of the constraints: `contract` of
`[-1,1]ᵖ` lies in `[-1,1]ᵖ`, keeps every factor vector of the unit box that satisfies the
constraints, and is not empty. -/
theorem ConPolyZono.rescale_exact (cPZ : ConPolyZono α)
    (contract : Interval (Vec ℝ cPZ.p) → Interval (Vec ℝ cPZ.p))
    (hsub : (contract (ConPolyZono.unitBox cPZ.p)).construct
      ⊆ (ConPolyZono.unitBox cPZ.p).construct)
    (hkeep : ∀ x : Vec ℝ cPZ.p, x ∈ (ConPolyZono.unitBox cPZ.p).construct → cPZ.satisfies x →
      x ∈ (contract (ConPolyZono.unitBox cPZ.p)).construct)
    (hne : (contract (ConPolyZono.unitBox cPZ.p)).construct.Nonempty) :
    (cPZ.rescale contract).construct = cPZ.construct := by -- --- PROOF ---
  -- unfold the contraction: `contract` is applied only when `A` is not empty
  unfold ConPolyZono.rescale
  dsimp only
  by_cases hA : cPZ.m = 0 ∨ cPZ.s = 0
  · -- empty `A`: CORA does not contract, the box stays `[-1,1]ᵖ`
    rw [if_pos hA]
    refine ConPolyZono.aux_rescale_exact_of_box cPZ _ (fun k => ?_) (fun a ha _ k => ?_)
    · simp [ConPolyZono.unitBox]
    · simpa [ConPolyZono.unitBox, abs_le] using ha k
  · rw [if_neg hA]
    obtain ⟨x0, hx0⟩ := hne
    -- a nonempty box inside the unit box has its bounds inside `[-1,1]`, one coordinate moved
    have hbox : ∀ k, -1 ≤ (contract (ConPolyZono.unitBox cPZ.p)).inf k
        ∧ (contract (ConPolyZono.unitBox cPZ.p)).inf k
          ≤ (contract (ConPolyZono.unitBox cPZ.p)).sup k
        ∧ (contract (ConPolyZono.unitBox cPZ.p)).sup k ≤ 1 := by
      intro k
      have hx0k : (contract (ConPolyZono.unitBox cPZ.p)).inf k ≤ x0 k
          ∧ x0 k ≤ (contract (ConPolyZono.unitBox cPZ.p)).sup k := hx0 k
      -- the point with coordinate `k` moved to `v` stays in the contracted box
      have hmem : ∀ v : ℝ, (contract (ConPolyZono.unitBox cPZ.p)).inf k ≤ v →
          v ≤ (contract (ConPolyZono.unitBox cPZ.p)).sup k →
          Function.update x0 k v ∈ (contract (ConPolyZono.unitBox cPZ.p)).construct := by
        intro v h1 h2 i
        by_cases hi : i = k
        · subst hi
          show _ ≤ Function.update x0 i v i ∧ Function.update x0 i v i ≤ _
          rw [Function.update_self]
          exact ⟨h1, h2⟩
        · show _ ≤ Function.update x0 k v i ∧ Function.update x0 k v i ≤ _
          rw [Function.update_of_ne hi]
          exact hx0 i
      -- the box's lower and upper bounds are attained by such points, which lie in the unit box
      have hlo := hsub (hmem _ le_rfl (hx0k.1.trans hx0k.2)) k
      have hhi := hsub (hmem _ (hx0k.1.trans hx0k.2) le_rfl) k
      have hlo' : (-1 : ℝ) ≤ Function.update x0 k
          ((contract (ConPolyZono.unitBox cPZ.p)).inf k) k := hlo.1
      have hhi' : Function.update x0 k ((contract (ConPolyZono.unitBox cPZ.p)).sup k) k
          ≤ 1 := hhi.2
      rw [Function.update_self] at hlo' hhi'
      exact ⟨hlo', hx0k.1.trans hx0k.2, hhi'⟩
    -- the contractor keeps every solution in the unit box
    refine ConPolyZono.aux_rescale_exact_of_box cPZ _ hbox (fun a ha hs k => ?_)
    exact hkeep a (fun i => abs_le.mp (ha i)) hs k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
