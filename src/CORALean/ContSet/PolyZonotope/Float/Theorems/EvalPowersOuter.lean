module

public import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPowers
public import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsLeErrorBound
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPowersListRel
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPowersListValue

@[expose] public section

/-!
# `PolyZonotope.evalPowers` encloses the polynomials of the neurons on the set

A point of the input is a nominal point at factors `a`, `β` plus a point `e` of the error box.
Coordinate by coordinate, the row with the center `c + e` is a real row whose powers give the
polynomial at the point (`Real.PolyZonotope.evalPowersList_value`), at the monomials of the
exponents of the powers and at new independent values shared by all rows. The float run encloses
that real run entry by entry (`Real.PolyZonotope.evalPowersList_rel` with `MidRad.Encloses`), so
the nominal point at the same factors misses the value by at most the radii, which the box holds.

## Inputs
* `pZ` – polynomial zonotope
* `coeffs` – coefficient vectors, lowest degree first
* `x` – point of the set

## Hypotheses
* `hx` – `x` lies in `pZ`

## Conclusion
* the polynomials at `x`, neuron by neuron, lie in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {β γ : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A float encloses its own value. -/
private theorem aux_encloses_exact (x : 𝕋) : (MidRad.exact x).Encloses (toReal x) :=
  ⟨by simp [MidRad.exact, toReal_zero]⟩

/-- The sum of two midpoint-radius floats encloses the sum of what they enclose. -/
private theorem aux_encloses_add {x y : ℝ} {a b : MidRad 𝕋} (ha : a.Encloses x) (hb : b.Encloses y)
    : -- --- CONCL ---
    (a.add b).Encloses (x + y) := by -- --- PROOF ---
  replace ha := ha.abs_sub_le
  replace hb := hb.abs_sub_le
  refine ⟨?_⟩
  simp only [MidRad.add]
  -- the stored sum is below the exact one, the rounding gap above the difference
  have h1 := addDown_le_add a.v b.v
  have h2 := add_le_addUp a.v b.v
  have h3 := sub_le_subUp (addUp a.v b.v) (addDown a.v b.v)
  have h4 := add_le_addUp a.r b.r
  have h5 := add_le_addUp (addUp a.r b.r) (subUp (addUp a.v b.v) (addDown a.v b.v))
  rw [abs_le] at ha hb ⊢
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-- The product of two midpoint-radius floats encloses the product of what they enclose. -/
private theorem aux_encloses_mul {x y : ℝ} {a b : MidRad 𝕋} (ha : a.Encloses x) (hb : b.Encloses y)
    : -- --- CONCL ---
    (a.mul b).Encloses (x * y) := by -- --- PROOF ---
  replace ha := ha.abs_sub_le
  replace hb := hb.abs_sub_le
  refine ⟨?_⟩
  simp only [MidRad.mul]
  have hra : 0 ≤ toReal a.r := le_trans (abs_nonneg _) ha
  have hrb : 0 ≤ toReal b.r := le_trans (abs_nonneg _) hb
  -- every rounding of the radius upward, the product's own gap between its two roundings
  have h1 := mulDown_le_mul a.v b.v
  have h2 := mul_le_mulUp a.v b.v
  have h3 := sub_le_subUp (mulUp a.v b.v) (mulDown a.v b.v)
  have m1 := mul_le_mulUp (absolute a.v) b.r
  have m2 := mul_le_mulUp (absolute b.v) a.r
  have m3 := mul_le_mulUp a.r b.r
  have s1 := add_le_addUp (mulUp (absolute a.v) b.r) (mulUp (absolute b.v) a.r)
  have s2 := add_le_addUp (mulUp a.r b.r) (subUp (mulUp a.v b.v) (mulDown a.v b.v))
  have s3 := add_le_addUp (addUp (mulUp (absolute a.v) b.r) (mulUp (absolute b.v) a.r))
    (addUp (mulUp a.r b.r) (subUp (mulUp a.v b.v) (mulDown a.v b.v)))
  rw [toReal_absolute] at m1 m2
  -- the exact product's distance from the product of the values
  have key : |x * y - toReal a.v * toReal b.v|
      ≤ |toReal a.v| * toReal b.r + |toReal b.v| * toReal a.r + toReal a.r * toReal b.r := by
    have e : x * y - toReal a.v * toReal b.v = toReal a.v * (y - toReal b.v)
        + toReal b.v * (x - toReal a.v) + (x - toReal a.v) * (y - toReal b.v) := by ring
    rw [e]
    refine le_trans (abs_add_le _ _) (add_le_add (le_trans (abs_add_le _ _) ?_) ?_)
    · rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
        (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
    · rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hra
  rw [abs_le] at key ⊢
  constructor <;> linarith [key.1, key.2]

/-- `pairsWith` commutes with a map that carries the operation. -/
private theorem aux_pairsWith_map {f : β → β → β} {f' : γ → γ → γ} {g : β → γ}
    (hg : ∀ a b, g (f a b) = f' (g a) (g b)) (a : List β) :
    (Real.PolyZonotope.pairsWith f a).map g = Real.PolyZonotope.pairsWith f' (a.map g) := by
  induction a with
  | nil => rfl
  | cons x r ih => simp [Real.PolyZonotope.pairsWith, ih, hg]

/-- `crossWith` commutes with a map that carries the operation. -/
private theorem aux_crossWith_map {f : β → β → β} {f' : γ → γ → γ} {g : β → γ}
    (hg : ∀ a b, g (f a b) = f' (g a) (g b)) (a b : List β) :
    (Real.PolyZonotope.crossWith f a b).map g = Real.PolyZonotope.crossWith f' (a.map g) (b.map
        g) := by
  simp only [Real.PolyZonotope.crossWith, List.map_flatMap, List.flatMap_map, List.map_map]
  congr 1; funext y; congr 1; funext x; simp [hg]

/-- Every power commutes with a map that carries the operation. -/
private theorem aux_powerExt_map {f : β → β → β} {f' : γ → γ → γ} {g : β → γ}
    (hg : ∀ a b, g (f a b) = f' (g a) (g b)) (M : List β) (i : ℕ) : -- --- CONCL ---
    (Real.PolyZonotope.powerExt f M i).map g = Real.PolyZonotope.powerExt f' (M.map g)
        i := by -- --- PROOF ---
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [Real.PolyZonotope.powerExt.eq_1, Real.PolyZonotope.powerExt.eq_1 f' _ i]
    split_ifs with h1 h2
    · rfl
    · have e := ih (i / 2) (by omega)
      rw [List.map_append, List.map_append, List.map_append, e, aux_pairsWith_map hg, e,
          List.map_map]
      congr 2
      rw [← e, List.map_map]
      congr 1; funext a; simp [hg]
    · simp only [List.map_append, ih (i / 2) (by omega), ih ((i + 1) / 2) (by omega),
        aux_crossWith_map hg]

/-- The monomials of the powers commute with a map that carries the operation. -/
private theorem aux_powerOut_map {f : β → β → β} {f' : γ → γ → γ} {g : β → γ}
    (hg : ∀ a b, g (f a b) = f' (g a) (g b)) (M : List β) (k : ℕ) :
    (Real.PolyZonotope.powerOut f M k).map g = Real.PolyZonotope.powerOut f' (M.map g) k := by
  simp only [Real.PolyZonotope.powerOut, Real.PolyZonotope.powerParts, List.map_append,
      List.map_flatMap, List.map_drop,
    aux_powerExt_map hg, ← List.length_map (f := g)]

/-- The real run of coordinate `i` against the float run of all coordinates. -/
private theorem aux_rel (i : Fin n) {as : List ℝ} {as' : List (Vec (MidRad 𝕋) n)}
    (has : List.Forall₂ (fun t (b : Vec (MidRad 𝕋) n) => (b i).Encloses t) as as')
    {x : Real.PowerRow ℝ} {y : Real.PowerRow (Vec (MidRad 𝕋) n)} (hc : (y.c i).Encloses x.c)
    (hG : List.Forall₂ (fun t (b : Vec (MidRad 𝕋) n) => (b i).Encloses t) x.G y.G)
    (hGI : List.Forall₂ (fun t (b : Vec (MidRad 𝕋) n) => (b i).Encloses t) x.GI y.GI)
        : -- --- CONCL ---
    ((Real.PolyZonotope.evalPowersList PolyZonotope.step_midRadOps as' y).c i).Encloses
        (Real.PolyZonotope.evalPowersList Real.PowerOps.real as x).c
      ∧ List.Forall₂ (fun t (b : Vec (MidRad 𝕋) n) => (b i).Encloses t)
        (Real.PolyZonotope.evalPowersList Real.PowerOps.real as x).G
        (Real.PolyZonotope.evalPowersList PolyZonotope.step_midRadOps as' y).G
      ∧ List.Forall₂ (fun t (b : Vec (MidRad 𝕋) n) => (b i).Encloses t)
        (Real.PolyZonotope.evalPowersList Real.PowerOps.real as x).GI
        (Real.PolyZonotope.evalPowersList PolyZonotope.step_midRadOps as'
            y).GI := by -- --- PROOF ---
  have hz : (MidRad.exact (zero : 𝕋)).Encloses 0 := by
    have := aux_encloses_exact (𝕋 := 𝕋) zero
    rwa [toReal_zero] at this
  have h2 : ((MidRad.exact (one : 𝕋)).add (MidRad.exact one)).Encloses 2 := by
    have := aux_encloses_add (aux_encloses_exact (𝕋 := 𝕋) one) (aux_encloses_exact one)
    rw [toReal_one] at this
    exact (show (1 : ℝ) + 1 = 2 by norm_num) ▸ this
  have hh : (MidRad.exact (half (one : 𝕋))).Encloses (1 / 2) := by
    have := aux_encloses_exact (𝕋 := 𝕋) (half one)
    rw [toReal_half, toReal_one] at this
    exact this
  exact Real.PolyZonotope.evalPowersList_rel (o := Real.PowerOps.real)
    (o' := PolyZonotope.step_midRadOps) (R := fun t (b : Vec (MidRad 𝕋) n) => (b i).Encloses t)
    hz h2 hh (fun ha hb => aux_encloses_add ha hb) (fun ha hb => aux_encloses_mul ha hb)
    has hc hG hGI

/-- Two lists of the same length related entry by entry, built from functions on `Fin`. -/
private theorem aux_forall₂_ofFn {α β : Type} {R : α → β → Prop} :
    ∀ {L : ℕ} {f : Fin L → α} {g : Fin L → β},
    (∀ l, R (f l) (g l)) → List.Forall₂ R (List.ofFn f) (List.ofFn g)
  | 0, _, _, _ => by simp
  | L + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (aux_forall₂_ofFn fun l => h l.succ)

/-- Two maps of one list related entry by entry. -/
private theorem aux_forall₂_map {α β γ : Type} {R : α → β → Prop} {f : γ → α} {g : γ → β}
    (h : ∀ c, R (f c) (g c)) : ∀ l : List γ, List.Forall₂ R (l.map f) (l.map g)
  | [] => List.Forall₂.nil
  | c :: l => List.Forall₂.cons (h c) (aux_forall₂_map h l)

/-- A dot product of two lists as the sum over the indices of the first. -/
private theorem aux_dot_eq_sum_getD : ∀ (u w : List ℝ), u.length = w.length →
    (List.zipWith (· * ·) u w).sum = ∑ l : Fin u.length, u.getD l 0 * w.getD l 0
  | [], [], _ => by simp
  | x :: u, y :: w, h => by
    rw [List.zipWith_cons_cons, List.sum_cons, aux_dot_eq_sum_getD u w (by simpa using h)]
    show _ = ∑ l : Fin (u.length + 1), _
    rw [Fin.sum_univ_succ]
    simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The same over the indices `Fin L` of a common length. -/
private theorem aux_dot_eq_sum {u w : List ℝ} {L : ℕ} (hu : u.length = L) (hw : w.length = L) :
    (List.zipWith (· * ·) u w).sum = ∑ l : Fin L, u.getD l 0 * w.getD l 0 := by
  subst hu
  exact aux_dot_eq_sum_getD u w hw.symm

/-- A dot product of two lists of functions on `Fin L` is the sum of the products. -/
private theorem aux_dot_ofFn {L : ℕ} (f g : Fin L → ℝ) :
    (List.zipWith (· * ·) (List.ofFn f) (List.ofFn g)).sum = ∑ l, f l * g l := by
  rw [aux_dot_eq_sum (L := L) (by simp) (by simp)]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [List.getD_eq_getElem?_getD, l.2]

/-- Two sums against weights in `[-1, 1]` differ by at most the sum of the distances. -/
private theorem aux_abs_sum_sub_le {L : ℕ} (u v r m : Fin L → ℝ) (hm : ∀ l, |m l| ≤ 1)
    (h : ∀ l, |u l - v l| ≤ r l) : |∑ l, u l * m l - ∑ l, v l * m l| ≤ ∑ l, r l := by
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun l _ => ?_)
  rw [← sub_mul, abs_mul]
  nlinarith [hm l, h l, abs_nonneg (m l), abs_nonneg (u l - v l)]

/-- An entry by index, inside the list. -/
private theorem aux_getD_of_lt {α : Type} {l : List α} {i : ℕ} (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- An entry of a list in `[-1, 1]`, or the default `0`, lies in `[-1, 1]`. -/
private theorem aux_abs_getD_le {l : List ℝ} (hl : ∀ m ∈ l, |m| ≤ 1) (j : ℕ) : |l.getD j 0| ≤
    1 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[j]? with
  | none => simp
  | some v => exact hl v (List.mem_of_getElem? h)

/-- The real row of coordinate `i` at the center displaced by `e`. -/
private def aux_row (pZ : PolyZonotope (Vec 𝕋 n)) (e : Vec ℝ n) (i : Fin n) : Real.PowerRow ℝ :=
  ⟨toReal (pZ.c i) + e i, List.ofFn fun l => toReal (pZ.G l i),
    List.ofFn fun j => toReal (pZ.GI j i)⟩

/-- The real run of coordinate `i`: the exact powers of its row. -/
private noncomputable def aux_realRun (pZ : PolyZonotope (Vec 𝕋 n)) (coeffs : List (Vec 𝕋 n))
    (e : Vec ℝ n) (i : Fin n) : Real.PowerRow ℝ :=
  Real.PolyZonotope.evalPowersList Real.PowerOps.real (coeffs.map fun v => toReal (v i))
    (aux_row pZ e i)


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.evalPowers_outer (pZ : PolyZonotope (Vec 𝕋 n)) (coeffs : List (Vec 𝕋 n))
    {x : Vec ℝ n} (hx : x ∈ pZ.toSet) : -- --- CONCL ---
    (fun i => Real.PolyZonotope.evalPolyReal (coeffs.map fun v => toReal (v i)) (x i))
      ∈ (PolyZonotope.evalPowers pZ coeffs).toSet := by -- --- PROOF ---
  obtain ⟨y, hy, e, he, rfl⟩ := hx
  obtain ⟨a, β, ha, hβ, hyi⟩ := PolyZonotope.mem_nominalSet_iff.mp hy
  -- the monomials and the independent values of the point
  set k := max 1 (coeffs.length - 1) with hk
  set cols : List (Fin pZ.p → ℕ) := List.ofFn fun l k => pZ.E k l with hcols
  set mono : (Fin pZ.p → ℕ) → ℝ := fun col => ∏ r, a r ^ col r with hmono
  set M := List.ofFn fun l => Real.PolyZonotope.monomial pZ.E a l with hMdef
  set N := List.ofFn β with hNdef
  have hMb : ∀ m ∈ M, |m| ≤ 1 := by
    intro m hm
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hm
    exact Real.PolyZonotope.abs_monomial_le_one pZ.E ha l
  have hNb : ∀ m ∈ N, |m| ≤ 1 := by
    intro m hm
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hm
    exact hβ j
  obtain ⟨N', hN'b, hN'⟩ := Real.PolyZonotope.evalPowersList_value hMb hNb k
  -- the stored run, and the real run of every coordinate
  set xb : Real.PowerRow (Vec (MidRad 𝕋) n) :=
    ⟨fun i => ⟨pZ.c i, PolyZonotope.errorBound pZ.I_error i⟩,
      List.ofFn fun l i => MidRad.exact (pZ.G l i), List.ofFn fun j i => MidRad.exact (pZ.GI j i)⟩
    with hxb
  set run := Real.PolyZonotope.evalPowersList PolyZonotope.step_midRadOps
    (coeffs.map fun v i => MidRad.exact (v i)) xb with hrun
  set Eout := Real.PolyZonotope.powerOut (· + ·) cols k with hEout
  have hkas : ∀ (as : List ℝ), as.length = coeffs.length → max 1 (as.length - 1) = k :=
    fun as h => by rw [h]
  -- every coordinate's real run is within the radii of the float run
  have hrel : ∀ i, (run.c i).Encloses (aux_realRun pZ coeffs e i).c
      ∧ List.Forall₂ (fun t (b : Vec (MidRad 𝕋) n) => (b i).Encloses t)
        (aux_realRun pZ coeffs e i).G run.G
      ∧ List.Forall₂ (fun t (b : Vec (MidRad 𝕋) n) => (b i).Encloses t)
        (aux_realRun pZ coeffs e i).GI run.GI := by
    intro i
    rw [hrun, aux_realRun]
    have h1 := aux_forall₂_map (R := fun t (b : Vec (MidRad 𝕋) n) => (b i).Encloses t)
      (f := fun v => toReal (v i)) (g := fun v j => MidRad.exact (v j))
      (fun v => aux_encloses_exact (v i)) coeffs
    have h2 : (xb.c i).Encloses (aux_row pZ e i).c := by
      refine ⟨?_⟩
      show |toReal (pZ.c i) + e i - toReal (pZ.c i)|
        ≤ toReal (PolyZonotope.errorBound pZ.I_error i)
      rw [add_sub_cancel_left]
      exact PolyZonotope.abs_le_errorBound he i
    -- the generators are exact
    have h3 : List.Forall₂ (fun t (b : Vec (MidRad 𝕋) n) => (b i).Encloses t)
        (aux_row pZ e i).G xb.G :=
      aux_forall₂_ofFn (R := fun t (b : Vec (MidRad 𝕋) n) => (b i).Encloses t)
        (f := fun l => toReal (pZ.G l i)) (g := fun l j => MidRad.exact (pZ.G l j))
        fun l => aux_encloses_exact (pZ.G l i)
    have h4 : List.Forall₂ (fun t (b : Vec (MidRad 𝕋) n) => (b i).Encloses t)
        (aux_row pZ e i).GI xb.GI :=
      aux_forall₂_ofFn (R := fun t (b : Vec (MidRad 𝕋) n) => (b i).Encloses t)
        (f := fun l => toReal (pZ.GI l i)) (g := fun l j => MidRad.exact (pZ.GI l j))
        fun l => aux_encloses_exact (pZ.GI l i)
    exact aux_rel i h1 h2 h3 h4
  -- the monomials of the powers are those of the exponents of the powers
  have hEM : Real.PolyZonotope.powerOut (· * ·) M k = Eout.map mono := by
    rw [hEout, aux_powerOut_map (g := mono) (f' := (· * ·))]
    · congr 1
      simp only [hMdef, hcols, List.map_ofFn]
      rfl
    · intro c1 c2
      simp only [hmono, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  -- the lengths of the float run, from a real run of zeros
  let row0 : Real.PowerRow ℝ :=
    ⟨0, List.ofFn fun (_ : Fin pZ.h) => 0, List.ofFn fun (_ : Fin pZ.q) => 0⟩
  have h0 := hN' (coeffs.map fun _ => 0) (hkas _ (by simp)) row0 (by simp [row0, M])
    (by simp [row0, N])
  have htriv := Real.PolyZonotope.evalPowersList_rel (R := fun _ _ => True)
    (o := Real.PowerOps.real) (o' := PolyZonotope.step_midRadOps) trivial trivial trivial
    (fun _ _ => trivial) (fun _ _ => trivial) (as := coeffs.map fun _ => 0)
    (as' := coeffs.map fun v j => MidRad.exact (v j)) (aux_forall₂_map (fun _ => trivial) coeffs)
    (x := row0) (y := xb) trivial (aux_forall₂_ofFn fun _ => trivial)
    (aux_forall₂_ofFn fun _ => trivial)
  -- the related runs have equal lengths
  have hGlen : run.G.length = Eout.length := by
    rw [← htriv.2.1.length_eq, h0.1, hEM, List.length_map]
  have hGIlen : run.GI.length = N'.length := by rw [← htriv.2.2.length_eq, h0.2.1]
  -- the nominal point at the same factors, the run's products as the independent ones
  set β' : Fin run.GI.length → ℝ := fun j => N'.getD j 0 with hβ'def
  have hβ' : ∀ j, |β' j| ≤ 1 := fun j => aux_abs_getD_le hN'b j
  set z : Vec ℝ n := fun i => toReal ((run.c i).v)
    + (∑ l : Fin run.G.length, toReal ((run.G.get l i).v) * mono (Eout.getD l 0))
    + ∑ j : Fin run.GI.length, toReal ((run.GI.get j i).v) * β' j with hzdef
  have hz : z ∈ InflatedContSet.nominalSet (PolyZonotope.evalPowers pZ coeffs) :=
    PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β', ha, hβ', fun i => rfl⟩
  refine Set.mem_add.mpr ⟨z, hz, _ - z, ?_, add_sub_cancel _ _⟩
  intro i
  -- the coordinate's real run reaches the target
  obtain ⟨-, -, hval⟩ := hN' (coeffs.map fun v => toReal (v i)) (hkas _ (by simp)) (aux_row pZ e i)
    (by simp [aux_row, M]) (by simp [aux_row, N])
  have hrow : (aux_row pZ e i).c + (List.zipWith (· * ·) (aux_row pZ e i).G M).sum
      + (List.zipWith (· * ·) (aux_row pZ e i).GI N).sum = y i + e i := by
    simp only [aux_row, hMdef, hNdef, aux_dot_ofFn, hyi i]; ring
  obtain ⟨hRc, hRG', hRGI'⟩ := hrel i
  set rr := aux_realRun pZ coeffs e i with hrr
  have hRG := List.forall₂_iff_get.mp hRG'
  have hRGI := List.forall₂_iff_get.mp hRGI'
  have hMout : (Real.PolyZonotope.powerOut (· * ·) M k).length = run.G.length := by
    rw [hEM, List.length_map, hGlen]
  -- the dot products as sums over the stored generators
  have hdG : (List.zipWith (· * ·) rr.G (Real.PolyZonotope.powerOut (· * ·) M k)).sum
      = ∑ l : Fin run.G.length, rr.G.getD l 0 * mono (Eout.getD l 0) := by
    rw [aux_dot_eq_sum hRG.1 hMout]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    have hl : (l : ℕ) < Eout.length := hGlen ▸ l.2
    rw [hEM, aux_getD_of_lt _ (by simpa using hl), List.getElem_map, aux_getD_of_lt _ hl]
  have hdGI : (List.zipWith (· * ·) rr.GI N').sum
      = ∑ j : Fin run.GI.length, rr.GI.getD j 0 * β' j :=
    aux_dot_eq_sum hRGI.1 hGIlen.symm
  set tv := Real.PolyZonotope.evalPolyReal (coeffs.map fun v => toReal (v i)) (y i + e i)
    with htv
  have htarget : tv = rr.c
      + (List.zipWith (· * ·) rr.G (Real.PolyZonotope.powerOut (· * ·) M k)).sum
      + (List.zipWith (· * ·) rr.GI N').sum := by
    rw [htv, ← hrow, ← hval, hrr, aux_realRun]
  -- each part within its radii
  have hG : |(∑ l : Fin run.G.length, rr.G.getD l 0 * mono (Eout.getD l 0))
      - ∑ l : Fin run.G.length, toReal ((run.G.get l i).v) * mono (Eout.getD l 0)|
      ≤ ∑ l : Fin run.G.length, toReal ((run.G.get l i).r) := by
    refine aux_abs_sum_sub_le _ _ _ _ (fun l => ?_) (fun l => ?_)
    · simp only [hmono]
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun r _ => abs_nonneg _)
        (fun r _ => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (ha r))
    · have hl : (l : ℕ) < rr.G.length := by rw [hRG.1]; exact l.2
      rw [aux_getD_of_lt _ hl]
      exact (hRG.2 l hl l.2).abs_sub_le
  have hGI : |(∑ j : Fin run.GI.length, rr.GI.getD j 0 * β' j)
      - ∑ j : Fin run.GI.length, toReal ((run.GI.get j i).v) * β' j|
      ≤ ∑ j : Fin run.GI.length, toReal ((run.GI.get j i).r) := by
    refine aux_abs_sum_sub_le _ _ _ _ hβ' (fun j => ?_)
    have hj : (j : ℕ) < rr.GI.length := by rw [hRGI.1]; exact j.2
    rw [aux_getD_of_lt _ hj]
    exact (hRGI.2 j hj j.2).abs_sub_le
  -- the radii, summed upward, are the box
  have hsum := add_le_addUp (run.c i).r (addUp (sumUp fun l => (run.G.get l i).r)
    (sumUp fun j => (run.GI.get j i).r))
  have hsum2 := add_le_addUp (sumUp fun l => (run.G.get l i).r)
    (sumUp fun j => (run.GI.get j i).r)
  have hs1 := sum_le_sumUp fun l : Fin run.G.length => (run.G.get l i).r
  have hs2 := sum_le_sumUp fun j : Fin run.GI.length => (run.GI.get j i).r
  -- the distance to the nominal point, split into the three parts
  have hdiff : tv - z i
      = (rr.c - toReal (run.c i).v)
        + ((∑ l : Fin run.G.length, rr.G.getD l 0 * mono (Eout.getD l 0))
          - ∑ l : Fin run.G.length, toReal ((run.G.get l i).v) * mono (Eout.getD l 0))
        + ((∑ j : Fin run.GI.length, rr.GI.getD j 0 * β' j)
          - ∑ j : Fin run.GI.length, toReal ((run.GI.get j i).v) * β' j) := by
    rw [htarget, hdG, hdGI]; simp only [hzdef]; ring
  have hfin : |tv - z i|
      ≤ toReal (addUp (run.c i).r (addUp (sumUp fun l => (run.G.get l i).r)
          (sumUp fun j => (run.GI.get j i).r))) := by
    rw [hdiff]
    have hRc' : |rr.c - toReal (run.c i).v| ≤ toReal (run.c i).r := hRc.abs_sub_le
    refine le_trans (abs_add_le _ _) ?_
    have := abs_add_le (rr.c - toReal (run.c i).v)
      ((∑ l : Fin run.G.length, rr.G.getD l 0 * mono (Eout.getD l 0))
        - ∑ l : Fin run.G.length, toReal ((run.G.get l i).v) * mono (Eout.getD l 0))
    linarith
  -- the distance within the symmetric box of the stored error
  rw [abs_le] at hfin
  refine ⟨?_, hfin.2⟩
  show toReal (neg _) ≤ _
  rw [toReal_neg]; exact hfin.1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
