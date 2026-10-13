import CORALean.ContSet.HPolytope.Real.Operations.OfEqs1D

/-!
# `HPolytope.compact1DEqCora`: the equality half of CORA's `priv_compact_1D`

`@polytope/private/priv_compact_1D.m` with equality rows `Ae x = be` in one dimension and no
inequality rows (so l. 73-110 are skipped). It divides every row with `be ≠ 0` by `be`, so each
offset is `0` or `1` (l. 40, `priv_normalizeConstraints(..., 'b')`). With more than one row
(l. 43) it flags rows `= 1` together with rows `= 0` as empty but does not return (l. 44-47), so
l. 69 then reads `be(1)` of `[]` and errors; it flags rows with offset `1` and different
coefficients, or offset `0` and different coefficients, as empty (l. 50-65); otherwise it merges
all rows into one with `Ae = 1; be = be(1) / Ae(1);` (l. 69). The second statement reads `Ae(1)`
after the first has set `Ae = 1`, so the merged row is `x = be(1)`, the normalized offset, and not
`x = be(1) / Ae(1)` for the row's own coefficient.

The output is the triple `(empty, Ae, be)` of the source as a flag and an `HPolytope` of equality
rows (`HPolytope.ofEqs1D`); `none` is the error. `withinTol` reads as exact equality. Read from
the source, not run. `vertices_` of a 1-D polytope passes its raw constraints here
(`priv_vertices_1D.m`, l. 35); `compact_(P, 'all')` reaches it after `priv_compact_alignedEq`,
which keeps a pair `x = c`, `-x = -c` since it tests alignment, not anti-alignment.

## References

* [1] `contSet/@polytope/private/priv_compact_1D.m`, CORA, ll. 34-71.
* [2] `contSet/@polytope/private/priv_normalizeConstraints.m`, CORA, type `'b'`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1] at the equality rows `Ae x = be` of a 1-D polytope without inequality rows: the empty
flag and the rows it returns; `none` is the error after l. 44-47. -/
noncomputable def HPolytope.compact1DEqCora {k : ℕ} (Ae be : Fin k → ℝ) :
    Option (Bool × HPolytope (Vec ℝ 1)) :=
  open Classical in
  -- l. 36: `if ~isempty(Ae)`
  if hk : k = 0 then some (false, HPolytope.ofEqs1D Ae be)
  else
    -- l. 40, [2]: `Ae(idx,:) = Ae(idx,:) ./ be(idx)` for `be ≠ 0`
    let Ae₁ : Fin k → ℝ := fun i => if be i ≠ 0 then Ae i / be i else Ae i
    -- l. 40, [2]: `be(idx) = 1` for `be ≠ 0`
    let be₁ : Fin k → ℝ := fun i => if be i ≠ 0 then 1 else be i
    -- l. 43: `if size(Ae,1) > 1`
    if 1 < k then
      -- l. 44-47: offsets `1` and `0` both present: cleared without a return, l. 69 errors
      if (∃ i, be₁ i = 1) ∧ (∃ i, be₁ i = 0) then none
      -- l. 50-65: rows `= 1` (or `= 0`) with different coefficients: empty
      else if (∃ i j, be₁ i = 1 ∧ be₁ j = 1 ∧ Ae₁ i ≠ Ae₁ j) ∨
          (∃ i j, be₁ i = 0 ∧ be₁ j = 0 ∧ Ae₁ i ≠ Ae₁ j) then
        some (true, HPolytope.ofEqs1D (k := 0) Fin.elim0 Fin.elim0)
      else
        -- l. 69: `Ae = 1;`
        let Ae₂ : ℝ := 1
        -- l. 69: `be = be(1) / Ae(1);`, reading the `Ae` just assigned
        let be₂ : ℝ := be₁ ⟨0, Nat.pos_of_ne_zero hk⟩ / Ae₂
        some (false, HPolytope.ofEqs1D ![Ae₂] ![be₂])
    else some (false, HPolytope.ofEqs1D Ae₁ be₁)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
