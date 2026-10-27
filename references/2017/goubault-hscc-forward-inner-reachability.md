# Forward Inner-Approximated Reachability of Non-Linear Continuous Systems

```bibtex
@inproceedings{goubault2017forward,
  author = {Goubault, E. and Putot, S.},
  title = {Forward Inner-Approximated Reachability of Non-Linear Continuous Systems},
  booktitle = {Proceedings of the 20th International Conference on Hybrid Systems: Computation and Control},
  year = {2017}
}
```

**Source:** http://www.lix.polytechnique.fr/Labo/Sylvie.Putot/Publications/hscc17.pdf (the published ACM version with its copyright block, doi:10.1145/3049797.3049811, 10 pages, read in full; text extracted with `pypdf`). CORA cites the paper in `nonlinearSys/reachInner.m`, `nonlinearSys/private/priv_reachInnerProjection.m` ("implementation of Alg. 1"), `priv_reachInnerParallelotope.m` (for the Jacobian dynamics of Sec. 3.1) and `global/classes/intKaucher.m` (Example 1).  
**Inventory:** confirmed (Definition 1, Proposition 1, Theorem 1, Examples 1-6, Algorithm 1 and equations (1)-(30), each with its own counter; Sections 2-4)

Inner approximations of the reachable sets of non-linear ODEs, computed forward: Goldsztejn's
generalized mean-value theorem in Kaucher arithmetic (`Thm. 1`, cited) applied to the flow,
with Taylor-model outer enclosures of the solution from one initial point and of the
Jacobian of the flow, which solves the variational equations (Sec. 3, `Alg. 1`). Formalized:
the Lie derivative along the variational field (`Eq. 14`), the commutation of Jacobian and
Lie derivative that lets (17) reuse the Taylor coefficients of `f` (Sec. 3.3), Step 3, (18),
with the enclosures of Steps 1-2 as hypotheses, and the loop of `Alg. 1` around it, with the
Taylor models as an argument. The Taylor-model integration itself (Steps 1 and 2) is not
computed. Step 3's inner approximation is per component; the box of the components is not
inside the reachable set, which is what CORA's `'proj'` returns.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Sec. 2.1` | (Mean-value extension) range(f, x) ⊆ f(x₀) + [f'](x)(x - x₀), and the AE readings of outer and inner approximations. | n/a — the classical interval mean-value extension, restated from Moore 1966 [23] | `restated` |
| `Sec. 2.2` | Kaucher addition and multiplication on generalized intervals, dual and pro. | n/a — restated from Kaucher 1980 [17] | `restated` |
| `Def. 1` | ((f, x)-interpretable) z is (f, x)-interpretable if (∀x_A ∈ x_A)(Q_z z ∈ pro z)(∃x_E ∈ pro x_E)(f(x) = z), Q_z = ∃ for z proper, ∀ otherwise. | n/a — restated from Goldsztejn et al. 2005 [10] | `restated` |
| `Prop. 1` | For an expression with each variable occurring once (degree 1), its Kaucher evaluation is (f, x)-interpretable. | n/a — restated from Goldsztejn et al. [10] | `restated` |
| `Thm. 1` | (Generalized mean-value extension) For f differentiable, x improper and {∂f/∂xᵢ(x) \| x ∈ pro x} ⊆ [Δᵢ], f(x̃) + Σᵢ[Δᵢ](xᵢ - x̃ᵢ) in Kaucher arithmetic is (f, x)-interpretable for any x̃ ∈ pro x (5). | n/a — restated from Goldsztejn et al. [10]; `kaucherInnerStep_inner` has the inner case, with an enclosure of `f(x̃)` | `restated` |
| `Sec. 2.3` | The Kaucher products (5) needs: P × dual Z = [x̲y̲, x̲ȳ], -P × dual Z = [x̄ȳ, x̄y̲], Z × dual Z = 0; nonempty only when [Δᵢ] ∌ 0. | n/a — restated from Kaucher [17]; `kaucherMulDualZ` has the three cases | `restated` |
| `Example 1` | x² - x on [2, 3]: f(2.5) + [3, 5]([3, 2] - 2.5) = [5.25, 2.25], so [2.25, 5.25] ⊆ range. | n/a — an illustration | `not-a-claim` |
| `Eq. 6` | (Interval Taylor method) [z](t, t_j, [z_j]) = [z_j] + Σ_{i<k}(t - t_j)ⁱ/i! f^[i]([z_j]) + (t - t_j)ᵏ/k! f^[k]([r_{j+1}]) encloses the solutions on [t_j, t_{j+1}]. | n/a — restated from Nedialkov, Jackson and Corliss 1999 [25] | `restated` |
| `Eq. 8` | (Lie derivatives) f^[1] = f, f^[i+1] = Σⱼ ∂f^[i]/∂zⱼ fⱼ, and d^{l+1}z/dt^{l+1} = f^[l+1](z(t)). | n/a — restated from [25] ("let us quickly recall"); `lieIter` is the recursion | `restated` |
| `Example 2` | The Brusselator and its Jacobian. | n/a — an illustration | `not-a-claim` |
| `Eq. 10` | (Variational equations) J̇ = Jac_z f(z(t, z₀)) J, J(t₀) = Id, (9). | n/a — the variational equations, restated from Zgliczyński 2002 [29]; `augField` is the field | `restated` |
| `Eq. 14` | (Lie derivative along the augmented field) H^[2] = Σᵢ ∂H/∂zᵢ fᵢ + Σ_{k,l} ∂H/∂J_kl (Σₛ ∂f_k/∂zₛ J_sl), the time derivative of H(z(t), J(t)). | [`LieDerivative.lean`](../../src/CORALean/Global/LieDerivative.lean) — `hasDerivAt_lieDeriv_augField`: coordinate-free, `DH(z, J)(f(z), Df(z)J)`, one column of `J` at a time | `correct` |
| `Alg. 1` | (Inner and outer reachable sets) Per step: rough enclosures by interval Picard-Lindelöf (Step 1), Taylor models (15)-(17) of the solution, the solution from z̃₀ and the Jacobian (Step 2), the inner range (18) (Step 3), the next initial enclosures (Step 4). | [`ForwardInnerReach.lean`](../../src/CORALean/Global/ForwardInnerReach.lean) — `forwardInnerState` (the loop: Steps 1-2 are the argument `models`, Step 4 its value at `t_{j+1}`), `forwardInnerRange` (Step 3, [`kaucherInnerStep`](../../src/CORALean/Global/KaucherInner.lean)) and `forwardInner_sound`. For Taylor models that are valid at every `t` of a step when the enclosures at `t_j` are, the carried enclosures are valid at every grid time and each `pro ]z[ᵢ` is inside the `i`-th projection of the flow image at every `t` of the step | `underspecified` — Steps 1-2 (the Picard-Lindelöf iteration and the Taylor models (15)-(17), the validated integration of [25]) are an argument with the validity hypothesis, not computed; and Step 3's guarantee is per component, see `Eq. 18` |
| `Sec. 3.3` | (17) and (20) are equivalent: ∇_z(f^[i]) = (∇_z f)^[i], the Jacobian and the Lie derivative commute, (21)-(22). | [`LieDerivative.lean`](../../src/CORALean/Global/LieDerivative.lean) — `jacLift_lieIter`, for smooth `f`; the induction step is the symmetry of the second derivative | `correct` |
| `Example 3` | Rough enclosures [r₁], [R₁] for the Brusselator on [0, h]. | n/a — an illustration, computed by the prototype | `not-a-claim` |
| `Example 4` | First-order Taylor models of the Brusselator in affine arithmetic, (23)-(28). | n/a — an illustration, computed by the prototype | `not-a-claim` |
| `Example 5` | The solution from the center (2.075, 0.125) at h. | n/a — an illustration, computed by the prototype | `not-a-claim` |
| `Eq. 18` | (Step 3) If ]z[(t, t_j) = [z̃](t, t_j, [z̃_j]) + [J](t, t_j, [z_j]) * ([z̄₀, z̲₀] - z̃₀) is improper, pro ]z[(t, t_j) is an inner approximation of the set of solutions {z(t, z₀) \| z₀ ∈ z₀} at t; otherwise the inner approximation is empty. | [`KaucherInner.lean`](../../src/CORALean/Global/KaucherInner.lean), [`KaucherInnerBox.lean`](../../src/CORALean/Global/Counterexamples/KaucherInnerBox.lean) — `kaucherInnerStep_inner` for each component, `φ` the flow at `t` and the enclosures `[z̃] ∋ φ(z̃₀)`, `[J] ∋ ∂φ/∂z₀` hypotheses; the box of the components is not inside the set | `underspecified` — the inner approximation is per component, `pro ]z[ᵢ` inside the `i`-th projection, as Sec. 4 measures it; read as the box of all components it is false; see Findings |
| `Sec. 3.4` | Wider outer enclosures give tighter inner ones, possibly empty. | n/a — a discussion | `not-a-claim` |
| `Example 6` | [1.8973, 2.0400] ⊆ z₁(h, 0, [z₀]) ⊆ [1.88320, 2.05421] for the Brusselator. | n/a — an illustration, from the prototype's enclosures | `not-a-claim` |
| `Sec. 4` | Experiments: the Brusselator (Figs. 1-3), a 7-dimensional biological system (Fig. 4), comparisons with Chen et al. and Xue et al. | n/a — experiments | `not-a-claim` |

## Findings

**`Eq. 18` — per component, not a box.** Step 3 applies `Thm. 1`, a statement about a
real-valued function, to the flow; what it gives is `pro ]z[ᵢ ⊆ {zᵢ(t, z₀) | z₀ ∈ z₀}` for each
component `i` (`kaucherInnerStep_inner`), and Sec. 4 ("our method naturally gives inner ranges
for the projection of the flow system on its state variables") and `Example 6` use it that
way. Read as "the box `pro ]z[` is inside the set of solutions", Step 3 is false: for the
time-`1` flow `φ(x) = ((x₀ + x₁)/2, (x₁ - x₀)/2)` of a linear system on `[-1, 1]²`, with exact
enclosures, both components are `[-1, 1]` while the reachable set is the diamond
`|y₀| + |y₁| ≤ 1` (`kaucherInnerStep_box_counterexample`). The joint inner box needs the
argument of Goubault and Putot's 2020 `Thm. 3` (Brouwer), see
[that page](../2020/goubault-lcss-robust-underapproximations.md). CORA's `'proj'` stores the
box as its inner approximation, and writes `(-∞, ∞)` for a component whose (18) is proper
([`nonlinearSys` `reachInner`](../coverage/contDynamics/nonlinearSys.md)).

**`Alg. 1` — the Taylor models are an argument.** Steps 1 and 2 compute enclosures by the interval
Picard-Lindelöf iteration and the Taylor models (15)-(17), whose validity is that of the
validated integration of [25] and of the differentiability of the flow with respect to its initial
condition (variational equations, `Eq. 10`); CORALean has neither for this scheme. The loop is
formalized around them: the models enter as a function from the enclosures at `t_j` to the
enclosures at `t`, and `forwardInner_sound` proves what the loop adds, that Step 4's hand-over and
Step 3's (18) at every `t` of a step keep the enclosures valid and give per-component inner ranges,
from the hypothesis that the models are valid. The listing's Step 3 reads "`pro ]z[` is an
inner-approximation of the set of solutions"; read as the box of the components that is false (the
`Eq. 18` finding above), so the formalization states it per component.
