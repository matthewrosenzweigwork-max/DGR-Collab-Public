import DGPS.Frontier.LIP051.T01
import DGPS.Frontier.LIP051.T05
import DGPS.Frontier.LIP051.T24

/-!
# LIP051.CLOSE: Joint Gaussian and quadratic fluctuation limit

Task id `LIP051.CLOSE`, title "Joint Gaussian and quadratic fluctuation limit" (closing unit of
node LIP051). Prerequisite modules: `DGPS.Frontier.LIP051.T01` (campaign data and the Wick limit
`Q_T`), `DGPS.Frontier.LIP051.T05` (completeness of the product basis) and
`DGPS.Frontier.LIP051.T24` (arbitrary finite positive-coordinate block, with
`DGPS.Frontier.LIP051.T23`, `T14` and their helpers underneath).

Frozen statement (informal). For `Z_{N,j} = N^{-1/2} ∑_{l=1}^N e_j(X_l)`, every finite
coordinate block jointly with `U_N` converges under `Q_N` to standard product Gaussian
coordinates jointly with `U_∞ = (Q_T + d_K) / 2`. Here `Q_T` is the `L²` Wick quadratic limit and
`d_K = ∫ K(x, x) dμ`, not an assumed operator trace.

## Provides

* `DGPS.Lipschitz.joint_gaussian_and_quadratic_fluctuation_limit`: the closing statement. For the
  campaign data `(S, A, D, J, hD)` and every block `j : Fin m → ℕ` of positive modes (a)
  `Q_T` is the `L²(γ)` limit of the Wick sections, (b) for every measurable version `Q'` of the
  class `Q_T`, the pair (block of `Z_{N,j(k)}`, `U_N`) converges in distribution under the
  product laws `μ^{⊗N}` to the pair (block of coordinates `z (j k)`, `(Q' z + d_K) / 2`) under the
  countable standard Gaussian product measure, (c) for injective `j` the block of limit
  coordinates has the standard product Gaussian law on `ℝ^m`, (d) `d_K = ∫ K(x, x) dμ`.
* `DGPS.Lipschitz.jointFluctuationLimit_LIP051CLOSE`: the closing statement in the campaign gate
  form `JointFluctuationLimit_LIP05101 S D.K` (blocks `Fin m` with index `i + 1`, every `m`).
* `DGPS.Lipschitz.wickQuad_eq_LIP051CLOSE` (helper): the Wick quadratic as a double sum minus the
  trace-like diagonal sum.
* `DGPS.Lipschitz.bounded_W_LIP051CLOSE` (helper): the interaction kernel is bounded (continuity
  on a compact space).
* `DGPS.Lipschitz.coefT_eq_TK_LIP051CLOSE` (helper): the abstract coefficient of the LIP051.34
  interface equals the campaign coefficient `TK`.
* `DGPS.Lipschitz.lpNorm_wick_tendsto_LIP051CLOSE` (helper): `L²` convergence of the campaign
  Wick sections gives the explicit `lpNorm` form used by the abstract interface.
* `DGPS.Lipschitz.original_kernel_eq_LIP051CLOSE` (helper): the original kernel is the centered
  kernel of the abstract interface, as a function.
* `DGPS.Lipschitz.joint_core_LIP051CLOSE` (helper): the joint convergence for the centered kernel
  of the abstract interface, from LIP051.23 at rank `rankLIP05124 j` and the continuous
  projection `blockProj_LIP05124 j`.

## R5 notes

1. The target declaration. The frozen name did not exist in the campaign, so it is declared here
   in namespace `DGPS.Lipschitz`. Its binders are `(S : Spec d) (A : Aux S) (D : KData d)
   (J : InteractionData d) (hD)` with `hD : ∀ x y, D.K x y = centeredKernel J
   (specProbability_LIP016 S) x y`, the same campaign header as LIP016 and as the proposal in the
   LIP051.01 notes. The Hessian-coercivity binders of the LIP016 header are not assumed. `A : Aux S`
   is used only for `S.e 0 = 1` (`spectralBasis_zero_LIP016`), which LIP051.23 needs. No
   hypothesis beyond these binders and the block data is added.
2. Positive modes (defect FD-002). The block is `j : Fin m → ℕ` with `hpos : ∀ k, 0 < j k`. The
   mode index `0` is never quantified over, and `m = 0` is allowed. The constant mode would give
   `Z_{N,0} = sqrt N`, which LIP051.01 refutes
   (`gate_lip051_01_bind_campaign_data_source_data_zero_mode`). The campaign gate form is also
   proved, for the blocks `i + 1` with `i < m`.
3. Distinctness. "Coordinate block" is read as a family of positive mode indices. The
   convergence in distribution does not need the indices to be distinct, so no `Function.Injective`
   hypothesis is placed on it, which is strictly stronger than LIP051.24 (that theorem carries an
   injectivity binder for all of its conjuncts). Injectivity appears only as the antecedent of
   the product-law conjunct, where it is genuinely required (a repeated index gives a diagonal
   law). For this reason the proof applies LIP051.23 and the LIP051.24 helpers
   (`rankLIP05124`, `blockProj_LIP05124`) directly rather than the LIP051.24 theorem.
4. Features. `Z_{N,j}` is `Z_LIP05101 S N j`, built from the continuous representatives `S.v j`
   of the basis classes `S.e j`. Representative independence is part of LIP051.01
   (`gate_lip051_01_bind_campaign_data_source_data_Z`).
5. The Wick object. `Q_T` is `QT_LIP05101 S D.K`, the `L²` limit class of the unsmoothed positive
   rectangular Wick sections over `Finset.Icc 1 R`. Conjunct (a) states that the sections tend to
   it in `Lp ℝ 2 gaussianCountable_LIP016`. The limit in distribution is stated for every
   measurable function `Q'` that agrees almost everywhere with a representative of the class
   `Q_T`, so no choice of representative is hidden. The explicit `lpNorm` form of conjunct (a) with
   `wickQuad_LIP05116` is available as the helper `lpNorm_wick_tendsto_LIP051CLOSE`.
6. Original diagonal. `hD` is pointwise, so `D.K` is the centered kernel as a function, diagonal
   included. `U_N` and `d_K` use the pointwise diagonal. `d_K` is the integral of that diagonal
   (conjunct (d)), not an `L²` class and not an operator trace.
7. Boundedness. A bound on `J.W` is not assumed. LIP051.23 needs one, and it is obtained from the
   continuity of `J.W` on the compact torus product.
8. Prerequisite modules. `DGPS.Frontier.LIP051.T05` is a listed prerequisite of this unit and is
   brought in so that the whole prerequisite set builds together. No declaration of that module
   occurs in the proofs below; the closing argument uses `T01`, `T03`, `T14`, `T23`, `T24` and the
   campaign modules they rely on.
9. Non-literal reading of "converges under `Q_N`". This is Mathlib's `TendstoInDistribution` along
   `atTop` in `N`, with the laws `refLaw_LIP05101 S N = Measure.pi (fun _ => S.mu)` and the limit
   law `gaussianCountable_LIP016 = Measure.infinitePi (fun _ => gaussianReal 0 1)`. Terms with
   `N = 0` take Lean's junk values and do not affect the limit.
10. "Standard product Gaussian coordinates". The limit coordinates are the evaluations `z (j k)`
   under `gaussianCountable_LIP016`. The product-law conjunct states, for injective `j`, that
   the law of the block `(z (j k))_k` in `Fin m → ℝ` is `Measure.pi` of standard Gaussians
   (LIP051.14). The joint law with `U_∞` is not asserted to factor, which matches the
   specification (`Q_T` is a function of all coordinates).
11. Proof route. Transport the campaign data to the abstract data `(μ, W, e, f)` of LIP051.23 and
   LIP051.24 (the bridge `lip051_03_centering_integrability_original_kernel_eq_centeredKernel`,
   `coefT_eq_TK_LIP051CLOSE`, `lpNorm_wick_tendsto_LIP051CLOSE`), apply LIP051.23 at the rank
   `rankLIP05124 j`, and push forward by the continuous projection `blockProj_LIP05124 j`
   (`TendstoInDistribution.continuous_comp`). The convergence of the Wick sections is
   LIP051.01 (`wickSection_tendsto_LIP05101`), and the product law is LIP051.14.
12. Lean-exposed specification defects: none found beyond the zero-mode defect FD-002 already
   handled in note 2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent DGPS.Lipschitz
  DGPS.Lipschitz.KernelApproximation DGPS.Frontier.LIP051

namespace DGPS.Lipschitz

/-- The Wick quadratic as a double sum minus the diagonal sum of the coefficients. -/
theorem wickQuad_eq_LIP051CLOSE (s : Finset ℕ) (A : ℕ → ℕ → ℝ) (z : ℕ → ℝ) :
    wickQuad_LIP05116 s A z = (∑ i ∈ s, ∑ j ∈ s, A i j * z i * z j) - ∑ i ∈ s, A i i := by
  unfold wickQuad_LIP05116
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp [hi]

/-- The interaction kernel is bounded: continuity on the compact product of two tori. -/
theorem bounded_W_LIP051CLOSE {d : ℕ} (J : InteractionData d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x y, |J.W x y| ≤ M := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn J.W_continuous.continuousOn
  exact ⟨|C|, abs_nonneg _, fun x y => by
    simpa using (hC (x, y) (Set.mem_univ _)).trans (le_abs_self C)⟩

/-- The abstract coefficient of the LIP051.34 interface is the campaign coefficient `TK` of the
abstract centered kernel. -/
theorem coefT_eq_TK_LIP051CLOSE {d : ℕ} (S : Spec d) (W : Torus d → Torus d → ℝ) (i j : ℕ) :
    coefT_LIP05134 S.mu W S.v i j = TK S (centeredKernelOf_LIP05103 S.mu W) i j := by
  unfold coefT_LIP05134 TK
  exact integral_congr_ae (Filter.Eventually.of_forall fun p => mul_assoc _ _ _)

/-- `L²` convergence of the campaign Wick sections to a class `Q`, together with the identification
of the coefficients with `A`, gives the explicit `lpNorm` form of the abstract interface. -/
theorem lpNorm_wick_tendsto_LIP051CLOSE {d : ℕ} (S : Spec d) (K : Torus d → Torus d → ℝ)
    (A : ℕ → ℕ → ℝ) (hA : ∀ i j, TK S K i j = A i j) (Q : Lp ℝ 2 gaussianCountable_LIP016)
    (h : Tendsto (wickSection_LIP05101 S K) atTop (𝓝 Q)) :
    Tendsto (fun R : ℕ => lpNorm (fun z : ℕ → ℝ =>
      wickQuad_LIP05116 (Finset.Icc 1 R) A z - (Q : (ℕ → ℝ) → ℝ) z) 2 gam_LIP05144)
      atTop (𝓝 0) := by
  refine (tendsto_iff_norm_sub_tendsto_zero.mp h).congr fun R => ?_
  rw [Lp.norm_def]
  unfold lpNorm
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub (wickSection_LIP05101 S K R) Q, wickSection_ae_LIP05101 S K R]
    with z hz1 hz2
  rw [hz1, Pi.sub_apply, hz2, wickQuad_eq_LIP051CLOSE]
  simp only [hA]

/-- The original kernel is the abstract centered kernel, as a function. -/
theorem original_kernel_eq_LIP051CLOSE {d : ℕ} (S : Spec d) (D : KData d) (J : InteractionData d)
    (hD : ∀ x y, D.K x y = centeredKernel J (specProbability_LIP016 S) x y) :
    D.K = centeredKernelOf_LIP05103 S.mu J.W := by
  funext x y
  exact (hD x y).trans
    (lip051_03_centering_integrability_original_kernel_eq_centeredKernel J
      (specProbability_LIP016 S) x y).symm

/-- The joint convergence for the abstract centered kernel, for every block of positive modes. -/
theorem joint_core_LIP051CLOSE {d : ℕ} (S : Spec d) (A : Aux S) (J : InteractionData d)
    (K : Torus d → Torus d → ℝ) (hK : K = centeredKernelOf_LIP05103 S.mu J.W)
    (hwick : Tendsto (wickSection_LIP05101 S K) atTop (𝓝 (QT_LIP05101 S K)))
    {m : ℕ} (j : Fin m → ℕ) (hpos : ∀ k, 0 < j k)
    (Q' : (ℕ → ℝ) → ℝ) (hQ'm : Measurable Q')
    (hQ'eq : Q' =ᵐ[gaussianCountable_LIP016] (QT_LIP05101 S K : (ℕ → ℝ) → ℝ)) :
    TendstoInDistribution
      (fun (N : ℕ) (x : Fin N → Torus d) =>
        ((WithLp.toLp 2 (fun k : Fin m => Z_LIP05101 S N (j k) x) : EuclideanSpace ℝ (Fin m)),
          U_LIP05101 K N x))
      atTop
      (fun z : ℕ → ℝ => ((WithLp.toLp 2 (fun k : Fin m => z (j k)) : EuclideanSpace ℝ (Fin m)),
        (Q' z + dK_LIP05101 S K) / 2))
      (fun N => refLaw_LIP05101 S N) gaussianCountable_LIP016 := by
  subst hK
  obtain ⟨M, hM, hb⟩ := bounded_W_LIP051CLOSE J
  have hfm : ∀ i, Measurable (S.v i) := fun i => (S.vc i).measurable
  have hfe : ∀ i, S.v i =ᵐ[S.mu] ((S.e i : Hw d S.w) : Torus d → ℝ) :=
    fun i => S.ae_mu (S.ve i)
  have he0 : S.e 0 = Lp.const 2 S.mu (1 : ℝ) := spectralBasis_zero_LIP016 S A
  have hQmem : MemLp (QT_LIP05101 S (centeredKernelOf_LIP05103 S.mu J.W) : (ℕ → ℝ) → ℝ) 2
      gam_LIP05144 := Lp.memLp _
  have hlim := lpNorm_wick_tendsto_LIP051CLOSE S (centeredKernelOf_LIP05103 S.mu J.W)
    (coefT_LIP05134 S.mu J.W S.v) (fun i j => (coefT_eq_TK_LIP051CLOSE S J.W i j).symm)
    _ hwick
  have hconv := (lip051_23_pass_infinite_rank (μ := S.mu) J.W_continuous J.W_symm hM hb S.e he0
    S.v hfm hfe (m := rankLIP05124 j) (rank_pos_LIP05124 j)).2 _ hQmem hlim Q' hQ'm hQ'eq
  refine (hconv.continuous_comp (continuous_blockProj_LIP05124 j)).congr
    (fun n => Filter.Eventually.of_forall fun x => ?_)
    (Filter.Eventually.of_forall fun z => ?_)
  · exact blockProj_apply_LIP05124 j hpos (fun i => zLIP05121 n S.v i x) _
  · exact blockProj_apply_LIP05124 j hpos z _

/-- Joint Gaussian and quadratic fluctuation limit (LIP051 closing statement). See the module
docstring, R5 notes. For the campaign data `(S, A, D, J, hD)` and a block `j` of positive modes:
(a) the Wick sections tend to `Q_T` in `L²` of the countable Gaussian product measure; (b) for
every measurable version `Q'` of the class `Q_T`, the pair (block `Z_{N,j(k)}`, `U_N`) converges in
distribution under the product laws to the pair (coordinates `z (j k)`, `(Q' z + d_K) / 2`) under
the countable Gaussian product measure; (c) for injective `j` the limit coordinates have the
standard product Gaussian law; (d) `d_K` is the integral of the diagonal of `K`. -/
theorem joint_gaussian_and_quadratic_fluctuation_limit {d : ℕ} (S : Spec d) (A : Aux S)
    (D : KData d) (J : InteractionData d)
    (hD : ∀ x y, D.K x y = centeredKernel J (specProbability_LIP016 S) x y)
    {m : ℕ} (j : Fin m → ℕ) (hpos : ∀ k, 0 < j k) :
    Tendsto (wickSection_LIP05101 S D.K) atTop (𝓝 (QT_LIP05101 S D.K)) ∧
    (∀ Q' : (ℕ → ℝ) → ℝ, Measurable Q' →
      Q' =ᵐ[gaussianCountable_LIP016] (QT_LIP05101 S D.K : (ℕ → ℝ) → ℝ) →
      TendstoInDistribution
        (fun (N : ℕ) (x : Fin N → Torus d) =>
          ((WithLp.toLp 2 (fun k : Fin m => Z_LIP05101 S N (j k) x) : EuclideanSpace ℝ (Fin m)),
            U_LIP05101 D.K N x))
        atTop
        (fun z : ℕ → ℝ => ((WithLp.toLp 2 (fun k : Fin m => z (j k)) : EuclideanSpace ℝ (Fin m)),
          (Q' z + dK_LIP05101 S D.K) / 2))
        (fun N => refLaw_LIP05101 S N) gaussianCountable_LIP016) ∧
    (Function.Injective j →
      gaussianCountable_LIP016.map (fun (z : ℕ → ℝ) (k : Fin m) => z (j k)) =
        Measure.pi (fun _ : Fin m => gaussianReal 0 1)) ∧
    dK_LIP05101 S D.K = ∫ x, D.K x x ∂S.mu := by
  have hwick : Tendsto (wickSection_LIP05101 S D.K) atTop (𝓝 (QT_LIP05101 S D.K)) :=
    wickSection_tendsto_LIP05101 S A D (original_kernel_symmetric_LIP016 S D J hD)
      (original_kernel_centered_LIP016 S D J hD)
  refine ⟨hwick, fun Q' hQ'm hQ'eq => ?_, fun hinj => ?_, rfl⟩
  · exact joint_core_LIP051CLOSE S A J D.K (original_kernel_eq_LIP051CLOSE S D J hD) hwick j hpos
      Q' hQ'm hQ'eq
  · exact lip051_14_countable_gaussian_product_block_law j hinj

/-- The closing statement in the campaign gate form: for every `m`, the block of the first `m`
positive modes (indices `i + 1`) jointly with `U_N` converges in distribution to the block of
Gaussian coordinates jointly with `(Q_T + d_K) / 2`. -/
theorem jointFluctuationLimit_LIP051CLOSE {d : ℕ} (S : Spec d) (A : Aux S) (D : KData d)
    (J : InteractionData d)
    (hD : ∀ x y, D.K x y = centeredKernel J (specProbability_LIP016 S) x y) :
    JointFluctuationLimit_LIP05101 S D.K := by
  intro m
  exact (joint_gaussian_and_quadratic_fluctuation_limit S A D J hD
    (m := m) (fun i : Fin m => i.val + 1) (fun i => Nat.succ_pos _)).2.1
    (QT_LIP05101 S D.K : (ℕ → ℝ) → ℝ) (Lp.stronglyMeasurable _).measurable Filter.EventuallyEq.rfl

end DGPS.Lipschitz
