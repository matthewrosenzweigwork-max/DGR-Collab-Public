import DGPS.FiniteN.Tools.Hubbard
import DGPS.FiniteN.Tools.GaussianCoupling
import DGPS.FiniteN.Tools.ConditionalMeanDerivative
import DGPS.FiniteN.Tools.BoundedComparison
import Mathlib

/-!
# From the auxiliary Poincare inequality to the unrestricted particle Poincare inequality (FIN013)

Setting: the finite-rank Hubbard identity (FIN010) writes the particle law `P_N` as the
`x`-marginal of the joint law `J` of `(w, x)`, with `w`-marginal `η_N` (`auxLaw`), conditional law
`q_w^{⊗N}` (`condLaw`) of `x` given `w`, and conditional law `N(h + D S(x)/N, D/N)` of `w` given
`x` (FIN011, `gaussLaw`).  Abstractly (test class `Sm`, carre-du-champ `Γ`, as in FIN004):

* `η_N` has Poincare rate `λ_aux` for bounded differentiable tests with the Euclidean gradient;
* `q_w^{⊗N}` has inverse Poincare constant `C(w)`;
* `E[C(w) | x] ≤ K` for every particle configuration `x`.

Then `Var_{P_N} f ≤ K (1 + N L² / λ_aux) ∫ Γ f dP_N` for every test `f` (no symmetry).
The proof: `Var f = E[Var(f | w)] + Var_η(M_f)`, the auxiliary Poincare inequality for `M_f` with
the gradient bound of FIN012, the conditional Poincare inequality, and reversal of the
disintegration to average `C(w)` over the posterior of `w` given `x`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DGPS.FiniteN.Tools.AuxiliaryTransfer

open DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling
  DGPS.FiniteN.Tools.ConditionalMeanDerivative DGPS.FiniteN.Tools.BoundedComparison

variable {k : ℕ}

/-- Test class on the auxiliary space `ℝ^k`: bounded differentiable functions. -/
def AuxTest (g : (Fin k → ℝ) → ℝ) : Prop :=
  (∃ B : ℝ, ∀ w, |g w| ≤ B) ∧ Differentiable ℝ g

/-- The Euclidean carre-du-champ `|∇g|²` on `ℝ^k`. -/
noncomputable def auxGradSq (g : (Fin k → ℝ) → ℝ) (w : Fin k → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ j, (fderiv ℝ g w (Pi.single j 1)) ^ 2)

section Disintegration

variable {M : Type*} [MeasurableSpace M] {m : Measure M} [IsFiniteMeasure m] {U : M → ℝ}
  {φ : M → Fin k → ℝ} (hyp : HubbardHyp m U φ) {D : Matrix (Fin k) (Fin k) ℝ}
include hyp

theorem isProbabilityMeasure_auxLaw (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) :
    IsProbabilityMeasure (auxLaw D h U φ m N) := by
  have := isProbabilityMeasure_hubbardJoint hyp (m := m) hD h N
  rw [← hubbardJoint_map_fst hyp hD h N]
  exact (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).2 inferInstance

theorem isProbabilityMeasure_particleLaw (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) :
    IsProbabilityMeasure (hubbardParticleLaw D h U φ m N) := by
  have := isProbabilityMeasure_hubbardJoint hyp (m := m) hD h N
  rw [← hubbardJoint_map_snd hyp hD h N]
  exact (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).2 inferInstance

/-- The kernel `w ↦ q_w^{⊗N}`. -/
noncomputable def condKernel (N : ℕ+) : Kernel (Fin k → ℝ) (Fin N → M) where
  toFun w := condLaw U φ m N w
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have h1 := measurable_kernelFn hyp (N := N) (measurable_snd hs)
    have h2 : (fun w => condLaw U φ m N w s) = kernelFn U φ m (Prod.snd ⁻¹' s) := by
      funext w
      exact pi_siteLaw_slice hyp (measurable_snd hs) w
    simpa [h2] using h1

theorem condKernel_apply (N : ℕ+) (w : Fin k → ℝ) :
    (condKernel hyp N) w = condLaw U φ m N w := rfl

instance isMarkovKernel_condKernel (N : ℕ+) : IsMarkovKernel (condKernel hyp N) :=
  ⟨fun w => by
    rw [condKernel_apply]
    exact isProbabilityMeasure_condLaw hyp N w⟩

/-- The kernel `x ↦ N(h + D S(x)/N, D/N)` (posterior of `w` given `x`). -/
noncomputable def gaussKernel (h : Fin k → ℝ) (N : ℕ+) : Kernel (Fin N → M) (Fin k → ℝ) where
  toFun x := gaussLaw D N (posteriorCenter D h φ N x)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    exact measurable_gaussKernel hyp D h N (s := Prod.fst ⁻¹' s) (measurable_fst hs)

omit [IsFiniteMeasure m] in
theorem gaussKernel_apply (h : Fin k → ℝ) (N : ℕ+) (x : Fin N → M) :
    (gaussKernel (D := D) hyp h N) x = gaussLaw D N (posteriorCenter D h φ N x) := rfl

omit [IsFiniteMeasure m] in
theorem isMarkovKernel_gaussKernel (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) :
    IsMarkovKernel (gaussKernel (D := D) hyp h N) :=
  ⟨fun x => by
    rw [gaussKernel_apply]
    rw [← map_stdGaussian_affine hD N (posteriorCenter D h φ N x)]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_affineMap D N _).aemeasurable).2 inferInstance⟩

theorem hubbardJoint_eq_compProd (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) :
    hubbardJoint D h U φ m N = (auxLaw D h U φ m N).compProd (condKernel hyp N) := by
  have := isProbabilityMeasure_auxLaw hyp hD h N
  refine Measure.ext fun s hs => ?_
  rw [hubbardJoint_apply hyp hD h N hs, Measure.compProd_apply hs]
  rfl

theorem hubbardJoint_swap_eq (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) :
    (hubbardJoint D h U φ m N).map Prod.swap =
      (hubbardParticleLaw D h U φ m N).compProd (gaussKernel (D := D) hyp h N) := by
  have := isProbabilityMeasure_particleLaw hyp hD h N
  have := isMarkovKernel_gaussKernel hyp hD h N
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply measurable_swap hs,
    hubbardJoint_eq_gauss hyp hD h N (measurable_swap hs), Measure.compProd_apply hs]
  rfl

/-- Disintegration of the joint law along `w`. -/
theorem lintegral_joint_eq (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+)
    {G : (Fin k → ℝ) × (Fin N → M) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ z, G z ∂(hubbardJoint D h U φ m N) =
      ∫⁻ w, ∫⁻ x, G (w, x) ∂(condLaw U φ m N w) ∂(auxLaw D h U φ m N) := by
  have := isProbabilityMeasure_auxLaw hyp hD h N
  have := isMarkovKernel_condKernel hyp N
  rw [hubbardJoint_eq_compProd hyp hD h N, Measure.lintegral_compProd hG]
  rfl

/-- Disintegration of the joint law along `x` (reversed disintegration). -/
theorem lintegral_joint_eq_gauss (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+)
    {G : (Fin k → ℝ) × (Fin N → M) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ z, G z ∂(hubbardJoint D h U φ m N) =
      ∫⁻ x, ∫⁻ w, G (w, x) ∂(gaussLaw D N (posteriorCenter D h φ N x))
        ∂(hubbardParticleLaw D h U φ m N) := by
  have := isProbabilityMeasure_particleLaw hyp hD h N
  have := isMarkovKernel_gaussKernel hyp hD h N
  have h1 : ∫⁻ z, G z ∂(hubbardJoint D h U φ m N) =
      ∫⁻ y, (G ∘ Prod.swap) y ∂((hubbardJoint D h U φ m N).map Prod.swap) := by
    rw [lintegral_map (hG.comp measurable_swap) measurable_swap]
    simp
  rw [h1, hubbardJoint_swap_eq hyp hD h N, Measure.lintegral_compProd (hG.comp measurable_swap)]
  rfl

/-- Real-valued disintegration of bounded measurable observables along `w`. -/
theorem integral_particle_eq (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+)
    {g : (Fin N → M) → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    ∫ x, g x ∂(hubbardParticleLaw D h U φ m N) =
      ∫ w, ∫ x, g x ∂(condLaw U φ m N w) ∂(auxLaw D h U φ m N) := by
  have := isProbabilityMeasure_auxLaw hyp hD h N
  have := isMarkovKernel_condKernel hyp N
  have := isProbabilityMeasure_hubbardJoint hyp (m := m) hD h N
  have hint : Integrable (fun z : (Fin k → ℝ) × (Fin N → M) => g z.2)
      ((auxLaw D h U φ m N).compProd (condKernel hyp N)) := by
    rw [← hubbardJoint_eq_compProd hyp hD h N]
    exact Integrable.of_bound (hg.comp measurable_snd).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hB z.2)
  rw [← hubbardJoint_map_snd hyp hD h N, integral_map measurable_snd.aemeasurable
    hg.aestronglyMeasurable, hubbardJoint_eq_compProd hyp hD h N, Measure.integral_compProd hint]
  rfl

theorem abs_condMean_le (N : ℕ+) {g : (Fin N → M) → ℝ} {B : ℝ} (hB : ∀ x, |g x| ≤ B)
    (w : Fin k → ℝ) : |condMean U φ m N g w| ≤ B := by
  have := isProbabilityMeasure_condLaw hyp N w
  have := norm_integral_le_of_norm_le_const (μ := condLaw U φ m N w) (f := g) (C := B)
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
  simpa [condMean, Real.norm_eq_abs] using this

theorem measurable_condMean (N : ℕ+) {g : (Fin N → M) → ℝ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ x, |g x| ≤ B) : Measurable (condMean U φ m N g) := by
  have hc : Continuous (condMean U φ m N g) :=
    continuous_iff_continuousAt.2 fun w => (hasFDerivAt_condMean hyp hg hB w).continuousAt
  exact hc.measurable

/-- Total variance = average conditional variance + variance of the conditional mean. -/
theorem ofReal_variance_split (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+)
    {f : (Fin N → M) → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    ENNReal.ofReal (variance f (hubbardParticleLaw D h U φ m N)) =
      ∫⁻ w, ENNReal.ofReal (variance f (condLaw U φ m N w)) ∂(auxLaw D h U φ m N) +
        evariance (condMean U φ m N f) (auxLaw D h U φ m N) := by
  have := isProbabilityMeasure_auxLaw hyp hD h N
  have := isProbabilityMeasure_particleLaw hyp hD h N
  have hf2 : Measurable fun x => f x ^ 2 := hf.pow_const 2
  have hB2 : ∀ x, |f x ^ 2| ≤ B ^ 2 := fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
  set a := condMean U φ m N f with ha
  set b := condMean U φ m N (fun x => f x ^ 2) with hb
  have ham : Measurable a := measurable_condMean hyp N hf hB
  have hbm : Measurable b := measurable_condMean hyp N hf2 hB2
  have habd : ∀ w, |a w| ≤ B := abs_condMean_le hyp N hB
  have hbbd : ∀ w, |b w| ≤ B ^ 2 := abs_condMean_le hyp N hB2
  have hbdd : ∀ {g : (Fin N → M) → ℝ} {C : ℝ}, Measurable g → (∀ x, |g x| ≤ C) →
      ∀ ν : Measure (Fin N → M), IsFiniteMeasure ν → MemLp g 2 ν := fun hg hC ν _ =>
    MemLp.of_bound hg.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
  have hbddw : ∀ {g : (Fin k → ℝ) → ℝ} {C : ℝ}, Measurable g → (∀ x, |g x| ≤ C) →
      MemLp g 2 (auxLaw D h U φ m N) := fun hg hC =>
    MemLp.of_bound hg.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
  have hfP : MemLp f 2 (hubbardParticleLaw D h U φ m N) := hbdd hf hB _ inferInstance
  have hVw : ∀ w, variance f (condLaw U φ m N w) = b w - a w ^ 2 := by
    intro w
    have := isProbabilityMeasure_condLaw hyp N w
    rw [variance_eq_sub (hbdd hf hB _ inferInstance)]
    simp [ha, hb, condMean]
  have hint_a : Integrable a (auxLaw D h U φ m N) :=
    Integrable.of_bound ham.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun w => by simpa [Real.norm_eq_abs] using habd w)
  have hint_b : Integrable b (auxLaw D h U φ m N) :=
    Integrable.of_bound hbm.aestronglyMeasurable (B ^ 2)
      (Filter.Eventually.of_forall fun w => by simpa [Real.norm_eq_abs] using hbbd w)
  have hint_a2 : Integrable (fun w => a w ^ 2) (auxLaw D h U φ m N) :=
    (hbddw ham habd).integrable_sq
  have hI1 : ∫ x, f x ∂(hubbardParticleLaw D h U φ m N) = ∫ w, a w ∂(auxLaw D h U φ m N) :=
    integral_particle_eq hyp hD h N hf hB
  have hI2 : ∫ x, f x ^ 2 ∂(hubbardParticleLaw D h U φ m N) =
      ∫ w, b w ∂(auxLaw D h U φ m N) :=
    integral_particle_eq hyp hD h N hf2 hB2
  have hvarP : variance f (hubbardParticleLaw D h U φ m N) =
      ∫ w, variance f (condLaw U φ m N w) ∂(auxLaw D h U φ m N) +
        variance a (auxLaw D h U φ m N) := by
    rw [variance_eq_sub hfP, variance_eq_sub (hbddw ham habd)]
    simp only [hVw, Pi.pow_apply]
    rw [integral_sub hint_b hint_a2, hI1]
    rw [hI2]
    ring
  have hV0 : ∀ w, 0 ≤ variance f (condLaw U φ m N w) := fun w => variance_nonneg _ _
  have hVint : Integrable (fun w => variance f (condLaw U φ m N w)) (auxLaw D h U φ m N) := by
    simp only [hVw]
    exact hint_b.sub hint_a2
  rw [hvarP, ENNReal.ofReal_add (integral_nonneg hV0) (variance_nonneg _ _),
    ofReal_integral_eq_lintegral_ofReal hVint (Filter.Eventually.of_forall hV0),
    (hbddw ham habd).ofReal_variance_eq]

end Disintegration

section Transfer

variable {M : Type*} [MeasurableSpace M] {m : Measure M} [IsFiniteMeasure m] {U : M → ℝ}
  {φ : M → Fin k → ℝ} (hyp : HubbardHyp m U φ) {D : Matrix (Fin k) (Fin k) ℝ}
include hyp

/-- **Abstract auxiliary-to-particle Poincare transfer.** -/
theorem poincare_transfer (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) {lam : ℝ} (hlam : 0 < lam)
    (haux : PoincareAt (auxLaw D h U φ m N) AuxTest auxGradSq lam⁻¹)
    {Sm : ((Fin N → M) → ℝ) → Prop} {Γ : ((Fin N → M) → ℝ) → (Fin N → M) → ℝ≥0∞}
    (hSm : ∀ f, Sm f → Measurable f ∧ ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hΓ : ∀ f, Sm f → Measurable (Γ f))
    {C : (Fin k → ℝ) → ℝ} (hC : Measurable C)
    (hcond : ∀ w, PoincareAt (condLaw U φ m N w) Sm Γ (C w))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, ∫⁻ w, ENNReal.ofReal (C w) ∂(gaussLaw D N (posteriorCenter D h φ N x)) ≤
      ENNReal.ofReal K)
    {L : ℝ} (hL : ∀ x, √(∑ j, φ x j ^ 2) ≤ L) :
    PoincareAt (hubbardParticleLaw D h U φ m N) Sm Γ (K * (1 + N * L ^ 2 / lam)) := by
  intro f hfS
  obtain ⟨hf, B, hB⟩ := hSm f hfS
  have hΓf := hΓ f hfS
  have := isProbabilityMeasure_auxLaw hyp hD h N
  have := isProbabilityMeasure_particleLaw hyp hD h N
  set P := hubbardParticleLaw D h U φ m N with hP
  set η := auxLaw D h U φ m N with hη
  set a := condMean U φ m N f with ha
  have hder : ∀ w, HasFDerivAt a (lin (condGrad U φ m N f w)) w :=
    fun w => hasFDerivAt_condMean hyp hf hB w
  have ha_diff : Differentiable ℝ a := fun w => (hder w).differentiableAt
  have ha_bdd : ∃ B' : ℝ, ∀ w, |a w| ≤ B' := ⟨B, abs_condMean_le hyp N hB⟩
  set T : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal (C w) * ∫⁻ x, Γ f x ∂(condLaw U φ m N w) ∂η with hT
  have hV : ∫⁻ w, ENNReal.ofReal (variance f (condLaw U φ m N w)) ∂η ≤ T :=
    lintegral_mono fun w => by
      have := isProbabilityMeasure_condLaw hyp N w
      have hmem : MemLp f 2 (condLaw U φ m N w) :=
        MemLp.of_bound hf.aestronglyMeasurable B
          (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
      rw [hmem.ofReal_variance_eq]
      exact hcond w f hfS
  have hgrad : ∫⁻ w, auxGradSq a w ∂η ≤ ENNReal.ofReal (N * L ^ 2) * T := by
    calc ∫⁻ w, auxGradSq a w ∂η
        ≤ ∫⁻ w, ENNReal.ofReal (N * L ^ 2) *
            ENNReal.ofReal (variance f (condLaw U φ m N w)) ∂η := by
          refine lintegral_mono fun w => ?_
          unfold auxGradSq
          have hfd : fderiv ℝ a w = lin (condGrad U φ m N f w) := (hder w).fderiv
          have hs : ∑ j, (fderiv ℝ a w (Pi.single j 1)) ^ 2 =
              ∑ j, condGrad U φ m N f w j ^ 2 := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hfd, lin_apply]
            simp [Pi.single_apply]
          rw [hs, ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal
            (condGrad_sq_le hyp hf hB w hL)
      _ = ENNReal.ofReal (N * L ^ 2) *
            ∫⁻ w, ENNReal.ofReal (variance f (condLaw U φ m N w)) ∂η :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (N * L ^ 2) * T := by gcongr
  have haux' := haux a ⟨ha_bdd, ha_diff⟩
  have hsplit := ofReal_variance_split hyp hD h N hf hB
  have hfP : MemLp f 2 P :=
    MemLp.of_bound hf.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
  have hx : 0 ≤ (N : ℝ) * L ^ 2 / lam := by positivity
  have hstep : evariance f P ≤ ENNReal.ofReal (1 + N * L ^ 2 / lam) * T := by
    calc evariance f P
        = ∫⁻ w, ENNReal.ofReal (variance f (condLaw U φ m N w)) ∂η + evariance a η := by
          rw [← hfP.ofReal_variance_eq]; exact hsplit
      _ ≤ T + ENNReal.ofReal lam⁻¹ * (ENNReal.ofReal (N * L ^ 2) * T) :=
          add_le_add hV (haux'.trans (by gcongr))
      _ = ENNReal.ofReal (1 + N * L ^ 2 / lam) * T := by
          have e : lam⁻¹ * ((N : ℝ) * L ^ 2) = N * L ^ 2 / lam := by
            rw [div_eq_inv_mul]
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hlam.le), e,
            ENNReal.ofReal_add zero_le_one hx, ENNReal.ofReal_one, add_mul, one_mul]
  have hCm : Measurable fun w => ENNReal.ofReal (C w) := ENNReal.measurable_ofReal.comp hC
  have hTle : T ≤ ENNReal.ofReal K * ∫⁻ x, Γ f x ∂P := by
    have hG : Measurable fun z : (Fin k → ℝ) × (Fin N → M) => ENNReal.ofReal (C z.1) * Γ f z.2 :=
      (hCm.comp measurable_fst).mul (hΓf.comp measurable_snd)
    have e1 : T = ∫⁻ z, ENNReal.ofReal (C z.1) * Γ f z.2 ∂(hubbardJoint D h U φ m N) := by
      rw [lintegral_joint_eq hyp hD h N hG]
      refine lintegral_congr fun w => ?_
      exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    rw [e1, lintegral_joint_eq_gauss hyp hD h N hG]
    calc ∫⁻ x, ∫⁻ w, ENNReal.ofReal (C w) * Γ f x
          ∂(gaussLaw D N (posteriorCenter D h φ N x)) ∂P
        = ∫⁻ x, (∫⁻ w, ENNReal.ofReal (C w)
          ∂(gaussLaw D N (posteriorCenter D h φ N x))) * Γ f x ∂P :=
          lintegral_congr fun x => lintegral_mul_const _ hCm
      _ ≤ ∫⁻ x, ENNReal.ofReal K * Γ f x ∂P :=
          lintegral_mono fun x => by gcongr; exact hK x
      _ = ENNReal.ofReal K * ∫⁻ x, Γ f x ∂P := lintegral_const_mul _ hΓf
  calc evariance f P ≤ ENNReal.ofReal (1 + N * L ^ 2 / lam) * T := hstep
    _ ≤ ENNReal.ofReal (1 + N * L ^ 2 / lam) * (ENNReal.ofReal K * ∫⁻ x, Γ f x ∂P) :=
        by gcongr
    _ = ENNReal.ofReal (K * (1 + N * L ^ 2 / lam)) * ∫⁻ x, Γ f x ∂P := by
        rw [ENNReal.ofReal_mul hK0]; ring

end Transfer

end DGPS.FiniteN.Tools.AuxiliaryTransfer

namespace DGPS.FiniteN

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling
  DGPS.FiniteN.Tools.ConditionalMeanDerivative DGPS.FiniteN.Tools.BoundedComparison
  DGPS.FiniteN.Tools.AuxiliaryTransfer

/-- Monotonicity of a Poincare inequality in its constant. -/
theorem poincareAt_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Sm : (Ω → ℝ) → Prop}
    {Γ : (Ω → ℝ) → Ω → ℝ≥0∞} {C C' : ℝ} (h : PoincareAt μ Sm Γ C) (hCC : C ≤ C') :
    PoincareAt μ Sm Γ C' := fun f hf =>
  (h f hf).trans (by gcongr)

/-- **FIN013.** Auxiliary Poincare inequality (rate `lam` for `η_N`), conditional inverse Poincare
constants `C(w)` with posterior average bounded by `K`, and `|φ| ≤ L` give the unrestricted particle
Poincare inequality `Var_{P_N} f ≤ K (1 + N L² / lam) ∫ Γ f dP_N` for every test `f`; then the
power-law and exponential rate consequences. -/
theorem auxiliary_to_unrestricted_particle_poincare {k : ℕ} {M : Type*} [MeasurableSpace M]
    {m : Measure M} [IsFiniteMeasure m] {U : M → ℝ} {φ : M → Fin k → ℝ}
    (hyp : HubbardHyp m U φ) {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef) (h : Fin k → ℝ)
    (N : ℕ+) {lam : ℝ} (hlam : 0 < lam)
    (haux : PoincareAt (auxLaw D h U φ m N) AuxTest auxGradSq lam⁻¹)
    {Sm : ((Fin N → M) → ℝ) → Prop} {Γ : ((Fin N → M) → ℝ) → (Fin N → M) → ℝ≥0∞}
    (hSm : ∀ f, Sm f → Measurable f ∧ ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hΓ : ∀ f, Sm f → Measurable (Γ f))
    {C : (Fin k → ℝ) → ℝ} (hC : Measurable C)
    (hcond : ∀ w, PoincareAt (condLaw U φ m N w) Sm Γ (C w))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, ∫⁻ w, ENNReal.ofReal (C w) ∂(gaussLaw D N (posteriorCenter D h φ N x))
      ≤ ENNReal.ofReal K)
    {L : ℝ} (hL : ∀ x, √(∑ j, φ x j ^ 2) ≤ L) :
    PoincareAt (hubbardParticleLaw D h U φ m N) Sm Γ (K * (1 + N * L ^ 2 / lam)) :=
  poincare_transfer hyp hD h N hlam haux hSm hΓ hC hcond hK0 hK hL

/-- Power-law rate: `lam ≥ c N^α`, `0 ≤ α ≤ 1` gives inverse constant `≤ (c' N^(α-1))⁻¹`. -/
theorem auxiliary_to_unrestricted_particle_poincare_power {k : ℕ} {M : Type*}
    [MeasurableSpace M] {m : Measure M} [IsFiniteMeasure m] {U : M → ℝ} {φ : M → Fin k → ℝ}
    (hyp : HubbardHyp m U φ) {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef) (h : Fin k → ℝ)
    (N : ℕ+) {lam c α : ℝ} (hc : 0 < c) (hα1 : α ≤ 1)
    (hlam : c * (N : ℝ) ^ α ≤ lam)
    (haux : PoincareAt (auxLaw D h U φ m N) AuxTest auxGradSq lam⁻¹)
    {Sm : ((Fin N → M) → ℝ) → Prop} {Γ : ((Fin N → M) → ℝ) → (Fin N → M) → ℝ≥0∞}
    (hSm : ∀ f, Sm f → Measurable f ∧ ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hΓ : ∀ f, Sm f → Measurable (Γ f))
    {C : (Fin k → ℝ) → ℝ} (hC : Measurable C)
    (hcond : ∀ w, PoincareAt (condLaw U φ m N w) Sm Γ (C w))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, ∫⁻ w, ENNReal.ofReal (C w) ∂(gaussLaw D N (posteriorCenter D h φ N x))
      ≤ ENNReal.ofReal K)
    {L : ℝ} (hL : ∀ x, √(∑ j, φ x j ^ 2) ≤ L) :
    ∃ c' : ℝ, 0 < c' ∧
      PoincareAt (hubbardParticleLaw D h U φ m N) Sm Γ ((c' * (N : ℝ) ^ (α - 1))⁻¹) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hN0 : (0 : ℝ) < N := by linarith
  have hpos : 0 < c * (N : ℝ) ^ α := mul_pos hc (Real.rpow_pos_of_pos hN0 _)
  have hlam0 : 0 < lam := hpos.trans_le hlam
  have hmain := auxiliary_to_unrestricted_particle_poincare hyp hD h N hlam0 haux hSm hΓ hC hcond
    hK0 hK hL
  set s : ℝ := (N : ℝ) ^ (1 - α) with hs
  have hs1 : 1 ≤ s := Real.one_le_rpow hN1 (by linarith)
  have hsN : (N : ℝ) = (N : ℝ) ^ α * s := by
    rw [hs, ← Real.rpow_add hN0]; simp
  set K' : ℝ := max K 1 with hK'
  have hK'1 : 1 ≤ K' := le_max_right _ _
  have hKK' : K ≤ K' := le_max_left _ _
  set A : ℝ := K' * (1 + L ^ 2 / c) with hA
  have hA0 : 0 < A := by positivity
  refine ⟨A⁻¹, inv_pos.2 hA0, poincareAt_mono hmain ?_⟩
  have hinv : ((A⁻¹ * (N : ℝ) ^ (α - 1))⁻¹) = A * s := by
    have : (N : ℝ) ^ (α - 1) = s⁻¹ := by
      rw [hs, ← Real.rpow_neg hN0.le]; congr 1; ring
    rw [this, mul_inv, inv_inv, inv_inv]
  rw [hinv]
  have hq : (N : ℝ) * L ^ 2 / lam ≤ L ^ 2 / c * s := by
    calc (N : ℝ) * L ^ 2 / lam ≤ (N : ℝ) * L ^ 2 / (c * (N : ℝ) ^ α) :=
          div_le_div_of_nonneg_left (by positivity) hpos hlam
      _ = L ^ 2 / c * s := by
          have : (N : ℝ) ^ α ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
          calc (N : ℝ) * L ^ 2 / (c * (N : ℝ) ^ α)
              = ((N : ℝ) ^ α * s) * L ^ 2 / (c * (N : ℝ) ^ α) := by rw [← hsN]
            _ = L ^ 2 / c * s := by field_simp
  have h2 : 1 + (N : ℝ) * L ^ 2 / lam ≤ (1 + L ^ 2 / c) * s := by
    have : 0 ≤ L ^ 2 / c := by positivity
    nlinarith
  calc K * (1 + (N : ℝ) * L ^ 2 / lam) ≤ K' * ((1 + L ^ 2 / c) * s) := by
        apply mul_le_mul hKK' h2 (by positivity) (by linarith)
    _ = A * s := by rw [hA]; ring

/-- Exponential rate: `lam ≥ c e^{-N B}`, `B ≥ 0` gives inverse constant
`≤ (c' N⁻¹ e^{-N B})⁻¹`. -/
theorem auxiliary_to_unrestricted_particle_poincare_exp {k : ℕ} {M : Type*}
    [MeasurableSpace M] {m : Measure M} [IsFiniteMeasure m] {U : M → ℝ} {φ : M → Fin k → ℝ}
    (hyp : HubbardHyp m U φ) {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef) (h : Fin k → ℝ)
    (N : ℕ+) {lam c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (hlam : c * Real.exp (-((N : ℝ) * B)) ≤ lam)
    (haux : PoincareAt (auxLaw D h U φ m N) AuxTest auxGradSq lam⁻¹)
    {Sm : ((Fin N → M) → ℝ) → Prop} {Γ : ((Fin N → M) → ℝ) → (Fin N → M) → ℝ≥0∞}
    (hSm : ∀ f, Sm f → Measurable f ∧ ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hΓ : ∀ f, Sm f → Measurable (Γ f))
    {C : (Fin k → ℝ) → ℝ} (hC : Measurable C)
    (hcond : ∀ w, PoincareAt (condLaw U φ m N w) Sm Γ (C w))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, ∫⁻ w, ENNReal.ofReal (C w) ∂(gaussLaw D N (posteriorCenter D h φ N x))
      ≤ ENNReal.ofReal K)
    {L : ℝ} (hL : ∀ x, √(∑ j, φ x j ^ 2) ≤ L) :
    ∃ c' : ℝ, 0 < c' ∧
      PoincareAt (hubbardParticleLaw D h U φ m N) Sm Γ
        ((c' * ((N : ℝ)⁻¹ * Real.exp (-((N : ℝ) * B))))⁻¹) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hN0 : (0 : ℝ) < N := by linarith
  have hpos : 0 < c * Real.exp (-((N : ℝ) * B)) := mul_pos hc (Real.exp_pos _)
  have hlam0 : 0 < lam := hpos.trans_le hlam
  have hmain := auxiliary_to_unrestricted_particle_poincare hyp hD h N hlam0 haux hSm hΓ hC hcond
    hK0 hK hL
  set s : ℝ := (N : ℝ) * Real.exp ((N : ℝ) * B) with hs
  have hNB : 0 ≤ (N : ℝ) * B := by positivity
  have hs1 : 1 ≤ s := by
    have : 1 ≤ Real.exp ((N : ℝ) * B) := Real.one_le_exp hNB
    nlinarith
  have hs0 : 0 < s := by linarith
  set K' : ℝ := max K 1 with hK'
  have hK'1 : 1 ≤ K' := le_max_right _ _
  have hKK' : K ≤ K' := le_max_left _ _
  set A : ℝ := K' * (1 + L ^ 2 / c) with hA
  have hA0 : 0 < A := by positivity
  refine ⟨A⁻¹, inv_pos.2 hA0, poincareAt_mono hmain ?_⟩
  have hinv : ((A⁻¹ * ((N : ℝ)⁻¹ * Real.exp (-((N : ℝ) * B))))⁻¹) = A * s := by
    rw [Real.exp_neg, hs]
    field_simp
  rw [hinv]
  have hq : (N : ℝ) * L ^ 2 / lam ≤ L ^ 2 / c * s := by
    calc (N : ℝ) * L ^ 2 / lam ≤ (N : ℝ) * L ^ 2 / (c * Real.exp (-((N : ℝ) * B))) :=
          div_le_div_of_nonneg_left (by positivity) hpos hlam
      _ ≤ L ^ 2 / c * s := by
          rw [Real.exp_neg, hs]
          have : 0 < Real.exp ((N : ℝ) * B) := Real.exp_pos _
          apply le_of_eq
          field_simp
  have h2 : 1 + (N : ℝ) * L ^ 2 / lam ≤ (1 + L ^ 2 / c) * s := by
    have : 0 ≤ L ^ 2 / c := by positivity
    nlinarith
  calc K * (1 + (N : ℝ) * L ^ 2 / lam) ≤ K' * ((1 + L ^ 2 / c) * s) := by
        apply mul_le_mul hKK' h2 (by positivity) (by linarith)
    _ = A * s := by rw [hA]; ring

end DGPS.FiniteN
