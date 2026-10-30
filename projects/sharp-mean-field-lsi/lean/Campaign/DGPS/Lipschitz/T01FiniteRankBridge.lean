import DGPS.Lipschitz.T01SpectralBridge
import DGPS.Particle.CenteredKernelMoments
import DGPS.Analysis.LSITensorization
import DGPS.Lipschitz.T01KernelGradientBridge
import DGPS.Particle.CenteredForceMoment
import SharpSymmetricLSI.Statements.R25_Lemma_A_2
import FullLabeledLSI.Defs.F05_FiniteRank

/-!
# Positive-mode finite-rank representation for the direct-Lipschitz replacement argument

The constant spectral mode is removed by kernel centering. Coefficients outside the stated
finite positive block are zero; no approximation property is inferred from that support fact.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

open KernelApproximation

variable {d : ℕ}

noncomputable def positiveKernelCoefficient (S : Spec d) (D : KData d) (t : ℝ)
    (m i j : ℕ) : ℝ :=
  if i < m ∧ j < m then
    Real.exp (-(t * (S.lam (i + 1) + S.lam (j + 1)))) * TK S D.K (i + 1) (j + 1)
  else 0

theorem positiveKernelCoefficient_symm (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x) (t : ℝ) (m i j : ℕ) :
    positiveKernelCoefficient S D t m i j = positiveKernelCoefficient S D t m j i := by
  by_cases h : i < m ∧ j < m
  · simp only [positiveKernelCoefficient, if_pos h, if_pos h.symm]
    rw [add_comm (S.lam (i + 1)), CenteredKernelMoments.TK_symm S D hK]
  · have h' : ¬(j < m ∧ i < m) := fun hj => h hj.symm
    simp only [positiveKernelCoefficient, if_neg h, if_neg h']

theorem positiveKernelCoefficient_support (S : Spec d) (D : KData d) (t : ℝ) (m i j : ℕ)
    (h : i ∉ Finset.range m ∨ j ∉ Finset.range m) :
    positiveKernelCoefficient S D t m i j = 0 := by
  unfold positiveKernelCoefficient
  simp only [Finset.mem_range] at h
  split_ifs with hij
  · exact False.elim (h.elim (fun hi => hi hij.1) (fun hj => hj hij.2))
  · rfl

theorem smoothK_eq_positive_block (S : Spec d) (aux : Aux S) (D : KData d)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (hK : ∀ x y, D.K x y = D.K y x)
    (t : ℝ) (m : ℕ) (x y : Torus d) :
    smoothK S D t m x y =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
        positiveKernelCoefficient S D t m i j * S.v (i + 1) x * S.v (j + 1) y := by
  have h0l := TK_zero_left S D aux.v0 hc
  have h0r := TK_zero_right S D aux.v0 hc hK
  unfold smoothK
  rw [Finset.sum_range_succ']
  simp only [h0l, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_range_succ']
  simp only [h0r, mul_zero, zero_mul, zero_add, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [positiveKernelCoefficient, if_pos ⟨Finset.mem_range.mp hi, Finset.mem_range.mp hj⟩]
  ring

theorem legacy_pair_H1_integral_eq (S : Spec d) (aux : Aux S) (D : KData d) :
    (∫⁻ X, ENNReal.ofReal ((SharpLSI.kerC2 D.K X) ^ 2 +
      SharpLSI.gradSqC (SharpLSI.kerC2 D.K) X)
      ∂Measure.pi (fun _ : Fin 2 => S.mu)) =
      ENNReal.ofReal ((∫ p, D.K p.1 p.2 ^ 2 ∂S.mu.prod S.mu) +
        (∫ p, ‖D.G1 p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu) +
        ∫ p, ‖D.G2 p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have h2 : Integrable (fun p : Torus d × Torus d => ‖D.G2 p.1 p.2‖ ^ 2)
      (S.mu.prod S.mu) :=
    Integrable.of_bound (D.G2m.norm.pow_const 2).aestronglyMeasurable (D.B ^ 2)
      (Eventually.of_forall fun p => by
        simp only [norm_pow, norm_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (D.G2b p.1 p.2) 2)
  have hi := ((D.integrable_K2 S).add (D.integrable_G1 S)).add h2
  calc
    _ = ∫⁻ X, ENNReal.ofReal ((D.K (X 0) (X 1)) ^ 2 +
        ‖D.G1 (X 0) (X 1)‖ ^ 2 + ‖D.G2 (X 0) (X 1)‖ ^ 2)
        ∂Measure.pi (fun _ : Fin 2 => S.mu) := by
      refine lintegral_congr_ae ?_
      filter_upwards [legacy_pair_gradSqC_ae S aux D] with X hX
      simp only [SharpLSI.kerC2, hX]
      congr 1
      ring
    _ = ∫⁻ p : Torus d × Torus d, ENNReal.ofReal (D.K p.1 p.2 ^ 2 +
        ‖D.G1 p.1 p.2‖ ^ 2 + ‖D.G2 p.1 p.2‖ ^ 2) ∂S.mu.prod S.mu :=
      SharpLSI.lintegral_pi_two _
    _ = ENNReal.ofReal (∫ p, D.K p.1 p.2 ^ 2 +
        ‖D.G1 p.1 p.2‖ ^ 2 + ‖D.G2 p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu) :=
      (ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall fun p => by
          change 0 ≤ D.K p.1 p.2 ^ 2 + ‖D.G1 p.1 p.2‖ ^ 2 + ‖D.G2 p.1 p.2‖ ^ 2
          positivity)).symm
    _ = _ := by
      have hadd := integral_add ((D.integrable_K2 S).add (D.integrable_G1 S)) h2
      have hadd' := integral_add (D.integrable_K2 S) (D.integrable_G1 S)
      simp only [Pi.add_apply] at hadd hadd'
      rw [hadd, hadd']

private theorem eLpNorm_top_tendsto_of_uniform_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (F : ℕ → α → ℝ)
    (hm : ∀ n, AEStronglyMeasurable (F n) μ)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x, ‖F n x‖ ≤ ε) :
    Tendsto (fun n => eLpNorm (F n) ⊤ μ) atTop (𝓝 0) := by
  refine SharpLSI.tendsto_zero_of_forall_real fun ε hε => ?_
  filter_upwards [h ε hε] with n hn
  simpa using eLpNorm_le_of_ae_bound (p := ⊤) (hm n) (Eventually.of_forall hn)

theorem legacy_pair_uniform_error_tendsto (S : Spec d)
    (F : ℕ → Torus d → Torus d → ℝ) (K : Torus d → Torus d → ℝ)
    (hF : ∀ n, Continuous (Function.uncurry (F n))) (hK : Continuous (Function.uncurry K))
    (h : TendstoUniformly (fun n (p : Torus d × Torus d) => F n p.1 p.2)
      (fun p => K p.1 p.2) atTop) :
    Tendsto (fun n => eLpNorm (fun X : SharpLSI.Config 2 d =>
      SharpLSI.kerC2 (F n) X - SharpLSI.kerC2 K X) ⊤
      (Measure.pi fun _ : Fin 2 => S.mu)) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  apply eLpNorm_top_tendsto_of_uniform_bound
  · intro n
    exact ((SharpLSI.continuous_kerC2 (hF n)).sub (SharpLSI.continuous_kerC2 hK)).aestronglyMeasurable
  · intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp h) ε hε] with n hn X
    simpa only [SharpLSI.kerC2, Real.norm_eq_abs, Real.dist_eq, abs_sub_comm] using (hn (X 0, X 1)).le

theorem legacy_centeredKernel_eq (J : InteractionData d) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] :
    SharpLSI.centeredKernel J.W μ = centeredKernel J μ := by
  funext x y
  unfold SharpLSI.centeredKernel centeredKernel SharpLSI.convMeas interactionConvolution
    SharpLSI.interE interactionEnergy
  rw [integral_prod_symm _ (J.W_continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]

noncomputable def smoothKernelData (S : Spec d) (aux : Aux S) (D : KData d)
    (t : ℝ) (m : ℕ) (C : ℝ)
    (h1 : ∀ x y, ‖smoothG1 S aux D t m x y‖ ≤ C)
    (h2 : ∀ x y, ‖smoothG2 S aux D t m x y‖ ≤ C) : KData d where
  K := smoothK S D t m
  G1 := smoothG1 S aux D t m
  G2 := smoothG2 S aux D t m
  Kc := CenteredKernelMoments.smoothK_continuous S D t m
  G1m := by
    rw [smoothG1_eq]
    exact G1fin_meas S aux D t (m + 1)
  G2m := by
    rw [smoothG2_eq]
    exact G2fin_meas S aux D t (m + 1)
  B := C
  G1b := h1
  G2b := h2
  g1 y := by
    rw [smoothK_eq, smoothG1_eq]
    exact Kfin_wg1 S aux D t (m + 1) y
  g2 x := by
    rw [smoothK_eq, smoothG2_eq]
    exact Kfin_wg2 S aux D t (m + 1) x

noncomputable def subKernelData (D E : KData d) : KData d where
  K x y := D.K x y - E.K x y
  G1 x y := D.G1 x y - E.G1 x y
  G2 x y := D.G2 x y - E.G2 x y
  Kc := D.Kc.sub E.Kc
  G1m := D.G1m.sub E.G1m
  G2m := D.G2m.sub E.G2m
  B := D.B + E.B
  G1b x y := (norm_sub_le _ _).trans (add_le_add (D.G1b x y) (E.G1b x y))
  G2b x y := (norm_sub_le _ _).trans (add_le_add (D.G2b x y) (E.G2b x y))
  g1 y := wg_sub (D.g1 y) (E.g1 y)
  g2 x := wg_sub (D.g2 x) (E.g2 x)

theorem legacy_smooth_pair_sup_bounds (S : Spec d) (aux : Aux S) (D : KData d)
    (t : ℝ) (m : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ x y, |smoothK S D t m x y| ≤ C)
    (h1 : ∀ x y, ‖smoothG1 S aux D t m x y‖ ≤ C)
    (h2 : ∀ x y, ‖smoothG2 S aux D t m x y‖ ≤ C) :
    eLpNorm (SharpLSI.kerC2 (smoothK S D t m)) ⊤ (Measure.pi fun _ : Fin 2 => S.mu) +
      eLpNorm (fun X => Real.sqrt (SharpLSI.gradSqC (SharpLSI.kerC2 (smoothK S D t m)) X))
        ⊤ (Measure.pi fun _ : Fin 2 => S.mu) ≤ ENNReal.ofReal C + ENNReal.ofReal (2 * C) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  let E := smoothKernelData S aux D t m C h1 h2
  have hval : eLpNorm (SharpLSI.kerC2 (smoothK S D t m)) ⊤
      (Measure.pi fun _ : Fin 2 => S.mu) ≤ ENNReal.ofReal C := by
    change eLpNorm (SharpLSI.kerC2 E.K) ⊤ (Measure.pi fun _ : Fin 2 => S.mu) ≤ ENNReal.ofReal C
    simpa using eLpNorm_le_of_ae_bound (p := ⊤)
      (SharpLSI.continuous_kerC2 E.Kc).aestronglyMeasurable
      (Eventually.of_forall fun X => by
        change |smoothK S D t m (X 0) (X 1)| ≤ C
        exact hK (X 0) (X 1))
  have hm : Measurable fun X : SharpLSI.Config 2 d =>
      Real.sqrt (‖E.G1 (X 0) (X 1)‖ ^ 2 + ‖E.G2 (X 0) (X 1)‖ ^ 2) :=
    (((E.G1m.comp SharpLSI.measurable_config_pair).norm.pow_const 2).add
      ((E.G2m.comp SharpLSI.measurable_config_pair).norm.pow_const 2)).sqrt
  have hgrad : eLpNorm (fun X => Real.sqrt (SharpLSI.gradSqC (SharpLSI.kerC2 E.K) X))
      ⊤ (Measure.pi fun _ : Fin 2 => S.mu) ≤ ENNReal.ofReal (2 * C) := by
    refine SharpLSI.eLpNorm_top_le_of_ae hm.aestronglyMeasurable
      ((legacy_pair_gradSqC_ae S aux E).mono fun X hX => congrArg Real.sqrt hX)
      (Eventually.of_forall fun X => ?_)
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hb1 := pow_le_pow_left₀ (norm_nonneg _) (h1 (X 0) (X 1)) 2
    have hb2 := pow_le_pow_left₀ (norm_nonneg _) (h2 (X 0) (X 1)) 2
    change ‖smoothG1 S aux D t m (X 0) (X 1)‖ ^ 2 +
      ‖smoothG2 S aux D t m (X 0) (X 1)‖ ^ 2 ≤ (2 * C) ^ 2
    nlinarith [sq_nonneg C]
  exact add_le_add hval hgrad

theorem legacy_smooth_diagonal_sup_bound (S : Spec d) (aux : Aux S) (D : KData d)
    (t : ℝ) (m : ℕ) {C : ℝ}
    (h1 : ∀ x y, ‖smoothG1 S aux D t m x y‖ ≤ C)
    (h2 : ∀ x y, ‖smoothG2 S aux D t m x y‖ ≤ C) :
    eLpNorm (fun x => Real.sqrt (SharpLSI.sqNorm
      (SharpLSI.weakGrad (fun z => smoothK S D t m z z) x))) ⊤ S.mu ≤ ENNReal.ofReal (2 * C) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hm1 : Measurable (Function.uncurry (smoothG1 S aux D t m)) := by
    rw [smoothG1_eq]
    exact G1fin_meas S aux D t (m + 1)
  have hm2 : Measurable (Function.uncurry (smoothG2 S aux D t m)) := by
    rw [smoothG2_eq]
    exact G2fin_meas S aux D t (m + 1)
  have hg : Measurable fun x => smoothG1 S aux D t m x x + smoothG2 S aux D t m x x :=
    (hm1.comp (measurable_id.prodMk measurable_id)).add
      (hm2.comp (measurable_id.prodMk measurable_id))
  have hae := S.ae_mu (DGPS.Analysis.legacy_memH1
    (CenteredForceMoment.smoothK_diag_wg S aux D t m)).2
  refine SharpLSI.eLpNorm_top_le_of_ae hg.norm.aestronglyMeasurable ?_
    (Eventually.of_forall fun x => ?_)
  · filter_upwards [hae] with x hx
    rw [hx, ← DGPS.Analysis.norm_sq_eq_sqNorm, Real.sqrt_sq (norm_nonneg _)]
  · rw [abs_of_nonneg (norm_nonneg _)]
    exact (norm_add_le _ _).trans (by
      change ‖smoothG1 S aux D t m x x‖ + ‖smoothG2 S aux D t m x x‖ ≤ 2 * C
      linarith [h1 x x, h2 x x])

theorem legacy_isKernelApprox_of_smoothing (J : InteractionData d) (S : Spec d)
    (aux : Aux S) (D : KData d) (hD : D.K = centeredKernel J S.mu)
    (t : ℕ → ℝ) (m : ℕ → ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ R x y, |smoothK S D (t R) (m R) x y| ≤ C)
    (h1 : ∀ R x y, ‖smoothG1 S aux D (t R) (m R) x y‖ ≤ C)
    (h2 : ∀ R x y, ‖smoothG2 S aux D (t R) (m R) x y‖ ≤ C)
    (hU : TendstoUniformly (fun R (p : Torus d × Torus d) =>
      smoothK S D (t R) (m R) p.1 p.2) (fun p => D.K p.1 p.2) atTop)
    (hH1 : Tendsto (fun R =>
      (∫ p, (D.K p.1 p.2 - smoothK S D (t R) (m R) p.1 p.2) ^ 2 ∂S.mu.prod S.mu) +
      (∫ p, ‖D.G1 p.1 p.2 - smoothG1 S aux D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu) +
      ∫ p, ‖D.G2 p.1 p.2 - smoothG2 S aux D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu)
      atTop (𝓝 0)) :
    SharpLSI.IsKernelApprox J.W S.mu S.v (fun R => smoothK S D (t R) (m R)) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hDs : D.K = SharpLSI.centeredKernel J.W S.mu :=
    hD.trans (legacy_centeredKernel_eq J S.mu).symm
  have hsym : ∀ x y, D.K x y = D.K y x := by
    intro x y
    rw [hD]
    exact centeredKernel_symm J S.mu x y
  have hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0 := by
    intro y
    simp only [hD, centeredKernel_symm J S.mu _ y]
    exact integral_centeredKernel_right J S.mu y
  unfold SharpLSI.IsKernelApprox
  rw [← hDs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro R
    exact ⟨Finset.range (m R), positiveKernelCoefficient S D (t R) (m R),
      positiveKernelCoefficient_symm S D hsym (t R) (m R),
      smoothK_eq_positive_block S aux D hc hsym (t R) (m R)⟩
  · exact legacy_pair_uniform_error_tendsto S (fun R => smoothK S D (t R) (m R)) D.K
      (fun R => CenteredKernelMoments.smoothK_continuous S D (t R) (m R)) D.Kc hU
  · let E R := smoothKernelData S aux D (t R) (m R) C (h1 R) (h2 R)
    let Q R := subKernelData (E R) D
    have heq : ∀ R, (∫⁻ X, ENNReal.ofReal
        ((SharpLSI.kerC (smoothK S D (t R) (m R)) X - SharpLSI.kerC D.K X) ^ 2 +
          SharpLSI.gradSqC (fun Y => SharpLSI.kerC (smoothK S D (t R) (m R)) Y -
            SharpLSI.kerC D.K Y) X) ∂Measure.pi (fun _ : Fin 2 => S.mu)) =
        ENNReal.ofReal ((∫ p, (D.K p.1 p.2 - smoothK S D (t R) (m R) p.1 p.2) ^ 2 ∂S.mu.prod S.mu) +
          (∫ p, ‖D.G1 p.1 p.2 - smoothG1 S aux D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu) +
          ∫ p, ‖D.G2 p.1 p.2 - smoothG2 S aux D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu) := by
      intro R
      change (∫⁻ X, ENNReal.ofReal ((SharpLSI.kerC2 (Q R).K X) ^ 2 +
        SharpLSI.gradSqC (SharpLSI.kerC2 (Q R).K) X) ∂Measure.pi (fun _ : Fin 2 => S.mu)) = _
      rw [legacy_pair_H1_integral_eq S aux (Q R)]
      have hk : (∫ p, (Q R).K p.1 p.2 ^ 2 ∂S.mu.prod S.mu) =
          ∫ p, (D.K p.1 p.2 - smoothK S D (t R) (m R) p.1 p.2) ^ 2 ∂S.mu.prod S.mu := by
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by dsimp [Q, E, subKernelData, smoothKernelData]; ring
      have hg1 : (∫ p, ‖(Q R).G1 p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu) =
          ∫ p, ‖D.G1 p.1 p.2 - smoothG1 S aux D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu := by
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by dsimp [Q, E, subKernelData, smoothKernelData]; rw [norm_sub_rev]
      have hg2 : (∫ p, ‖(Q R).G2 p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu) =
          ∫ p, ‖D.G2 p.1 p.2 - smoothG2 S aux D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu := by
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by dsimp [Q, E, subKernelData, smoothKernelData]; rw [norm_sub_rev]
      rw [hk, hg1, hg2]
    simp_rw [heq]
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hH1
  · refine ⟨ENNReal.ofReal C + ENNReal.ofReal (2 * C),
      ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩, fun R => ?_⟩
    exact legacy_smooth_pair_sup_bounds S aux D (t R) (m R) hC (hK R) (h1 R) (h2 R)
  · apply eLpNorm_top_tendsto_of_uniform_bound
    · intro R
      exact (((CenteredKernelMoments.smoothK_continuous S D (t R) (m R)).comp
        (continuous_id.prodMk continuous_id)).sub
          (D.Kc.comp (continuous_id.prodMk continuous_id))).aestronglyMeasurable
    · intro ε hε
      filter_upwards [(Metric.tendstoUniformly_iff.mp hU) ε hε] with R hR x
      simpa only [Real.norm_eq_abs, Real.dist_eq, abs_sub_comm] using (hR (x, x)).le
  · refine ⟨ENNReal.ofReal (2 * C), ENNReal.ofReal_lt_top, fun R => ?_⟩
    exact legacy_smooth_diagonal_sup_bound S aux D (t R) (m R) (h1 R) (h2 R)

theorem exists_legacy_finiteRankApprox (J : InteractionData d) (S : Spec d)
    (aux : Aux S) (D : KData d) (hD : D.K = centeredKernel J S.mu) :
    ∃ (t : ℕ → ℝ) (m : ℕ → ℕ) (F : SharpLSI.FL.FiniteRankApprox J.W S.mu S.v),
      (∀ R, 0 < t R) ∧ Tendsto t atTop (𝓝 0) ∧ StrictMono m ∧
      (∀ R, F.s R = Finset.range (m R)) ∧
      ∀ R i j, F.a R i j = positiveKernelCoefficient S D (t R) (m R) i j := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hsym : ∀ x y, D.K x y = D.K y x := by
    intro x y
    rw [hD]
    exact centeredKernel_symm J S.mu x y
  have hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0 := by
    intro y
    simp only [hD, centeredKernel_symm J S.mu _ y]
    exact integral_centeredKernel_right J S.mu y
  obtain ⟨t, m, C, ht, -, htend, hm, hC, hK, h1, h2, -, -, hU, hH1⟩ :=
    smoothed_approximation' S aux D
  have hApprox := legacy_isKernelApprox_of_smoothing J S aux D hD t m hC hK h1 h2 hU hH1
  let F : SharpLSI.FL.FiniteRankApprox J.W S.mu S.v := {
    s := fun R => Finset.range (m R)
    a := fun R => positiveKernelCoefficient S D (t R) (m R)
    symm := fun R => positiveKernelCoefficient_symm S D hsym (t R) (m R)
    supp := fun R i j => positiveKernelCoefficient_support S D (t R) (m R) i j
    approx := by
      have he : (fun R x y => ∑ i ∈ Finset.range (m R), ∑ j ∈ Finset.range (m R),
          positiveKernelCoefficient S D (t R) (m R) i j * S.v (i + 1) x * S.v (j + 1) y) =
          (fun R => smoothK S D (t R) (m R)) := by
        funext R x y
        exact (smoothK_eq_positive_block S aux D hc hsym (t R) (m R) x y).symm
      rw [he]
      exact hApprox }
  exact ⟨t, m, F, ht, htend, hm, fun _ => rfl, fun _ _ _ => rfl⟩

end DGPS.Lipschitz
