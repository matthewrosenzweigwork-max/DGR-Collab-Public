import DGPS.Examples.RoughBoundary.SemicontinuityCountersequence
import Mathlib.Topology.Semicontinuity.Defs

/-!
# Common smoothing sequence for SEM011

Source: preparation `SOURCE_MATERIAL/REGULARITY/ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md`,
sections 8.1--8.3 (S1). The widths are independent of the Hölder and Sobolev exponents.
The all-width bounded-profile persistence lemma gives the selected primary model and its
smooth landscape certificates without an exponent-dependent subsequence. Sobolev exponents
are real `p` with `1 ≤ p < 2`, passed to `eLpNorm` as `ENNReal.ofReal p`.
The exhibited gradients are identified with the topology's chosen gradients by L1 uniqueness.
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal NNReal ContDiff

namespace DGPS.Examples.RoughBoundary.Semicontinuity

open DGPS.Analysis.PeriodicMollification
open DGPS.Analysis.RateTopology
open DGPS.Examples.RoughBoundary.Spikes (pt)
open DGPS.Examples.RoughBoundary.Landscape (RoughLandscapeCertificate)

/-- A fixed positive mollification sequence, entirely below the support threshold. -/
noncomputable def width_SEM011 (j : ℕ) : ℝ := 1 / ((j : ℝ) + 5)

lemma width_pos_SEM011 (j : ℕ) : 0 < width_SEM011 j := by unfold width_SEM011; positivity

lemma width_lt_quarter_SEM011 (j : ℕ) : width_SEM011 j < 1 / 4 := by
  unfold width_SEM011
  apply (div_lt_div_iff₀ (by positivity) (by norm_num)).2
  have : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

lemma tendsto_width_SEM011 : Tendsto width_SEM011 atTop (𝓝 0) := by
  have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h := h0.comp (tendsto_add_atTop_nat 4)
  have he : width_SEM011 = (fun j : ℕ => 1 / ((j : ℝ) + 1)) ∘ (fun j : ℕ => j + 4) := by
    funext j
    dsimp [width_SEM011, Function.comp_def]
    congr 1
    push_cast
    ring
  rw [he]
  exact h

lemma smooth_profile_SEM011 (j : ℕ) : IsSmoothPeriodic (mollify (width_SEM011 j) Spikes.gT) :=
  isSmoothPeriodic_mollify (width_pos_SEM011 j)
    (continuous_gT.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

noncomputable def approximation_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) (j : ℕ) : RoughKernelClass :=
  smoothKernel_SEM011 hL η (smooth_profile_SEM011 j)

lemma primary_holder_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {α : ℝ≥0}
    (h0 : 0 < (α : ℝ)) (h1 : (α : ℝ) < 1) :
    ∃ C : ℝ≥0, HolderWith C α (primaryKernel_SEM011 hL η).W :=
  exists_holderWith_kernelOfProfile_SEM011 hL η h0 h1 (holder_gT h0 h1)

lemma approximation_holder_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {α : ℝ≥0}
    (h0 : 0 < (α : ℝ)) (h1 : (α : ℝ) < 1) (j : ℕ) :
    ∃ C : ℝ≥0, HolderWith C α (approximation_SEM011 hL η j).W :=
  exists_holderWith_kernelOfProfile_SEM011 hL η h0 h1
    (holderBdd_mollify_gT_SEM011 (width_pos_SEM011 j) h0 h1)

lemma tendsto_holder_approximation_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {α : ℝ≥0}
    (h0 : 0 < (α : ℝ)) (h1 : (α : ℝ) < 1) :
    @Tendsto ℕ (HolderKernel α)
      (fun j => ⟨approximation_SEM011 hL η j, approximation_holder_SEM011 hL η h0 h1 j⟩)
      atTop (@nhds _ (holderTopology α)
        ⟨primaryKernel_SEM011 hL η, primary_holder_SEM011 hL η h0 h1⟩) := by
  obtain ⟨M, -, H⟩ := kernel_diff_estimates_SEM011 hL η h0 h1
  have hγ : 0 < ((α : ℝ) + 1) / 2 - α := by linarith
  have ht : Tendsto (fun j => width_SEM011 j ^ (((α : ℝ) + 1) / 2 - α)) atTop (𝓝 0) := by
    simpa [Real.zero_rpow hγ.ne'] using
      tendsto_width_SEM011.rpow_const (.inr hγ.le)
  apply tendsto_holderKernel_SEM011 _ _ (fun j => M *
      width_SEM011 j ^ (((α : ℝ) + 1) / 2 - α))
    (by simpa using ht.const_mul M)
  · intro j z
    exact (H _ (width_pos_SEM011 j) (width_lt_quarter_SEM011 j)).1 z
  · intro j z z'
    exact (H _ (width_pos_SEM011 j) (width_lt_quarter_SEM011 j)).2 z z'

/-- The scalar weak derivative of the primary profile. -/
noncomputable def profileDeriv_SEM011 (y : Torus 1) : ℝ := Spikes.hSum y - Spikes.hMean

lemma profile_weakGradient_SEM011 {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) :
    IsWeakGradientLp (ENNReal.ofReal p) Spikes.gT
      (fun y => (EuclideanSpace.single 0 (profileDeriv_SEM011 y) : Tangent 1)) := by
  refine ⟨continuous_gT.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), ?_, ?_⟩
  · have hm := Spikes.memLp_hSum_sub_mean hp hp2
    refine MemLp.mono hm (continuous_single1.comp_aestronglyMeasurable hm.aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    simp [profileDeriv_SEM011]
  · intro φ hφ j
    rw [Subsingleton.elim j 0]
    simpa [profileDeriv_SEM011] using Spikes.weak_ibp hφ

lemma primary_sobolev_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {p : ℝ}
    (hp : 1 ≤ p) (hp2 : p < 2) :
    ∃ G, IsWeakGradientLp (ENNReal.ofReal p) (primaryKernel_SEM011 hL η).W G :=
  ⟨Model.gradW L η, Model.isWeakGradientLp_Wtor hL η hp hp2⟩

lemma approximation_sobolev_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ)
    (p : ℝ≥0∞) (j : ℕ) :
    ∃ G, IsWeakGradientLp p (approximation_SEM011 hL η j).W G :=
  ⟨_, isWeakGradientLp_prodKernel_SEM011 p
    (isSmoothPeriodic_UfeatF_SEM011 hL η (smooth_profile_SEM011 j))
    (coordPartial_UfeatF_SEM011 hL η (smooth_profile_SEM011 j))⟩


lemma tendsto_feature_sup_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) :
    Tendsto (fun j => vecSupNorm
      (Efun L η Spikes.gT (mollify (width_SEM011 j) Spikes.gT))) atTop (𝓝 0) := by
  obtain ⟨A, B, -, -, -, H⟩ := feature_diff_bounds_SEM011 hL η
    (α := 1 / 2) (β := 3 / 4) (by norm_num) (by norm_num) (by norm_num)
  have ht : Tendsto (fun j => A * width_SEM011 j ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_width_SEM011.rpow_const (.inr (by norm_num : (0 : ℝ) ≤ 1 / 4))
    simpa using h.const_mul A
  exact squeeze_zero (fun _ => vecSupNorm_nonneg _)
    (fun j => by
      convert (H _ (width_pos_SEM011 j) (width_lt_quarter_SEM011 j)).1 using 1; norm_num) ht

lemma tendsto_profile_sobolev_SEM011 {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) :
    Tendsto (fun j => eLpNorm
      (fun y => mollify (width_SEM011 j) Spikes.gT y - Spikes.gT y)
      (ENNReal.ofReal p) (haar 1)) atTop (𝓝 0) ∧
    Tendsto (fun j => eLpNorm
      (fun y => coordPartial 0 (mollify (width_SEM011 j) Spikes.gT) y -
        profileDeriv_SEM011 y) (ENNReal.ofReal p) (haar 1)) atTop (𝓝 0) := by
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have hg := profile_weakGradient_SEM011 hp hp2
  have h := strong_sobolev_mollification_including_p_equals_one.2.2.2
    width_SEM011 width_pos_SEM011 tendsto_width_SEM011 (ENNReal.ofReal p) hp'
    ENNReal.ofReal_ne_top Spikes.gT _ hg
  refine ⟨h.1, ?_⟩
  have hd : ∀ j, coordPartial 0 (mollify (width_SEM011 j) Spikes.gT) =
      mollify (width_SEM011 j) profileDeriv_SEM011 := fun j => by
    simpa using (isWeakGradientLp_mollify (width_pos_SEM011 j) hp' hg).1
  simpa [hd, mollifyGrad] using h.2

lemma tendsto_feature_deriv_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {p : ℝ}
    (hp : 1 ≤ p) (hp2 : p < 2) :
    Tendsto (fun j => eLpNorm
      (fun y => UprimeF L η (mollify (width_SEM011 j) Spikes.gT)
        (coordPartial 0 (mollify (width_SEM011 j) Spikes.gT)) y -
        Feature.Uprime L η y) (ENNReal.ofReal p) (haar 1)) atTop (𝓝 0) := by
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have hfm : AEStronglyMeasurable profileDeriv_SEM011 (haar 1) :=
    (Spikes.hSum_meas.sub measurable_const).aestronglyMeasurable
  have hgm := (continuous_gT.aestronglyMeasurable (μ := haar 1))
  have hdt : dthetaTF L η profileDeriv_SEM011 = Feature.dthetaT L η := by
    funext y
    exact (Feature.dthetaT_eq' L η y).symm
  have hdtfin : eLpNorm (dthetaTF L η profileDeriv_SEM011) (ENNReal.ofReal p) (haar 1) ≠ ⊤ := by
    rw [hdt]
    exact (Feature.memLp_dthetaT hL η hp hp2).eLpNorm_ne_top
  have hsup := ENNReal.tendsto_ofReal
    ((tendsto_feature_sup_SEM011 hL η).const_mul (2 * π))
  have hterm2 := ENNReal.Tendsto.mul_const hsup (Or.inr hdtfin)
  have hterm1 := ENNReal.Tendsto.const_mul
    (tendsto_profile_sobolev_SEM011 hp hp2).2 (a := ENNReal.ofReal (6 * |η|))
    (Or.inr ENNReal.ofReal_ne_top)
  have hterm1' := ENNReal.Tendsto.const_mul hterm1
    (a := ENNReal.ofReal (2 * π)) (Or.inr ENNReal.ofReal_ne_top)
  have hbound := hterm1'.add hterm2
  simp only [mul_zero, zero_mul, zero_add, ENNReal.ofReal_zero] at hbound
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => bot_le) (fun j => ?_)
  have hsm := ((smooth_profile_SEM011 j).continuous_torus.aestronglyMeasurable (μ := haar 1))
  have hsd := (((smooth_profile_SEM011 j).continuous_coordPartial 0).aestronglyMeasurable (μ := haar 1))
  have h := (quantitative_phase_composition_continuity hL η).2.2.2
    (ENNReal.ofReal p) hp' Spikes.gT profileDeriv_SEM011
    (mollify (width_SEM011 j) Spikes.gT)
    (coordPartial 0 (mollify (width_SEM011 j) Spikes.gT))
  have h1 := h.1 hgm hsm hfm hsd
  have h2 := h.2 (hsd.sub hfm)
  rw [h2] at h1
  have hprim : UprimeF L η Spikes.gT profileDeriv_SEM011 = Feature.Uprime L η := by
    change UprimeF L η Spikes.gT (fun y => Spikes.hSum y - Spikes.hMean) = _
    exact UprimeF_gT L η
  rw [hprim] at h1
  exact h1

lemma tendsto_kernel_Lp_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {p : ℝ}
    (hp : 1 ≤ p) (hp2 : p < 2) :
    Tendsto (fun j => eLpNorm
      (fun z => (approximation_SEM011 hL η j).W z - (primaryKernel_SEM011 hL η).W z)
      (ENNReal.ofReal p) (haar 2)) atTop (𝓝 0) := by
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have ht := (tendsto_profile_sobolev_SEM011 hp hp2).1
  have h1 := ENNReal.Tendsto.const_mul ht (a := ENNReal.ofReal |η|)
    (Or.inr ENNReal.ofReal_ne_top)
  have h2 := ENNReal.Tendsto.const_mul h1 (a := ENNReal.ofReal (2 * π))
    (Or.inr ENNReal.ofReal_ne_top)
  have h3 := ENNReal.Tendsto.const_mul h2 (a := ENNReal.ofReal (2 * Model.kappa))
    (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3
    (fun _ => bot_le) (fun j => ?_)
  exact prodKernel_UfeatF_Lp_le hL η hp' (continuous_gT.aestronglyMeasurable (μ := haar 1))
    ((smooth_profile_SEM011 j).continuous_torus.aestronglyMeasurable (μ := haar 1))
    (((smooth_profile_SEM011 j).continuous_torus.aestronglyMeasurable (μ := haar 1)).sub
      (continuous_gT.aestronglyMeasurable (μ := haar 1)))

/-- Sum bound for the two components of a tangent field. -/
lemma eLpNorm_tangent_le_SEM011 {F : Torus 2 → Tangent 2} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hF : AEStronglyMeasurable F (haar 2)) :
    eLpNorm F p (haar 2) ≤
      eLpNorm (fun z => F z 0) p (haar 2) + eLpNorm (fun z => F z 1) p (haar 2) := by
  have h0 := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp_aestronglyMeasurable hF
  have h1 := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp_aestronglyMeasurable hF
  calc _ ≤ eLpNorm (fun z => ‖F z 0‖ + ‖F z 1‖) p (haar 2) := by
        refine eLpNorm_mono_real hF fun z => ?_
        have e : F z = EuclideanSpace.single 0 (F z 0) + EuclideanSpace.single 1 (F z 1) := by
          ext i; fin_cases i <;> simp
        calc ‖F z‖ = ‖EuclideanSpace.single 0 (F z 0) + EuclideanSpace.single 1 (F z 1)‖ :=
              congrArg norm e
          _ ≤ ‖EuclideanSpace.single 0 (F z 0)‖ + ‖EuclideanSpace.single 1 (F z 1)‖ := norm_add_le _ _
          _ = _ := by simp
    _ ≤ eLpNorm (fun z => ‖F z 0‖) p (haar 2) + eLpNorm (fun z => ‖F z 1‖) p (haar 2) :=
      eLpNorm_add_le hp
    _ = _ := by rw [eLpNorm_norm _ h0, eLpNorm_norm _ h1]

noncomputable def approximationGrad_SEM011 (L η : ℝ) (j : ℕ) : Torus 2 → Tangent 2 :=
  prodGrad_SEM011 (UfeatF L η (mollify (width_SEM011 j) Spikes.gT))
    (UprimeF L η (mollify (width_SEM011 j) Spikes.gT)
      (coordPartial 0 (mollify (width_SEM011 j) Spikes.gT)))

lemma approximation_weakGradient_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) (p : ℝ≥0∞) (j : ℕ) :
    IsWeakGradientLp p (approximation_SEM011 hL η j).W (approximationGrad_SEM011 L η j) :=
  isWeakGradientLp_prodKernel_SEM011 p
    (isSmoothPeriodic_UfeatF_SEM011 hL η (smooth_profile_SEM011 j))
    (coordPartial_UfeatF_SEM011 hL η (smooth_profile_SEM011 j))

lemma primary_grad_eq_SEM011 (L η : ℝ) :
    Model.gradW L η = prodGrad_SEM011 (Feature.Ufeat L η) (Feature.Uprime L η) := rfl

lemma tendsto_kernel_grad_Lp_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {p : ℝ}
    (hp : 1 ≤ p) (hp2 : p < 2) :
    Tendsto (fun j => eLpNorm
      (fun z => approximationGrad_SEM011 L η j z - Model.gradW L η z)
      (ENNReal.ofReal p) (haar 2)) atTop (𝓝 0) := by
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have hu := ((Feature.continuous_Ufeat hL η).aestronglyMeasurable (μ := haar 1))
  have hu' := ((Model.measurable_Uprime_vec hL η).aestronglyMeasurable (μ := haar 1))
  have hufin : eLpNorm (Feature.Uprime L η) (ENNReal.ofReal p) (haar 1) ≠ ⊤ := by
    rw [← eLpNorm_norm _ hu']
    exact (Model.memLp_norm_Uprime hL η hp hp2).eLpNorm_ne_top
  have ht1 := tendsto_feature_deriv_SEM011 hL η hp hp2
  have ht2 := ENNReal.Tendsto.const_mul
    (ENNReal.tendsto_ofReal (tendsto_feature_sup_SEM011 hL η))
    (a := eLpNorm (Feature.Uprime L η) (ENNReal.ofReal p) (haar 1)) (Or.inr hufin)
  have ht := ENNReal.Tendsto.const_mul (ht1.add ht2)
    (a := ENNReal.ofReal Model.kappa) (Or.inr ENNReal.ofReal_ne_top)
  simp only [ENNReal.ofReal_zero, mul_zero, add_zero] at ht
  have hbound : ∀ j,
      eLpNorm (fun z => approximationGrad_SEM011 L η j z - Model.gradW L η z)
        (ENNReal.ofReal p) (haar 2) ≤
      (ENNReal.ofReal Model.kappa *
        (eLpNorm (fun y => UprimeF L η (mollify (width_SEM011 j) Spikes.gT)
          (coordPartial 0 (mollify (width_SEM011 j) Spikes.gT)) y - Feature.Uprime L η y)
          (ENNReal.ofReal p) (haar 1) +
        eLpNorm (Feature.Uprime L η) (ENNReal.ofReal p) (haar 1) *
          ENNReal.ofReal (vecSupNorm (Efun L η Spikes.gT
            (mollify (width_SEM011 j) Spikes.gT))))) +
      (ENNReal.ofReal Model.kappa *
        (eLpNorm (fun y => UprimeF L η (mollify (width_SEM011 j) Spikes.gT)
          (coordPartial 0 (mollify (width_SEM011 j) Spikes.gT)) y - Feature.Uprime L η y)
          (ENNReal.ofReal p) (haar 1) +
        eLpNorm (Feature.Uprime L η) (ENNReal.ofReal p) (haar 1) *
          ENNReal.ofReal (vecSupNorm (Efun L η Spikes.gT
            (mollify (width_SEM011 j) Spikes.gT))))) := by
    intro j
    have hm := ((smooth_profile_SEM011 j).continuous_torus.aestronglyMeasurable (μ := haar 1))
    have hmd := (((smooth_profile_SEM011 j).continuous_coordPartial 0).aestronglyMeasurable (μ := haar 1))
    have hv := aestronglyMeasurable_UfeatF L η hm
    have hv' := aestronglyMeasurable_UprimeF L η hm hmd
    have h := (quantitative_product_kernel_convergence
      (U := Feature.Ufeat L η) (Ut := UfeatF L η (mollify (width_SEM011 j) Spikes.gT))
      (U' := Feature.Uprime L η)
      (Ut' := UprimeF L η (mollify (width_SEM011 j) Spikes.gT)
        (coordPartial 0 (mollify (width_SEM011 j) Spikes.gT)))
      (Feature.norm_Ufeat L η) (norm_UfeatF L η _)).2.2 (ENNReal.ofReal p) hp' hu hv hu' hv'
    have hd := ((approximation_weakGradient_SEM011 hL η (ENNReal.ofReal p) j).memLp_grad.aestronglyMeasurable).sub
      (Model.memLp_gradW hL η hp hp2).aestronglyMeasurable
    refine (eLpNorm_tangent_le_SEM011 hp' hd).trans (add_le_add ?_ ?_)
    · have he : Efun L η Spikes.gT (mollify (width_SEM011 j) Spikes.gT) =
          (fun z => UfeatF L η (mollify (width_SEM011 j) Spikes.gT) z - Feature.Ufeat L η z) := rfl
      rw [he]
      simpa [approximationGrad_SEM011, primary_grad_eq_SEM011, prodGrad_SEM011] using h.1
    · have he : Efun L η Spikes.gT (mollify (width_SEM011 j) Spikes.gT) =
          (fun z => UfeatF L η (mollify (width_SEM011 j) Spikes.gT) z - Feature.Ufeat L η z) := rfl
      rw [he]
      simpa [approximationGrad_SEM011, primary_grad_eq_SEM011, prodGrad_SEM011] using h.2
  have hlim := ht.add ht
  simp only [add_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hbound


/-- The topology's selected gradient equals any exhibited weak gradient in `L^p`. -/
lemma sobolevEmbed_eq_gradient_SEM011 {p : ℝ≥0∞} (hp : 1 ≤ p)
    (K : SobolevKernel p) (G : Torus 2 → Tangent 2) (hG : IsWeakGradientLp p K.1.W G) :
    haveI : Fact (1 ≤ p) := ⟨hp⟩
    sobolevEmbed p K = (hG.memLp.toLp K.1.W, hG.memLp_grad.toLp G) := by
  let _ : Fact (1 ≤ p) := ⟨hp⟩
  apply Prod.ext
  · rfl
  · have h := Classical.choose_spec K.2
    apply MemLp.toLp_congr h.memLp_grad hG.memLp_grad
    exact IsWeakGradientLp.ae_eq_of_one
      ⟨h.memLp.mono_exponent hp, h.memLp_grad.mono_exponent hp, h.ibp⟩
      ⟨hG.memLp.mono_exponent hp, hG.memLp_grad.mono_exponent hp, hG.ibp⟩

lemma tendsto_sobolevKernel_SEM011 {p : ℝ≥0∞} (hp : 1 ≤ p)
    (Kj : ℕ → SobolevKernel p) (K : SobolevKernel p)
    (Gj : ℕ → Torus 2 → Tangent 2) (G : Torus 2 → Tangent 2)
    (hj : ∀ j, IsWeakGradientLp p (Kj j).1.W (Gj j))
    (hG : IsWeakGradientLp p K.1.W G)
    (hv : Tendsto (fun j => eLpNorm (fun z => (Kj j).1.W z - K.1.W z) p (haar 2)) atTop (𝓝 0))
    (hg : Tendsto (fun j => eLpNorm (fun z => Gj j z - G z) p (haar 2)) atTop (𝓝 0)) :
    haveI : Fact (1 ≤ p) := ⟨hp⟩
    @Tendsto ℕ (SobolevKernel p) Kj atTop (@nhds _ (sobolevTopology p) K) := by
  let _ : Fact (1 ≤ p) := ⟨hp⟩
  let _ : TopologicalSpace (SobolevKernel p) := sobolevTopology p
  rw [(sobolevEmbed_isEmbedding p).tendsto_nhds_iff]
  have e1 : sobolevEmbed p ∘ Kj =
      (fun j => ((hj j).memLp.toLp _, (hj j).memLp_grad.toLp _)) := by
    funext j
    exact sobolevEmbed_eq_gradient_SEM011 hp (Kj j) (Gj j) (hj j)
  have e2 : sobolevEmbed p K = (hG.memLp.toLp _, hG.memLp_grad.toLp _) :=
    sobolevEmbed_eq_gradient_SEM011 hp K G hG
  rw [e1, e2]
  apply Tendsto.prodMk_nhds
  · rw [tendsto_iff_edist_tendsto_0]
    simpa only [Lp.edist_toLp_toLp, Pi.sub_def] using hv
  · rw [tendsto_iff_edist_tendsto_0]
    simpa only [Lp.edist_toLp_toLp, Pi.sub_def] using hg

lemma tendsto_sobolev_approximation_SEM011 {L : ℝ} (hL : 0 < L) (η : ℝ) {p : ℝ}
    (hp : 1 ≤ p) (hp2 : p < 2) :
    haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by exact_mod_cast ENNReal.ofReal_le_ofReal hp⟩
    @Tendsto ℕ (SobolevKernel (ENNReal.ofReal p))
      (fun j => ⟨approximation_SEM011 hL η j, approximation_sobolev_SEM011 hL η _ j⟩)
      atTop (@nhds _ (sobolevTopology (ENNReal.ofReal p))
        ⟨primaryKernel_SEM011 hL η, primary_sobolev_SEM011 hL η hp hp2⟩) := by
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp
  exact tendsto_sobolevKernel_SEM011 hp' _ _ (approximationGrad_SEM011 L η) (Model.gradW L η)
    (approximation_weakGradient_SEM011 hL η (ENNReal.ofReal p))
    (Model.isWeakGradientLp_Wtor hL η hp hp2)
    (tendsto_kernel_Lp_SEM011 hL η hp hp2) (tendsto_kernel_grad_Lp_SEM011 hL η hp hp2)

noncomputable def scalarKernelRate_SEM011 (K : RoughKernelClass) : ℝ≥0∞ :=
  scalarRate K.toInteraction K.drift

noncomputable def speciesKernelRate_SEM011 (K : RoughKernelClass) : ℝ≥0∞ :=
  speciesRate K.toInteraction K.drift

lemma positive_a0_SEM011 : (0 : ℝ≥0∞) < ENNReal.ofReal (4 * π ^ 2) :=
  ENNReal.ofReal_pos.2 (by positivity)

lemma primary_rates_SEM011 {L : ℝ} (hL : 0 < L) {η : ℝ} (hη : η ≠ 0)
    (hc : RoughLandscapeCertificate (Feature.Ufeat L η)) :
    scalarKernelRate_SEM011 (primaryKernel_SEM011 hL η) = ENNReal.ofReal (4 * π ^ 2) ∧
    speciesKernelRate_SEM011 (primaryKernel_SEM011 hL η) = ENNReal.ofReal (4 * π ^ 2) := by
  have h := toInteraction_primaryKernel_SEM011 hL η
  let b : AbsoluteDrift (Model.modelData hL η) := h ▸ (primaryKernel_SEM011 hL η).drift
  have hdec := FreeEnergy.freeEnergyDecomposition_of_certificate η hc
  have hs := (Nonlinear.exact_scalar_rate_of_the_rough_example hL hη hdec b).1
  have hm := (Nonlinear.exact_arbitrary_finite_species_rate hL hη hdec b).1
  exact ⟨(scalarRate_congr_SEM011 h _ b).trans hs, (speciesRate_congr_SEM011 h _ b).trans hm⟩

lemma zero_sequence_not_lsc_SEM011 {X : Type*} [TopologicalSpace X] {f : X → ℝ≥0∞}
    {xs : ℕ → X} {x : X} (ht : Tendsto xs atTop (𝓝 x)) (hz : ∀ j, f (xs j) = 0)
    (hpos : 0 < f x) : ¬ LowerSemicontinuousAt f x := by
  intro hl
  have he := ht.eventually (hl 0 hpos)
  have hn : ∀ᶠ j in atTop, ¬ 0 < f (xs j) := Eventually.of_forall fun j => by simp [hz j]
  exact (he.and hn).exists.elim fun _ h => h.2 h.1

/-- SEM011: a single sequence of smooth kernels has both actual rates zero and converges
in every fixed strict Hölder and subcritical Sobolev norm to the primary kernel with both
rates `a0 = 4π² > 0`. The resulting rates fail lower semicontinuity in every such topology. -/
theorem lower_semicontinuity_countersequence :
    ∃ (L : ℝ) (hL : 0 < L),
      scalarKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) = ENNReal.ofReal (4 * π ^ 2) ∧
      speciesKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) = ENNReal.ofReal (4 * π ^ 2) ∧
      (0 : ℝ≥0∞) < ENNReal.ofReal (4 * π ^ 2) ∧
      (∀ j, IsSmoothPeriodic (approximation_SEM011 hL (1 / L) j).W ∧
        scalarKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0 ∧
        speciesKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0) ∧
      (∀ (α : ℝ≥0) (h0 : 0 < (α : ℝ)) (h1 : (α : ℝ) < 1),
        @Tendsto ℕ (HolderKernel α)
          (fun j => ⟨approximation_SEM011 hL (1 / L) j, approximation_holder_SEM011 hL _ h0 h1 j⟩)
          atTop (@nhds _ (holderTopology α)
            ⟨primaryKernel_SEM011 hL (1 / L), primary_holder_SEM011 hL _ h0 h1⟩) ∧
        (haveI := holderTopology α
         ¬ LowerSemicontinuousAt (fun K : HolderKernel α => scalarKernelRate_SEM011 K.1)
           ⟨primaryKernel_SEM011 hL (1 / L), primary_holder_SEM011 hL _ h0 h1⟩ ∧
         ¬ LowerSemicontinuousAt (fun K : HolderKernel α => speciesKernelRate_SEM011 K.1)
           ⟨primaryKernel_SEM011 hL (1 / L), primary_holder_SEM011 hL _ h0 h1⟩)) ∧
      (∀ (p : ℝ) (hp : 1 ≤ p) (hp2 : p < 2),
        haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by exact_mod_cast ENNReal.ofReal_le_ofReal hp⟩
        @Tendsto ℕ (SobolevKernel (ENNReal.ofReal p))
          (fun j => ⟨approximation_SEM011 hL (1 / L) j, approximation_sobolev_SEM011 hL _ _ j⟩)
          atTop (@nhds _ (sobolevTopology (ENNReal.ofReal p))
            ⟨primaryKernel_SEM011 hL (1 / L), primary_sobolev_SEM011 hL _ hp hp2⟩) ∧
        (haveI := sobolevTopology (ENNReal.ofReal p)
         ¬ LowerSemicontinuousAt (fun K : SobolevKernel (ENNReal.ofReal p) =>
           scalarKernelRate_SEM011 K.1)
           ⟨primaryKernel_SEM011 hL (1 / L), primary_sobolev_SEM011 hL _ hp hp2⟩ ∧
         ¬ LowerSemicontinuousAt (fun K : SobolevKernel (ENNReal.ofReal p) =>
           speciesKernelRate_SEM011 K.1)
           ⟨primaryKernel_SEM011 hL (1 / L), primary_sobolev_SEM011 hL _ hp hp2⟩)) := by
  obtain ⟨L, hL1, hcert⟩ := certificate_of_bounded_profile
  have hL : 0 < L := one_pos.trans_le hL1
  have hc : RoughLandscapeCertificate (Feature.Ufeat L (1 / L)) :=
    hcert L le_rfl Spikes.gT continuous_gT.measurable Spikes.abs_gT_le
  have hr := primary_rates_SEM011 hL (one_div_ne_zero hL.ne') hc
  have hz : ∀ j, scalarKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0 ∧
      speciesKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0 := fun j =>
    smoothKernel_rates_zero_SEM011 hL (1 / L) (smooth_profile_SEM011 j)
      (hcert L le_rfl _ (continuous_mollify_gT (width_pos_SEM011 j)).measurable
        (abs_mollify_gT_le (width_pos_SEM011 j))) _
  refine ⟨L, hL, hr.1, hr.2, positive_a0_SEM011, fun j => ⟨?_, hz j⟩, ?_, ?_⟩
  · exact isSmoothPeriodic_prodKernel_SEM011
      (isSmoothPeriodic_UfeatF_SEM011 hL (1 / L) (smooth_profile_SEM011 j))
  · intro α h0 h1
    have ht := tendsto_holder_approximation_SEM011 hL (1 / L) h0 h1
    refine ⟨ht, ?_⟩
    let _ := holderTopology α
    exact ⟨zero_sequence_not_lsc_SEM011 ht (fun j => (hz j).1) (by rw [hr.1]; exact positive_a0_SEM011),
      zero_sequence_not_lsc_SEM011 ht (fun j => (hz j).2) (by rw [hr.2]; exact positive_a0_SEM011)⟩
  · intro p hp hp2
    have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      exact_mod_cast ENNReal.ofReal_le_ofReal hp
    let _ : Fact (1 ≤ ENNReal.ofReal p) := ⟨hp'⟩
    have ht := tendsto_sobolev_approximation_SEM011 hL (1 / L) hp hp2
    refine ⟨ht, ?_⟩
    let _ := sobolevTopology (ENNReal.ofReal p)
    exact ⟨zero_sequence_not_lsc_SEM011 ht (fun j => (hz j).1) (by rw [hr.1]; exact positive_a0_SEM011),
      zero_sequence_not_lsc_SEM011 ht (fun j => (hz j).2) (by rw [hr.2]; exact positive_a0_SEM011)⟩

end DGPS.Examples.RoughBoundary.Semicontinuity
