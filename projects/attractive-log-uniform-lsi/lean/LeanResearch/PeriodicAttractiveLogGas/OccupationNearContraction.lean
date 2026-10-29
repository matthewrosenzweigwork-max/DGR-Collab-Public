import LeanResearch.PeriodicAttractiveLogGas.OccupationPartitionTransport
import LeanResearch.PeriodicAttractiveLogGas.ReferenceConvolutionGradient
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.Topology.MetricSpace.Contracting

/-! The actual near-uniform occupation map, source Lemma
`lem:occupation-contraction`.  The convolution estimates below apply to
signed L4 functions; no bounded-density assumption is inserted in the
probability ball.  Source correspondence and checking history are recorded
in `research/reviews/occupation-near-contraction-development.md`. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

namespace PeriodicAttractiveLogGas.OccupationNearContraction

open MeshCells GreenConditionalInfluence

def densityPotential (f : Torus → ℝ) (x : Torus) : ℝ :=
  ∫ y, f y * regularGreenRepresentative (x - y) ∂torusMeasure

def regularizedPotential (f : Torus → ℝ) (ε : ℝ) (hε : 0 < ε) (x : Torus) : ℝ :=
  ∫ y, f y * regularizedGreen ε hε (x - y) ∂torusMeasure

def regularizedGradientConstant : ℝ :=
  Classical.choose exists_regularizedGreenGradient_bound

theorem regularizedGradientConstant_pos : 0 < regularizedGradientConstant :=
  (Classical.choose_spec exists_regularizedGreenGradient_bound).1

theorem regularizedGradientConstant_bound (ε : ℝ) (hε : 0 < ε)
    (hs : ε ≤ 1 / 16) {z : Torus} (hz : z ≠ 0) :
    ‖regularizedGreenGradient ε hε z‖ ≤
      regularizedGradientConstant / torusEuclideanNorm z :=
  (Classical.choose_spec exists_regularizedGreenGradient_bound).2 ε hε hs z hz

def inverseRadiusMoment : ℝ :=
  lpNorm (fun z : Torus ↦ (torusEuclideanNorm z)⁻¹) conjugateExponent torusMeasure

def convolutionLipschitzConstant : ℝ :=
  1 + regularizedGradientConstant * inverseRadiusMoment

theorem convolutionLipschitzConstant_pos : 0 < convolutionLipschitzConstant := by
  have h := regularizedGradientConstant_pos
  have hm : 0 ≤ inverseRadiusMoment := lpNorm_nonneg
  unfold convolutionLipschitzConstant
  positivity

theorem inverseRadius_memLp : MemLp (fun z : Torus ↦ (torusEuclideanNorm z)⁻¹)
    conjugateExponent torusMeasure :=
  memLp_torusEuclideanNorm_inv (4 / 3) (by norm_num) (by norm_num)

theorem green_memLp : MemLp regularGreenRepresentative conjugateExponent torusMeasure :=
  memLp_regularGreenRepresentative (4 / 3) (by norm_num)

theorem translated_memLp {p : ℝ≥0∞} {g : Torus → ℝ}
    (hg : MemLp g p torusMeasure) (x : Torus) :
    MemLp (fun y ↦ g (x - y)) p torusMeasure :=
  (TorusPatchDensity.memLp_comp_iff (torusMeasure.measurePreserving_sub_left x)
    hg.aestronglyMeasurable p).mpr hg

theorem densityPotential_integrable {f : Torus → ℝ}
    (hf : MemLp f 4 torusMeasure) (x : Torus) :
    Integrable (fun y ↦ f y * regularGreenRepresentative (x - y)) torusMeasure :=
  integrable_four_mul_conjugate hf (translated_memLp green_memLp x)

theorem densityPotential_eq_original {f : Torus → ℝ}
    (_hf : MemLp f 4 torusMeasure) (x : Torus) :
    densityPotential f x = ∫ y, greenRealRepresentative (x - y) * f y ∂torusMeasure := by
  apply integral_congr_ae
  filter_upwards [(torusMeasure.measurePreserving_sub_left x).quasiMeasurePreserving.ae
    regularGreenRepresentative_ae] with y hy
  simp only [hy, mul_comm]

theorem densityPotential_sub {f g : Torus → ℝ}
    (hf : MemLp f 4 torusMeasure) (hg : MemLp g 4 torusMeasure) (x : Torus) :
    densityPotential (f - g) x = densityPotential f x - densityPotential g x := by
  simp only [densityPotential, Pi.sub_apply, sub_mul]
  exact integral_sub (densityPotential_integrable hf x) (densityPotential_integrable hg x)

theorem densityPotential_one (x : Torus) : densityPotential (fun _ ↦ 1) x = 0 := by
  simp only [densityPotential, one_mul]
  rw [TorusPatchDensity.integral_comp_ae (torusMeasure.measurePreserving_sub_left x)
    regularGreenRepresentative_integrable.aestronglyMeasurable]
  exact regularGreenRepresentative_integral_zero

theorem densityPotential_bound {f : Torus → ℝ}
    (hf : MemLp f 4 torusMeasure) (x : Torus) :
    |densityPotential f x| ≤ lpNorm f 4 torusMeasure *
      lpNorm regularGreenRepresentative conjugateExponent torusMeasure := by
  have hh := integral_norm_mul_le hf (translated_memLp green_memLp x)
  rw [TorusPatchDensity.lpNorm_comp_ae (torusMeasure.measurePreserving_sub_left x)
    green_memLp.aestronglyMeasurable] at hh
  have h := norm_integral_le_integral_norm (μ := torusMeasure)
    (fun y ↦ f y * regularGreenRepresentative (x - y))
  have h' : |densityPotential f x| ≤
      ∫ y, |f y| * |regularGreenRepresentative (x - y)| ∂torusMeasure := by
    simpa only [densityPotential, norm_mul, Real.norm_eq_abs] using h
  exact h'.trans hh

theorem regularizedDifferential_integrable {f : Torus → ℝ}
    (hf : MemLp f 4 torusMeasure) (ε : ℝ) (hε : 0 < ε)
    (hs : ε ≤ 1 / 16) (x : Torus) :
    Integrable (fun y ↦ f y • regularizedGreenDifferential ε hε (x - y)) torusMeasure := by
  let A : C(Torus, PlanarSpace →L[ℝ] ℝ) :=
    ⟨regularizedGreenDifferential ε hε, continuous_regularizedGreenDifferential ε hε hs⟩
  have hc : Continuous (fun y : Torus ↦ regularizedGreenDifferential ε hε (x - y)) := by
    apply (continuous_regularizedGreenDifferential ε hε hs).comp
    fun_prop
  apply ((hf.integrable (by norm_num)).norm.mul_const ‖A‖).mono'
    (hf.aestronglyMeasurable.smul hc.aestronglyMeasurable)
  exact Eventually.of_forall fun y ↦ by
    change ‖f y • regularizedGreenDifferential ε hε (x - y)‖ ≤ ‖f y‖ * ‖A‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (A.norm_coe_le_norm (x - y)) (norm_nonneg _)

theorem hasFDerivAt_regularizedPotential {f : Torus → ℝ}
    (hf : MemLp f 4 torusMeasure) (ε : ℝ) (hε : 0 < ε)
    (hs : ε ≤ 1 / 16) (x : PlanarSpace) :
    HasFDerivAt (fun w : PlanarSpace ↦ regularizedPotential f ε hε (torusQuotient w))
      (∫ y, f y • regularizedGreenDifferential ε hε (torusQuotient x - y) ∂torusMeasure) x := by
  let F : PlanarSpace → Torus → ℝ :=
    fun w y ↦ f y * regularizedGreen ε hε (torusQuotient w - y)
  let D : PlanarSpace → Torus → PlanarSpace →L[ℝ] ℝ :=
    fun w y ↦ f y • regularizedGreenDifferential ε hε (torusQuotient w - y)
  let A : C(Torus, PlanarSpace →L[ℝ] ℝ) :=
    ⟨regularizedGreenDifferential ε hε, continuous_regularizedGreenDifferential ε hε hs⟩
  let B : C(Torus, ℝ) := ⟨regularizedGreen ε hε, continuous_regularizedGreen ε hε⟩
  have hFc (w : PlanarSpace) : Continuous
      (fun y : Torus ↦ regularizedGreen ε hε (torusQuotient w - y)) := by
    apply (continuous_regularizedGreen ε hε).comp
    fun_prop
  have hDc (w : PlanarSpace) : Continuous
      (fun y : Torus ↦ regularizedGreenDifferential ε hε (torusQuotient w - y)) := by
    apply (continuous_regularizedGreenDifferential ε hε hs).comp
    fun_prop
  have hFi : Integrable (F x) torusMeasure := by
    apply ((hf.integrable (by norm_num)).norm.mul_const ‖B‖).mono'
      (hf.aestronglyMeasurable.mul (hFc x).aestronglyMeasurable)
    exact Eventually.of_forall fun y ↦ by
      change ‖f y * regularizedGreen ε hε (torusQuotient x - y)‖ ≤ ‖f y‖ * ‖B‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (B.norm_coe_le_norm _) (norm_nonneg _)
  have hb : ∀ᵐ y ∂torusMeasure, ∀ w ∈ (Set.univ : Set PlanarSpace),
      ‖D w y‖ ≤ ‖f y‖ * ‖A‖ := Eventually.of_forall fun y w _ ↦ by
    dsimp only [D]
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (A.norm_coe_le_norm _) (norm_nonneg _)
  have hd : ∀ᵐ y ∂torusMeasure, ∀ w ∈ (Set.univ : Set PlanarSpace),
      HasFDerivAt (fun v ↦ F v y) (D w y) w := by
    exact Eventually.of_forall fun y w _ ↦ by
      simpa only [F, D] using!
        (ReferenceConvolutionGradient.hasFDerivAt_regularizedGreen_sub ε hε hs w y).const_mul (f y)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Set.univ) (Filter.univ_mem : Set.univ ∈ 𝓝 x)
    (Eventually.of_forall fun w ↦ hf.aestronglyMeasurable.mul (hFc w).aestronglyMeasurable)
    hFi (hf.aestronglyMeasurable.smul (hDc x).aestronglyMeasurable) hb
    ((hf.integrable (by norm_num)).norm.mul_const ‖A‖) hd

theorem norm_regularizedDifferential_integral_le {f : Torus → ℝ}
    (hf : MemLp f 4 torusMeasure) (ε : ℝ) (hε : 0 < ε)
    (hs : ε ≤ 1 / 16) (x : Torus) :
    ‖∫ y, f y • regularizedGreenDifferential ε hε (x - y) ∂torusMeasure‖ ≤
      convolutionLipschitzConstant * lpNorm f 4 torusMeasure := by
  let r : Torus → ℝ := fun y ↦ (torusEuclideanNorm (x - y))⁻¹
  have hr : MemLp r conjugateExponent torusMeasure := translated_memLp inverseRadius_memLp x
  have hi : Integrable (fun y ↦ |f y| * r y) torusMeasure := by
    simpa only [Real.norm_eq_abs] using integrable_four_mul_conjugate hf.norm hr
  have hb : ∀ᵐ y ∂torusMeasure,
      ‖f y • regularizedGreenDifferential ε hε (x - y)‖ ≤
        regularizedGradientConstant * (|f y| * r y) := by
    filter_upwards [(torusMeasure.measurePreserving_sub_left x).quasiMeasurePreserving.ae
      (torusMeasure.ae_ne (0 : Torus))] with y hy
    rw [norm_smul, ← norm_regularizedGreenGradient, Real.norm_eq_abs]
    have h := mul_le_mul_of_nonneg_left
      (regularizedGradientConstant_bound ε hε hs hy) (abs_nonneg (f y))
    simpa only [r, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have hh := integral_norm_mul_le hf hr
  simp only [r, abs_of_nonneg (inv_nonneg.mpr (torusEuclideanNorm_nonneg _)),
    TorusPatchDensity.lpNorm_comp_ae (torusMeasure.measurePreserving_sub_left x)
      inverseRadius_memLp.aestronglyMeasurable] at hh
  have hi' := integral_mono_ae (regularizedDifferential_integrable hf ε hε hs x).norm
    (hi.const_mul regularizedGradientConstant) hb
  rw [integral_const_mul] at hi'
  have hC := regularizedGradientConstant_pos.le
  have hL : 0 ≤ lpNorm f 4 torusMeasure := lpNorm_nonneg
  have hI := mul_le_mul_of_nonneg_left hh hC
  apply (norm_integral_le_integral_norm _).trans
  apply hi'.trans
  dsimp only [convolutionLipschitzConstant, inverseRadiusMoment]
  nlinarith only [hI, hL]

theorem lipschitzWith_regularizedPotential {f : Torus → ℝ}
    (hf : MemLp f 4 torusMeasure) (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ 1 / 16) :
    LipschitzWith ⟨convolutionLipschitzConstant * lpNorm f 4 torusMeasure,
      mul_nonneg convolutionLipschitzConstant_pos.le lpNorm_nonneg⟩
      (fun w : PlanarSpace ↦ regularizedPotential f ε hε (torusQuotient w)) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    (fun w ↦ (hasFDerivAt_regularizedPotential hf ε hε hs w).differentiableAt)
  intro w
  change ‖fderiv ℝ _ w‖ ≤ _
  rw [(hasFDerivAt_regularizedPotential hf ε hε hs w).fderiv]
  exact norm_regularizedDifferential_integral_le hf ε hε hs _

theorem exists_regularizedGreen_conjugate_majorant :
    ∃ M : Torus → ℝ, MemLp M conjugateExponent torusMeasure ∧
      ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ (1 / 16 : ℝ) →
        ∀ᵐ z ∂torusMeasure, ‖regularizedGreen ε hε z‖ ≤ M z := by
  obtain ⟨Cg, hCg, hlower⟩ := exists_regularGreenRepresentative_lower_bound
  obtain ⟨C, hC, hupper⟩ := exists_regularizedGreen_upper_bound
  refine ⟨fun z ↦ ‖regularGreenRepresentative z‖ + Cg + C,
    (green_memLp.norm.add (memLp_const Cg)).add (memLp_const C), ?_⟩
  intro ε hε hs
  filter_upwards [torusMeasure.ae_ne (0 : Torus)] with z hz
  have hlo := regularizedGreen_lower_bound hlower ε hε hs z
  have hup := hupper ε hε hs z hz
  have hscale : ε ^ 2 ≤ 1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hscale hC.le
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hg := norm_nonneg (regularGreenRepresentative z)
    linarith
  · have hg := le_abs_self (regularGreenRepresentative z)
    rw [← Real.norm_eq_abs] at hg
    linarith

theorem tendsto_regularizedPotential {f : Torus → ℝ}
    (hf : MemLp f 4 torusMeasure)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hs : ∀ n, ε n ≤ 1 / 16)
    (ht : Tendsto ε atTop (𝓝 0)) (x : Torus) :
    Tendsto (fun n ↦ regularizedPotential f (ε n) (hε n) x)
      atTop (𝓝 (densityPotential f x)) := by
  obtain ⟨M, hM, hb⟩ := exists_regularizedGreen_conjugate_majorant
  have hMI : Integrable (fun y ↦ ‖f y‖ * M (x - y)) torusMeasure :=
    integrable_four_mul_conjugate hf.norm (translated_memLp hM x)
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun y ↦ f y * regularizedGreen (ε n) (hε n) (x - y)) torusMeasure := by
    have hc : Continuous (fun y : Torus ↦ regularizedGreen (ε n) (hε n) (x - y)) := by
      apply (continuous_regularizedGreen (ε n) (hε n)).comp
      fun_prop
    exact hf.aestronglyMeasurable.mul hc.aestronglyMeasurable
  apply tendsto_integral_of_dominated_convergence (fun y ↦ ‖f y‖ * M (x - y)) hmeas hMI
  · intro n
    filter_upwards [(torusMeasure.measurePreserving_sub_left x).quasiMeasurePreserving.ae
      (hb (ε n) (hε n) (hs n))] with y hy
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)
  · filter_upwards [(torusMeasure.measurePreserving_sub_left x).quasiMeasurePreserving.ae
      (torusMeasure.ae_ne (0 : Torus))] with y hy
    exact tendsto_const_nhds.mul (tendsto_regularizedGreen hε hs ht hy)

/-- A genuine signed-L4 convolution estimate, obtained by smooth
differentiation and a common conjugate-exponent majorant. -/
theorem lipschitzWith_densityPotential {f : Torus → ℝ}
    (hf : MemLp f 4 torusMeasure) :
    LipschitzWith ⟨convolutionLipschitzConstant * lpNorm f 4 torusMeasure,
      mul_nonneg convolutionLipschitzConstant_pos.le lpNorm_nonneg⟩
      (fun w : PlanarSpace ↦ densityPotential f (torusQuotient w)) := by
  let ε : ℕ → ℝ := fun n ↦ (1 / 16 : ℝ) * (1 / ((n : ℝ) + 1))
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hs (n : ℕ) : ε n ≤ (1 / 16 : ℝ) := by
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (le_add_of_nonneg_left (Nat.cast_nonneg n))
    dsimp [ε]
    nlinarith
  have ht : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 16 : ℝ)
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  apply le_of_tendsto ((tendsto_regularizedPotential hf ε hε hs ht (torusQuotient x)).sub
    (tendsto_regularizedPotential hf ε hε hs ht (torusQuotient y))).norm
  exact Eventually.of_forall fun n ↦ lipschitzWith_iff_norm_sub_le.mp
    (lipschitzWith_regularizedPotential hf (ε n) (hε n) (hs n)) x y

theorem continuous_densityPotential {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure) :
    Continuous (densityPotential f) := by
  apply isOpenQuotientMap_torusQuotient.isQuotientMap.continuous_iff.mpr
  exact (lipschitzWith_densityPotential hf).continuous

theorem densityPotential_congr_ae {f g : Torus → ℝ} (h : f =ᵐ[torusMeasure] g) :
    densityPotential f = densityPotential g := by
  funext x
  exact integral_congr_ae (h.mono fun y hy ↦ by simp only [hy])

theorem densityPotential_cell_oscillation {f : Torus → ℝ}
    (hf : MemLp f 4 torusMeasure) {J : ℕ} (hJ : 0 < J)
    (a : MeshIndex J) {x y : Torus}
    (hx : x ∈ closure (meshCell J hJ a)) (hy : y ∈ closure (meshCell J hJ a)) :
    |densityPotential f x - densityPotential f y| ≤
      convolutionLipschitzConstant * lpNorm f 4 torusMeasure * (Real.sqrt 2 / (J : ℝ)) :=
  ReferenceConvolutionGradient.cell_oscillation_le_of_lipschitz
    (lipschitzWith_densityPotential hf) hJ a hx hy

abbrev L4 : Type := Lp ℝ 4 torusMeasure

instance four_ge_one : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

def oneL4 : L4 := Lp.const 4 torusMeasure 1

theorem lpNorm_coe (f : L4) : lpNorm f 4 torusMeasure = ‖f‖ := by
  rw [Lp.norm_def, toReal_eLpNorm]

theorem oneL4_ae : oneL4 =ᵐ[torusMeasure] fun _ ↦ (1 : ℝ) :=
  Lp.coeFn_const 4 torusMeasure 1

theorem norm_oneL4 : ‖oneL4‖ = 1 := by
  have hm0 : torusMeasure ≠ 0 := by
    intro hz
    have hp : torusMeasure Set.univ = 1 := measure_univ
    simp [hz] at hp
  rw [← lpNorm_coe]
  have h := congrArg ENNReal.toReal (eLpNorm_congr_ae (p := 4) oneL4_ae)
  change lpNorm oneL4 4 torusMeasure = lpNorm (fun _ : Torus ↦ (1 : ℝ)) 4 torusMeasure at h
  rw [h, lpNorm_const (by norm_num : (4 : ℝ≥0∞) ≠ 0) hm0]
  simp only [norm_one, probReal_univ, Real.one_rpow, mul_one]

theorem integral_lipschitz : LipschitzWith 1 (fun f : L4 ↦ ∫ x, f x ∂torusMeasure) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro f g
  have he : (∫ x, (f - g) x ∂torusMeasure) =
      (∫ x, f x ∂torusMeasure) - ∫ x, g x ∂torusMeasure := by
    rw [integral_congr_ae (Lp.coeFn_sub f g)]
    exact integral_sub ((Lp.memLp f).integrable (by norm_num))
      ((Lp.memLp g).integrable (by norm_num))
  have hh := DensityMoments.norm_integral_le_lpNorm (Lp.memLp (f - g)) (by norm_num)
  simpa only [he, lpNorm_coe, Real.norm_eq_abs, NNReal.coe_one, one_mul] using hh

/-- The literal closed probability ball from the manuscript. -/
def probabilityBall : Set L4 :=
  {f | 0 ≤ f ∧ (∫ x, f x ∂torusMeasure) = 1 ∧ ‖f - oneL4‖ ≤ 1 / 2}

theorem probabilityBall_isClosed : IsClosed probabilityBall := by
  have h₁ : IsClosed {f : L4 | 0 ≤ f} := isClosed_Ici
  have h₂ : IsClosed {f : L4 | (∫ x, f x ∂torusMeasure) = 1} :=
    isClosed_eq integral_lipschitz.continuous continuous_const
  have h₃ : IsClosed {f : L4 | ‖f - oneL4‖ ≤ 1 / 2} :=
    isClosed_le (continuous_id.sub continuous_const).norm continuous_const
  exact h₁.inter (h₂.inter h₃)

theorem oneL4_mem_probabilityBall : oneL4 ∈ probabilityBall := by
  refine ⟨(Lp.coeFn_nonneg oneL4).mp (oneL4_ae.mono fun _ hx ↦ by simp only [hx]; norm_num), ?_, ?_⟩
  · rw [integral_congr_ae oneL4_ae, integral_const, probReal_univ, one_smul]
  · simp only [sub_self, norm_zero]
    norm_num

instance probabilityBall_complete : CompleteSpace ↥probabilityBall :=
  probabilityBall_isClosed.completeSpace_coe

instance probabilityBall_nonempty : Nonempty ↥probabilityBall :=
  ⟨⟨oneL4, oneL4_mem_probabilityBall⟩⟩

theorem probabilityBall_norm_le {f : L4} (hf : f ∈ probabilityBall) : ‖f‖ ≤ 3 / 2 := by
  have hh : ‖f‖ ≤ ‖f - oneL4‖ + ‖oneL4‖ := by
    simpa only [sub_add_cancel] using norm_add_le (f - oneL4) oneL4
  rw [norm_oneL4] at hh
  linarith [hf.2.2]

theorem integrable_continuous_torus (ν : Measure Torus) [IsFiniteMeasure ν]
    {f : Torus → ℝ} (hf : Continuous f) : Integrable f ν := by
  let F : C(Torus, ℝ) := ⟨f, hf⟩
  exact (integrable_const ‖F‖).mono' hf.aestronglyMeasurable
    (Eventually.of_forall F.norm_coe_le_norm)

def cellNormalizer {J : ℕ} (hJ : 0 < J) (u : Torus → ℝ) (a : MeshIndex J) : ℝ :=
  ∫ x, Real.exp (u x) ∂meshCellMeasure J hJ a

def cellDensity {J : ℕ} (hJ : 0 < J) (u : Torus → ℝ) (a : MeshIndex J) (x : Torus) : ℝ :=
  Real.exp (u x) / cellNormalizer hJ u a

theorem cellNormalizer_pos {J : ℕ} (hJ : 0 < J) {u : Torus → ℝ}
    (hu : Continuous u) (a : MeshIndex J) : 0 < cellNormalizer hJ u a :=
  integral_exp_pos (integrable_continuous_torus _ (Real.continuous_exp.comp hu))

theorem continuous_cellDensity {J : ℕ} (hJ : 0 < J) {u : Torus → ℝ}
    (hu : Continuous u) (a : MeshIndex J) : Continuous (cellDensity hJ u a) :=
  (Real.continuous_exp.comp hu).div_const _

theorem cellDensity_pos {J : ℕ} (hJ : 0 < J) {u : Torus → ℝ}
    (hu : Continuous u) (a : MeshIndex J) (x : Torus) : 0 < cellDensity hJ u a x :=
  div_pos (Real.exp_pos _) (cellNormalizer_pos hJ hu a)

theorem cellDensity_integral {J : ℕ} (hJ : 0 < J) {u : Torus → ℝ}
    (hu : Continuous u) (a : MeshIndex J) :
    (∫ x, cellDensity hJ u a x ∂meshCellMeasure J hJ a) = 1 := by
  simp only [cellDensity, integral_div]
  exact div_self (cellNormalizer_pos hJ hu a).ne'

/-- Pointwise normalization bounds use the actual cell probability law.
They apply to every cell, without a positive occupation requirement. -/
theorem cellDensity_bounds {J : ℕ} (hJ : 0 < J) {u : Torus → ℝ}
    (hu : Continuous u) (a : MeshIndex J) {M : ℝ}
    (hosc : ∀ x ∈ meshCell J hJ a, ∀ y ∈ meshCell J hJ a, |u x - u y| ≤ M)
    {x : Torus} (hx : x ∈ meshCell J hJ a) :
    Real.exp (-M) ≤ cellDensity hJ u a x ∧ cellDensity hJ u a x ≤ Real.exp M := by
  let ν := meshCellMeasure J hJ a
  have hi : Integrable (fun y ↦ Real.exp (u y)) ν :=
    integrable_continuous_torus _ (Real.continuous_exp.comp hu)
  have hlo : Real.exp (u x - M) ≤ cellNormalizer hJ u a := by
    have hh := integral_mono_ae (integrable_const (Real.exp (u x - M))) hi
      ((ae_mem_meshCell J hJ a).mono fun y hy ↦ Real.exp_le_exp.mpr (by
        have := (abs_le.mp (hosc x hx y hy)).2
        linarith))
    simpa only [integral_const, probReal_univ, one_smul, cellNormalizer, ν] using hh
  have hup : cellNormalizer hJ u a ≤ Real.exp (u x + M) := by
    have hh := integral_mono_ae hi (integrable_const (Real.exp (u x + M)))
      ((ae_mem_meshCell J hJ a).mono fun y hy ↦ Real.exp_le_exp.mpr (by
        have := (abs_le.mp (hosc x hx y hy)).1
        linarith))
    simpa only [integral_const, probReal_univ, one_smul, cellNormalizer, ν] using hh
  constructor
  · apply (le_div_iff₀ (cellNormalizer_pos hJ hu a)).mpr
    calc
      _ ≤ Real.exp (-M) * Real.exp (u x + M) :=
        mul_le_mul_of_nonneg_left hup (Real.exp_pos _).le
      _ = Real.exp (u x) := by rw [← Real.exp_add]; congr 1; ring
  · apply (div_le_iff₀ (cellNormalizer_pos hJ hu a)).mpr
    calc
      Real.exp (u x) = Real.exp M * Real.exp (u x - M) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (Real.exp_pos _).le

theorem cellDensity_sub_one_le {J : ℕ} (hJ : 0 < J) {u : Torus → ℝ}
    (hu : Continuous u) (a : MeshIndex J) {M : ℝ} (hM : 0 ≤ M)
    (hsmall : M ≤ 1)
    (hosc : ∀ x ∈ meshCell J hJ a, ∀ y ∈ meshCell J hJ a, |u x - u y| ≤ M)
    {x : Torus} (hx : x ∈ meshCell J hJ a) : |cellDensity hJ u a x - 1| ≤ 2 * M := by
  have hb := cellDensity_bounds hJ hu a hosc hx
  have hh := Real.abs_exp_sub_one_le (x := M) (by simpa only [abs_of_nonneg hM] using hsmall)
  have hl := Real.abs_exp_sub_one_le (x := -M) (by simpa only [abs_neg, abs_of_nonneg hM] using hsmall)
  rw [abs_of_nonneg hM] at hh
  rw [abs_neg, abs_of_nonneg hM] at hl
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hh).2, (abs_le.mp hl).1]

section ScalarInterpolation

open NormalizedExponentialInterpolation

theorem continuous_admissible (ν : Measure Torus) [IsFiniteMeasure ν]
    {u w : Torus → ℝ} (hu : Continuous u) (hw : Continuous w) : Admissible ν u w := by
  refine ⟨hu.measurable.aemeasurable, hw.measurable.aemeasurable, ?_⟩
  apply integrable_continuous_torus ν
  unfold majorant endpointBound
  fun_prop

theorem hasDerivWithinAt_cellDensity (ν : Measure Torus) [IsFiniteMeasure ν] [NeZero ν]
    {u w : Torus → ℝ} (h : Admissible ν u w) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (x : Torus) : HasDerivWithinAt (fun s ↦ density ν u w s x)
      (densitySlope ν u w t x) (Icc (0 : ℝ) 1) t := by
  have hz := (h.hasDerivWithinAt_normalizer ht).inv (h.normalizer_pos ht).ne'
  have hd := hz.mul (hasDerivAt_weight u w t x).hasDerivWithinAt
  apply hd.congr_deriv
  simp only [Pi.inv_apply]
  rw [densitySlope, density, h.meanW_eq ht, weightSlope]
  field_simp [(h.normalizer_pos ht).ne']
  ring

theorem abs_sub_meanW_le {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    {u w : Torus → ℝ} (h : Admissible (meshCellMeasure J hJ a) u w)
    {t D : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hw : ∀ x ∈ meshCell J hJ a, ∀ y ∈ meshCell J hJ a, |w x - w y| ≤ D)
    {x : Torus} (hx : x ∈ meshCell J hJ a) :
    |w x - meanW (meshCellMeasure J hJ a) u w t| ≤ D := by
  let ρ := law (meshCellMeasure J hJ a) u w t
  let : IsProbabilityMeasure ρ := h.law_probability ht
  have hi : Integrable (fun y ↦ w x - w y) ρ :=
    (integrable_const (w x)).sub (h.integrable_w_law ht)
  have hp : ∀ᵐ y ∂ρ, y ∈ meshCell J hJ a :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_mem_meshCell J hJ a)
  have hb := integral_mono_ae hi.abs (integrable_const D)
    (hp.mono fun y hy ↦ hw x hx y hy)
  have hn := norm_integral_le_integral_norm (μ := ρ) (fun y ↦ w x - w y)
  rw [integral_sub (integrable_const (w x)) (h.integrable_w_law ht),
    integral_const, probReal_univ, one_smul] at hn
  simp only [integral_const, probReal_univ, one_smul] at hb
  simpa only [Real.norm_eq_abs, meanW, ρ] using hn.trans hb

/-- The pointwise normalized-exponential interpolation is genuinely
differentiated. Its derivative is bounded by the cell oscillation of the
increment, not by the absolute size of its arbitrary additive constant. -/
theorem cellDensity_interpolation_bound {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    {u w : Torus → ℝ} (hu : Continuous u) (hw : Continuous w) {M D : ℝ}
    (hD : 0 ≤ D)
    (hosc : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ meshCell J hJ a,
      ∀ y ∈ meshCell J hJ a, |(u x + t * w x) - (u y + t * w y)| ≤ M)
    (hwosc : ∀ x ∈ meshCell J hJ a, ∀ y ∈ meshCell J hJ a, |w x - w y| ≤ D)
    {x : Torus} (hx : x ∈ meshCell J hJ a) :
    |cellDensity hJ (fun y ↦ u y + w y) a x - cellDensity hJ u a x| ≤ Real.exp M * D := by
  let ν := meshCellMeasure J hJ a
  have h := continuous_admissible ν hu hw
  have hl : LipschitzOnWith ⟨Real.exp M * D, mul_nonneg (Real.exp_pos _).le hD⟩
      (fun t ↦ density ν u w t x) (Icc (0 : ℝ) 1) := by
    apply (convex_Icc (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht ↦ hasDerivWithinAt_cellDensity ν h ht x)
    intro t ht
    apply NNReal.coe_le_coe.mp
    change |densitySlope ν u w t x| ≤ Real.exp M * D
    rw [densitySlope, abs_mul, abs_of_pos (h.density_pos ht x)]
    have hc : Continuous (fun y ↦ u y + t * w y) := by fun_prop
    have hd : density ν u w t x ≤ Real.exp M := by
      simpa only [density, normalizer, weight, cellDensity, cellNormalizer,
        div_eq_mul_inv, mul_comm, ν] using (cellDensity_bounds hJ hc a (hosc t ht) hx).2
    exact mul_le_mul hd (abs_sub_meanW_le hJ a h ht hwosc hx)
      (abs_nonneg _) (Real.exp_pos _).le
  have he := hl.dist_le_mul 1 (by norm_num) 0 (by norm_num)
  change |density ν u w 1 x - density ν u w 0 x| ≤ (Real.exp M * D) * |(1 : ℝ) - 0| at he
  simpa only [density, normalizer, weight, cellDensity, cellNormalizer,
    Real.dist_eq, one_mul, zero_mul, mul_zero, add_zero, sub_zero, abs_one, mul_one,
    div_eq_mul_inv, mul_comm, ν] using he

end ScalarInterpolation

theorem memLp_continuous_torus (ν : Measure Torus) [IsFiniteMeasure ν]
    {f : Torus → ℝ} (hf : Continuous f) (p : ℝ≥0∞) : MemLp f p ν := by
  let F : C(Torus, ℝ) := ⟨f, hf⟩
  exact MemLp.of_bound hf.aestronglyMeasurable ‖F‖
    (Eventually.of_forall F.norm_coe_le_norm)

def scaledPotential (β : ℝ) (f : L4) (x : Torus) : ℝ := β * densityPotential f x

theorem continuous_scaledPotential (β : ℝ) (f : L4) : Continuous (scaledPotential β f) :=
  (continuous_densityPotential (Lp.memLp f)).const_mul β

def occupationMapValue {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (β : ℝ) (f : L4) (x : Torus) : ℝ :=
  ∑ a, (J : ℝ) ^ 2 * θ a *
    (meshCell J hJ a).indicator (cellDensity hJ (scaledPotential β f) a) x

theorem occupationMapValue_memLp {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (β : ℝ) (f : L4) (p : ℝ≥0∞) : MemLp (occupationMapValue hJ θ β f) p torusMeasure := by
  apply memLp_finsetSum
  intro a _
  exact ((memLp_continuous_torus torusMeasure
    (continuous_cellDensity hJ (continuous_scaledPotential β f) a) p).indicator
      (measurableSet_meshCell J hJ a)).const_mul _

theorem occupationMapValue_measurable {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (β : ℝ) (f : L4) : Measurable (occupationMapValue hJ θ β f) := by
  apply Finset.measurable_sum
  intro a _
  exact (((continuous_cellDensity hJ (continuous_scaledPotential β f) a).measurable).indicator
    (measurableSet_meshCell J hJ a)).const_mul _

theorem occupationMapValue_apply {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (β : ℝ) (f : L4) (x : Torus) :
    occupationMapValue hJ θ β f x = (J : ℝ) ^ 2 * θ (meshLabel J hJ x) *
      cellDensity hJ (scaledPotential β f) (meshLabel J hJ x) x := by
  classical
  rw [occupationMapValue, Finset.sum_eq_single (meshLabel J hJ x)]
  · rw [indicator_of_mem (show x ∈ meshCell J hJ (meshLabel J hJ x) from rfl)]
  · intro a _ ha
    rw [indicator_of_notMem (show x ∉ meshCell J hJ a from fun hx ↦ ha hx.symm), mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem occupationMapValue_nonneg {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ}
    (hθ : ∀ a, 0 ≤ θ a) (β : ℝ) (f : L4) (x : Torus) :
    0 ≤ occupationMapValue hJ θ β f x := by
  rw [occupationMapValue_apply]
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (hθ _))
    (cellDensity_pos hJ (continuous_scaledPotential β f) _ _).le

theorem cellDensity_haar_mass {J : ℕ} (hJ : 0 < J) {u : Torus → ℝ}
    (hu : Continuous u) (a : MeshIndex J) :
    (J : ℝ) ^ 2 * (∫ x, (meshCell J hJ a).indicator (cellDensity hJ u a) x ∂torusMeasure) = 1 := by
  have hh := cellDensity_integral hJ hu a
  rw [integral_indicator (measurableSet_meshCell J hJ a)]
  simpa only [meshCellMeasure, integral_smul_measure, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, smul_eq_mul] using hh

theorem occupationMapValue_integral {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ}
    (hθ : ∑ a, θ a = 1) (β : ℝ) (f : L4) :
    (∫ x, occupationMapValue hJ θ β f x ∂torusMeasure) = 1 := by
  have hi (a : MeshIndex J) : Integrable
      (fun x ↦ (J : ℝ) ^ 2 * θ a *
        (meshCell J hJ a).indicator (cellDensity hJ (scaledPotential β f) a) x) torusMeasure :=
    ((integrable_continuous_torus torusMeasure
      (continuous_cellDensity hJ (continuous_scaledPotential β f) a)).indicator
        (measurableSet_meshCell J hJ a)).const_mul _
  change (∫ x, ∑ a, (J : ℝ) ^ 2 * θ a *
    (meshCell J hJ a).indicator (cellDensity hJ (scaledPotential β f) a) x ∂torusMeasure) = 1
  rw [integral_finsetSum Finset.univ (fun a _ ↦ hi a)]
  convert hθ using 1
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_const_mul]
  have hm := cellDensity_haar_mass hJ (continuous_scaledPotential β f) a
  nlinarith only [congrArg (fun r : ℝ ↦ θ a * r) hm]

def occupationMap {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ) (β : ℝ) (f : L4) : L4 :=
  (occupationMapValue_memLp hJ θ β f 4).toLp (occupationMapValue hJ θ β f)

theorem occupationMap_ae {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ) (β : ℝ) (f : L4) :
    occupationMap hJ θ β f =ᵐ[torusMeasure] occupationMapValue hJ θ β f :=
  (occupationMapValue_memLp hJ θ β f 4).coeFn_toLp

theorem occupationMap_nonneg {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ}
    (hθ : ∀ a, 0 ≤ θ a) (β : ℝ) (f : L4) : 0 ≤ occupationMap hJ θ β f := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [occupationMap_ae hJ θ β f] with x hx
  rw [hx]
  exact occupationMapValue_nonneg hJ hθ β f x

theorem occupationMap_integral {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ}
    (hθ : ∑ a, θ a = 1) (β : ℝ) (f : L4) :
    (∫ x, occupationMap hJ θ β f x ∂torusMeasure) = 1 := by
  rw [integral_congr_ae (occupationMap_ae hJ θ β f)]
  exact occupationMapValue_integral hJ hθ β f

theorem scaledPotential_one (β : ℝ) : scaledPotential β oneL4 = fun _ ↦ 0 := by
  funext x
  rw [scaledPotential, densityPotential_congr_ae oneL4_ae, densityPotential_one, mul_zero]

theorem occupationMapValue_one {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (β : ℝ) (x : Torus) : occupationMapValue hJ θ β oneL4 x =
      (J : ℝ) ^ 2 * θ (meshLabel J hJ x) := by
  rw [occupationMapValue_apply, scaledPotential_one]
  simp only [cellDensity, cellNormalizer, Real.exp_zero, integral_const, probReal_univ,
    one_smul, div_self (by norm_num : (1 : ℝ) ≠ 0), mul_one]

theorem lpNorm_le_of_ae_bound {f : Torus → ℝ} (hf : AEStronglyMeasurable f torusMeasure)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ x ∂torusMeasure, |f x| ≤ C)
    {p : ℝ≥0∞} (hp : p ≠ 0) : MemLp f p torusMeasure ∧ lpNorm f p torusMeasure ≤ C := by
  have hc : MemLp (fun _ : Torus ↦ C) p torusMeasure := memLp_const C
  have hh := ENNReal.toReal_mono hc.eLpNorm_ne_top (eLpNorm_mono_ae (g := fun _ : Torus ↦ C) (p := p) hf
    (hb.mono fun x hx ↦ by simpa only [Real.norm_eq_abs, abs_of_nonneg hC] using hx))
  have hm0 : torusMeasure ≠ 0 := by
    intro hz
    have hh : torusMeasure univ = 1 := measure_univ
    simp [hz] at hh
  refine ⟨MemLp.of_bound hf C (hb.mono fun x hx ↦ by simpa only [Real.norm_eq_abs] using hx), ?_⟩
  change lpNorm f p torusMeasure ≤ lpNorm (fun _ : Torus ↦ C) p torusMeasure at hh
  rw [lpNorm_const hp hm0] at hh
  simpa only [probReal_univ, Real.one_rpow, mul_one, Real.norm_eq_abs, abs_of_nonneg hC] using hh

theorem L4_norm_le_of_ae_bound (f : L4) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂torusMeasure, |f x| ≤ C) : ‖f‖ ≤ C := by
  rw [← lpNorm_coe]
  exact (lpNorm_le_of_ae_bound (Lp.memLp f).aestronglyMeasurable hC hb (by norm_num)).2

def meshNumerator (β₀ : ℝ) : ℝ :=
  max β₀ 0 * convolutionLipschitzConstant * Real.sqrt 2

def meshRate (J : ℕ) (β₀ : ℝ) : ℝ := meshNumerator β₀ / (J : ℝ)

def contractionFactor (J : ℕ) (β₀ : ℝ) : ℝ := 4 * meshRate J β₀

theorem meshNumerator_nonneg (β₀ : ℝ) : 0 ≤ meshNumerator β₀ :=
  mul_nonneg (mul_nonneg (le_max_right _ _) convolutionLipschitzConstant_pos.le) (Real.sqrt_nonneg _)

theorem meshRate_nonneg (J : ℕ) (β₀ : ℝ) : 0 ≤ meshRate J β₀ :=
  div_nonneg (meshNumerator_nonneg _) (Nat.cast_nonneg _)

theorem contractionFactor_nonneg (J : ℕ) (β₀ : ℝ) : 0 ≤ contractionFactor J β₀ :=
  mul_nonneg (by norm_num) (meshRate_nonneg _ _)

theorem meshRate_le {J : ℕ} (hJ : 0 < J) {β₀ : ℝ}
    (hscale : 16 * meshNumerator β₀ ≤ (J : ℝ)) :
    meshRate J β₀ ≤ 1 / 16 ∧ contractionFactor J β₀ ≤ 1 / 4 := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hh : meshRate J β₀ ≤ 1 / 16 := (div_le_iff₀ hJr).mpr (by linarith)
  exact ⟨hh, by dsimp only [contractionFactor]; linarith⟩

theorem scaledPotential_sub (β : ℝ) (f g : L4) :
    scaledPotential β (f - g) = fun x ↦ scaledPotential β f x - scaledPotential β g x := by
  funext x
  rw [scaledPotential, densityPotential_congr_ae (Lp.coeFn_sub f g),
    densityPotential_sub (Lp.memLp f) (Lp.memLp g)]
  simp only [scaledPotential, mul_sub]

theorem scaledPotential_cell_oscillation {J : ℕ} (hJ : 0 < J) {β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (f : L4) (a : MeshIndex J)
    {x y : Torus} (hx : x ∈ meshCell J hJ a) (hy : y ∈ meshCell J hJ a) :
    |scaledPotential β f x - scaledPotential β f y| ≤ meshRate J β₀ * ‖f‖ := by
  have hh := densityPotential_cell_oscillation (Lp.memLp f) hJ a
    (subset_closure hx) (subset_closure hy)
  rw [lpNorm_coe] at hh
  change |β * densityPotential f x - β * densityPotential f y| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg hβ]
  calc
    _ ≤ β * (convolutionLipschitzConstant * ‖f‖ * (Real.sqrt 2 / (J : ℝ))) :=
      mul_le_mul_of_nonneg_left hh hβ
    _ ≤ max β₀ 0 * (convolutionLipschitzConstant * ‖f‖ * (Real.sqrt 2 / (J : ℝ))) :=
      mul_le_mul_of_nonneg_right (hβ₀.trans (le_max_left _ _))
        (mul_nonneg (mul_nonneg convolutionLipschitzConstant_pos.le (norm_nonneg _))
          (div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)))
    _ = _ := by unfold meshRate meshNumerator; ring

theorem affine_oscillation {u v : Torus → ℝ} {A : Set Torus} {M : ℝ}
    (hu : ∀ x ∈ A, ∀ y ∈ A, |u x - u y| ≤ M)
    (hv : ∀ x ∈ A, ∀ y ∈ A, |v x - v y| ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x y : Torus} (hx : x ∈ A) (hy : y ∈ A) :
    |(u x + t * (v x - u x)) - (u y + t * (v y - u y))| ≤ M := by
  have h₁ : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  calc
    _ = |(1 - t) * (u x - u y) + t * (v x - v y)| := by congr 1; ring
    _ ≤ |(1 - t) * (u x - u y)| + |t * (v x - v y)| := abs_add_le _ _
    _ = (1 - t) * |u x - u y| + t * |v x - v y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg h₁, abs_of_nonneg ht.1]
    _ ≤ (1 - t) * M + t * M :=
      add_le_add (mul_le_mul_of_nonneg_left (hu x hx y hy) h₁)
        (mul_le_mul_of_nonneg_left (hv x hx y hy) ht.1)
    _ = M := by ring

/-- The actual pointwise L-infinity contraction. The occupation prefactor
is retained; its upper bound is 5/4, and exp(1) is bounded by 3. -/
theorem occupationMapValue_contraction {J : ℕ} (hJ : 0 < J) {β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hscale : 16 * meshNumerator β₀ ≤ (J : ℝ))
    {θ : MeshIndex J → ℝ} (hθ : ∀ a, |(J : ℝ) ^ 2 * θ a - 1| ≤ 1 / 4)
    (f g : L4) (hf : ‖f‖ ≤ 3 / 2) (hg : ‖g‖ ≤ 3 / 2) (x : Torus) :
    |occupationMapValue hJ θ β f x - occupationMapValue hJ θ β g x| ≤
      contractionFactor J β₀ * ‖f - g‖ := by
  let a := meshLabel J hJ x
  have hx : x ∈ meshCell J hJ a := rfl
  have hr := (meshRate_le hJ hscale).1
  have hr0 := meshRate_nonneg J β₀
  have hosc (v : L4) (hv : ‖v‖ ≤ 3 / 2) :
      ∀ z ∈ meshCell J hJ a, ∀ y ∈ meshCell J hJ a,
        |scaledPotential β v z - scaledPotential β v y| ≤ 1 := by
    intro z hz y hy
    apply (scaledPotential_cell_oscillation hJ hβ hβ₀ v a hz hy).trans
    exact (mul_le_mul_of_nonneg_left hv hr0).trans (by linarith)
  have hwosc : ∀ z ∈ meshCell J hJ a, ∀ y ∈ meshCell J hJ a,
      |(scaledPotential β f z - scaledPotential β g z) -
        (scaledPotential β f y - scaledPotential β g y)| ≤ meshRate J β₀ * ‖f - g‖ := by
    intro z hz y hy
    simpa only [scaledPotential_sub] using
      scaledPotential_cell_oscillation hJ hβ hβ₀ (f - g) a hz hy
  have hh := cellDensity_interpolation_bound hJ a (continuous_scaledPotential β g)
    ((continuous_scaledPotential β f).sub (continuous_scaledPotential β g))
    (M := 1) (mul_nonneg hr0 (norm_nonneg _))
    (fun t ht z hz y hy ↦ affine_oscillation (hosc g hg) (hosc f hf) ht hz hy) hwosc hx
  have he : (fun y ↦ scaledPotential β g y +
      (scaledPotential β f y - scaledPotential β g y)) = scaledPotential β f := by
    funext y
    ring
  simp only [Pi.sub_apply] at hh
  rw [he] at hh
  have ha := abs_le.mp (hθ a)
  have ha0 : 0 ≤ (J : ℝ) ^ 2 * θ a := by linarith
  have ha1 : (J : ℝ) ^ 2 * θ a ≤ 5 / 4 := by linarith
  have he1 : Real.exp 1 ≤ 3 := by
    have h := Real.abs_exp_sub_one_le (x := 1) (by norm_num)
    norm_num only [abs_one] at h
    linarith [(abs_le.mp h).2]
  have hm : ((J : ℝ) ^ 2 * θ a) * Real.exp 1 ≤ 4 :=
    (mul_le_mul ha1 he1 (Real.exp_pos _).le (by norm_num)).trans (by norm_num)
  rw [occupationMapValue_apply, occupationMapValue_apply, ← mul_sub, abs_mul,
    abs_of_nonneg ha0]
  calc
    _ ≤ ((J : ℝ) ^ 2 * θ a) * (Real.exp 1 * (meshRate J β₀ * ‖f - g‖)) :=
      mul_le_mul_of_nonneg_left hh ha0
    _ = (((J : ℝ) ^ 2 * θ a) * Real.exp 1) * (meshRate J β₀ * ‖f - g‖) := by ring
    _ ≤ 4 * (meshRate J β₀ * ‖f - g‖) :=
      mul_le_mul_of_nonneg_right hm (mul_nonneg hr0 (norm_nonneg _))
    _ = _ := by unfold contractionFactor; ring

theorem occupationMap_contraction {J : ℕ} (hJ : 0 < J) {β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hscale : 16 * meshNumerator β₀ ≤ (J : ℝ))
    {θ : MeshIndex J → ℝ} (hθ : ∀ a, |(J : ℝ) ^ 2 * θ a - 1| ≤ 1 / 4)
    (f g : L4) (hf : f ∈ probabilityBall) (hg : g ∈ probabilityBall) :
    ‖occupationMap hJ θ β f - occupationMap hJ θ β g‖ ≤ contractionFactor J β₀ * ‖f - g‖ := by
  apply L4_norm_le_of_ae_bound _ (mul_nonneg (contractionFactor_nonneg _ _) (norm_nonneg _))
  filter_upwards [Lp.coeFn_sub (occupationMap hJ θ β f) (occupationMap hJ θ β g),
    occupationMap_ae hJ θ β f, occupationMap_ae hJ θ β g] with x hs hfx hgx
  simp only [hs, Pi.sub_apply, hfx, hgx]
  exact occupationMapValue_contraction hJ hβ hβ₀ hscale hθ f g
    (probabilityBall_norm_le hf) (probabilityBall_norm_le hg) x

def profileDeviation {J : ℕ} (θ : MeshIndex J → ℝ) : ℝ :=
  ‖fun a ↦ (J : ℝ) ^ 2 * θ a - 1‖

theorem profileDeviation_nonneg {J : ℕ} (θ : MeshIndex J → ℝ) : 0 ≤ profileDeviation θ :=
  norm_nonneg _

theorem profileDeviation_apply_le {J : ℕ} (θ : MeshIndex J → ℝ) (a : MeshIndex J) :
    |(J : ℝ) ^ 2 * θ a - 1| ≤ profileDeviation θ := by
  simpa only [profileDeviation, Real.norm_eq_abs] using!
    norm_le_pi_norm (fun a ↦ (J : ℝ) ^ 2 * θ a - 1) a

theorem occupationMap_one_displacement {J : ℕ} (hJ : 0 < J)
    (θ : MeshIndex J → ℝ) (β : ℝ) :
    ‖occupationMap hJ θ β oneL4 - oneL4‖ ≤ profileDeviation θ := by
  apply L4_norm_le_of_ae_bound _ (profileDeviation_nonneg θ)
  filter_upwards [Lp.coeFn_sub (occupationMap hJ θ β oneL4) oneL4,
    occupationMap_ae hJ θ β oneL4, oneL4_ae] with x hs ht h1
  simp only [hs, Pi.sub_apply, ht, h1, occupationMapValue_one]
  exact profileDeviation_apply_le θ _

/-- Only source parameter restrictions are packaged here. No analytic
contraction, invariance, fixed-point, or marginal estimate is a field. -/
structure NearParameters {J : ℕ} (θ : MeshIndex J → ℝ) (β β₀ : ℝ) : Prop where
  beta_nonneg : 0 ≤ β
  beta_le : β ≤ β₀
  scale : 16 * meshNumerator β₀ ≤ (J : ℝ)
  occupation_nonneg : ∀ a, 0 ≤ θ a
  occupation_mass : ∑ a, θ a = 1
  occupation_near : profileDeviation θ ≤ 1 / 4

theorem occupationMap_invariant {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ} {β β₀ : ℝ}
    (h : NearParameters θ β β₀) {f : L4} (hf : f ∈ probabilityBall) :
    occupationMap hJ θ β f ∈ probabilityBall := by
  refine ⟨occupationMap_nonneg hJ h.occupation_nonneg β f,
    occupationMap_integral hJ h.occupation_mass β f, ?_⟩
  have hc := occupationMap_contraction hJ h.beta_nonneg h.beta_le h.scale
    (fun a ↦ (profileDeviation_apply_le θ a).trans h.occupation_near)
    f oneL4 hf oneL4_mem_probabilityBall
  have hd := occupationMap_one_displacement hJ θ β
  have ht : ‖occupationMap hJ θ β f - oneL4‖ ≤
      ‖occupationMap hJ θ β f - occupationMap hJ θ β oneL4‖ +
        ‖occupationMap hJ θ β oneL4 - oneL4‖ := by
    calc
      _ = ‖(occupationMap hJ θ β f - occupationMap hJ θ β oneL4) +
          (occupationMap hJ θ β oneL4 - oneL4)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hq := (meshRate_le hJ h.scale).2
  have hp := mul_le_mul_of_nonneg_left hf.2.2 (contractionFactor_nonneg J β₀)
  have hq' := mul_le_mul_of_nonneg_right hq (by norm_num : (0 : ℝ) ≤ 1 / 2)
  linarith [h.occupation_near]

def ballMap {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ} {β β₀ : ℝ}
    (h : NearParameters θ β β₀) (f : ↥probabilityBall) : ↥probabilityBall :=
  ⟨occupationMap hJ θ β f.val, occupationMap_invariant hJ h f.property⟩

theorem ballMap_contracting {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ} {β β₀ : ℝ}
    (h : NearParameters θ β β₀) :
    ContractingWith ⟨contractionFactor J β₀, contractionFactor_nonneg J β₀⟩ (ballMap hJ h) := by
  constructor
  · change contractionFactor J β₀ < 1
    exact lt_of_le_of_lt (meshRate_le hJ h.scale).2 (by norm_num)
  · apply LipschitzWith.of_dist_le_mul
    intro f g
    change dist (occupationMap hJ θ β f.val) (occupationMap hJ θ β g.val) ≤
      contractionFactor J β₀ * dist f.val g.val
    rw [dist_eq_norm, dist_eq_norm]
    exact occupationMap_contraction hJ h.beta_nonneg h.beta_le h.scale
      (fun a ↦ (profileDeviation_apply_le θ a).trans h.occupation_near)
      f.val g.val f.property g.property

def nearFixedPoint {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ} {β β₀ : ℝ}
    (h : NearParameters θ β β₀) : ↥probabilityBall :=
  ContractingWith.fixedPoint (ballMap hJ h) (ballMap_contracting hJ h)

theorem nearFixedPoint_eq {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ} {β β₀ : ℝ}
    (h : NearParameters θ β β₀) :
    occupationMap hJ θ β (nearFixedPoint hJ h).val = (nearFixedPoint hJ h).val :=
  congrArg Subtype.val (ballMap_contracting hJ h).fixedPoint_isFixedPt.eq

theorem nearFixedPoint_unique {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ} {β β₀ : ℝ}
    (h : NearParameters θ β β₀) {f : L4} (hf : f ∈ probabilityBall)
    (hfix : occupationMap hJ θ β f = f) : f = (nearFixedPoint hJ h).val := by
  have hh : Function.IsFixedPt (ballMap hJ h) (⟨f, hf⟩ : ↥probabilityBall) := by
    apply Subtype.ext
    exact hfix
  exact congrArg Subtype.val ((ballMap_contracting hJ h).fixedPoint_unique hh)

/-- The a posteriori estimate applies only after the input has genuinely
been placed in the closed probability ball. -/
theorem nearFixedPoint_distance_le {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ} {β β₀ : ℝ}
    (h : NearParameters θ β β₀) {f : L4} (hf : f ∈ probabilityBall) :
    ‖f - (nearFixedPoint hJ h).val‖ ≤ (4 / 3 : ℝ) * ‖f - occupationMap hJ θ β f‖ := by
  let g := (nearFixedPoint hJ h).val
  have hc := occupationMap_contraction hJ h.beta_nonneg h.beta_le h.scale
    (fun a ↦ (profileDeviation_apply_le θ a).trans h.occupation_near)
    f g hf (nearFixedPoint hJ h).property
  rw [nearFixedPoint_eq hJ h] at hc
  have ht : ‖f - g‖ ≤ ‖f - occupationMap hJ θ β f‖ + ‖occupationMap hJ θ β f - g‖ := by
    calc
      _ = ‖(f - occupationMap hJ θ β f) + (occupationMap hJ θ β f - g)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hq := mul_le_mul_of_nonneg_right (meshRate_le hJ h.scale).2 (norm_nonneg (f - g))
  change ‖f - g‖ ≤ _
  linarith

theorem nearFixedPoint_L4_bound {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ} {β β₀ : ℝ}
    (h : NearParameters θ β β₀) :
    ‖(nearFixedPoint hJ h).val - oneL4‖ ≤ (4 / 3 : ℝ) * profileDeviation θ := by
  have hh := nearFixedPoint_distance_le hJ h oneL4_mem_probabilityBall
  rw [norm_sub_rev oneL4 (nearFixedPoint hJ h).val,
    norm_sub_rev oneL4 (occupationMap hJ θ β oneL4)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (occupationMap_one_displacement hJ θ β) (by norm_num))

theorem nearFixedPoint_profile_ae {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ} {β β₀ : ℝ}
    (h : NearParameters θ β β₀) :
    ∀ᵐ x ∂torusMeasure, |(nearFixedPoint hJ h).val x - 1| ≤ (4 / 3 : ℝ) * profileDeviation θ := by
  have he := occupationMap_ae hJ θ β (nearFixedPoint hJ h).val
  rw [nearFixedPoint_eq hJ h] at he
  have hq := (meshRate_le hJ h.scale).2
  have hn := nearFixedPoint_L4_bound hJ h
  have hn0 := profileDeviation_nonneg θ
  filter_upwards [he] with x hx
  rw [hx]
  have hc := occupationMapValue_contraction hJ h.beta_nonneg h.beta_le h.scale
    (fun a ↦ (profileDeviation_apply_le θ a).trans h.occupation_near)
    (nearFixedPoint hJ h).val oneL4 (probabilityBall_norm_le (nearFixedPoint hJ h).property)
    (by rw [norm_oneL4]; norm_num) x
  have hd : |occupationMapValue hJ θ β oneL4 x - 1| ≤ profileDeviation θ := by
    rw [occupationMapValue_one]
    exact profileDeviation_apply_le θ _
  have ht := (abs_sub_le (occupationMapValue hJ θ β (nearFixedPoint hJ h).val x)
    (occupationMapValue hJ θ β oneL4 x) 1).trans (add_le_add hc hd)
  have hm := mul_le_mul_of_nonneg_left hn (contractionFactor_nonneg J β₀)
  have hq' := mul_le_mul_of_nonneg_right hq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3) hn0)
  linarith

theorem nearFixedPoint_Linfty_bound {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ} {β β₀ : ℝ}
    (h : NearParameters θ β β₀) :
    MemLp (fun x ↦ (nearFixedPoint hJ h).val x - 1) ∞ torusMeasure ∧
      lpNorm (fun x ↦ (nearFixedPoint hJ h).val x - 1) ∞ torusMeasure ≤
        (4 / 3 : ℝ) * profileDeviation θ :=
  lpNorm_le_of_ae_bound ((Lp.memLp (nearFixedPoint hJ h).val).aestronglyMeasurable.sub
    aestronglyMeasurable_const)
    (mul_nonneg (by norm_num) (profileDeviation_nonneg θ)) (nearFixedPoint_profile_ae hJ h) (by simp)

def cellIntegral {J : ℕ} (hJ : 0 < J) (u : Torus → ℝ) (a : MeshIndex J) : ℝ :=
  ∫ x in meshCell J hJ a, Real.exp (u x) ∂torusMeasure

theorem cellNormalizer_eq_haar {J : ℕ} (hJ : 0 < J) (u : Torus → ℝ) (a : MeshIndex J) :
    cellNormalizer hJ u a = (J : ℝ) ^ 2 * cellIntegral hJ u a := by
  simp only [cellNormalizer, cellIntegral, meshCellMeasure, integral_smul_measure,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, smul_eq_mul]

theorem cellIntegral_pos {J : ℕ} (hJ : 0 < J) {u : Torus → ℝ}
    (hu : Continuous u) (a : MeshIndex J) : 0 < cellIntegral hJ u a := by
  have hh := cellNormalizer_pos hJ hu a
  rw [cellNormalizer_eq_haar] at hh
  exact (mul_pos_iff_of_pos_left (pow_pos (by exact_mod_cast hJ : (0 : ℝ) < J) 2)).mp hh

theorem cellDensity_haar {J : ℕ} (hJ : 0 < J) {u : Torus → ℝ}
    (hu : Continuous u) (a : MeshIndex J) (x : Torus) :
    (J : ℝ) ^ 2 * cellDensity hJ u a x = Real.exp (u x) / cellIntegral hJ u a := by
  rw [cellDensity, cellNormalizer_eq_haar]
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  field_simp [hJ0, (cellIntegral_pos hJ hu a).ne']

/-- Exact equality with source `eq:occupation-cell-map`, including cells
with zero profile mass and their strictly positive Haar denominators. -/
theorem occupationMapValue_haar {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (β : ℝ) (f : L4) (x : Torus) :
    occupationMapValue hJ θ β f x =
      ∑ a, θ a * (meshCell J hJ a).indicator
        (fun y ↦ Real.exp (scaledPotential β f y) / cellIntegral hJ (scaledPotential β f) a) x := by
  classical
  unfold occupationMapValue
  apply Finset.sum_congr rfl
  intro a _
  by_cases hx : x ∈ meshCell J hJ a
  · rw [indicator_of_mem hx, indicator_of_mem hx]
    calc
      _ = θ a * ((J : ℝ) ^ 2 * cellDensity hJ (scaledPotential β f) a x) := by ring
      _ = _ := by rw [cellDensity_haar hJ (continuous_scaledPotential β f)]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero, mul_zero]

theorem cellNormalizer_ratio_eq_haar {J : ℕ} (hJ : 0 < J) {u : Torus → ℝ}
    (hu : Continuous u) (a b : MeshIndex J) :
    cellNormalizer hJ u b / cellNormalizer hJ u a = cellIntegral hJ u b / cellIntegral hJ u a := by
  rw [cellNormalizer_eq_haar, cellNormalizer_eq_haar]
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  field_simp [hJ0, (cellIntegral_pos hJ hu a).ne']

theorem cellNormalizer_log_difference {J : ℕ} (hJ : 0 < J) {u v : Torus → ℝ}
    (hu : Continuous u) (hv : Continuous v) {D : ℝ} (hb : ∀ x, |u x - v x| ≤ D)
    (a : MeshIndex J) : |Real.log (cellNormalizer hJ u a) - Real.log (cellNormalizer hJ v a)| ≤ D := by
  have hcomp {r s : Torus → ℝ} (hr : Continuous r) (hs : Continuous s)
      (hrs : ∀ x, r x ≤ D + s x) : cellNormalizer hJ r a ≤ Real.exp D * cellNormalizer hJ s a := by
    have hh := integral_mono
      (integrable_continuous_torus (meshCellMeasure J hJ a) (Real.continuous_exp.comp hr))
      ((integrable_continuous_torus (meshCellMeasure J hJ a) (Real.continuous_exp.comp hs)).const_mul (Real.exp D))
      (fun x ↦ by
        simp only [Function.comp_apply]
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (hrs x))
    change (∫ x, Real.exp (r x) ∂meshCellMeasure J hJ a) ≤
      ∫ x, Real.exp D * Real.exp (s x) ∂meshCellMeasure J hJ a at hh
    simpa only [integral_const_mul, cellNormalizer] using hh
  have huv := hcomp hu hv (fun x ↦ by have hh := (abs_le.mp (hb x)).2; linarith)
  have hvu := hcomp hv hu (fun x ↦ by have hh := (abs_le.mp (hb x)).1; linarith)
  have hl := Real.log_le_log (cellNormalizer_pos hJ hu a) huv
  have hr := Real.log_le_log (cellNormalizer_pos hJ hv a) hvu
  rw [Real.log_mul (Real.exp_ne_zero _) (cellNormalizer_pos hJ hv a).ne', Real.log_exp] at hl
  rw [Real.log_mul (Real.exp_ne_zero _) (cellNormalizer_pos hJ hu a).ne', Real.log_exp] at hr
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def potentialDifferenceConstant (β₀ : ℝ) : ℝ :=
  max β₀ 0 * lpNorm regularGreenRepresentative conjugateExponent torusMeasure

theorem potentialDifferenceConstant_nonneg (β₀ : ℝ) : 0 ≤ potentialDifferenceConstant β₀ :=
  mul_nonneg (le_max_right _ _) lpNorm_nonneg

theorem scaledPotential_difference_bound {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (f g : L4) (x : Torus) :
    |scaledPotential β f x - scaledPotential β g x| ≤ potentialDifferenceConstant β₀ * ‖f - g‖ := by
  rw [← congrFun (scaledPotential_sub β f g) x]
  simp only [scaledPotential]
  rw [abs_mul, abs_of_nonneg hβ]
  have hh := densityPotential_bound (Lp.memLp (f - g)) x
  rw [lpNorm_coe] at hh
  calc
    _ ≤ β * (‖f - g‖ * lpNorm regularGreenRepresentative conjugateExponent torusMeasure) :=
      mul_le_mul_of_nonneg_left hh hβ
    _ ≤ max β₀ 0 * (‖f - g‖ * lpNorm regularGreenRepresentative conjugateExponent torusMeasure) :=
      mul_le_mul_of_nonneg_right (hβ₀.trans (le_max_left _ _)) (mul_nonneg (norm_nonneg _) lpNorm_nonneg)
    _ = _ := by unfold potentialDifferenceConstant; ring

theorem cellIntegral_log_ratio_difference {J : ℕ} (hJ : 0 < J) {β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (f g : L4) (a b : MeshIndex J) :
    |Real.log (cellIntegral hJ (scaledPotential β f) b / cellIntegral hJ (scaledPotential β f) a) -
      Real.log (cellIntegral hJ (scaledPotential β g) b / cellIntegral hJ (scaledPotential β g) a)| ≤
        2 * potentialDifferenceConstant β₀ * ‖f - g‖ := by
  rw [← cellNormalizer_ratio_eq_haar hJ (continuous_scaledPotential β f),
    ← cellNormalizer_ratio_eq_haar hJ (continuous_scaledPotential β g)]
  rw [Real.log_div (cellNormalizer_pos hJ (continuous_scaledPotential β f) b).ne'
      (cellNormalizer_pos hJ (continuous_scaledPotential β f) a).ne',
    Real.log_div (cellNormalizer_pos hJ (continuous_scaledPotential β g) b).ne'
      (cellNormalizer_pos hJ (continuous_scaledPotential β g) a).ne']
  have ha := cellNormalizer_log_difference hJ (continuous_scaledPotential β f)
    (continuous_scaledPotential β g) (scaledPotential_difference_bound hβ hβ₀ f g) a
  have hb := cellNormalizer_log_difference hJ (continuous_scaledPotential β f)
    (continuous_scaledPotential β g) (scaledPotential_difference_bound hβ hβ₀ f g) b
  calc
    _ = |(Real.log (cellNormalizer hJ (scaledPotential β f) b) -
          Real.log (cellNormalizer hJ (scaledPotential β g) b)) -
        (Real.log (cellNormalizer hJ (scaledPotential β f) a) -
          Real.log (cellNormalizer hJ (scaledPotential β g) a))| := by congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans ((add_le_add hb ha).trans_eq (by ring))

def nearInputBound (β₀ : ℝ) : ℝ :=
  max (3 / 2) ((9 / 8) * ConditionalLawEstimates.densityNormBound β₀)

theorem nearInputBound_pos (β₀ : ℝ) : 0 < nearInputBound β₀ :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 2) (le_max_left _ _)

/-- The mesh is chosen before N and before the profile and beta. -/
def nearMeshThreshold (β₀ : ℝ) : ℕ :=
  max 1 ⌈max (16 * meshNumerator β₀) (32 * nearInputBound β₀ * meshNumerator β₀)⌉₊

theorem nearMeshThreshold_bounds {J : ℕ} {β₀ : ℝ} (hJ : nearMeshThreshold β₀ ≤ J) :
    0 < J ∧ 16 * meshNumerator β₀ ≤ (J : ℝ) ∧
      meshRate J β₀ * nearInputBound β₀ ≤ 1 / 32 := by
  have hJ1 : 1 ≤ J := (le_max_left _ _).trans hJ
  have hm : max (16 * meshNumerator β₀) (32 * nearInputBound β₀ * meshNumerator β₀) ≤ (J : ℝ) :=
    Nat.ceil_le.mp ((le_max_right _ _).trans hJ)
  have hJr : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  refine ⟨by omega, (le_max_left _ _).trans hm, ?_⟩
  have hb := (le_max_right _ _).trans hm
  unfold meshRate
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hJr).mpr
  nlinarith

def nearParticleThreshold (J : ℕ) (β₀ : ℝ) : ℕ :=
  max (OccupationPartitionTransport.ratioThreshold J β₀)
    ⌈(8 * OccupationFieldApproximation.approximationConstant J β₀) ^ 2⌉₊

theorem nearParticleThreshold_bounds {N J : ℕ} {β₀ : ℝ}
    (hN : nearParticleThreshold J β₀ ≤ N) :
    OccupationPartitionTransport.ratioThreshold J β₀ ≤ N ∧ 2 ≤ N ∧ 8 * β₀ ≤ (N : ℝ) ∧
      OccupationFieldApproximation.approximationConstant J β₀ / Real.sqrt (N : ℝ) ≤ 1 / 8 := by
  have hr : OccupationPartitionTransport.ratioThreshold J β₀ ≤ N := (le_max_left _ _).trans hN
  have hf := OccupationPartitionTransport.ratioThreshold_bounds hr
  have hs : (8 * OccupationFieldApproximation.approximationConstant J β₀) ^ 2 ≤ (N : ℝ) :=
    Nat.ceil_le.mp ((le_max_right _ _).trans hN)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsq := Real.sq_sqrt hNr.le
  have hsp := Real.sqrt_pos.mpr hNr
  refine ⟨hr, hf.1, hf.2.1, (div_le_iff₀ hsp).mpr ?_⟩
  nlinarith

open LabelOccupations ConditionalLawEstimates

def occupationProfile {N J : ℕ} (η : LabelVector J N) (a : MeshIndex J) : ℝ :=
  (occupation η a : ℝ) / (N : ℝ)

theorem occupationProfile_nonneg {N J : ℕ} (η : LabelVector J N) (a : MeshIndex J) :
    0 ≤ occupationProfile η a := by unfold occupationProfile; positivity

theorem occupationProfile_mass {N J : ℕ} (hN : 0 < N) (η : LabelVector J N) :
    ∑ a, occupationProfile η a = 1 := by
  unfold occupationProfile
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_occupation]
  exact div_self (by exact_mod_cast hN.ne')

theorem near_profile_fourth_bound {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ}
    (hθ : ∀ a, 0 ≤ θ a) (hnear : profileDeviation θ ≤ 1 / 8) :
    (J : ℝ) ^ 6 * ∑ a, θ a ^ 4 ≤ (9 / 8 : ℝ) ^ 4 := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have ha (a : MeshIndex J) : θ a ≤ (9 / 8 : ℝ) / (J : ℝ) ^ 2 := by
    apply (le_div_iff₀ (pow_pos hJr 2)).mpr
    have hh := (abs_le.mp ((profileDeviation_apply_le θ a).trans hnear)).2
    nlinarith
  calc
    _ ≤ (J : ℝ) ^ 6 * ∑ _a : MeshIndex J, ((9 / 8 : ℝ) / (J : ℝ) ^ 2) ^ 4 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun a _ ↦ pow_le_pow_left₀ (hθ a) (ha a) 4) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, card_meshIndex, nsmul_eq_mul, Nat.cast_pow]
      field_simp [hJr.ne']

theorem occupationMapValue_near_step {J : ℕ} (hJ : 0 < J) {β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hnearJ : nearMeshThreshold β₀ ≤ J)
    {θ : MeshIndex J → ℝ} (hnear : profileDeviation θ ≤ 1 / 8)
    (f : L4) (hf : ‖f‖ ≤ nearInputBound β₀) (x : Torus) :
    |occupationMapValue hJ θ β f x - (J : ℝ) ^ 2 * θ (meshLabel J hJ x)| ≤ 1 / 8 := by
  let a := meshLabel J hJ x
  have hx : x ∈ meshCell J hJ a := rfl
  have hosc : ∀ y ∈ meshCell J hJ a, ∀ z ∈ meshCell J hJ a,
      |scaledPotential β f y - scaledPotential β f z| ≤ meshRate J β₀ * nearInputBound β₀ := by
    intro y hy z hz
    exact (scaledPotential_cell_oscillation hJ hβ hβ₀ f a hy hz).trans
      (mul_le_mul_of_nonneg_left hf (meshRate_nonneg J β₀))
  have hM := (nearMeshThreshold_bounds hnearJ).2.2
  have hd := cellDensity_sub_one_le hJ (continuous_scaledPotential β f) a
    (mul_nonneg (meshRate_nonneg J β₀) (nearInputBound_pos β₀).le)
    (hM.trans (by norm_num)) hosc hx
  have ha := abs_le.mp ((profileDeviation_apply_le θ a).trans hnear)
  have ha0 : 0 ≤ (J : ℝ) ^ 2 * θ a := by linarith
  have ha1 : (J : ℝ) ^ 2 * θ a ≤ 9 / 8 := by linarith
  rw [occupationMapValue_apply]
  change |(J : ℝ) ^ 2 * θ a * cellDensity hJ (scaledPotential β f) a x -
    (J : ℝ) ^ 2 * θ a| ≤ _
  rw [← mul_sub_one, abs_mul, abs_of_nonneg ha0]
  have hsmall : |cellDensity hJ (scaledPotential β f) a x - 1| ≤ 1 / 16 := by linarith
  calc
    _ ≤ (9 / 8 : ℝ) * (1 / 16) := mul_le_mul ha1 hsmall (abs_nonneg _) (by norm_num)
    _ ≤ _ := by norm_num

theorem approximationConstant_nonneg (J : ℕ) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    0 ≤ OccupationFieldApproximation.approximationConstant J β₀ := by
  unfold OccupationFieldApproximation.approximationConstant
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (div_nonneg (mul_nonneg (by norm_num)
      (OccupationFieldApproximation.exponentialErrorConstant_nonneg J hβ₀))
      (OccupationFieldApproximation.fieldNormalizerLower_pos J β₀).le)

section ActualAverage

variable {n J : ℕ} (hN : 2 ≤ n + 1) {β₀ β δ : ℝ}
  (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
  (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
  (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)

/-- The L4 equivalence class of the actual average of the original
prescribed-cell Gibbs marginals; no new marginal law is introduced. -/
def averageMarginalL4 : L4 :=
  (OccupationFieldL2.averageDensity_L4 hN hβ hβ₀ hsub hδ hmesh η hη).1.toLp
    (OccupationFieldL2.averageDensity (mesh_pos hmesh) η β)

local notation "fN" => averageMarginalL4 hN hβ hβ₀ hsub hδ hmesh η hη
local notation "θN" => occupationProfile η

theorem averageMarginalL4_ae :
    fN =ᵐ[torusMeasure] OccupationFieldL2.averageDensity (mesh_pos hmesh) η β :=
  (OccupationFieldL2.averageDensity_L4 hN hβ hβ₀ hsub hδ hmesh η hη).1.coeFn_toLp

theorem averageMarginalL4_norm :
    ‖fN‖ = lpNorm (OccupationFieldL2.averageDensity (mesh_pos hmesh) η β) 4 torusMeasure := by
  rw [← lpNorm_coe]
  exact congrArg ENNReal.toReal (eLpNorm_congr_ae (p := 4)
    (averageMarginalL4_ae hN hβ hβ₀ hsub hδ hmesh η hη))

theorem averageMarginalL4_nonneg : 0 ≤ fN := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [averageMarginalL4_ae hN hβ hβ₀ hsub hδ hmesh η hη] with x hx
  rw [hx]
  exact OccupationFieldL2.averageDensity_nonneg (mesh_pos hmesh) η β x

theorem averageMarginalL4_mass : (∫ x, fN x ∂torusMeasure) = 1 := by
  rw [integral_congr_ae (averageMarginalL4_ae hN hβ hβ₀ hsub hδ hmesh η hη)]
  exact (OccupationFieldL2.averageDensity_L4 hN hβ hβ₀ hsub hδ hmesh η hη).2.2

theorem averageMarginalL4_potential (x : Torus) :
    scaledPotential β fN x = β * OccupationFieldL2.meanPotential (mesh_pos hmesh) η β x := by
  rw [scaledPotential, densityPotential_congr_ae
    (averageMarginalL4_ae hN hβ hβ₀ hsub hδ hmesh η hη),
    densityPotential_eq_original (OccupationFieldL2.averageDensity_L4 hN hβ hβ₀ hsub hδ hmesh η hη).1]
  rfl

/-- This bound precedes, and does not use, membership in the contraction
ball. It is the refined actual occupation-weighted L4 estimate. -/
theorem averageMarginalL4_near_norm (hnear : profileDeviation θN ≤ 1 / 8) :
    ‖fN‖ ≤ (9 / 8 : ℝ) * densityNormBound β₀ := by
  have hm := OccupationFieldL2.averageDensity_L4_refined hN hβ hβ₀ hsub hδ hmesh η hη
  rw [← averageMarginalL4_norm hN hβ hβ₀ hsub hδ hmesh η hη] at hm
  have hθ := near_profile_fourth_bound (mesh_pos hmesh) (occupationProfile_nonneg η) hnear
  have hprod := mul_le_mul_of_nonneg_left hθ (pow_nonneg (densityNormBound_pos β₀).le 4)
  have he : ‖fN‖ ^ 4 ≤ ((9 / 8 : ℝ) * densityNormBound β₀) ^ 4 := by
    have hm' : ‖fN‖ ^ 4 ≤ densityNormBound β₀ ^ 4 * (J : ℝ) ^ 6 * ∑ a, θN a ^ 4 := by
      simpa only [occupationProfile, Nat.cast_add, Nat.cast_one] using hm
    exact hm'.trans (by convert hprod using 1 <;> ring)
  have hc : 0 ≤ (9 / 8 : ℝ) * densityNormBound β₀ := by
    exact mul_nonneg (by norm_num) (densityNormBound_pos β₀).le
  by_contra hh
  have hh' : (9 / 8 : ℝ) * densityNormBound β₀ < ‖fN‖ := lt_of_not_ge hh
  have hp : 0 < (‖fN‖ - (9 / 8 : ℝ) * densityNormBound β₀) *
      (‖fN‖ + (9 / 8 : ℝ) * densityNormBound β₀) :=
    mul_pos (sub_pos.mpr hh') (by linarith)
  have hp' : 0 < (‖fN‖ ^ 2 - ((9 / 8 : ℝ) * densityNormBound β₀) ^ 2) *
      (‖fN‖ ^ 2 + ((9 / 8 : ℝ) * densityNormBound β₀) ^ 2) :=
    mul_pos (by nlinarith only [hp])
      (by nlinarith only [hp, sq_nonneg ((9 / 8 : ℝ) * densityNormBound β₀)])
  nlinarith only [hp', he]

theorem averageMarginalL4_map_residual (hlarge : 8 * β₀ ≤ (n + 1 : ℕ)) (x : Torus) :
    |OccupationFieldL2.averageDensity (mesh_pos hmesh) η β x -
      occupationMapValue (mesh_pos hmesh) θN β fN x| ≤
        OccupationFieldApproximation.approximationConstant J β₀ / Real.sqrt (n + 1 : ℝ) := by
  have hh := OccupationFieldApproximation.approximate_fixed_point hN hβ hβ₀ hsub hδ hmesh η hη hlarge x
  rw [occupationMapValue_haar]
  simpa only [cellIntegral, averageMarginalL4_potential hN hβ hβ₀ hsub hδ hmesh η hη,
    occupationProfile, Nat.cast_add, Nat.cast_one] using hh

theorem averageMarginalL4_map_residual_L4 (hlarge : 8 * β₀ ≤ (n + 1 : ℕ)) :
    ‖fN - occupationMap (mesh_pos hmesh) θN β fN‖ ≤
      OccupationFieldApproximation.approximationConstant J β₀ / Real.sqrt (n + 1 : ℝ) := by
  apply L4_norm_le_of_ae_bound _
    (div_nonneg (approximationConstant_nonneg J (hβ.trans hβ₀)) (Real.sqrt_nonneg _))
  filter_upwards [Lp.coeFn_sub fN (occupationMap (mesh_pos hmesh) θN β fN),
    averageMarginalL4_ae hN hβ hβ₀ hsub hδ hmesh η hη,
    occupationMap_ae (mesh_pos hmesh) θN β fN] with x hs hf ht
  simp only [hs, Pi.sub_apply, hf, ht]
  exact averageMarginalL4_map_residual hN hβ hβ₀ hsub hδ hmesh η hη hlarge x

/-- Actual placement of the original average marginal in the complete
ball, before applying any contraction error estimate. -/
theorem averageMarginalL4_mem_probabilityBall
    (hnearJ : nearMeshThreshold β₀ ≤ J) (hnearN : nearParticleThreshold J β₀ ≤ n + 1)
    (hnear : profileDeviation θN ≤ 1 / 8) : fN ∈ probabilityBall := by
  refine ⟨averageMarginalL4_nonneg hN hβ hβ₀ hsub hδ hmesh η hη,
    averageMarginalL4_mass hN hβ hβ₀ hsub hδ hmesh η hη, ?_⟩
  have hn := nearParticleThreshold_bounds hnearN
  have hb : ‖fN‖ ≤ nearInputBound β₀ :=
    (averageMarginalL4_near_norm hN hβ hβ₀ hsub hδ hmesh η hη hnear).trans (le_max_right _ _)
  apply L4_norm_le_of_ae_bound _ (by norm_num)
  filter_upwards [Lp.coeFn_sub fN oneL4,
    averageMarginalL4_ae hN hβ hβ₀ hsub hδ hmesh η hη, oneL4_ae] with x hs hf h1
  simp only [hs, Pi.sub_apply, hf, h1]
  have hr := averageMarginalL4_map_residual hN hβ hβ₀ hsub hδ hmesh η hη hn.2.2.1 x
  have ht := occupationMapValue_near_step (mesh_pos hmesh) hβ hβ₀ hnearJ hnear fN hb x
  have he := (profileDeviation_apply_le θN (meshLabel J (mesh_pos hmesh) x)).trans hnear
  have htri := abs_sub_le (OccupationFieldL2.averageDensity (mesh_pos hmesh) η β x)
    (occupationMapValue (mesh_pos hmesh) θN β fN x) 1
  have htri' := abs_sub_le (occupationMapValue (mesh_pos hmesh) θN β fN x)
    ((J : ℝ) ^ 2 * θN (meshLabel J (mesh_pos hmesh) x)) 1
  have hn' : OccupationFieldApproximation.approximationConstant J β₀ / Real.sqrt (n + 1 : ℝ) ≤ 1 / 8 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hn.2.2.2
  linarith

end ActualAverage

/-- A single fixed tolerance and spatial threshold suffice for every
probability profile and every beta in the closed interval starting at zero. -/
theorem nearProfileParameters {J : ℕ} {β β₀ : ℝ} {θ : MeshIndex J → ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hJ : nearMeshThreshold β₀ ≤ J)
    (hθ₀ : ∀ a, 0 ≤ θ a) (hθ₁ : ∑ a, θ a = 1)
    (hnear : profileDeviation θ ≤ 1 / 8) : NearParameters θ β β₀ :=
  ⟨hβ, hβ₀, (nearMeshThreshold_bounds hJ).2.1, hθ₀, hθ₁, hnear.trans (by norm_num)⟩

theorem occupationMap_Linfty_contraction {J : ℕ} (hJ : 0 < J) {β β₀ : ℝ}
    {θ : MeshIndex J → ℝ} (h : NearParameters θ β β₀)
    (f g : L4) (hf : f ∈ probabilityBall) (hg : g ∈ probabilityBall) :
    MemLp (fun x ↦ occupationMapValue hJ θ β f x - occupationMapValue hJ θ β g x)
      ∞ torusMeasure ∧
    lpNorm (fun x ↦ occupationMapValue hJ θ β f x - occupationMapValue hJ θ β g x)
      ∞ torusMeasure ≤ contractionFactor J β₀ * ‖f - g‖ := by
  apply lpNorm_le_of_ae_bound
    ((occupationMapValue_measurable hJ θ β f).sub
      (occupationMapValue_measurable hJ θ β g)).aestronglyMeasurable
    (mul_nonneg (contractionFactor_nonneg J β₀) (norm_nonneg _)) _ (by simp)
  exact Eventually.of_forall fun x ↦ occupationMapValue_contraction hJ h.beta_nonneg h.beta_le h.scale
    (fun a ↦ (profileDeviation_apply_le θ a).trans h.occupation_near) f g
    (probabilityBall_norm_le hf) (probabilityBall_norm_le hg) x

/-- The first two conclusions of source `lem:occupation-contraction`:
actual contraction, existence and uniqueness in the stated ball, and the
exact 4/3 profile bound. No fixed-point premise is imposed. -/
theorem near_profile_fixed_point {J : ℕ} {β β₀ : ℝ} {θ : MeshIndex J → ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hJ : nearMeshThreshold β₀ ≤ J)
    (hθ₀ : ∀ a, 0 ≤ θ a) (hθ₁ : ∑ a, θ a = 1)
    (hnear : profileDeviation θ ≤ 1 / 8) :
    contractionFactor J β₀ ≤ 1 / 4 ∧
    ∃ f : L4, f ∈ probabilityBall ∧
      occupationMap (nearMeshThreshold_bounds hJ).1 θ β f = f ∧
      (∀ g ∈ probabilityBall, occupationMap (nearMeshThreshold_bounds hJ).1 θ β g = g → g = f) ∧
      MemLp (fun x ↦ f x - 1) ∞ torusMeasure ∧
      lpNorm (fun x ↦ f x - 1) ∞ torusMeasure ≤ (4 / 3 : ℝ) * profileDeviation θ := by
  let h := nearProfileParameters hβ hβ₀ hJ hθ₀ hθ₁ hnear
  let hp := (nearMeshThreshold_bounds hJ).1
  exact ⟨(meshRate_le hp h.scale).2, (nearFixedPoint hp h).val,
    (nearFixedPoint hp h).property, nearFixedPoint_eq hp h,
    fun _ hg he ↦ nearFixedPoint_unique hp h hg he,
    nearFixedPoint_Linfty_bound hp h⟩

theorem occupationMapValue_beta_zero {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (f : L4) (x : Torus) :
    occupationMapValue hJ θ 0 f x = (J : ℝ) ^ 2 * θ (meshLabel J hJ x) := by
  rw [occupationMapValue_apply]
  simp only [cellDensity, cellNormalizer, scaledPotential, zero_mul, Real.exp_zero,
    integral_const, probReal_univ, one_smul, div_one, mul_one]

open OccupationProbability LabelRatioTransport

open Classical in
/-- The real error indexed by every ordered pair of cells. The value is
zero outside the source supremum's literal conditions. -/
def nearRateError {N J : ℕ} (hJ : 0 < J) (η : LabelVector J N) (β : ℝ) (f : L4)
    (ab : MeshIndex J × MeshIndex J) : ℝ :=
  if ab.1 ≠ ab.2 ∧ 1 ≤ occupation η ab.1 then
    Real.log ((profileWeight (N := N) hJ (moveOccupation (occupation η) ab.1 ab.2) β).toReal /
      (profileWeight (N := N) hJ (occupation η) β).toReal) -
      Real.log (cellIntegral hJ (scaledPotential β f) ab.2 / cellIntegral hJ (scaledPotential β f) ab.1)
  else 0

def nearRateConstant (J : ℕ) (β₀ : ℝ) : ℝ :=
  (4 / 3 : ℝ) * OccupationFieldApproximation.approximationConstant J β₀ +
    OccupationPartitionTransport.logarithmicRatioConstant J β₀ +
    (8 / 3 : ℝ) * potentialDifferenceConstant β₀ * OccupationFieldApproximation.approximationConstant J β₀

theorem nearRateConstant_nonneg (J : ℕ) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    0 ≤ nearRateConstant J β₀ := by
  unfold nearRateConstant
  have hA := approximationConstant_nonneg J hβ₀
  have hQ := OccupationPartitionTransport.logarithmicRatioConstant_nonneg J hβ₀
  have hP := potentialDifferenceConstant_nonneg β₀
  positivity

section NearRates

variable {n J : ℕ} {β₀ β δ : ℝ}
  (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
  (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
  (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
  (hnearJ : nearMeshThreshold β₀ ≤ J) (hnearN : nearParticleThreshold J β₀ ≤ n + 1)
  (hnear : profileDeviation (occupationProfile η) ≤ 1 / 8)

def actualNearFixedPoint : ↥probabilityBall :=
  nearFixedPoint (mesh_pos hmesh)
    (nearProfileParameters hβ hβ₀ hnearJ (occupationProfile_nonneg η)
      (occupationProfile_mass (by omega) η) hnear)

local notation "hN" => And.left (And.right (nearParticleThreshold_bounds hnearN))
local notation "fN" => averageMarginalL4 hN hβ hβ₀ hsub hδ hmesh η hη
local notation "fθ" => Subtype.val (actualNearFixedPoint hβ hβ₀ hmesh η hnearJ hnear)

theorem actualNearFixedPoint_eq :
    occupationMap (mesh_pos hmesh) (occupationProfile η) β fθ = fθ :=
  nearFixedPoint_eq _ _

theorem actualNearFixedPoint_unique {f : L4} (hf : f ∈ probabilityBall)
    (he : occupationMap (mesh_pos hmesh) (occupationProfile η) β f = f) : f = fθ :=
  nearFixedPoint_unique _ _ hf he

theorem actualNearFixedPoint_profile_bound :
    MemLp (fun x ↦ fθ x - 1) ∞ torusMeasure ∧
      lpNorm (fun x ↦ fθ x - 1) ∞ torusMeasure ≤ (4 / 3 : ℝ) * profileDeviation (occupationProfile η) :=
  nearFixedPoint_Linfty_bound _ _

/-- The posterior estimate is invoked only with the independently proved
actual marginal placement from `averageMarginalL4_mem_probabilityBall`. -/
theorem averageMarginal_near_fixed_point :
    ‖fN - fθ‖ ≤ (4 / 3 : ℝ) * OccupationFieldApproximation.approximationConstant J β₀ /
      Real.sqrt (n + 1 : ℝ) := by
  have hm := averageMarginalL4_mem_probabilityBall hN hβ hβ₀ hsub hδ hmesh η hη hnearJ hnearN hnear
  have hh := nearFixedPoint_distance_le (mesh_pos hmesh)
    (nearProfileParameters hβ hβ₀ hnearJ (occupationProfile_nonneg η)
      (occupationProfile_mass (by omega) η) hnear) hm
  have hr := averageMarginalL4_map_residual_L4 hN hβ hβ₀ hsub hδ hmesh η hη
    (nearParticleThreshold_bounds hnearN).2.2.1
  change ‖fN - fθ‖ ≤ _ at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 4 / 3)).trans_eq (by ring))

include hsub hδ hη hnearN

theorem averageMarginal_near_fixed_point_lpNorm :
    lpNorm (fun x ↦ OccupationFieldL2.averageDensity (mesh_pos hmesh) η β x - fθ x)
      4 torusMeasure ≤ (4 / 3 : ℝ) * OccupationFieldApproximation.approximationConstant J β₀ /
        Real.sqrt (n + 1 : ℝ) := by
  have he : (fN - fθ : L4) =ᵐ[torusMeasure]
      fun x ↦ OccupationFieldL2.averageDensity (mesh_pos hmesh) η β x - fθ x := by
    filter_upwards [Lp.coeFn_sub fN fθ,
      averageMarginalL4_ae hN hβ hβ₀ hsub hδ hmesh η hη] with x hs hx
    simp only [hs, Pi.sub_apply, hx]
  have hn := congrArg ENNReal.toReal (eLpNorm_congr_ae (p := 4) he)
  change lpNorm (fN - fθ : L4) 4 torusMeasure =
    lpNorm (fun x ↦ OccupationFieldL2.averageDensity (mesh_pos hmesh) η β x - fθ x) 4 torusMeasure at hn
  rw [← hn, lpNorm_coe]
  exact averageMarginal_near_fixed_point hβ hβ₀ hsub hδ hmesh η hη hnearJ hnearN hnear

/-- Every source cell with positive occupation is permitted, and no
positive-occupation condition is imposed on the destination cell. -/
theorem actual_near_Q_log_ratio (a b : MeshIndex J) (ha : 1 ≤ occupation η a) :
    |Real.log ((profileWeight (N := n + 1) (mesh_pos hmesh)
        (moveOccupation (occupation η) a b) β).toReal /
      (profileWeight (N := n + 1) (mesh_pos hmesh) (occupation η) β).toReal) -
      Real.log (cellIntegral (mesh_pos hmesh) (scaledPotential β fθ) b /
        cellIntegral (mesh_pos hmesh) (scaledPotential β fθ) a)| ≤
      (OccupationPartitionTransport.logarithmicRatioConstant J β₀ +
        (8 / 3 : ℝ) * potentialDifferenceConstant β₀ *
          OccupationFieldApproximation.approximationConstant J β₀) / Real.sqrt (n + 1 : ℝ) := by
  have hp := OccupationPartitionTransport.occupation_Q_log_ratio_cells
    (nearParticleThreshold_bounds hnearN).1 hβ hβ₀ hsub hδ hmesh η hη a b ha
  have he : (fun x ↦ β * OccupationFieldL2.meanPotential (mesh_pos hmesh) η β x) =
      scaledPotential β fN := funext fun x ↦
    (averageMarginalL4_potential hN hβ hβ₀ hsub hδ hmesh η hη x).symm
  change |Real.log _ - Real.log
    (cellIntegral (mesh_pos hmesh) (fun x ↦ β * OccupationFieldL2.meanPotential (mesh_pos hmesh) η β x) b /
      cellIntegral (mesh_pos hmesh) (fun x ↦ β * OccupationFieldL2.meanPotential (mesh_pos hmesh) η β x) a)| ≤ _ at hp
  rw [he] at hp
  have hd := cellIntegral_log_ratio_difference (mesh_pos hmesh) hβ hβ₀ fN fθ a b
  have hf := averageMarginal_near_fixed_point hβ hβ₀ hsub hδ hmesh η hη hnearJ hnearN hnear
  have hb := mul_le_mul_of_nonneg_left hf (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (potentialDifferenceConstant_nonneg β₀))
  calc
    _ ≤ |Real.log ((profileWeight (N := n + 1) (mesh_pos hmesh)
        (moveOccupation (occupation η) a b) β).toReal /
      (profileWeight (N := n + 1) (mesh_pos hmesh) (occupation η) β).toReal) -
        Real.log (cellIntegral (mesh_pos hmesh) (scaledPotential β fN) b /
          cellIntegral (mesh_pos hmesh) (scaledPotential β fN) a)| +
      |Real.log (cellIntegral (mesh_pos hmesh) (scaledPotential β fN) b /
        cellIntegral (mesh_pos hmesh) (scaledPotential β fN) a) -
        Real.log (cellIntegral (mesh_pos hmesh) (scaledPotential β fθ) b /
          cellIntegral (mesh_pos hmesh) (scaledPotential β fθ) a)| := abs_sub_le _ _ _
    _ ≤ _ := (add_le_add hp (hd.trans hb)).trans_eq (by ring)

theorem actual_near_Q_log_ratio_sup :
    ‖nearRateError (mesh_pos hmesh) η β fθ‖ ≤
      (OccupationPartitionTransport.logarithmicRatioConstant J β₀ +
        (8 / 3 : ℝ) * potentialDifferenceConstant β₀ *
          OccupationFieldApproximation.approximationConstant J β₀) / Real.sqrt (n + 1 : ℝ) := by
  have hA := approximationConstant_nonneg J (hβ.trans hβ₀)
  have hQ := OccupationPartitionTransport.logarithmicRatioConstant_nonneg J (hβ.trans hβ₀)
  have hP := potentialDifferenceConstant_nonneg β₀
  have hC : 0 ≤ (OccupationPartitionTransport.logarithmicRatioConstant J β₀ +
      (8 / 3 : ℝ) * potentialDifferenceConstant β₀ *
        OccupationFieldApproximation.approximationConstant J β₀) / Real.sqrt (n + 1 : ℝ) := by positivity
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro ab
  rw [Real.norm_eq_abs]
  unfold nearRateError
  split
  · rename_i hab
    exact actual_near_Q_log_ratio hβ hβ₀ hsub hδ hmesh η hη hnearJ hnearN hnear ab.1 ab.2 hab.2
  · simpa only [abs_zero] using hC

/-- Source `eq:occupation-near-rates` with the actual average marginal,
the genuine unique nearby fixed point, original particle number, and the
finite supremum over the literal admissible occupation moves. -/
theorem source_near_rates :
    lpNorm (fun x ↦ OccupationFieldL2.averageDensity (mesh_pos hmesh) η β x - fθ x) 4 torusMeasure +
      ‖nearRateError (mesh_pos hmesh) η β fθ‖ ≤ nearRateConstant J β₀ / Real.sqrt (n + 1 : ℝ) := by
  have hL := averageMarginal_near_fixed_point_lpNorm hβ hβ₀ hsub hδ hmesh η hη hnearJ hnearN hnear
  have hR := actual_near_Q_log_ratio_sup hβ hβ₀ hsub hδ hmesh η hη hnearJ hnearN hnear
  exact (add_le_add hL hR).trans_eq (by unfold nearRateConstant; ring)

end NearRates

end PeriodicAttractiveLogGas.OccupationNearContraction
