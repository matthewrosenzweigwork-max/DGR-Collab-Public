import DGPS.Particle.RateEquivalences
import DGPS.FiniteN.Tools.WeightedSobolev
import DGPS.FiniteN.Tools.Linearization
import DGPS.Particle.Contractions
import DGPS.Analysis.CircleLSI
import DGPS.Analysis.BoundedPerturbation


/-!
# Finite positive particle rate and real bridge (FIN001)

For every fixed particle number `N ≥ 1` (and `d ≥ 1`) the Gibbs density is bounded above and
below by positive constants, and the three finite-`N` rates `particleRateAll`, `particleRateSym`
(DEF019) and the unrestricted ordinary Poincare rate `particlePoincareRate` (SETUP-T13) lie in
`(0, ∞)` as extended nonnegative reals.  Their real parts then preserve inequalities; the scale
predicates `ThetaScale` and `ArrheniusScale` are stated for real sequences, so logarithms are only
taken after this bridge.

Design notes (R5):
* `InteractionData` carries only continuity of `V, W`; the density bounds need nothing more.
* `0 < d` is necessary: for `d = 0` the torus is a point, no test has positive variance and all
  three infima are `⊤`.
* Lower bounds: Haar LSI / Poincare on `𝕋^{Nd}` transferred to the particle torus, compared with
  the Gibbs law through the two-sided density bounds.  Upper bounds: the smooth bounded symmetric
  function `∑ᵢ Re e^{2πi xᵢ₀}` (centred), linearized by `linearization_rate_le`.
-/

open MeasureTheory
open scoped ENNReal ContDiff

namespace DGPS.FiniteN.PositiveRate

open DGPS DGPS.FiniteN.Tools.WeightedSobolev

theorem homogeneousEntropy_comp_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (v : β → ℝ) :
    homogeneousEntropy μ (fun x => v (e x)) = homogeneousEntropy ν v := by
  unfold homogeneousEntropy
  have h1 : ∫ x, v (e x) ∂μ = ∫ y, v y ∂ν := he.integral_comp' v
  simp only [h1]
  congr 1
  exact he.lintegral_comp_emb e.measurableEmbedding
    (fun y => ENNReal.ofReal (entropyIntegrand (∫ y, v y ∂ν) (v y)))

theorem entropy_le_of_measure_le_smul {α : Type*} [MeasurableSpace α] {P m : Measure α}
    [IsProbabilityMeasure P] [IsProbabilityMeasure m] {C : ℝ} (hPm : P ≤ ENNReal.ofReal C • m)
    {v : α → ℝ} (hv0 : ∀ x, 0 ≤ v x) (hv : Integrable v m) :
    homogeneousEntropy P v ≤ ENNReal.ofReal C * homogeneousEntropy m v := by
  have hvP : Integrable v P := hv.of_measure_le_smul ENNReal.ofReal_ne_top hPm
  by_cases haP : ∫ x, v x ∂P = 0
  · rw [homogeneousEntropy_of_integral_eq_zero haP]; exact bot_le
  have hPac : P ≪ m := by
    intro s hs
    have := hPm s
    simp only [Measure.smul_apply, smul_eq_mul, hs, mul_zero, nonpos_iff_eq_zero] at this
    exact this
  have hbpos : 0 < ∫ x, v x ∂m := by
    refine lt_of_le_of_ne (integral_nonneg hv0) fun h0 => haP ?_
    have hz : v =ᵐ[m] 0 := (integral_eq_zero_iff_of_nonneg hv0 hv).1 h0.symm
    exact integral_eq_zero_of_ae (hPac.ae_le hz)
  calc homogeneousEntropy P v
      ≤ ∫⁻ x, ENNReal.ofReal (entropyIntegrand (∫ y, v y ∂m) (v x)) ∂P :=
        def025_entropy_le_lintegral hv0 hvP hbpos
    _ ≤ ∫⁻ x, ENNReal.ofReal (entropyIntegrand (∫ y, v y ∂m) (v x))
          ∂(ENNReal.ofReal C • m) := lintegral_mono' hPm le_rfl
    _ = ENNReal.ofReal C * homogeneousEntropy m v := by
        rw [lintegral_smul_measure, smul_eq_mul,
          homogeneousEntropy_of_integral_ne_zero hbpos.ne']

theorem norm_sq_tangentL {d : ℕ} {N : ℕ+} (v : Fin N → Tangent d) :
    ‖tangentL d N v‖ ^ 2 = particleTangentNormSq v := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold particleTangentNormSq
  simp only [Real.norm_eq_abs, sq_abs, tangentL_apply, EuclideanSpace.norm_sq_eq]
  rw [← Fintype.sum_prod_type' (f := fun i j => (v i).ofLp j ^ 2)]
  exact Fintype.sum_equiv (idx N d).symm _ _ (fun _ => rfl)


/-- Haar LSI on the particle torus, transferred from `𝕋^{Nd}`. -/
theorem particleHaar_lsi {d : ℕ} {N : ℕ+} {f : ParticleSpace d N → ℝ}
    {g : ParticleSpace d N → Fin N → Tangent d} (hg : IsParticleHaarWeakGradient N f g) :
    homogeneousEntropy (particleHaar d N) (fun x => f x ^ 2) ≤
      ENNReal.ofReal (2 / (4 * Real.pi ^ 2)) *
        ∫⁻ x, ENNReal.ofReal (particleTangentNormSq (g x)) ∂particleHaar d N := by
  have h := haar_torus_lsi ((N : ℕ) * d) _ _ (isWeakGradient_comp_ofT hg)
  have hp := (measurePreserving_toT (d := d) (N := N)).symm (torusEquiv d N)
  have e1 := homogeneousEntropy_comp_equiv (torusEquiv d N).symm hp (fun x => f x ^ 2)
  have e2 := hp.lintegral_comp_emb (torusEquiv d N).symm.measurableEmbedding
    (fun x => ENNReal.ofReal (particleTangentNormSq (g x)))
  simp only [torusEquiv_symm_apply] at e1 e2
  rw [← e1]
  simp only [norm_sq_tangentL] at h
  rw [e2] at h
  exact h


theorem particleLaw_le_smul {d : ℕ} (A : InteractionData d) (N : ℕ+) {C : ℝ}
    (hb : ∀ x, particleDensity A N x ≤ C) :
    particleLaw A N ≤ ENNReal.ofReal C • particleHaar d N := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [particleLaw, withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ x in s, ENNReal.ofReal (particleDensity A N x) ∂particleHaar d N
      ≤ ∫⁻ _ in s, ENNReal.ofReal C ∂particleHaar d N :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hb x)
    _ = _ := by rw [setLIntegral_const]

theorem particleHaar_le_smul {d : ℕ} (A : InteractionData d) (N : ℕ+) {c : ℝ} (hc : 0 < c)
    (hb : ∀ x, c ≤ particleDensity A N x) :
    particleHaar d N ≤ ENNReal.ofReal c⁻¹ • particleLaw A N := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul, particleLaw, withDensity_apply _ hs]
  calc particleHaar d N s = ∫⁻ _ in s, 1 ∂particleHaar d N := by simp
    _ ≤ ∫⁻ x in s, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (particleDensity A N x) ∂particleHaar d N :=
        lintegral_mono fun x => by
          rw [← ENNReal.ofReal_mul (inv_pos.2 hc).le]
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (by
            rw [inv_mul_eq_div, le_div_iff₀ hc]; simpa using hb x)
    _ = _ := by
        rw [lintegral_const_mul _ (DGPS.Particle.particleDensity_measurable A N).ennreal_ofReal]

/-- Positive LSI constant for the Gibbs law from the density bounds and the Haar LSI. -/
theorem particleRateAll_pos_aux {d : ℕ} (A : InteractionData d) (N : ℕ+) :
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ particleRateAll A N := by
  obtain ⟨c, C, hc, hcC, hb⟩ := DGPS.Particle.particleDensity_bounded A N
  have hC : 0 < C := lt_of_lt_of_le hc hcC
  have hπ : 0 < 4 * Real.pi ^ 2 := by positivity
  refine ⟨4 * Real.pi ^ 2 * c / C, by positivity, ?_⟩
  rw [← particleRate_iff_lsi A N (by positivity)]
  intro f
  have hgP := isParticleWeakGradient_particleWeakGradient f
  have hg := (isParticleWeakGradient_iff A N _ _).1 hgP
  set g := particleWeakGradient f with hgdef
  have hPprob := DGPS.Particle.particleLaw_isProbabilityMeasure' A N
  have h1 : particleLaw A N ≤ ENNReal.ofReal C • particleHaar d N :=
    particleLaw_le_smul A N fun x => (hb x).2
  have h2 : particleHaar d N ≤ ENNReal.ofReal c⁻¹ • particleLaw A N :=
    particleHaar_le_smul A N hc fun x => (hb x).1
  have hE : ∫⁻ x, ENNReal.ofReal (particleTangentNormSq (g x)) ∂particleLaw A N =
      ENNReal.ofReal (particleEnergy A N f) := by
    unfold particleEnergy
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_particleTangentNormSq hgP.memLp_grad)
      (Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)]
  calc particleEntropy A N f
      = homogeneousEntropy (particleLaw A N) (fun x => f x ^ 2) := rfl
    _ ≤ ENNReal.ofReal C * homogeneousEntropy (particleHaar d N) (fun x => f x ^ 2) :=
        entropy_le_of_measure_le_smul h1 (fun x => sq_nonneg _) hg.memLp.integrable_sq
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (2 / (4 * Real.pi ^ 2)) *
          ∫⁻ x, ENNReal.ofReal (particleTangentNormSq (g x)) ∂particleHaar d N) :=
        by gcongr; exact particleHaar_lsi hg
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (2 / (4 * Real.pi ^ 2)) *
          ∫⁻ x, ENNReal.ofReal (particleTangentNormSq (g x))
            ∂(ENNReal.ofReal c⁻¹ • particleLaw A N)) :=
        by gcongr
    _ = ENNReal.ofReal (2 * particleEnergy A N f / (4 * Real.pi ^ 2 * c / C)) := by
        rw [lintegral_smul_measure, smul_eq_mul, hE, ← mul_assoc, ← mul_assoc,
          ← ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp


theorem torus_poincare {n : ℕ} {u : Torus n → ℝ} {g : Torus n → Tangent n}
    (h : IsWeakGradient u g) :
    4 * Real.pi ^ 2 * ProbabilityTheory.variance u (haar n) ≤ ∫ y, ‖g y‖ ^ 2 ∂haar n := by
  have hg := memLp_coord h.memLp_grad
  have hP := SharpLSI.poincare_torus h.isWeakGrad h.memLp hg
  have : ∫ y, ‖g y‖ ^ 2 ∂haar n = ∑ j, ∫ y, g y j ^ 2 ∂haar n := by
    rw [← integral_finsetSum _ fun j _ => (hg j).integrable_sq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  rw [this]
  exact hP


theorem variance_comp_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) {v : β → ℝ}
    (hv : MemLp v 2 ν) :
    ProbabilityTheory.variance (fun x => v (e x)) μ = ProbabilityTheory.variance v ν := by
  have h2 : MemLp (fun x => v (e x)) 2 μ := hv.comp_measurePreserving he
  rw [ProbabilityTheory.variance_eq_sub hv, ProbabilityTheory.variance_eq_sub h2]
  simp only [Pi.pow_apply]
  rw [he.integral_comp' (fun y => v y ^ 2), he.integral_comp' v]

theorem particleHaar_poincare {d : ℕ} {N : ℕ+} {f : ParticleSpace d N → ℝ}
    {g : ParticleSpace d N → Fin N → Tangent d} (hg : IsParticleHaarWeakGradient N f g) :
    4 * Real.pi ^ 2 * ProbabilityTheory.variance f (particleHaar d N) ≤
      ∫ x, particleTangentNormSq (g x) ∂particleHaar d N := by
  have h := torus_poincare (isWeakGradient_comp_ofT hg)
  have hp := (measurePreserving_toT (d := d) (N := N)).symm (torusEquiv d N)
  have e1 := variance_comp_equiv (torusEquiv d N).symm hp (v := f) hg.memLp
  have e2 := hp.integral_comp' (fun x => particleTangentNormSq (g x))
  simp only [torusEquiv_symm_apply] at e1 e2
  simp only [norm_sq_tangentL] at h
  rw [e1] at h
  rw [← e2]
  exact h


theorem variance_le_integral_sq_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : MemLp f 2 μ) (a : ℝ) :
    ProbabilityTheory.variance f μ ≤ ∫ x, (f x - a) ^ 2 ∂μ := by
  have h1 : Integrable f μ := hf.integrable one_le_two
  have h2 : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have e : ∫ x, (f x - a) ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ - 2 * a * ∫ x, f x ∂μ + a ^ 2 := by
    have : (fun x => (f x - a) ^ 2) = fun x => (f x ^ 2 - (2 * a) * f x) + a ^ 2 := by
      ext x; ring
    have h3 : Integrable (fun x => f x ^ 2 - 2 * a * f x) μ := h2.sub (h1.const_mul _)
    rw [this, integral_add h3 (integrable_const _), integral_sub h2 (h1.const_mul _),
      integral_const_mul]
    simp
  rw [e, ProbabilityTheory.variance_eq_sub hf]
  simp only [Pi.pow_apply]
  nlinarith [sq_nonneg (∫ x, f x ∂μ - a)]

/-- Positive Poincaré constant for the Gibbs law. -/
theorem particlePoincare_pos_aux {d : ℕ} (A : InteractionData d) (N : ℕ+) :
    ∃ r : ℝ, 0 < r ∧ ∀ f : ParticleH1 A N,
      r * ProbabilityTheory.variance f.1 (particleLaw A N) ≤ particleEnergy A N f := by
  obtain ⟨c, C, hc, hcC, hb⟩ := DGPS.Particle.particleDensity_bounded A N
  have hC : 0 < C := lt_of_lt_of_le hc hcC
  have hπ : 0 < 4 * Real.pi ^ 2 := by positivity
  refine ⟨4 * Real.pi ^ 2 * c / C, by positivity, fun f => ?_⟩
  have hgP := isParticleWeakGradient_particleWeakGradient f
  have hg := (isParticleWeakGradient_iff A N _ _).1 hgP
  set g := particleWeakGradient f with hgdef
  have hPprob := DGPS.Particle.particleLaw_isProbabilityMeasure' A N
  set a := ∫ x, f.1 x ∂particleHaar d N with ha
  have hfsq : Integrable (fun x => (f.1 x - a) ^ 2) (particleHaar d N) :=
    (hg.memLp.sub (memLp_const a)).integrable_sq
  have hgn : Integrable (fun x => particleTangentNormSq (g x)) (particleHaar d N) :=
    integrable_particleTangentNormSq hg.memLp_grad
  have hnn : ∀ x, 0 ≤ particleTangentNormSq (g x) :=
    fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have m1 := (integral_particleLaw_mono A N (fun x => sq_nonneg (f.1 x - a)) hfsq hb hc.le).2
  have m2 := (integral_particleLaw_mono A N hnn hgn hb hc.le).1
  have hvarm : ProbabilityTheory.variance f.1 (particleHaar d N) =
      ∫ x, (f.1 x - a) ^ 2 ∂particleHaar d N := by
    rw [ProbabilityTheory.variance_eq_integral hg.memLp.aestronglyMeasurable.aemeasurable]
  have hP := particleHaar_poincare hg
  have hv1 : ProbabilityTheory.variance f.1 (particleLaw A N) ≤
      ∫ x, (f.1 x - a) ^ 2 ∂particleLaw A N :=
    variance_le_integral_sq_sub (hgP.memLp) a
  have hE : particleEnergy A N f = ∫ x, particleTangentNormSq (g x) ∂particleLaw A N := rfl
  rw [hvarm] at hP
  rw [hE]
  have key : 4 * Real.pi ^ 2 * ProbabilityTheory.variance f.1 (particleLaw A N) ≤
      C / c * ∫ x, particleTangentNormSq (g x) ∂particleLaw A N := by
    calc _ ≤ 4 * Real.pi ^ 2 * ∫ x, (f.1 x - a) ^ 2 ∂particleLaw A N := by gcongr
      _ ≤ 4 * Real.pi ^ 2 * (C * ∫ x, (f.1 x - a) ^ 2 ∂particleHaar d N) := by gcongr
      _ = C * (4 * Real.pi ^ 2 * ∫ x, (f.1 x - a) ^ 2 ∂particleHaar d N) := by ring
      _ ≤ C * ∫ x, particleTangentNormSq (g x) ∂particleHaar d N := by gcongr
      _ ≤ C * (c⁻¹ * ∫ x, particleTangentNormSq (g x) ∂particleLaw A N) := by
          gcongr
          rw [inv_mul_eq_div, le_div_iff₀ hc]
          linarith
      _ = _ := by field_simp
  have : 4 * Real.pi ^ 2 * c / C * ProbabilityTheory.variance f.1 (particleLaw A N) =
      c / C * (4 * Real.pi ^ 2 * ProbabilityTheory.variance f.1 (particleLaw A N)) := by ring
  rw [this]
  calc _ ≤ c / C * (C / c * ∫ x, particleTangentNormSq (g x) ∂particleLaw A N) := by gcongr
    _ = _ := by field_simp


theorem particleLift_secT {d : ℕ} {N : ℕ+} (x : ParticleSpace d N) :
    particleLift (fun i => SharpLSI.secT (x i)) = x := by
  funext i; simp [particleLift, torusLift, SharpLSI.liftT_secT]

theorem particlePartial_mul {d : ℕ} {N : ℕ+} {φ ψ : ParticleSpace d N → ℝ}
    (hφ : IsSmoothPeriodicParticle φ) (hψ : IsSmoothPeriodicParticle ψ) (i : Fin N) (j : Fin d)
    (x : ParticleSpace d N) :
    particlePartial i j (fun y => φ y * ψ y) x =
      ψ x * particlePartial i j φ x + φ x * particlePartial i j ψ x := by
  unfold particlePartial
  have h : ((fun y => φ y * ψ y) ∘ particleLift) = (φ ∘ particleLift) * (ψ ∘ particleLift) := rfl
  rw [h, fderiv_mul' ((hφ.differentiable (by simp)) _) ((hψ.differentiable (by simp)) _)]
  simp [Function.comp_def, particleLift_secT]
  ring

/-- A smooth periodic function on the particle torus has the weak gradient given by its partial
derivatives. -/
theorem isParticleHaarWeakGradient_of_smooth {d : ℕ} {N : ℕ+} {φ : ParticleSpace d N → ℝ}
    (hφ : IsSmoothPeriodicParticle φ) :
    IsParticleHaarWeakGradient N φ
      (fun x i => WithLp.toLp 2 fun j => particlePartial i j φ x) := by
  refine ⟨hφ.memLp_top.mono_exponent le_top, ?_, ?_⟩
  · rw [memLp_pi_iff]
    intro i
    rw [memLp_piLp_iff]
    intro j
    exact (hφ.memLp_top_particlePartial i j).mono_exponent le_top
  · intro ψ hψ i j
    have h0 := linearization_integral_particlePartial
      (φ := fun y => φ y * ψ y) (hφ.mul hψ) i j
    have hp1 := integrable_mul_of_memLp_two_particle
      (hφ.memLp_top.mono_exponent le_top) (hψ.memLp_top_particlePartial i j)
    have hp2 := integrable_mul_of_memLp_two_particle
      (hψ.memLp_top.mono_exponent le_top) (hφ.memLp_top_particlePartial i j)
    simp_rw [particlePartial_mul hφ hψ] at h0
    rw [integral_add (hp2.congr (Filter.Eventually.of_forall fun x => by simp))
      hp1] at h0
    simp only [mul_comm (ψ _)] at h0
    linarith


/-- The bounded symmetric smooth witness `x ↦ ∑ᵢ Re e^{2πi x_{i,0}}`. -/
noncomputable def witnessSum {d : ℕ} (N : ℕ+) (hd : 0 < d) (x : ParticleSpace d N) : ℝ :=
  ∑ i, (fourier 1 (x i ⟨0, hd⟩ : UnitAddCircle)).re

theorem witnessSum_eq_mFourier {d : ℕ} {N : ℕ+} (hd : 0 < d) (x : ParticleSpace d N) :
    witnessSum N hd x = ∑ i, (UnitAddTorus.mFourier
      (Pi.single (i, (⟨0, hd⟩ : Fin d)) (1 : ℤ) : Fin N × Fin d → ℤ) (particleUncurry d N x)).re := by
  unfold witnessSum
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  rw [Finset.prod_eq_single (i, (⟨0, hd⟩ : Fin d))]
  · simp [particleUncurry_apply]
  · intro b _ hb
    simp [hb]
  · simp

theorem isSmooth_witnessSum {d : ℕ} {N : ℕ+} (hd : 0 < d) :
    IsSmoothPeriodicParticle (witnessSum N hd) := by
  have : witnessSum N hd = fun x => ∑ i, (UnitAddTorus.mFourier
      (Pi.single (i, (⟨0, hd⟩ : Fin d)) (1 : ℤ) : Fin N × Fin d → ℤ) (particleUncurry d N x)).re :=
    funext (witnessSum_eq_mFourier hd)
  rw [this]
  unfold IsSmoothPeriodicParticle
  have h := fun i : Fin N => isSmoothPeriodicParticle_re_mFourier (d := d) (N := N)
    (Pi.single (i, (⟨0, hd⟩ : Fin d)) (1 : ℤ))
  exact ContDiff.sum fun i _ => h i

theorem continuous_witnessSum {d : ℕ} {N : ℕ+} (hd : 0 < d) : Continuous (witnessSum N hd) := by
  unfold witnessSum
  refine continuous_finsetSum _ fun i _ => ?_
  exact Complex.continuous_re.comp ((map_continuous (fourier (T := 1) 1)).comp
    ((continuous_apply _).comp (continuous_apply i)))

theorem abs_witnessSum_le {d : ℕ} {N : ℕ+} (hd : 0 < d) (x : ParticleSpace d N) :
    |witnessSum N hd x| ≤ N := by
  unfold witnessSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i : Fin N, |(fourier 1 (x i ⟨0, hd⟩ : UnitAddCircle)).re| ≤ 1 := fun i =>
    (Complex.abs_re_le_norm _).trans (by simp)
  refine (Finset.sum_le_sum fun i _ => this i).trans ?_
  simp


theorem witnessSum_zero {d : ℕ} {N : ℕ+} (hd : 0 < d) :
    witnessSum N hd (fun _ _ => 0) = N := by
  simp [witnessSum]

theorem witnessSum_half {d : ℕ} {N : ℕ+} (hd : 0 < d) :
    witnessSum N hd (fun _ _ => ((1 / 2 : ℝ) : UnitAddCircle)) = -N := by
  unfold witnessSum
  have : ∀ i : Fin N, (fourier 1 (((1 / 2 : ℝ) : UnitAddCircle))).re = -1 := fun i => by
    rw [fourier_coe_apply]
    have : (2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) * ((1 / 2 : ℝ) : ℂ) / ((1 : ℝ) : ℂ)) =
        Real.pi * Complex.I := by push_cast; ring
    rw [this, Complex.exp_re]
    simp
  rw [Finset.sum_congr rfl (fun i _ => this i)]
  simp

theorem witnessSum_permute {d : ℕ} {N : ℕ+} (hd : 0 < d) (σ : Equiv.Perm (Fin N))
    (x : ParticleSpace d N) : witnessSum N hd (permuteParticles σ x) = witnessSum N hd x := by
  unfold witnessSum permuteParticles
  exact Equiv.sum_comp σ (fun i => (fourier 1 (x i ⟨0, hd⟩ : UnitAddCircle)).re)

theorem witnessSum_not_ae_const {d : ℕ} (A : InteractionData d) {N : ℕ+} (hd : 0 < d) (a : ℝ) :
    ¬ (witnessSum N hd =ᵐ[particleLaw A N] fun _ => a) := by
  intro h
  obtain ⟨c, C, hc, hcC, hb⟩ := DGPS.Particle.particleDensity_bounded A N
  have hle := particleHaar_le_smul A N hc fun x => (hb x).1
  have h' : witnessSum N hd =ᵐ[particleHaar d N] fun _ => a :=
    (Measure.absolutelyContinuous_of_le_smul hle).ae_le h
  have : (particleHaar d N).IsOpenPosMeasure := by unfold particleHaar; infer_instance
  have h2 := (Continuous.ae_eq_iff_eq (particleHaar d N) (continuous_witnessSum hd)
    continuous_const).1 h'
  have e0 := congrFun h2 (fun _ _ => 0)
  have e1 := congrFun h2 (fun _ _ => ((1 / 2 : ℝ) : UnitAddCircle))
  rw [witnessSum_zero] at e0
  rw [witnessSum_half] at e1
  have : (0 : ℝ) < N := by exact_mod_cast N.pos
  linarith


/-- A bounded, mean-zero, permutation-invariant test of positive variance. -/
theorem exists_witness {d : ℕ} (A : InteractionData d) (N : ℕ+) (hd : 0 < d) :
    ∃ F : ParticleH1 A N, (∃ M : ℝ, ∀ x, |F x| ≤ M) ∧ ∫ x, F x ∂particleLaw A N = 0 ∧
      0 < ProbabilityTheory.variance F.1 (particleLaw A N) ∧ IsSymmetricParticleTest F := by
  have hP := DGPS.Particle.particleLaw_isProbabilityMeasure' A N
  have hG := isParticleHaarWeakGradient_of_smooth (isSmooth_witnessSum (d := d) (N := N) hd)
  set a := ∫ x, witnessSum N hd x ∂particleLaw A N with ha
  have hmem : MemParticleH1 A N (fun x => witnessSum N hd x - a) := by
    have := hG.affine 1 (-a)
    simp only [one_mul, ← sub_eq_add_neg] at this
    exact (memParticleH1_iff A N _).2 ⟨_, this⟩
  refine ⟨⟨_, hmem⟩, ⟨N + |a|, fun x => ?_⟩, ?_, ?_, ?_⟩
  · calc |witnessSum N hd x - a| ≤ |witnessSum N hd x| + |a| := abs_sub _ _
      _ ≤ N + |a| := by gcongr; exact abs_witnessSum_le hd x
  · have hint : Integrable (witnessSum N hd) (particleLaw A N) :=
      (continuous_witnessSum hd).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    show ∫ x, (witnessSum N hd x - a) ∂particleLaw A N = 0
    rw [integral_sub hint (integrable_const _)]
    simp [ha]
  · have hmL : MemLp (witnessSum N hd) 2 (particleLaw A N) :=
      (DGPS.Particle.memLp_particleLaw_iff A N).2 hG.memLp
    show 0 < ProbabilityTheory.variance (fun x => witnessSum N hd x - a) (particleLaw A N)
    have hv : ProbabilityTheory.variance (fun x => witnessSum N hd x - a) (particleLaw A N) =
        ProbabilityTheory.variance (witnessSum N hd) (particleLaw A N) :=
      ProbabilityTheory.variance_sub_const hmL.aestronglyMeasurable a
    rw [hv]
    refine lt_of_le_of_ne (ProbabilityTheory.variance_nonneg _ _) fun h0 => ?_
    exact witnessSum_not_ae_const A hd _ (ProbabilityTheory.ae_eq_integral_of_variance_eq_zero hmL h0.symm)
  · rw [isSymmetricParticleTest_iff (⟨_, hmem⟩ : ParticleH1 A N)]
    intro σ
    refine Filter.Eventually.of_forall fun x => ?_
    show witnessSum N hd (permuteParticles σ x) - a = witnessSum N hd x - a
    rw [witnessSum_permute]


end DGPS.FiniteN.PositiveRate

namespace DGPS

/-- The ordinary Poincare quotient `E_N(f) / Var_{P_N}(f)` in `ℝ≥0∞`. -/
noncomputable def particlePoincareQuotient {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (f : ParticleH1 A N) : ℝ≥0∞ :=
  ENNReal.ofReal (particleEnergy A N f) /
    ENNReal.ofReal (ProbabilityTheory.variance f.1 (particleLaw A N))

/-- SETUP-T13: the unrestricted ordinary Poincare rate
`λ_N = inf_{f ∈ H¹(P_N), Var_{P_N}(f) > 0} E_N(f) / Var_{P_N}(f)` (no symmetry restriction). -/
noncomputable def particlePoincareRate {d : ℕ} (A : InteractionData d) (N : ℕ+) : ℝ≥0∞ :=
  ⨅ f : {f : ParticleH1 A N // 0 < ProbabilityTheory.variance f.1 (particleLaw A N)},
    particlePoincareQuotient A N f.1

theorem particlePoincareRate_le_quotient {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (f : ParticleH1 A N) (hf : 0 < ProbabilityTheory.variance f.1 (particleLaw A N)) :
    particlePoincareRate A N ≤ particlePoincareQuotient A N f :=
  iInf_le (fun g : {f : ParticleH1 A N // 0 < ProbabilityTheory.variance f.1 (particleLaw A N)} =>
    particlePoincareQuotient A N g.1) ⟨f, hf⟩

theorem le_particlePoincareRate_iff_forall {d : ℕ} (A : InteractionData d) (N : ℕ+) (r : ℝ) :
    ENNReal.ofReal r ≤ particlePoincareRate A N ↔
      ∀ f : ParticleH1 A N, 0 < ProbabilityTheory.variance f.1 (particleLaw A N) →
        r * ProbabilityTheory.variance f.1 (particleLaw A N) ≤ particleEnergy A N f := by
  unfold particlePoincareRate
  rw [le_iInf_iff]
  constructor
  · intro h f hf
    have h1 := h ⟨f, hf⟩
    unfold particlePoincareQuotient at h1
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hf)) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul'  (ProbabilityTheory.variance_nonneg _ _)] at h1
    by_cases hr : 0 ≤ r
    · have hE := particleEnergy_nonneg f
      exact (ENNReal.ofReal_le_ofReal_iff hE).1 h1
    · have := mul_neg_of_neg_of_pos (not_le.1 hr) hf
      exact this.le.trans (particleEnergy_nonneg f)
  · intro h f
    unfold particlePoincareQuotient
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using f.2)) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul' (ProbabilityTheory.variance_nonneg _ _)]
    exact ENNReal.ofReal_le_ofReal (h f.1 f.2)

end DGPS

namespace DGPS.FiniteN

open DGPS MeasureTheory

/-- `Θ_p(a)`: eventual two-sided polynomial bound `c N^(-p) ≤ a_N ≤ C N^(-p)`. -/
def ThetaScale (p : ℝ) (a : ℕ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    c * (N : ℝ) ^ (-p) ≤ a N ∧ a N ≤ C * (N : ℝ) ^ (-p)

/-- `Arr_B(a)`: Arrhenius scale `log(a_N) / N → -B`. -/
def ArrheniusScale (B : ℝ) (a : ℕ → ℝ) : Prop :=
  Filter.Tendsto (fun N : ℕ => Real.log (a N) / (N : ℝ)) Filter.atTop (nhds (-B))

/-- Finiteness and positivity of the three finite-`N` rates, and the real bridge. -/
theorem rates_pos_lt_top {d : ℕ} (A : InteractionData d) (N : ℕ+) (hd : 0 < d) :
    (0 < particleRateAll A N ∧ particleRateAll A N < ⊤) ∧
    (0 < particleRateSym A N ∧ particleRateSym A N < ⊤) ∧
    (0 < particlePoincareRate A N ∧ particlePoincareRate A N < ⊤) := by
  obtain ⟨F, ⟨M, hM⟩, hmean, hvar, hsym⟩ := PositiveRate.exists_witness A N hd
  have hP := DGPS.Particle.particleLaw_isProbabilityMeasure' A N
  have hFm : AEMeasurable F.1 (particleLaw A N) :=
    (F.2.choose_spec.memLp).aestronglyMeasurable.aemeasurable
  have hint : ∫ x, F x ^ 2 ∂particleLaw A N = ProbabilityTheory.variance F.1 (particleLaw A N) := by
    rw [ProbabilityTheory.variance_of_integral_eq_zero hFm hmean]
  have hV : 0 < ∫ x, F x ^ 2 ∂particleLaw A N := by rw [hint]; exact hvar
  obtain ⟨hall, hsymle⟩ := linearization_rate_le F hM hmean hV
  have hsy := hsymle hsym
  obtain ⟨r1, hr1, h1⟩ := PositiveRate.particleRateAll_pos_aux A N
  obtain ⟨r2, hr2, h2⟩ := PositiveRate.particlePoincare_pos_aux A N
  have h2' : ENNReal.ofReal r2 ≤ particlePoincareRate A N :=
    (le_particlePoincareRate_iff_forall A N r2).2 fun f _ => h2 f
  have hpos1 : 0 < ENNReal.ofReal r1 := ENNReal.ofReal_pos.2 hr1
  have hpos2 : 0 < ENNReal.ofReal r2 := ENNReal.ofReal_pos.2 hr2
  have hpq : particlePoincareRate A N ≤ particlePoincareQuotient A N F :=
    particlePoincareRate_le_quotient A N F hvar
  have hq : particlePoincareQuotient A N F < ⊤ := by
    unfold particlePoincareQuotient
    exact ENNReal.div_lt_top ENNReal.ofReal_ne_top (by simpa using hvar)
  refine ⟨⟨hpos1.trans_le h1, lt_of_le_of_lt hall ENNReal.ofReal_lt_top⟩,
    ⟨hpos1.trans_le (h1.trans (particleRateAll_le_sym A N)),
      lt_of_le_of_lt hsy ENNReal.ofReal_lt_top⟩,
    ⟨hpos2.trans_le h2', lt_of_le_of_lt hpq hq⟩⟩

/-- Real bridge: for `R ∈ (0,∞)`, `ofReal r ≤ R ↔ r ≤ R.toReal` and `ofReal R.toReal = R`. -/
theorem toReal_bridge {R : ℝ≥0∞} (h0 : 0 < R) (hT : R < ⊤) :
    0 < R.toReal ∧ ENNReal.ofReal R.toReal = R ∧
      ∀ r : ℝ, ENNReal.ofReal r ≤ R ↔ r ≤ R.toReal := by
  refine ⟨ENNReal.toReal_pos h0.ne' hT.ne, ENNReal.ofReal_toReal hT.ne, fun r => ?_⟩
  exact ENNReal.ofReal_le_iff_le_toReal hT.ne

/-- FIN001: finite positive particle rate and real bridge. For `0 < d` and every `N ≥ 1`:
the Gibbs density is strictly positive and bounded above and below; the rates
`r_N^all`, `r_N^sym`, `λ_N` lie in `(0,∞)`; their real parts are positive, preserve the
order `r^all ≤ r^sym`, and convert `ofReal`-inequalities to real inequalities. -/
theorem finite_positive_particle_rate_and_real_bridge {d : ℕ} (A : InteractionData d)
    (hd : 0 < d) (N : ℕ+) :
    (∀ x, 0 < particleDensity A N x) ∧
    (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ x, c ≤ particleDensity A N x ∧
        particleDensity A N x ≤ C) ∧
    (0 < particleRateAll A N ∧ particleRateAll A N < ⊤) ∧
    (0 < particleRateSym A N ∧ particleRateSym A N < ⊤) ∧
    (0 < particlePoincareRate A N ∧ particlePoincareRate A N < ⊤) ∧
    (0 < (particleRateAll A N).toReal ∧ 0 < (particleRateSym A N).toReal ∧
      0 < (particlePoincareRate A N).toReal) ∧
    ENNReal.ofReal (particleRateAll A N).toReal = particleRateAll A N ∧
    ENNReal.ofReal (particleRateSym A N).toReal = particleRateSym A N ∧
    ENNReal.ofReal (particlePoincareRate A N).toReal = particlePoincareRate A N ∧
    (particleRateAll A N).toReal ≤ (particleRateSym A N).toReal ∧
    (∀ r : ℝ, ENNReal.ofReal r ≤ particleRateAll A N ↔ r ≤ (particleRateAll A N).toReal) ∧
    (∀ r : ℝ, ENNReal.ofReal r ≤ particleRateSym A N ↔ r ≤ (particleRateSym A N).toReal) ∧
    (∀ r : ℝ, ENNReal.ofReal r ≤ particlePoincareRate A N ↔
      r ≤ (particlePoincareRate A N).toReal) := by
  obtain ⟨⟨a0, aT⟩, ⟨s0, sT⟩, ⟨p0, pT⟩⟩ := rates_pos_lt_top A N hd
  obtain ⟨a1, a2, a3⟩ := toReal_bridge a0 aT
  obtain ⟨s1, s2, s3⟩ := toReal_bridge s0 sT
  obtain ⟨p1, p2, p3⟩ := toReal_bridge p0 pT
  exact ⟨DGPS.Particle.particleDensity_pos A N, DGPS.Particle.particleDensity_bounded A N,
    ⟨a0, aT⟩, ⟨s0, sT⟩, ⟨p0, pT⟩, ⟨a1, s1, p1⟩, a2, s2, p2,
    ENNReal.toReal_mono sT.ne (particleRateAll_le_sym A N), a3, s3, p3⟩

end DGPS.FiniteN
