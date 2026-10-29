import DGPS.Model.ScalarRate
import DGPS.Analysis.CircleLSI
import DGPS.Particle.RateEquivalences
import DGPS.Particle.Contractions

/-!
# Free-model and `N = 1` normalization tests (DEF032)

* `DGPS.freeModel_normalization`: for `V = W = 0` the minimum free energy is `0`, the gap is the
  relative entropy `H(ρ|m)`, the dissipation is `4 ∫ |∇√ρ|²` (for every weak-drift provider) and
  the quotient `D/(2G)` equals `2 ∫ |∇√ρ|² / Ent(ρ)`.
* `DGPS.particle_one_zeroDiagonal`: for `N = 1` the Hamiltonian is `V` (the zero diagonal kills
  `W`), `P_1 ∝ e^{-V} m`, and `P_1 = m` when `V = 0`.
* `DGPS.circle_free_rates`: on the circle the scalar free-model rate and the `N = 1` particle
  rates `r_1^all`, `r_1^sym` all equal `a0 = 4π²`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS

section FreeModel

variable {d : ℕ}

theorem freeEnergy_zero_data (ν : ProbabilityMeasure (Torus d)) :
    freeEnergy (InteractionData.zero d) ν =
      ((relativeEntropy (ν : Measure (Torus d)) (haar d) : ℝ≥0∞) : EReal) := by
  simp [freeEnergy, potentialEnergy, interactionEnergy, InteractionData.zero]

theorem freeEnergyMinimumReal_zero_data : freeEnergyMinimumReal (InteractionData.zero d) = 0 := by
  have h : freeEnergyMinimum (InteractionData.zero d) = ((0 : ℝ) : EReal) := by
    refine le_antisymm ?_ ?_
    · refine (iInf_le _ (haarProbability d)).trans ?_
      rw [freeEnergy_zero_data]
      show ((relativeEntropy (haar d) (haar d) : ℝ≥0∞) : EReal) ≤ _
      rw [relativeEntropy_self]; simp
    · refine le_iInf fun ν => ?_
      rw [freeEnergy_zero_data]
      simpa using EReal.coe_ennreal_nonneg (relativeEntropy (ν : Measure (Torus d)) (haar d))
  rw [freeEnergyMinimumReal, h]; rfl

theorem relativeEntropy_density_eq (ρ : AbsoluteDensity d) :
    relativeEntropy (densityMeasure ρ) (haar d) = homogeneousEntropy (haar d) ρ.density :=
  relativeEntropy_withDensity (Filter.Eventually.of_forall ρ.density_nonneg)
    ρ.integrable_density.aestronglyMeasurable.aemeasurable

/-- **Free-model normalization** (DEF032): for `V = W = 0`, `F_* = 0`, the gap is `H(ρ|m)`, the
dissipation is `4 ∫ |∇√ρ|²` and `D/(2G) = 2 ∫ |∇√ρ|² / Ent(ρ)`, for every weak-drift provider. -/
theorem freeModel_normalization (b : AbsoluteDrift (InteractionData.zero d))
    (ρ : AbsoluteDensity d) :
    freeEnergyMinimumReal (InteractionData.zero d) = 0 ∧
    ((scalarGap (InteractionData.zero d) ρ : ℝ≥0) : ℝ≥0∞) =
      relativeEntropy (densityMeasure ρ) (haar d) ∧
    relativeEntropy (densityMeasure ρ) (haar d) = homogeneousEntropy (haar d) ρ.density ∧
    scalarDissipation (InteractionData.zero d) b ρ =
      4 * ∫⁻ x, ENNReal.ofReal (‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2) ∂haar d ∧
    scalarQuotient (InteractionData.zero d) b ρ =
      2 * (∫⁻ x, ENNReal.ofReal (‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2) ∂haar d) /
        homogeneousEntropy (haar d) ρ.density := by
  have hfin : relativeEntropy (densityMeasure ρ) (haar d) ≠ ⊤ :=
    (absoluteDensity_entropy_finite ρ).2.2.1
  have hgap : ((scalarGap (InteractionData.zero d) ρ : ℝ≥0) : ℝ≥0∞) =
      relativeEntropy (densityMeasure ρ) (haar d) := by
    have h1 : ((scalarGap (InteractionData.zero d) ρ : ℝ≥0) : ℝ) =
        (relativeEntropy (densityMeasure ρ) (haar d)).toReal := by
      rw [coe_scalarGap, freeEnergyMinimumReal_zero_data, sub_zero]
      have h2 : ((densityFreeEnergy (InteractionData.zero d) ρ : ℝ) : EReal) =
          ((relativeEntropy (densityMeasure ρ) (haar d) : ℝ≥0∞) : EReal) := by
        rw [coe_densityFreeEnergy, freeEnergy_zero_data]
      rw [← EReal.toReal_coe (densityFreeEnergy (InteractionData.zero d) ρ), h2]
      simp
    rw [← ENNReal.ofReal_coe_nnreal, h1, ENNReal.ofReal_toReal hfin]
  have hD : scalarDissipation (InteractionData.zero d) b ρ =
      4 * ∫⁻ x, ENNReal.ofReal (‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2) ∂haar d := by
    have hz := absoluteDrift_unique b (AbsoluteDrift.zero d) ρ
    unfold scalarDissipation
    have : (∫⁻ x, ENNReal.ofReal (‖scalarScore (InteractionData.zero d) b ρ x‖ ^ 2) ∂haar d) =
        ∫⁻ x, 4 * ENNReal.ofReal (‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2) ∂haar d := by
      refine lintegral_congr_ae ?_
      filter_upwards [hz] with x hx
      have hx' : b.force ρ x = 0 := hx
      have : scalarScore (InteractionData.zero d) b ρ x =
          (2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x := by
        simp [scalarScore, hx']
      rw [this, norm_smul, mul_pow, Real.norm_two, ENNReal.ofReal_mul (by norm_num)]
      norm_num
    rw [this, lintegral_const_mul' _ _ (by simp)]
  refine ⟨freeEnergyMinimumReal_zero_data, hgap, relativeEntropy_density_eq ρ, hD, ?_⟩
  unfold scalarQuotient
  rw [hD, hgap, relativeEntropy_density_eq ρ]
  have : (4 : ℝ≥0∞) * (∫⁻ x, ENNReal.ofReal (‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2) ∂haar d) =
      2 * (2 * ∫⁻ x, ENNReal.ofReal (‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2) ∂haar d) := by
    rw [← mul_assoc]; norm_num
  rw [this, ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

end FreeModel

section ParticleOne

variable {d : ℕ}

/-- **`N = 1` normalization** (DEF032): the Hamiltonian is `V` (zero diagonal), the Gibbs density
is `e^{-V}/∫ e^{-V} dm`, and `P_1 = m` when `V = 0`. -/
theorem particle_one_zeroDiagonal (A : InteractionData d) :
    (∀ x : ParticleSpace d 1, particleHamiltonian A 1 x = A.V (x 0)) ∧
    particlePartition A 1 = ∫ y, Real.exp (-A.V y) ∂haar d ∧
    (∀ x : ParticleSpace d 1,
      particleDensity A 1 x = (∫ y, Real.exp (-A.V y) ∂haar d)⁻¹ * Real.exp (-A.V (x 0))) ∧
    ((∀ y, A.V y = 0) → particleLaw A 1 = particleHaar d 1) := by
  have hH : ∀ x : ParticleSpace d 1, particleHamiltonian A 1 x = A.V (x 0) := by
    intro x
    have s1 : ∀ f : Fin ((1 : ℕ+) : ℕ) → ℝ, ∑ i, f i = f 0 := fun f => Fin.sum_univ_one f
    unfold particleHamiltonian
    rw [s1 (fun i => A.V (x i)), s1 (fun i => ∑ j, A.W (x i) (x j)),
      s1 (fun j => A.W (x 0) (x j)), A.W_diag]
    simp
  have hZ : particlePartition A 1 = ∫ y, Real.exp (-A.V y) ∂haar d := by
    have hm := (measurePreserving_eval (fun _ : Fin ((1 : ℕ+) : ℕ) => haar d) 0).map_eq
    unfold particlePartition particleHaar
    simp_rw [hH]
    have hf : AEStronglyMeasurable (fun y : Torus d => Real.exp (-A.V y))
        (Measure.map (fun f : Fin ((1 : ℕ+) : ℕ) → Torus d => f 0)
          (Measure.pi fun _ => haar d)) :=
      (Real.continuous_exp.comp A.V_continuous.neg).aestronglyMeasurable
    have h2 := integral_map (μ := Measure.pi fun _ : Fin ((1 : ℕ+) : ℕ) => haar d)
      (φ := fun f : Fin ((1 : ℕ+) : ℕ) → Torus d => f 0) (measurable_pi_apply 0).aemeasurable hf
    rw [hm] at h2
    exact h2.symm
  refine ⟨hH, hZ, fun x => by simp [particleDensity, hZ, hH], fun hV => ?_⟩
  have hH0 : ∀ x : ParticleSpace d 1, particleHamiltonian A 1 x = 0 := fun x => by
    rw [hH, hV]
  have hZ0 : particlePartition A 1 = 1 := by
    simp [particlePartition, hH0]
  unfold particleLaw
  have : (fun x => ENNReal.ofReal (particleDensity A 1 x)) = fun _ => 1 := by
    funext x; simp [particleDensity, hZ0, hH0]
  rw [this]; exact withDensity_one

end ParticleOne

section ParticleTorus

variable {d : ℕ} {N : ℕ+}

theorem particleTangentNormSq_eq_norm_gradT (g : ParticleSpace d N → Fin N → Tangent d)
    (x : ParticleSpace d N) :
    particleTangentNormSq (g x) = ‖particleGradT g (particleTorusEquiv d N x)‖ ^ 2 := by
  rw [tangent_norm_sq, particleTangentNormSq_eq]
  simp only [particleGradT_apply, MeasurableEquiv.symm_apply_apply]
  rw [Equiv.sum_comp (particleIdx d N).symm (fun p : Fin N × Fin d => g x p.1 p.2 ^ 2),
    Fintype.sum_prod_type]

/-- On the free model the Gibbs energy is the `𝕋^{Nd}` Dirichlet energy of the transported
gradient. -/
theorem ofReal_particleEnergy_zero (f : ParticleH1 (InteractionData.zero d) N)
    {g : ParticleSpace d N → Fin N → Tangent d} (hg : IsParticleHaarWeakGradient N f.1 g) :
    ENNReal.ofReal (particleEnergy (InteractionData.zero d) N f) =
      ∫⁻ z, ENNReal.ofReal (‖particleGradT g z‖ ^ 2) ∂haar ((N : ℕ) * d) := by
  have hint : Integrable (fun z => ‖particleGradT g z‖ ^ 2) (haar ((N : ℕ) * d)) :=
    ((memLp_particleGradT_iff).2 hg.memLp_grad).norm.integrable_sq
  have hE : particleEnergy (InteractionData.zero d) N f =
      ∫ z, ‖particleGradT g z‖ ^ 2 ∂haar ((N : ℕ) * d) := by
    rw [particleEnergy_eq_of_isParticleWeakGradient f
      ((isParticleWeakGradient_iff _ N _ _).2 hg), DGPS.Particle.particleLaw_zero]
    simp_rw [particleTangentNormSq_eq_norm_gradT]
    exact (measurePreserving_particleTorusEquiv d N).integral_comp'
      (fun z => ‖particleGradT g z‖ ^ 2)
  rw [hE]
  exact ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun z => sq_nonneg _)

theorem particleEntropy_zero_eq (f : ParticleH1 (InteractionData.zero d) N) :
    particleEntropy (InteractionData.zero d) N f =
      homogeneousEntropy (haar ((N : ℕ) * d))
        (fun z => (f.1 ∘ (particleTorusEquiv d N).symm) z ^ 2) := by
  have hg : IsParticleHaarWeakGradient N f.1 (particleWeakGradient f) :=
    (isParticleWeakGradient_iff _ N _ _).1 (isParticleWeakGradient_particleWeakGradient f)
  have hgT := (isParticleHaarWeakGradient_iff_weakGradient).1 hg
  have hv : AEStronglyMeasurable (fun z => (f.1 ∘ (particleTorusEquiv d N).symm) z ^ 2)
      (haar ((N : ℕ) * d)) := hgT.memLp.integrable_sq.aestronglyMeasurable
  have := Analysis.homogeneousEntropy_comp_measurePreserving
    (measurePreserving_particleTorusEquiv d N) hv
  unfold particleEntropy
  rw [DGPS.Particle.particleLaw_zero]
  simpa [Function.comp_def] using this

/-- The Haar LSI on `𝕋^{Nd}` gives the free-model particle LSI. -/
theorem particleLSI_of_haarLSI_zero {a : ℝ} (ha : 0 < a) (H : Analysis.HaarLSI ((N : ℕ) * d) a)
    (f : ParticleH1 (InteractionData.zero d) N) :
    particleEntropy (InteractionData.zero d) N f ≤
      ENNReal.ofReal (2 * particleEnergy (InteractionData.zero d) N f / a) := by
  have hg : IsParticleHaarWeakGradient N f.1 (particleWeakGradient f) :=
    (isParticleWeakGradient_iff _ N _ _).1 (isParticleWeakGradient_particleWeakGradient f)
  have h := H _ _ ((isParticleHaarWeakGradient_iff_weakGradient).1 hg)
  rw [particleEntropy_zero_eq]
  refine h.trans (le_of_eq ?_)
  rw [show 2 * particleEnergy (InteractionData.zero d) N f / a =
      2 / a * particleEnergy (InteractionData.zero d) N f by ring,
    ENNReal.ofReal_mul (by positivity), ofReal_particleEnergy_zero f hg]

/-- Conversely, for `N = 1` the symmetric free-model particle LSI at rate `a` gives the Haar LSI
on `𝕋^{d}` at rate `a`. -/
theorem haarLSI_of_particleLSI_one {a : ℝ} (ha : 0 < a)
    (H : ∀ f : ParticleH1 (InteractionData.zero d) 1, IsSymmetricParticleTest f →
      particleEntropy (InteractionData.zero d) 1 f ≤
        ENNReal.ofReal (2 * particleEnergy (InteractionData.zero d) 1 f / a)) :
    Analysis.HaarLSI (((1 : ℕ+) : ℕ) * d) a := by
  intro f' g' hg'
  let e := particleTorusEquiv d 1
  let f : ParticleSpace d 1 → ℝ := f' ∘ e
  let g : ParticleSpace d 1 → Fin (((1 : ℕ+) : ℕ)) → Tangent d := fun x i =>
    WithLp.toLp 2 fun j => g' (e x) (particleIdx d 1 (i, j))
  have hgT : particleGradT g = g' := by
    funext z
    ext k
    show particleGradT g z k = g' z k
    rw [particleGradT_apply]
    simp only [g, e, MeasurableEquiv.apply_symm_apply, Prod.mk.eta, Equiv.apply_symm_apply]
  have hff : f ∘ e.symm = f' := by
    funext z
    show f' (e (e.symm z)) = f' z
    rw [MeasurableEquiv.apply_symm_apply]
  have hgrad : IsParticleHaarWeakGradient 1 f g := by
    refine (isParticleHaarWeakGradient_iff_weakGradient).2 ?_
    rw [hff, hgT]
    exact hg'
  have hmem : MemParticleH1 (InteractionData.zero d) 1 f :=
    (memParticleH1_iff _ _ _).2 ⟨g, hgrad⟩
  let F : ParticleH1 (InteractionData.zero d) 1 := ⟨f, hmem⟩
  have hsym : IsSymmetricParticleTest F := fun σ => by
    have hσ : σ = 1 := Equiv.ext fun i => Fin.ext (by
      have h1 := i.2
      have h2 := (σ i).2
      have h3 : ((1 : ℕ+) : ℕ) = 1 := rfl
      show (σ i : ℕ) = (i : ℕ)
      omega)
    rw [hσ]
    exact Filter.EventuallyEq.rfl
  have h := H F hsym
  rw [particleEntropy_zero_eq] at h
  have hF : F.1 ∘ e.symm = f' := hff
  rw [hF] at h
  refine h.trans (le_of_eq ?_)
  rw [show 2 * particleEnergy (InteractionData.zero d) 1 F / a =
      2 / a * particleEnergy (InteractionData.zero d) 1 F by ring,
    ENNReal.ofReal_mul (by positivity), ofReal_particleEnergy_zero F hgrad, hgT]

end ParticleTorus

section CircleRates

theorem scalar_quotient_iff (ρ : AbsoluteDensity 1)
    (hpos : 0 < homogeneousEntropy (haar 1) ρ.density) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal r ≤
        2 * (∫⁻ x, ENNReal.ofReal (‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2) ∂haar 1) /
          homogeneousEntropy (haar 1) ρ.density ↔
      2 * r * Analysis.circleEntropy ρ ≤ Analysis.circleFisherInformation ρ := by
  obtain ⟨hH, hint, -⟩ := haar_circle_lsi ρ
  rw [ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl hH)]
  have hL : ∫⁻ x, ENNReal.ofReal (‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2) ∂haar 1 =
      ENNReal.ofReal (∫ x, ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 ∂haar 1) :=
    (ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
  have hJ : 0 ≤ ∫ x, ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 ∂haar 1 :=
    integral_nonneg fun x => sq_nonneg _
  have hE : homogeneousEntropy (haar 1) ρ.density = ENNReal.ofReal (Analysis.circleEntropy ρ) := by
    unfold Analysis.circleEntropy
    rw [ENNReal.ofReal_toReal hH]
  have hC : 0 ≤ Analysis.circleEntropy ρ := ENNReal.toReal_nonneg
  have h2 : ∀ J : ℝ, (2 : ℝ≥0∞) * ENNReal.ofReal J = ENNReal.ofReal (2 * J) := fun J => by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  rw [hL, hE, ← ENNReal.ofReal_mul hr, h2, ENNReal.ofReal_le_ofReal_iff (by positivity)]
  unfold Analysis.circleFisherInformation
  constructor <;> intro h <;> linarith

/-- **Circle free rates** (DEF032): on the circle, the scalar free-model rate and the `N = 1`
free-model particle rates all equal `a0 = 4π²`. -/
theorem circle_free_rates (b : AbsoluteDrift (InteractionData.zero 1)) :
    scalarRate (InteractionData.zero 1) b = ENNReal.ofReal (4 * Real.pi ^ 2) ∧
    particleRateAll (InteractionData.zero 1) 1 = ENNReal.ofReal (4 * Real.pi ^ 2) ∧
    particleRateSym (InteractionData.zero 1) 1 = ENNReal.ofReal (4 * Real.pi ^ 2) := by
  have ha0 : (0 : ℝ) < 4 * Real.pi ^ 2 := by positivity
  have hd : 0 < ((1 : ℕ+) : ℕ) * 1 := by norm_num
  -- the positive-entropy reformulation of the scalar gap
  have hgapE : ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (InteractionData.zero 1) ρ ↔
      0 < homogeneousEntropy (haar 1) ρ.density := by
    intro ρ
    obtain ⟨-, hgap, hrel, -, -⟩ := freeModel_normalization b ρ
    rw [← ENNReal.coe_pos, hgap, hrel]
  have hquot : ∀ ρ : AbsoluteDensity 1, scalarQuotient (InteractionData.zero 1) b ρ =
      2 * (∫⁻ x, ENNReal.ofReal (‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2) ∂haar 1) /
        homogeneousEntropy (haar 1) ρ.density := fun ρ =>
    (freeModel_normalization b ρ).2.2.2.2
  -- scalar rate
  have hscal_lo : ENNReal.ofReal (4 * Real.pi ^ 2) ≤ scalarRate (InteractionData.zero 1) b := by
    refine le_iInf fun ρ => ?_
    rw [hquot, scalar_quotient_iff ρ.1 ((hgapE ρ.1).1 ρ.2) ha0.le]
    exact (haar_circle_lsi ρ.1).2.2
  have hscal_hi : scalarRate (InteractionData.zero 1) b ≤ ENNReal.ofReal (4 * Real.pi ^ 2) := by
    by_contra hlt
    obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 (not_le.1 hlt)
    obtain ⟨hra, hrpos⟩ := (ENNReal.ofReal_lt_ofReal_iff').1 hr1
    refine absurd (haar_circle_lsi_sharp (a := r) fun ρ => ?_) (not_le.2 hra)
    by_cases hz : 0 < homogeneousEntropy (haar 1) ρ.density
    · have hq := scalarRate_le_quotient (InteractionData.zero 1) b ρ ((hgapE ρ).2 hz)
      rw [hquot] at hq
      exact (scalar_quotient_iff ρ hz hr0).1 ((hr2.le).trans hq)
    · have h0 : homogeneousEntropy (haar 1) ρ.density = 0 := nonpos_iff_eq_zero.1 (not_lt.1 hz)
      have hent : Analysis.circleEntropy ρ = 0 := by
        unfold Analysis.circleEntropy; rw [h0]; simp
      rw [hent]
      unfold Analysis.circleFisherInformation
      have : 0 ≤ ∫ x, ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 ∂haar 1 :=
        integral_nonneg fun x => sq_nonneg _
      linarith
  -- particle rates
  have hall_lo : ENNReal.ofReal (4 * Real.pi ^ 2) ≤ particleRateAll (InteractionData.zero 1) 1 :=
    (particleRate_iff_lsi _ _ ha0).1
      (fun f => particleLSI_of_haarLSI_zero ha0 (haar_torus_lsi _) f)
  have hsym_hi : particleRateSym (InteractionData.zero 1) 1 ≤ ENNReal.ofReal (4 * Real.pi ^ 2) := by
    by_contra hlt
    obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 (not_le.1 hlt)
    obtain ⟨hra, hrpos⟩ := (ENNReal.ofReal_lt_ofReal_iff').1 hr1
    have hL := haarLSI_of_particleLSI_one hrpos
      ((particleRateSym_iff_lsi _ _ hrpos).2 hr2.le)
    exact absurd ((haar_lsi_sharp hd).2.1 r hL) (not_le.2 hra)
  have hle := particleRateAll_le_sym (InteractionData.zero 1) 1
  exact ⟨le_antisymm hscal_hi hscal_lo, le_antisymm (hle.trans hsym_hi) hall_lo,
    le_antisymm hsym_hi (hall_lo.trans hle)⟩

end CircleRates

end DGPS
