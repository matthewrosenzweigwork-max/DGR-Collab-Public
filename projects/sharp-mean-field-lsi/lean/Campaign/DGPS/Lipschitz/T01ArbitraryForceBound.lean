import DGPS.Lipschitz.T01ReferenceData
import DGPS.Lipschitz.T01SpectralBridge
import DGPS.Particle.CenteredForceExponential

/-!
# Actual centered-force bounds under arbitrary laws

The product exponential moment and reference entropy comparison imply the force estimate
used by defective absorption. The comparison law need not be symmetric. Its relative entropy
is required to be finite before taking its real value.
-/

open MeasureTheory InformationTheory Filter
open scoped ENNReal

namespace DGPS.Lipschitz

open KernelApproximation CenteredForceExponential

/-- Entropy duality for a bounded nonnegative observable, in the exact real form needed
for the centered force. Boundedness is allowed to depend on the fixed particle number. -/
theorem t01_integral_le_entropy_of_exponential {Ω : Type*} [MeasurableSpace Ω]
    (Q ν : Measure Ω) [IsProbabilityMeasure Q] [IsProbabilityMeasure ν]
    {F : Ω → ℝ} (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hFb : ∃ B, ∀ x, F x ≤ B) {α K : ℝ} (hα : 0 < α) (hK : 1 ≤ K)
    (hexp : ∫ x, Real.exp (α * F x) ∂Q ≤ K) (hfin : klDiv ν Q ≠ ⊤) :
    ∫ x, F x ∂ν ≤ α⁻¹ * ((klDiv ν Q).toReal + Real.log K) := by
  obtain ⟨B, hB⟩ := hFb
  have hbound : ∀ x, |α * F x| ≤ α * B := fun x => by
    rw [abs_of_nonneg (mul_nonneg hα.le (hF0 x))]
    exact mul_le_mul_of_nonneg_left (hB x) hα.le
  have hdv := SharpLSI.dvFun_le_klDiv (ρ := ν) (ν := Q) (hFm.const_mul α) hbound
  rw [← ENNReal.ofReal_toReal hfin, EReal.coe_ennreal_ofReal,
    max_eq_left ENNReal.toReal_nonneg] at hdv
  have hdv' := EReal.coe_le_coe_iff.mp hdv
  unfold SharpLSI.dvFun at hdv'
  rw [integral_const_mul] at hdv'
  have hpos : 0 < ∫ x, Real.exp (α * F x) ∂Q :=
    integral_exp_pos (integrable_exp_of_bound (ν := Q) (hFm.const_mul α) hbound)
  have hlog : Real.log (∫ x, Real.exp (α * F x) ∂Q) ≤ Real.log K :=
    Real.log_le_log hpos hexp
  rw [inv_mul_eq_div, le_div_iff₀ hα]
  linarith

/-- Fixed-N boundedness of the explicitly differentiated centered force. This bound is
used only to justify entropy duality; the resulting expectation bound is uniform in N. -/
private theorem t01_centered_force_bounded {d : ℕ} (D : KData d)
    (g : Torus d → Tangent d) {Mg : ℝ} (hMg : ∀ x, ‖g x‖ ≤ Mg) (N : ℕ+) :
    ∃ B : ℝ, ∀ X : ParticleSpace d N,
      ∑ i : Fin N, ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, D.G1 (X i) (X j) +
        (2 * (N : ℝ))⁻¹ • g (X i)‖ ^ 2 ≤ B := by
  let R : Fin N → ℝ := fun i =>
    (N : ℝ)⁻¹ * ((Finset.univ.erase i).card * D.B) + (2 * (N : ℝ))⁻¹ * Mg
  refine ⟨∑ i, (R i) ^ 2, fun X => Finset.sum_le_sum fun i _ => ?_⟩
  apply pow_le_pow_left₀ (norm_nonneg _)
  apply (norm_add_le _ _).trans
  refine add_le_add ?_ ?_
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
    calc ∑ j ∈ Finset.univ.erase i, ‖D.G1 (X i) (X j)‖ ≤ ∑ _j ∈ Finset.univ.erase i, D.B :=
          Finset.sum_le_sum fun j _ => D.G1b _ _
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hMg _) (by positivity)

/-- Genuine centered gradients, with a uniform force expectation under every finite-entropy
law. The only analytic input beyond the current equilibrium is the reference entropy estimate;
the product exponential moment is derived here from the bounded centered kernel gradient. -/
theorem t01_arbitrary_force_bound_of_reference_entropy {d : ℕ} (A : InteractionData d)
    (hA : LipschitzData A) (hd : 0 < d) (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    {Cref : ℝ} (hCref : 0 ≤ Cref)
    (hentropy : ∀ (N : ℕ+) (ν : Measure (ParticleSpace d N)) [IsProbabilityMeasure ν],
      klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤
        ENNReal.ofReal Cref * (klDiv ν (particleLaw A N) + 1)) :
    ∃ (gU : (N : ℕ+) → ParticleSpace d N → Fin N → Tangent d) (C : ℝ),
      0 ≤ C ∧
      (∀ N, IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) (gU N)) ∧
      (∀ N, Measurable (fun X => particleTangentNormSq (gU N X))) ∧
      (∀ N, ∃ B : ℝ, ∀ X, particleTangentNormSq (gU N X) ≤ B) ∧
      ∀ (N : ℕ+) (ν : Measure (ParticleSpace d N)) [IsProbabilityMeasure ν],
        klDiv ν (particleLaw A N) ≠ ⊤ →
          ∫ X, particleTangentNormSq (gU N X) ∂ν ≤
            C * ((klDiv ν (particleLaw A N)).toReal + 1) := by
  obtain ⟨D, hD⟩ := exists_centeredKernel_data A hA (μ : Measure (Torus d))
  obtain ⟨gδ, hδm, ⟨Mδ, hδb⟩, hδ⟩ :=
    exists_centeredKernel_diagonal_gradient A hA (μ : Measure (Torus d))
  have hDK : D.K = DGPS.centeredKernel A μ := hD
  have hδ' : IsWeakGradient (fun x => D.K x x) gδ := by rw [hDK]; exact hδ
  have hsym : ∀ x y, D.K x y = D.K y x := by rw [hDK]; exact DGPS.centeredKernel_symm A μ
  have hc : ∀ x, ∫ y, D.K x y ∂(μ : Measure (Torus d)) = 0 := by
    rw [hDK]
    exact DGPS.integral_centeredKernel_right A μ
  have hac : (μ : Measure (Torus d)) ≪ haar d := by
    rw [← hμ]
    exact (frozenGibbs A μ).measure_ac_haar
  obtain ⟨⟨hU, -⟩, hb0⟩ := force_package_centered (μ := (μ : Measure (Torus d)))
    (fun _ h => hac.ae_le h) hsym D.Kc D.G1m D.G1b hδm hδb D.g1 hδ' hc
  let gU : (N : ℕ+) → ParticleSpace d N → Fin N → Tangent d := fun N X i =>
    (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, D.G1 (X i) (X j) +
      (2 * (N : ℝ))⁻¹ • gδ (X i)
  have hU' : ∀ N, IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) (gU N) := by
    intro N
    unfold centeredParticlePotential
    simp only [one_div]
    simpa only [gU, hDK] using hU N
  let α : ℝ := (8 * (d : ℝ) * (1 + D.B ^ 2 + Mδ ^ 2))⁻¹
  have hα : 0 < α := by dsimp [α]; positivity
  let K : ℝ := 2 * Real.exp (1 / 16)
  have hK : 1 ≤ K := by
    dsimp [K]
    have he := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1 / 16)
    linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hexp : ∀ N : ℕ+, ∫ X, Real.exp (α * particleTangentNormSq (gU N X))
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ K := by
    intro N
    have hlin : ∫⁻ X, ENNReal.ofReal (Real.exp (α * particleTangentNormSq (gU N X)))
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ ENNReal.ofReal K := by
      simpa only [gU, particleTangentNormSq, K, ENNReal.ofReal_mul zero_le_two] using
        exp_moment_core hd D.G1m hδm D.B_nonneg D.G1b hδb hb0 rfl N.pos
    have hmExp : AEStronglyMeasurable
        (fun X : ParticleSpace d N => Real.exp (α * particleTangentNormSq (gU N X)))
        (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) :=
      ((measurable_force_sq D.G1m hδm N).const_mul α).exp.aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun X => (Real.exp_pos _).le) hmExp]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin
  have hFm : ∀ N, Measurable (fun X => particleTangentNormSq (gU N X)) :=
    fun N => measurable_force_sq D.G1m hδm N
  have hFb : ∀ N, ∃ B : ℝ, ∀ X, particleTangentNormSq (gU N X) ≤ B :=
    fun N => t01_centered_force_bounded D gδ hδb N
  refine ⟨gU, α⁻¹ * (Cref + Real.log K), by positivity, hU', hFm, hFb, ?_⟩
  intro N ν _ hfin
  have hbound := hentropy N ν
  have hRfin : ENNReal.ofReal Cref * (klDiv ν (particleLaw A N) + 1) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨hfin, ENNReal.one_ne_top⟩)
  have hQfin := ne_top_of_le_ne_top hRfin hbound
  have hQreal : (klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))).toReal ≤
      Cref * ((klDiv ν (particleLaw A N)).toReal + 1) := by
    have hh := ENNReal.toReal_mono hRfin hbound
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCref,
      ENNReal.toReal_add hfin ENNReal.one_ne_top, ENNReal.toReal_one] at hh
  have hF0 : ∀ X, 0 ≤ particleTangentNormSq (gU N X) := fun X =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hdual := t01_integral_le_entropy_of_exponential
    (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ν
    (hFm N) hF0 (hFb N) hα hK (hexp N) hQfin
  refine hdual.trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ α⁻¹)
  have hH : 0 ≤ (klDiv ν (particleLaw A N)).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_nonneg hlogK hH]

/-- Every genuine representative of the centered particle gradient has the same force
integral under a finite-entropy comparison law. -/
theorem t01_centered_force_integral_eq {d : ℕ} (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+)
    {g g' : ParticleSpace d N → Fin N → Tangent d}
    (hg : IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) g)
    (hg' : IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) g')
    (ν : Measure (ParticleSpace d N)) [IsProbabilityMeasure ν]
    (hfin : klDiv ν (particleLaw A N) ≠ ⊤) :
    (∫ X, particleTangentNormSq (g X) ∂ν) = ∫ X, particleTangentNormSq (g' X) ∂ν := by
  have hac : ν ≪ particleHaar d N :=
    (klDiv_ne_top_iff.mp hfin).1.trans (Particle.particleLaw_absolutelyContinuous A N)
  have heq : g =ᵐ[ν] g' := hac.ae_le (hg.ae_eq hg')
  exact integral_congr_ae (heq.mono fun X hX => congrArg particleTangentNormSq hX)

/-- Positive scalar rate supplies the actual equilibrium and a uniform arbitrary-law force
bound for every genuine representative of its centered particle gradient. -/
theorem t01_positive_rate_arbitrary_force_bound {d : ℕ} (A : InteractionData d)
    (hA : LipschitzData A) (hd : 0 < d) (b : AbsoluteDrift A)
    (hrate : 0 < scalarRate A b) :
    ∃ μ : ProbabilityMeasure (Torus d),
      DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A ∧
      (∀ ρ : ProbabilityMeasure (Torus d),
        DGPS.freeEnergy A ρ = DGPS.freeEnergyMinimum A → ρ = μ) ∧
      (frozenGibbs A μ).measure = (μ : Measure (Torus d)) ∧
      ∃ (gU : (N : ℕ+) → ParticleSpace d N → Fin N → Tangent d) (C : ℝ),
        0 ≤ C ∧
        (∀ N, IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) (gU N)) ∧
        ∀ (N : ℕ+) (g : ParticleSpace d N → Fin N → Tangent d),
          IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) g →
          ∀ (ν : Measure (ParticleSpace d N)) [IsProbabilityMeasure ν],
            klDiv ν (particleLaw A N) ≠ ⊤ →
              ∫ X, particleTangentNormSq (g X) ∂ν ≤
                C * ((klDiv ν (particleLaw A N)).toReal + 1) := by
  obtain ⟨μ, hmin, huniq, -, hfix, c, Cref, p, -, -, hCref, -, -, hN⟩ :=
    t01_positive_rate_reference_data A hA b hrate
  have hentropy : ∀ (N : ℕ+) (ν : Measure (ParticleSpace d N)) [IsProbabilityMeasure ν],
      klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤
        ENNReal.ofReal Cref * (klDiv ν (particleLaw A N) + 1) :=
    fun N ν _ => (hN N).2.2 ν
  obtain ⟨gU, C, hC, hU, -, -, hbound⟩ :=
    t01_arbitrary_force_bound_of_reference_entropy A hA hd μ hfix hCref.le hentropy
  refine ⟨μ, hmin, huniq, hfix, gU, C, hC, hU, ?_⟩
  intro N g hg ν _ hfin
  rw [t01_centered_force_integral_eq A μ N hg (hU N) ν hfin]
  exact hbound N ν hfin

end DGPS.Lipschitz
