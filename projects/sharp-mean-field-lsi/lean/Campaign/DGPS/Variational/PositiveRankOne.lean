import DGPS.Analysis.RelativeFisher
import DGPS.Model.SpeciesFamily
import DGPS.Variational.ScoreDecomposition
import DGPS.Variational.EquilibriumGibbs
import DGPS.Foundations.SobolevEmbedding
import DGPS.Foundations.SobolevCalculus

open MeasureTheory
open scoped ENNReal NNReal
open InformationTheory

namespace DGPS.PositiveRankOne

/-- A positive centered rank-one model on the circle. -/
structure RankOneModel where
  q : Torus 1 → ℝ
  φ : Torus 1 → ℝ
  η : ℝ
  q_smooth : IsSmoothPeriodic q
  q_pos : ∀ x, 0 < q x
  q_mass : ∫ x, q x ∂haar 1 = 1
  φ_smooth : IsSmoothPeriodic φ
  φ_centered : ∫ x, φ x * q x ∂haar 1 = 0
  η_nonneg : 0 ≤ η

end DGPS.PositiveRankOne

namespace DGPS.PositiveRankOne.RankOneModel

variable (M : RankOneModel)

theorem q_cont : Continuous M.q := M.q_smooth.continuous_torus
theorem φ_cont : Continuous M.φ := M.φ_smooth.continuous_torus

/-- One-body potential `V = -log q + (η/2) φ²`. -/
noncomputable def V (x : Torus 1) : ℝ := -Real.log (M.q x) + M.η / 2 * M.φ x ^ 2

/-- Zero-diagonal gauge kernel `W(x,y) = η (φ(x)φ(y) - φ(x)²/2 - φ(y)²/2)`. -/
noncomputable def W (x y : Torus 1) : ℝ :=
  M.η * (M.φ x * M.φ y - M.φ x ^ 2 / 2 - M.φ y ^ 2 / 2)

noncomputable def data : InteractionData 1 where
  V := M.V
  W := M.W
  V_continuous := by
    have := M.φ_cont
    have h2 : Continuous fun x => Real.log (M.q x) := M.q_cont.log fun x => (M.q_pos x).ne'
    unfold V; fun_prop
  W_continuous := by
    have := M.φ_cont
    unfold W; fun_prop
  W_symm := fun x y => by unfold W; ring
  W_diag := fun x => by unfold W; ring

theorem exists_bound : ∃ C, ∀ x, |coordPartial 0 M.q x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (M.q_smooth.continuous_coordPartial 0).continuousOn
  exact ⟨C, fun x => by simpa using hC x (Set.mem_univ x)⟩

theorem lipschitz : TorusLipschitzWith (Classical.choose M.exists_bound) M.q := by
  intro x y
  obtain ⟨a, b, rfl, rfl, hab, -⟩ := exists_lifts_one x y
  have hd : ∀ t, HasDerivAt (fun t : ℝ => M.q (torusLift fun _ => t))
      (coordPartial 0 M.q (torusLift fun _ => t)) t := hasDerivAt_smooth_one M.q_smooth
  have hb : ∀ t, ‖deriv (fun t : ℝ => M.q (torusLift fun _ => t)) t‖ ≤ Classical.choose M.exists_bound := by
    intro t
    rw [(hd t).deriv, Real.norm_eq_abs]
    exact Classical.choose_spec M.exists_bound _
  have := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (hd t).differentiableAt) (fun t _ => hb t) (Set.mem_univ b) (Set.mem_univ a)
  rw [← hab]
  simpa [Real.norm_eq_abs] using this

/-- The reference probability `q m`. -/
noncomputable def ref : BoundedPositiveReference 1 where
  density := M.q
  measurable_density := M.q_cont.measurable
  lower := M.q (Classical.choose (isCompact_univ.exists_isMinOn Set.univ_nonempty M.q_cont.continuousOn))
  upper := M.q (Classical.choose (isCompact_univ.exists_isMaxOn Set.univ_nonempty M.q_cont.continuousOn))
  lower_pos := M.q_pos _
  lower_le := Filter.Eventually.of_forall fun x =>
    (Classical.choose_spec (isCompact_univ.exists_isMinOn Set.univ_nonempty M.q_cont.continuousOn)).2
      (Set.mem_univ x)
  le_upper := Filter.Eventually.of_forall fun x =>
    (Classical.choose_spec (isCompact_univ.exists_isMaxOn Set.univ_nonempty M.q_cont.continuousOn)).2
      (Set.mem_univ x)
  mass_one := M.q_mass

theorem ref_lip : M.ref.hasPositiveLipschitzDensity := by
  refine ⟨_, M.ref.lower, M.ref.lower_pos, fun x => ?_, M.lipschitz⟩
  exact (Classical.choose_spec (isCompact_univ.exists_isMinOn Set.univ_nonempty M.q_cont.continuousOn)).2
      (Set.mem_univ x)


theorem log_smooth : IsSmoothPeriodic fun x => Real.log (M.q x) :=
  RelativeFisher.isSmoothPeriodic_comp M.q_smooth
    (Real.contDiffOn_log.mono fun _ ht => (Set.mem_Ioi.mp ht).ne') M.q_pos

theorem sqrt_smooth : IsSmoothPeriodic fun x => Real.sqrt (M.q x) :=
  RelativeFisher.isSmoothPeriodic_comp M.q_smooth
    (fun _ ht => (Real.contDiffAt_sqrt (Set.mem_Ioi.mp ht).ne').contDiffWithinAt) M.q_pos

/-- The reference density `q` as an absolute-admissible density. -/
noncomputable def absQ : AbsoluteDensity 1 where
  sqrt := fun x => Real.sqrt (M.q x)
  sqrt_mem := ⟨_, M.sqrt_smooth.isWeakGradient⟩
  sqrt_nonneg := Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
  mass_one := by
    have : (fun x => Real.sqrt (M.q x) ^ 2) = M.q := by
      funext x; exact Real.sq_sqrt (M.q_pos x).le
    rw [this, M.q_mass]


/-- Integral against the measure of an absolute density, in Haar form. -/
theorem integral_densityMeasure (ρ : AbsoluteDensity 1) (f : Torus 1 → ℝ) :
    ∫ x, f x ∂(densityMeasure ρ : Measure (Torus 1)) = ∫ x, ρ.density x * f x ∂haar 1 := by
  rw [densityMeasure_coe, integral_withDensity_eq_integral_toReal_smul₀]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [AbsoluteDensity.density, ENNReal.toReal_ofReal (sq_nonneg _)]
  · exact (ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

section energies

variable (ν : ProbabilityMeasure (Torus 1))

theorem real_univ : (ν : Measure (Torus 1)).real Set.univ = 1 := by
  simp [Measure.real]

theorem integrable_cont {f : Torus 1 → ℝ} (hf : Continuous f) :
    Integrable f (ν : Measure (Torus 1)) :=
  DGPS.Lipschitz.integrable_of_continuous_torus hf _

theorem inner_W (y : Torus 1) : ∫ x, M.W x y ∂(ν : Measure (Torus 1)) =
    M.η * ((∫ x, M.φ x ∂(ν : Measure (Torus 1))) * M.φ y -
      (∫ x, M.φ x ^ 2 ∂(ν : Measure (Torus 1))) / 2 - M.φ y ^ 2 / 2) := by
  have h1 : Integrable M.φ (ν : Measure (Torus 1)) := integrable_cont ν M.φ_cont
  have h2 : Integrable (fun x => M.φ x ^ 2) (ν : Measure (Torus 1)) :=
    integrable_cont ν (M.φ_cont.pow 2)
  have e : (fun x => M.W x y) = fun x =>
      (M.η * M.φ y) * M.φ x - (M.η / 2) * M.φ x ^ 2 - M.η * M.φ y ^ 2 / 2 := by
    funext x; unfold W; ring
  have ia : Integrable (fun x => (M.η * M.φ y) * M.φ x) (ν : Measure (Torus 1)) := h1.const_mul _
  have ib : Integrable (fun x => (M.η / 2) * M.φ x ^ 2) (ν : Measure (Torus 1)) := h2.const_mul _
  have iab : Integrable (fun x => (M.η * M.φ y) * M.φ x - (M.η / 2) * M.φ x ^ 2)
      (ν : Measure (Torus 1)) := ia.sub ib
  have hr := real_univ ν
  rw [e, integral_sub iab (integrable_const _), integral_sub ia ib, integral_const_mul,
    integral_const_mul, integral_const]
  rw [hr]
  ring

theorem potentialEnergy_eq : potentialEnergy M.data ν =
    -∫ x, Real.log (M.q x) ∂(ν : Measure (Torus 1)) +
      M.η / 2 * ∫ x, M.φ x ^ 2 ∂(ν : Measure (Torus 1)) := by
  have h1 : Integrable (fun x => Real.log (M.q x)) (ν : Measure (Torus 1)) :=
    integrable_cont ν M.log_smooth.continuous_torus
  have h2 : Integrable (fun x => M.φ x ^ 2) (ν : Measure (Torus 1)) :=
    integrable_cont ν (M.φ_cont.pow 2)
  unfold potentialEnergy
  show ∫ x, (-Real.log (M.q x) + M.η / 2 * M.φ x ^ 2) ∂(ν : Measure (Torus 1)) = _
  have i1 : Integrable (fun x => -Real.log (M.q x)) (ν : Measure (Torus 1)) := h1.neg
  have i2 : Integrable (fun x => M.η / 2 * M.φ x ^ 2) (ν : Measure (Torus 1)) := h2.const_mul _
  rw [integral_add i1 i2, integral_neg, integral_const_mul]

theorem interactionEnergy_eq : interactionEnergy M.data ν =
    M.η * ((∫ x, M.φ x ∂(ν : Measure (Torus 1))) ^ 2 -
      ∫ x, M.φ x ^ 2 ∂(ν : Measure (Torus 1))) := by
  have h1 : Integrable M.φ (ν : Measure (Torus 1)) := integrable_cont ν M.φ_cont
  have h2 : Integrable (fun x => M.φ x ^ 2) (ν : Measure (Torus 1)) :=
    integrable_cont ν (M.φ_cont.pow 2)
  rw [interactionEnergy_eq_iterated]
  have : ∀ y, ∫ x, M.data.W x y ∂(ν : Measure (Torus 1)) = M.η * ((∫ x, M.φ x ∂(ν : Measure (Torus 1))) * M.φ y -
      (∫ x, M.φ x ^ 2 ∂(ν : Measure (Torus 1))) / 2 - M.φ y ^ 2 / 2) := fun y => inner_W M ν y
  simp_rw [this]
  have ia : Integrable (fun y => (∫ x, M.φ x ∂(ν : Measure (Torus 1))) * M.φ y)
      (ν : Measure (Torus 1)) := h1.const_mul _
  have ib : Integrable (fun _ : Torus 1 => (∫ x, M.φ x ^ 2 ∂(ν : Measure (Torus 1))) / 2)
      (ν : Measure (Torus 1)) := integrable_const _
  have ic : Integrable (fun y => M.φ y ^ 2 / 2) (ν : Measure (Torus 1)) := h2.div_const _
  have iab : Integrable (fun y => (∫ x, M.φ x ∂(ν : Measure (Torus 1))) * M.φ y -
      (∫ x, M.φ x ^ 2 ∂(ν : Measure (Torus 1))) / 2) (ν : Measure (Torus 1)) := ia.sub ib
  have hr := real_univ ν
  rw [integral_const_mul, integral_sub iab ic, integral_sub ia ib, integral_const_mul,
    integral_const, integral_div]
  rw [hr]
  ring

end energies

theorem tilted_eq : (haar 1 : Measure (Torus 1)).tilted (fun x => Real.log (M.q x)) = M.ref.measure := by
  have h : ∀ x, Real.exp (Real.log (M.q x)) = M.q x := fun x => Real.exp_log (M.q_pos x)
  simp only [Measure.tilted, h]
  rw [M.q_mass]
  simp [BoundedPositiveReference.measure, ref]

theorem log_bound : ∃ B, ∀ x, |Real.log (M.q x)| ≤ B := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn M.log_smooth.continuous_torus.continuousOn
  exact ⟨C, fun x => by simpa using hC x (Set.mem_univ x)⟩

theorem free_energy_identity (ν : ProbabilityMeasure (Torus 1))
    (h : relativeEntropy (ν : Measure (Torus 1)) (haar 1) ≠ ⊤) :
    relativeEntropy (ν : Measure (Torus 1)) M.ref.measure ≠ ⊤ ∧
      (relativeEntropy (ν : Measure (Torus 1)) (haar 1)).toReal + potentialEnergy M.data ν +
        1 / 2 * interactionEnergy M.data ν =
      (relativeEntropy (ν : Measure (Torus 1)) M.ref.measure).toReal +
        M.η / 2 * (∫ x, M.φ x ∂(ν : Measure (Torus 1))) ^ 2 := by
  obtain ⟨B, hB⟩ := M.log_bound
  have h' : klDiv (ν : Measure (Torus 1)) (haar 1) ≠ ⊤ := by
    rwa [← DGPS.Analysis.relativeEntropy_eq_klDiv]
  obtain ⟨h1, h2⟩ := DGPS.Lipschitz.klDiv_tilted_forward (ρ := (ν : Measure (Torus 1))) (ν := haar 1)
    M.log_smooth.continuous_torus.measurable hB h'
  rw [M.tilted_eq] at h1 h2
  refine ⟨by rwa [DGPS.Analysis.relativeEntropy_eq_klDiv], ?_⟩
  rw [DGPS.Analysis.relativeEntropy_eq_klDiv, DGPS.Analysis.relativeEntropy_eq_klDiv, h2,
    potentialEnergy_eq, interactionEnergy_eq]
  have hq : ∫ x, Real.exp (Real.log (M.q x)) ∂(haar 1 : Measure (Torus 1)) = 1 := by
    have h2 : (fun x => Real.exp (Real.log (M.q x))) = M.q := funext fun x => Real.exp_log (M.q_pos x)
    rw [h2]; exact M.q_mass
  rw [hq]
  simp
  ring

theorem entropy_ref_eq (ν : ProbabilityMeasure (Torus 1))
    (h : relativeEntropy (ν : Measure (Torus 1)) (haar 1) ≠ ⊤) :
    (relativeEntropy (ν : Measure (Torus 1)) M.ref.measure).toReal =
      (relativeEntropy (ν : Measure (Torus 1)) (haar 1)).toReal -
        ∫ x, Real.log (M.q x) ∂(ν : Measure (Torus 1)) := by
  have := (M.free_energy_identity ν h).2
  rw [potentialEnergy_eq, interactionEnergy_eq] at this
  linarith

theorem densityMeasure_absQ : (densityMeasure M.absQ : Measure (Torus 1)) = M.ref.measure := by
  rw [densityMeasure_coe]
  have : ∀ x, ENNReal.ofReal (M.absQ.sqrt x ^ 2) = ENNReal.ofReal (M.q x) := fun x => by
    show ENNReal.ofReal (Real.sqrt (M.q x) ^ 2) = _
    rw [Real.sq_sqrt (M.q_pos x).le]
  simp only [BoundedPositiveReference.measure, ref, this]

theorem freeEnergyMinimumReal_eq_zero : freeEnergyMinimumReal M.data = 0 := by
  apply le_antisymm
  · have hfin := (absoluteDensity_entropy_finite M.absQ).2.2.1
    have h1 := freeEnergyMinimumReal_le M.data (densityMeasure M.absQ) hfin
    have h2 := (M.free_energy_identity (densityMeasure M.absQ) hfin).2
    rw [potentialEnergy_eq, interactionEnergy_eq] at h1 h2
    rw [densityMeasure_absQ] at h2 h1
    have hz : relativeEntropy M.ref.measure M.ref.measure = 0 := by
      rw [DGPS.Analysis.relativeEntropy_eq_klDiv]; exact klDiv_self _
    have hφ : ∫ x, M.φ x ∂(M.ref.measure) = 0 := by
      have := integral_densityMeasure M.absQ M.φ
      rw [densityMeasure_absQ] at this
      rw [this]
      have e : ∀ x, M.absQ.density x * M.φ x = M.φ x * M.q x := fun x => by
        show Real.sqrt (M.q x) ^ 2 * _ = _
        rw [Real.sq_sqrt (M.q_pos x).le]; ring
      simp_rw [e]; exact M.φ_centered
    rw [hz, hφ] at h2
    rw [hφ] at h1
    simp only [ENNReal.toReal_zero] at h2
    nlinarith
  · obtain ⟨μ, hμ⟩ := freeEnergy_minimum_exists M.data
    have hf : FiniteFreeEnergy M.data μ := by
      obtain ⟨r, hr⟩ := (freeEnergyMinimum_finite M.data).1
      exact ⟨r, hμ.trans hr⟩
    have hH := (finiteFreeEnergy_iff M.data μ).1 hf
    have h1 := freeEnergy_eq_real M.data μ hH
    rw [hμ, ← coe_freeEnergyMinimumReal, EReal.coe_eq_coe_iff] at h1
    have h2 := (M.free_energy_identity μ hH).2
    rw [h1]
    rw [potentialEnergy_eq, interactionEnergy_eq] at h2 ⊢
    have h3 := ENNReal.toReal_nonneg (a := relativeEntropy (μ : Measure (Torus 1)) M.ref.measure)
    have h4 : 0 ≤ M.η / 2 * (∫ x, M.φ x ∂(μ : Measure (Torus 1))) ^ 2 :=
      mul_nonneg (by linarith [M.η_nonneg]) (sq_nonneg _)
    linarith

theorem integrable_density_mul (ρ : AbsoluteDensity 1) {f : Torus 1 → ℝ} (hf : Continuous f) :
    Integrable (fun x => ρ.density x * f x) (haar 1) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have := ρ.integrable_density.mul_bdd (c := C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))
  exact this

theorem integral_barycenter (F : SpeciesFamily 1) {f : Torus 1 → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂(densityMeasure (barycenter F) : Measure (Torus 1)) =
      ∑ s, F.weight s * ∫ x, f x ∂(densityMeasure (F.density s) : Measure (Torus 1)) := by
  rw [integral_densityMeasure]
  simp_rw [integral_densityMeasure, SpeciesFamily.barycenter_density_eq_sum]
  simp_rw [Finset.sum_mul, ← integral_const_mul]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun s _ => integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [mul_assoc]
  · intro s _
    have := (integrable_density_mul (F.density s) hf).const_mul (F.weight s)
    simpa only [mul_assoc] using this

theorem gap_eq (F : SpeciesFamily 1) :
    (speciesGap M.data F : ℝ) =
      ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus 1))
        M.ref.measure).toReal +
      M.η / 2 * (∫ x, M.φ x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) ^ 2 := by
  rw [coe_speciesGap, speciesRawGap, M.freeEnergyMinimumReal_eq_zero, potentialEnergy_eq,
    interactionEnergy_eq]
  have hs : ∀ s, (relativeEntropy (densityMeasure (F.density s) : Measure (Torus 1))
      M.ref.measure).toReal = (relativeEntropy (densityMeasure (F.density s) : Measure (Torus 1))
      (haar 1)).toReal - ∫ x, Real.log (M.q x) ∂(densityMeasure (F.density s) : Measure (Torus 1)) :=
    fun s => M.entropy_ref_eq _ (absoluteDensity_entropy_finite (F.density s)).2.2.1
  simp_rw [hs, mul_sub, Finset.sum_sub_distrib]
  rw [← integral_barycenter F M.log_smooth.continuous_torus]
  ring

theorem coordPartial_lin {v w : Torus 1 → ℝ} (hv : IsSmoothPeriodic v) (hw : IsSmoothPeriodic w)
    (a b c : ℝ) (x : Torus 1) :
    coordPartial 0 (fun y => a * v y + b * w y + c) x =
      a * coordPartial 0 v x + b * coordPartial 0 w x := by
  have hv1 : DifferentiableAt ℝ (v ∘ torusLift) (SharpLSI.secT x) :=
    (hv.differentiable (by simp)) _
  have hw1 : DifferentiableAt ℝ (w ∘ torusLift) (SharpLSI.secT x) :=
    (hw.differentiable (by simp)) _
  show fderiv ℝ (fun y => a * (v ∘ torusLift) y + b * (w ∘ torusLift) y + c) (SharpLSI.secT x)
    (Pi.single 0 1) = _
  rw [fderiv_add_const, fderiv_fun_add (hv1.const_mul a) (hw1.const_mul b),
    fderiv_const_mul hv1, fderiv_const_mul hw1]
  simp [coordPartial]

/-- `φ'`. -/
noncomputable def dφ (x : Torus 1) : ℝ := coordPartial 0 M.φ x

/-- `(log q)'`. -/
noncomputable def dlogq (x : Torus 1) : ℝ := coordPartial 0 (fun y => Real.log (M.q y)) x

/-- The generator `A_q f = -f'' - (log q)' f'` applied to the feature. -/
noncomputable def Aq (x : Torus 1) : ℝ :=
  -coordPartial 0 (coordPartial 0 M.φ) x - M.dlogq x * M.dφ x

theorem dφ_smooth : IsSmoothPeriodic M.dφ := M.φ_smooth.isSmoothPeriodic_coordPartial 0
theorem dφ_cont : Continuous M.dφ := M.dφ_smooth.continuous_torus
theorem dlogq_cont : Continuous M.dlogq :=
  M.log_smooth.continuous_coordPartial 0
theorem ddφ_cont : Continuous (coordPartial 0 M.dφ) :=
  M.dφ_smooth.continuous_coordPartial 0
theorem Aq_cont : Continuous M.Aq := by
  unfold Aq
  have := M.dφ_smooth.continuous_coordPartial 0
  have := M.dlogq_cont
  have := M.dφ_cont
  exact (M.dφ_smooth.continuous_coordPartial 0).neg.sub (M.dlogq_cont.mul M.dφ_cont)

theorem force_coord (b : AbsoluteDrift M.data) (ρ : AbsoluteDensity 1) :
    ∀ᵐ x ∂haar 1, b.force ρ x 0 =
      -M.dlogq x + M.η * (∫ y, M.φ y ∂(densityMeasure ρ : Measure (Torus 1))) * M.dφ x := by
  set m := ∫ y, M.φ y ∂(densityMeasure ρ : Measure (Torus 1)) with hm
  set C := ∫ y, M.φ y ^ 2 ∂(densityMeasure ρ : Measure (Torus 1)) with hC
  have hU : interactionPotential M.data ρ =
      fun y => (-1) * Real.log (M.q y) + (M.η * m) * M.φ y + (-(M.η * C / 2)) := by
    funext x
    have h := inner_W M (densityMeasure ρ) x
    unfold interactionPotential
    have e : ∫ y, M.data.W x y ∂(densityMeasure ρ : Measure (Torus 1)) =
        ∫ y, M.W y x ∂(densityMeasure ρ : Measure (Torus 1)) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => (M.data.W_symm y x).symm)
    rw [e, h]
    show M.V x + _ = _
    unfold V
    ring
  have hsm : IsSmoothPeriodic (fun y => (-1) * Real.log (M.q y) + (M.η * m) * M.φ y +
      (-(M.η * C / 2))) := by
    have h1 := M.log_smooth
    have h2 := M.φ_smooth
    exact ((h1.const_smul (-1 : ℝ)).add (h2.const_smul (M.η * m))).add contDiff_const
  have hw := hsm.isWeakGradient
  rw [isWeakGradient_iff_isWeakGradientLp] at hw
  have hw1 : IsWeakGradientLp 1 (interactionPotential M.data ρ)
      (smoothGrad fun y => (-1) * Real.log (M.q y) + (M.η * m) * M.φ y + (-(M.η * C / 2))) := by
    rw [hU]
    exact ⟨hw.memLp.mono_exponent one_le_two, hw.memLp_grad.mono_exponent one_le_two, hw.ibp⟩
  filter_upwards [b.ae_eq_of_isWeakGradient ρ hw1] with x hx
  rw [hx, smoothGrad_apply, coordPartial_lin M.log_smooth M.φ_smooth]
  unfold dlogq dφ
  ring

theorem memLp_mul_cont {c f : Torus 1 → ℝ} (hc : Continuous c) (hf : MemLp f 2 (haar 1)) :
    MemLp (fun x => f x * c x) 2 (haar 1) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have h : MemLp c ∞ (haar 1) := memLp_top_of_bound hc.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))
  have : MemLp (c * f) 2 (haar 1) := h.mul (r := 2) hf
  have e : (fun x => f x * c x) = c * f := by funext x; simp [mul_comm]
  rw [e]; exact this

theorem integrable_cont_mul {c f : Torus 1 → ℝ} (hc : Continuous c) (hf : Integrable f (haar 1)) :
    Integrable (fun x => c x * f x) (haar 1) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact hf.bdd_mul (c := C) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))

theorem dissipation_integral {u : Torus 1 → ℝ} {w : Torus 1 → Tangent 1}
    (hw : IsWeakGradient u w) (K : ℝ) :
    Integrable (fun x => (2 * w x 0 - u x * M.dlogq x) ^ 2) (haar 1) ∧
    Integrable (fun x => (2 * w x 0 + u x * (-M.dlogq x + K * M.dφ x)) ^ 2) (haar 1) ∧
    ∫ x, (2 * w x 0 + u x * (-M.dlogq x + K * M.dφ x)) ^ 2 ∂haar 1 =
      ∫ x, (2 * w x 0 - u x * M.dlogq x) ^ 2 ∂haar 1 +
        2 * K * ∫ x, u x ^ 2 * M.Aq x ∂haar 1 +
        K ^ 2 * ∫ x, u x ^ 2 * M.dφ x ^ 2 ∂haar 1 := by
  have hu : MemLp u 2 (haar 1) := hw.memLp
  have hg : MemLp (fun x => w x 0) 2 (haar 1) := memLp_coord hw.memLp_grad 0
  have ha : MemLp (fun x => 2 * w x 0 - u x * M.dlogq x) 2 (haar 1) :=
    (hg.const_mul 2).sub (memLp_mul_cont M.dlogq_cont hu)
  have hu2 : Integrable (fun x => u x ^ 2) (haar 1) := hu.integrable_sq
  have hua : Integrable (fun x => u x * (2 * w x 0 - u x * M.dlogq x)) (haar 1) :=
    hu.integrable_mul ha
  have hug : Integrable (fun x => u x * w x 0) (haar 1) := hu.integrable_mul hg
  have i1 : Integrable (fun x => (2 * w x 0 - u x * M.dlogq x) ^ 2) (haar 1) := ha.integrable_sq
  have i2 : Integrable (fun x => M.dφ x * (u x * (2 * w x 0 - u x * M.dlogq x))) (haar 1) :=
    integrable_cont_mul M.dφ_cont hua
  have i3 : Integrable (fun x => M.dφ x ^ 2 * u x ^ 2) (haar 1) :=
    integrable_cont_mul (M.dφ_cont.pow 2) hu2
  have pt : ∀ x, (2 * w x 0 + u x * (-M.dlogq x + K * M.dφ x)) ^ 2 =
      (2 * w x 0 - u x * M.dlogq x) ^ 2 +
      2 * K * (M.dφ x * (u x * (2 * w x 0 - u x * M.dlogq x))) +
      K ^ 2 * (M.dφ x ^ 2 * u x ^ 2) := fun x => by ring
  have i4 : Integrable (fun x => (2 * w x 0 + u x * (-M.dlogq x + K * M.dφ x)) ^ 2) (haar 1) := by
    simp_rw [pt]
    exact (i1.add (i2.const_mul _)).add (i3.const_mul _)
  refine ⟨i1, i4, ?_⟩
  simp_rw [pt]
  have s1 : ∫ x, ((2 * w x 0 - u x * M.dlogq x) ^ 2 +
      2 * K * (M.dφ x * (u x * (2 * w x 0 - u x * M.dlogq x))) +
      K ^ 2 * (M.dφ x ^ 2 * u x ^ 2)) ∂haar 1 =
      ∫ x, ((2 * w x 0 - u x * M.dlogq x) ^ 2 +
        2 * K * (M.dφ x * (u x * (2 * w x 0 - u x * M.dlogq x)))) ∂haar 1 +
      ∫ x, K ^ 2 * (M.dφ x ^ 2 * u x ^ 2) ∂haar 1 :=
    integral_add (i1.add (i2.const_mul _)) (i3.const_mul _)
  have s2 : ∫ x, ((2 * w x 0 - u x * M.dlogq x) ^ 2 +
        2 * K * (M.dφ x * (u x * (2 * w x 0 - u x * M.dlogq x)))) ∂haar 1 =
      ∫ x, (2 * w x 0 - u x * M.dlogq x) ^ 2 ∂haar 1 +
      ∫ x, 2 * K * (M.dφ x * (u x * (2 * w x 0 - u x * M.dlogq x))) ∂haar 1 :=
    integral_add i1 (i2.const_mul _)
  rw [s1, s2, integral_const_mul, integral_const_mul]
  -- the cross term
  have e1 : Integrable (fun x => M.dφ x * (u x * w x 0)) (haar 1) :=
    integrable_cont_mul M.dφ_cont hug
  have e2 : Integrable (fun x => u x ^ 2 * (M.dlogq x * M.dφ x)) (haar 1) :=
    (integrable_cont_mul (c := fun x => M.dlogq x * M.dφ x) (M.dlogq_cont.mul M.dφ_cont) hu2).congr
      (Filter.Eventually.of_forall fun x => by simp only []; ring)
  have e3 : Integrable (fun x => u x ^ 2 * coordPartial 0 M.dφ x) (haar 1) :=
    (integrable_cont_mul M.ddφ_cont hu2).congr
      (Filter.Eventually.of_forall fun x => by simp only []; ring)
  have hibp := (weak_square_gradient hw).ibp M.dφ M.dφ_smooth 0
  have hcross : ∫ x, M.dφ x * (u x * (2 * w x 0 - u x * M.dlogq x)) ∂haar 1 =
      ∫ x, u x ^ 2 * M.Aq x ∂haar 1 := by
    have l1 : ∫ x, M.dφ x * (u x * (2 * w x 0 - u x * M.dlogq x)) ∂haar 1 =
        2 * ∫ x, M.dφ x * (u x * w x 0) ∂haar 1 -
          ∫ x, u x ^ 2 * (M.dlogq x * M.dφ x) ∂haar 1 := by
      rw [← integral_const_mul, ← integral_sub (e1.const_mul 2) e2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only; ring
    have l2 : ∫ x, u x ^ 2 * M.Aq x ∂haar 1 =
        -∫ x, u x ^ 2 * coordPartial 0 M.dφ x ∂haar 1 -
          ∫ x, u x ^ 2 * (M.dlogq x * M.dφ x) ∂haar 1 := by
      have h0 : ∫ x, u x ^ 2 * M.Aq x ∂haar 1 = ∫ x, (-(u x ^ 2 * coordPartial 0 M.dφ x) -
          u x ^ 2 * (M.dlogq x * M.dφ x)) ∂haar 1 :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          have hd : M.dφ = coordPartial 0 M.φ := rfl
          simp only [Aq, hd, dφ]; ring)
      have e3' : Integrable (fun x => -(u x ^ 2 * coordPartial 0 M.dφ x)) (haar 1) := e3.neg
      rw [h0, integral_sub e3' e2, integral_neg]
    have l3 : ∫ x, u x ^ 2 * coordPartial 0 M.dφ x ∂haar 1 =
        -(2 * ∫ x, M.dφ x * (u x * w x 0) ∂haar 1) := by
      rw [hibp, ← integral_const_mul]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [PiLp.smul_apply, smul_eq_mul]; ring
    rw [l1, l2, l3]; ring
  have hh : ∫ x, M.dφ x ^ 2 * u x ^ 2 ∂haar 1 = ∫ x, u x ^ 2 * M.dφ x ^ 2 ∂haar 1 :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hcross, hh]


theorem norm_sq_tangent (v : Tangent 1) : ‖v‖ ^ 2 = v 0 ^ 2 := by
  rw [tangent_norm_sq]; simp

theorem enorm_sq_tangent (v : Tangent 1) : ‖v‖ₑ ^ 2 = ENNReal.ofReal (v 0 ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), norm_sq_tangent]

theorem ofReal_integral_eq {f : Torus 1 → ℝ} (h : Integrable f (haar 1)) (h0 : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂haar 1) = ∫⁻ x, ENNReal.ofReal (f x) ∂haar 1 :=
  ofReal_integral_eq_lintegral_ofReal h (Filter.Eventually.of_forall h0)

theorem fisher_eq (ρ : AbsoluteDensity 1) :
    ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) M.ref =
      ENNReal.ofReal (∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x) ^ 2
        ∂haar 1) := by
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  have hG := isWeakGradient_weakGradient (M.ref.memH1_log M.ref_lip)
  have hG' : IsWeakGradient (fun x => Real.log (M.ref.density x)) (smoothGrad fun x => Real.log (M.q x)) :=
    M.log_smooth.isWeakGradient
  have hae := hG.ae_eq hG'
  rw [positiveReference_absolute_identity M.ref M.ref_lip ρ]
  have hint := (M.dissipation_integral hw 0).1
  rw [ofReal_integral_eq hint (fun x => sq_nonneg _)]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [enorm_sq_tangent]
  congr 2
  have h0 := congrArg (fun v : Tangent 1 => v 0) hx
  simp only [smoothGrad_apply] at h0
  simp [h0, dlogq]


theorem species_term (b : AbsoluteDrift M.data) (F : SpeciesFamily 1) (s : Fin F.count) :
    ∫⁻ x, ENNReal.ofReal
        (‖(2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • b.force (barycenter F) x‖ ^ 2)
        ∂haar 1 =
      ENNReal.ofReal (∫ x, (2 * F.sqrtGradient s x 0 + (F.density s).sqrt x *
        (-M.dlogq x + M.η * (∫ y, M.φ y ∂(densityMeasure (barycenter F) : Measure (Torus 1))) *
          M.dφ x)) ^ 2 ∂haar 1) := by
  have hw := F.isWeakGradient_sqrtGradient s
  have hint := (M.dissipation_integral hw
    (M.η * ∫ y, M.φ y ∂(densityMeasure (barycenter F) : Measure (Torus 1)))).2.1
  rw [ofReal_integral_eq hint (fun x => sq_nonneg _)]
  refine lintegral_congr_ae ?_
  filter_upwards [M.force_coord b (barycenter F)] with x hx
  congr 1
  rw [norm_sq_tangent]
  simp [hx]

end DGPS.PositiveRankOne.RankOneModel



namespace DGPS.Examples

open DGPS.PositiveRankOne

/-- EX006: positive rank-one gap and family dissipation. -/
theorem positive_rank_one_gap_and_family_dissipation (M : RankOneModel)
    (b : AbsoluteDrift M.data) (F : SpeciesFamily 1) :
    (speciesGap M.data F : ℝ) =
        ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus 1))
          M.ref.measure).toReal +
        M.η / 2 * (∫ x, M.φ x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) ^ 2 ∧
      (∀ s, ordinaryRelativeFisher (densityMeasure (F.density s) : Measure (Torus 1)) M.ref ≠ ⊤) ∧
      speciesDissipation M.data b F ≠ ⊤ ∧
      (speciesDissipation M.data b F).toReal =
        ∑ s, F.weight s *
            (ordinaryRelativeFisher (densityMeasure (F.density s) : Measure (Torus 1)) M.ref).toReal +
          2 * M.η * (∫ x, M.φ x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) *
            (∫ x, M.Aq x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) +
          M.η ^ 2 * (∫ x, M.φ x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) ^ 2 *
            (∫ x, M.dφ x ^ 2 ∂(densityMeasure (barycenter F) : Measure (Torus 1))) := by
  refine ⟨M.gap_eq F, fun s => ?_, ?_⟩
  · rw [M.fisher_eq]; exact ENNReal.ofReal_ne_top
  set m := ∫ y, M.φ y ∂(densityMeasure (barycenter F) : Measure (Torus 1)) with hm
  set K := M.η * m with hK
  -- per-species integral
  have hJ : ∀ s, ∫ x, (2 * F.sqrtGradient s x 0 + (F.density s).sqrt x * (-M.dlogq x + K * M.dφ x)) ^ 2 ∂haar 1 =
      (ordinaryRelativeFisher (densityMeasure (F.density s) : Measure (Torus 1)) M.ref).toReal +
        2 * K * ∫ x, M.Aq x ∂(densityMeasure (F.density s) : Measure (Torus 1)) +
        K ^ 2 * ∫ x, M.dφ x ^ 2 ∂(densityMeasure (F.density s) : Measure (Torus 1)) := by
    intro s
    have hw := F.isWeakGradient_sqrtGradient s
    have hdiss := (M.dissipation_integral hw K).2.2
    have hF : (ordinaryRelativeFisher (densityMeasure (F.density s) : Measure (Torus 1)) M.ref).toReal =
        ∫ x, (2 * F.sqrtGradient s x 0 - (F.density s).sqrt x * M.dlogq x) ^ 2 ∂haar 1 := by
      rw [M.fisher_eq, ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg _)]
      refine integral_congr_ae ?_
      filter_upwards [(isWeakGradient_weakGradient (F.density s).sqrt_mem).ae_eq hw] with x hx
      rw [hx]
    rw [hdiss, hF, RankOneModel.integral_densityMeasure, RankOneModel.integral_densityMeasure]
    rfl
  have hnn : ∀ s, 0 ≤ ∫ x, (2 * F.sqrtGradient s x 0 + (F.density s).sqrt x *
      (-M.dlogq x + K * M.dφ x)) ^ 2 ∂haar 1 := fun s => integral_nonneg fun x => sq_nonneg _
  have hD : speciesDissipation M.data b F = ENNReal.ofReal (∑ s, F.weight s *
      ∫ x, (2 * F.sqrtGradient s x 0 + (F.density s).sqrt x * (-M.dlogq x + K * M.dφ x)) ^ 2 ∂haar 1) := by
    unfold speciesDissipation
    rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => mul_nonneg (F.weight_nonneg s) (hnn s))]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [M.species_term b F s, ENNReal.ofReal_mul (F.weight_nonneg s)]
  refine ⟨by rw [hD]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [hD, ENNReal.toReal_ofReal (Finset.sum_nonneg fun s _ => mul_nonneg (F.weight_nonneg s) (hnn s))]
  have hA := RankOneModel.integral_barycenter F M.Aq_cont
  have hS := RankOneModel.integral_barycenter F (f := fun x => M.dφ x ^ 2) (M.dφ_cont.pow 2)
  have e : ∀ s, F.weight s * (∫ x, (2 * F.sqrtGradient s x 0 + (F.density s).sqrt x *
      (-M.dlogq x + K * M.dφ x)) ^ 2 ∂haar 1) =
      F.weight s * (ordinaryRelativeFisher (densityMeasure (F.density s) : Measure (Torus 1)) M.ref).toReal +
        2 * K * (F.weight s * ∫ x, M.Aq x ∂(densityMeasure (F.density s) : Measure (Torus 1))) +
        K ^ 2 * (F.weight s * ∫ x, M.dφ x ^ 2 ∂(densityMeasure (F.density s) : Measure (Torus 1))) := by
    intro s; rw [hJ s]; ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hA, ← hS]
  simp only [hK]
  ring

/-- The scalar case is the one-species family `SpeciesFamily.single ρ`, not a separate definition. -/
theorem positive_rank_one_scalar_case (M : RankOneModel) (b : AbsoluteDrift M.data)
    (ρ : AbsoluteDensity 1) :
    (speciesGap M.data (SpeciesFamily.single ρ) : ℝ) =
        (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) M.ref.measure).toReal +
        M.η / 2 * (∫ x, M.φ x ∂(densityMeasure ρ : Measure (Torus 1))) ^ 2 ∧
      ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) M.ref ≠ ⊤ ∧
      speciesDissipation M.data b (SpeciesFamily.single ρ) ≠ ⊤ ∧
      (speciesDissipation M.data b (SpeciesFamily.single ρ)).toReal =
        (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) M.ref).toReal +
          2 * M.η * (∫ x, M.φ x ∂(densityMeasure ρ : Measure (Torus 1))) *
            (∫ x, M.Aq x ∂(densityMeasure ρ : Measure (Torus 1))) +
          M.η ^ 2 * (∫ x, M.φ x ∂(densityMeasure ρ : Measure (Torus 1))) ^ 2 *
            (∫ x, M.dφ x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))) := by
  have h := positive_rank_one_gap_and_family_dissipation M b (SpeciesFamily.single ρ)
  have bar : ∀ (f : Torus 1 → ℝ), Continuous f →
      ∫ x, f x ∂(densityMeasure (barycenter (SpeciesFamily.single ρ)) : Measure (Torus 1)) =
        ∫ x, f x ∂(densityMeasure ρ : Measure (Torus 1)) := fun f hf => by
    rw [RankOneModel.integral_barycenter _ hf]
    show ∑ _s : Fin 1, (1 : ℝ) * ∫ x, f x ∂(densityMeasure ρ : Measure (Torus 1)) = _
    simp
  rw [bar _ M.φ_cont, bar _ M.Aq_cont, bar (fun x => M.dφ x ^ 2) (M.dφ_cont.pow 2)] at h
  have hs : ∀ g : Fin (SpeciesFamily.single ρ).count → ℝ,
      ∑ s, (SpeciesFamily.single ρ).weight s * g s = g 0 := fun g => by
    show ∑ s : Fin 1, (1 : ℝ) * g s = g 0
    rw [Fin.sum_univ_one, one_mul]; rfl
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, h2 0, h3, ?_⟩
  · rw [h1, hs fun s => (relativeEntropy (densityMeasure ((SpeciesFamily.single ρ).density s) :
      Measure (Torus 1)) M.ref.measure).toReal]
    rfl
  · rw [h4, hs fun s => (ordinaryRelativeFisher (densityMeasure ((SpeciesFamily.single ρ).density s) :
      Measure (Torus 1)) M.ref).toReal]
    rfl

end DGPS.Examples
