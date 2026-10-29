import DGPS.FiniteN.CriticalXYScale
import DGPS.FiniteN.Tools.AngularAssembly
import DGPS.FiniteN.Tools.AuxiliaryTransfer

open MeasureTheory
open scoped ENNReal ContDiff Matrix

/-!
# Critical unrestricted LSI lower bound (FIN030)

For `V = 0` and `W(x,y) = 2(1 - cos 2π(x-y))` (`IsCriticalXY`), `H_N = N - |∑ e^{iθ_i}|²/N`, so the
exact Hubbard law is the one of FIN029 (`D = 2·I`, `h = 0`) with conditional `q_z^{⊗N}`. Hence
`r_N^all ≥ a0 γ / (1 + √N / c₁) ≥ c a0 N^{-1/2}` for every `N ≥ 1`
(`critical_unrestricted_lsi_lower_bound`).

Design notes (R5).
* The XY hypothesis `IsCriticalXY` is stated on the torus lift `torusLift (fun _ => s)`.
* FIN015's `auxiliary_lsi_to_particle_entropy` is consumed through its tail: the one-site classical
  Sobolev hypothesis is proved here directly from `uniform_one_site_von_mises_lsi` with the
  classical carre du champ `criticalClGamma`, avoiding the non-dischargeable `haem` hypothesis.
* `D = diag(2)`, `h = 0`; the mapped auxiliary law equals `criticalAuxiliaryLaw N` by comparing
  two probability measures proportional to `exp(-N ψ)`.
-/

namespace DGPS.FiniteN

open DGPS DGPS.Circle.AngularNormalization DGPS.FiniteN.Tools
  DGPS.FiniteN.Tools.UniformVonMises DGPS.FiniteN.Tools.BoundedComparison
  DGPS.FiniteN.UnitTorusNormalization DGPS.FiniteN.Tools.ConditionalEntropyPinsker
  DGPS.FiniteN.Tools.AngularAssembly DGPS.Circle.BesselMoments

noncomputable def criticalD : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal fun _ => (2 : ℝ)

theorem criticalD_posDef : criticalD.PosDef := by
  unfold criticalD
  simp [Matrix.posDef_diagonal_iff]

theorem criticalD_inv : criticalD⁻¹ = Matrix.diagonal fun _ => (1 / 2 : ℝ) := by
  unfold criticalD
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; norm_num

theorem quadForm_criticalD_inv (v : Fin 2 → ℝ) :
    Hubbard.quadForm criticalD⁻¹ v = (v 0 ^ 2 + v 1 ^ 2) / 2 := by
  rw [criticalD_inv]
  simp [Hubbard.quadForm, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two]
  ring

theorem phi_coe (t : ℝ) : phi (t : AngCircle) = ![Real.cos t, Real.sin t] := by
  have h : ((AddCircle.toCircle (t : AngCircle) : Circle) : ℂ) = Complex.exp (t * Complex.I) := by
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
    congr 2
    field_simp
  unfold phi
  rw [h, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem angEquiv_symm_coe (t : ℝ) :
    angEquiv.symm ((t : ℝ) : AngCircle) = torusLift (fun _ => t / (2 * Real.pi)) := by
  rw [MeasurableEquiv.symm_apply_eq, angEquiv_apply]
  have : (torusLift (fun _ : Fin 1 => t / (2 * Real.pi)) 0) = ((t / (2 * Real.pi) : ℝ) : UnitAddCircle) := rfl
  rw [this, angRescale_mk]
  congr 1
  field_simp


/-- The critical XY interaction data: `V = 0`, `W(x,y) = 2(1 - cos 2π(x-y))`. -/
def IsCriticalXY (A : InteractionData 1) : Prop :=
  (∀ x, A.V x = 0) ∧
    ∀ s t : ℝ, A.W (torusLift fun _ => s) (torusLift fun _ => t) =
      2 * (1 - Real.cos (2 * Real.pi * (s - t)))

theorem angV_critical {A : InteractionData 1} (hA : IsCriticalXY A) :
    angV A = fun _ => (0 : ℝ) := by
  funext θ; exact hA.1 _

theorem angW_critical {A : InteractionData 1} (hA : IsCriticalXY A) (a b : AngCircle) :
    angW A a b = 2 - 2 * (phi a ⬝ᵥ phi b) := by
  induction a using QuotientAddGroup.induction_on with
  | H s =>
  induction b using QuotientAddGroup.induction_on with
  | H t =>
  unfold angW
  rw [angEquiv_symm_coe, angEquiv_symm_coe, hA.2]
  have e : 2 * Real.pi * (s / (2 * Real.pi) - t / (2 * Real.pi)) = s - t := by
    field_simp
  rw [e, Real.cos_sub]
  have h1 : phi (s : AngCircle) = phi (s : AngCircle) := rfl
  have hs := phi_coe s
  have ht := phi_coe t
  rw [hs, ht]
  simp [dotProduct, Fin.sum_univ_two]
  ring

theorem sum_phi_dot (N : ℕ+) (θ : AngParticleSpace N) :
    ∑ i, ∑ j, (phi (θ i) ⬝ᵥ phi (θ j)) =
      Hubbard.fieldSum phi θ ⬝ᵥ Hubbard.fieldSum phi θ := by
  unfold Hubbard.fieldSum
  simp [dotProduct, Finset.sum_mul, Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  congr 1 <;> exact Finset.sum_comm


theorem dot_criticalD (v : Fin 2 → ℝ) : v ⬝ᵥ criticalD *ᵥ v = 2 * (v ⬝ᵥ v) := by
  simp [criticalD, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two]
  ring

theorem angHamiltonian_critical {A : InteractionData 1} (hA : IsCriticalXY A) (N : ℕ+)
    (θ : AngParticleSpace N) :
    angHamiltonian (angV A) (angW A) N θ =
      (N : ℝ) - (Hubbard.fieldSum phi θ ⬝ᵥ Hubbard.fieldSum phi θ) / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  unfold angHamiltonian
  simp_rw [angV_critical hA, angW_critical hA]
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_phi_dot]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem particleWeight_critical (N : ℕ+) (θ : AngParticleSpace N) :
    Hubbard.particleWeight (fun _ : AngCircle => (0 : ℝ)) phi criticalD (fun _ : Fin 2 => (0 : ℝ)) N θ =
      Real.exp ((Hubbard.fieldSum phi θ ⬝ᵥ Hubbard.fieldSum phi θ) / N) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  unfold Hubbard.particleWeight
  rw [dot_criticalD]
  congr 1
  simp
  field_simp

theorem angDensity_critical {A : InteractionData 1} (hA : IsCriticalXY A) (N : ℕ+)
    (θ : AngParticleSpace N) :
    ENNReal.ofReal (angDensity (angV A) (angW A) N θ) =
      ENNReal.ofReal ((angPartition (angV A) (angW A) N)⁻¹ * Real.exp (-(N : ℝ))) *
        ENNReal.ofReal (Hubbard.particleWeight (fun _ : AngCircle => (0 : ℝ)) phi criticalD
          (fun _ : Fin 2 => (0 : ℝ)) N θ) := by
  have hZ : 0 ≤ angPartition (angV A) (angW A) N := integral_nonneg fun _ => (Real.exp_pos _).le
  rw [← ENNReal.ofReal_mul (by positivity), particleWeight_critical]
  congr 1
  unfold angDensity
  rw [angHamiltonian_critical hA, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- classical carre du champ on the circle -/
noncomputable def criticalClGamma (f : AngCircle → ℝ) (θ : AngCircle) : ℝ≥0∞ :=
  ENNReal.ofReal (angDeriv f θ ^ 2)

theorem criticalLogSobolev_oneSite {γ : ℝ} (hγ : 0 < γ)
    (h1 : ∀ (w : E2) (f g : AngCircle → ℝ), IsAngularWeakDeriv f g →
      homogeneousEntropy (vmLaw w) (fun θ => f θ ^ 2) ≤
        ENNReal.ofReal (2 / γ * ∫ θ, g θ ^ 2 ∂(vmLaw w))) (w : E2) :
    LogSobolevAt (vmLaw w) IsSmoothAngular criticalClGamma (2 / γ) := by
  intro f hf
  refine (h1 w f _ (smooth_isWeakDeriv hf)).trans ?_
  have hm := memLp_vmLaw w (smooth_isWeakDeriv hf).memLp_deriv
  rw [ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hm.integrable_sq (ae_of_all _ fun _ => sq_nonneg _)]
  rfl

theorem criticalClassicalProductLSI {γ : ℝ} (hγ : 0 < γ)
    (h1 : ∀ (w : E2) (f g : AngCircle → ℝ), IsAngularWeakDeriv f g →
      homogeneousEntropy (vmLaw w) (fun θ => f θ ^ 2) ≤
        ENNReal.ofReal (2 / γ * ∫ θ, g θ ^ 2 ∂(vmLaw w))) (N : ℕ+) :
    ClassicalProductLSI N γ := by
  intro w F hF
  have hF' : ContDiff ℝ ∞ (liftAng F) := hF
  have hdens : ∀ i x, dens criticalClGamma F i x =
      ENNReal.ofReal (angParticlePartial i F x ^ 2) := by
    intro i x
    unfold dens criticalClGamma
    rw [angParticlePartial_eq_angDeriv_slice hF i x]
  have hT : TP IsSmoothAngular criticalClGamma (fun _ : Fin N => vmLaw w) F :=
    { meas := measurable_liftAng_comp hF
      memLp := memLp_of_smooth hF _
      sm := fun x i => isSmoothAngular_slice hF' i x
      aem := fun i => by
        have : dens criticalClGamma F i = fun x => ENNReal.ofReal (angParticlePartial i F x ^ 2) :=
          funext (hdens i)
        rw [this]
        exact ((measurable_angParticlePartial i).pow_const 2).ennreal_ofReal.aemeasurable }
  have := logSobolev_tensorization (fun _ : Fin N => vmLaw w)
    (fun _ => criticalLogSobolev_oneSite hγ h1 w) F hT
  refine this.trans (le_of_eq ?_)
  congr 1
  refine lintegral_congr fun x => ?_
  have e : ∀ i, criticalClGamma (slice i F x) (x i) = ENNReal.ofReal (angParticlePartial i F x ^ 2) :=
    fun i => hdens i x
  simp_rw [e]
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]


theorem criticalRate_of_classical (A : InteractionData 1) (N : ℕ+)
    {D : Matrix (Fin 2) (Fin 2) ℝ} (hD : D.PosDef) (h : Fin 2 → ℝ)
    (hP : angParticleLaw (angV A) (angW A) N =
      Hubbard.hubbardParticleLaw D h (fun _ : AngCircle => (0 : ℝ)) phi angHaar N)
    {γ lam : ℝ} (hγ : 0 < γ) (hlam : 0 < lam) (hcl : ClassicalProductLSI N γ)
    (haux : StrongConvexityLSI.HasLSIRate
      ((Hubbard.auxLaw D h (fun _ : AngCircle => (0 : ℝ)) phi angHaar N).map
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))) lam) :
    ENNReal.ofReal (a0 * γ / (1 + (N : ℝ) / lam)) ≤ particleRateAll A N := by
  have hc : 0 < 2 / γ * (1 + (N : ℝ) / lam) := by positivity
  set c : ℝ := 2 / γ * (1 + (N : ℝ) / lam) with hcdef
  have hsm : ∀ ψ : AngParticleSpace N → ℝ, IsSmoothAngParticle ψ →
      homogeneousEntropy (angParticleLaw (angV A) (angW A) N) (fun x => ψ x ^ 2) ≤
        ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (∑ i, angParticlePartial i ψ x ^ 2)
          ∂angParticleLaw (angV A) (angW A) N := by
    intro ψ hψ
    rw [hP]
    exact smooth_entropy_le hD h hγ hlam hcl haux hψ
  have hK := smooth_periodic_entropy_le A hc.le hsm
  have h2 : ∀ f : ParticleH1 A N,
      particleEntropy A N f ≤ ENNReal.ofReal (c / a0 * particleEnergy A N f) :=
    fun f => (fixed_n_weighted_sobolev_extension A N).2.1 (c / a0) hK f
  refine le_iInf fun f => ?_
  have hf := f.2
  unfold particleQuotient
  rw [ENNReal.le_div_iff_mul_le (Or.inl hf.ne') (Or.inr ENNReal.ofReal_ne_top)]
  calc ENNReal.ofReal (a0 * γ / (1 + (N : ℝ) / lam)) * particleEntropy A N f.1
      ≤ ENNReal.ofReal (a0 * γ / (1 + (N : ℝ) / lam)) *
          ENNReal.ofReal (c / a0 * particleEnergy A N f.1) := by
        gcongr
        exact h2 f.1
    _ = ENNReal.ofReal (2 * particleEnergy A N f.1) := by
        have ha := a0_pos
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hcdef]
        field_simp [a0_pos.ne']


theorem eq_of_prob_smul {α : Type*} [MeasurableSpace α] {ν : Measure α} {c₁ c₂ : ℝ≥0∞}
    (h₁ : IsProbabilityMeasure (c₁ • ν)) (h₂ : IsProbabilityMeasure (c₂ • ν)) :
    c₁ • ν = c₂ • ν := by
  have e₁ : c₁ * ν Set.univ = 1 := by
    have := h₁.measure_univ
    rwa [Measure.smul_apply, smul_eq_mul] at this
  have e₂ : c₂ * ν Set.univ = 1 := by
    have := h₂.measure_univ
    rwa [Measure.smul_apply, smul_eq_mul] at this
  rw [ENNReal.eq_inv_of_mul_eq_one_left e₁, ENNReal.eq_inv_of_mul_eq_one_left e₂]

theorem particleLaw_critical {A : InteractionData 1} (hA : IsCriticalXY A) (N : ℕ+) :
    angParticleLaw (angV A) (angW A) N =
      Hubbard.hubbardParticleLaw criticalD (fun _ : Fin 2 => (0 : ℝ)) (fun _ : AngCircle => (0 : ℝ))
        phi angHaar N := by
  have hP : IsProbabilityMeasure (angParticleLaw (angV A) (angW A) N) := by
    rw [← map_particleLaw A N]
    exact (Measure.isProbabilityMeasure_map_iff (angEquivN N).measurable.aemeasurable).2
      inferInstance
  have hH := AuxiliaryTransfer.isProbabilityMeasure_particleLaw hubbardHyp_angular
    criticalD_posDef (fun _ : Fin 2 => (0 : ℝ)) N
  set ν : Measure (AngParticleSpace N) := (angParticleHaar N).withDensity fun θ =>
    ENNReal.ofReal (Hubbard.particleWeight (fun _ : AngCircle => (0 : ℝ)) phi criticalD
          (fun _ : Fin 2 => (0 : ℝ)) N θ) with hν
  have e1 : angParticleLaw (angV A) (angW A) N =
      ENNReal.ofReal ((angPartition (angV A) (angW A) N)⁻¹ * Real.exp (-(N : ℝ))) • ν := by
    unfold angParticleLaw
    simp_rw [angDensity_critical hA N]
    rw [hν]
    exact withDensity_smul' _ _ ENNReal.ofReal_ne_top
  have e2 : Hubbard.hubbardParticleLaw criticalD (fun _ : Fin 2 => (0 : ℝ))
      (fun _ : AngCircle => (0 : ℝ)) phi angHaar N =
      (Hubbard.particleMass criticalD (fun _ : Fin 2 => (0 : ℝ)) (fun _ : AngCircle => (0 : ℝ))
        phi angHaar N)⁻¹ • ν := rfl
  rw [e1, e2]
  rw [e1] at hP
  rw [e2] at hH
  exact eq_of_prob_smul hP hH

theorem vmCplx_norm (w : EuclideanSpace ℝ (Fin 2)) : vmRadius w = ‖w‖ := by
  unfold vmRadius vmCplx
  rw [EuclideanSpace.norm_eq, Complex.norm_def, Complex.normSq_mk, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq]

theorem vmNorm_eq_bessel (w : EuclideanSpace ℝ (Fin 2)) : vmNorm w = besselI 0 ‖w‖ := by
  have h1 : ∀ θ, vmPhase (EuclideanSpace.single 0 ‖w‖) θ = ‖w‖ * angCos θ := by
    intro θ
    induction θ using QuotientAddGroup.induction_on with
    | H s => 
      rw [vmPhase_coe]
      simp [angCos, angMode_coe]
  have h2 : vmNorm (EuclideanSpace.single 0 ‖w‖) = besselI 0 ‖w‖ := by
    unfold vmNorm besselI
    simp [h1, angMode_zero]
  rw [← h2, vmNorm_eq, vmNorm_eq, vmCplx_norm, vmCplx_norm]
  simp

theorem auxPotential_critical (w : Fin 2 → ℝ) :
    Hubbard.auxPotential (fun _ : AngCircle => (0 : ℝ)) phi criticalD (fun _ : Fin 2 => (0 : ℝ))
        angHaar w = criticalPotential (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 2)) := by
  have hZ : Hubbard.auxPartition (fun _ : AngCircle => (0 : ℝ)) phi angHaar w =
      besselI 0 ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 2))‖ := by
    rw [← vmNorm_eq_bessel]
    unfold Hubbard.auxPartition Hubbard.expTerm vmNorm
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [sub_zero]
    rw [show w ⬝ᵥ phi θ = vmPhase (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 2)) θ from dot_phi _ θ]
  unfold Hubbard.auxPotential criticalPotential criticalPsi
  have hw : w - (fun _ : Fin 2 => (0 : ℝ)) = w := by funext i; simp
  rw [hZ, hw, quadForm_criticalD_inv, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have : 0 ≤ ‖w 0‖ ^ 2 + ‖w 1‖ ^ 2 := by positivity
  rw [Real.sq_sqrt this]
  simp only [Real.norm_eq_abs, sq_abs]
  ring_nf

theorem map_withDensity_toLp (G : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (s : Set (EuclideanSpace ℝ (Fin 2)))
    (hs : MeasurableSet s) :
    ((volume : Measure (Fin 2 → ℝ)).withDensity (fun w => G (WithLp.toLp 2 w))).map
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) s =
      (volume : Measure (EuclideanSpace ℝ (Fin 2))).withDensity G s := by
  have hT := PiLp.volume_preserving_toLp (Fin 2)
  have hemb : MeasurableEmbedding (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding
  rw [Measure.map_apply (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable hs,
    withDensity_apply _ ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable hs),
    withDensity_apply _ hs]
  exact hT.setLIntegral_comp_preimage_emb hemb G s


theorem auxLaw_map_critical (N : ℕ+) :
    (Hubbard.auxLaw criticalD (fun _ : Fin 2 => (0 : ℝ)) (fun _ : AngCircle => (0 : ℝ)) phi
        angHaar N).map (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) = criticalAuxiliaryLaw (N : ℝ) := by
  set G : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (Real.exp (-(N : ℝ) * criticalPotential z)) with hG
  set ν : Measure (EuclideanSpace ℝ (Fin 2)) := volume.withDensity G with hν
  have hF : (fun w : Fin 2 → ℝ => ENNReal.ofReal (Real.exp (-(N : ℝ) *
      Hubbard.auxPotential (fun _ : AngCircle => (0 : ℝ)) phi criticalD
        (fun _ : Fin 2 => (0 : ℝ)) angHaar w))) = fun w => G (WithLp.toLp 2 w) := by
    funext w
    simp only [hG, auxPotential_critical]
  have hmap : ((volume : Measure (Fin 2 → ℝ)).withDensity (fun w : Fin 2 → ℝ =>
      ENNReal.ofReal (Real.exp (-(N : ℝ) *
      Hubbard.auxPotential (fun _ : AngCircle => (0 : ℝ)) phi criticalD
        (fun _ : Fin 2 => (0 : ℝ)) angHaar w)))).map (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) = ν := by
    refine Measure.ext fun s hs => ?_
    rw [hF]
    exact map_withDensity_toLp G s hs
  have e1 : (Hubbard.auxLaw criticalD (fun _ : Fin 2 => (0 : ℝ)) (fun _ : AngCircle => (0 : ℝ)) phi
        angHaar N).map (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) =
      (Hubbard.auxMass criticalD (fun _ : Fin 2 => (0 : ℝ)) (fun _ : AngCircle => (0 : ℝ)) phi
        angHaar N)⁻¹ • ν := by
    unfold Hubbard.auxLaw
    rw [Measure.map_smul, hmap]
    exact (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.aemeasurable
  have hmass : ν Set.univ = Hubbard.auxMass criticalD (fun _ : Fin 2 => (0 : ℝ))
      (fun _ : AngCircle => (0 : ℝ)) phi angHaar N := by
    rw [← hmap, Measure.map_apply (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable MeasurableSet.univ,
      Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rfl
  have hcont : Continuous (criticalPotential (E := EuclideanSpace ℝ (Fin 2))) :=
    (critical_radial_hessian_coercivity (E := EuclideanSpace ℝ (Fin 2))).1.continuous
  have hint : Integrable (fun z : EuclideanSpace ℝ (Fin 2) =>
      Real.exp (-((N : ℝ) * criticalPotential z))) := by
    have hm : AEStronglyMeasurable (fun z : EuclideanSpace ℝ (Fin 2) =>
        Real.exp (-((N : ℝ) * criticalPotential z))) volume :=
      (Real.continuous_exp.comp (continuous_const.mul hcont).neg).aestronglyMeasurable
    rw [← lintegral_ofReal_ne_top_iff_integrable hm (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    have : ∫⁻ z : EuclideanSpace ℝ (Fin 2), ENNReal.ofReal (Real.exp (-((N : ℝ) * criticalPotential z))) = ν Set.univ := by
      rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      simp only [hG, neg_mul]
    rw [this, hmass]
    exact Hubbard.auxMass_ne_top hubbardHyp_angular criticalD_posDef _ N
  have hgib : IsProbabilityMeasure (criticalAuxiliaryLaw (N : ℝ)) :=
    StrongConvexityLSI.gibbs_isProbabilityMeasure hint
  have e2 : criticalAuxiliaryLaw (N : ℝ) = ENNReal.ofReal
      ((∫ y : EuclideanSpace ℝ (Fin 2), Real.exp (-((N : ℝ) * criticalPotential y)))⁻¹) • ν := by
    unfold criticalAuxiliaryLaw StrongConvexityLSI.gibbs
    rw [hν, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext x
    have hZ : 0 ≤ ∫ y : EuclideanSpace ℝ (Fin 2), Real.exp (-((N : ℝ) * criticalPotential y)) :=
      integral_nonneg fun _ => (Real.exp_pos _).le
    simp only [hG, neg_mul, Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (by positivity), div_eq_inv_mul]
  have hP1 : IsProbabilityMeasure ((Hubbard.auxLaw criticalD (fun _ : Fin 2 => (0 : ℝ))
      (fun _ : AngCircle => (0 : ℝ)) phi angHaar N).map (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))) := by
    have := AuxiliaryTransfer.isProbabilityMeasure_auxLaw hubbardHyp_angular criticalD_posDef
      (fun _ : Fin 2 => (0 : ℝ)) N
    exact (Measure.isProbabilityMeasure_map_iff
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.aemeasurable).2 this
  rw [e1, e2]
  rw [e1] at hP1
  rw [e2] at hgib
  exact eq_of_prob_smul hP1 hgib


theorem critical_unrestricted_lsi_lower_bound :
    ∃ γ c : ℝ, 0 < γ ∧ 0 < c ∧ ∀ A : InteractionData 1, IsCriticalXY A → ∀ N : ℕ+,
      ENNReal.ofReal (a0 * γ / (1 + Real.sqrt (N : ℝ) / criticalAuxiliaryRate)) ≤
          particleRateAll A N ∧
        ENNReal.ofReal (c * a0 * (N : ℝ) ^ (-(1 / 2 : ℝ))) ≤ particleRateAll A N := by
  obtain ⟨γ, hγ, h1, -⟩ := uniform_one_site_von_mises_lsi
  have hc1 := criticalAuxiliaryRate_pos
  set c₁ := criticalAuxiliaryRate with hc₁
  refine ⟨γ, γ * c₁ / (c₁ + 1), hγ, by positivity, fun A hA N => ?_⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast N.pos
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := by
    rw [Real.one_le_sqrt]; exact hN1
  set s := Real.sqrt (N : ℝ) with hs
  have hs0 : 0 < s := by linarith
  have hlam : 0 < c₁ * s := by positivity
  have haux : StrongConvexityLSI.HasLSIRate
      ((Hubbard.auxLaw criticalD (fun _ : Fin 2 => (0 : ℝ)) (fun _ : AngCircle => (0 : ℝ)) phi
        angHaar N).map (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))) (c₁ * s) := by
    rw [auxLaw_map_critical N]
    exact (critical_auxiliary_lsi_scale).2.2 (N : ℝ) hN1
  have hmain := criticalRate_of_classical A N criticalD_posDef (fun _ : Fin 2 => (0 : ℝ))
    (particleLaw_critical hA N) hγ hlam (criticalClassicalProductLSI hγ h1 N) haux
  have hNs : (N : ℝ) / (c₁ * s) = s / c₁ := by
    have : (N : ℝ) = s * s := (Real.mul_self_sqrt (by positivity)).symm
    rw [this]; field_simp
  rw [hNs] at hmain
  refine ⟨hmain, le_trans (ENNReal.ofReal_le_ofReal ?_) hmain⟩
  have hp : (N : ℝ) ^ (-(1 / 2 : ℝ)) = s⁻¹ := by
    rw [Real.rpow_neg (by positivity), hs, Real.sqrt_eq_rpow]
  rw [hp]
  have ha := a0_pos
  rw [show a0 * γ / (1 + s / c₁) = a0 * γ * c₁ / (c₁ + s) by field_simp,
    show γ * c₁ / (c₁ + 1) * a0 * s⁻¹ = a0 * γ * c₁ / ((c₁ + 1) * s) by field_simp]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)

end DGPS.FiniteN
