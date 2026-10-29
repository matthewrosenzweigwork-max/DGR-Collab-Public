import DGPS.FiniteN.ScalarFoldFIN060B
import DGPS.FiniteN.ScalarFoldFIN060C
import DGPS.FiniteN.ScalarFoldFIN060E
import DGPS.Circle.AngularNormalization

/-!
# FIN060 (part F): the scalar-cosine model as a Hubbard model

`k = 1`, `U = 0`, `φ = scalarCos`, `D = (κ)`, `m = haar 1`.  We identify the Hubbard auxiliary
partition with `I₀`, the auxiliary potential with `scalarPsi`, the Hubbard particle weight with the
Boltzmann weight of `scalarCosine κ h`, and the auxiliary law (pushed to `ℝ^1`) with `imsEta`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ContDiff ENNReal

namespace DGPS.FiniteN.ScalarFoldFIN060

open DGPS DGPS.Models DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.AuxiliaryTransfer
  DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments

/-- The scalar cosine as a one-component field. -/
noncomputable def phiSFIN060 : Torus 1 → Fin 1 → ℝ := fun x _ => scalarCos x

/-- The trivial single-site potential. -/
def uSFIN060 : Torus 1 → ℝ := fun _ => 0

/-- The Hubbard matrix `D = (κ)`. -/
noncomputable def dSFIN060 (κ : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := Matrix.diagonal fun _ => κ

/-- The external field vector. -/
def hSFIN060 (h : ℝ) : Fin 1 → ℝ := fun _ => h

theorem scalarCos_eq_angCos_FIN060 (x : Torus 1) : scalarCos x = angCos (angEquiv x) := by
  rw [angEquiv_apply]
  unfold scalarCos
  generalize x 0 = s
  induction s using QuotientAddGroup.induction_on with
  | H t =>
    rw [angRescale_mk]
    have : (fourier 1 (t : AddCircle (1 : ℝ))).re = Real.cos (2 * Real.pi * t) := by
      rw [fourier_coe_apply]
      have : (2 * Real.pi * Complex.I * ((1:ℤ) : ℂ) * (t : ℂ) / ((1 : ℝ) : ℂ)) =
          ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.exp_ofReal_mul_I_re]
    rw [this]
    simp [angCos, angMode_coe]

theorem integral_exp_scalarCos_FIN060 (c : ℝ) :
    ∫ x, Real.exp (c * scalarCos x) ∂(haar 1) = besselI 0 c := by
  rw [besselI_zero]
  simp_rw [scalarCos_eq_angCos_FIN060]
  simpa using integral_comp_angEquiv (fun θ => Real.exp (c * angCos θ))

theorem hubbardHyp_FIN060 : HubbardHyp (haar 1) uSFIN060 phiSFIN060 where
  m_ne_zero := (haar_isProbabilityMeasure 1).ne_zero
  U_meas := measurable_const
  U_lower := ⟨0, fun _ => le_rfl⟩
  φ_meas := Measurable.of_eval fun _ => continuous_scalarCos.measurable
  φ_bound := ⟨1, fun x => by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    simpa [phiSFIN060, Real.norm_eq_abs] using scalarCos_bound x⟩

theorem dSFIN060_posDef {κ : ℝ} (hκ : 0 < κ) : (dSFIN060 κ).PosDef := by
  unfold dSFIN060
  simp [Matrix.posDef_diagonal_iff, hκ]

theorem dSFIN060_inv {κ : ℝ} (hκ : 0 < κ) : (dSFIN060 κ)⁻¹ = Matrix.diagonal fun _ => 1 / κ := by
  unfold dSFIN060
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; field_simp

theorem quadForm_dSFIN060_inv {κ : ℝ} (hκ : 0 < κ) (v : Fin 1 → ℝ) :
    quadForm (dSFIN060 κ)⁻¹ v = v 0 ^ 2 / κ := by
  rw [dSFIN060_inv hκ]
  simp [quadForm, Matrix.mulVec_diagonal, dotProduct]
  ring

theorem auxPartition_FIN060 (w : Fin 1 → ℝ) :
    auxPartition uSFIN060 phiSFIN060 (haar 1) w = besselI 0 (w 0) := by
  rw [← integral_exp_scalarCos_FIN060]
  unfold auxPartition expTerm
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [uSFIN060, phiSFIN060, dotProduct]

theorem auxPotential_FIN060 {κ : ℝ} (hκ : 0 < κ) (h : ℝ) (w : Fin 1 → ℝ) :
    auxPotential uSFIN060 phiSFIN060 (dSFIN060 κ) (hSFIN060 h) (haar 1) w =
      scalarPsi κ h (w 0) := by
  unfold auxPotential scalarPsi
  rw [auxPartition_FIN060, quadForm_dSFIN060_inv hκ]
  simp only [hSFIN060, Pi.sub_apply]
  ring

theorem particleWeight_FIN060 (κ h : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    particleWeight uSFIN060 phiSFIN060 (dSFIN060 κ) (hSFIN060 h) N x =
      Real.exp (-particleHamiltonian (scalarCosine κ h) N x) := by
  unfold particleWeight
  rw [scalarCosine_hamiltonian]
  congr 1
  simp [uSFIN060, hSFIN060, fieldSum, phiSFIN060, dSFIN060, dotProduct, Matrix.mulVec_diagonal]
  ring

theorem map_withDensity_toLp_FIN060 (G : E1 → ℝ≥0∞) (s : Set E1) (hs : MeasurableSet s) :
    ((volume : Measure (Fin 1 → ℝ)).withDensity (fun w => G (WithLp.toLp 2 w))).map
        (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)) s =
      (volume : Measure E1).withDensity G s := by
  have hT := PiLp.volume_preserving_toLp (Fin 1)
  have hemb : MeasurableEmbedding (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurableEmbedding
  rw [Measure.map_apply (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurable hs,
    withDensity_apply _ ((MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurable hs),
    withDensity_apply _ hs]
  exact hT.setLIntegral_comp_preimage_emb hemb G s

/-- The auxiliary law of the scalar cosine Hubbard model, transported to `ℝ^1`, is `imsEta`. -/
theorem auxLaw_map_FIN060 {κ : ℝ} (hκ : 0 < κ) (h : ℝ) (N : ℕ+) :
    (auxLaw (dSFIN060 κ) (hSFIN060 h) uSFIN060 phiSFIN060 (haar 1) N).map
        (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)) =
      DGPS.FiniteN.imsEta (N : ℝ) (psiE (scalarPsi κ h)) := by
  set G : E1 → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (Real.exp (-((N : ℝ) * psiE (scalarPsi κ h) z))) with hG
  set ν : Measure E1 := volume.withDensity G with hν
  have hF : (fun w : Fin 1 → ℝ => ENNReal.ofReal (Real.exp (-(N : ℝ) *
      auxPotential uSFIN060 phiSFIN060 (dSFIN060 κ) (hSFIN060 h) (haar 1) w))) =
        fun w => G (WithLp.toLp 2 w) := by
    funext w
    simp only [hG, auxPotential_FIN060 hκ, psiE, neg_mul]
  have hmap : ((volume : Measure (Fin 1 → ℝ)).withDensity (fun w : Fin 1 → ℝ =>
      ENNReal.ofReal (Real.exp (-(N : ℝ) *
      auxPotential uSFIN060 phiSFIN060 (dSFIN060 κ) (hSFIN060 h) (haar 1) w)))).map
        (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)) = ν := by
    refine Measure.ext fun s hs => ?_
    rw [hF]
    exact map_withDensity_toLp_FIN060 G s hs
  have hmass : ν Set.univ = auxMass (dSFIN060 κ) (hSFIN060 h) uSFIN060 phiSFIN060 (haar 1) N := by
    rw [← hmap, Measure.map_apply (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurable
      MeasurableSet.univ, Set.preimage_univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    rfl
  have hint : ∫⁻ x : E1, ENNReal.ofReal (Real.exp (-((N : ℝ) * psiE (scalarPsi κ h) x))) =
      ν Set.univ := by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  unfold auxLaw DGPS.FiniteN.imsEta
  rw [Measure.map_smul, hmap, hint, hmass]
  exact (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurable.aemeasurable

end DGPS.FiniteN.ScalarFoldFIN060
