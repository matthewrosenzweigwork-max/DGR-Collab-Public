import DGRHS.Gaussian.PeriodicFirstShellTilt
import DGRHS.Gaussian.PeriodicTrialProductLaw

/-! Exact first-shell tilted iid Radon--Nikodym product law and spatial
residual lower bound. Actual normalizers and densities are constructed;
there is no desired residual moment or product-law premise. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicResidualParticleExponent (β : ℝ) (N : ℕ) (x : Fin N → PeriodicTorus ι) : ℝ :=
  β/(2*(N:ℝ))*∑ i,∑ j,if i=j then 0 else periodicFirstShellResidualPair (x i,x j)

lemma periodicResidualParticleExponent_measurable (β : ℝ) (N : ℕ) :
    Measurable (periodicResidualParticleExponent (ι := ι) β N) := by
  have hR : Measurable (periodicFirstShellResidualPair (ι := ι)) :=
    (periodicLogKernel_measurable.comp (measurable_fst.sub measurable_snd)).sub periodicFirstShellPair_continuous.measurable
  unfold periodicResidualParticleExponent
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  by_cases hij : i=j
  · simp only [hij,if_true];exact measurable_const
  · simp only [hij,if_false]
    exact hR.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))

lemma periodic_firstShell_tilt_particle_law (t : ℝ) (z : ι × Bool → ℝ) (N : ℕ) :
    Measure.pi (fun _ : Fin N => periodicBoundedDensityLaw (periodicFirstShellTiltDensity t z)) =
      (Measure.pi (fun _ : Fin N => periodicHaar ι)).withDensity
        (fun x => ENNReal.ofReal (∏ i,periodicFirstShellTiltDensity t z (x i))) := by
  have hf := periodicFirstShellTiltDensity_measurable t z
  have hi : Integrable (periodicFirstShellTiltDensity t z) (periodicHaar ι) :=
    (integrable_const (Real.exp (periodicFirstShellFieldBound t z)/periodicFirstShellNormalizer t z)).mono'
      hf.aestronglyMeasurable (Eventually.of_forall (periodicFirstShellTiltDensity_bound t z))
  have hp := periodicBoundedDensityLaw_probability _ hi
    (fun x => (periodicFirstShellTiltDensity_pos t z x).le) (periodicFirstShellTiltDensity_integral t z)
  exact finite_product_withDensity_ofReal (periodicHaar ι)
    (fun _ : Fin N => periodicFirstShellTiltDensity t z) (fun _ => hf) (fun _ => hi)
    (fun _ x => (periodicFirstShellTiltDensity_pos t z x).le) (fun _ => hp)

lemma periodic_firstShell_weight_product (t : ℝ) (z : ι × Bool → ℝ) (N : ℕ)
    (x : Fin N → PeriodicTorus ι) :
    (∏ i,periodicFirstShellWeight t z (x i)) = periodicFirstShellNormalizer t z^N*
      (∏ i,periodicFirstShellTiltDensity t z (x i)) := by
  have he (i : Fin N) : periodicFirstShellWeight t z (x i)=periodicFirstShellNormalizer t z*
      periodicFirstShellTiltDensity t z (x i) := by
    unfold periodicFirstShellTiltDensity
    rw [mul_div_cancel₀ _ (periodicFirstShellNormalizer_pos t z).ne']
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp

/-- The actual spatial first-shell weighted residual integral dominates the
N-th power of its true normalizer, by the proper tilted iid mean and Jensen. -/
theorem periodic_firstShell_weighted_residual_lower (t : ℝ) (z : ι × Bool → ℝ)
    (β : ℝ) (hβ : 0≤β) (N : ℕ) (hN : 1≤N) :
    ENNReal.ofReal (periodicFirstShellNormalizer t z^N) ≤
      ∫⁻ x : Fin N → PeriodicTorus ι,ENNReal.ofReal
        ((∏ i,periodicFirstShellWeight t z (x i))*Real.exp (periodicResidualParticleExponent β N x))
          ∂Measure.pi (fun _ => periodicHaar ι) := by
  let μ := Measure.pi (fun _ : Fin N => periodicHaar ι)
  let P := fun x : Fin N → PeriodicTorus ι => ∏ i,periodicFirstShellTiltDensity t z (x i)
  let U := periodicResidualParticleExponent (ι := ι) β N
  have hP : Measurable P := Finset.measurable_prod _
    (fun i _ => (periodicFirstShellTiltDensity_measurable t z).comp (measurable_pi_apply i))
  have hU : Measurable U := periodicResidualParticleExponent_measurable β N
  have hn : ∀ x,0≤P x := fun x => Finset.prod_nonneg (fun i _ => (periodicFirstShellTiltDensity_pos t z (x i)).le)
  have hres := periodic_firstShell_tilt_residual_lower t z β hβ N hN
  rw [periodic_firstShell_tilt_particle_law] at hres
  change (1:ℝ≥0∞) ≤ ∫⁻ x,ENNReal.ofReal (Real.exp (U x)) ∂μ.withDensity (fun x => ENNReal.ofReal (P x)) at hres
  rw [lintegral_withDensity_eq_lintegral_mul μ hP.ennreal_ofReal (hU.exp.ennreal_ofReal)] at hres
  calc
    _ = ENNReal.ofReal (periodicFirstShellNormalizer t z^N)*1 := by simp
    _ ≤ ENNReal.ofReal (periodicFirstShellNormalizer t z^N)*
        (∫⁻ x,ENNReal.ofReal (P x)*ENNReal.ofReal (Real.exp (U x)) ∂μ) := mul_le_mul_of_nonneg_left hres zero_le
    _ = ∫⁻ x,ENNReal.ofReal (periodicFirstShellNormalizer t z^N)*
        (ENNReal.ofReal (P x)*ENNReal.ofReal (Real.exp (U x))) ∂μ :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne).symm
    _ = _ := by
      apply lintegral_congr
      intro x
      rw [←ENNReal.ofReal_mul (hn x),←ENNReal.ofReal_mul (pow_nonneg (periodicFirstShellNormalizer_pos t z).le N)]
      rw [periodic_firstShell_weight_product]
      congr 1
      ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicResidualParticleExponent_measurable
#print axioms DGRHS.Periodic.periodic_firstShell_tilt_particle_law
#print axioms DGRHS.Periodic.periodic_firstShell_weight_product
#print axioms DGRHS.Periodic.periodic_firstShell_weighted_residual_lower
#check @DGRHS.Periodic.periodic_firstShell_weighted_residual_lower
