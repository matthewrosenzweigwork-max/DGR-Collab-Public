import DGRHS.Gaussian.PeriodicLogShortSum
import DGRHS.Gaussian.PeriodicLogLongKernel
import DGRHS.Gaussian.PeriodicRieszSmoothKernel

/-!
Packet P9h, unit 3 (LOG, part 5): the canonical smooth representative of the periodic LOG kernel.

For a short scale `τ > 0` (heat time `ε = 2π²τ²`) the periodic LOG kernel is almost everywhere equal to
`G(z) = F_L K₀ Σ_m P_τ(z+m) + L_ε(z) - F_L ε^{d/2} / (d/2)`, where `P_τ = gaussianLogShortRange τ`,
`F_L = periodicLogMellinFactor`, `K₀ = 2 π^{d/2}`, `L_ε` the smooth cosine series of heat times `> ε`.
(The `s = 0` analogue of `PeriodicRieszSmoothKernel`.)
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The constant of the lattice-sum part of the smooth LOG lift. -/
def periodicLogSmoothCoeff (ι : Type u) [Fintype ι] : ℝ :=
  periodicLogMellinFactor ι * periodicRieszProfileConst ι 0

lemma periodicLogSmoothCoeff_pos : 0 < periodicLogSmoothCoeff ι :=
  mul_pos periodicLogMellinFactor_pos (periodicRieszProfileConst_pos 0)

/-- The canonical smooth representative of the periodic LOG kernel on `ℝ^d`. -/
def periodicLogSmoothLift (τ : ℝ) (z : E) : ℝ :=
  periodicLogSmoothCoeff ι * periodicLogProfileSum τ z + periodicLogLongKernel (periodicHeatCut τ) z -
    periodicLogMellinFactor ι * (periodicHeatCut τ) ^ ((Fintype.card ι : ℝ) / 2) /
      ((Fintype.card ι : ℝ) / 2)

/-- Pointwise Mellin identity off the lattice for the LOG kernel. -/
theorem periodicLogMellinGreen_off_lattice (τ : ℝ) (hτ : 0 < τ) {z : E}
    (hz : z ∈ (periodicOffLattice : Set E)) :
    periodicLogMellinGreen 0 (periodicLift z) =
      periodicLogSmoothCoeff ι * periodicLogProfileSum τ z -
        periodicLogMellinFactor ι * (periodicHeatCut τ) ^ ((Fintype.card ι : ℝ) / 2) /
          ((Fintype.card ι : ℝ) / 2) +
      periodicLogPhysicalTail (periodicHeatCut τ) (periodicLift z) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  unfold periodicHeatCut
  have hε0 : 0 < 2 * Real.pi ^ 2 * τ ^ 2 := by positivity
  obtain ⟨hshort_int, hshort⟩ := periodic_short_heat_integral_log (ι := ι) τ hτ hz
  have hp1 : (-1 : ℝ) < ((Fintype.card ι : ℝ) - 0) / 2 - 1 := by linarith
  have htail := periodicLogTailIntegrand_integrableOn (ι := ι) 0 (2 * Real.pi ^ 2 * τ ^ 2) le_rfl hε0
    (periodicLift z)
  unfold periodicLogMellinGreen periodicUnshiftedMellinHeatGreen periodicLogPhysicalTail
    periodicLogMellinTail periodicLogMellinExponent at *
  have hexp : ((Fintype.card ι : ℝ) / 2) = (((Fintype.card ι : ℝ) - 0) / 2 - 1) + 1 := by ring
  generalize hεdef : 2 * Real.pi ^ 2 * τ ^ 2 = ε at *
  generalize hpdef : ((Fintype.card ι : ℝ) - 0) / 2 - 1 = p at *
  have hpint : IntegrableOn (fun u : ℝ => u ^ p) (Ioc 0 ε) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ε) hp1)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hε0.le).1 this
  have hIoc : IntegrableOn (fun u : ℝ => u ^ p * ((periodicGaussianHeat (u + 0) (periodicLift z)).re - 1))
      (Ioc 0 ε) := by
    have := hshort_int.sub hpint
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioc
    simp only [Pi.sub_apply, add_zero]
    ring
  have hI0 : IntegrableOn (fun u : ℝ => u ^ p * ((periodicGaussianHeat (u + 0) (periodicLift z)).re - 1))
      (Ioi 0) := by
    have := hIoc.union htail
    rwa [Ioc_union_Ioi_eq_Ioi hε0.le] at this
  have hsplit := intervalIntegral.integral_interval_add_Ioi hI0 htail
  rw [intervalIntegral.integral_of_le hε0.le] at hsplit
  have hpint' : (∫ u in Ioc 0 ε, u ^ p) = ε ^ (p + 1) / (p + 1) := by
    rw [← intervalIntegral.integral_of_le hε0.le, integral_rpow (Or.inl hp1),
      Real.zero_rpow (by linarith : p + 1 ≠ 0), sub_zero]
  have hshort' : (∫ u in Ioc 0 ε, u ^ p * ((periodicGaussianHeat (u + 0) (periodicLift z)).re - 1)) =
      periodicRieszProfileConst ι 0 * periodicLogProfileSum τ z - ε ^ (p + 1) / (p + 1) := by
    simp only [add_zero]
    have : (fun u : ℝ => u ^ p * ((periodicGaussianHeat u (periodicLift z)).re - 1)) =
        fun u => u ^ p * (periodicGaussianHeat u (periodicLift z)).re - u ^ p := by
      funext u; ring
    rw [this, integral_sub hshort_int hpint, hshort, hpint']
  have hp1' : p + 1 = (Fintype.card ι : ℝ) / 2 := by rw [← hpdef]; ring
  rw [← hsplit, hshort', hp1']
  unfold periodicLogSmoothCoeff
  ring

lemma periodicLogLCKernel_lift (ε : ℝ) (hε : 0 < ε) (z : E) :
    periodicLogLCKernel ε (periodicLift z) = periodicLogLongKernel ε z := by
  unfold periodicLogLCKernel periodicPositiveFourierKernel periodicLogLongKernel
  rw [Complex.re_tsum]
  · refine tsum_congr fun k => ?_
    rw [Complex.re_ofReal_mul, periodicMFourier_lift_re]
  · apply Summable.of_norm
    have hsum := periodicLogLCCoeff_summable (ι := ι) ε hε
    simpa only [norm_mul, Complex.norm_real, periodic_mFourier_norm_apply, mul_one,
      Real.norm_of_nonneg (periodicLogLCCoeff_nonneg ε hε.le _)] using hsum

/-- The canonical smooth lift represents the periodic LOG kernel almost everywhere on the torus. -/
theorem periodicLogSmoothLift_ae (τ : ℝ) (hτ : 0 < τ) :
    (fun x : PeriodicTorus ι => periodicLogSmoothLift τ (periodicCenteredLift x)) =ᵐ[periodicHaar ι]
      periodicLogKernel := by
  have h1 := periodicLogMellinGreen_ae_kernel (ι := ι)
  have h2 := periodicLogPhysicalTail_ae_LCKernel (ι := ι) (periodicHeatCut τ) (periodicHeatCut_pos hτ)
  have hn := periodicHaar_nullSingletonClass (ι := ι)
  have h3 : ∀ᵐ x ∂periodicHaar ι, x ≠ 0 := (periodicHaar ι).ae_ne 0
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  have hlift : periodicLift (periodicCenteredLift x) = x := periodicLift_centeredLift x
  have hz : periodicCenteredLift x ∈ (periodicOffLattice : Set E) := by
    intro m hm
    apply hx3
    have := congrArg periodicLift hm
    rwa [periodicLift_add_lattice, hlift, periodicLift_zero] at this
  have hid := periodicLogMellinGreen_off_lattice τ hτ hz
  rw [hlift] at hid
  have hL := periodicLogLCKernel_lift (periodicHeatCut τ) (periodicHeatCut_pos hτ)
    (periodicCenteredLift x)
  rw [hlift] at hL
  unfold periodicLogSmoothLift
  rw [← hx1, hid, hx2, hL]
  ring

/-- Derivatives of the smooth LOG lift off the lattice (order `n ≥ 1`): lattice sum of the profile
derivatives plus the derivative of the smooth long kernel. -/
theorem periodicLogSmoothLift_iteratedFDeriv (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (hn : 1 ≤ n) {z : E}
    (hz : z ∈ (periodicOffLattice : Set E)) :
    iteratedFDeriv ℝ n (periodicLogSmoothLift (ι := ι) τ) z =
      periodicLogSmoothCoeff ι • ∑' m : PeriodicFrequency ι,
          iteratedFDeriv ℝ n (gaussianLogShortRange τ) (z + periodicFrequencyVector m) +
        iteratedFDeriv ℝ n (periodicLogLongKernel (ι := ι) (periodicHeatCut τ)) z := by
  have hP := periodicLogProfileSum_contDiffAt (ι := ι) τ hτ n hz
  have hP' : ContDiffAt ℝ n (fun y => periodicLogSmoothCoeff ι * periodicLogProfileSum τ y) z :=
    contDiffAt_const.mul hP
  have hL : ContDiffAt ℝ n (periodicLogLongKernel (ι := ι) (periodicHeatCut τ)) z :=
    (contDiff_periodicLogLongKernel (periodicHeatCut τ) (periodicHeatCut_pos hτ) n).contDiffAt
  have hPL : ContDiffAt ℝ n ((fun y => periodicLogSmoothCoeff ι * periodicLogProfileSum τ y) +
      periodicLogLongKernel (ι := ι) (periodicHeatCut τ)) z := hP'.add hL
  have hK : ContDiffAt ℝ n (fun _ : E => periodicLogMellinFactor ι *
      (periodicHeatCut τ) ^ ((Fintype.card ι : ℝ) / 2) / ((Fintype.card ι : ℝ) / 2)) z :=
    contDiffAt_const
  have he : periodicLogSmoothLift τ =
      ((fun y => periodicLogSmoothCoeff ι * periodicLogProfileSum τ y) +
        periodicLogLongKernel (ι := ι) (periodicHeatCut τ)) -
      fun _ : E => periodicLogMellinFactor ι *
        (periodicHeatCut τ) ^ ((Fintype.card ι : ℝ) / 2) / ((Fintype.card ι : ℝ) / 2) := by
    funext y
    simp only [periodicLogSmoothLift, Pi.sub_apply, Pi.add_apply]
  have hcm : iteratedFDeriv ℝ n (fun y => periodicLogSmoothCoeff ι * periodicLogProfileSum τ y) z =
      periodicLogSmoothCoeff ι • iteratedFDeriv ℝ n (periodicLogProfileSum (ι := ι) τ) z := by
    change iteratedFDeriv ℝ n (periodicLogSmoothCoeff ι • periodicLogProfileSum (ι := ι) τ) z = _
    exact iteratedFDeriv_const_smul_apply hP
  rw [he, iteratedFDeriv_sub_apply hPL hK, iteratedFDeriv_add_apply hP' hL,
    iteratedFDeriv_const_of_ne (by omega : n ≠ 0), Pi.zero_apply, sub_zero, hcm,
    periodicLogProfileSum_iteratedFDeriv τ hτ n hz]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLogSmoothLift_ae
#print axioms DGRHS.Periodic.periodicLogSmoothLift_iteratedFDeriv
