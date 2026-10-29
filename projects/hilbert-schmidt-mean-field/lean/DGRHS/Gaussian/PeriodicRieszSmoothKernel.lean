import DGRHS.Gaussian.PeriodicRieszShortSum
import DGRHS.Gaussian.PeriodicRieszLongKernel
import DGRHS.Gaussian.PeriodicPositiveMellinTail
import DGRHS.Gaussian.PeriodicRieszSingularPartition

/-!
Packet P9h, unit 2 (part 9): the canonical smooth representative of the periodic Riesz kernel.

For a short scale `τ > 0` (heat time `ε = 2π²τ²`) the periodic Riesz kernel `g` of Remark 2.1 is
almost everywhere equal to
`G(z) = F_s K₀ Σ_m ∫_{0<t≤τ} t^{-s-1} e^{-|z+m|²/(2t²)} dt + L_ε(z) - F_s ε^{(d-s)/2} / ((d-s)/2)`
(`F_s` the Mellin factor, `K₀ = periodicRieszProfileConst`), where the first term is the lattice sum of
Gaussian-scale profiles (smooth off the lattice) and `L_ε` the smooth cosine series of heat times
`> ε`.  `periodicRieszSmoothLift s τ` is this function on `ℝ^d`.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The short heat-time cut `ε = 2π²τ²` attached to the scale `τ`. -/
def periodicHeatCut (τ : ℝ) : ℝ := 2 * Real.pi ^ 2 * τ ^ 2

lemma periodicHeatCut_pos {τ : ℝ} (hτ : 0 < τ) : 0 < periodicHeatCut τ := by
  unfold periodicHeatCut; positivity

/-- The canonical smooth representative of the periodic Riesz kernel on `ℝ^d`. -/
def periodicRieszSmoothLift (s τ : ℝ) (z : E) : ℝ :=
  periodicProfileSum (periodicRieszMellinFactor ι s * periodicRieszProfileConst ι s) s (Ioc 0 τ) z +
    periodicRieszLongKernel s (periodicHeatCut τ) z -
    periodicRieszMellinFactor ι s * (periodicHeatCut τ) ^ (((Fintype.card ι : ℝ) - s) / 2) /
      (((Fintype.card ι : ℝ) - s) / 2)

lemma periodicProfileSum_const_mul (c₁ c₂ s : ℝ) (S : Set ℝ) (z : E) :
    c₁ * periodicProfileSum c₂ s S z = periodicProfileSum (c₁ * c₂) s S z := by
  unfold periodicProfileSum periodicProfile
  rw [← tsum_mul_left]
  exact tsum_congr fun m => by ring

/-- Pointwise Mellin identity off the lattice: the Mellin Green function is the short lattice sum
plus the constant plus the physical tail. -/
theorem periodicRieszMellinGreen_off_lattice (s τ : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 < τ) {z : E}
    (hz : z ∈ (periodicOffLattice : Set E)) :
    periodicRieszMellinGreen s 0 (periodicLift z) =
      periodicProfileSum (periodicRieszMellinFactor ι s * periodicRieszProfileConst ι s) s (Ioc 0 τ) z -
        periodicRieszMellinFactor ι s * (periodicHeatCut τ) ^ (((Fintype.card ι : ℝ) - s) / 2) /
          (((Fintype.card ι : ℝ) - s) / 2) +
      periodicRieszPhysicalTail s 0 (periodicHeatCut τ) (periodicLift z) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  unfold periodicHeatCut
  have hε0 : 0 < 2 * Real.pi ^ 2 * τ ^ 2 := by positivity
  obtain ⟨hshort_int, hshort⟩ := periodic_short_heat_integral s τ hs hτ hz
  have hp1 : (-1 : ℝ) < ((Fintype.card ι : ℝ) - s) / 2 - 1 := by linarith
  have htail := periodicRieszMellin_tail_integrable s 0 (2 * Real.pi ^ 2 * τ ^ 2) hs le_rfl hε0
    (periodicLift z)
  unfold periodicRieszMellinGreen periodicUnshiftedMellinHeatGreen periodicRieszPhysicalTail
    periodicRieszMellinTail
  have hexp : ((Fintype.card ι : ℝ) - s) / 2 = (((Fintype.card ι : ℝ) - s) / 2 - 1) + 1 := by ring
  generalize hεdef : 2 * Real.pi ^ 2 * τ ^ 2 = ε at *
  generalize hpdef : ((Fintype.card ι : ℝ) - s) / 2 - 1 = p at *
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
      periodicProfileSum (periodicRieszProfileConst ι s) s (Ioc 0 τ) z - ε ^ (p + 1) / (p + 1) := by
    simp only [add_zero]
    have : (fun u : ℝ => u ^ p * ((periodicGaussianHeat u (periodicLift z)).re - 1)) =
        fun u => u ^ p * (periodicGaussianHeat u (periodicLift z)).re - u ^ p := by
      funext u; ring
    rw [this, integral_sub hshort_int hpint, hshort, hpint']
  rw [← hsplit, hshort', hexp, ← periodicProfileSum_const_mul]
  ring


lemma periodicLift_zero : periodicLift (0 : E) = (0 : PeriodicTorus ι) := by
  funext i
  simp [periodicLift]

lemma periodicRieszLCKernel_lift (s ε : ℝ) (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hε : 0 < ε) (z : E) :
    periodicRieszLCKernel s ε (periodicLift z) = periodicRieszLongKernel s ε z := by
  unfold periodicRieszLCKernel periodicPositiveFourierKernel periodicRieszLongKernel
  rw [Complex.re_tsum]
  · refine tsum_congr fun k => ?_
    rw [Complex.re_ofReal_mul, periodicMFourier_lift_re]
  · apply Summable.of_norm
    have hsum := periodicRieszLCCoeff_summable (ι := ι) s ε hs0 hs2 hε
    simpa only [norm_mul, Complex.norm_real, periodic_mFourier_norm_apply, mul_one,
      Real.norm_of_nonneg (periodicRieszLCCoeff_nonneg s ε hs0 hε.le _)] using hsum

/-- The canonical smooth lift represents the periodic Riesz kernel almost everywhere on the torus. -/
theorem periodicRieszSmoothLift_ae (s τ : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hτ : 0 < τ) :
    (fun x : PeriodicTorus ι => periodicRieszSmoothLift s τ (periodicCenteredLift x)) =ᵐ[periodicHaar ι]
      periodicRieszKernel s hs2 := by
  have h1 := periodicRieszMellinGreen_ae_kernel (ι := ι) s hs2
  have h2 := periodicRieszPhysicalTail_ae_LCKernel (ι := ι) s (periodicHeatCut τ) hs hs2
    (periodicHeatCut_pos hτ)
  have hn := periodicHaar_nullSingletonClass (ι := ι)
  have h3 : ∀ᵐ x ∂periodicHaar ι, x ≠ 0 := (periodicHaar ι).ae_ne 0
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  have hlift : periodicLift (periodicCenteredLift x) = x := periodicLift_centeredLift x
  have hz : periodicCenteredLift x ∈ (periodicOffLattice : Set E) := by
    intro m hm
    apply hx3
    have := congrArg periodicLift hm
    rwa [periodicLift_add_lattice, hlift, periodicLift_zero] at this
  have hid := periodicRieszMellinGreen_off_lattice s τ hs hs2 hτ hz
  rw [hlift] at hid
  have hL := periodicRieszLCKernel_lift s (periodicHeatCut τ) hs hs2 (periodicHeatCut_pos hτ)
    (periodicCenteredLift x)
  rw [hlift] at hL
  unfold periodicRieszSmoothLift
  rw [← hx1, hid, hx2, hL]
  ring


/-- Constant of the lattice-sum part of the smooth lift. -/
def periodicRieszSmoothCoeff (ι : Type u) [Fintype ι] (s : ℝ) : ℝ :=
  periodicRieszMellinFactor ι s * periodicRieszProfileConst ι s

lemma periodicRieszSmoothCoeff_pos (s : ℝ) (hs : 0 < s) : 0 < periodicRieszSmoothCoeff ι s :=
  mul_pos (periodicRieszMellinFactor_pos s hs) (periodicRieszProfileConst_pos s)

lemma periodicRieszSmoothLift_eq (s τ : ℝ) (z : E) :
    periodicRieszSmoothLift s τ z =
      periodicProfileSum (periodicRieszSmoothCoeff ι s) s (Ioc 0 τ) z +
        periodicRieszLongKernel s (periodicHeatCut τ) z -
        periodicRieszMellinFactor ι s * (periodicHeatCut τ) ^ (((Fintype.card ι : ℝ) - s) / 2) /
          (((Fintype.card ι : ℝ) - s) / 2) := rfl

/-- Derivatives of the smooth lift off the lattice (order `n ≥ 1`): lattice sum of the profile
derivatives plus the derivative of the smooth long kernel. -/
theorem periodicRieszSmoothLift_iteratedFDeriv (s τ : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 < τ) (n : ℕ) (hn : 1 ≤ n) {z : E}
    (hz : z ∈ (periodicOffLattice : Set E)) :
    iteratedFDeriv ℝ n (periodicRieszSmoothLift s τ) z =
      ∑' m : PeriodicFrequency ι, iteratedFDeriv ℝ n
          (periodicProfile (periodicRieszSmoothCoeff ι s) s (Ioc 0 τ)) (z + periodicFrequencyVector m) +
        iteratedFDeriv ℝ n (periodicRieszLongKernel (ι := ι) s (periodicHeatCut τ)) z := by
  have hc0 := (periodicRieszSmoothCoeff_pos (ι := ι) s hs).le
  have hP := periodicProfileSum_contDiffAt (ι := ι) (periodicRieszSmoothCoeff ι s) s τ hc0 hs hτ
    (Ioc 0 τ) measurableSet_Ioc (subset_refl _) n hz
  have hL : ContDiffAt ℝ n (periodicRieszLongKernel (ι := ι) s (periodicHeatCut τ)) z :=
    (contDiff_periodicRieszLongKernel s (periodicHeatCut τ) hs hs2 (periodicHeatCut_pos hτ) n).contDiffAt
  have hK : ContDiffAt ℝ n (fun _ : E => periodicRieszMellinFactor ι s *
      (periodicHeatCut τ) ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2)) z :=
    contDiffAt_const
  have hPL : ContDiffAt ℝ n (periodicProfileSum (periodicRieszSmoothCoeff ι s) s (Ioc 0 τ) +
      periodicRieszLongKernel (ι := ι) s (periodicHeatCut τ)) z := hP.add hL
  have he : periodicRieszSmoothLift s τ =
      (periodicProfileSum (periodicRieszSmoothCoeff ι s) s (Ioc 0 τ) +
        periodicRieszLongKernel (ι := ι) s (periodicHeatCut τ)) -
      fun _ : E => periodicRieszMellinFactor ι s *
        (periodicHeatCut τ) ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2) := by
    funext y
    simp only [periodicRieszSmoothLift_eq, Pi.sub_apply, Pi.add_apply]
  rw [he, iteratedFDeriv_sub_apply hPL hK, iteratedFDeriv_add_apply hP hL,
    iteratedFDeriv_const_of_ne (by omega : n ≠ 0), Pi.zero_apply, sub_zero,
    periodicProfileSum_iteratedFDeriv _ s τ hc0 hs hτ (Ioc 0 τ) measurableSet_Ioc (subset_refl _) n hz]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicRieszSmoothLift_ae
#print axioms DGRHS.Periodic.periodicRieszSmoothLift_iteratedFDeriv
