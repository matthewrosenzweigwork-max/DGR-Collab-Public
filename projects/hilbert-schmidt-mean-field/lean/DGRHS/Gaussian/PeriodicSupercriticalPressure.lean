import DGRHS.Gaussian.PeriodicPartitionFinite
import Mathlib.Order.LiminfLimsup

/-! Finite real pressure and the original strict supercritical liminf.
Properness and the upper bound are proved first, so ENNReal.toReal cannot
silently turn an infinite partition into zero. -/
noncomputable section
open MeasureTheory Set Filter Real
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicPressure (β : ℝ) (N : ℕ) : ℝ :=
  Real.log ((periodicAttractivePartition (ι := ι) β N).toReal)/(N:ℝ)

lemma periodicGreenExponentialMass_ge_one (γ : ℝ) (hγ0 : 0≤γ) (hγd : γ<(Fintype.card ι:ℝ)) :
    1≤periodicGreenExponentialMass (ι := ι) γ := by
  have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall (fun _ => mem_univ _)) (periodicLogKernel_integrable.const_mul γ)
    (periodicLogKernel_exp_integrable γ hγ0 hγd)
  simpa only [integral_const_mul,periodicLogKernel_integral_zero,mul_zero,Real.exp_zero,periodicGreenExponentialMass] using h

lemma periodicAttractivePartition_ge_one (β : ℝ) (N : ℕ) (hN : 1≤N) :
    1≤periodicAttractivePartition (ι := ι) β N := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h := periodic_cosine_trial_partition_lower i 0 β (by norm_num) N hN
  simpa [periodicCosineTrialDensity] using h

lemma periodicAttractivePartition_toReal_bounds (β : ℝ) (hβ0 : 0≤β)
    (hβd : β<2*(Fintype.card ι:ℝ)) (N : ℕ) (hN : 1≤N) :
    1≤(periodicAttractivePartition (ι := ι) β N).toReal ∧
      (periodicAttractivePartition (ι := ι) β N).toReal≤(periodicGreenExponentialMass (ι := ι) (β/2))^(N-1) := by
  have hfin := periodicAttractivePartition_finite_upper β hβ0 hβd N hN
  have hQ := periodicGreenExponentialMass_ge_one (ι := ι) (β/2) (by positivity) (by linarith)
  constructor
  · simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hfin.2.ne (periodicAttractivePartition_ge_one β N hN)
  · have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfin.1
    simpa only [ENNReal.toReal_ofReal (pow_nonneg (by linarith : 0≤periodicGreenExponentialMass (ι := ι) (β/2)) _)] using h

lemma periodicPressure_bounds (β : ℝ) (hβ0 : 0≤β)
    (hβd : β<2*(Fintype.card ι:ℝ)) (N : ℕ) (hN : 1≤N) :
    0≤periodicPressure (ι := ι) β N ∧
      periodicPressure (ι := ι) β N≤Real.log (periodicGreenExponentialMass (ι := ι) (β/2)) := by
  have hz := periodicAttractivePartition_toReal_bounds β hβ0 hβd N hN
  have hQ := periodicGreenExponentialMass_ge_one (ι := ι) (β/2) (by positivity) (by linarith)
  have hn : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hlQ : 0≤Real.log (periodicGreenExponentialMass (ι := ι) (β/2)) := Real.log_nonneg hQ
  have hlog := Real.log_le_log (by linarith : 0<(periodicAttractivePartition (ι := ι) β N).toReal) hz.2
  rw [Real.log_pow] at hlog
  unfold periodicPressure
  constructor
  · exact div_nonneg (Real.log_nonneg hz.1) hn.le
  · apply (div_le_iff₀ hn).mpr
    have hNcast : ((N-1:ℕ):ℝ)=(N:ℝ)-1 := by rw [Nat.cast_sub hN,Nat.cast_one]
    rw [hNcast] at hlog
    nlinarith

/-- The strict source supercritical liminf for a genuinely finite real
pressure, with a finite uniform upper bound and actual partition properness. -/
theorem periodic_supercritical_pressure (β : ℝ)
    (hβs : periodicStabilityThreshold ι<β) (hβd : β<2*(Fintype.card ι:ℝ)) :
    (∀ N : ℕ,1≤N → periodicAttractivePartition (ι := ι) β N<∞) ∧
      0<liminf (periodicPressure (ι := ι) β) atTop := by
  have hβ0 : 0≤β := (periodicStabilityThreshold_pos.trans hβs).le
  refine ⟨fun N hN => (periodicAttractivePartition_finite_upper β hβ0 hβd N hN).2,?_⟩
  obtain ⟨c,A,hc,hlo⟩ := exists_periodic_supercritical_exponential_lower β hβs
  obtain ⟨M,hM⟩ := exists_nat_gt (2*|A|/c)
  have hev : ∀ᶠ N : ℕ in atTop,c/2≤periodicPressure (ι := ι) β N := by
    filter_upwards [eventually_ge_atTop (max 1 M)] with N hN
    have hN1 : 1≤N := (le_max_left _ _).trans hN
    have hNM : M≤N := (le_max_right _ _).trans hN
    have hn : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
    have hnm : (M:ℝ)≤N := by exact_mod_cast hNM
    have hMc : 2*|A|<(M:ℝ)*c := (div_lt_iff₀ hc).mp hM
    have hfin := (periodicAttractivePartition_finite_upper β hβ0 hβd N hN1).2
    have he := ENNReal.toReal_mono hfin.ne (hlo N hN1)
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at he
    have hlog := Real.log_le_log (Real.exp_pos _) he
    rw [Real.log_exp] at hlog
    unfold periodicPressure
    apply (le_div_iff₀ hn).mpr
    nlinarith [le_abs_self A,mul_le_mul_of_nonneg_right hnm hc.le]
  have hup : ∀ᶠ N : ℕ in atTop,periodicPressure (ι := ι) β N≤
      Real.log (periodicGreenExponentialMass (ι := ι) (β/2)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (periodicPressure_bounds β hβ0 hβd N hN).2
  exact (by positivity : (0:ℝ)<c/2).trans_le
    (le_liminf_of_le (isCoboundedUnder_ge_of_eventually_le atTop hup) hev)

/-- Exact d>=11 scope of source proposition part(ii), with finite pressure. -/
theorem periodic_supercritical_pressure_source (d : ℕ) (hd : 11≤d) (β : ℝ)
    (hβs : periodicStabilityThreshold (Fin d)<β) (hβd : β<2*(d:ℝ)) :
    letI : NeZero d := ⟨by omega⟩
    (∀ N : ℕ,1≤N → periodicAttractivePartition (ι := Fin d) β N<∞) ∧
      0<liminf (periodicPressure (ι := Fin d) β) atTop := by
  letI : NeZero d := ⟨by omega⟩
  exact periodic_supercritical_pressure β hβs (by simpa only [Fintype.card_fin] using hβd)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicPressure_bounds
#print axioms DGRHS.Periodic.periodic_supercritical_pressure
#print axioms DGRHS.Periodic.periodic_supercritical_pressure_source
#check @DGRHS.Periodic.periodic_supercritical_pressure_source
