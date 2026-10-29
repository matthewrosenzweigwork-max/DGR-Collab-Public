import DGRHS.Gaussian.PeriodicD11Centered
import DGRHS.Gaussian.PeriodicSupercriticalPressure

noncomputable section
open MeasureTheory Set Filter Real
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic

theorem periodic_d11_positive_pressure (β : ℝ)
    (hβs : (8653/8680:ℝ)*periodicStabilityThreshold (Fin 11)≤β) (hβd : β<22) :
    (∀ N : ℕ,1≤N → periodicAttractivePartition (ι := Fin 11) β N<∞) ∧
      0<liminf (periodicPressure (ι := Fin 11) β) atTop := by
  have hβ0 : 0≤β := (mul_nonneg (by norm_num) periodicStabilityThreshold_pos.le).trans hβs
  have hβdim : β<2*(Fintype.card (Fin 11):ℝ) := by convert hβd using 1 <;> norm_num
  refine ⟨fun N hN => (periodicAttractivePartition_finite_upper β hβ0 hβdim N hN).2,?_⟩
  obtain ⟨c,A,hc,hlo⟩ := periodic_d11_exponential_lower β hβs
  obtain ⟨M,hM⟩ := exists_nat_gt (2*|A|/c)
  have hev : ∀ᶠ N : ℕ in atTop,c/2≤periodicPressure (ι := Fin 11) β N := by
    filter_upwards [eventually_ge_atTop (max 1 M)] with N hN
    have hN1 : 1≤N := (le_max_left _ _).trans hN
    have hNM : M≤N := (le_max_right _ _).trans hN
    have hn : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
    have hnm : (M:ℝ)≤N := by exact_mod_cast hNM
    have hMc : 2*|A|<(M:ℝ)*c := (div_lt_iff₀ hc).mp hM
    have hfin := (periodicAttractivePartition_finite_upper β hβ0 hβdim N hN1).2
    have he := ENNReal.toReal_mono hfin.ne (hlo N hN1)
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at he
    have hlog := Real.log_le_log (Real.exp_pos _) he
    rw [Real.log_exp] at hlog
    unfold periodicPressure
    apply (le_div_iff₀ hn).mpr
    nlinarith [le_abs_self A,mul_le_mul_of_nonneg_right hnm hc.le]
  have hup : ∀ᶠ N : ℕ in atTop,periodicPressure (ι := Fin 11) β N≤
      Real.log (periodicGreenExponentialMass (ι := Fin 11) (β/2)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (periodicPressure_bounds β hβ0 hβdim N hN).2
  exact (by positivity : (0:ℝ)<c/2).trans_le
    (le_liminf_of_le (isCoboundedUnder_ge_of_eventually_le atTop hup) hev)

theorem periodic_d11_critical_exponential_lower :
    ∃ c A : ℝ,0<c ∧ ∀ N : ℕ,1≤N →
      ENNReal.ofReal (Real.exp ((N:ℝ)*c-A))≤
        periodicAttractivePartition (ι := Fin 11) (periodicStabilityThreshold (Fin 11)) N := by
  apply periodic_d11_exponential_lower
  nlinarith [periodicStabilityThreshold_pos (ι := Fin 11)]

theorem periodic_d11_critical_pressure :
    (∀ N : ℕ,1≤N → periodicAttractivePartition (ι := Fin 11) (periodicStabilityThreshold (Fin 11)) N<∞) ∧
      0<liminf (periodicPressure (ι := Fin 11) (periodicStabilityThreshold (Fin 11))) atTop := by
  exact periodic_d11_positive_pressure _ (by nlinarith [periodicStabilityThreshold_pos (ι := Fin 11)])
    periodicStabilityThreshold_eleven_lt

theorem periodic_d11_strict_ratio_witness : ∃ β : ℝ,0<β ∧
    β<(8653/8673:ℝ)*periodicStabilityThreshold (Fin 11) ∧
    β<periodicStabilityThreshold (Fin 11) ∧ β<22 ∧
    (∀ N : ℕ,1≤N → periodicAttractivePartition (ι := Fin 11) β N<∞) ∧
    0<liminf (periodicPressure (ι := Fin 11) β) atTop := by
  let β : ℝ := (8653/8680:ℝ)*periodicStabilityThreshold (Fin 11)
  have hS := periodicStabilityThreshold_pos (ι := Fin 11)
  have hβ : β<22 := by dsimp [β]; nlinarith [periodicStabilityThreshold_eleven_lt]
  refine ⟨β,mul_pos (by norm_num) hS,?_,?_,hβ,periodic_d11_positive_pressure β le_rfl hβ⟩
  · dsimp [β]; nlinarith
  · dsimp [β]; nlinarith

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_d11_positive_pressure
#print axioms DGRHS.Periodic.periodic_d11_critical_exponential_lower
#print axioms DGRHS.Periodic.periodic_d11_critical_pressure
#print axioms DGRHS.Periodic.periodic_d11_strict_ratio_witness
#check @DGRHS.Periodic.periodic_d11_positive_pressure
#check @DGRHS.Periodic.periodic_d11_critical_exponential_lower
#check @DGRHS.Periodic.periodic_d11_critical_pressure
#check @DGRHS.Periodic.periodic_d11_strict_ratio_witness
