/- Original all-temperature logarithmic partition growth. The sharp iid
energy bound is derived from finite-IR cancellation, not supplied as a
favorable premise. Literal collision weights are identified only after
properness under the genuine iid measure. -/
import DGRHS.Entropy.SourceTemperatureWindow
import DGRHS.Entropy.SourceLogSharpIidFloor
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Entropy

theorem exponential_temperature_growth {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (X : S → ℝ) (B : ℝ) (hB : 0 < B)
    (A C β : ℝ) (hC : 1 ≤ C) (hβ : 0 ≤ β)
    (hupper : ∀ᵐ x ∂μ, X x ≤ A)
    (hiB : Integrable (fun x => Real.exp (B*X x)) μ)
    (hiβ : Integrable (fun x => Real.exp (β*X x)) μ)
    (hcap : (∫ x, Real.exp (B*X x) ∂μ) ≤ C) :
    (∫ x, Real.exp (β*X x) ∂μ) ≤ C*Real.exp (A*max (β-B) 0) := by
  by_cases hb : β ≤ B
  · obtain ⟨_, hout⟩ := exponential_temperature_window μ X B hB hiB C hC hcap β hβ hb
    simpa only [max_eq_right (sub_nonpos.mpr hb), mul_zero, Real.exp_zero, mul_one] using hout
  · have hlarge : 0 ≤ β-B := sub_nonneg.mpr (le_of_lt (lt_of_not_ge hb))
    have hp : ∀ᵐ x ∂μ, Real.exp (β*X x) ≤
        Real.exp (A*(β-B))*Real.exp (B*X x) := by
      filter_upwards [hupper] with x hx
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hx hlarge
      nlinarith
    calc
      _ ≤ ∫ x, Real.exp (A*(β-B))*Real.exp (B*X x) ∂μ :=
        integral_mono_ae hiβ (hiB.const_mul _) hp
      _ = Real.exp (A*(β-B))*(∫ x, Real.exp (B*X x) ∂μ) := integral_const_mul _ _
      _ ≤ Real.exp (A*(β-B))*C := mul_le_mul_of_nonneg_left hcap (Real.exp_pos _).le
      _ = _ := by rw [max_eq_left hlarge]; ring

open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]

theorem sourceLogPartition_all_temperature_growth (B : ℝ≥0) (hB : 0 < (B : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ))) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ β : ℝ≥0, ∀ N : ℕ, 1 ≤ N →
      (sourceLogSingularPartition β ρ N).toReal ≤
        C*Real.exp (C*max ((β : ℝ)-(B : ℝ)) 0*Real.log (Real.exp 1+(N : ℝ))) := by
  obtain ⟨Cb, hCb, hcap⟩ := sourceLogPartition_original_bounds_one_le B hd ρ M hM hρ hpair
  let C0 := 2*gaussianLogShortConstant M ι+1+1/(2*(Fintype.card ι : ℝ))
  have hc := gaussianLogShortConstant_nonneg (ι := ι) M hM hd
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  let C := max Cb C0
  have hC : 1 ≤ C := hCb.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro β N hN
  let μ := gaussianRieszDensityMeasure ρ
  let P := Measure.pi (fun _ : Fin N => μ)
  let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
    (DGRHS.potential μ (fun a b => logPhysicalPair (a,b)))
    (DGRHS.interactionEnergy μ (fun a b => logPhysicalPair (a,b))) N
  let X := fun x => -(N : ℝ)*E x
  let a := Real.log (Real.exp 1+(N : ℝ))
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hnp : 0 < (N : ℝ) := by linarith
  have ha1 : 1 ≤ a := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by linarith)
  have halog : Real.log (N : ℝ) ≤ a :=
    Real.log_le_log hnp (by linarith [Real.exp_pos 1])
  have hiden (x : Fin N → EuclideanSpace ℝ ι) :
      X x = logPhysicalMomentExponent μ 1 N x := by
    rw [sourceLogMomentExponent_eq]
    simpa only [sourceParticleExponent, X, E, neg_one_mul, one_mul] using
      sourceCanonicalModulatedEnergy_exponent (hoeffdingCentered μ logPhysicalPair)
        (DGRHS.potential μ (fun a b => logPhysicalPair (a,b)))
        (DGRHS.interactionEnergy μ (fun a b => logPhysicalPair (a,b))) 1 (by omega) x
  have hupper : ∀ᵐ x ∂P, X x ≤ C0*a := by
    have hconst := mul_le_mul_of_nonneg_left ha1 (by positivity :
      0 ≤ 2*gaussianLogShortConstant M ι+1)
    have hlogterm := div_le_div_of_nonneg_right halog (by positivity :
      0 ≤ 2*(Fintype.card ι : ℝ))
    filter_upwards [logPhysicalMomentExponent_sharp_logN_ae hd ρ M hM hρ hpair N hN] with x hx
    change logPhysicalMomentExponent μ 1 N x ≤
      2*gaussianLogShortConstant M ι+1/8+Real.log (N : ℝ)/(2*(Fintype.card ι : ℝ)) at hx
    rw [hiden]
    dsimp [C0]
    simp only [div_eq_mul_inv] at hlogterm hx ⊢
    nlinarith [hx]
  have he (b : ℝ) : (fun x => Real.exp (b*X x)) =
      (fun x => Real.exp (-b*(N : ℝ)*E x)) := by funext x; congr 1; dsimp [X]; ring
  have hi (b : ℝ) (hb : 0 ≤ b) : Integrable (fun x => Real.exp (b*X x)) P := by
    rw [he]
    exact sourceLogEnergyWeight_integrable b hb hd ρ M hM hρ hpair N
  have hb : (∫ x, Real.exp ((B : ℝ)*X x) ∂P) ≤ Cb := by
    have hh := (hcap N hN).2
    rw [sourceLogSingularPartition_eq_integral B hd ρ M hM hρ hpair N,
      ENNReal.toReal_ofReal (integral_nonneg fun x => (Real.exp_pos _).le)] at hh
    rw [he]
    exact hh
  have hout := exponential_temperature_growth P X (B : ℝ) hB (C0*a) Cb (β : ℝ) hCb
    β.coe_nonneg hupper (hi (B : ℝ) B.coe_nonneg) (hi (β : ℝ) β.coe_nonneg) hb
  rw [he] at hout
  rw [sourceLogSingularPartition_eq_integral β hd ρ M hM hρ hpair N,
    ENNReal.toReal_ofReal (integral_nonneg fun x => (Real.exp_pos _).le)]
  refine hout.trans ?_
  have hex : C0*a*max ((β : ℝ)-(B : ℝ)) 0 ≤ C*max ((β : ℝ)-(B : ℝ)) 0*a := by
    have hh := mul_le_mul_of_nonneg_right (le_max_right Cb C0)
      (mul_nonneg (le_max_right ((β : ℝ)-(B : ℝ)) (0 : ℝ)) (by linarith : 0 ≤ a))
    dsimp [C]
    nlinarith [hh]
  exact mul_le_mul (le_max_left Cb C0) (Real.exp_le_exp.mpr hex)
    (Real.exp_pos _).le (by linarith)

end DGRHS.Entropy
#check @DGRHS.Entropy.exponential_temperature_growth
#check @DGRHS.Entropy.sourceLogPartition_all_temperature_growth
#print axioms DGRHS.Entropy.exponential_temperature_growth
#print axioms DGRHS.Entropy.sourceLogPartition_all_temperature_growth
