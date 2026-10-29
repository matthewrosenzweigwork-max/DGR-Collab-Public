import FullLabeledLSI.Examples.E01b_LaneA
import FullLabeledLSI.Examples.Paper.Sec9DeficitCalc

/-!
# Lemma 9.5, steps L0 and L2: Haar is the minimizer for `harmKernel`; the deficit in real form

Lane C of the Section 9 formalization.  Uses the proved lane-A lemmas `fourier_entropy_bound_proved`,
`msGap_attr_proved`, `msDiss_attr_proved`, `msDiss_ne_top_attr_proved` (E01b).
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL.Ex.Def

open SharpLSI FL.Ex.Reg FL.Ex FL.Ex.SR

/-! ### L0 -/

theorem cosK_zero (k : ℤ) : Reg.cosK k (0 : Torus 1) = 1 := by
  rw [cosK_eq_re]; simp

theorem sinK_zero_eq (k : ℤ) : sinK k (0 : Torus 1) = 0 := by
  rw [sinK_eq_im]; simp

theorem fourier_integral_eq {ρ : Torus 1 → ℝ} (hρ : Integrable ρ (haar 1)) (k : ℕ) :
    ∫ x, fourier (k : ℤ) (x 0) * (ρ x : ℂ) ∂haar 1 =
      ((mcos k ρ : ℝ) : ℂ) + ((msin k ρ : ℝ) : ℂ) * Complex.I := by
  have hpt : ∀ x : Torus 1, fourier (k : ℤ) (x 0) * (ρ x : ℂ) =
      ((Reg.cosK k x * ρ x : ℝ) : ℂ) + Complex.I * ((sinK k x * ρ x : ℝ) : ℂ) := by
    intro x
    rw [fourier_eq_cosK_sinK]; push_cast; ring
  simp_rw [hpt]
  rw [integral_add (integrable_cosK_mul hρ k).ofReal ((integrable_sinK_mul hρ k).ofReal.const_mul _),
    integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
  unfold mcos msin
  ring

theorem normSq_fourier {ρ : Torus 1 → ℝ} (hρ : Integrable ρ (haar 1)) (k : ℕ) :
    Complex.normSq (∫ x, fourier (k : ℤ) (x 0) * (ρ x : ℂ) ∂haar 1) =
      mcos k ρ ^ 2 + msin k ρ ^ 2 := by
  rw [fourier_integral_eq hρ k, Complex.normSq_add_mul_I]

/-- `∬ G(x-y) dν dν` for `G = -harmKernel` in terms of the first Fourier modulus. -/
theorem Qint_neg_harm (k : ℕ) (a : ℝ) (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] :
    Sec8.Qint ν (fun x => -harmKernel k a x) =
      -(2 * a) * ((∫ x, Reg.cosK k x ∂ν) ^ 2 + (∫ x, sinK k x ∂ν) ^ 2) := by
  unfold Sec8.Qint
  have hc : ∀ j : ℤ, Integrable (Reg.cosK j) ν := fun j => Sec8.integrable_cont_meas ν (continuous_cosK j)
  have hs : ∀ j : ℤ, Integrable (sinK j) ν := fun j => Sec8.integrable_cont_meas ν (continuous_sinK j)
  have hinner : ∀ y, ∫ x, -harmKernel k a (x - y) ∂ν =
      -(2 * a) * ((∫ x, Reg.cosK k x ∂ν) * Reg.cosK k y + (∫ x, sinK k x ∂ν) * sinK k y) := by
    intro y
    have e : ∀ x, -harmKernel k a (x - y) =
        -(2 * a) * (Reg.cosK k y * Reg.cosK k x + sinK k y * sinK k x) := fun x => by
      rw [harmKernel_eq, cosK_sub]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_add ((hc k).const_mul _) ((hs k).const_mul _),
      integral_const_mul, integral_const_mul]
    ring
  simp_rw [hinner]
  rw [integral_const_mul, integral_add ((hc k).const_mul _) ((hs k).const_mul _),
    integral_const_mul, integral_const_mul]
  ring

theorem Fstar_harm {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (_ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Fstar zeroV (attrW (harmKernel k a)) = ((a : ℝ) : EReal) := by
  have hC := goodKernel_harmKernel hk a
  set G : Torus 1 → ℝ := fun x => -harmKernel k a x with hG
  have hGc : Continuous G := (continuous_of_isSmoothT hC.smooth).neg
  have hmean : Sec8.meanT G = 0 := by
    have := hC.meanZero
    simp only [hG, Sec8.meanT, integral_neg]
    have h2 : (volume : Measure (Torus 1)) = haar 1 := rfl
    rw [h2, this]; simp
  have hG0 : G 0 = -(2 * a) := by
    simp only [hG, harmKernel_eq, cosK_zero]; ring
  have hval : (Sec8.meanT G - G 0) / 2 = a := by rw [hmean, hG0]; ring
  have hz : zeroV = fun _ => (0 : ℝ) := rfl
  rw [attrW_eq_WG, hz]
  apply le_antisymm
  · exact (iInf_le (fun ρ : ProbabilityMeasure (Torus 1) =>
      freeEnergy (fun _ => (0 : ℝ)) (Sec8.WG G) ρ) ⟨haar 1, inferInstance⟩).trans
      (le_of_eq ((Sec8.freeEnergy_WG_haar hGc).trans (by rw [hval])))
  · refine le_iInf fun μ => ?_
    have : IsProbabilityMeasure (μ : Measure (Torus 1)) := inferInstance
    rw [Sec8.freeEnergy_WG hGc]
    by_cases hK : klDiv (μ : Measure (Torus 1)) (haar 1) = ⊤
    · rw [hK]
      simp
    · have hac : (μ : Measure (Torus 1)) ≪ haar 1 := (klDiv_ne_top_iff.1 hK).1
      set ρ := densOf (μ : Measure (Torus 1)) with hρ
      have hρ0 : ∀ x, 0 ≤ ρ x := fun x => ENNReal.toReal_nonneg
      have hρ1 : ∫ x, ρ x ∂haar 1 = 1 := integral_densOf_eq_one hac
      have hρi : Integrable ρ (haar 1) := integrable_densOf _
      have hμ : (μ : Measure (Torus 1)) = densMeasure ρ := eq_densMeasure_densOf hac
      have hfe := fourier_entropy_bound_proved hk ρ hρ0 hρ1
      rw [← hμ, normSq_fourier hρi k] at hfe
      set H := (klDiv (μ : Measure (Torus 1)) (haar 1)).toReal with hH
      have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
      have hKH : klDiv (μ : Measure (Torus 1)) (haar 1) = ENNReal.ofReal H :=
        (ENNReal.ofReal_toReal hK).symm
      rw [hKH] at hfe
      have hn : mcos k ρ ^ 2 + msin k ρ ^ 2 ≤ H := (ENNReal.ofReal_le_ofReal_iff hH0).1 hfe
      have hQ := Qint_neg_harm k a (μ : Measure (Torus 1))
      have e1 : ∫ x, Reg.cosK k x ∂(μ : Measure (Torus 1)) = mcos k ρ :=
        (integral_densOf_mul hac (Reg.cosK k)).symm
      have e2 : ∫ x, sinK k x ∂(μ : Measure (Torus 1)) = msin k ρ :=
        (integral_densOf_mul hac (sinK k)).symm
      rw [e1, e2] at hQ
      rw [← EReal.coe_ennreal_toReal hK, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have hQ' : Sec8.Qint (μ : Measure (Torus 1)) G = -(2 * a) * (mcos k ρ ^ 2 + msin k ρ ^ 2) := hQ
      rw [hQ', hG0]
      have hn0 : 0 ≤ mcos k ρ ^ 2 + msin k ρ ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right ha1 hn0]

theorem harmKernel_isMinimizer {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    IsMinimizer zeroV (attrW (harmKernel k a)) haarPM := by
  have hC := goodKernel_harmKernel hk a
  set G : Torus 1 → ℝ := fun x => -harmKernel k a x with hG
  have hGc : Continuous G := (continuous_of_isSmoothT hC.smooth).neg
  have hmean : Sec8.meanT G = 0 := by
    have := hC.meanZero
    simp only [hG, Sec8.meanT, integral_neg]
    have h2 : (volume : Measure (Torus 1)) = haar 1 := rfl
    rw [h2, this]; simp
  have hG0 : G 0 = -(2 * a) := by
    simp only [hG, harmKernel_eq, cosK_zero]; ring
  unfold IsMinimizer
  rw [Fstar_harm hk ha0 ha1, attrW_eq_WG]
  have hz : zeroV = fun _ => (0 : ℝ) := rfl
  rw [hz]
  have := Sec8.freeEnergy_WG_haar (d := 1) hGc
  have hv : ((0 : ℝ) - -(2 * a)) / 2 = a := by ring
  rw [hmean, hG0, hv] at this
  exact this

/-! ### L2: the deficit in real form -/

/-- `J_r(q) = I(q|m) - 2r H(q|m)` in real form. -/
noncomputable def Jfun (r : ℝ) (q : Torus 1 → ℝ) : ℝ :=
  (fisherInfo (densMeasure q) (haar 1)).toReal - 2 * r * (klDiv (densMeasure q) (haar 1)).toReal

theorem klDiv_ne_top_adm {ρ : Torus 1 → ℝ} (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1)
    (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) : klDiv (densMeasure ρ) (haar 1) ≠ ⊤ :=
  (circle_quantitative_lsi_aux h0 h1 hH).1

theorem deficit_eq {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (r : ℝ)
    (F : Family 1) (hF : F.Admissible) :
    deficit (attrW (harmKernel k a)) r F =
      ∑ i, F.θ i * Jfun r (F.ρ i) +
        Psi k a r (mcos k F.bar) (msin k F.bar) (mcos (2 * (k : ℤ)) F.bar)
          (msin (2 * (k : ℤ)) F.bar) := by
  have hC := goodKernel_harmKernel hk a
  have hmin := harmKernel_isMinimizer hk ha0 ha1
  have hbar1 := bar_integral' F hF
  have hbari : Integrable F.bar (haar 1) := integrable_of_integral_eq_one' hbar1
  have hθ0 : ∀ i, 0 ≤ F.θ i := fun i => (hF.1 i).le
  have hkl : ∀ i, klDiv (densMeasure (F.ρ i)) (haar 1) ≠ ⊤ := fun i =>
    klDiv_ne_top_adm (hF.2.2 i).1 (hF.2.2 i).2.1 (hF.2.2 i).2.2
  have hSne : (∑ i, ENNReal.ofReal (F.θ i) * klDiv (densMeasure (F.ρ i)) (haar 1) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hkl i)
  have hStoReal : (∑ i, ENNReal.ofReal (F.θ i) * klDiv (densMeasure (F.ρ i)) (haar 1) : ℝ≥0∞).toReal =
      ∑ i, F.θ i * (klDiv (densMeasure (F.ρ i)) (haar 1)).toReal := by
    rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hkl i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hθ0 i)]
  have hgap : (msGap zeroV (attrW (harmKernel k a)) F).toReal =
      (∑ i, F.θ i * (klDiv (densMeasure (F.ρ i)) (haar 1)).toReal) -
        1 / 2 * ∫ x, F.bar x * convT (harmKernel k a) F.bar x ∂haar 1 := by
    rw [msGap_attr_proved hC hmin F hF, ← EReal.coe_ennreal_toReal hSne, ← EReal.coe_sub,
      EReal.toReal_coe, hStoReal]
  have hfin := msDiss_ne_top_attr_proved hC F hF
  unfold deficit
  rw [msDiss_attr_proved hC hmin F hF hfin, hgap]
  have hPhi := Phi_eq hbari hbar1 k a r
  unfold Jfun
  have hJ : ∑ i, F.θ i * ((fisherInfo (densMeasure (F.ρ i)) (haar 1)).toReal -
        2 * r * (klDiv (densMeasure (F.ρ i)) (haar 1)).toReal) =
      ∑ i, F.θ i * (fisherInfo (densMeasure (F.ρ i)) (haar 1)).toReal -
        2 * r * ∑ i, F.θ i * (klDiv (densMeasure (F.ρ i)) (haar 1)).toReal := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hJ, ← hPhi]
  ring

end SharpLSI.FL.Ex.Def
