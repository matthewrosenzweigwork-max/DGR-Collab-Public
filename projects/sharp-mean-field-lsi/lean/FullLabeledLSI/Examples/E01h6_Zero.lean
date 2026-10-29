import FullLabeledLSI.Examples.E01h6_Core
import SharpSymmetricLSI.Paper.GroundState
import SharpSymmetricLSI.Paper.FourierPoincare

/-!
# Lane D, Task D (E01h6): zero dissipation forces the uniform density (skeleton, to be proved)
-/

open MeasureTheory InformationTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

theorem isSmoothT_exp_neg_half {h : Torus 1 → ℝ} (hh : IsSmoothT h) :
    IsSmoothT (fun y => Real.exp ((-(1/2:ℝ)) * h y)) := by
  unfold IsSmoothT at *
  have : (fun y => Real.exp ((-(1/2:ℝ)) * h y)) ∘ liftT = fun x => Real.exp ((-(1/2:ℝ)) * (h ∘ liftT) x) := rfl
  rw [this]
  exact Real.contDiff_exp.comp (contDiff_const.mul hh)

theorem ae_const_mul_exp {f : Torus 1 → ℝ} (hH : MemH1 (haar 1) f) {h : Torus 1 → ℝ}
    (hh : IsSmoothT h)
    (hder : ∀ᵐ x ∂haar 1, 2 * weakGrad f x 0 = f x * dT h x) :
    ∃ κ : ℝ, ∀ᵐ x ∂haar 1, f x = κ * Real.exp (h x / 2) := by
  set Θ : (Fin 1 → ℝ) → ℝ := fun x => Real.exp ((-(1/2:ℝ)) * (h ∘ liftT) x) with hΘdef
  have hΘ : ContDiff ℝ ∞ Θ := Real.contDiff_exp.comp (contDiff_const.mul hh)
  have hp : IsPer Θ := fun m x => by
    simp only [hΘdef]; rw [isPer_lift h m x]
  have hw := isWeakGrad_weakGrad hH.1
  have hm := hw.mul_smooth hΘ hp
  have hΘs : ∀ y, Θ (secT y) = Real.exp ((-(1/2:ℝ)) * h y) := fun y => by
    simp only [hΘdef, Function.comp_apply, liftT_secT]
  have hDs : ∀ y, Dk Θ 0 (secT y) = -(1/2) * Real.exp ((-(1/2:ℝ)) * h y) * dT h y := by
    intro y
    have hd : Differentiable ℝ (h ∘ liftT) := hh.differentiable (by simp)
    have hfd := ((hd (secT y)).hasFDerivAt.const_mul (-(1/2:ℝ))).exp
    have := hfd.fderiv
    simp only [Dk]
    rw [this]
    simp only [smul_apply, smul_eq_mul]
    rw [fderiv_secT_eq_dT hh y]
    simp only [Function.comp_apply, liftT_secT]
    ring
  have hΦ := isSmoothT_exp_neg_half hh
  have hu2 : MemLp (fun y => f y * Θ (secT y)) 2 volume := by
    have := memLp_two_mul_smooth hH.2.1 hΦ
    refine this.ae_eq (Eventually.of_forall fun y => ?_)
    simp only [hΘs]
  set G : Torus 1 → Fin 1 → ℝ := fun y k => weakGrad f y k * Θ (secT y) + f y * Dk Θ k (secT y)
    with hG
  have hG0 : ∀ᵐ y ∂(volume : Measure (Torus 1)), ∀ j, G y j = 0 := by
    filter_upwards [hder] with y hy j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp only [hG, hΘs, hDs]
    have : weakGrad f y 0 = f y * dT h y / 2 := by linarith
    rw [this]; ring
  have hgL : ∀ j, MemLp (fun y => G y j) 2 volume := fun j =>
    (memLp_const (0:ℝ) : MemLp (fun _ : Torus 1 => (0:ℝ)) 2 volume).ae_eq
      (hG0.mono fun y hy => (hy j).symm)
  have hP := poincare_torus hm hu2 hgL
  have hint : ∀ j, ∫ y, G y j ^ 2 = 0 := fun j => by
    rw [integral_congr_ae (g := fun _ => (0:ℝ)) (hG0.mono fun y hy => by simp [hy j])]
    simp
  simp only [hint, Finset.sum_const_zero] at hP
  have h4 : (0 : ℝ) < 4 * π ^ 2 := by positivity
  have hvar : ProbabilityTheory.variance (fun y => f y * Θ (secT y)) volume = 0 := by
    refine le_antisymm ?_ (ProbabilityTheory.variance_nonneg _ _)
    have : 4 * π ^ 2 * ProbabilityTheory.variance (fun y => f y * Θ (secT y)) volume ≤ 4 * π ^ 2 * 0 := by
      rw [mul_zero]; exact hP
    exact le_of_mul_le_mul_left this h4
  rw [ProbabilityTheory.variance_eq_integral hu2.aestronglyMeasurable.aemeasurable] at hvar
  set m₀ := ∫ y, f y * Θ (secT y)
  have hconst : (fun y => f y * Θ (secT y)) =ᵐ[volume] fun _ => m₀ := by
    have := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (f y * Θ (secT y) - m₀))
      (hu2.sub (memLp_const m₀)).integrable_sq).mp hvar
    filter_upwards [this] with y hy
    simpa [sub_eq_zero] using hy
  refine ⟨m₀, ?_⟩
  filter_upwards [hconst] with y hy
  rw [hΘs] at hy
  have : Real.exp (-(1/2:ℝ) * h y) * Real.exp (h y / 2) = 1 := by
    rw [← Real.exp_add]; convert Real.exp_zero using 2; ring
  calc f y = f y * Real.exp (-(1/2:ℝ) * h y) * Real.exp (h y / 2) := by
        rw [mul_assoc, this]; ring
    _ = _ := by rw [hy]



theorem eq_one_of_densMeasure_eq {ρ : Torus 1 → ℝ} (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) (hμ : densMeasure ρ = haar 1) : ρ =ᵐ[haar 1] fun _ => 1 := by
  have hi := integrable_of_integral_eq_one' h1
  have hm : AEMeasurable (fun x => ENNReal.ofReal (ρ x)) (haar 1) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hi.aestronglyMeasurable.aemeasurable
  have hlin : ∫⁻ x, ENNReal.ofReal (ρ x) ∂haar 1 ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall h0)]
    exact ENNReal.ofReal_ne_top
  have hw : (haar 1 : Measure (Torus 1)).withDensity (fun x => ENNReal.ofReal (ρ x)) =
      (haar 1 : Measure (Torus 1)).withDensity (1 : Torus 1 → ℝ≥0∞) := by
    rw [withDensity_one]; exact hμ
  have h' := (withDensity_eq_iff hm (aemeasurable_const : AEMeasurable (1 : Torus 1 → ℝ≥0∞) (haar 1)) hlin).1 hw
  filter_upwards [h'] with x hx
  exact ENNReal.ofReal_eq_one.1 hx

/-- If `|C| ≤ M` with `2 M < 1` (and `C` good), the only density of zero dissipation is `1`. -/
theorem hzero_of_bound {C : Torus 1 → ℝ} (hC : GoodKernel C) {M : ℝ} (hM : ∀ x, |C x| ≤ M)
    (hM2 : 2 * M < 1) :
    ∀ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) → ∫ x, ρ x ∂haar 1 = 1 →
      dissipation zeroV (attrW C) ρ = 0 → ρ =ᵐ[haar 1] fun _ => 1 := by
  intro ρ h0 h1 hdiss
  haveI := isProbabilityMeasure_densMeasure' h0 h1
  have hρi := integrable_of_integral_eq_one' h1
  have hCc := continuous_of_smooth hC.smooth
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  -- MemH1
  have hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x)) := by
    by_contra hn
    have : dissipation zeroV (attrW C) ρ = ⊤ := by
      unfold dissipation
      rw [if_neg]
      rintro ⟨a, _⟩
      exact hn a
    rw [this] at hdiss
    exact ENNReal.top_ne_zero hdiss
  -- DR = 0
  have hDR : DR C ρ = 0 := by
    have := diss_eq hC h0 h1 hH
    rw [hdiss] at this
    have h2 := ENNReal.ofReal_eq_zero.1 this.symm
    exact le_antisymm h2 (integral_nonneg fun x => sq_nonneg _)
  have hint := integrable_DR_integrand hC h0 h1 hH
  have hae0 : ∀ᵐ x ∂haar 1, (2 * weakGrad (fun y => Real.sqrt (ρ y)) x 0 -
      Real.sqrt (ρ x) * convT (dT C) ρ x) ^ 2 = 0 := by
    have := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hint).1 hDR
    exact this
  -- smooth h
  set h : Torus 1 → ℝ := convT C ρ with hhdef
  have hcs : IsSmoothT h := by
    rw [hhdef, convT_eq_conv h0 h1]; exact isSmoothT_conv hC.smooth _
  have hdh : dT h = convT (dT C) ρ := dT_convT hC h0 h1
  have hder : ∀ᵐ x ∂haar 1, 2 * weakGrad (fun y => Real.sqrt (ρ y)) x 0 =
      Real.sqrt (ρ x) * dT h x := by
    filter_upwards [hae0] with x hx
    rw [hdh]
    have := pow_eq_zero_iff (two_ne_zero) |>.1 hx
    linarith
  obtain ⟨κ, hκ⟩ := ae_const_mul_exp hH hcs hder
  have hhc : Continuous h := continuous_of_smooth hcs
  have hρe : ∀ᵐ x ∂haar 1, ρ x = κ ^ 2 * Real.exp (h x) := by
    filter_upwards [hκ] with x hx
    rw [← Real.sq_sqrt (h0 x), hx, mul_pow, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  set c : ℝ := κ ^ 2 with hc
  have hexpi : Integrable (fun x => Real.exp (h x)) (haar 1) :=
    (Real.continuous_exp.comp hhc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hhi : Integrable h (haar 1) :=
    hhc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hZ : c * ∫ x, Real.exp (h x) ∂haar 1 = 1 := by
    have := integral_congr_ae (μ := haar 1) hρe
    rw [integral_const_mul, h1] at this
    exact this.symm
  have hh0 : ∫ x, h x ∂haar 1 = 0 := integral_convT_eq_zero hC h1
  have hZ1 : 1 ≤ ∫ x, Real.exp (h x) ∂haar 1 := by
    have := integral_mono (f := fun x => 1 + h x) ((integrable_const _).add hhi) hexpi
      (fun x => by simpa [add_comm] using Real.add_one_le_exp (h x))
    rw [integral_add (integrable_const _) hhi, hh0] at this
    simpa using this
  have hc0 : 0 ≤ c := sq_nonneg κ
  have hcpos : 0 < c := by
    rcases hc0.eq_or_lt with h | h
    · rw [← h] at hZ; simp at hZ
    · exact h
  have hc1 : c ≤ 1 := by nlinarith
  have hlogc : Real.log c ≤ 0 := Real.log_nonpos hc0 hc1
  -- entropy
  have hfin := (circle_quantitative_lsi_aux h0 h1 hH).1
  have hρh : Integrable (fun x => ρ x * h x) (haar 1) := by
    obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus 1)).exists_bound_of_continuousOn hhc.continuousOn
    exact hρi.mul_bdd (c := B) hhc.aestronglyMeasurable (Eventually.of_forall fun x => by
      simpa using hB x (Set.mem_univ _))
  have hent : entR ρ = Real.log c + cqR C ρ := by
    unfold entR
    rw [klDiv_toReal_eq_integral h0 h1]
    have e : ∀ᵐ x ∂haar 1, klFun (ρ x) = Real.log c * ρ x + ρ x * h x + (1 - ρ x) := by
      filter_upwards [hρe] with x hx
      rw [klFun_apply]
      have hlog : Real.log (ρ x) = Real.log c + h x := by
        rw [hx, Real.log_mul hcpos.ne' (Real.exp_pos _).ne', Real.log_exp]
      rw [hlog]; ring
    rw [integral_congr_ae e]
    have i1 : Integrable (fun x => Real.log c * ρ x) (haar 1) := hρi.const_mul _
    have i2 : Integrable (fun x => 1 - ρ x) (haar 1) := (integrable_const _).sub hρi
    have i12 : Integrable (fun x => Real.log c * ρ x + ρ x * h x) (haar 1) := i1.add hρh
    rw [integral_add i12 i2, integral_add i1 hρh, integral_sub (integrable_const _) hρi,
      integral_const_mul, h1]
    simp [cqR, hhdef]
  have hcq := cqR_le_ent hC hM h0 h1 hfin
  have hent0 : 0 ≤ entR ρ := ENNReal.toReal_nonneg
  have hent_eq : entR ρ = 0 := by nlinarith
  have hkl : klDiv (densMeasure ρ) (haar 1) = 0 := by
    unfold entR at hent_eq
    rcases (ENNReal.toReal_eq_zero_iff _).1 hent_eq with h | h
    · exact h
    · exact absurd h hfin
  have hμ : densMeasure ρ = haar 1 := (klDiv_eq_zero_iff).1 hkl
  exact eq_one_of_densMeasure_eq h0 h1 hμ

end SharpLSI.FL.Ex.LaneD
