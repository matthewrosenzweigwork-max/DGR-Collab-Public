import FullLabeledLSI.Paper.Sec8Lin5
import FullLabeledLSI.Paper.Sec3Entropy

/-!
# Section 8.3 (linearization), part 6: admissibility and the gap along `p (1 + t hₐ)`

For `|t| (B + 2) ≤ 1/8` the family `fam p θ h t` is admissible, and
`G_θ = gap(ρ̄) + ∑ θₐ klPhi(hₐ, h̄)`, so `G_θ / t² → ½ (⟨h̄,(I+T)h̄⟩ + ∑ θₐ ‖ηₐ‖²)`.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

set_option linter.unusedSectionVars false

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem small_aux {B t : ℝ} (ht : |t| * (B + 2) ≤ 1 / 8) (hB0 : 0 ≤ B) :
    |t| * B ≤ 1 / 8 ∧ |t| * B ≤ 1 / 2 ∧ |t| * (B + 2) ≤ 1 / 2 := by
  have : |t| * B ≤ |t| * (B + 2) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
  exact ⟨by linarith, by linarith, by linarith⟩

theorem p_bounds (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {p : Torus d → ℝ} (hp : HasPosLipDensity μ p) :
    ∃ (c C : ℝ) (Lp : ℝ≥0), 0 < c ∧ (∀ x, c ≤ p x ∧ p x ≤ C) ∧ LipschitzWith Lp p := by
  obtain rfl := p_eq_elDens hyp hμ hp
  obtain ⟨c, C, L, hc, hb⟩ := elDensity_bounds hyp (V := V) (W := W)
  obtain ⟨h1, h2⟩ := hb (μ : Measure (Torus d)) inferInstance
  exact ⟨c, C, L, hc, h1, h2⟩

section lin
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {q : ℕ} (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ) (hθ : ∀ a, 0 < θ a) (hθ1 : ∑ a, θ a = 1)
  (hLip : ∀ a, ∃ L : ℝ≥0, LipschitzWith L (h a)) (hbd : ∀ a, ∃ B, ∀ x, |h a x| ≤ B)
  (hmean : ∀ a, ∫ x, h a x ∂(μ : Measure (Torus d)) = 0)
include hyp hμ hθ hθ1 hLip hbd hmean

theorem fam_admissible {p : Torus d → ℝ} (hp : HasPosLipDensity μ p) {B : ℝ}
    (hB : ∀ a x, |h a x| ≤ B) {t : ℝ} (ht : |t| * B ≤ 1 / 2) : (fam p θ h t).Admissible := by
  obtain ⟨c, C, Lp, hc, hpb, hpL⟩ := p_bounds hyp hμ hp
  obtain rfl := p_eq_elDens hyp hμ hp
  refine ⟨hθ, hθ1, fun a => ?_⟩
  obtain ⟨L, hL⟩ := hLip a
  obtain ⟨h0, h1, -⟩ := pert_props hyp hμ hL.continuous.measurable (hB a) (hmean a) ht
  exact ⟨h0, h1, (pert_weak hc hpb hpL ⟨L, hL⟩ (bounds_of_small (hB a) ht)).2.2.2⟩

theorem bar_facts {p : Torus d → ℝ} (hp : HasPosLipDensity μ p) {B : ℝ}
    (hBb : ∀ x, |hb θ h x| ≤ B) {t : ℝ} (ht : |t| * B ≤ 1 / 2) :
    (∀ x, 0 ≤ p x * (1 + t * hb θ h x)) ∧ ∫ x, p x * (1 + t * hb θ h x) ∂haar d = 1 ∧
      MemH1 (haar d) (fun y => Real.sqrt (p y * (1 + t * hb θ h y))) := by
  obtain ⟨c, C, Lp, hc, hpb, hpL⟩ := p_bounds hyp hμ hp
  obtain rfl := p_eq_elDens hyp hμ hp
  have hbL := lip_hb θ h hLip
  obtain ⟨L, hL⟩ := hbL
  obtain ⟨h0, h1, -⟩ := pert_props hyp hμ hL.continuous.measurable hBb
    (hb_integral θ h hLip hbd hmean) ht
  exact ⟨h0, h1, (pert_weak hc hpb hpL ⟨L, hL⟩ (bounds_of_small hBb ht)).2.2.2⟩

theorem fam_ac {p : Torus d → ℝ} (hp : HasPosLipDensity μ p) {B : ℝ}
    (hB : ∀ a x, |h a x| ≤ B) {t : ℝ} (ht : |t| * B ≤ 1 / 2) (a : Fin q) :
    densMeasure (fun x => p x * (1 + t * h a x)) ≪
      densMeasure (fun x => p x * (1 + t * hb θ h x)) := by
  have hF := fam_admissible hyp hμ θ h hθ hθ1 hLip hbd hmean hp hB ht
  have e : densMeasure ((fam p θ h t).ρ a) ≪ densMeasure (fam p θ h t).bar := by
    rw [densMeasure_eq_ratio _ hF a]; exact withDensity_absolutelyContinuous _ _
  rw [fam_bar p θ h t hθ1] at e
  exact e

theorem klPhi_nonneg {p : Torus d → ℝ} (hp : HasPosLipDensity μ p) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ a x, |h a x| ≤ B) (hBb : ∀ x, |hb θ h x| ≤ B) {t : ℝ} (ht : |t| * B ≤ 1 / 8)
    (a : Fin q) : 0 ≤ klPhi p (h a) (hb θ h) t := by
  have hp0 := hp.1
  have hca := (lip_data (hLip a)).1
  have hcb := (lip_data (lip_hb θ h hLip)).1
  obtain ⟨-, hK0⟩ := klKt_props hp0 hca hcb hB0 (hB a) hBb ht
  exact integral_nonneg fun x => mul_nonneg (hp0 x).le (hK0 x)

theorem msGap_toReal_eq {p : Torus d → ℝ} (hp : HasPosLipDensity μ p) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ a x, |h a x| ≤ B) (hBb : ∀ x, |hb θ h x| ≤ B) {t : ℝ} (ht : |t| * B ≤ 1 / 8) :
    (msGap V W (fam p θ h t)).toReal =
      (gap V W (densMeasure fun x => p x * (1 + t * hb θ h x))).toReal +
        ∑ a, θ a * klPhi p (h a) (hb θ h) t := by
  have ht' : |t| * B ≤ 1 / 2 := by linarith
  have hp0 := hp.1
  have hF := fam_admissible hyp hμ θ h hθ hθ1 hLip hbd hmean hp hB ht'
  obtain ⟨hdec, -, -⟩ := species_decomposition hyp _ hF
  obtain ⟨hb0, hb1, hbH⟩ := bar_facts hyp hμ θ h hθ hθ1 hLip hbd hmean hp hBb ht'
  have hbar := fam_bar p θ h t hθ1
  have hprob := isProbabilityMeasure_densMeasure' hb0 hb1
  have hgt := (gap_lt_top_aux hyp hb0 hb1 hbH).1
  have hg0 : 0 ≤ gap V W (densMeasure fun x => p x * (1 + t * hb θ h x)) :=
    gap_nonneg' hyp ⟨_, hprob⟩
  have hca := fun a => (lip_data (hLip a)).1
  have hcb := (lip_data (lip_hb θ h hLip)).1
  have hpc := (lip_data hp.2.1).1
  have hkl : ∀ a, klDiv (densMeasure ((fam p θ h t).ρ a)) (densMeasure (fam p θ h t).bar) =
      ENNReal.ofReal (klPhi p (h a) (hb θ h) t) := fun a => by
    rw [klDiv_species _ hF a]
    obtain ⟨hKc, hK0⟩ := klKt_props hp0 (hca a) hcb hB0 (hB a) hBb ht
    have hx : ∀ x, (fam p θ h t).bar x * klFun ((fam p θ h t).ρ a x / (fam p θ h t).bar x) =
        p x * ((1 + t * hb θ h x) * klFun ((1 + t * h a x) / (1 + t * hb θ h x))) := fun x => by
      rw [hbar]
      show p x * (1 + t * hb θ h x) * klFun (p x * (1 + t * h a x) / (p x * (1 + t * hb θ h x))) = _
      rw [mul_div_mul_left _ _ (hp0 x).ne']
      ring
    rw [lintegral_congr fun x => by rw [hx x]]
    unfold klPhi
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_of_continuous (hpc.mul hKc))
      (Eventually.of_forall fun x => mul_nonneg (hp0 x).le (hK0 x))).symm
  have hθf : ∀ a, (fam p θ h t).θ a = θ a := fun a => rfl
  rw [hdec]
  simp only [hkl, hθf]
  have hsne : (∑ a, ENNReal.ofReal (θ a) * ENNReal.ofReal (klPhi p (h a) (hb θ h) t)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun a _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  rw [hbar]
  change (gap V W (densMeasure fun x => p x * (1 + t * hb θ h x)) +
    ((∑ a : Fin q, ENNReal.ofReal (θ a) * ENNReal.ofReal (klPhi p (h a) (hb θ h) t) : ℝ≥0∞) :
      EReal)).toReal = _
  rw [EReal.toReal_add hgt.ne (lt_of_lt_of_le EReal.bot_lt_zero hg0).ne'
    (fun hh => hsne (EReal.coe_ennreal_eq_top_iff.mp hh)) (EReal.coe_ennreal_ne_bot _), EReal.toReal_coe_ennreal,
    ENNReal.toReal_sum fun a _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hθ a).le,
    ENNReal.toReal_ofReal (klPhi_nonneg hyp hμ θ h hθ hθ1 hLip hbd hmean hp hB0 hB hBb ht a)]

theorem gap_limit {p : Torus d → ℝ} (hp : HasPosLipDensity μ p) :
    Tendsto (fun t : ℝ => (msGap V W (fam p θ h t)).toReal / t ^ 2) (𝓝[≠] 0)
      (𝓝 ((secondVar W (μ : Measure (Torus d)) (hb θ h) +
        ∑ a, θ a * ∫ x, (h a x - hb θ h x) ^ 2 ∂(μ : Measure (Torus d))) / 2)) := by
  obtain ⟨B, hB0, hB, hBb⟩ := lin_bounds θ h hθ hθ1 hbd
  have hp' := hp
  obtain rfl := p_eq_elDens hyp hμ hp
  obtain ⟨hpm, hp0, hp1⟩ := elDensity_props hyp (μ : Measure (Torus d))
  have hpc := (lip_data hp'.2.1).1
  have hbL := lip_hb θ h hLip
  have hcb := (lip_data hbL).1
  have hca := fun a => (lip_data (hLip a)).1
  have h1 := tendsto_gap_pert hyp hμ hcb.measurable ⟨B, hBb⟩ (hb_integral θ h hLip hbd hmean)
  have h2 : ∀ a, Tendsto (fun t : ℝ => klPhi (elDens V W (μ : Measure (Torus d))) (h a) (hb θ h) t / t ^ 2)
      (𝓝[≠] 0) (𝓝 (∫ x, elDens V W (μ : Measure (Torus d)) x *
        ((h a x - hb θ h x) ^ 2 / 2) ∂haar d)) := fun a =>
    tendsto_klPhi hp0 hpc hp1 (hca a) hcb (hB a) hBb
  have h3 := h1.add (tendsto_finset_sum Finset.univ fun a _ => (h2 a).const_mul (θ a))
  have e1 : ∀ a, ∫ x, elDens V W (μ : Measure (Torus d)) x * ((h a x - hb θ h x) ^ 2 / 2) ∂haar d =
      (∫ x, (h a x - hb θ h x) ^ 2 ∂(μ : Measure (Torus d))) / 2 := fun a => by
    rw [integral_minimizer hyp hμ, ← integral_div]
    congr 1; funext x; ring
  have e : (secondVar W (μ : Measure (Torus d)) (hb θ h) +
        ∑ a, θ a * ∫ x, (h a x - hb θ h x) ^ 2 ∂(μ : Measure (Torus d))) / 2 =
      secondVar W (μ : Measure (Torus d)) (hb θ h) / 2 +
        ∑ a, θ a * ∫ x, elDens V W (μ : Measure (Torus d)) x *
          ((h a x - hb θ h x) ^ 2 / 2) ∂haar d := by
    rw [add_div, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [e1 a]; ring
  rw [e]
  refine h3.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (eventually_small' (B := B + 2)), self_mem_nhdsWithin]
    with t ht ht0
  obtain ⟨ht1, -, -⟩ := small_aux ht hB0
  have := msGap_toReal_eq hyp hμ θ h hθ hθ1 hLip hbd hmean hp' hB0 hB hBb ht1
  show _ = (msGap V W (fam _ θ h t)).toReal / t ^ 2
  rw [this, add_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_div_assoc]

end lin

end Sec8
end SharpLSI.FL
