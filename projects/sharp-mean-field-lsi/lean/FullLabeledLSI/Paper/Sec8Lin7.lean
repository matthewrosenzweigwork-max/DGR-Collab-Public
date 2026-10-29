import FullLabeledLSI.Paper.Sec8Lin6

/-!
# Section 8.3 (linearization), part 7: the dissipation along `p (1 + t hₐ)` and (8.9)–(8.10)

`D_θ = D(ρ̄) + ∑ θₐ I(ρₐ | ρ̄)`; `D(ρ̄)/t² → ∫|∇(h̄ + T h̄)|² dμ` and `I(ρₐ | ρ̄)/t² → ∫|∇ηₐ|² dμ`.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

set_option linter.unusedSectionVars false

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section lin
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {q : ℕ} (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ) (hθ : ∀ a, 0 < θ a) (hθ1 : ∑ a, θ a = 1)
  (hLip : ∀ a, ∃ L : ℝ≥0, LipschitzWith L (h a)) (hbd : ∀ a, ∃ B, ∀ x, |h a x| ≤ B)
  (hmean : ∀ a, ∫ x, h a x ∂(μ : Measure (Torus d)) = 0)
include hyp hμ hθ hθ1 hLip hbd hmean

theorem diss_limit {p : Torus d → ℝ} (hp : HasPosLipDensity μ p) :
    Tendsto (fun t : ℝ => (msDiss V W (fam p θ h t)).toReal / t ^ 2) (𝓝[≠] 0)
      (𝓝 ((dirichlet (μ : Measure (Torus d))
          (fun x => hb θ h x + Top W (μ : Measure (Torus d)) (hb θ h) x)).toReal +
        ∑ a, θ a * (dirichlet (μ : Measure (Torus d)) (fun x => h a x - hb θ h x)).toReal)) := by
  obtain ⟨B, hB0, hB, hBb⟩ := lin_bounds θ h hθ hθ1 hbd
  obtain ⟨c, C, Lp, hc, hpb, hpL⟩ := p_bounds hyp hμ hp
  have hp' := hp
  obtain rfl := p_eq_elDens hyp hμ hp
  obtain ⟨hpm, hp0, hp1⟩ := elDensity_props hyp (μ : Measure (Torus d))
  have hpi : Integrable (elDens V W (μ : Measure (Torus d))) (haar d) :=
    integrable_of_integral_eq_one' hp1
  have hbL := lip_hb θ h hLip
  have hcb := (lip_data hbL).1
  have hbmean := hb_integral θ h hLip hbd hmean
  have hL20 : MemL20 (μ : Measure (Torus d)) (hb θ h) :=
    ⟨MemLp.of_bound hcb.measurable.aestronglyMeasurable B
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBb x), hbmean⟩
  obtain ⟨CT0, hCT⟩ := Top_W1inf hyp (μ : Measure (Torus d))
  obtain ⟨hTb, hTL⟩ := hCT _ hL20
  have hgL := lip_add hbL ⟨_, hTL⟩
  obtain ⟨hgc, hgw, ⟨Kg, hKg⟩, hgm⟩ := lip_data hgL
  have hac : (μ : Measure (Torus d)) ≪ haar d := by
    rw [minimizer_eq_elDensity hyp hμ]; exact withDensity_absolutelyContinuous _ _
  -- the limit of the dissipation of the average
  have hJ := (tendsto_diss_pertG hyp hμ hcb hKg hgm hBb).mono_left
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  rw [← dirichlet_toReal_of_wg hac hgw hKg hgm] at hJ
  -- the limits of the relative Fisher informations
  have hR : ∀ a, Tendsto (fun t : ℝ => (relFisher
      (fun x => elDens V W (μ : Measure (Torus d)) x * (1 + t * h a x))
      (fun x => elDens V W (μ : Measure (Torus d)) x * (1 + t * hb θ h x))).toReal / t ^ 2)
      (𝓝[≠] 0) (𝓝 (dirichlet (μ : Measure (Torus d)) (fun x => h a x - hb θ h x)).toReal) :=
    fun a => by
    obtain ⟨hca, hwa, ⟨Ka, hKa⟩, hma⟩ := lip_data (hLip a)
    obtain ⟨-, hwb, ⟨Kb, hKb⟩, hmb⟩ := lip_data hbL
    have hacev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), densMeasure
        (fun x => elDens V W (μ : Measure (Torus d)) x * (1 + t * h a x)) ≪
        densMeasure (fun x => elDens V W (μ : Measure (Torus d)) x * (1 + t * hb θ h x)) := by
      filter_upwards [nhdsWithin_le_nhds (eventually_small (B := B))] with t ht
      exact fam_ac hyp hμ θ h hθ hθ1 hLip hbd hmean hp' hB ht a
    have hlim := tendsto_relFisher_toReal hc hpb hpL (hLip a) hbL (hB a) hBb hacev
    have hw : IsWeakGrad (fun x => h a x - hb θ h x)
        (fun x k => lipGrad (h a) x k - lipGrad (hb θ h) x k) := by
      have := hwa.add (hwb.cmul (-1))
      have e1 : (fun x => h a x - hb θ h x) = fun y => h a y + (-1) * hb θ h y := by
        funext y; ring
      have e2 : (fun x k => lipGrad (h a) x k - lipGrad (hb θ h) x k) =
          fun y k => lipGrad (h a) y k + (-1) * lipGrad (hb θ h) y k := by
        funext y k; ring
      rw [e1, e2]; exact this
    have e : ∫ x, elDens V W (μ : Measure (Torus d)) x *
        ∑ k, (lipGrad (h a) x k - lipGrad (hb θ h) x k) ^ 2 ∂haar d =
        (dirichlet (μ : Measure (Torus d)) (fun x => h a x - hb θ h x)).toReal := by
      rw [dirichlet_toReal_of_wg hac hw (K := Ka + Kb)
        (fun x k => (abs_sub _ _).trans (add_le_add (hKa x k) (hKb x k)))
        (fun k => (hma k).sub (hmb k)), integral_minimizer hyp hμ]
    rw [e] at hlim
    exact hlim
  have hsum := hJ.add (tendsto_finset_sum Finset.univ fun a _ => (hR a).const_mul (θ a))
  refine hsum.congr' ?_
  obtain ⟨K, hK⟩ := dissIntG_bounds hyp (W := W) hpi hcb hKg hgm hBb
  filter_upwards [nhdsWithin_le_nhds (eventually_small' (B := B + 2)), self_mem_nhdsWithin]
    with t ht ht0
  obtain ⟨ht1, ht2, ht3⟩ := small_aux ht hB0
  have hF := fam_admissible hyp hμ θ h hθ hθ1 hLip hbd hmean hp' hB ht2
  obtain ⟨-, hdec, -⟩ := species_decomposition hyp _ hF
  have hbar := fam_bar (elDens V W (μ : Measure (Torus d))) θ h t hθ1
  have hdiss := dissipation_pertG hyp hμ hcb hgw hKg hgm (fun x => rfl) hBb ht3
  have hrf : ∀ a, relFisher (fun x => elDens V W (μ : Measure (Torus d)) x * (1 + t * h a x))
      (fun x => elDens V W (μ : Measure (Torus d)) x * (1 + t * hb θ h x)) =
      ENNReal.ofReal (t ^ 2 * ∫ x, elDens V W (μ : Measure (Torus d)) x *
        relJ (lipGrad (h a)) (lipGrad (hb θ h)) (h a) (hb θ h) t x ∂haar d) := fun a =>
    relFisher_pert hc hpb hpL (hLip a) hbL (bounds_of_small (hB a) ht2)
      (bounds_of_small hBb ht2) (fam_ac hyp hμ θ h hθ hθ1 hLip hbd hmean hp' hB ht2 a)
  have hrne : ∀ a, relFisher (fun x => elDens V W (μ : Measure (Torus d)) x * (1 + t * h a x))
      (fun x => elDens V W (μ : Measure (Torus d)) x * (1 + t * hb θ h x)) ≠ ⊤ :=
    fun a => by rw [hrf a]; exact ENNReal.ofReal_ne_top
  have hJnn : 0 ≤ ∫ x, dissIntG W (elDens V W (μ : Measure (Torus d))) (hb θ h) (lipGrad
      (fun x => hb θ h x + Top W (μ : Measure (Torus d)) (hb θ h) x)) t x
      ∂(μ : Measure (Torus d)) := integral_nonneg fun x => ((hK t ht3).2 x).1
  have ht2ne : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
  show _ = (msDiss V W (fam _ θ h t)).toReal / t ^ 2
  unfold msDiss
  rw [show (∑ a, ENNReal.ofReal ((fam (elDens V W (μ : Measure (Torus d))) θ h t).θ a) *
      speciesDiss V W ((fam (elDens V W (μ : Measure (Torus d))) θ h t).ρ a)
        (fam (elDens V W (μ : Measure (Torus d))) θ h t).bar) =
      dissipation V W (fun x => elDens V W (μ : Measure (Torus d)) x * (1 + t * hb θ h x)) +
      ∑ a : Fin q, ENNReal.ofReal (θ a) *
        relFisher (fun x => elDens V W (μ : Measure (Torus d)) x * (1 + t * h a x))
          (fun x => elDens V W (μ : Measure (Torus d)) x * (1 + t * hb θ h x)) from by
    have := hdec
    rw [hbar] at this
    exact this]
  rw [ENNReal.toReal_add (by rw [hdiss]; exact ENNReal.ofReal_ne_top)
    (ENNReal.sum_ne_top.2 fun a _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hrne a)),
    hdiss, ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _) hJnn),
    ENNReal.toReal_sum fun a _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hrne a),
    add_div, mul_div_cancel_left₀ _ ht2ne, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hθ a).le, mul_div_assoc]

/-- Section 8.3, (8.9) and (8.10), for the family `fam`. -/
theorem lin_expansions {p : Torus d → ℝ} (hp : HasPosLipDensity μ p) :
    (∀ᶠ t in 𝓝[≠] (0 : ℝ), (fam p θ h t).Admissible ∧
      msGap V W (fam p θ h t) < ⊤ ∧ msDiss V W (fam p θ h t) < ⊤) ∧
    Tendsto (fun t : ℝ => (msGap V W (fam p θ h t)).toReal / t ^ 2) (𝓝[≠] 0)
        (𝓝 ((secondVar W (μ : Measure (Torus d)) (hb θ h) +
          ∑ a, θ a * ∫ x, (h a x - hb θ h x) ^ 2 ∂(μ : Measure (Torus d))) / 2)) ∧
      Tendsto (fun t : ℝ => (msDiss V W (fam p θ h t)).toReal / t ^ 2) (𝓝[≠] 0)
        (𝓝 ((dirichlet (μ : Measure (Torus d))
          (fun x => hb θ h x + Top W (μ : Measure (Torus d)) (hb θ h) x)).toReal +
        ∑ a, θ a * (dirichlet (μ : Measure (Torus d)) (fun x => h a x - hb θ h x)).toReal)) := by
  refine ⟨?_, gap_limit hyp hμ θ h hθ hθ1 hLip hbd hmean hp,
    diss_limit hyp hμ θ h hθ hθ1 hLip hbd hmean hp⟩
  obtain ⟨B, hB0, hB, hBb⟩ := lin_bounds θ h hθ hθ1 hbd
  filter_upwards [nhdsWithin_le_nhds (eventually_small' (B := B + 2))] with t ht
  obtain ⟨-, ht2, -⟩ := small_aux ht hB0
  have hF := fam_admissible hyp hμ θ h hθ hθ1 hLip hbd hmean hp hB ht2
  exact ⟨hF, (msGap_bounds_of_admissible hyp hF).1, msDiss_lt_top_of_admissible hyp hF⟩

end lin

end Sec8
end SharpLSI.FL
