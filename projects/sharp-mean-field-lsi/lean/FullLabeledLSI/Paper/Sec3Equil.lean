import FullLabeledLSI.Paper.Sec3Fisher
import FullLabeledLSI.Paper.Sec3Diss
import FullLabeledLSI.Paper.Sec3Force
import FullLabeledLSI.Paper.Sec3Ref
import FullLabeledLSI.Paper.PermAvgFisher2
import SharpSymmetricLSI.Paper.Defective21
import SharpSymmetricLSI.Paper.ReferenceLSI

/-!
# Equilibrium data for Section 3.3

Facts about the equilibrium density `q = elDens V W μ`: `MemH1 √q`, the score `∇ log q = -∇Φ`
(`Φ = V + W*μ`), and `∇Φ = ∇V + b_q`.
-/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal NNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ}

theorem lipschitz_comp_liftT {q : Torus d → ℝ} {L : ℝ≥0} (hL : LipschitzWith L q) :
    LipschitzWith L (q ∘ liftT) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  simp only [Function.comp]
  exact (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left (dist_liftT_le a b) L.2)

theorem memH1_sqrt_of_lipschitz {q : Torus d → ℝ} {c C : ℝ} {L : ℝ≥0} (hc : 0 < c)
    (hb : ∀ x, c ≤ q x ∧ q x ≤ C) (hL : LipschitzWith L q) :
    IsWeakGrad (fun x => Real.sqrt (q x)) (fun y k => lipGrad q y k / (2 * Real.sqrt (q y))) ∧
      MemH1 (haar d) (fun x => Real.sqrt (q x)) := by
  have hq0 : ∀ x, 0 < q x := fun x => hc.trans_le (hb x).1
  have hqc : Continuous q := hL.continuous
  have hqm : Measurable q := hqc.measurable
  have hw := isWeakGrad_lipGrad hqc (lipschitz_comp_liftT hL)
  have hqi : Integrable q (haar d) := Integrable.of_bound hqm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (hq0 x)]; exact (hb x).2)
  have hgi : ∀ k, Integrable (fun y => lipGrad q y k) (haar d) := fun k =>
    Integrable.of_bound (hw.aestronglyMeasurable_grad k) L (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact abs_lipGrad_le (lipschitz_comp_liftT hL) y k)
  have hS := isWeakGrad_sqrt_of_ge hw hqi hgi hc (fun x => (hb x).1)
  refine ⟨hS, ⟨_, hS⟩, ?_, ?_⟩
  · refine MemLp.of_bound hS.aestronglyMeasurable_fun (Real.sqrt C)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hb x).2
  · have hmeas : AEStronglyMeasurable (fun x => Real.sqrt (sqNorm (weakGrad (fun x => Real.sqrt (q x)) x)))
        (haar d) := Real.continuous_sqrt.comp_aestronglyMeasurable
      (isWeakGrad_weakGrad ⟨_, hS⟩).aestronglyMeasurable_sqNorm
    have hc2 : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
    refine MemLp.of_bound hmeas (Fintype.card (Fin d) * (L / (2 * Real.sqrt c)))
      ?_
    filter_upwards [weakGrad_ae_eq hS] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hx]
    refine (sqrt_sqNorm_le_sum_abs _).trans ?_
    calc ∑ k, |lipGrad q x k / (2 * Real.sqrt (q x))|
        ≤ ∑ _k : Fin d, L / (2 * Real.sqrt c) := Finset.sum_le_sum fun k _ => by
          have hsq : 0 < Real.sqrt (q x) := Real.sqrt_pos.2 (hq0 x)
          rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sqrt (q x))]
          exact div_le_div₀ (by positivity) (abs_lipGrad_le (lipschitz_comp_liftT hL) x k)
            (by positivity) (by have := Real.sqrt_le_sqrt (hb x).1; linarith)
      _ = _ := by simp


theorem sumsq_add_le {n : ℕ} (A δ : Fin n → ℝ) (t : ℝ) :
    ∑ k, (A k + t * δ k) ^ 2 ≤ 2 * ∑ k, A k ^ 2 + 2 * (t ^ 2 * ∑ k, δ k ^ 2) := by
  calc ∑ k, (A k + t * δ k) ^ 2 ≤ ∑ k, (2 * A k ^ 2 + 2 * (t ^ 2 * δ k ^ 2)) :=
        Finset.sum_le_sum fun k _ => by nlinarith [sq_nonneg (A k - t * δ k)]
    _ = 2 * ∑ k, A k ^ 2 + 2 * (t ^ 2 * ∑ k, δ k ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

section Equil

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
include hyp hμ

theorem elDens_data : ∃ (c C : ℝ) (L : ℝ≥0), 0 < c ∧
    (∀ x, c ≤ elDens V W (μ : Measure (Torus d)) x ∧ elDens V W (μ : Measure (Torus d)) x ≤ C) ∧
      LipschitzWith L (elDens V W (μ : Measure (Torus d))) := by
  obtain ⟨c, C, L, hc, hb⟩ := elDensity_bounds hyp (W := W)
  obtain ⟨h1, h2⟩ := hb (μ : Measure (Torus d)) inferInstance
  exact ⟨c, C, L, hc, h1, h2⟩

theorem lipGrad_elDens_ae :
    ∀ᵐ x ∂haar d, ∀ k, lipGrad (elDens V W (μ : Measure (Torus d))) x k =
      -(elDens V W (μ : Measure (Torus d)) x * lipGrad (PhiMF V W μ) x k) := by
  obtain ⟨c, C, L, hc, hb, hL⟩ := elDens_data hyp hμ
  have h1 := isWeakGrad_lipGrad hL.continuous (lipschitz_comp_liftT hL)
  have h2 := isWeakGrad_elDens hyp hμ
  have := weakGrad_ae_unique h1 h2
  filter_upwards [this] with x hx k
  exact congrFun hx k

theorem score_elDens_ae :
    ∀ᵐ x ∂haar d, ∀ k, score (elDens V W (μ : Measure (Torus d))) x k =
      -lipGrad (PhiMF V W μ) x k := by
  obtain ⟨c, C, L, hc, hb, hL⟩ := elDens_data hyp hμ
  obtain ⟨hS, -⟩ := memH1_sqrt_of_lipschitz hc hb hL
  have hw := weakGrad_ae_eq hS
  filter_upwards [hw, lipGrad_elDens_ae hyp hμ] with x hx hg k
  have hq0 : 0 < elDens V W (μ : Measure (Torus d)) x := hc.trans_le (hb x).1
  have hs : 0 < Real.sqrt (elDens V W (μ : Measure (Torus d)) x) := Real.sqrt_pos.2 hq0
  have hs2 : Real.sqrt (elDens V W (μ : Measure (Torus d)) x) ^ 2 =
      elDens V W (μ : Measure (Torus d)) x := Real.sq_sqrt hq0.le
  simp only [score, if_pos hq0]
  rw [congrFun hx k, hg k]
  set q0 := elDens V W (μ : Measure (Torus d)) x with hq0def
  set s := Real.sqrt q0 with hsdef
  have e : q0 = s ^ 2 := hs2.symm
  rw [e]
  field_simp

theorem lipGrad_Phi_ae :
    ∀ᵐ x ∂haar d, ∀ k, lipGrad (PhiMF V W μ) x k = lipGrad V x k +
      bForceL W (elDens V W (μ : Measure (Torus d))) x k := by
  have hμq := minimizer_eq_elDensity hyp hμ
  obtain ⟨hm, hpos, h1⟩ := elDensity_props hyp (W := W) (μ : Measure (Torus d))
  have hac := minimizer_ac hyp hμ
  have hqi : Integrable (elDens V W (μ : Measure (Torus d))) (haar d) :=
    integrable_of_integral_eq_one' h1
  have hPhi : PhiMF V W μ = fun x => V x + convDens W (elDens V W (μ : Measure (Torus d))) x := by
    funext x
    simp only [PhiMF, convMeas, convDens]
    have key : ∫ y, W x y ∂(μ : Measure (Torus d)) =
        ∫ y, W x y ∂densMeasure (elDens V W (μ : Measure (Torus d))) :=
      congrArg (fun m => ∫ y, W x y ∂m) hμq
    rw [key, integral_densMeasure' (fun y => (hpos y).le) h1]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
  have hVw := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W))
  have h1' := hVw.add (isWeakGrad_convDens' hyp hqi (W := W))
  have h2 := isWeakGrad_PhiMF hyp hac (μ := (μ : Measure (Torus d)))
  rw [hPhi] at h2
  have := weakGrad_ae_unique h2 h1'
  filter_upwards [this] with x hx k
  rw [hPhi]
  exact congrFun hx k


variable {B : ℝ} (hB : ∀ᵐ X ∂(volume : Measure (Config 2 d)),
      sqNorm (fun k => grad1W W (X 0) (X 1) k) ≤ B ^ 2)
include hB

theorem relFisher_le (F : Family d) (hF : F.Admissible) (a : Fin F.q) :
    relFisher (F.ρ a) (elDens V W (μ : Measure (Torus d))) ≤
      2 * speciesDiss V W (F.ρ a) F.bar + ENNReal.ofReal (2 * (B ^ 2 *
        (∫ x, |F.bar x - elDens V W (μ : Measure (Torus d)) x| ∂haar d) ^ 2)) := by
  set q := elDens V W (μ : Measure (Torus d)) with hqdef
  obtain ⟨c, C, L, hc, hb, hL⟩ := elDens_data hyp hμ
  obtain ⟨-, hq1⟩ := memH1_sqrt_of_lipschitz hc hb hL
  obtain ⟨hqm, hqpos, hqint⟩ := elDensity_props hyp (W := W) (μ : Measure (Torus d))
  have hqi : Integrable q (haar d) := integrable_of_integral_eq_one' hqint
  have hacq : densMeasure (F.ρ a) ≪ densMeasure q := by
    refine (withDensity_absolutelyContinuous _ _).trans ?_
    exact withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp_aemeasurable
      hqm.aemeasurable) (Filter.Eventually.of_forall fun x => by simpa using hqpos x)
  have hrel : relFisher (F.ρ a) q = ∫⁻ x, ENNReal.ofReal (∑ k, (2 * sg F a x k -
      Real.sqrt (F.ρ a x) * score q x k) ^ 2) ∂haar d := by
    unfold relFisher
    rw [if_pos ⟨hacq, (hF.2.2 a).2.2, hq1⟩]
    rfl
  rw [hrel, speciesDiss_eq F hyp hF a]
  set M : ℝ := ∫ x, |F.bar x - q x| ∂haar d with hM
  set E : ℝ := 2 * (B ^ 2 * M ^ 2) with hE
  -- a.e. facts
  have hbarI := bar_integrable hF
  have hdiffI : Integrable (fun x => F.bar x - q x) (haar d) := hbarI.sub hqi
  have hforce := isWeakGrad_weakGrad (hasWeakGrad_force F hyp hF)
  have hVw := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W))
  have hfk := weakGrad_ae_unique hforce (hVw.add (isWeakGrad_convDens' hyp hbarI (W := W)))
  have hpair := bGrad_pair_bound hyp hB
  have hcomp : ∀ᵐ p ∂(haar d).prod (haar d), ∀ k, |bGrad W p.1 p.2 k| ≤ |B| := by
    filter_upwards [hpair] with p hp k
    refine (appA_abs_le_sqrt_sqNorm _ k).trans ?_
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hp
  have hlin : ∀ᵐ x ∂haar d, ∀ k, bForceL W (fun y => F.bar y - q y) x k =
      bForceL W F.bar x k - bForceL W q x k := by
    filter_upwards [integrable_bGrad_mul hcomp hyp hbarI, integrable_bGrad_mul hcomp hyp hqi]
      with x h1 h2 k
    unfold bForceL
    rw [← integral_sub (h1 k) (h2 k)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
  have hbd := bForceL_sqNorm_le hyp hB hdiffI
  have hscore := score_elDens_ae hyp hμ
  have hPhi := lipGrad_Phi_ae hyp hμ
  have hρ0 : ∀ x, 0 ≤ F.ρ a x := fun x => (hF.2.2 a).1 x
  set f : Torus d → Fin d → ℝ := fun x k => weakGrad (fun y => V y + convDens W F.bar y) x k
    with hf
  have hpt : ∀ᵐ x ∂haar d, ENNReal.ofReal (∑ k, (2 * sg F a x k -
      Real.sqrt (F.ρ a x) * score q x k) ^ 2) ≤
      2 * ENNReal.ofReal (∑ k, (2 * sg F a x k + Real.sqrt (F.ρ a x) * f x k) ^ 2) +
        ENNReal.ofReal E * ENNReal.ofReal (F.ρ a x) := by
    filter_upwards [hscore, hPhi, hfk, hlin, hbd] with x h1 h2 h3 h4 h5
    set δ : Fin d → ℝ := fun k => lipGrad (PhiMF V W μ) x k - f x k with hδ
    have hδ' : ∀ k, δ k = -bForceL W (fun y => F.bar y - q y) x k := fun k => by
      simp only [hδ, hf]
      rw [h4 k, h2 k, congrFun h3 k]
      ring
    have hδsq : ∑ k, δ k ^ 2 ≤ B ^ 2 * M ^ 2 := by
      have : ∑ k, δ k ^ 2 = sqNorm (fun k => bForceL W (fun y => F.bar y - q y) x k) := by
        unfold sqNorm
        exact Finset.sum_congr rfl fun k _ => by rw [hδ' k, neg_sq]
      rw [this]; exact h5
    have heq : ∀ k, 2 * sg F a x k - Real.sqrt (F.ρ a x) * score q x k =
        (2 * sg F a x k + Real.sqrt (F.ρ a x) * f x k) + Real.sqrt (F.ρ a x) * δ k := fun k => by
      rw [h1 k]; simp only [hδ]; ring
    have hs2 : Real.sqrt (F.ρ a x) ^ 2 = F.ρ a x := Real.sq_sqrt (hρ0 x)
    have hmain := sumsq_add_le (fun k => 2 * sg F a x k + Real.sqrt (F.ρ a x) * f x k) δ
      (Real.sqrt (F.ρ a x))
    simp_rw [heq]
    have hR : 2 * ∑ k, (2 * sg F a x k + Real.sqrt (F.ρ a x) * f x k) ^ 2 +
        2 * (Real.sqrt (F.ρ a x) ^ 2 * ∑ k, δ k ^ 2) ≤
        2 * ∑ k, (2 * sg F a x k + Real.sqrt (F.ρ a x) * f x k) ^ 2 + E * F.ρ a x := by
      rw [hs2, hE]
      nlinarith [mul_le_mul_of_nonneg_left hδsq (hρ0 x)]
    have hSn : 0 ≤ ∑ k, (2 * sg F a x k + Real.sqrt (F.ρ a x) * f x k) ^ 2 :=
      Finset.sum_nonneg fun k _ => sq_nonneg _
    have hE0 : 0 ≤ E := by rw [hE]; positivity
    calc ENNReal.ofReal (∑ k, ((2 * sg F a x k + Real.sqrt (F.ρ a x) * f x k) +
          Real.sqrt (F.ρ a x) * δ k) ^ 2)
        ≤ ENNReal.ofReal (2 * ∑ k, (2 * sg F a x k + Real.sqrt (F.ρ a x) * f x k) ^ 2 +
            E * F.ρ a x) := ENNReal.ofReal_le_ofReal (hmain.trans hR)
      _ = 2 * ENNReal.ofReal (∑ k, (2 * sg F a x k + Real.sqrt (F.ρ a x) * f x k) ^ 2) +
          ENNReal.ofReal E * ENNReal.ofReal (F.ρ a x) := by
        rw [ENNReal.ofReal_add (by positivity) (mul_nonneg hE0 (hρ0 x)),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_mul hE0]
        simp
  refine (lintegral_mono_ae hpt).trans ?_
  -- integrate the right-hand side
  have hρm : AEMeasurable (F.ρ a) (haar d) := rho_aemeasurable F hF a
  have hfk' : ∀ k, AEMeasurable (fun x => f x k) (haar d) := fun k =>
    (hforce.aestronglyMeasurable_grad k).aemeasurable
  have hsa : AEMeasurable (fun x => Real.sqrt (F.ρ a x)) (haar d) :=
    (sg_isWeakGrad F hF a).aestronglyMeasurable_fun.aemeasurable
  have hga : ∀ k, AEMeasurable (fun x => sg F a x k) (haar d) := fun k =>
    ((sg_isWeakGrad F hF a).aestronglyMeasurable_grad k).aemeasurable
  have hmS : AEMeasurable (fun x => ENNReal.ofReal (∑ k, (2 * sg F a x k +
      Real.sqrt (F.ρ a x) * f x k) ^ 2)) (haar d) :=
    aemeasurable_ofReal_sq_sum fun k => ((hga k).const_mul 2).add (hsa.mul (hfk' k))
  rw [lintegral_add_left' (hmS.const_mul 2), lintegral_const_mul' _ _ (by norm_num),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hρ1 : ∫⁻ x, ENNReal.ofReal (F.ρ a x) ∂haar d = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (rho_integrable F hF a)
      (Filter.Eventually.of_forall hρ0), (hF.2.2 a).2.1]
    simp
  rw [hρ1, mul_one]

end Equil

end SharpLSI.FL
