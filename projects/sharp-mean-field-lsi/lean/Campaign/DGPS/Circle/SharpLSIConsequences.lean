import DGPS.Analysis.BoundedPerturbation
import DGPS.Foundations.SobolevEmbedding
import DGPS.Analysis.CircleLSI
import DGPS.Circle.QuantitativeLSI

/-!
# LIP041: sharp torus LSI consequences and the fixed-dimensional defect

Final theorem `DGPS.Lipschitz.sharp_torus_lsi_tensorization_and_fixed_dimensional_defect`: the
quantitative circle inequalities (FOU016), the exactly sharp rate `a_T = 4 pi^2` of the Haar LSI on
every torus (DEF024, FOU014), the arbitrarily-small-energy-coefficient defective inequality in each
fixed dimension (via the Sobolev embedding and a tangent-line entropy bound), and the transfer to
references with two-sided density bounds (DEF025).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

theorem lip041_sobolev (d : ℕ) :
    ∃ q K : ℝ, 2 < q ∧ 0 < K ∧ ∀ (u : Torus d → ℝ) (g : Torus d → Tangent d),
      IsWeakGradient u g →
      MemLp u (ENNReal.ofReal q) (haar d) ∧
      eLpNorm u (ENNReal.ofReal q) (haar d) ≤
        ENNReal.ofReal K * (eLpNorm u 2 (haar d) + eLpNorm g 2 (haar d)) := by
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ 2 < d) with rfl | rfl | rfl | h
  · refine ⟨3, 1, by norm_num, one_pos, fun u g hg => ?_⟩
    have hc : u = fun _ => u (fun i => i.elim0) := by
      funext x; congr 1; funext i; exact i.elim0
    have hP : haar 0 Set.univ = 1 := measure_univ
    refine ⟨by rw [hc]; exact memLp_const _, ?_⟩
    have hne : haar 0 ≠ 0 := fun h => by simp [h] at hP
    rw [hc, eLpNorm_const _ (by simp) hne, eLpNorm_const _ (by simp) hne, hP]
    simp
  · refine ⟨3, 1, by norm_num, one_pos, fun u g hg => ?_⟩
    obtain ⟨w, -, hae, -, hb, hT⟩ := DGPS.sobolev_embedding_dim_one hg
    have h2 : eLpNorm u 2 (haar 1) ≠ ⊤ := hg.memLp.eLpNorm_ne_top
    have h3 : eLpNorm g 2 (haar 1) ≠ ⊤ := hg.memLp_grad.eLpNorm_ne_top
    have hbd : ∀ᵐ x ∂haar 1, ‖u x‖ ≤ (eLpNorm u 2 (haar 1)).toReal + (eLpNorm g 2 (haar 1)).toReal := by
      filter_upwards [hae] with x hx
      rw [Real.norm_eq_abs, ← hx]; exact hb x
    have hle := eLpNorm_le_of_ae_bound (p := ENNReal.ofReal 3) hg.memLp.aestronglyMeasurable hbd
    refine ⟨hT.mono_exponent le_top, hle.trans ?_⟩
    rw [measure_univ]
    rw [ENNReal.one_rpow, one_mul, ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal h2, ENNReal.ofReal_toReal h3, ENNReal.ofReal_one, one_mul]
  · obtain ⟨C, hC⟩ := DGPS.sobolev_embedding_dim_two (d := 2) rfl 3
    refine ⟨3, C + 1, by norm_num, by positivity, fun u g hg => ?_⟩
    obtain ⟨h1, h2⟩ := hC u g hg
    have e3 : ENNReal.ofReal 3 = ((3 : ℝ≥0) : ℝ≥0∞) := by simp
    rw [e3]
    have hCK : (C : ℝ≥0∞) ≤ ENNReal.ofReal ((C : ℝ) + 1) := by
      rw [ENNReal.ofReal_add C.coe_nonneg zero_le_one]
      simp
    exact ⟨h1, h2.trans (mul_le_mul' hCK le_rfl)⟩
  · obtain ⟨C, hC⟩ := DGPS.sobolev_embedding_critical h
    have hd' : (2 : ℝ) < d := by exact_mod_cast h
    have hlt : (2 : ℝ) < 2 * d / (d - 2) := by
      rw [lt_div_iff₀ (by linarith)]; linarith
    refine ⟨2 * d / (d - 2), C + 1, hlt, by positivity, fun u g hg => ?_⟩
    obtain ⟨h1, h2⟩ := hC u g hg
    have hCK : (C : ℝ≥0∞) ≤ ENNReal.ofReal ((C : ℝ) + 1) := by
      rw [ENNReal.ofReal_add C.coe_nonneg zero_le_one]
      simp
    exact ⟨h1, h2.trans (mul_le_mul' hCK le_rfl)⟩


/-- Pointwise tangent-line bound for the entropy integrand. -/
theorem lip041_pointwise {s a Y t : ℝ} (hs : 1 < s) (ha : 0 < a) (hY : 0 < Y) (ht : 0 ≤ t) :
    entropyIntegrand a t ≤
      1 / (s - 1) * (a ^ (1 - s) * t ^ s / Y - t + t * Real.log Y) - t + a := by
  have hs1 : 0 < s - 1 := by linarith
  rcases ht.eq_or_lt with h0 | htp
  · subst h0
    simp [entropyIntegrand, Real.zero_rpow (by linarith : s ≠ 0)]
  · have hy : 0 < (t / a) ^ (s - 1) := Real.rpow_pos_of_pos (div_pos htp ha) _
    have hlog : Real.log ((t / a) ^ (s - 1)) = (s - 1) * Real.log (t / a) :=
      Real.log_rpow (div_pos htp ha) _
    have h1 : Real.log ((t / a) ^ (s - 1)) ≤ (t / a) ^ (s - 1) / Y - 1 + Real.log Y := by
      have := Real.log_le_sub_one_of_pos (div_pos hy hY)
      rw [Real.log_div hy.ne' hY.ne'] at this
      linarith
    have h2 : t * (t / a) ^ (s - 1) = a ^ (1 - s) * t ^ s := by
      rw [Real.div_rpow htp.le ha.le, Real.rpow_sub_one htp.ne', Real.rpow_sub_one ha.ne',
        show (1 - s) = -(s - 1) by ring, Real.rpow_neg ha.le, Real.rpow_sub_one ha.ne']
      have : 0 < a ^ s := Real.rpow_pos_of_pos ha _
      have : 0 < t ^ s := Real.rpow_pos_of_pos htp _
      field_simp
    have h3 : t * Real.log (t / a) = 1 / (s - 1) * (t * ((t / a) ^ (s - 1) / Y - 1 + Real.log Y)) -
        1 / (s - 1) * (t * ((t / a) ^ (s - 1) / Y - 1 + Real.log Y - Real.log ((t / a) ^ (s - 1)))) := by
      rw [hlog]; field_simp; ring
    have h4 : 0 ≤ 1 / (s - 1) * (t * ((t / a) ^ (s - 1) / Y - 1 + Real.log Y -
        Real.log ((t / a) ^ (s - 1)))) :=
      mul_nonneg (by positivity) (mul_nonneg ht (by linarith))
    have h5 : t * ((t / a) ^ (s - 1) / Y - 1 + Real.log Y) =
        a ^ (1 - s) * t ^ s / Y - t + t * Real.log Y := by
      rw [← h2]; field_simp
    unfold entropyIntegrand
    rw [h5] at h3
    linarith [h3, h4]


/-- Integrated tangent-line entropy bound. -/
theorem lip041_entropy_bound {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] {v : α → ℝ} {s Y : ℝ} (hs : 1 < s) (hY : 0 < Y)
    (hv0 : ∀ x, 0 ≤ v x) (hv : Integrable v P) (hvs : Integrable (fun x => v x ^ s) P)
    (ha : 0 < ∫ x, v x ∂P) (hN : ∫ x, v x ^ s ∂P ≤ (∫ x, v x ∂P) ^ s * Y) :
    homogeneousEntropy P v ≤ ENNReal.ofReal ((∫ x, v x ∂P) * Real.log Y / (s - 1)) := by
  set a := ∫ x, v x ∂P with hadef
  have hs1 : 0 < s - 1 := by linarith
  rw [homogeneousEntropy_of_integral_ne_zero ha.ne', ← hadef]
  set α' : ℝ := a ^ (1 - s) / ((s - 1) * Y) with hα
  set β : ℝ := (Real.log Y - 1) / (s - 1) - 1 with hβ
  have hpt : ∀ x, entropyIntegrand a (v x) ≤ α' * v x ^ s + β * v x + a := by
    intro x
    have := lip041_pointwise hs ha hY (hv0 x)
    refine this.trans (le_of_eq ?_)
    rw [hα, hβ]; field_simp; ring
  have hψ : Integrable (fun x => α' * v x ^ s + β * v x + a) P :=
    ((hvs.const_mul α').add (hv.const_mul β)).add (integrable_const a)
  have hnn : ∀ x, 0 ≤ entropyIntegrand a (v x) := fun x => entropyIntegrand_nonneg ha (hv0 x)
  calc ∫⁻ x, ENNReal.ofReal (entropyIntegrand a (v x)) ∂P
      ≤ ∫⁻ x, ENNReal.ofReal (α' * v x ^ s + β * v x + a) ∂P :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal (∫ x, (α' * v x ^ s + β * v x + a) ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hψ
          (Filter.Eventually.of_forall fun x => (hnn x).trans (hpt x))).symm
    _ ≤ ENNReal.ofReal (a * Real.log Y / (s - 1)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hI : ∫ x, (α' * v x ^ s + β * v x + a) ∂P =
            α' * ∫ x, v x ^ s ∂P + β * a + a := by
          rw [integral_add (f := fun x => α' * v x ^ s + β * v x) (g := fun _ => a)
            ((hvs.const_mul α').add (hv.const_mul β)) (integrable_const a),
            integral_add (f := fun x => α' * v x ^ s) (g := fun x => β * v x)
              (hvs.const_mul α') (hv.const_mul β), integral_const_mul, integral_const_mul,
              integral_const]
          simp [← hadef]
        rw [hI]
        have hαnn : 0 ≤ α' := by positivity
        have h1 : α' * ∫ x, v x ^ s ∂P ≤ α' * (a ^ s * Y) := mul_le_mul_of_nonneg_left hN hαnn
        have h2 : α' * (a ^ s * Y) = a / (s - 1) := by
          rw [hα]
          have : a ^ (1 - s) * a ^ s = a := by
            rw [← Real.rpow_add ha]; simp
          field_simp
          linarith [this, mul_comm (a ^ s) (a ^ (1 - s))]
        rw [hβ]
        have h3 : a / (s - 1) + ((Real.log Y - 1) / (s - 1) - 1) * a + a = a * Real.log Y / (s - 1) := by
          field_simp; ring
        linarith


theorem lip041_rpow_sq {x s q : ℝ} (hq : q = 2 * s) : (x ^ 2) ^ s = ‖x‖ ^ q := by
  rw [Real.norm_eq_abs, hq, Real.rpow_mul (abs_nonneg x), Real.rpow_two, sq_abs]

theorem lip041_log_one_add_le {x δ : ℝ} (hx : 0 ≤ x) (hδ : 0 < δ) :
    Real.log (1 + x) ≤ δ * x + (δ - 1 - Real.log δ) := by
  have h1 : 0 < δ * (1 + x) := by positivity
  have := Real.log_le_sub_one_of_pos h1
  rw [Real.log_mul hδ.ne' (by positivity)] at this
  nlinarith

/-- Fixed-dimensional defective LSI, with an arbitrarily small energy coefficient. -/
theorem lip041_defect (d : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient f g →
      homogeneousEntropy (haar d) (fun x => f x ^ 2) ≤
        ENNReal.ofReal η * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂haar d +
          ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂haar d := by
  obtain ⟨q, K, hq, hK, hS⟩ := lip041_sobolev d
  set s : ℝ := q / 2 with hsdef
  have hs : 1 < s := by rw [hsdef]; linarith
  have hs0 : 0 < s := by linarith
  have hqs : q = 2 * s := by rw [hsdef]; ring
  set δ : ℝ := η * (s - 1) / s with hδdef
  have hδ : 0 < δ := by rw [hδdef]; have : 0 < s - 1 := by linarith
                        positivity
  set L : ℝ := Real.log (K ^ q * 2 ^ s) with hL
  set cδ : ℝ := δ - 1 - Real.log δ with hcδ
  refine ⟨max 0 ((L + s * cδ) / (s - 1)), le_max_left _ _, fun f g hg => ?_⟩
  obtain ⟨hmq, hnorm⟩ := hS f g hg
  have hv : Integrable (fun x => f x ^ 2) (haar d) := hg.memLp.integrable_sq
  have hE : Integrable (fun x => ‖g x‖ ^ 2) (haar d) := hg.memLp_grad.norm.integrable_sq
  set M : ℝ := ∫ x, f x ^ 2 ∂haar d with hM
  set E : ℝ := ∫ x, ‖g x‖ ^ 2 ∂haar d with hEdef
  have hM0 : 0 ≤ M := integral_nonneg fun x => sq_nonneg _
  have hE0 : 0 ≤ E := integral_nonneg fun x => sq_nonneg _
  have hlE : ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂haar d = ENNReal.ofReal E :=
    (ofReal_integral_eq_lintegral_ofReal hE (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
  have hlM : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂haar d = ENNReal.ofReal M :=
    (ofReal_integral_eq_lintegral_ofReal hv (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
  rw [hlE, hlM]
  rcases hM0.eq_or_lt with hM00 | hMpos
  · rw [homogeneousEntropy_of_integral_eq_zero hM00.symm]; exact bot_le
  have hs1 : 0 < s - 1 := by linarith
  -- norms
  have hqne : ENNReal.ofReal q ≠ 0 := by simp; linarith
  have hint : Integrable (fun x => ‖f x‖ ^ (ENNReal.ofReal q).toReal) (haar d) :=
    hmq.integrable_norm_rpow hqne ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal (by linarith)] at hint
  have hvs : Integrable (fun x => (f x ^ 2) ^ s) (haar d) := by
    refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
    exact (lip041_rpow_sq hqs).symm
  set N : ℝ := ∫ x, (f x ^ 2) ^ s ∂haar d with hN
  have hN0 : 0 ≤ N := integral_nonneg fun x => Real.rpow_nonneg (sq_nonneg _) _
  have hnq : (eLpNorm f (ENNReal.ofReal q) (haar d)).toReal = N ^ (1 / q) := by
    rw [hmq.eLpNorm_eq_integral_rpow_norm hqne ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by linarith), hN]
    have hI : ∫ x, ‖f x‖ ^ q ∂haar d = N :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => (lip041_rpow_sq hqs).symm)
    rw [hI, one_div]
  have hn2 : (eLpNorm f 2 (haar d)).toReal = Real.sqrt M := toReal_eLpNorm_two hg.memLp
  have hng : (eLpNorm g 2 (haar d)).toReal = Real.sqrt E := by
    rw [← eLpNorm_norm, toReal_eLpNorm_two hg.memLp_grad.norm]
    exact hg.memLp_grad.aestronglyMeasurable
  have hle : (eLpNorm f (ENNReal.ofReal q) (haar d)).toReal ≤
      K * (Real.sqrt M + Real.sqrt E) := by
    have h2 : eLpNorm f 2 (haar d) ≠ ⊤ := hg.memLp.eLpNorm_ne_top
    have h3 : eLpNorm g 2 (haar d) ≠ ⊤ := hg.memLp_grad.eLpNorm_ne_top
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2 ⟨h2, h3⟩)) hnorm
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK.le, ENNReal.toReal_add h2 h3, hn2, hng]
      at this
  have hNle : N ≤ K ^ q * (2 * (M + E)) ^ s := by
    have hnq0 : 0 ≤ N ^ (1 / q) := Real.rpow_nonneg hN0 _
    have h1 : N = (N ^ (1 / q)) ^ q := by
      rw [← Real.rpow_mul hN0, one_div, inv_mul_cancel₀ (by linarith), Real.rpow_one]
    have h2 : (N ^ (1 / q)) ^ q ≤ (K * (Real.sqrt M + Real.sqrt E)) ^ q :=
      Real.rpow_le_rpow hnq0 (hnq ▸ hle) (by linarith)
    have h3 : (K * (Real.sqrt M + Real.sqrt E)) ^ q =
        K ^ q * (Real.sqrt M + Real.sqrt E) ^ q := Real.mul_rpow hK.le (by positivity)
    have h4 : (Real.sqrt M + Real.sqrt E) ^ q =
        ((Real.sqrt M + Real.sqrt E) ^ 2) ^ s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hqs]; norm_num
    have h5 : (Real.sqrt M + Real.sqrt E) ^ 2 ≤ 2 * (M + E) := by
      have := Real.sq_sqrt hM0
      have := Real.sq_sqrt hE0
      nlinarith [sq_nonneg (Real.sqrt M - Real.sqrt E)]
    have h6 : ((Real.sqrt M + Real.sqrt E) ^ 2) ^ s ≤ (2 * (M + E)) ^ s :=
      Real.rpow_le_rpow (by positivity) h5 hs0.le
    calc N = (N ^ (1 / q)) ^ q := h1
      _ ≤ K ^ q * (Real.sqrt M + Real.sqrt E) ^ q := h2.trans h3.le
      _ ≤ K ^ q * (2 * (M + E)) ^ s := by
          rw [h4]; exact mul_le_mul_of_nonneg_left h6 (by positivity)
  set Y : ℝ := K ^ q * 2 ^ s * (1 + E / M) ^ s with hY
  have hYpos : 0 < Y := by rw [hY]; positivity
  have hNY : N ≤ M ^ s * Y := by
    have : M ^ s * Y = K ^ q * (2 * (M + E)) ^ s := by
      rw [hY, show 2 * (M + E) = 2 * (M * (1 + E / M)) by field_simp,
        Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow hMpos.le (by positivity)]
      ring
    rw [this]; exact hNle
  have hent := lip041_entropy_bound (P := haar d) hs hYpos (fun x => sq_nonneg (f x)) hv hvs hMpos hNY
  refine hent.trans ?_
  have hlogY : Real.log Y = L + s * Real.log (1 + E / M) := by
    rw [hY, Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity)]
  have hlog := lip041_log_one_add_le (div_nonneg hE0 hMpos.le) hδ
  have h1 : M * Real.log Y / (s - 1) ≤ M * (L + s * (δ * (E / M) + cδ)) / (s - 1) := by
    refine div_le_div_of_nonneg_right ?_ hs1.le
    rw [hlogY]
    exact mul_le_mul_of_nonneg_left (by nlinarith) hMpos.le
  have h2 : M * (L + s * (δ * (E / M) + cδ)) / (s - 1) =
      η * E + (L + s * cδ) / (s - 1) * M := by
    rw [hδdef]; field_simp; ring
  have h3 : (L + s * cδ) / (s - 1) * M ≤ max 0 ((L + s * cδ) / (s - 1)) * M :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hMpos.le
  calc ENNReal.ofReal (M * Real.log Y / (s - 1))
      ≤ ENNReal.ofReal (η * E + max 0 ((L + s * cδ) / (s - 1)) * M) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal η * ENNReal.ofReal E +
          ENNReal.ofReal (max 0 ((L + s * cδ) / (s - 1))) * ENNReal.ofReal M := by
        rw [ENNReal.ofReal_add (mul_nonneg hη.le hE0)
          (mul_nonneg (le_max_left _ _) hMpos.le), ENNReal.ofReal_mul hη.le,
          ENNReal.ofReal_mul (le_max_left _ _)]

/-- Transfer of the defective inequality to a reference measure with two-sided density bounds. -/
theorem lip041_defect_transfer {d : ℕ} (P : BoundedPositiveReference d) {a1 A1 : ℝ}
    (ha1 : 0 < a1) (hcl : ∀ᵐ x ∂haar d, a1 ≤ P.density x)
    (hCu : ∀ᵐ x ∂haar d, P.density x ≤ A1) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Torus d → ℝ) (hf : f ∈ WeightedH1 P),
      homogeneousEntropy P.measure (fun x => f x ^ 2) ≤
        ENNReal.ofReal η * ∫⁻ x, ‖weightedGradient P f hf x‖ₑ ^ 2 ∂P.measure +
          ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂P.measure := by
  have hApos : 0 < A1 := by
    obtain ⟨x, h1, h2⟩ := (hcl.and hCu).exists
    linarith
  obtain ⟨C0, hC0, hD⟩ := lip041_defect d (η := η * a1 / A1) (by positivity)
  refine ⟨A1 * C0 / a1, by positivity, fun f hf => ?_⟩
  have hW := isWeightedWeakGradient_weightedGradient P hf
  have hg : IsWeakGradient f (weightedGradient P f hf) := (isWeightedWeakGradient_iff P).1 hW
  set g := weightedGradient P f hf with hgdef
  have hv : Integrable (fun x => f x ^ 2) (haar d) := hg.memLp.integrable_sq
  have hent1 := def025_entropy_comparison P hCu (fun x => sq_nonneg (f x)) hv
  have hen : ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂haar d ≤
      ENNReal.ofReal a1⁻¹ * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂P.measure := by
    calc ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂haar d
        ≤ ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂(ENNReal.ofReal a1⁻¹ • P.measure) :=
          lintegral_mono' (def025_haar_le_smul P ha1 hcl) le_rfl
      _ = ENNReal.ofReal a1⁻¹ * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂P.measure := by
          rw [lintegral_smul_measure, smul_eq_mul]
          congr 1
          refine lintegral_congr fun x => ?_
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hmass : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂haar d ≤
      ENNReal.ofReal a1⁻¹ * ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂P.measure := by
    calc ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂haar d
        ≤ ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂(ENNReal.ofReal a1⁻¹ • P.measure) :=
          lintegral_mono' (def025_haar_le_smul P ha1 hcl) le_rfl
      _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]
  set E := ∫⁻ x, ‖g x‖ₑ ^ 2 ∂P.measure with hE
  set Mp := ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂P.measure with hMp
  have hD' := hD f g hg
  calc homogeneousEntropy P.measure (fun x => f x ^ 2)
      ≤ ENNReal.ofReal A1 * homogeneousEntropy (haar d) (fun x => f x ^ 2) := hent1
    _ ≤ ENNReal.ofReal A1 * (ENNReal.ofReal (η * a1 / A1) * (ENNReal.ofReal a1⁻¹ * E) +
          ENNReal.ofReal C0 * (ENNReal.ofReal a1⁻¹ * Mp)) :=
        mul_le_mul' le_rfl (hD'.trans (add_le_add (mul_le_mul' le_rfl hen)
          (mul_le_mul' le_rfl hmass)))
    _ = (ENNReal.ofReal A1 * ENNReal.ofReal (η * a1 / A1) * ENNReal.ofReal a1⁻¹) * E +
          (ENNReal.ofReal A1 * ENNReal.ofReal C0 * ENNReal.ofReal a1⁻¹) * Mp := by ring
    _ = ENNReal.ofReal η * E + ENNReal.ofReal (A1 * C0 / a1) * Mp := by
        have e1 : A1 * (η * a1 / A1) * a1⁻¹ = η := by field_simp
        have e2 : A1 * C0 * a1⁻¹ = A1 * C0 / a1 := by rw [div_eq_mul_inv]
        rw [← ENNReal.ofReal_mul hApos.le, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul hApos.le, ← ENNReal.ofReal_mul (by positivity), e1, e2]

/-- **LIP041 (sharp torus LSI, tensorization, and the fixed-dimensional defect).**
(1) On the circle, `I ≥ 2 a_T H + (a_T/6) H²` and `H ≤ 6 log (1 + I/(12 a_T))` with `a_T = 4π²`.
(2) Hence the Haar LSI rate on `𝕋^d` is exactly `a_T` (the sharp rate is attained and cannot be
exceeded, already on the circle). (3) For each fixed dimension and `η > 0` there is `C_η` with
`Ent_m(f²) ≤ η ∫|∇f|² + C_η ∫ f²`. (4) If `μ = w m` with `0 < a1 ≤ w ≤ A1`, then
`r_LS(μ) ≥ a_T a1 / A1`, and (5) the defective inequality transfers with model-dependent
constants. -/
theorem sharp_torus_lsi_tensorization_and_fixed_dimensional_defect :
    (∀ ρ : AbsoluteDensity 1,
      2 * (4 * Real.pi ^ 2) * Analysis.circleEntropy ρ + (4 * Real.pi ^ 2) / 6 *
          Analysis.circleEntropy ρ ^ 2 ≤ Analysis.circleFisherInformation ρ ∧
        Analysis.circleEntropy ρ ≤
          6 * Real.log (1 + Analysis.circleFisherInformation ρ / (12 * (4 * Real.pi ^ 2)))) ∧
    (∀ a : ℝ, (∀ ρ : AbsoluteDensity 1,
        2 * a * Analysis.circleEntropy ρ ≤ Analysis.circleFisherInformation ρ) →
      a ≤ 4 * Real.pi ^ 2) ∧
    (∀ d : ℕ, 0 < d →
      Analysis.HaarLSI d (4 * Real.pi ^ 2) ∧
        (∀ a : ℝ, Analysis.HaarLSI d a → a ≤ 4 * Real.pi ^ 2) ∧
        Analysis.haarLSIRate d = ENNReal.ofReal (4 * Real.pi ^ 2)) ∧
    (∀ (d : ℕ) {η : ℝ}, 0 < η →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient f g →
        homogeneousEntropy (haar d) (fun x => f x ^ 2) ≤
          ENNReal.ofReal η * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂haar d +
            ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂haar d) ∧
    (∀ (d : ℕ) (P : BoundedPositiveReference d) {a1 A1 : ℝ}, 0 < a1 →
      (∀ᵐ x ∂haar d, a1 ≤ P.density x) → (∀ᵐ x ∂haar d, P.density x ≤ A1) →
      ENNReal.ofReal (4 * Real.pi ^ 2 * a1 / A1) ≤ ordinaryLSRate P ∧
        ∀ {η : ℝ}, 0 < η →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Torus d → ℝ) (hf : f ∈ WeightedH1 P),
            homogeneousEntropy P.measure (fun x => f x ^ 2) ≤
              ENNReal.ofReal η * ∫⁻ x, ‖weightedGradient P f hf x‖ₑ ^ 2 ∂P.measure +
                ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂P.measure) := by
  refine ⟨fun ρ => ?_, fun a h => haar_circle_lsi_sharp h, fun d hd => haar_lsi_sharp hd,
    fun d η hη => lip041_defect d hη, fun d P a1 A1 ha1 hcl hCu => ⟨?_, fun hη =>
      lip041_defect_transfer P ha1 hcl hCu hη⟩⟩
  · obtain ⟨-, -, h3, h4⟩ := Analysis.circle_quantitative_lsi_on_the_absolute_domain ρ
    exact ⟨h3, h4⟩
  · have := def025_lsi_of_density_bounds P ha1 hcl hCu
    simpa [a0] using this

end DGPS.Lipschitz
