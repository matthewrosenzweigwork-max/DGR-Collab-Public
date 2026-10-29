import SharpSymmetricLSI.Paper.UpperApprox3
import SharpSymmetricLSI.Paper.TorusLSI

/-!
# Section 2.2: `limsup r_N^sym ≤ r_*` and the zero-rate case (Phase 3, lane D; R6)
-/

open MeasureTheory Set Filter Topology InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- Admissible densities have finite entropy (sharp LSI on the torus). -/
theorem klDiv_ne_top_of_H1 {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1)
    (hH1 : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) : klDiv (densMeasure ρ) (haar d) ≠ ⊤ := by
  have hρi := integrable_of_integral_eq_one' hρ1
  have hL := lsi_torus_H1 (ι := Fin d) hH1
  have hD : dirichlet volume (fun x => Real.sqrt (ρ x)) ≠ ⊤ := by
    unfold dirichlet
    have h := memLp_two_lintegral_ne_top hH1.2.2
    refine ne_top_of_le_ne_top h (le_of_eq (lintegral_congr fun x => ?_))
    rw [← ofReal_sq_eq_enorm_sq, Real.sq_sqrt (sqNorm_nonneg _)]
  have hent : ent volume (fun x => Real.sqrt (ρ x) ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD) hL
  have e1 : (fun x => Real.sqrt (ρ x) ^ 2) = ρ := funext fun x => Real.sq_sqrt (hρ0 x)
  rw [e1] at hent
  rw [klDiv_densMeasure' hρ0 hρ1]
  unfold ent at hent
  rw [if_pos hρi] at hent
  convert hent using 2
  funext x
  change ENNReal.ofReal (klFun (ρ x)) = ENNReal.ofReal ((∫ y, ρ y ∂haar d) * klFun (ρ x / ∫ y, ρ y ∂haar d))
  rw [hρ1, div_one, one_mul]

/-- Lower semicontinuity of the entropy along a.e. convergent densities. -/
theorem klDiv_le_liminf {ρ : Torus d → ℝ} {ρs : ℕ → Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar d = 1) (hρs0 : ∀ j x, 0 ≤ ρs j x) (hρs1 : ∀ j, ∫ x, ρs j x ∂haar d = 1)
    (hρsm : ∀ j, Measurable (ρs j))
    (hae : ∀ᵐ x ∂haar d, Tendsto (fun j => ρs j x) atTop (𝓝 (ρ x))) :
    klDiv (densMeasure ρ) (haar d) ≤ liminf (fun j => klDiv (densMeasure (ρs j)) (haar d)) atTop := by
  rw [klDiv_densMeasure' hρ0 hρ1]
  simp_rw [klDiv_densMeasure' (hρs0 _) (hρs1 _)]
  have hF := lintegral_liminf_le' (μ := haar d) (u := atTop)
    (fun j => (ENNReal.measurable_ofReal.comp (measurable_klFun.comp (hρsm j))).aemeasurable)
  refine le_trans (le_of_eq ?_) hF
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  have := ((ENNReal.continuous_ofReal.comp continuous_klFun).tendsto _).comp hx
  exact this.liminf_eq.symm

theorem abs_integral_mul_sub_le {f f' g : Torus d → ℝ} (hf : Integrable f (haar d))
    (hf' : Integrable f' (haar d)) (hg : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    |∫ x, f x * g x ∂haar d - ∫ x, f' x * g x ∂haar d| ≤
      B * (∫⁻ x, ‖f x - f' x‖ₑ ∂haar d).toReal := by
  have hi : ∀ {r : Torus d → ℝ}, Integrable r (haar d) → Integrable (fun x => r x * g x) (haar d) :=
    fun {r} hr => (hr.norm.mul_const B).mono' (hr.aestronglyMeasurable.mul hg.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs (g x)]
        exact mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _))
  rw [← integral_sub (hi hf) (hi hf')]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ x, |f x * g x - f' x * g x| ∂haar d ≤ ∫ x, B * |f x - f' x| ∂haar d :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          ((hf.sub hf').abs.const_mul B) (Eventually.of_forall fun x => by
            show |f x * g x - f' x * g x| ≤ B * |f x - f' x|
            rw [← sub_mul, abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _))
    _ = B * (∫⁻ x, ‖f x - f' x‖ₑ ∂haar d).toReal := by
        rw [integral_const_mul]
        congr 1
        have := integral_norm_eq_lintegral_enorm (μ := haar d) (hf.sub hf').aestronglyMeasurable
        simpa [Real.norm_eq_abs] using this

theorem tendsto_of_abs_le {a : ℕ → ℝ} {a₀ : ℝ} {e : ℕ → ℝ≥0∞} {B : ℝ}
    (he : Tendsto e atTop (𝓝 0)) (hb : ∀ j, |a j - a₀| ≤ B * (e j).toReal) :
    Tendsto a atTop (𝓝 a₀) := by
  have hz : Tendsto (fun j => B * (e j).toReal) atTop (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he).const_mul B
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero_norm (fun j => by rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]; exact hb j) hz

theorem potE_tendsto (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} {ρs : ℕ → Torus d → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1) (hρs0 : ∀ j x, 0 ≤ ρs j x)
    (hρs1 : ∀ j, ∫ x, ρs j x ∂haar d = 1)
    (hL1 : Tendsto (fun j => ∫⁻ x, ‖ρs j x - ρ x‖ₑ ∂haar d) atTop (𝓝 0)) :
    Tendsto (fun j => potE V (densMeasure (ρs j))) atTop (𝓝 (potE V (densMeasure ρ))) := by
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
  refine tendsto_of_abs_le (B := BV) hL1 fun j => ?_
  unfold potE
  rw [integral_densMeasure' (hρs0 j) (hρs1 j), integral_densMeasure' hρ0 hρ1]
  exact abs_integral_mul_sub_le (integrable_of_integral_eq_one' (hρs1 j))
    (integrable_of_integral_eq_one' hρ1) hyp.continuous_V.measurable hBV

theorem interE_densMeasure {f : Torus d → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∫ x, f x ∂haar d = 1) :
    interE W (densMeasure f) (densMeasure f) =
      ∫ y, f y * (∫ x, f x * W x y ∂haar d) ∂haar d := by
  unfold interE
  rw [integral_densMeasure' hf0 hf1]
  congr 1; funext y
  rw [integral_densMeasure' hf0 hf1]

theorem interE_tendsto (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} {ρs : ℕ → Torus d → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1) (hρs0 : ∀ j x, 0 ≤ ρs j x)
    (hρs1 : ∀ j, ∫ x, ρs j x ∂haar d = 1)
    (hL1 : Tendsto (fun j => ∫⁻ x, ‖ρs j x - ρ x‖ₑ ∂haar d) atTop (𝓝 0)) :
    Tendsto (fun j => interE W (densMeasure (ρs j)) (densMeasure (ρs j))) atTop
      (𝓝 (interE W (densMeasure ρ) (densMeasure ρ))) := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hBW0 : 0 ≤ BW := (abs_nonneg _).trans (hBW 0)
  have hWm : Measurable (Function.uncurry W) := hyp.continuous_W.measurable
  have hρi := integrable_of_integral_eq_one' hρ1
  have hρsi : ∀ j, Integrable (ρs j) (haar d) := fun j => integrable_of_integral_eq_one' (hρs1 j)
  set h : (Torus d → ℝ) → Torus d → ℝ := fun f y => ∫ x, f x * W x y ∂haar d with hh
  have hhm : ∀ {f : Torus d → ℝ}, Integrable f (haar d) → Measurable (h f) := fun {f} hf => by
    set f' := hf.aestronglyMeasurable.mk f
    have hff : f =ᵐ[haar d] f' := hf.aestronglyMeasurable.ae_eq_mk
    have e : h f = h f' := funext fun y => integral_congr_ae (hff.mono fun x hx => by
      simp only [hx])
    rw [e]
    exact (((hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable.comp measurable_fst).mul
      hWm).stronglyMeasurable.integral_prod_left (μ := haar d)
        (f := fun x y => f' x * W x y)).measurable
  have hhb : ∀ {f : Torus d → ℝ}, (∀ x, 0 ≤ f x) → ∫ x, f x ∂haar d = 1 → ∀ y, |h f y| ≤ BW :=
    fun {f} hf0 hf1 y => by
      have := abs_integral_mul_sub_le (f := f) (f' := fun _ => 0) (g := fun x => W x y)
        (integrable_of_integral_eq_one' hf1) (integrable_const 0)
        (hyp.continuous_W.comp (continuous_id.prodMk continuous_const)).measurable
        (fun x => hBW (x, y))
      simp only [zero_mul, integral_zero, sub_zero] at this
      refine this.trans ?_
      have h1 : (∫⁻ x, ‖f x‖ₑ ∂haar d).toReal = 1 := by
        have := integral_norm_eq_lintegral_enorm (μ := haar d)
          (integrable_of_integral_eq_one' hf1).aestronglyMeasurable
        rw [← this]
        simp_rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
        exact hf1
      rw [h1, mul_one]
  have hhd : ∀ j y, |h (ρs j) y - h ρ y| ≤ BW * (∫⁻ x, ‖ρs j x - ρ x‖ₑ ∂haar d).toReal :=
    fun j y => abs_integral_mul_sub_le (hρsi j) hρi
      (hyp.continuous_W.comp (continuous_id.prodMk continuous_const)).measurable
      (fun x => hBW (x, y))
  refine tendsto_of_abs_le (B := 2 * BW) hL1 fun j => ?_
  rw [interE_densMeasure (hρs0 j) (hρs1 j), interE_densMeasure hρ0 hρ1]
  have e1 := abs_integral_mul_sub_le (hρsi j) hρi (hhm (hρsi j)) (hhb (hρs0 j) (hρs1 j))
  have hi : Integrable (fun y => ρ y * h (ρs j) y) (haar d) :=
    (hρi.norm.mul_const BW).mono' (hρi.aestronglyMeasurable.mul (hhm (hρsi j)).aestronglyMeasurable)
      (Eventually.of_forall fun y => by
        rw [norm_mul, Real.norm_eq_abs (h (ρs j) y)]
        exact mul_le_mul_of_nonneg_left (hhb (hρs0 j) (hρs1 j) y) (norm_nonneg _))
  have hi2 : Integrable (fun y => ρ y * h ρ y) (haar d) :=
    (hρi.norm.mul_const BW).mono' (hρi.aestronglyMeasurable.mul (hhm hρi).aestronglyMeasurable)
      (Eventually.of_forall fun y => by
        rw [norm_mul, Real.norm_eq_abs (h ρ y)]
        exact mul_le_mul_of_nonneg_left (hhb hρ0 hρ1 y) (norm_nonneg _))
  have e2 : |∫ y, ρ y * h (ρs j) y ∂haar d - ∫ y, ρ y * h ρ y ∂haar d| ≤
      BW * (∫⁻ x, ‖ρs j x - ρ x‖ₑ ∂haar d).toReal := by
    rw [← integral_sub hi hi2]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |ρ y * h (ρs j) y - ρ y * h ρ y| ∂haar d
        ≤ ∫ y, ρ y * (BW * (∫⁻ x, ‖ρs j x - ρ x‖ₑ ∂haar d).toReal) ∂haar d :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            (hρi.mul_const _) (Eventually.of_forall fun y => by
              show |ρ y * h (ρs j) y - ρ y * h ρ y| ≤ _
              rw [← mul_sub, abs_mul, abs_of_nonneg (hρ0 y)]
              exact mul_le_mul_of_nonneg_left (hhd j y) (hρ0 y))
      _ = _ := by rw [integral_mul_const, hρ1, one_mul]
  calc |∫ y, ρs j y * h (ρs j) y ∂haar d - ∫ y, ρ y * h ρ y ∂haar d|
      ≤ |∫ y, ρs j y * h (ρs j) y ∂haar d - ∫ y, ρ y * h (ρs j) y ∂haar d| +
        |∫ y, ρ y * h (ρs j) y ∂haar d - ∫ y, ρ y * h ρ y ∂haar d| := abs_sub_le _ _ _
    _ ≤ BW * (∫⁻ x, ‖ρs j x - ρ x‖ₑ ∂haar d).toReal +
        BW * (∫⁻ x, ‖ρs j x - ρ x‖ₑ ∂haar d).toReal := add_le_add e1 e2
    _ = 2 * BW * (∫⁻ x, ‖ρs j x - ρ x‖ₑ ∂haar d).toReal := by ring

/-- **Section 2.2**: `limsup r_N^sym ≤ r_*`. -/
theorem upper_bound_aux (hyp : Hyp V W KV KW) :
    limsup (fun N => rSym V W N) atTop ≤ rStar V W := by
  unfold rStar
  refine le_iInf₂ fun ρ hρ => ?_
  obtain ⟨hρ0, hρ1, hH1, hG⟩ := hρ
  have hK := klDiv_ne_top_of_H1 hρ0 hρ1 hH1
  have := isProbabilityMeasure_densMeasure' hρ0 hρ1
  set F := (Fstar V W).toReal
  set KL := (klDiv (densMeasure ρ) (haar d)).toReal
  set E := energyMF V W (densMeasure ρ)
  have hgap : gap V W (densMeasure ρ) = ((KL + E - F : ℝ) : EReal) := gap_eq_coe hyp hK
  set g := KL + E - F with hgdef
  have hgpos : 0 < g := by rw [hgap] at hG; exact_mod_cast hG
  have hgE : (gap V W (densMeasure ρ)).toENNReal = ENNReal.ofReal g := by
    rw [hgap]; simp [EReal.toENNReal]
  have h2g : (2 : ℝ≥0∞) * ENNReal.ofReal g ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  by_cases hDt : dissipation V W ρ = ⊤
  · rw [hDt, hgE, ENNReal.top_div_of_ne_top h2g]; exact le_top
  set D := (dissipation V W ρ).toReal
  have hDD : dissipation V W ρ = ENNReal.ofReal D := (ENNReal.ofReal_toReal hDt).symm
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  obtain ⟨ρs, hρs, hL1, hae, hlim⟩ := approx_dissipation hyp hρ0 hρ1 hH1
  have hρs0 : ∀ j x, 0 ≤ ρs j x := fun j x => ((hρs j).2.1 x).le
  have hρs1 : ∀ j, ∫ x, ρs j x ∂haar d = 1 := fun j => (hρs j).2.2
  have hρsK : ∀ j, klDiv (densMeasure (ρs j)) (haar d) ≠ ⊤ := fun j =>
    klDiv_densMeasure_ne_top_of_continuous (hρs j).1.continuous (hρs0 j) (hρs1 j)
  have hgj : ∀ j, gap V W (densMeasure (ρs j)) =
      (((klDiv (densMeasure (ρs j)) (haar d)).toReal + energyMF V W (densMeasure (ρs j)) - F : ℝ) :
        EReal) := fun j => gap_eq_coe hyp (hρsK j)
  have hEl : Tendsto (fun j => energyMF V W (densMeasure (ρs j))) atTop (𝓝 E) :=
    (potE_tendsto hyp hρ0 hρ1 hρs0 hρs1 hL1).add
      ((interE_tendsto hyp hρ0 hρ1 hρs0 hρs1 hL1).div_const 2)
  have hKl := klDiv_le_liminf hρ0 hρ1 hρs0 hρs1 (fun j => (hρs j).1.continuous.measurable) hae
  have hkey : ∀ ε : ℝ, 0 < ε → ε < g / 2 →
      limsup (fun N => rSym V W N) atTop ≤ ENNReal.ofReal ((D + ε) / (2 * (g - ε))) := by
    intro ε hε hεg
    have hD_ev : ∀ᶠ j in atTop, dissipation V W (ρs j) < ENNReal.ofReal (D + ε) := by
      refine eventually_lt_of_limsup_lt (hlim.trans_lt ?_)
      rw [hDD]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
    have hK_ev : ∀ᶠ j in atTop, KL - ε / 2 ≤ (klDiv (densMeasure (ρs j)) (haar d)).toReal := by
      by_cases hsmall : KL ≤ ε / 2
      · exact Eventually.of_forall fun j => by linarith [(ENNReal.toReal_nonneg :
          0 ≤ (klDiv (densMeasure (ρs j)) (haar d)).toReal)]
      · push_neg at hsmall
        have hlt : ENNReal.ofReal (KL - ε / 2) < klDiv (densMeasure ρ) (haar d) := by
          rw [← ENNReal.ofReal_toReal hK]
          exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
        filter_upwards [eventually_lt_of_lt_liminf (hlt.trans_le hKl)] with j hj
        exact ((ENNReal.ofReal_le_iff_le_toReal (hρsK j)).mp hj.le)
    have hE_ev : ∀ᶠ j in atTop, E - ε / 2 ≤ energyMF V W (densMeasure (ρs j)) :=
      (hEl.eventually (lt_mem_nhds (by linarith : E - ε / 2 < E))).mono fun j hj => hj.le
    obtain ⟨j, hj1, hj2, hj3⟩ := (hD_ev.and (hK_ev.and hE_ev)).exists
    set gj := (klDiv (densMeasure (ρs j)) (haar d)).toReal + energyMF V W (densMeasure (ρs j)) - F
    have hgjle : g - ε ≤ gj := by simp only [gj, hgdef]; linarith
    have hgjpos : 0 < gj := by linarith
    have hGj : 0 < gap V W (densMeasure (ρs j)) := by rw [hgj j]; exact_mod_cast hgjpos
    have hUC := upper_comparison_aux hyp (hρs j).1 (hρs j).2.1 (hρs j).2.2 hGj
    refine hUC.trans ?_
    have hDjne : dissipation V W (ρs j) ≠ ⊤ := ne_top_of_lt hj1
    have hgjE : (gap V W (densMeasure (ρs j))).toENNReal = ENNReal.ofReal gj := by
      rw [hgj j, EReal.toENNReal, if_neg (EReal.coe_ne_top _), EReal.toReal_coe]
    rw [← ENNReal.ofReal_toReal hDjne, hgjE, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_div_of_pos (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hDj : (dissipation V W (ρs j)).toReal ≤ D + ε :=
      ENNReal.toReal_le_of_le_ofReal (by linarith) hj1.le
    exact div_le_div₀ (by linarith) hDj (by linarith) (by linarith)
  set e : ℕ → ℝ := fun n => g / (4 * ((n : ℝ) + 1)) with he
  have he0 : ∀ n, 0 < e n := fun n => by simp only [he]; positivity
  have heg : ∀ n, e n < g / 2 := fun n => by
    simp only [he]
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hel : Tendsto e atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := h1.const_mul (g / 4)
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    simp only [he]; field_simp
  have hlimit : Tendsto (fun n => ENNReal.ofReal ((D + e n) / (2 * (g - e n)))) atTop
      (𝓝 (ENNReal.ofReal (D / (2 * g)))) := by
    refine ENNReal.tendsto_ofReal ?_
    have := ((tendsto_const_nhds (x := D)).add hel).div
      ((tendsto_const_nhds (x := (2 : ℝ))).mul ((tendsto_const_nhds (x := g)).sub hel))
      (by simp; exact hgpos.ne')
    simp only [add_zero, sub_zero] at this
    exact this.congr fun n => rfl
  have hfinal : limsup (fun N => rSym V W N) atTop ≤ ENNReal.ofReal (D / (2 * g)) :=
    ge_of_tendsto hlimit (Eventually.of_forall fun n => hkey (e n) (he0 n) (heg n))
  rw [hDD, hgE, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_div_of_pos (by positivity)]
  exact hfinal

/-- **The zero-rate case**. -/
theorem zero_rate_aux (hyp : Hyp V W KV KW) (h0 : rStar V W = 0) :
    Tendsto (fun N => rSym V W N) atTop (𝓝 0) := by
  have hl : limsup (fun N => rSym V W N) atTop = 0 :=
    le_antisymm ((upper_bound_aux hyp).trans h0.le) zero_le
  exact tendsto_of_le_liminf_of_limsup_le zero_le hl.le

end SharpLSI
