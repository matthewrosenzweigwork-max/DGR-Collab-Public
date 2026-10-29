import SharpSymmetricLSI.Paper.ParticleForce
import SharpSymmetricLSI.Paper.TorusLipschitz
import SharpSymmetricLSI.Paper.CondForce1

/-!
# Lemma 4.1, (4.1): the Euler–Lagrange equation (Phase 3, lane D; R13)

For a minimizer with density `f` and `q = e^{-Φ}/Z`, `Φ = V + W*μ`, the first variation of `F`
along `(1-t)f + tq` gives `∫ klFun f + ∫ fΦ ≤ ∫ klFun q + ∫ qΦ = -log Z`, i.e.
`∫ f log(f/q) ≤ 0`, hence `f = q` a.e. (Gibbs inequality, written with `klFun`).
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The Euler–Lagrange density (a copy of `elDensity` from the R13 statement file). -/
noncomputable def elDens (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (x : Torus d) : ℝ :=
  Real.exp (-V x - convMeas W μ x) / ∫ y, Real.exp (-V y - convMeas W μ y) ∂haar d

theorem eq_densMeasure_densOf {μ : Measure (Torus d)} [IsFiniteMeasure μ] (hac : μ ≪ haar d) :
    μ = densMeasure (densOf μ) := by
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ (haar d) hac]
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top μ (haar d)] with x hx
  simp only [densOf, ENNReal.ofReal_toReal hx.ne]

/-- The bilinear form `A(h₁,h₂) = ∫ h₂ (W*h₁) dm`. -/
def Aform (W : Torus d → Torus d → ℝ) (h₁ h₂ : Torus d → ℝ) : ℝ :=
  ∫ x, h₂ x * convDens W h₁ x ∂haar d

/-- Elementary: `0 ≤ tX + t²Y` for all `t ∈ (0,1]` forces `0 ≤ X`. -/
theorem nonneg_of_forall_small {X Y : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ t * X + t ^ 2 * Y) :
    0 ≤ X := by
  by_contra hX
  push_neg at hX
  set t := min 1 (-X / (2 * (|Y| + 1))) with ht
  have hY : 0 < |Y| + 1 := by positivity
  have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ -X / (2 * (|Y| + 1)) := min_le_right _ _
  have h1 := h t ht0 ht1
  have h2 : t ^ 2 * Y ≤ t * (t * (|Y| + 1)) := by
    have : Y ≤ |Y| + 1 := by linarith [le_abs_self Y]
    nlinarith [sq_nonneg t]
  have h3 : t * (|Y| + 1) ≤ -X / 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (|Y| + 1))] at ht2
    linarith
  nlinarith

theorem integral_lin4 {α : Type*} [MeasurableSpace α] {P : Measure α} {f₁ f₂ f₃ f₄ : α → ℝ}
    (i₁ : Integrable f₁ P) (i₂ : Integrable f₂ P) (i₃ : Integrable f₃ P) (i₄ : Integrable f₄ P)
    (a b c e : ℝ) :
    ∫ x, (a * f₁ x + b * f₂ x + c * f₃ x + e * f₄ x) ∂P =
      a * ∫ x, f₁ x ∂P + b * ∫ x, f₂ x ∂P + c * ∫ x, f₃ x ∂P + e * ∫ x, f₄ x ∂P := by
  rw [integral_add (f := fun x => a * f₁ x + b * f₂ x + c * f₃ x) (g := fun x => e * f₄ x)
      (((i₁.const_mul a).add (i₂.const_mul b)).add (i₃.const_mul c)) (i₄.const_mul e),
    integral_add (f := fun x => a * f₁ x + b * f₂ x) (g := fun x => c * f₃ x)
      ((i₁.const_mul a).add (i₂.const_mul b)) (i₃.const_mul c),
    integral_add (f := fun x => a * f₁ x) (g := fun x => b * f₂ x) (i₁.const_mul a) (i₂.const_mul b),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]

theorem minimizer_klDiv_ne_top {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) :
    klDiv (μ : Measure (Torus d)) (haar d) ≠ ⊤ := by
  have hle : freeEnergy V W μ ≤ freeEnergy V W (haar d) := by
    unfold IsMinimizer at hμ
    rw [hμ]
    exact iInf_le (fun ρ : ProbabilityMeasure (Torus d) => freeEnergy V W ρ)
      ⟨haar d, inferInstance⟩
  have hF : freeEnergy V W μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hle
    unfold freeEnergy
    simp only [klDiv_self, EReal.coe_ennreal_zero, zero_add]
    exact EReal.coe_ne_top _
  intro h
  apply hF
  unfold freeEnergy
  rw [h]
  simp

/-- The potential `Φ = V + W*μ` is bounded by `‖V‖∞ + ‖W‖∞`. -/
theorem abs_potential_le {BV BW : ℝ} (hBV : ∀ x, |V x| ≤ BV)
    (hBW : ∀ x y, |W x y| ≤ BW) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (x : Torus d) :
    |V x + convMeas W μ x| ≤ BV + BW := by
  refine (abs_add_le _ _).trans (add_le_add (hBV x) ?_)
  exact abs_integral_le_of_bdd fun y => hBW x y

section dens
variable (hyp : Hyp V W KV KW)
include hyp

theorem convDens_bdd {h : Torus d → ℝ} (hi : Integrable h (haar d)) :
    ∃ C, ∀ x, |convDens W h x| ≤ C := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  refine ⟨BW * ∫ y, |h y| ∂haar d, fun x => (abs_integral_le_integral_abs).trans ?_⟩
  calc ∫ y, |W x y * h y| ∂haar d ≤ ∫ y, BW * |h y| ∂haar d :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (hi.abs.const_mul BW) (Eventually.of_forall fun y => by
            show |W x y * h y| ≤ BW * |h y|
            rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hBW (x, y)) (abs_nonneg _))
    _ = _ := integral_const_mul _ _

theorem measurable_convDens {h : Torus d → ℝ} (hm : Measurable h) :
    Measurable (convDens W h) :=
  ((hyp.continuous_W.measurable.mul (hm.comp measurable_snd)).stronglyMeasurable.integral_prod_right
    (ν := haar d) (f := fun x y => W x y * h y)).measurable

theorem integrable_mul_convDens {h₁ h₂ : Torus d → ℝ} (hm₁ : Measurable h₁)
    (hi₁ : Integrable h₁ (haar d)) (hi₂ : Integrable h₂ (haar d)) :
    Integrable (fun x => h₂ x * convDens W h₁ x) (haar d) := by
  obtain ⟨C, hC⟩ := convDens_bdd hyp hi₁
  refine Integrable.mono' (hi₂.abs.mul_const C) (hi₂.aestronglyMeasurable.mul
    (measurable_convDens hyp hm₁).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

theorem convDens_add {h₁ h₂ : Torus d → ℝ} (hi₁ : Integrable h₁ (haar d))
    (hi₂ : Integrable h₂ (haar d)) (a b : ℝ) (x : Torus d) :
    convDens W (fun y => a * h₁ y + b * h₂ y) x = a * convDens W h₁ x + b * convDens W h₂ x := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hWm : Measurable fun y => W x y := hyp.continuous_W.measurable.comp measurable_prodMk_left
  have i : ∀ {h : Torus d → ℝ}, Integrable h (haar d) → Integrable (fun y => W x y * h y) (haar d) :=
    fun {h} hi => Integrable.mono' (hi.abs.const_mul BW) (hWm.aestronglyMeasurable.mul
      hi.aestronglyMeasurable) (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hBW (x, y)) (abs_nonneg _))
  unfold convDens
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((i hi₁).const_mul a)
    ((i hi₂).const_mul b)]
  congr 1; funext y; ring

/-- Symmetry of `A` (Fubini and `W(x,y) = W(y,x)`). -/
theorem Aform_comm {h₁ h₂ : Torus d → ℝ} (hm₁ : Measurable h₁) (hm₂ : Measurable h₂)
    (hi₁ : Integrable h₁ (haar d)) (hi₂ : Integrable h₂ (haar d)) :
    Aform W h₁ h₂ = Aform W h₂ h₁ := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hint : Integrable (Function.uncurry fun x y => h₂ x * (W x y * h₁ y))
      ((haar d).prod (haar d)) := by
    refine Integrable.mono' ((hi₂.abs.mul_prod hi₁.abs).const_mul BW) ?_
      (Eventually.of_forall fun p => ?_)
    · exact ((hm₂.comp measurable_fst).mul (hyp.continuous_W.measurable.mul
        (hm₁.comp measurable_snd))).aestronglyMeasurable
    · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
      have := hBW p
      calc |h₂ p.1| * (|W p.1 p.2| * |h₁ p.2|) ≤ |h₂ p.1| * (BW * |h₁ p.2|) := by gcongr; exact this
        _ = BW * (|h₂ p.1| * |h₁ p.2|) := by ring
  unfold Aform convDens
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [hyp.symm]; ring

/-- `F(ρ) = ∫ klFun ρ + ∫ ρV + A(ρ,ρ)/2` for a density with `klFun ∘ ρ` integrable. -/
theorem freeEnergy_densMeasure {h : Torus d → ℝ} (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x)
    (h1 : ∫ x, h x ∂haar d = 1) (hK : Integrable (fun x => klFun (h x)) (haar d)) :
    freeEnergy V W (densMeasure h) =
      ((∫ x, klFun (h x) ∂haar d + ∫ x, h x * V x ∂haar d + Aform W h h / 2 : ℝ) : EReal) := by
  have hKd := klDiv_densMeasure' h0 h1
  have hKe : klDiv (densMeasure h) (haar d) = ENNReal.ofReal (∫ x, klFun (h x) ∂haar d) := by
    rw [hKd, ofReal_integral_eq_lintegral_ofReal hK (Eventually.of_forall fun x =>
      klFun_nonneg (h0 x))]
  have hne : klDiv (densMeasure h) (haar d) ≠ ⊤ := by rw [hKe]; exact ENNReal.ofReal_ne_top
  rw [freeEnergy_eq _ hne, hKe, ENNReal.toReal_ofReal (integral_nonneg fun x => klFun_nonneg (h0 x))]
  have hp : potE V (densMeasure h) = ∫ x, h x * V x ∂haar d := integral_densMeasure' h0 h1 V
  have hi : interE W (densMeasure h) (densMeasure h) = Aform W h h := by
    unfold interE Aform convDens
    rw [integral_densMeasure' h0 h1]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [integral_densMeasure' h0 h1]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [hyp.symm]; ring
  unfold energyMF
  rw [hp, hi]
  congr 1
  ring
/-- **First variation**: `∫klFun f + ∫fV + A(f,f) ≤ ∫klFun g + ∫gV + A(f,g)`. -/
theorem first_variation {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {f g : Torus d → ℝ} (hfm : Measurable f) (hgm : Measurable g) (hf0 : ∀ x, 0 ≤ f x)
    (hg0 : ∀ x, 0 ≤ g x) (hf1 : ∫ x, f x ∂haar d = 1) (hg1 : ∫ x, g x ∂haar d = 1)
    (hKf : Integrable (fun x => klFun (f x)) (haar d))
    (hKg : Integrable (fun x => klFun (g x)) (haar d))
    (hμf : (μ : Measure (Torus d)) = densMeasure f) :
    ∫ x, klFun (f x) ∂haar d + ∫ x, f x * V x ∂haar d + Aform W f f ≤
      ∫ x, klFun (g x) ∂haar d + ∫ x, g x * V x ∂haar d + Aform W f g := by
  have hfi := integrable_of_integral_eq_one' hf1
  have hgi := integrable_of_integral_eq_one' hg1
  have hVi : ∀ {h : Torus d → ℝ}, Integrable h (haar d) → Integrable (fun x => h x * V x) (haar d) :=
    fun {h} hi => by
      obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
      exact Integrable.mono' (hi.abs.mul_const BV) (hi.aestronglyMeasurable.mul
        hyp.continuous_V.aestronglyMeasurable) (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_left (hBV x) (abs_nonneg _))
  set Kf := ∫ x, klFun (f x) ∂haar d
  set Kg := ∫ x, klFun (g x) ∂haar d
  set Vf := ∫ x, f x * V x ∂haar d
  set Vg := ∫ x, g x * V x ∂haar d
  have hAcomm := Aform_comm hyp hfm hgm hfi hgi
  suffices hX : 0 ≤ (Kg + Vg + Aform W f g) - (Kf + Vf + Aform W f f) by linarith
  refine nonneg_of_forall_small (Y := Aform W f f / 2 - Aform W f g + Aform W g g / 2)
    fun t ht0 ht1 => ?_
  set h : Torus d → ℝ := fun x => (1 - t) * f x + t * g x with hh
  have hhm : Measurable h := (measurable_const.mul hfm).add (measurable_const.mul hgm)
  have hh0 : ∀ x, 0 ≤ h x := fun x => by
    simp only [hh]; have := hf0 x; have := hg0 x; nlinarith
  have hhi : Integrable h (haar d) := (hfi.const_mul _).add (hgi.const_mul _)
  have hh1 : ∫ x, h x ∂haar d = 1 := by
    rw [integral_add (hfi.const_mul _) (hgi.const_mul _), integral_const_mul, integral_const_mul,
      hf1, hg1]; ring
  have hconv : ∀ x, klFun (h x) ≤ (1 - t) * klFun (f x) + t * klFun (g x) := fun x =>
    convexOn_klFun.2 (Set.mem_Ici.mpr (hf0 x)) (Set.mem_Ici.mpr (hg0 x)) (by linarith) ht0.le
      (by ring)
  have hKh : Integrable (fun x => klFun (h x)) (haar d) :=
    Integrable.mono' ((hKf.const_mul _).add (hKg.const_mul _))
      (measurable_klFun.comp hhm).aestronglyMeasurable (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg (hh0 x))]; exact hconv x)
  -- `F(μ) ≤ F(ρ_t)`
  haveI := isProbabilityMeasure_densMeasure' hh0 hh1
  have hle : freeEnergy V W (μ : Measure (Torus d)) ≤ freeEnergy V W (densMeasure h) := by
    unfold IsMinimizer at hμ
    rw [hμ]
    exact iInf_le (fun ρ : ProbabilityMeasure (Torus d) => freeEnergy V W ρ) ⟨densMeasure h, inferInstance⟩
  rw [hμf, freeEnergy_densMeasure hyp hfm hf0 hf1 hKf,
    freeEnergy_densMeasure hyp hhm hh0 hh1 hKh, EReal.coe_le_coe_iff] at hle
  -- the three pieces of `F(ρ_t)`
  have hK : ∫ x, klFun (h x) ∂haar d ≤ (1 - t) * Kf + t * Kg := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hKf.const_mul _)
      (hKg.const_mul _)]
    exact integral_mono hKh ((hKf.const_mul _).add (hKg.const_mul _)) hconv
  have hV : ∫ x, h x * V x ∂haar d = (1 - t) * Vf + t * Vg := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hVi hfi).const_mul _)
      ((hVi hgi).const_mul _)]
    congr 1; funext x; simp only [hh]; ring
  have hA : Aform W h h = (1 - t) ^ 2 * Aform W f f + 2 * t * (1 - t) * Aform W f g +
      t ^ 2 * Aform W g g := by
    have hc : ∀ x, convDens W h x = (1 - t) * convDens W f x + t * convDens W g x :=
      convDens_add hyp hfi hgi _ _
    have i1 := integrable_mul_convDens hyp hfm hfi hfi
    have i2 := integrable_mul_convDens hyp hgm hgi hfi
    have i3 := integrable_mul_convDens hyp hfm hfi hgi
    have i4 := integrable_mul_convDens hyp hgm hgi hgi
    unfold Aform at hAcomm ⊢
    simp_rw [hc]
    have e : ∀ x, h x * ((1 - t) * convDens W f x + t * convDens W g x) =
        (1 - t) ^ 2 * (f x * convDens W f x) + (1 - t) * t * (f x * convDens W g x) +
        t * (1 - t) * (g x * convDens W f x) + t ^ 2 * (g x * convDens W g x) := fun x => by
      simp only [hh]; ring
    simp_rw [e]
    rw [integral_lin4 i1 i2 i3 i4, ← hAcomm]
    ring
  rw [hV, hA] at hle
  nlinarith [hK]

/-- **(4.1)**: a minimizer is the Euler–Lagrange density. -/
theorem minimizer_eq_elDensity {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) :
    (μ : Measure (Torus d)) = densMeasure (elDens V W μ) := by
  have hac := minimizer_ac hyp hμ
  set μm := (μ : Measure (Torus d))
  set f := densOf μm with hfdef
  have hμf : μm = densMeasure f := eq_densMeasure_densOf hac
  have hfm : Measurable f := measurable_densOf μm
  have hf0 : ∀ x, 0 ≤ f x := fun x => ENNReal.toReal_nonneg
  have hf1 : ∫ x, f x ∂haar d = 1 := integral_densOf_eq_one hac
  have hfi := integrable_of_integral_eq_one' hf1
  have hKf : Integrable (fun x => klFun (f x)) (haar d) := by
    have h := minimizer_klDiv_ne_top hμ
    rw [show (μ : Measure (Torus d)) = μm from rfl, hμf, klDiv_densMeasure' hf0 hf1] at h
    exact (lintegral_ofReal_ne_top_iff_integrable (measurable_klFun.comp hfm).aestronglyMeasurable
      (Eventually.of_forall fun x => klFun_nonneg (hf0 x))).mp h
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  set B := BV + BW
  set Φ : Torus d → ℝ := fun x => V x + convMeas W μm x with hΦ
  have hΦb : ∀ x, |Φ x| ≤ B := fun x => abs_potential_le hBV (fun x y => hBW (x, y)) μm x
  have hΦm : Measurable Φ := hyp.continuous_V.measurable.add (by
    rw [convMeas_eq_convDens hac]; exact measurable_convDens hyp hfm)
  set Z := ∫ y, exp (-Φ y) ∂haar d with hZ
  have hei : Integrable (fun y => exp (-Φ y)) (haar d) :=
    integrable_of_bdd (measurable_exp.comp hΦm.neg) (C := exp B) fun y => by
      rw [abs_of_pos (exp_pos _)]; exact exp_le_exp.mpr (by linarith [neg_le_abs (Φ y), hΦb y])
  have hZpos : 0 < Z := integral_exp_pos hei
  set g := elDens V W μm with hgdef
  have hg : ∀ x, g x = exp (-Φ x) / Z := fun x => by
    simp only [hgdef, elDens, hΦ, hZ, neg_add']
  have hgpos : ∀ x, 0 < g x := fun x => by rw [hg]; positivity
  have hgm : Measurable g := by
    have : g = fun x => exp (-Φ x) / Z := funext hg
    rw [this]; exact (measurable_exp.comp hΦm.neg).div_const _
  have hg1 : ∫ x, g x ∂haar d = 1 := by
    simp_rw [hg]; rw [integral_div, ← hZ, div_self hZpos.ne']
  have hgb : ∀ x, g x ≤ exp B / Z := fun x => by
    rw [hg]; gcongr; linarith [neg_le_abs (Φ x), hΦb x]
  have hgi := integrable_of_integral_eq_one' hg1
  have hKg : Integrable (fun x => klFun (g x)) (haar d) := by
    have := (klDiv_densMeasure_bdd hgm (fun x => (hgpos x).le) hg1 hgb)
    have hlt := this.1
    rw [klDiv_densMeasure' (fun x => (hgpos x).le) hg1] at hlt
    exact (lintegral_ofReal_ne_top_iff_integrable (measurable_klFun.comp hgm).aestronglyMeasurable
      (Eventually.of_forall fun x => klFun_nonneg (hgpos x).le)).mp hlt
  have hFV := first_variation hyp hμ hfm hgm hf0 (fun x => (hgpos x).le) hf1 hg1 hKf hKg hμf
  -- rewrite both sides with `Φ`
  have hconv : ∀ x, convDens W f x = convMeas W μm x := fun x => by
    rw [convMeas_eq_convDens hac]
  have hΦi : ∀ {h : Torus d → ℝ}, Integrable h (haar d) → Integrable (fun x => h x * Φ x) (haar d) :=
    fun {h} hi => Integrable.mono' (hi.abs.mul_const B) (hi.aestronglyMeasurable.mul
      hΦm.aestronglyMeasurable) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_left (hΦb x) (abs_nonneg _))
  have hVi : ∀ {h : Torus d → ℝ}, Integrable h (haar d) → Integrable (fun x => h x * V x) (haar d) :=
    fun {h} hi => Integrable.mono' (hi.abs.mul_const BV) (hi.aestronglyMeasurable.mul
      hyp.continuous_V.aestronglyMeasurable) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_left (hBV x) (abs_nonneg _))
  have hsplit : ∀ {h : Torus d → ℝ}, Integrable h (haar d) →
      ∫ x, h x * V x ∂haar d + Aform W f h = ∫ x, h x * Φ x ∂haar d := fun {h} hi => by
    unfold Aform
    rw [← integral_add (hVi hi) (integrable_mul_convDens hyp hfm hfi hi)]
    congr 1; funext x; rw [hconv, hΦ]; ring
  rw [add_assoc, add_assoc, hsplit hfi, hsplit hgi] at hFV
  -- the Gibbs side equals `-log Z`
  have hlogg : ∀ x, Real.log (g x) = -Φ x - Real.log Z := fun x => by
    rw [hg, Real.log_div (exp_pos _).ne' hZpos.ne', Real.log_exp]
  have hRHS : ∫ x, klFun (g x) ∂haar d + ∫ x, g x * Φ x ∂haar d = -Real.log Z := by
    rw [← integral_add hKg (hΦi hgi)]
    have e : ∀ x, klFun (g x) + g x * Φ x = 1 - g x - Real.log Z * g x := fun x => by
      rw [klFun_apply, hlogg]; ring
    simp_rw [e]
    rw [integral_sub (f := fun x => 1 - g x) (g := fun x => Real.log Z * g x)
      ((integrable_const 1).sub hgi) (hgi.const_mul _), integral_sub (f := fun _ => (1 : ℝ))
      (g := g) (integrable_const 1) hgi, integral_const_mul, hg1]
    simp
  -- `∫ g klFun(f/g) = ∫ klFun f + ∫ fΦ + log Z ≤ 0`
  set D : Torus d → ℝ := fun x => g x * klFun (f x / g x) with hD
  have hDe : ∀ x, D x = klFun (f x) - 1 + f x * Φ x + f x * Real.log Z + g x := fun x => by
    simp only [hD, klFun_apply]
    rcases (hf0 x).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hg0 := (hgpos x).ne'
      rw [Real.log_div hpos.ne' hg0, hlogg]
      field_simp
      ring
  have hDi : Integrable D (haar d) := by
    have : D = fun x => klFun (f x) - 1 + f x * Φ x + f x * Real.log Z + g x := funext hDe
    rw [this]
    exact (((hKf.sub (integrable_const 1)).add (hΦi hfi)).add (hfi.mul_const _)).add hgi
  have hDint : ∫ x, D x ∂haar d ≤ 0 := by
    have i1 := hKf.sub (integrable_const (1 : ℝ))
    have i2 := hΦi hfi
    have i3 := hfi.mul_const (Real.log Z)
    rw [integral_congr_ae (Eventually.of_forall hDe),
      integral_add (f := fun x => klFun (f x) - 1 + f x * Φ x + f x * Real.log Z) (g := g)
        ((i1.add i2).add i3) hgi,
      integral_add (f := fun x => klFun (f x) - 1 + f x * Φ x)
        (g := fun x => f x * Real.log Z) (i1.add i2) i3,
      integral_add (f := fun x => klFun (f x) - 1) (g := fun x => f x * Φ x) i1 i2,
      integral_sub (f := fun x => klFun (f x)) (g := fun _ => (1 : ℝ)) hKf (integrable_const 1),
      integral_mul_const, hf1, hg1]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith
  have hD0 : ∀ x, 0 ≤ D x := fun x =>
    mul_nonneg (hgpos x).le (klFun_nonneg (div_nonneg (hf0 x) (hgpos x).le))
  have hDz : D =ᵐ[haar d] 0 :=
    (integral_eq_zero_iff_of_nonneg hD0 hDi).mp (le_antisymm hDint (integral_nonneg hD0))
  have hfg : f =ᵐ[haar d] g := by
    filter_upwards [hDz] with x hx
    simp only [hD, Pi.zero_apply, mul_eq_zero, (hgpos x).ne', false_or] at hx
    have := (klFun_eq_zero_iff (div_nonneg (hf0 x) (hgpos x).le)).mp hx
    exact (div_eq_one_iff_eq (hgpos x).ne').mp this
  rw [hμf]
  exact withDensity_congr_ae (hfg.mono fun x hx => by simp only [hx])

end dens

/-- `|e^a - e^b| ≤ e^M |a - b|` for `a, b ≤ M`. -/
theorem abs_exp_sub_exp_le {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    |exp a - exp b| ≤ exp M * |a - b| := by
  have key : ∀ {u v : ℝ}, u ≤ v → v ≤ M → exp v - exp u ≤ exp M * (v - u) := fun {u v} huv hv => by
    have h1 := Real.add_one_le_exp (-(v - u))
    have h2 : exp v - exp u = exp v * (1 - exp (-(v - u))) := by
      rw [mul_sub, mul_one, ← exp_add]; ring_nf
    rw [h2]
    calc exp v * (1 - exp (-(v - u))) ≤ exp v * (v - u) :=
          mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le
      _ ≤ exp M * (v - u) := mul_le_mul_of_nonneg_right (exp_le_exp.mpr hv) (by linarith)
  rcases le_total a b with h | h
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (exp_le_exp.mpr h)),
      abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]
    exact key h hb
  · rw [abs_of_nonneg (sub_nonneg.mpr (exp_le_exp.mpr h)), abs_of_nonneg (sub_nonneg.mpr h)]
    exact key h ha

section bounds
variable (hyp : Hyp V W KV KW)
include hyp

/-- Uniform bounds and a uniform Lipschitz constant for `e^{-V-W*μ}/Z`, `μ` any probability. -/
theorem elDensity_bounds :
    ∃ (c C : ℝ) (L : NNReal), 0 < c ∧ ∀ μ : Measure (Torus d), IsProbabilityMeasure μ →
      (∀ x, c ≤ elDens V W μ x ∧ elDens V W μ x ≤ C) ∧ LipschitzWith L (elDens V W μ) := by
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  set B := BV + BW
  set K1 : NNReal := Real.toNNReal (KV * Fintype.card (Fin d) / 2)
  set K2 : NNReal := Real.toNNReal (KW * Fintype.card (Fin 2 × Fin d) / 2) * 1
  refine ⟨exp (-(2 * B)), exp (2 * B), Real.toNNReal (exp (2 * B) * (K1 + K2)), exp_pos _,
    fun μ hμ => ?_⟩
  set Φ : Torus d → ℝ := fun x => V x + convMeas W μ x with hΦ
  have hΦb : ∀ x, |Φ x| ≤ B := fun x => abs_potential_le hBV (fun x y => hBW (x, y)) μ x
  set Z := ∫ y, exp (-Φ y) ∂haar d with hZ
  have hΦm : Measurable Φ := hyp.continuous_V.measurable.add
    ((hyp.continuous_W.measurable.stronglyMeasurable.integral_prod_right (ν := μ)
      (f := fun x y => W x y)).measurable)
  have hei : Integrable (fun y => exp (-Φ y)) (haar d) :=
    integrable_of_bdd (measurable_exp.comp hΦm.neg) (C := exp B) fun y => by
      rw [abs_of_pos (exp_pos _)]; exact exp_le_exp.mpr (by linarith [neg_le_abs (Φ y), hΦb y])
  have hZlo : exp (-B) ≤ Z := by
    have : ∫ _y, exp (-B) ∂haar d ≤ Z := integral_mono (integrable_const _) hei fun y =>
      exp_le_exp.mpr (by linarith [le_abs_self (Φ y), hΦb y])
    simpa using this
  have hZhi : Z ≤ exp B := by
    have : Z ≤ ∫ _y, exp B ∂haar d := integral_mono hei (integrable_const _) fun y =>
      exp_le_exp.mpr (by linarith [neg_le_abs (Φ y), hΦb y])
    simpa using this
  have hZpos : 0 < Z := (exp_pos _).trans_le hZlo
  have hg : ∀ x, elDens V W μ x = exp (-Φ x) / Z := fun x => by
    simp only [elDens, hΦ, hZ, neg_add']
  refine ⟨fun x => ⟨?_, ?_⟩, ?_⟩
  · rw [hg, le_div_iff₀ hZpos]
    calc exp (-(2 * B)) * Z ≤ exp (-(2 * B)) * exp B :=
          mul_le_mul_of_nonneg_left hZhi (exp_pos _).le
      _ = exp (-B) := by rw [← exp_add]; ring_nf
      _ ≤ exp (-Φ x) := exp_le_exp.mpr (by linarith [le_abs_self (Φ x), hΦb x])
  · rw [hg, div_le_iff₀ hZpos]
    calc exp (-Φ x) ≤ exp B := exp_le_exp.mpr (by linarith [neg_le_abs (Φ x), hΦb x])
      _ = exp (2 * B) * exp (-B) := by rw [← exp_add]; ring_nf
      _ ≤ exp (2 * B) * Z := mul_le_mul_of_nonneg_left hZlo (exp_pos _).le
  · -- Lipschitz on lifts, then on the torus
    have hΦL : LipschitzWith (K1 + K2) (Φ ∘ liftT) := by
      have hV := lipschitz_V hyp (V := V) (W := W)
      have hw : LipschitzWith K2 ((convMeas W μ) ∘ liftT) := by
        refine LipschitzWith.of_dist_le_mul fun a b => ?_
        simp only [Function.comp, Real.dist_eq, convMeas]
        have hi : ∀ z, Integrable (fun y => W (liftT z) y) μ := fun z =>
          integrable_of_bdd (hyp.continuous_W.measurable.comp measurable_prodMk_left)
            (fun y => hBW (liftT z, y))
        rw [← integral_sub (hi a) (hi b)]
        refine (abs_integral_le_of_bdd fun y => ?_)
        have := (lipschitz_slice hyp y).dist_le_mul a b
        simp only [Function.comp, Real.dist_eq] at this
        exact this
      exact hV.add hw
    refine lipschitzWith_of_liftT (LipschitzWith.of_dist_le_mul fun a b => ?_)
    simp only [Function.comp, Real.dist_eq, hg]
    rw [← sub_div, abs_div, abs_of_pos hZpos, div_le_iff₀ hZpos]
    have h1 := abs_exp_sub_exp_le (a := -Φ (liftT a)) (b := -Φ (liftT b)) (M := B)
      (by linarith [neg_le_abs (Φ (liftT a)), hΦb (liftT a)])
      (by linarith [neg_le_abs (Φ (liftT b)), hΦb (liftT b)])
    have h2 := hΦL.dist_le_mul a b
    simp only [Function.comp, Real.dist_eq] at h2
    rw [show -Φ (liftT a) - -Φ (liftT b) = -(Φ (liftT a) - Φ (liftT b)) by ring, abs_neg] at h1
    have hK : (0 : ℝ) ≤ ((K1 + K2 : NNReal) : ℝ) := NNReal.coe_nonneg _
    rw [Real.coe_toNNReal _ (by positivity)]
    calc |exp (-Φ (liftT a)) - exp (-Φ (liftT b))| ≤ exp B * (((K1 + K2 : NNReal) : ℝ) * dist a b) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (exp_pos _).le)
      _ = exp (2 * B) * exp (-B) * (((K1 + K2 : NNReal) : ℝ) * dist a b) := by
          rw [← exp_add]; ring_nf
      _ ≤ exp (2 * B) * ((K1 + K2 : NNReal) : ℝ) * dist a b * Z := by
          have hd := dist_nonneg (x := a) (y := b)
          have := mul_le_mul_of_nonneg_left hZlo (by positivity :
            (0 : ℝ) ≤ exp (2 * B) * ((K1 + K2 : NNReal) : ℝ) * dist a b)
          nlinarith [exp_pos (2 * B), exp_pos (-B)]

end bounds

end SharpLSI
