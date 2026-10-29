import SharpSymmetricLSI.Paper.FourierSynth
import SharpSymmetricLSI.Paper.CosineLabeled

/-!
# Step 2 of Proposition 3.5: the minimizer of the full-labeled gap (Phase 3, lane C; R39)

On the flat torus `𝕋^{N×1}` with the Gibbs density `w = gsW`, write
`E_w(u) = ∫ w |∇u|²` and `V_w(u) = ∫ w u² - (∫ w u)²`. Then `λ := λ^all_{N,κ}` satisfies
`λ V_w ≤ E_w` on `H¹`, and normalized near-minimizers exist. Rellich compactness
(`rellich_torus`) and weak lower semicontinuity give a minimizer.
-/

open MeasureTheory InformationTheory Set Filter Topology Complex
open scoped ENNReal Real ContDiff ComplexConjugate
open UnitAddTorus

namespace SharpLSI

theorem tendsto_integral_mul_of_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {d : ℕ → α → ℝ} {h : α → ℝ} (hd : ∀ n, MemLp (d n) 2 μ) (hh : MemLp h 2 μ)
    (hlim : Tendsto (fun n => ∫ x, d n x ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, h x * d n x ∂μ) atTop (𝓝 0) := by
  have hh2 : 0 ≤ ∫ x, h x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / (∫ x, h x ^ 2 ∂μ + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.1 hlim) (ε * δ) (by positivity)
  refine ⟨N0, fun n hn => ?_⟩
  have h1 := hN0 n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun x => sq_nonneg _)] at h1
  rw [Real.dist_eq, sub_zero]
  have hint : Integrable (fun x => h x * d n x) μ := by
    refine Integrable.mono' ((hh.integrable_sq.add (hd n).integrable_sq).div_const 1)
      (hh.aestronglyMeasurable.mul (hd n).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    show ‖h x * d n x‖ ≤ (h x ^ 2 + d n x ^ 2) / 1
    rw [Real.norm_eq_abs, div_one, abs_mul, ← sq_abs (h x), ← sq_abs (d n x)]
    nlinarith [sq_nonneg (|h x| - |d n x|), abs_nonneg (h x), abs_nonneg (d n x),
      mul_nonneg (abs_nonneg (h x)) (abs_nonneg (d n x))]
  have hb : ∀ x, |h x * d n x| ≤ (δ * h x ^ 2 + d n x ^ 2 / δ) / 2 := fun x => by
    have e : (δ * |h x| - |d n x|) ^ 2 / (2 * δ) =
        δ * |h x| ^ 2 / 2 - |h x| * |d n x| + |d n x| ^ 2 / (2 * δ) := by
      field_simp; ring
    have h0 : 0 ≤ (δ * |h x| - |d n x|) ^ 2 / (2 * δ) := by positivity
    rw [sq_abs, sq_abs] at e
    rw [abs_mul]
    have e2 : (δ * h x ^ 2 + d n x ^ 2 / δ) / 2 = δ * h x ^ 2 / 2 + d n x ^ 2 / (2 * δ) := by
      field_simp
    linarith
  calc |∫ x, h x * d n x ∂μ| ≤ ∫ x, |h x * d n x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (δ * h x ^ 2 + d n x ^ 2 / δ) / 2 ∂μ :=
        integral_mono hint.abs (((hh.integrable_sq.const_mul δ).add
          ((hd n).integrable_sq.div_const δ)).div_const 2) hb
    _ = (δ * ∫ x, h x ^ 2 ∂μ + (∫ x, d n x ^ 2 ∂μ) / δ) / 2 := by
        rw [integral_div, integral_add (hh.integrable_sq.const_mul δ)
          ((hd n).integrable_sq.div_const δ), integral_const_mul, integral_div]
    _ < ε := by
        have e1 : δ * ∫ x, h x ^ 2 ∂μ < ε := by
          rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
        have e2 : (∫ x, d n x ^ 2 ∂μ) / δ < ε := by rw [div_lt_iff₀ hδ0]; linarith
        linarith

theorem eq_zero_of_quadratic_nonneg {a b : ℝ} (h : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * b) : a = 0 := by
  by_contra ha
  have hb1 : 0 < |b| + 1 := by positivity
  have hc := h (-a / (|b| + 1))
  have ha2 : 0 < a ^ 2 := by positivity
  have e : 2 * (-a / (|b| + 1)) * a + (-a / (|b| + 1)) ^ 2 * b =
      a ^ 2 * (b - 2 * (|b| + 1)) / (|b| + 1) ^ 2 := by field_simp; ring
  rw [e] at hc
  have : a ^ 2 * (b - 2 * (|b| + 1)) < 0 := by
    have := le_abs_self b
    nlinarith
  have : a ^ 2 * (b - 2 * (|b| + 1)) / (|b| + 1) ^ 2 < 0 := div_neg_of_neg_of_pos this (by positivity)
  linarith

section Cosine

variable {N : ℕ}

/-- `E_w(u) = ∫ w |∇u|²`. -/
noncomputable def Ew (κ : ℝ) (N : ℕ) (u : UnitAddTorus (Fin N × Fin 1) → ℝ) : ℝ :=
  ∫ y, gsW κ N y * sqNorm (weakGrad u y)

/-- `V_w(u) = ∫ w u² - (∫ w u)²`. -/
noncomputable def Vw (κ : ℝ) (N : ℕ) (u : UnitAddTorus (Fin N × Fin 1) → ℝ) : ℝ :=
  (∫ y, gsW κ N y * u y ^ 2) - (∫ y, gsW κ N y * u y) ^ 2

theorem memH1_gsMeas_of_volume {κ : ℝ} (hκ : 0 ≤ κ) {u : UnitAddTorus (Fin N × Fin 1) → ℝ}
    (hu : MemH1 volume u) : MemH1 (gsMeas κ N) u :=
  ⟨hu.1, hu.2.1.of_measure_le_smul ENNReal.ofReal_ne_top (gsMeas_le_smul_volume hκ),
    hu.2.2.of_measure_le_smul ENNReal.ofReal_ne_top (gsMeas_le_smul_volume hκ)⟩

theorem integrable_sqNorm_of_memH1 {P : Measure (UnitAddTorus (Fin N × Fin 1))}
    {u : UnitAddTorus (Fin N × Fin 1) → ℝ} (hu : MemH1 P u) :
    Integrable (fun y => sqNorm (weakGrad u y)) P := by
  refine hu.2.2.integrable_sq.congr (Eventually.of_forall fun y => ?_)
  exact Real.sq_sqrt (show 0 ≤ sqNorm (weakGrad u y) from Finset.sum_nonneg fun k _ => sq_nonneg _)

theorem memH1C_of_flat {κ : ℝ} (hκ : 0 ≤ κ) {u : UnitAddTorus (Fin N × Fin 1) → ℝ}
    (hu : MemH1 volume u) : MemH1C (gibbs cosV (cosW κ) N) (fun X => u (flat X)) := by
  show MemH1 ((gibbs cosV (cosW κ) N).map flat) _
  rw [gibbs_map_flat_eq]
  exact memH1_gsMeas_of_volume hκ hu

theorem energy_flat {κ : ℝ} (hκ : 0 ≤ κ) {u : UnitAddTorus (Fin N × Fin 1) → ℝ}
    (hu : MemH1 volume u) :
    energy cosV (cosW κ) N (fun X => u (flat X)) = ENNReal.ofReal (Ew κ N u) := by
  rw [energy_eq_dirichlet (cosine_hyp_all κ)
    (show HasWeakGrad ((fun X => u (flat X)) ∘ unflat) from hu.1)]
  show dirichlet ((gibbs cosV (cosW κ) N).map flat) u = _
  rw [gibbs_map_flat_eq]
  have hW := memH1_gsMeas_of_volume hκ hu
  unfold dirichlet Ew
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sqNorm_of_memH1 hW)
    (Eventually.of_forall fun y => Finset.sum_nonneg fun k _ => sq_nonneg _), integral_gsMeas]

theorem var_flat {κ : ℝ} (hκ : 0 ≤ κ) {u : UnitAddTorus (Fin N × Fin 1) → ℝ}
    (hu : MemLp u 2 volume) :
    var (gibbs cosV (cosW κ) N) (fun X => u (flat X)) = ENNReal.ofReal (Vw κ N u) := by
  have hW : MemLp u 2 (gsMeas κ N) :=
    hu.of_measure_le_smul ENNReal.ofReal_ne_top (gsMeas_le_smul_volume hκ)
  rw [var_map_eq _ measurable_flat (by rw [gibbs_map_flat_eq]; exact hW.aestronglyMeasurable),
    gibbs_map_flat_eq, var, ← ProbabilityTheory.ofReal_variance hW,
    ProbabilityTheory.variance_eq_sub hW]
  unfold Vw
  simp only [Pi.pow_apply]
  rw [integral_gsMeas, integral_gsMeas]

theorem integral_flat {κ : ℝ} (F : UnitAddTorus (Fin N × Fin 1) → ℝ)
    (hF : AEStronglyMeasurable F volume) :
    ∫ X, F (flat X) ∂gibbs cosV (cosW κ) N = ∫ y, gsW κ N y * F y := by
  rw [← integral_gsMeas]
  unfold gsMeas
  rw [← gibbs_map_flat_eq, integral_map measurable_flat.aemeasurable (by
      rw [gibbs_map_flat_eq]
      exact hF.mono_ac (withDensity_absolutelyContinuous _ _))]

theorem ent_const {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P] (c : ℝ) :
    ent P (fun _ => c) = 0 := by
  unfold ent
  rw [if_pos (integrable_const c)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rcases eq_or_ne c 0 with h | h
  · simp [h]
  · simp [div_self h, klFun_one]

theorem lamAll_lt_top {κ : ℝ} (hN : 1 ≤ N) : lamAll cosV (cosW κ) N < ⊤ := by
  haveI := gibbs_isProbabilityMeasure (cosine_hyp_all κ) N
  set ε : ℝ := 1 / 100
  obtain ⟨hmem, hent, -⟩ := cosine_tagged_aux κ hN (memH1_hEps ε)
  beta_reduce at hmem hent
  have hE : 0 < entHEps ε := by
    have hb := (abs_le.mp (entHEps_approx (ε := ε) (by norm_num [ε, abs_of_pos]))).1
    norm_num [ε, abs_of_pos] at hb ⊢
    linarith
  have hpos : 0 < ent (gibbs cosV (cosW κ) N) (fun X => (1 + ε * gCos (X ⟨0, hN⟩)) ^ 2) := by
    rw [hent, ent_hEps]; exact ENNReal.ofReal_pos.mpr hE
  set f : Config N 1 → ℝ := fun X => 1 + ε * gCos (X ⟨0, hN⟩)
  have hvar : 0 < var (gibbs cosV (cosW κ) N) f := by
    refine lt_of_le_of_ne zero_le fun h0 => ?_
    have hae := (ProbabilityTheory.evariance_eq_zero_iff
      (memLp_of_memH1C (cosine_hyp_all κ) hmem).aestronglyMeasurable.aemeasurable).1 h0.symm
    have h2 : (fun X => f X ^ 2) =ᵐ[gibbs cosV (cosW κ) N]
        fun _ => (∫ X, f X ∂gibbs cosV (cosW κ) N) ^ 2 := hae.mono fun X hX => by
      simp only at hX ⊢; rw [hX]
    rw [ent_congr_ae h2, ent_const] at hpos
    exact lt_irrefl _ hpos
  have hEt := energy_lt_top (cosine_hyp_all κ) hmem
  calc lamAll cosV (cosW κ) N ≤ energy cosV (cosW κ) N f / var (gibbs cosV (cosW κ) N) f :=
        iInf₂_le f ⟨hmem, hvar⟩
    _ < ⊤ := ENNReal.div_lt_top hEt.ne hvar.ne'

theorem Vw_nonneg {κ : ℝ} (hκ : 0 ≤ κ) {u : UnitAddTorus (Fin N × Fin 1) → ℝ}
    (hu : MemLp u 2 volume) : 0 ≤ Vw κ N u := by
  have hW : MemLp u 2 (gsMeas κ N) :=
    hu.of_measure_le_smul ENNReal.ofReal_ne_top (gsMeas_le_smul_volume hκ)
  have := ProbabilityTheory.variance_nonneg u (gsMeas κ N)
  rw [ProbabilityTheory.variance_eq_sub hW] at this
  simp only [Pi.pow_apply] at this
  rw [integral_gsMeas, integral_gsMeas] at this
  exact this

theorem Ew_nonneg (κ : ℝ) (u : UnitAddTorus (Fin N × Fin 1) → ℝ) : 0 ≤ Ew κ N u :=
  integral_nonneg fun y => mul_nonneg (gsW_pos κ y).le
    (show 0 ≤ sqNorm (weakGrad u y) from Finset.sum_nonneg fun k _ => sq_nonneg _)

/-- (P1): `λ V_w(u) ≤ E_w(u)` on `H¹`. -/
theorem lam_mul_Vw_le {κ : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N) {u : UnitAddTorus (Fin N × Fin 1) → ℝ}
    (hu : MemH1 volume u) :
    (lamAll cosV (cosW κ) N).toReal * Vw κ N u ≤ Ew κ N u := by
  rcases (Vw_nonneg hκ.le hu.2.1).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact Ew_nonneg κ u
  have hm := memH1C_of_flat hκ.le hu
  have hvar : 0 < var (gibbs cosV (cosW κ) N) (fun X => u (flat X)) := by
    rw [var_flat hκ.le hu.2.1]; exact ENNReal.ofReal_pos.mpr hpos
  have hle : lamAll cosV (cosW κ) N ≤
      energy cosV (cosW κ) N (fun X => u (flat X)) / var (gibbs cosV (cosW κ) N) (fun X => u (flat X)) :=
    iInf₂_le _ ⟨hm, hvar⟩
  rw [energy_flat hκ.le hu, var_flat hκ.le hu.2.1, ← ENNReal.ofReal_div_of_pos hpos] at hle
  have := ENNReal.toReal_le_of_le_ofReal (div_nonneg (Ew_nonneg κ u) hpos.le) hle
  rwa [le_div_iff₀ hpos] at this

/-- Affine images preserve `H¹(m)`, with `∇(s(u - c)) = s ∇u`. -/
theorem memH1_affine {u : UnitAddTorus (Fin N × Fin 1) → ℝ} (hu : MemH1 volume u) (s c : ℝ) :
    MemH1 volume (fun y => s * (u y - c)) ∧
      weakGrad (fun y => s * (u y - c)) =ᵐ[volume] fun y k => s * weakGrad u y k := by
  have hw := isWeakGrad_weakGrad hu.1
  have hw' : IsWeakGrad (fun y => s * (u y - c)) (fun y k => s * weakGrad u y k) :=
    (hw.sub_const c).cmul s
  have hae := weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hw'⟩) hw'
  refine ⟨⟨⟨_, hw'⟩, (hu.2.1.sub (memLp_const c)).const_mul s, ?_⟩, hae⟩
  have h2 : MemLp (fun y => |s| * Real.sqrt (sqNorm (weakGrad u y))) 2 volume := hu.2.2.const_mul _
  refine h2.ae_eq (hae.mono fun y hy => ?_)
  simp only
  rw [hy]
  unfold sqNorm
  simp_rw [mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs]

/-- (P2): normalized near-minimizers. -/
theorem exists_near_min {κ : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : UnitAddTorus (Fin N × Fin 1) → ℝ, MemH1 volume u ∧ ∫ y, gsW κ N y * u y = 0 ∧
      ∫ y, gsW κ N y * u y ^ 2 = 1 ∧ Ew κ N u ≤ (lamAll cosV (cosW κ) N).toReal + ε := by
  set L := lamAll cosV (cosW κ) N with hL
  have hLt := lamAll_lt_top (κ := κ) hN
  have hLL : L = ENNReal.ofReal L.toReal := (ENNReal.ofReal_toReal hLt.ne).symm
  have hlt : L < ENNReal.ofReal (L.toReal + ε) := by
    rw [hLL, ENNReal.ofReal_lt_ofReal_iff (by positivity), ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    linarith
  rw [hL] at hlt
  unfold lamAll at hlt
  obtain ⟨g, hlt⟩ := iInf_lt_iff.mp hlt
  obtain ⟨⟨hg, hvar⟩, hq⟩ := iInf_lt_iff.mp hlt
  set u0 := g ∘ unflat with hu0def
  have hu0W : MemH1 (gsMeas κ N) u0 := by
    have : MemH1 ((gibbs cosV (cosW κ) N).map flat) u0 := hg
    rwa [gibbs_map_flat_eq] at this
  have hu0 := memH1_volume_of_gsMeas hκ.le hu0W
  have hgf : g = fun X => u0 (flat X) := rfl
  rw [hgf, energy_flat hκ.le hu0, var_flat hκ.le hu0.2.1] at hq
  rw [hgf, var_flat hκ.le hu0.2.1] at hvar
  set V := Vw κ N u0 with hV
  have hVpos : 0 < V := ENNReal.ofReal_pos.mp hvar
  rw [← ENNReal.ofReal_div_of_pos hVpos, ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hq
  set c := ∫ y, gsW κ N y * u0 y with hc
  set sc := 1 / Real.sqrt V with hsc
  obtain ⟨hu, hgae⟩ := memH1_affine hu0 sc c
  have hsc2 : sc ^ 2 = 1 / V := by rw [hsc, div_pow, Real.sq_sqrt hVpos.le, one_pow]
  have hw0 : Integrable (gsW κ N) volume := integrable_gsW κ
  have hgb : ∀ y, ‖gsW κ N y‖ ≤ gsC κ N := fun y => by
    rw [Real.norm_eq_abs, abs_of_pos (gsW_pos κ y)]
    obtain ⟨m, hm, hb⟩ := gsW_bounds (N := N) hκ.le
    exact (hb y).2
  have hwm : AEStronglyMeasurable (gsW κ N) volume := (measurable_gsW κ).aestronglyMeasurable
  have hu0i : Integrable u0 volume := hu0.2.1.integrable one_le_two
  have hwu0 : Integrable (fun y => gsW κ N y * u0 y) volume := hu0i.bdd_mul hwm (Eventually.of_forall hgb)
  have hwu02 : Integrable (fun y => gsW κ N y * u0 y ^ 2) volume :=
    hu0.2.1.integrable_sq.bdd_mul hwm (Eventually.of_forall hgb)
  refine ⟨fun y => sc * (u0 y - c), hu, ?_, ?_, ?_⟩
  · have e : ∀ y, gsW κ N y * (sc * (u0 y - c)) = sc * (gsW κ N y * u0 y - c * gsW κ N y) :=
      fun y => by ring
    simp_rw [e]
    rw [integral_const_mul, integral_sub hwu0 (hw0.const_mul c), integral_const_mul, integral_gsW,
      ← hc]
    ring
  · have e : ∀ y, gsW κ N y * (sc * (u0 y - c)) ^ 2 =
        sc ^ 2 * (gsW κ N y * u0 y ^ 2 - 2 * c * (gsW κ N y * u0 y) + c ^ 2 * gsW κ N y) :=
      fun y => by ring
    simp_rw [e]
    have ia : Integrable (fun y => gsW κ N y * u0 y ^ 2 - 2 * c * (gsW κ N y * u0 y)) volume :=
      hwu02.sub (hwu0.const_mul _)
    rw [integral_const_mul, integral_add (f := fun y => gsW κ N y * u0 y ^ 2 -
        2 * c * (gsW κ N y * u0 y)) (g := fun y => c ^ 2 * gsW κ N y) ia (hw0.const_mul _),
      integral_sub (f := fun y => gsW κ N y * u0 y ^ 2) (g := fun y => 2 * c * (gsW κ N y * u0 y))
        hwu02 (hwu0.const_mul _), integral_const_mul, integral_const_mul, integral_gsW,
      ← hc, hsc2]
    have : V = (∫ y, gsW κ N y * u0 y ^ 2) - c ^ 2 := rfl
    field_simp
    linarith
  · have hE : Ew κ N (fun y => sc * (u0 y - c)) = sc ^ 2 * Ew κ N u0 := by
      unfold Ew
      rw [← integral_const_mul]
      refine integral_congr_ae (hgae.mono fun y hy => ?_)
      simp only
      rw [hy]
      unfold sqNorm
      simp_rw [mul_pow, ← Finset.mul_sum]
      ring
    rw [hE, hsc2]
    have : 1 / V * Ew κ N u0 = Ew κ N u0 / V := by ring
    rw [this]
    exact hq.le

theorem memH1_of_weakGrad_pair {f : UnitAddTorus (Fin N × Fin 1) → ℝ}
    {G : UnitAddTorus (Fin N × Fin 1) → Fin N × Fin 1 → ℝ} (hfG : IsWeakGrad f G)
    (hf : MemLp f 2 volume) (hG : ∀ j, MemLp (fun y => G y j) 2 volume) :
    MemH1 volume f ∧ weakGrad f =ᵐ[volume] G := by
  have hae := weakGrad_ae_unique (isWeakGrad_weakGrad ⟨G, hfG⟩) hfG
  refine ⟨⟨⟨G, hfG⟩, hf, ?_⟩, hae⟩
  have hm : AEStronglyMeasurable (fun y => Real.sqrt (sqNorm (weakGrad f y))) volume :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (isWeakGrad_weakGrad ⟨G, hfG⟩).aestronglyMeasurable_sqNorm
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  have hs : Integrable (fun y => sqNorm (G y)) volume :=
    integrable_finset_sum Finset.univ fun j _ => (hG j).integrable_sq
  refine hs.congr (hae.mono fun y hy => ?_)
  show sqNorm (G y) = Real.sqrt (sqNorm (weakGrad f y)) ^ 2
  rw [Real.sq_sqrt (show 0 ≤ sqNorm (weakGrad f y) from Finset.sum_nonneg fun k _ => sq_nonneg _), hy]

/-- The minimizer on the flat torus. -/
theorem exists_minimizer_flat {κ : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N) :
    ∃ (f : UnitAddTorus (Fin N × Fin 1) → ℝ) (G : UnitAddTorus (Fin N × Fin 1) → Fin N × Fin 1 → ℝ),
      MemLp f 2 volume ∧ (∀ j, MemLp (fun y => G y j) 2 volume) ∧ IsWeakGrad f G ∧
      ∫ y, gsW κ N y * f y = 0 ∧ ∫ y, gsW κ N y * f y ^ 2 = 1 ∧
      ∫ y, gsW κ N y * sqNorm (G y) = (lamAll cosV (cosW κ) N).toReal := by
  set L := (lamAll cosV (cosW κ) N).toReal with hL
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  choose u hu hmean hnorm hE using fun n : ℕ =>
    exists_near_min hκ hN (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨m, hm, hb⟩ := gsW_bounds (N := N) hκ.le
  have hwm : AEStronglyMeasurable (gsW κ N) volume := (measurable_gsW κ).aestronglyMeasurable
  have hgb : ∀ y, ‖gsW κ N y‖ ≤ gsC κ N := fun y => by
    rw [Real.norm_eq_abs, abs_of_pos (gsW_pos κ y)]; exact (hb y).2
  have hw := fun n => isWeakGrad_weakGrad (hu n).1
  have hg2 := fun n => memLp_weakGrad_comp (hu n)
  -- the `H¹(m)` bound
  have hB : ∀ n, (∫ y, u n y ^ 2) + ∑ j, ∫ y, weakGrad (u n) y j ^ 2 ≤ 1 / m + (L + 1) / m := by
    intro n
    have h1 : ∫ y, u n y ^ 2 ≤ 1 / m := by
      have h1' : m * ∫ y, u n y ^ 2 ≤ ∫ y, gsW κ N y * u n y ^ 2 := by
        rw [← integral_const_mul]
        refine integral_mono ((hu n).2.1.integrable_sq.const_mul _)
          ((hu n).2.1.integrable_sq.bdd_mul hwm (Eventually.of_forall hgb)) fun y => ?_
        exact mul_le_mul_of_nonneg_right (hb y).1 (sq_nonneg _)
      rw [hnorm n] at h1'
      rw [le_div_iff₀ hm]; linarith
    have h2 : ∑ j, ∫ y, weakGrad (u n) y j ^ 2 ≤ (L + 1) / m := by
      rw [← integral_finset_sum _ fun j _ => (hg2 n j).integrable_sq, le_div_iff₀ hm]
      have hEn : Ew κ N (u n) ≤ L + 1 := by
        have := hE n
        have : 1 / ((n : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
        linarith
      refine le_trans ?_ hEn
      unfold Ew
      rw [← integral_mul_const]
      refine integral_mono ((integrable_finset_sum _ fun j _ => (hg2 n j).integrable_sq).mul_const _)
        ((integrable_sqNorm_of_memH1 (hu n)).bdd_mul hwm (Eventually.of_forall hgb)) fun y => ?_
      have hs : 0 ≤ sqNorm (weakGrad (u n) y) := Finset.sum_nonneg fun k _ => sq_nonneg _
      show (∑ j, weakGrad (u n) y j ^ 2) * m ≤ gsW κ N y * sqNorm (weakGrad (u n) y)
      have : (∑ j, weakGrad (u n) y j ^ 2) = sqNorm (weakGrad (u n) y) := rfl
      rw [this]; nlinarith [(hb y).1]
    linarith
  obtain ⟨φ, hφ, f, G, hf2, hG2, hfG, hstrong, hweak⟩ :=
    rellich_torus hw (fun n => (hu n).2.1) hg2 hB
  have hwL2 : MemLp (gsW κ N) 2 volume :=
    MemLp.of_bound hwm (gsC κ N) (Eventually.of_forall hgb)
  have hd : ∀ n, MemLp (fun y => u (φ n) y - f y) 2 volume := fun n => (hu (φ n)).2.1.sub hf2
  -- the mean
  have hmean0 : ∫ y, gsW κ N y * f y = 0 := by
    have h1 := tendsto_integral_mul_of_sq hd hwL2 hstrong
    have h2 : ∀ n, ∫ y, gsW κ N y * (u (φ n) y - f y) = -∫ y, gsW κ N y * f y := fun n => by
      have hi1 : Integrable (fun y => gsW κ N y * u (φ n) y) volume :=
        ((hu (φ n)).2.1.integrable one_le_two).bdd_mul hwm (Eventually.of_forall hgb)
      have hi2 : Integrable (fun y => gsW κ N y * f y) volume :=
        (hf2.integrable one_le_two).bdd_mul hwm (Eventually.of_forall hgb)
      simp_rw [mul_sub]
      rw [integral_sub hi1 hi2, hmean]; ring
    simp_rw [h2] at h1
    have := tendsto_nhds_unique tendsto_const_nhds h1
    linarith
  -- the mass
  have hnorm1 : ∫ y, gsW κ N y * f y ^ 2 = 1 := by
    have hwf : MemLp (fun y => gsW κ N y * f y) 2 volume := by
      refine (hf2.const_mul (gsC κ N)).of_le (hwm.mul hf2.aestronglyMeasurable)
        (Eventually.of_forall fun y => ?_)
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (gsC_pos κ N).le]
      exact mul_le_mul_of_nonneg_right (hgb y) (norm_nonneg _)
    have h1 := tendsto_integral_mul_of_sq hd hwf hstrong
    have h0 : Tendsto (fun n => ∫ y, gsW κ N y * (u (φ n) y - f y) ^ 2) atTop (𝓝 0) := by
      have hup : Tendsto (fun n => gsC κ N * ∫ y, (u (φ n) y - f y) ^ 2) atTop (𝓝 0) := by
        simpa using hstrong.const_mul (gsC κ N)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun n => integral_nonneg fun y => mul_nonneg (gsW_pos κ y).le (sq_nonneg _)) fun n => ?_
      rw [← integral_const_mul]
      exact integral_mono (((hd n).integrable_sq).bdd_mul hwm (Eventually.of_forall hgb))
        ((hd n).integrable_sq.const_mul _) fun y =>
          mul_le_mul_of_nonneg_right (hb y).2 (sq_nonneg _)
    have hexp : ∀ n, ∫ y, gsW κ N y * u (φ n) y ^ 2 =
        (∫ y, gsW κ N y * (u (φ n) y - f y) ^ 2) +
          2 * (∫ y, gsW κ N y * f y * (u (φ n) y - f y)) +
          ∫ y, gsW κ N y * f y ^ 2 := fun n => by
      have i1 : Integrable (fun y => gsW κ N y * (u (φ n) y - f y) ^ 2) volume :=
        ((hd n).integrable_sq).bdd_mul hwm (Eventually.of_forall hgb)
      have i2 : Integrable (fun y => gsW κ N y * f y * (u (φ n) y - f y)) volume := by
        have := (hwf.integrable_mul (hd n))
        exact this
      have i3 : Integrable (fun y => gsW κ N y * f y ^ 2) volume :=
        hf2.integrable_sq.bdd_mul hwm (Eventually.of_forall hgb)
      have e : (fun y => gsW κ N y * u (φ n) y ^ 2) = fun y =>
          gsW κ N y * (u (φ n) y - f y) ^ 2 + 2 * (gsW κ N y * f y * (u (φ n) y - f y)) +
            gsW κ N y * f y ^ 2 := by funext y; ring
      rw [e, integral_add (f := fun y => gsW κ N y * (u (φ n) y - f y) ^ 2 +
          2 * (gsW κ N y * f y * (u (φ n) y - f y))) (g := fun y => gsW κ N y * f y ^ 2)
          (i1.add (i2.const_mul 2)) i3,
        integral_add (f := fun y => gsW κ N y * (u (φ n) y - f y) ^ 2)
          (g := fun y => 2 * (gsW κ N y * f y * (u (φ n) y - f y))) i1 (i2.const_mul 2),
        integral_const_mul]
    have hlim : Tendsto (fun n => ∫ y, gsW κ N y * u (φ n) y ^ 2) atTop
        (𝓝 (0 + 2 * 0 + ∫ y, gsW κ N y * f y ^ 2)) := by
      simp_rw [hexp]
      exact (h0.add (h1.const_mul 2)).add tendsto_const_nhds
    simp_rw [hnorm] at hlim
    have := tendsto_nhds_unique tendsto_const_nhds hlim
    linarith
  -- lower semicontinuity of the energy
  have hle : ∫ y, gsW κ N y * sqNorm (G y) ≤ L := by
    have hwG : ∀ j, MemLp (fun y => gsW κ N y * G y j) 2 volume := fun j => by
      refine ((hG2 j).const_mul (gsC κ N)).of_le (hwm.mul (hG2 j).aestronglyMeasurable)
        (Eventually.of_forall fun y => ?_)
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (gsC_pos κ N).le]
      exact mul_le_mul_of_nonneg_right (hgb y) (norm_nonneg _)
    have hR : Tendsto (fun n => ∑ j, (2 * (∫ y, weakGrad (u (φ n)) y j * (gsW κ N y * G y j)) -
        ∫ y, gsW κ N y * G y j ^ 2)) atTop
        (𝓝 (∑ j, (2 * (∫ y, G y j * (gsW κ N y * G y j)) - ∫ y, gsW κ N y * G y j ^ 2))) :=
      tendsto_finset_sum _ fun j _ => ((hweak j _ (hwG j)).const_mul 2).sub_const
        (∫ y, gsW κ N y * G y j ^ 2)
    have hval : ∑ j, (2 * (∫ y, G y j * (gsW κ N y * G y j)) - ∫ y, gsW κ N y * G y j ^ 2) =
        ∫ y, gsW κ N y * sqNorm (G y) := by
      have e : ∀ j, 2 * (∫ y, G y j * (gsW κ N y * G y j)) - ∫ y, gsW κ N y * G y j ^ 2 =
          ∫ y, gsW κ N y * G y j ^ 2 := fun j => by
        have : ∫ y, G y j * (gsW κ N y * G y j) = ∫ y, gsW κ N y * G y j ^ 2 := by
          congr 1; funext y; ring
        rw [this]; ring
      simp_rw [e]
      rw [← integral_finset_sum _ fun j _ => (hG2 j).integrable_sq.bdd_mul hwm
        (Eventually.of_forall hgb)]
      congr 1; funext y; unfold sqNorm; rw [Finset.mul_sum]
    rw [hval] at hR
    have hU : Tendsto (fun n => L + 1 / ((φ n : ℝ) + 1)) atTop (𝓝 L) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).const_add L
      simpa [Function.comp_def] using this
    refine le_of_tendsto_of_tendsto' hR hU fun n => ?_
    refine le_trans ?_ (hE (φ n))
    unfold Ew
    have hpt : ∀ y, ∑ j, (2 * (weakGrad (u (φ n)) y j * (gsW κ N y * G y j)) - gsW κ N y * G y j ^ 2)
        ≤ gsW κ N y * sqNorm (weakGrad (u (φ n)) y) := fun y => by
      unfold sqNorm; rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      nlinarith [gsW_pos κ y, sq_nonneg (weakGrad (u (φ n)) y j - G y j),
        mul_nonneg (gsW_pos κ y).le (sq_nonneg (weakGrad (u (φ n)) y j - G y j))]
    have hi : ∀ j, Integrable (fun y => weakGrad (u (φ n)) y j * (gsW κ N y * G y j)) volume :=
      fun j => (hg2 (φ n) j).integrable_mul (hwG j)
    have hi2 : ∀ j, Integrable (fun y => gsW κ N y * G y j ^ 2) volume := fun j =>
      (hG2 j).integrable_sq.bdd_mul hwm (Eventually.of_forall hgb)
    calc ∑ j, (2 * (∫ y, weakGrad (u (φ n)) y j * (gsW κ N y * G y j)) - ∫ y, gsW κ N y * G y j ^ 2)
        = ∫ y, ∑ j, (2 * (weakGrad (u (φ n)) y j * (gsW κ N y * G y j)) - gsW κ N y * G y j ^ 2) := by
          rw [integral_finset_sum (f := fun j y => 2 * (weakGrad (u (φ n)) y j * (gsW κ N y * G y j)) -
            gsW κ N y * G y j ^ 2) _ fun j _ => ((hi j).const_mul 2).sub (hi2 j)]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [integral_sub (f := fun y => 2 * (weakGrad (u (φ n)) y j * (gsW κ N y * G y j)))
            (g := fun y => gsW κ N y * G y j ^ 2) ((hi j).const_mul 2) (hi2 j), integral_const_mul]
      _ ≤ ∫ y, gsW κ N y * sqNorm (weakGrad (u (φ n)) y) :=
          integral_mono (integrable_finset_sum _ fun j _ => ((hi j).const_mul 2).sub (hi2 j))
            ((integrable_sqNorm_of_memH1 (hu (φ n))).bdd_mul hwm (Eventually.of_forall hgb)) hpt
  -- the reverse inequality
  obtain ⟨hfH1, hfae⟩ := memH1_of_weakGrad_pair hfG hf2 hG2
  have hge := lam_mul_Vw_le hκ hN hfH1
  have hVf : Vw κ N f = 1 := by unfold Vw; rw [hnorm1, hmean0]; ring
  have hEf : Ew κ N f = ∫ y, gsW κ N y * sqNorm (G y) :=
    integral_congr_ae (hfae.mono fun y hy => by simp only [hy])
  rw [hVf, mul_one, hEf] at hge
  exact ⟨f, G, hf2, hG2, hfG, hmean0, hnorm1, le_antisymm hle hge⟩

/-- The Euler–Lagrange equation of the minimizer: `∫ w ∇f·∇ψ = λ ∫ w f ψ` on `H¹`. -/
theorem euler_lagrange_flat {κ : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N)
    {f : UnitAddTorus (Fin N × Fin 1) → ℝ} {G : UnitAddTorus (Fin N × Fin 1) → Fin N × Fin 1 → ℝ}
    (hf2 : MemLp f 2 volume) (hG2 : ∀ j, MemLp (fun y => G y j) 2 volume) (hfG : IsWeakGrad f G)
    (hmean : ∫ y, gsW κ N y * f y = 0) (hnorm : ∫ y, gsW κ N y * f y ^ 2 = 1)
    (hE : ∫ y, gsW κ N y * sqNorm (G y) = (lamAll cosV (cosW κ) N).toReal)
    {ψ : UnitAddTorus (Fin N × Fin 1) → ℝ} {H : UnitAddTorus (Fin N × Fin 1) → Fin N × Fin 1 → ℝ}
    (hψ2 : MemLp ψ 2 volume) (hH2 : ∀ j, MemLp (fun y => H y j) 2 volume) (hψH : IsWeakGrad ψ H) :
    ∫ y, gsW κ N y * ∑ j, G y j * H y j =
      (lamAll cosV (cosW κ) N).toReal * ∫ y, gsW κ N y * f y * ψ y := by
  set L := (lamAll cosV (cosW κ) N).toReal with hL
  obtain ⟨m, hm, hb⟩ := gsW_bounds (N := N) hκ.le
  have hwm : AEStronglyMeasurable (gsW κ N) volume := (measurable_gsW κ).aestronglyMeasurable
  have hgb : ∀ y, ‖gsW κ N y‖ ≤ gsC κ N := fun y => by
    rw [Real.norm_eq_abs, abs_of_pos (gsW_pos κ y)]; exact (hb y).2
  have bw : ∀ {F : UnitAddTorus (Fin N × Fin 1) → ℝ}, Integrable F volume →
      Integrable (fun y => gsW κ N y * F y) volume := fun hF =>
    hF.bdd_mul hwm (Eventually.of_forall hgb)
  -- integrable pieces
  have iGH : Integrable (fun y => gsW κ N y * ∑ j, G y j * H y j) volume :=
    bw (integrable_finset_sum _ fun j _ => (hG2 j).integrable_mul (hH2 j))
  have iHH : Integrable (fun y => gsW κ N y * sqNorm (H y)) volume :=
    bw (integrable_finset_sum _ fun j _ => (hH2 j).integrable_sq)
  have iGG : Integrable (fun y => gsW κ N y * sqNorm (G y)) volume :=
    bw (integrable_finset_sum _ fun j _ => (hG2 j).integrable_sq)
  have ifψ : Integrable (fun y => gsW κ N y * f y * ψ y) volume := by
    have := bw (hf2.integrable_mul hψ2)
    exact this.congr (Eventually.of_forall fun y => by simp only [Pi.mul_apply]; ring)
  have iψψ : Integrable (fun y => gsW κ N y * ψ y ^ 2) volume := bw hψ2.integrable_sq
  have iff : Integrable (fun y => gsW κ N y * f y ^ 2) volume := bw hf2.integrable_sq
  have iψ : Integrable (fun y => gsW κ N y * ψ y) volume := bw (hψ2.integrable one_le_two)
  have if1 : Integrable (fun y => gsW κ N y * f y) volume := bw (hf2.integrable one_le_two)
  -- the quadratic inequality
  have hq : ∀ t : ℝ, 0 ≤ 2 * t * ((∫ y, gsW κ N y * ∑ j, G y j * H y j) -
      L * ∫ y, gsW κ N y * f y * ψ y) + t ^ 2 * ((∫ y, gsW κ N y * sqNorm (H y)) -
      L * ((∫ y, gsW κ N y * ψ y ^ 2) - (∫ y, gsW κ N y * ψ y) ^ 2)) := by
    intro t
    have hw : IsWeakGrad (fun y => f y + t * ψ y) (fun y j => G y j + t * H y j) :=
      hfG.add (hψH.cmul t)
    obtain ⟨hH1, hae⟩ := memH1_of_weakGrad_pair hw (hf2.add (hψ2.const_mul t))
      (fun j => (hG2 j).add ((hH2 j).const_mul t))
    have hP := lam_mul_Vw_le hκ hN hH1
    have hEt : Ew κ N (fun y => f y + t * ψ y) = L + 2 * t * (∫ y, gsW κ N y * ∑ j, G y j * H y j) +
        t ^ 2 * ∫ y, gsW κ N y * sqNorm (H y) := by
      unfold Ew
      rw [integral_congr_ae (hae.mono fun y hy => show gsW κ N y * sqNorm (weakGrad _ y) =
        gsW κ N y * sqNorm (G y) + 2 * t * (gsW κ N y * ∑ j, G y j * H y j) +
          t ^ 2 * (gsW κ N y * sqNorm (H y)) by
        rw [hy]; unfold sqNorm; simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring)]
      have i1 : Integrable (fun y => gsW κ N y * sqNorm (G y) +
          2 * t * (gsW κ N y * ∑ j, G y j * H y j)) volume := iGG.add (iGH.const_mul _)
      rw [integral_add (f := fun y => gsW κ N y * sqNorm (G y) +
          2 * t * (gsW κ N y * ∑ j, G y j * H y j))
          (g := fun y => t ^ 2 * (gsW κ N y * sqNorm (H y))) i1 (iHH.const_mul _),
        integral_add (f := fun y => gsW κ N y * sqNorm (G y))
          (g := fun y => 2 * t * (gsW κ N y * ∑ j, G y j * H y j)) iGG (iGH.const_mul _),
        integral_const_mul, integral_const_mul, hE]
    have hVt : Vw κ N (fun y => f y + t * ψ y) = 1 + 2 * t * (∫ y, gsW κ N y * f y * ψ y) +
        t ^ 2 * ((∫ y, gsW κ N y * ψ y ^ 2) - (∫ y, gsW κ N y * ψ y) ^ 2) := by
      unfold Vw
      have e1 : ∫ y, gsW κ N y * (f y + t * ψ y) ^ 2 = (∫ y, gsW κ N y * f y ^ 2) +
          2 * t * (∫ y, gsW κ N y * f y * ψ y) + t ^ 2 * ∫ y, gsW κ N y * ψ y ^ 2 := by
        have e : (fun y => gsW κ N y * (f y + t * ψ y) ^ 2) = fun y => gsW κ N y * f y ^ 2 +
            2 * t * (gsW κ N y * f y * ψ y) + t ^ 2 * (gsW κ N y * ψ y ^ 2) := by funext y; ring
        have i1 : Integrable (fun y => gsW κ N y * f y ^ 2 + 2 * t * (gsW κ N y * f y * ψ y))
          volume := iff.add (ifψ.const_mul _)
        rw [e, integral_add (f := fun y => gsW κ N y * f y ^ 2 + 2 * t * (gsW κ N y * f y * ψ y))
            (g := fun y => t ^ 2 * (gsW κ N y * ψ y ^ 2)) i1 (iψψ.const_mul _),
          integral_add (f := fun y => gsW κ N y * f y ^ 2)
            (g := fun y => 2 * t * (gsW κ N y * f y * ψ y)) iff (ifψ.const_mul _),
          integral_const_mul, integral_const_mul]
      have e2 : ∫ y, gsW κ N y * (f y + t * ψ y) = (∫ y, gsW κ N y * f y) +
          t * ∫ y, gsW κ N y * ψ y := by
        have e : (fun y => gsW κ N y * (f y + t * ψ y)) = fun y => gsW κ N y * f y +
            t * (gsW κ N y * ψ y) := by funext y; ring
        rw [e, integral_add (f := fun y => gsW κ N y * f y) (g := fun y => t * (gsW κ N y * ψ y))
          if1 (iψ.const_mul _), integral_const_mul]
      rw [e1, e2, hnorm, hmean]; ring
    rw [hEt, hVt] at hP
    nlinarith
  have := eq_zero_of_quadratic_nonneg hq
  linarith

theorem memLp_smPer {ι' : Type} [Fintype ι'] [DecidableEq ι'] {Φ : (ι' → ℝ) → ℝ} (hΦ : SmPer Φ)
    (p : ℝ≥0∞) : MemLp (fun y => Φ (secT y)) p volume := by
  obtain ⟨B, hB⟩ := periodic_bounded hΦ.1.continuous hΦ.2
  exact MemLp.of_bound (hΦ.1.continuous.measurable.comp measurable_secT).aestronglyMeasurable B
    (Eventually.of_forall fun y => hB _)

/-- (3.42) on the flat torus, for smooth periodic test functions. -/
theorem weak_eigen_flat {κ : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N)
    {f : UnitAddTorus (Fin N × Fin 1) → ℝ} {G : UnitAddTorus (Fin N × Fin 1) → Fin N × Fin 1 → ℝ}
    (hf2 : MemLp f 2 volume) (hG2 : ∀ j, MemLp (fun y => G y j) 2 volume) (hfG : IsWeakGrad f G)
    (hmean : ∫ y, gsW κ N y * f y = 0) (hnorm : ∫ y, gsW κ N y * f y ^ 2 = 1)
    (hE : ∫ y, gsW κ N y * sqNorm (G y) = (lamAll cosV (cosW κ) N).toReal)
    {Θ : (Fin N × Fin 1 → ℝ) → ℝ} (hΘ : SmPer Θ) :
    ∫ y, ∑ p, G y p * Dk Θ p (secT y) =
      ∫ y, ((lamAll cosV (cosW κ) N).toReal * f y -
        ∑ p, Dk (UL κ N) p (secT y) * G y p) * Θ (secT y) := by
  set L := (lamAll cosV (cosW κ) N).toReal with hL
  have hU := smPer_UL (N := N) κ
  have hEp : SmPer (fun x => Real.exp (UL κ N x) / gsC κ N) :=
    ⟨(Real.contDiff_exp.comp hU.1).div_const _, fun m x => by simp only [hU.2 m x]⟩
  set Ψ : (Fin N × Fin 1 → ℝ) → ℝ := fun x => Θ x * (Real.exp (UL κ N x) / gsC κ N) with hΨ
  have hΨs : SmPer Ψ := hΘ.mul hEp
  set ψ : UnitAddTorus (Fin N × Fin 1) → ℝ := fun y => Ψ (secT y) with hψ
  have hψlift : ψ ∘ liftT = Ψ := funext fun x => hΨs.2.secT_liftT x
  have hψw := isWeakGrad_of_contDiff (f := ψ) (by rw [hψlift]; exact hΨs.1.of_le (by simp))
  rw [hψlift] at hψw
  set H : UnitAddTorus (Fin N × Fin 1) → Fin N × Fin 1 → ℝ := fun y p => Dk Ψ p (secT y) with hH
  have hEL := euler_lagrange_flat hκ hN hf2 hG2 hfG hmean hnorm hE (memLp_smPer hΨs 2)
    (fun j => memLp_smPer (hΨs.Dk j) 2) hψw
  -- the identities `w H = ∇Θ + Θ ∇U`, `w ψ = Θ`
  have hwe : ∀ y, gsW κ N y * (Real.exp (UL κ N (secT y)) / gsC κ N) = 1 := fun y => by
    have h1 : Real.exp (-UL κ N (secT y)) * Real.exp (UL κ N (secT y)) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h2 := (gsC_pos κ N).ne'
    rw [gsW]
    field_simp
    linarith
  have hDΨ : ∀ p x, Dk Ψ p x = (Dk Θ p x + Θ x * Dk (UL κ N) p x) *
      (Real.exp (UL κ N x) / gsC κ N) := fun p x => by
    have h1 := ((hU.1.differentiable (by simp) x).hasFDerivAt.exp).const_mul (1 / gsC κ N)
    have hd : HasFDerivAt (fun x => Real.exp (UL κ N x) / gsC κ N)
        ((1 / gsC κ N) • (Real.exp (UL κ N x) • fderiv ℝ (UL κ N) x)) x :=
      h1.congr_of_eventuallyEq (Eventually.of_forall fun y => by simp only; ring)
    rw [hΨ, Dk_mul (hΘ.1.differentiable (by simp)) (hEp.1.differentiable (by simp))]
    simp only [Dk]
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hlhs : ∫ y, gsW κ N y * ∑ j, G y j * H y j =
      ∫ y, ∑ p, (G y p * Dk Θ p (secT y) + Dk (UL κ N) p (secT y) * G y p * Θ (secT y)) := by
    congr 1; funext y
    simp only [hH, hDΨ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have := hwe y
    calc gsW κ N y * (G y p * ((Dk Θ p (secT y) + Θ (secT y) * Dk (UL κ N) p (secT y)) *
          (Real.exp (UL κ N (secT y)) / gsC κ N)))
        = (gsW κ N y * (Real.exp (UL κ N (secT y)) / gsC κ N)) *
            (G y p * (Dk Θ p (secT y) + Θ (secT y) * Dk (UL κ N) p (secT y))) := by ring
      _ = _ := by rw [this]; ring
  have hrhs : ∫ y, gsW κ N y * f y * ψ y = ∫ y, f y * Θ (secT y) := by
    congr 1; funext y
    have := hwe y
    simp only [hψ, hΨ]
    calc gsW κ N y * f y * (Θ (secT y) * (Real.exp (UL κ N (secT y)) / gsC κ N))
        = (gsW κ N y * (Real.exp (UL κ N (secT y)) / gsC κ N)) * (f y * Θ (secT y)) := by ring
      _ = _ := by rw [this, one_mul]
  rw [hlhs, hrhs] at hEL
  -- integrability
  have iG : ∀ p (Φ : (Fin N × Fin 1 → ℝ) → ℝ), SmPer Φ →
      Integrable (fun y => G y p * Φ (secT y)) volume := fun p Φ hΦ =>
    (hG2 p).integrable_mul (memLp_smPer hΦ 2)
  have iA : Integrable (fun y => ∑ p, G y p * Dk Θ p (secT y)) volume :=
    integrable_finset_sum _ fun p _ => iG p _ (hΘ.Dk p)
  have iB : Integrable (fun y => ∑ p, Dk (UL κ N) p (secT y) * G y p * Θ (secT y)) volume :=
    integrable_finset_sum _ fun p _ => (iG p _ ((hU.Dk p).mul hΘ)).congr
      (Eventually.of_forall fun y => by simp only; ring)
  have iC : Integrable (fun y => f y * Θ (secT y)) volume := hf2.integrable_mul (memLp_smPer hΘ 2)
  have e1 : ∫ y, ∑ p, (G y p * Dk Θ p (secT y) + Dk (UL κ N) p (secT y) * G y p * Θ (secT y)) =
      (∫ y, ∑ p, G y p * Dk Θ p (secT y)) +
        ∫ y, ∑ p, Dk (UL κ N) p (secT y) * G y p * Θ (secT y) := by
    rw [← integral_add iA iB]; congr 1; funext y; rw [Finset.sum_add_distrib]
  have e2 : ∫ y, (L * f y - ∑ p, Dk (UL κ N) p (secT y) * G y p) * Θ (secT y) =
      L * (∫ y, f y * Θ (secT y)) - ∫ y, ∑ p, Dk (UL κ N) p (secT y) * G y p * Θ (secT y) := by
    rw [← integral_const_mul, ← integral_sub (iC.const_mul L) iB]
    congr 1; funext y; rw [sub_mul, Finset.sum_mul]; ring
  rw [e2]
  linarith

theorem fourierCoeffT_eq_cf {ι' : Type} [Fintype ι'] [DecidableEq ι'] (f : UnitAddTorus ι' → ℝ)
    (k : ι' → ℤ) : fourierCoeffT f k = cf f k := by
  rw [fourierCoeffT, cf, SharpLSI.mFourierCoeff_eq_integral]
  congr 1; funext y
  rw [mFourier_neg, smul_eq_mul, mul_comm]

/-- The real and imaginary parts of `e_{-k}` as smooth periodic lifts. -/
theorem smPer_re_mFourier {ι' : Type} [Fintype ι'] [DecidableEq ι'] (k : ι' → ℤ) :
    SmPer (fun x : ι' → ℝ => (mFourier k (liftT x)).re) :=
  ⟨Complex.reCLM.contDiff.comp ((contDiff_mFourier_liftT k).of_le le_top), fun m x => by
    simp only [liftT_add_intVec]⟩

theorem smPer_im_mFourier {ι' : Type} [Fintype ι'] [DecidableEq ι'] (k : ι' → ℤ) :
    SmPer (fun x : ι' → ℝ => (mFourier k (liftT x)).im) :=
  ⟨Complex.imCLM.contDiff.comp ((contDiff_mFourier_liftT k).of_le le_top), fun m x => by
    simp only [liftT_add_intVec]⟩

theorem Dk_re_mFourier {ι' : Type} [Fintype ι'] [DecidableEq ι'] (k : ι' → ℤ) (p : ι')
    (x : ι' → ℝ) : Dk (fun x : ι' → ℝ => (mFourier k (liftT x)).re) p x =
      (2 * π * I * k p * mFourier k (liftT x)).re := by
  have hd := ((contDiff_mFourier_liftT k).differentiable (by simp) x).hasFDerivAt
  have : (fun x : ι' → ℝ => (mFourier k (liftT x)).re) =
      Complex.reCLM ∘ fun x : ι' → ℝ => mFourier k (liftT x) := rfl
  rw [Dk, this, (Complex.reCLM.hasFDerivAt.comp x hd).fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, Complex.reCLM_apply]
  rw [fderiv_mFourier_liftT]

theorem Dk_im_mFourier {ι' : Type} [Fintype ι'] [DecidableEq ι'] (k : ι' → ℤ) (p : ι')
    (x : ι' → ℝ) : Dk (fun x : ι' → ℝ => (mFourier k (liftT x)).im) p x =
      (2 * π * I * k p * mFourier k (liftT x)).im := by
  have hd := ((contDiff_mFourier_liftT k).differentiable (by simp) x).hasFDerivAt
  have : (fun x : ι' → ℝ => (mFourier k (liftT x)).im) =
      Complex.imCLM ∘ fun x : ι' → ℝ => mFourier k (liftT x) := rfl
  rw [Dk, this, (Complex.imCLM.hasFDerivAt.comp x hd).fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, Complex.imCLM_apply]
  rw [fderiv_mFourier_liftT]

/-- The Fourier form of (3.42): `4π²|k|² f̂(k) = R̂(k)`, `R = λf - ∇U·∇f`. -/
theorem cf_eigen {κ : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N)
    {f : UnitAddTorus (Fin N × Fin 1) → ℝ} {G : UnitAddTorus (Fin N × Fin 1) → Fin N × Fin 1 → ℝ}
    (hf2 : MemLp f 2 volume) (hG2 : ∀ j, MemLp (fun y => G y j) 2 volume) (hfG : IsWeakGrad f G)
    (hmean : ∫ y, gsW κ N y * f y = 0) (hnorm : ∫ y, gsW κ N y * f y ^ 2 = 1)
    (hE : ∫ y, gsW κ N y * sqNorm (G y) = (lamAll cosV (cosW κ) N).toReal) (k : Fin N × Fin 1 → ℤ) :
    (4 * π ^ 2 * ∑ j, ((k j : ℝ)) ^ 2 : ℝ) * cf f k =
      cf (fun y => (lamAll cosV (cosW κ) N).toReal * f y - ∑ p, Dk (UL κ N) p (secT y) * G y p) k := by
  set L := (lamAll cosV (cosW κ) N).toReal with hL
  set R : UnitAddTorus (Fin N × Fin 1) → ℝ :=
    fun y => L * f y - ∑ p, Dk (UL κ N) p (secT y) * G y p with hR
  have hU := smPer_UL (N := N) κ
  have hR2 : MemLp R 2 volume := by
    refine (hf2.const_mul L).sub ?_
    refine memLp_finset_sum (f := fun p y => Dk (UL κ N) p (secT y) * G y p) _ fun p _ => ?_
    obtain ⟨B, hB⟩ := periodic_bounded (hU.Dk p).1.continuous (hU.Dk p).2
    refine ((hG2 p).const_mul B).of_le
      (((hU.Dk p).1.continuous.measurable.comp measurable_secT).aestronglyMeasurable.mul
        (hG2 p).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    rw [norm_mul, norm_mul]
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    rw [Real.norm_of_nonneg hB0]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  set e : UnitAddTorus (Fin N × Fin 1) → ℂ := fun y => mFourier (-k) y with he
  have hc := weak_eigen_flat hκ hN hf2 hG2 hfG hmean hnorm hE (smPer_re_mFourier (-k))
  have hs := weak_eigen_flat hκ hN hf2 hG2 hfG hmean hnorm hE (smPer_im_mFourier (-k))
  simp only [Dk_re_mFourier, Dk_im_mFourier, liftT_secT] at hc hs
  -- complex combination
  have hGi : ∀ p, Integrable (fun y => (G y p : ℂ) * (2 * π * I * ((-k) p : ℤ) * e y)) volume :=
    fun p => by
      have hm : AEStronglyMeasurable (fun y => (G y p : ℂ) * (2 * π * I * ((-k) p : ℤ) * e y))
          volume :=
        (Complex.continuous_ofReal.comp_aestronglyMeasurable (hG2 p).aestronglyMeasurable).mul
          (continuous_const.mul (mFourier (-k)).continuous).aestronglyMeasurable
      refine Integrable.mono' (((hG2 p).integrable one_le_two).norm.const_mul
        (2 * π * |((((-k) p : ℤ) : ℝ))|)) hm (Eventually.of_forall fun y => ?_)
      have h1 := norm_mFourier_le (-k) y
      have hc : ‖(2 * π * I * ((((-k) p : ℤ)) : ℂ))‖ = 2 * π * |((((-k) p : ℤ) : ℝ))| := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_two,
          Real.norm_of_nonneg Real.pi_pos.le]
        rw [show (((-k) p : ℤ) : ℂ) = ((((-k) p : ℤ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
          Real.norm_eq_abs]
        ring
      have h2 : 0 ≤ 2 * π * |((((-k) p : ℤ) : ℝ))| := by positivity
      calc ‖(G y p : ℂ) * (2 * π * I * ((-k) p : ℤ) * e y)‖
          = ‖G y p‖ * (2 * π * |((((-k) p : ℤ) : ℝ))| * ‖mFourier (-k) y‖) := by
            rw [norm_mul, norm_mul, hc, Complex.norm_real]
        _ ≤ ‖G y p‖ * (2 * π * |((((-k) p : ℤ) : ℝ))| * 1) := by gcongr
        _ = 2 * π * |((((-k) p : ℤ) : ℝ))| * ‖G y p‖ := by ring
  have hRi : Integrable (fun y => (R y : ℂ) * e y) volume := by
    have := (hR2.integrable one_le_two).ofReal.mul_bdd (c := 1) (mFourier (-k)).continuous.aestronglyMeasurable
      (Eventually.of_forall fun y => norm_mFourier_le (-k) y)
    exact this
  have hcomplex : ∫ y, ∑ p, (G y p : ℂ) * (2 * π * I * ((-k) p : ℤ) * e y) = ∫ y, (R y : ℂ) * e y := by
    have hLi : Integrable (fun y => ∑ p, (G y p : ℂ) * (2 * π * I * ((-k) p : ℤ) * e y)) volume :=
      integrable_finset_sum _ fun p _ => hGi p
    apply Complex.ext
    · have h1 := integral_re hLi
      have h2 := integral_re hRi
      simp only [RCLike.re_to_complex] at h1 h2
      rw [← h1, ← h2]
      convert hc using 2
      · funext y; simp only [Complex.re_sum, Complex.re_ofReal_mul, he]
      · funext y; simp only [Complex.re_ofReal_mul, hR, he, hL]
    · have h1 := integral_im hLi
      have h2 := integral_im hRi
      simp only [RCLike.im_to_complex] at h1 h2
      rw [← h1, ← h2]
      convert hs using 2
      · funext y; simp only [Complex.im_sum, Complex.im_ofReal_mul, he]
      · funext y; simp only [Complex.im_ofReal_mul, hR, he, hL]
  -- evaluate both sides
  have hcfG : ∀ p, cf (fun y => G y p) k = 2 * π * I * k p * cf f k := fun p =>
    mFourierCoeff_grad hfG (hf2.integrable one_le_two) (fun j => (hG2 j).integrable one_le_two) k p
  have hl : ∫ y, ∑ p, (G y p : ℂ) * (2 * π * I * ((-k) p : ℤ) * e y) =
      ∑ p, (2 * π * I * ((-k) p : ℤ)) * cf (fun y => G y p) k := by
    rw [integral_finset_sum _ fun p _ => hGi p]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [cf, SharpLSI.mFourierCoeff_eq_integral, ← integral_const_mul]
    congr 1; funext y; simp only [he, smul_eq_mul]; ring
  have hr : ∫ y, (R y : ℂ) * e y = cf R k := by
    rw [cf, SharpLSI.mFourierCoeff_eq_integral]
    congr 1; funext y; simp only [he, smul_eq_mul]; ring
  rw [hl, hr] at hcomplex
  rw [← hcomplex]
  simp_rw [hcfG]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.neg_apply, Int.cast_neg]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem memLp_eigen_rhs {κ : ℝ} {f : UnitAddTorus (Fin N × Fin 1) → ℝ}
    {G : UnitAddTorus (Fin N × Fin 1) → Fin N × Fin 1 → ℝ} (hf2 : MemLp f 2 volume)
    (hG2 : ∀ j, MemLp (fun y => G y j) 2 volume) (L : ℝ) :
    MemLp (fun y => L * f y - ∑ p, Dk (UL κ N) p (secT y) * G y p) 2 volume := by
  have hU := smPer_UL (N := N) κ
  refine (hf2.const_mul L).sub ?_
  refine memLp_finset_sum (f := fun p y => Dk (UL κ N) p (secT y) * G y p) _ fun p _ => ?_
  obtain ⟨B, hB⟩ := periodic_bounded (hU.Dk p).1.continuous (hU.Dk p).2
  refine ((hG2 p).const_mul B).of_le
    (((hU.Dk p).1.continuous.measurable.comp measurable_secT).aestronglyMeasurable.mul
      (hG2 p).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  rw [norm_mul, norm_mul]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [Real.norm_of_nonneg hB0]
  exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)

/-- `H²` regularity of the minimizer. -/
theorem summable_H2 {κ : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N)
    {f : UnitAddTorus (Fin N × Fin 1) → ℝ} {G : UnitAddTorus (Fin N × Fin 1) → Fin N × Fin 1 → ℝ}
    (hf2 : MemLp f 2 volume) (hG2 : ∀ j, MemLp (fun y => G y j) 2 volume) (hfG : IsWeakGrad f G)
    (hmean : ∫ y, gsW κ N y * f y = 0) (hnorm : ∫ y, gsW κ N y * f y ^ 2 = 1)
    (hE : ∫ y, gsW κ N y * sqNorm (G y) = (lamAll cosV (cosW κ) N).toReal) :
    Summable fun k : Fin N × Fin 1 → ℤ => (1 + ∑ i, ((k i : ℝ)) ^ 2) ^ 2 * ‖cf f k‖ ^ 2 := by
  set R := fun y => (lamAll cosV (cosW κ) N).toReal * f y - ∑ p, Dk (UL κ N) p (secT y) * G y p
  have hR2 : MemLp R 2 volume := memLp_eigen_rhs hf2 hG2 _
  have hRs := (hasSum_sq_mFourierCoeff_real hR2).summable
  have hfs := (hasSum_sq_mFourierCoeff_real hf2).summable
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((hfs.mul_left 2).add (hRs.div_const (8 * π ^ 4)))
  set sk := ∑ i, ((k i : ℝ)) ^ 2 with hsk
  have hs0 : 0 ≤ sk := Finset.sum_nonneg fun i _ => sq_nonneg _
  have he := cf_eigen hκ hN hf2 hG2 hfG hmean hnorm hE k
  have hn : (4 * π ^ 2 * sk) * ‖cf f k‖ = ‖cf R k‖ := by
    rw [← he, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hsq : 16 * π ^ 4 * (sk ^ 2 * ‖cf f k‖ ^ 2) = ‖cf R k‖ ^ 2 := by
    rw [← hn]; ring
  have hpi : 0 < π ^ 4 := by positivity
  have h1 : sk ^ 2 * ‖cf f k‖ ^ 2 = ‖cf R k‖ ^ 2 / (16 * π ^ 4) := by
    rw [eq_div_iff (by positivity)]; linarith
  calc (1 + sk) ^ 2 * ‖cf f k‖ ^ 2 ≤ 2 * ‖cf f k‖ ^ 2 + 2 * (sk ^ 2 * ‖cf f k‖ ^ 2) := by
        nlinarith [sq_nonneg (1 - sk), sq_nonneg ‖cf f k‖, mul_nonneg (sq_nonneg (1 - sk))
          (sq_nonneg ‖cf f k‖)]
    _ = 2 * ‖cf f k‖ ^ 2 + ‖cf R k‖ ^ 2 / (8 * π ^ 4) := by rw [h1]; field_simp; ring

/-- Step 2 of Proposition 3.5. -/
theorem cosine_gap_minimizer_aux {κ : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N) :
    ∃ φ : Config N 1 → ℝ, MemH1C (gibbs cosV (cosW κ) N) φ ∧
      ∫ X, φ X ∂gibbs cosV (cosW κ) N = 0 ∧ ∫ X, φ X ^ 2 ∂gibbs cosV (cosW κ) N = 1 ∧
      energy cosV (cosW κ) N φ = lamAll cosV (cosW κ) N ∧ MemH2C φ ∧
      ∀ η : Config N 1 → ℝ, IsSmoothC η →
        ∫ X, ∑ i, weakGradC φ X i 0 * cpartialC η i 0 X =
          ∫ X, ((lamAll cosV (cosW κ) N).toReal * φ X -
            ∑ i, cpartialC (cosU κ N) i 0 X * weakGradC φ X i 0) * η X := by
  obtain ⟨f, G, hf2, hG2, hfG, hmean, hnorm, hE⟩ := exists_minimizer_flat hκ hN
  obtain ⟨hfH1, hfae⟩ := memH1_of_weakGrad_pair hfG hf2 hG2
  have hLt := lamAll_lt_top (κ := κ) hN
  refine ⟨fun X => f (flat X), memH1C_of_flat hκ.le hfH1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [integral_flat (κ := κ) f hf2.aestronglyMeasurable]; exact hmean
  · rw [integral_flat (κ := κ) (fun y => f y ^ 2) (hf2.aestronglyMeasurable.pow 2)]; exact hnorm
  · rw [energy_flat hκ.le hfH1]
    have : Ew κ N f = ∫ y, gsW κ N y * sqNorm (G y) :=
      integral_congr_ae (hfae.mono fun y hy => by simp only [hy])
    rw [this, hE, ENNReal.ofReal_toReal hLt.ne]
  · show MemH2 f
    refine ⟨hf2, ?_⟩
    simp_rw [fourierCoeffT_eq_cf]
    exact summable_H2 hκ hN hf2 hG2 hfG hmean hnorm hE
  · intro η hη
    set Θ := (η ∘ unflat) ∘ liftT with hΘ
    have hΘs : SmPer Θ := ⟨hη, isPer_lift _⟩
    have hweak := weak_eigen_flat hκ hN hf2 hG2 hfG hmean hnorm hE hΘs
    -- transfer both integrals to the flat torus
    have hmp := measurePreserving_flat (N := N)
    have hl : ∫ X, ∑ i, weakGradC (fun X => f (flat X)) X i 0 * cpartialC η i 0 X =
        ∫ y, ∑ p, G y p * Dk Θ p (secT y) := by
      have e : ∀ X : Config N 1, ∑ i, weakGradC (fun X => f (flat X)) X i 0 * cpartialC η i 0 X =
          (fun y => ∑ p : Fin N × Fin 1, weakGrad f y p * Dk Θ p (secT y)) (flat X) := fun X => by
        simp only [weakGradC]
        rw [Fintype.sum_prod_type]
        simp only [Fin.sum_univ_one]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show cpartialC η i 0 X = cpartialC η i 0 (unflat (flat X)) from rfl, cpartialC_unflat]
        rfl
      rw [integral_congr_ae (Eventually.of_forall e),
        hmp.integral_comp measurableEmbedding_flat
          (fun y => ∑ p : Fin N × Fin 1, weakGrad f y p * Dk Θ p (secT y))]
      exact integral_congr_ae (hfae.mono fun y hy => by simp only [hy])
    have hr : ∫ X, ((lamAll cosV (cosW κ) N).toReal * f (flat X) -
          ∑ i, cpartialC (cosU κ N) i 0 X * weakGradC (fun X => f (flat X)) X i 0) * η X =
        ∫ y, ((lamAll cosV (cosW κ) N).toReal * f y -
          ∑ p, Dk (UL κ N) p (secT y) * G y p) * Θ (secT y) := by
      have e : ∀ X : Config N 1, ((lamAll cosV (cosW κ) N).toReal * f (flat X) -
          ∑ i, cpartialC (cosU κ N) i 0 X * weakGradC (fun X => f (flat X)) X i 0) * η X =
          (fun y => ((lamAll cosV (cosW κ) N).toReal * f y -
            ∑ p : Fin N × Fin 1, Dk (UL κ N) p (secT y) * weakGrad f y p) * Θ (secT y)) (flat X) :=
        fun X => by
          simp only [weakGradC]
          rw [Fintype.sum_prod_type]
          simp only [Fin.sum_univ_one]
          congr 1
          · congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [show cpartialC (cosU κ N) i 0 X = cpartialC (cosU κ N) i 0 (unflat (flat X)) from rfl,
              cpartialC_unflat, ← UL_eq_lift]
            rfl
          · simp only [hΘ, Function.comp_apply, liftT_secT]
            rfl
      rw [integral_congr_ae (Eventually.of_forall e),
        hmp.integral_comp measurableEmbedding_flat
          (fun y => ((lamAll cosV (cosW κ) N).toReal * f y -
            ∑ p : Fin N × Fin 1, Dk (UL κ N) p (secT y) * weakGrad f y p) * Θ (secT y))]
      exact integral_congr_ae (hfae.mono fun y hy => by simp only [hy])
    rw [hl, hr]
    exact hweak

end Cosine

end SharpLSI
