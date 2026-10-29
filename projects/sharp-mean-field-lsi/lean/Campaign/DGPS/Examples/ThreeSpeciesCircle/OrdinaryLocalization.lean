import DGPS.Examples.ThreeSpeciesCircle.OrdinaryOptimizers

open MeasureTheory Filter Topology

/-!
# Ordinary optimizers: global localization in `H¹` (packet STR025a)

For `h_j → 0` and any global minimizers `ρ_j` of the ordinary quotient `I(ρ|μ_h)/(2H(ρ|μ_h))`
at `h_j`, `√ρ_j → 1` in `H¹(m)`: both `‖√ρ_j − 1‖²_{L²}` and `‖∇√ρ_j‖²_{L²}` tend to `0`
(the weak gradient of the constant `1` vanishes).  The `C^{2,α}` Euler bootstrap is a separate
packet.
-/

open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Young's inequality in the form `(a+b)² ≤ (1+η)a² + (1+1/η)b²`. -/
private theorem str025a_young {η : ℝ} (hη : 0 < η) (a b : ℝ) :
    (a + b) ^ 2 ≤ (1 + η) * a ^ 2 + (1 + 1 / η) * b ^ 2 := by
  rw [← sub_nonneg]
  have : (1 + η) * a ^ 2 + (1 + 1 / η) * b ^ 2 - (a + b) ^ 2 = (η * a - b) ^ 2 / η := by
    field_simp
    ring
  rw [this]
  positivity

/-- Hellinger-type bound: `‖√ρ - 1‖²_{L²} ≤ H(ρ | m)`. -/
private theorem str025a_hellinger_le (ρ : AbsoluteDensity 1) :
    ∫ x, (ρ.sqrt x - 1) ^ 2 ∂haar 1 ≤ DGPS.Analysis.circleEntropy ρ := by
  have hu : MemLp ρ.sqrt 2 (haar 1) := ρ.memLp_sqrt
  have i1 : Integrable (fun x => ρ.density x * Real.log (ρ.density x)) (haar 1) :=
    (absoluteDensity_entropy_finite ρ).1
  have i2 : Integrable ρ.density (haar 1) := ρ.integrable_density
  have hL : Integrable (fun x => (ρ.sqrt x - 1) ^ 2) (haar 1) :=
    (hu.sub (memLp_const 1)).integrable_sq
  have hR : Integrable (fun x => ρ.density x * Real.log (ρ.density x) - ρ.density x + 1)
      (haar 1) := (i1.sub i2).add (integrable_const 1)
  have hint : ∫ x, (ρ.density x * Real.log (ρ.density x) - ρ.density x + 1) ∂haar 1 =
      DGPS.Analysis.circleEntropy ρ := by
    rw [integral_add (f := fun x => ρ.density x * Real.log (ρ.density x) - ρ.density x)
      (g := fun _ => (1 : ℝ)) (i1.sub i2) (integrable_const 1), integral_sub i1 i2,
      ρ.integral_density, circleEntropy_eq]
    simp
  rw [← hint]
  refine integral_mono_ae hL hR ?_
  filter_upwards [ρ.sqrt_nonneg] with x hx
  have hx : 0 ≤ ρ.sqrt x := hx
  have hd : ρ.density x = ρ.sqrt x ^ 2 := rfl
  have hlog : Real.log (ρ.density x) = 2 * Real.log (ρ.sqrt x) := by
    rw [hd, Real.log_pow]; norm_num
  have hk := self_mul_log_sub_add_one_nonneg hx
  rw [hlog, hd]
  have : 0 ≤ 2 * ρ.sqrt x * (ρ.sqrt x * Real.log (ρ.sqrt x) - ρ.sqrt x + 1) :=
    mul_nonneg (by linarith) hk
  nlinarith [this]

/-- The entropy at `μ_h` is within `2|h|` of the entropy at Haar. -/
private theorem str025a_entropy_real (h : ℝ) (ρ : AbsoluteDensity 1) :
    ∃ y : ℝ, ordinaryEntropy h ρ = ENNReal.ofReal y ∧
      |y - DGPS.Analysis.circleEntropy ρ| ≤ 2 * |h| := by
  refine ⟨_, ordinaryEntropy_eq h ρ, ?_⟩
  have := abs_integral_density_mul_log_reference_le h ρ
  have e : DGPS.Analysis.circleEntropy ρ -
      ∫ x, ρ.density x * Real.log (referenceDensity h x) ∂haar 1 -
      DGPS.Analysis.circleEntropy ρ = -∫ x, ρ.density x * Real.log (referenceDensity h x) ∂haar 1 := by
    ring
  rw [e, abs_neg]
  exact this

/-- Comparison of the ordinary Fisher information with the circle Fisher information. -/
private theorem str025a_fisher_cmp (h : ℝ) (ρ : AbsoluteDensity 1) {η : ℝ} (hη : 0 < η) :
    (ordinaryFisher h ρ).toReal ≤
        (1 + η) * DGPS.Analysis.circleFisherInformation ρ + (1 + 1 / η) * logGradBound h ^ 2 ∧
      DGPS.Analysis.circleFisherInformation ρ ≤
        (1 + η) * (ordinaryFisher h ρ).toReal + (1 + 1 / η) * logGradBound h ^ 2 := by
  set g : Torus 1 → ℝ := fun x => weakGradient ρ.sqrt ρ.sqrt_mem x 0 with hg
  have hG := isWeakGradient_weakGradient ρ.sqrt_mem
  have hgm : MemLp g 2 (haar 1) := memLp_coord hG.memLp_grad 0
  have hum : MemLp (fun x => ρ.sqrt x * logScore h x) 2 (haar 1) :=
    memLp_mul_logScore h ρ.memLp_sqrt
  have iA : Integrable (fun x => (2 * g x) ^ 2) (haar 1) := (hgm.const_mul 2).integrable_sq
  have iB : Integrable (fun x => (ρ.sqrt x * logScore h x) ^ 2) (haar 1) := hum.integrable_sq
  have iD : Integrable (fun x => (2 * g x - ρ.sqrt x * logScore h x) ^ 2) (haar 1) :=
    ((hgm.const_mul 2).sub hum).integrable_sq
  have hIm : DGPS.Analysis.circleFisherInformation ρ = ∫ x, (2 * g x) ^ 2 ∂haar 1 := by
    rw [circleFisher_eq_four_mul]
    simp_rw [tangent1_norm, sq_abs, mul_pow]
    rw [integral_const_mul]
    norm_num [hg]
  have hJ : (ordinaryFisher h ρ).toReal = ∫ x, (2 * g x - ρ.sqrt x * logScore h x) ^ 2 ∂haar 1 := by
    rw [ordinaryFisher_eq, ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg _)]
  have hK : ∫ x, (ρ.sqrt x * logScore h x) ^ 2 ∂haar 1 ≤ logGradBound h ^ 2 := by
    have hb : ∫ x, (ρ.sqrt x * logScore h x) ^ 2 ∂haar 1 ≤
        ∫ x, logGradBound h ^ 2 * ρ.sqrt x ^ 2 ∂haar 1 := by
      refine integral_mono_ae iB (ρ.memLp_sqrt.integrable_sq.const_mul _) ?_
      filter_upwards [abs_logScore_le h] with x hx
      rw [mul_pow]
      have : logScore h x ^ 2 ≤ logGradBound h ^ 2 := by
        rw [← sq_abs (logScore h x)]
        exact pow_le_pow_left₀ (abs_nonneg _) hx 2
      nlinarith [sq_nonneg (ρ.sqrt x)]
    refine hb.trans (le_of_eq ?_)
    rw [integral_const_mul, ρ.mass_one]
    ring
  have hc : 0 ≤ 1 + 1 / η := by positivity
  constructor
  · rw [hJ, hIm]
    calc _ ≤ ∫ x, ((1 + η) * (2 * g x) ^ 2 + (1 + 1 / η) * (ρ.sqrt x * logScore h x) ^ 2)
          ∂haar 1 := by
          refine integral_mono iD ((iA.const_mul _).add (iB.const_mul _)) fun x => ?_
          have := str025a_young hη (2 * g x) (-(ρ.sqrt x * logScore h x))
          simpa [sub_eq_add_neg] using this
      _ = (1 + η) * ∫ x, (2 * g x) ^ 2 ∂haar 1 +
          (1 + 1 / η) * ∫ x, (ρ.sqrt x * logScore h x) ^ 2 ∂haar 1 := by
          rw [integral_add (iA.const_mul _) (iB.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ _ := by gcongr
  · rw [hJ, hIm]
    calc _ ≤ ∫ x, ((1 + η) * (2 * g x - ρ.sqrt x * logScore h x) ^ 2 +
          (1 + 1 / η) * (ρ.sqrt x * logScore h x) ^ 2) ∂haar 1 := by
          refine integral_mono iA ((iD.const_mul _).add (iB.const_mul _)) fun x => ?_
          have := str025a_young hη (2 * g x - ρ.sqrt x * logScore h x) (ρ.sqrt x * logScore h x)
          simpa using this
      _ = (1 + η) * ∫ x, (2 * g x - ρ.sqrt x * logScore h x) ^ 2 ∂haar 1 +
          (1 + 1 / η) * ∫ x, (ρ.sqrt x * logScore h x) ^ 2 ∂haar 1 := by
          rw [integral_add (iD.const_mul _) (iB.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ _ := by gcongr

/-- The real-variable core: the quotient bound, the strict Haar remainder and the comparison
of informations force the entropy and information at Haar to vanish. -/
private theorem str025a_core {a0 : ℝ} (ha0 : 0 < a0) {x I J L hh Hh : ℕ → ℝ}
    (hx : ∀ j, 0 ≤ x j) (hI : ∀ j, 2 * a0 * x j + a0 / 6 * x j ^ 2 ≤ I j) (hI0 : ∀ j, 0 ≤ I j)
    (hJ : ∀ j, ∀ η : ℝ, 0 < η → I j ≤ (1 + η) * J j + (1 + 1 / η) * L j ^ 2)
    (hHh : ∀ j, 0 < Hh j ∧ Hh j ≤ x j + 2 * |hh j|)
    (hq : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, J j ≤ 2 * (a0 + ε) * Hh j)
    (hL : Tendsto L atTop (𝓝 0)) (hhT : Tendsto hh atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0) ∧ Tendsto I atTop (𝓝 0) := by
  have hL2 : Tendsto (fun j => L j ^ 2) atTop (𝓝 0) := by
    simpa using hL.pow 2
  have hhabs : Tendsto (fun j => |hh j|) atTop (𝓝 0) := by simpa using hhT.abs
  have hx0 : Tendsto x atTop (𝓝 0) := by
    set K : ℝ := 144 * (a0 + 2) ^ 2 / a0 ^ 2 + 1 with hK
    have hK1 : 1 ≤ K := by
      have : 0 ≤ 144 * (a0 + 2) ^ 2 / a0 ^ 2 := by positivity
      linarith
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun j => lt_of_lt_of_le ha (hx j), ?_⟩
    intro a ha
    set ε : ℝ := min 1 (a / (2 * (K + 1))) with hε
    have hε0 : 0 < ε := lt_min one_pos (by positivity)
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hεa : (K + 1) * ε ≤ a / 2 := by
      have : ε ≤ a / (2 * (K + 1)) := min_le_right _ _
      calc (K + 1) * ε ≤ (K + 1) * (a / (2 * (K + 1))) := by gcongr
        _ = a / 2 := by field_simp
    set R : ℕ → ℝ := fun j => 2 * (1 + ε) * (a0 + ε) * (2 * |hh j|) + (1 + 1 / ε) * L j ^ 2
      with hR
    have hRt : Tendsto (fun j => 12 * R j / a0) atTop (𝓝 0) := by
      have : Tendsto R atTop (𝓝 (2 * (1 + ε) * (a0 + ε) * (2 * 0) + (1 + 1 / ε) * 0)) :=
        ((hhabs.const_mul 2).const_mul _).add (hL2.const_mul _)
      simpa [hR] using (this.const_mul 12).div_const a0
    filter_upwards [hq ε hε0, hRt.eventually (gt_mem_nhds (show (0 : ℝ) < ε ^ 2 by positivity))]
      with j hj1 hj2
    have h1 := hI j
    have h2 := hJ j ε hε0
    obtain ⟨hHp, hHb⟩ := hHh j
    have h3 : I j ≤ (1 + ε) * (2 * (a0 + ε) * (x j + 2 * |hh j|)) + (1 + 1 / ε) * L j ^ 2 := by
      refine h2.trans ?_
      have : J j ≤ 2 * (a0 + ε) * (x j + 2 * |hh j|) :=
        hj1.trans (by gcongr)
      have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ 1 + ε)
      linarith
    set κ : ℝ := 2 * ((1 + ε) * (a0 + ε) - a0) with hκ
    have h4 : a0 / 6 * x j ^ 2 ≤ κ * x j + R j := by
      have e : (1 + ε) * (2 * (a0 + ε) * (x j + 2 * |hh j|)) + (1 + 1 / ε) * L j ^ 2 =
          (2 * a0 * x j + κ * x j) + R j := by
        simp only [hκ, hR]; ring
      linarith
    have hκ0 : 0 ≤ κ := by
      simp only [hκ]; nlinarith
    have hκε : κ ≤ 2 * (a0 + 2) * ε := by
      simp only [hκ]; nlinarith
    have h5 : κ * x j ≤ a0 / 12 * x j ^ 2 + 3 * κ ^ 2 / a0 := by
      have : 0 ≤ a0 / 12 * (x j - 6 * κ / a0) ^ 2 := by positivity
      have e : a0 / 12 * (x j - 6 * κ / a0) ^ 2 =
          a0 / 12 * x j ^ 2 - κ * x j + 3 * κ ^ 2 / a0 := by field_simp; ring
      linarith
    have h6 : x j ^ 2 ≤ 36 * κ ^ 2 / a0 ^ 2 + 12 * R j / a0 := by
      have : a0 / 12 * x j ^ 2 ≤ 3 * κ ^ 2 / a0 + R j := by linarith
      have e : x j ^ 2 = 12 / a0 * (a0 / 12 * x j ^ 2) := by field_simp
      rw [e]
      calc 12 / a0 * (a0 / 12 * x j ^ 2) ≤ 12 / a0 * (3 * κ ^ 2 / a0 + R j) := by gcongr
        _ = 36 * κ ^ 2 / a0 ^ 2 + 12 * R j / a0 := by field_simp; ring
    have h7 : 36 * κ ^ 2 / a0 ^ 2 ≤ 144 * (a0 + 2) ^ 2 / a0 ^ 2 * ε ^ 2 := by
      have : κ ^ 2 ≤ (2 * (a0 + 2) * ε) ^ 2 := pow_le_pow_left₀ hκ0 hκε 2
      calc 36 * κ ^ 2 / a0 ^ 2 ≤ 36 * (2 * (a0 + 2) * ε) ^ 2 / a0 ^ 2 := by gcongr
        _ = _ := by ring
    have h8 : x j ^ 2 ≤ (K * ε) ^ 2 := by
      have hc : 0 ≤ 144 * (a0 + 2) ^ 2 / a0 ^ 2 := by positivity
      calc x j ^ 2 ≤ 144 * (a0 + 2) ^ 2 / a0 ^ 2 * ε ^ 2 + ε ^ 2 := by linarith
        _ = K * ε ^ 2 := by simp only [hK]; ring
        _ ≤ K ^ 2 * ε ^ 2 := by gcongr; nlinarith
        _ = (K * ε) ^ 2 := by ring
    have h9 : x j ≤ K * ε := by
      by_contra hcon
      replace hcon := not_le.1 hcon
      nlinarith [hx j, mul_pos (by linarith : (0 : ℝ) < K) hε0]
    calc x j ≤ K * ε := h9
      _ ≤ (K + 1) * ε := by nlinarith
      _ ≤ a / 2 := hεa
      _ < a := by linarith
  refine ⟨hx0, ?_⟩
  have hub : Tendsto (fun j => 4 * (a0 + 1) * (x j + 2 * |hh j|) + 2 * L j ^ 2) atTop (𝓝 0) := by
    have : Tendsto (fun j => 4 * (a0 + 1) * (x j + 2 * |hh j|) + 2 * L j ^ 2) atTop
        (𝓝 (4 * (a0 + 1) * (0 + 2 * 0) + 2 * 0)) :=
      (((hx0.add (hhabs.const_mul 2)).const_mul _).add (hL2.const_mul 2))
    simpa using this
  refine squeeze_zero' (Eventually.of_forall hI0) ?_ hub
  filter_upwards [hq 1 one_pos] with j hj
  have h2 := hJ j 1 one_pos
  obtain ⟨hHp, hHb⟩ := hHh j
  have h3 : J j ≤ 2 * (a0 + 1) * (x j + 2 * |hh j|) := hj.trans (by gcongr)
  norm_num at h2
  nlinarith

/-- Trial upper bound: for every `ε > 0`, eventually the optimal quotient is below `a0 + ε`. -/
theorem str025a_trial {h : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0))
    (ρ : ℕ → AbsoluteDensity 1)
    (hpos : ∀ j, 0 < ordinaryEntropy (h j) (ρ j))
    (hmin : ∀ j, ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy (h j) ρ' →
      ordinaryFisher (h j) (ρ j) / (2 * ordinaryEntropy (h j) (ρ j)) ≤
        ordinaryFisher (h j) ρ' / (2 * ordinaryEntropy (h j) ρ'))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, (ordinaryFisher (h j) (ρ j)).toReal ≤
      2 * (4 * Real.pi ^ 2 + ε) * (ordinaryEntropy (h j) (ρ j)).toReal := by
  set a0 : ℝ := 4 * Real.pi ^ 2 with ha0
  have ha0p : 0 < a0 := by positivity
  -- a trial below the sharp constant
  have hnot : ¬ ∀ ρ' : AbsoluteDensity 1,
      2 * (a0 + ε / 2) * DGPS.Analysis.circleEntropy ρ' ≤
        DGPS.Analysis.circleFisherInformation ρ' := fun hall =>
    absurd (DGPS.haar_circle_lsi_sharp hall) (by linarith)
  obtain ⟨ρ', hρ'⟩ := not_forall.1 hnot
  replace hρ' := not_le.1 hρ'
  set T := DGPS.Analysis.circleFisherInformation ρ' with hT
  set E := DGPS.Analysis.circleEntropy ρ' with hE
  have hT0 : 0 ≤ T := circleFisherInformation_nonneg ρ'
  have hEp : 0 < E := by
    by_contra hc
    have : E ≤ 0 := not_lt.1 hc
    nlinarith [circleEntropy_nonneg ρ']
  set r : ℝ := T / (2 * E) with hr
  have hr0 : 0 ≤ r := by positivity
  have hrlt : r < a0 + ε / 2 := by
    rw [hr, div_lt_iff₀ (by positivity)]; linarith
  set η : ℝ := ε / (2 * (a0 + ε / 2 + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hηr : η * r < ε / 2 := by
    have : η * r ≤ η * (a0 + ε / 2) := by gcongr
    refine this.trans_lt ?_
    rw [hη, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hlim : (1 + η) * r < a0 + ε := by linarith
  set Q : ℕ → ℝ := fun j => ((1 + η) * T + (1 + 1 / η) * logGradBound (h j) ^ 2) /
      (2 * (E - 2 * |h j|)) with hQ
  have hL0 : Tendsto (fun j => logGradBound (h j)) atTop (𝓝 0) := by
    have hc : Continuous logGradBound := by unfold logGradBound; fun_prop
    have := (hc.tendsto 0).comp hh
    have e : logGradBound 0 = 0 := by simp [logGradBound]
    rw [e] at this
    exact this
  have hQt : Tendsto Q atTop (𝓝 (((1 + η) * T + (1 + 1 / η) * 0 ^ 2) / (2 * (E - 2 * |0|)))) := by
    refine Tendsto.div ?_ ?_ (by simp; exact hEp.ne')
    · exact tendsto_const_nhds.add ((hL0.pow 2).const_mul _)
    · exact tendsto_const_nhds.mul (tendsto_const_nhds.sub ((hh.abs).const_mul 2))
  have hQlim : ((1 + η) * T + (1 + 1 / η) * 0 ^ 2) / (2 * (E - 2 * |(0 : ℝ)|)) = (1 + η) * r := by
    rw [hr]; simp; field_simp
  rw [hQlim] at hQt
  have hhEv : ∀ᶠ j in atTop, 2 * |h j| < E := by
    have := hh.abs.const_mul 2
    simp only [abs_zero, mul_zero] at this
    exact this.eventually (gt_mem_nhds hEp)
  filter_upwards [hQt.eventually (gt_mem_nhds hlim), hhEv] with j hQj hhj
  -- real-variable data for the trial at `h j`
  obtain ⟨y', hy'e, hy'⟩ := str025a_entropy_real (h j) ρ'
  have hy'p : E - 2 * |h j| ≤ y' := by
    have := (abs_le.1 hy').1; linarith
  have hy'pos : 0 < y' := by linarith
  have hH'pos : 0 < ordinaryEntropy (h j) ρ' := by rw [hy'e]; exact ENNReal.ofReal_pos.2 hy'pos
  have hH'real : (ordinaryEntropy (h j) ρ').toReal = y' := by
    rw [hy'e, ENNReal.toReal_ofReal hy'pos.le]
  have hmin' := hmin j ρ' hH'pos
  have hne1 : ordinaryFisher (h j) ρ' ≠ ⊤ := str025_fisher_ne_top _ _
  have hne2 : 2 * ordinaryEntropy (h j) ρ' ≠ 0 := by
    have := hH'pos.ne'; simpa using this
  have hne3 : 2 * ordinaryEntropy (h j) ρ' ≠ ⊤ := ENNReal.mul_ne_top (by simp) (str025_entropy_ne_top _ _)
  have hfin : ordinaryFisher (h j) ρ' / (2 * ordinaryEntropy (h j) ρ') ≠ ⊤ :=
    (ENNReal.div_lt_top hne1 hne2).ne
  have hreal := ENNReal.toReal_mono hfin hmin'
  rw [ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_mul,
    hH'real] at hreal
  simp only [ENNReal.toReal_ofNat] at hreal
  -- the optimizer's data
  have hHjpos : 0 < (ordinaryEntropy (h j) (ρ j)).toReal :=
    ENNReal.toReal_pos (hpos j).ne' (str025_entropy_ne_top _ _)
  have hJ' := (str025a_fisher_cmp (h j) ρ' hη0).1
  rw [← hT] at hJ'
  have hJ'0 : 0 ≤ (ordinaryFisher (h j) ρ').toReal := ENNReal.toReal_nonneg
  have hden : 0 < 2 * (E - 2 * |h j|) := by linarith
  have hQ1 : (ordinaryFisher (h j) ρ').toReal / (2 * y') ≤ Q j := by
    rw [hQ]
    calc (ordinaryFisher (h j) ρ').toReal / (2 * y') ≤
          ((1 + η) * T + (1 + 1 / η) * logGradBound (h j) ^ 2) / (2 * y') :=
          div_le_div_of_nonneg_right hJ' (by linarith)
      _ ≤ _ := by
          apply div_le_div_of_nonneg_left (by positivity) hden (by linarith)
  have hQ2 : (ordinaryFisher (h j) (ρ j)).toReal / (2 * (ordinaryEntropy (h j) (ρ j)).toReal) ≤
      a0 + ε := by linarith
  rw [div_le_iff₀ (by positivity)] at hQ2
  linarith

/-- STR025, `H¹` part of the global localization: for `h_j → 0` and any global minimizers `ρ_j`
of the ordinary quotient `I(ρ|μ_{h_j}) / (2 H(ρ|μ_{h_j}))` over positive-entropy densities,
`√ρ_j → 1` in `H¹(m)`: `‖√ρ_j − 1‖²_{L²} → 0` and `‖∇√ρ_j‖²_{L²} → 0` (the weak gradient of the
constant `1` is `0`, so these are the two components of `‖√ρ_j − 1‖²_{H¹}`). -/
theorem ordinaryOptimizer_globalLocalization_H1 (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (ρ : ℕ → AbsoluteDensity 1)
    (hpos : ∀ j, 0 < ordinaryEntropy (h j) (ρ j))
    (hmin : ∀ j, ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy (h j) ρ' →
      ordinaryFisher (h j) (ρ j) / (2 * ordinaryEntropy (h j) (ρ j)) ≤
        ordinaryFisher (h j) ρ' / (2 * ordinaryEntropy (h j) ρ')) :
    Tendsto (fun j => ∫ x, ((ρ j).sqrt x - 1) ^ 2 ∂haar 1) atTop (𝓝 0) ∧
    Tendsto (fun j => ∫ x, ‖weakGradient (ρ j).sqrt (ρ j).sqrt_mem x‖ ^ 2 ∂haar 1)
      atTop (𝓝 0) := by
  have ha0 : 0 < 4 * Real.pi ^ 2 := by positivity
  have hL0 : Tendsto (fun j => logGradBound (h j)) atTop (𝓝 0) := by
    have hc : Continuous logGradBound := by unfold logGradBound; fun_prop
    have := (hc.tendsto 0).comp hh
    have e : logGradBound 0 = 0 := by simp [logGradBound]
    rw [e] at this
    exact this
  obtain ⟨hx0, hI0⟩ := str025a_core (a0 := 4 * Real.pi ^ 2) ha0
    (x := fun j => DGPS.Analysis.circleEntropy (ρ j))
    (I := fun j => DGPS.Analysis.circleFisherInformation (ρ j))
    (J := fun j => (ordinaryFisher (h j) (ρ j)).toReal)
    (L := fun j => logGradBound (h j)) (hh := h)
    (Hh := fun j => (ordinaryEntropy (h j) (ρ j)).toReal)
    (fun j => circleEntropy_nonneg (ρ j))
    (fun j => by
      rcases (circleEntropy_nonneg (ρ j)).eq_or_lt with h0 | h0
      · rw [← h0]; simpa using circleFisherInformation_nonneg (ρ j)
      · have := (haarLSI_strict_positiveEntropy (ρ j) h0).1
        linarith)
    (fun j => circleFisherInformation_nonneg (ρ j))
    (fun j η hη => (str025a_fisher_cmp (h j) (ρ j) hη).2)
    (fun j => by
      refine ⟨ENNReal.toReal_pos (hpos j).ne' (str025_entropy_ne_top _ _), ?_⟩
      obtain ⟨y, hy, hyb⟩ := str025a_entropy_real (h j) (ρ j)
      have hy0 : 0 < y := by
        have := hpos j
        rw [hy] at this
        exact ENNReal.ofReal_pos.1 this
      rw [hy, ENNReal.toReal_ofReal hy0.le]
      have := (abs_le.1 hyb).2
      linarith)
    (fun ε hε => str025a_trial hh ρ hpos hmin hε) hL0 hh
  refine ⟨?_, ?_⟩
  · refine squeeze_zero (fun j => integral_nonneg fun x => sq_nonneg _)
      (fun j => str025a_hellinger_le (ρ j)) hx0
  · have : Tendsto (fun j => DGPS.Analysis.circleFisherInformation (ρ j) / 4) atTop (𝓝 0) := by
      simpa using hI0.div_const 4
    refine this.congr fun j => ?_
    rw [circleFisher_eq_four_mul]
    ring

end DGPS.Examples.ThreeSpeciesCircle
