import SharpSymmetricLSI.Paper.GaussLSI5
import FullLabeledLSI.Paper.Sec8Fourier11

/-!
# Section 8.3 (linearization), part 1: the dissipation along `p (1 + t h)` for Lipschitz `g = h + T h`

A copy of `dissipation_pert` / `tendsto_diss_pert` (symmetric project, `GaussLSI5`) in which the
`C¹` function `g = h + T h` with gradient `cgrad g` is replaced by a function `g` with a bounded
measurable weak gradient `gg` (a Lipschitz function and `lipGrad g`).
-/

noncomputable section
open MeasureTheory Filter Topology Finset Real

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-! ### The dissipation -/

section diss
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
include hyp hμ

/-- The integrand `|∇g + t h b_{ph}|² / (1 + t h)`. -/
def dissIntG (W : Torus d → Torus d → ℝ) (p h : Torus d → ℝ) (gg : Torus d → Fin d → ℝ) (t : ℝ)
    (x : Torus d) : ℝ :=
  (∑ k, (gg x k + t * h x * bForceL W (fun y => p y * h y) x k) ^ 2) / (1 + t * h x)

omit hμ in
theorem dissIntG_bounds {p h : Torus d → ℝ} {gg : Torus d → Fin d → ℝ} (hpi : Integrable p (haar d))
    (hc : Continuous h) {Kg : ℝ} (hgb : ∀ x k, |gg x k| ≤ Kg) (hgm : ∀ k, Measurable fun x => gg x k)
    {B : ℝ} (hB' : ∀ x, |h x| ≤ B) :
    ∃ K, ∀ t, |t| * (B + 2) ≤ 1 / 2 → Measurable (dissIntG W p h gg t) ∧
      ∀ x, 0 ≤ dissIntG W p h gg t x ∧ dissIntG W p h gg t x ≤ K := by
  have hphi := integrable_mul_cont hpi hc
  obtain ⟨Cb, hCb0, hbF⟩ := abs_bForceL_le_int hyp hphi
  set Bp := Cb * ∫ y, |p y * h y| ∂haar d
  set A := |Kg| + Bp / 2
  refine ⟨2 * (Fintype.card (Fin d) * A ^ 2), fun t ht => ⟨?_, fun x => ?_⟩⟩
  · exact (Finset.measurable_sum _ fun k _ => ((hgm k).add
      ((measurable_const.mul hc.measurable).mul (measurable_bForceL' hyp hphi k))).pow_const 2).div
      (measurable_const.add (measurable_const.mul hc.measurable))
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB' 0)
  have hth : |t * h x| ≤ 1 / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hB' x) (abs_nonneg t)).trans
      ((mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)).trans ht)
  have hpos : 1 / 2 ≤ 1 + t * h x := by linarith [(abs_le.mp hth).1]
  have hBp : 0 ≤ Bp := mul_nonneg hCb0 (integral_nonneg fun _ => abs_nonneg _)
  have hak : ∀ k, |gg x k + t * h x * bForceL W (fun y => p y * h y) x k| ≤ A := fun k => by
    refine (abs_add_le _ _).trans (add_le_add ((hgb x k).trans (le_abs_self _)) ?_)
    rw [abs_mul]
    calc |t * h x| * |bForceL W (fun y => p y * h y) x k| ≤ 1 / 2 * Bp :=
          mul_le_mul hth (hbF x k) (abs_nonneg _) (by norm_num)
      _ = Bp / 2 := by ring
  have hS : ∑ k, (gg x k + t * h x * bForceL W (fun y => p y * h y) x k) ^ 2 ≤
      Fintype.card (Fin d) * A ^ 2 := by
    calc _ ≤ ∑ _k : Fin d, A ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hak k) 2
      _ = _ := by simp
  have hS0 : 0 ≤ ∑ k, (gg x k + t * h x * bForceL W (fun y => p y * h y) x k) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨div_nonneg hS0 (by linarith), ?_⟩
  unfold dissIntG
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg (Fintype.card (Fin d)) : (0 : ℝ) ≤ _)
    (sq_nonneg A)) (by linarith : (0 : ℝ) ≤ 1 + t * h x - 1 / 2)]

/-- **`D(p(1+th)) = t² ∫ |∇g + t h b_{ph}|²/(1+th) dμ`.** -/
theorem dissipation_pertG {h g : Torus d → ℝ} {gg : Torus d → Fin d → ℝ} (hc : Continuous h)
    (hgw : IsWeakGrad g gg) {Kg : ℝ} (hgb : ∀ x k, |gg x k| ≤ Kg)
    (hgm : ∀ k, Measurable fun x => gg x k)
    (hsum : ∀ x, h x + Top W (μ : Measure (Torus d)) h x = g x) {B : ℝ} (hB' : ∀ x, |h x| ≤ B)
    {t : ℝ} (ht : |t| * (B + 2) ≤ 1 / 2) :
    dissipation V W (fun x => elDens V W (μ : Measure (Torus d)) x * (1 + t * h x)) =
      ENNReal.ofReal (t ^ 2 * ∫ x, dissIntG W (elDens V W (μ : Measure (Torus d))) h gg t x
        ∂(μ : Measure (Torus d))) := by
  set μm := (μ : Measure (Torus d))
  set p := elDens V W μm with hp
  obtain ⟨hpm, hp0, hp1⟩ := elDensity_props hyp μm
  have hpi : Integrable p (haar d) := integrable_of_integral_eq_one' hp1
  obtain ⟨cl, Cu, Lp, hcl, hbd⟩ := elDensity_bounds hyp
  obtain ⟨hpb, hpL⟩ := hbd μm inferInstance
  have hpc : Continuous p := hpL.continuous
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB' 0)
  have hth : ∀ x, |t * h x| ≤ 1 / 2 := fun x => by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hB' x) (abs_nonneg t)).trans
      ((mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)).trans ht)
  have hpos : ∀ x, 1 / 2 ≤ 1 + t * h x := fun x => by linarith [(abs_le.mp (hth x)).1]
  have hup : ∀ x, 1 + t * h x ≤ 3 / 2 := fun x => by linarith [(abs_le.mp (hth x)).2]
  set ph : Torus d → ℝ := fun y => p y * h y with hph
  have hphi : Integrable ph (haar d) := integrable_mul_cont hpi hc
  obtain ⟨Cb, hCb0, hbF⟩ := abs_bForceL_le_int hyp hphi
  obtain ⟨Cbp, hCbp0, hbFp⟩ := abs_bForceL_le_int hyp hpi
  set r : Torus d → ℝ := fun x => p x * (1 + t * h x) with hr
  have hr0 : ∀ x, 0 < r x := fun x => mul_pos (hp0 x) (by linarith [hpos x])
  have hrc : Continuous r := hpc.mul (continuous_const.add (continuous_const.mul hc))
  have hri : Integrable r (haar d) := integrable_of_continuous hrc
  have hreq : r = fun y => 1 * p y + t * ph y := by funext y; simp only [hr, hph]; ring
  -- `log p`
  set Z := ∫ y, Real.exp (-V y - convMeas W μm y) ∂haar d with hZ
  have hZ0 : 0 < Z := by
    have := hp0 (Classical.arbitrary _)
    simp only [hp, elDens] at this
    exact (div_pos_iff.mp this).elim (fun h => h.2) fun h => absurd h.1 (not_lt.mpr (exp_pos _).le)
  have hlogp : ∀ x, Real.log (p x) = -V x - convDens W p x - Real.log Z := fun x => by
    have hc' : convMeas W μm x = convDens W p x := by
      unfold convMeas
      rw [integral_minimizer hyp hμ]
      unfold convDens
      congr 1; funext y; ring
    simp only [hp, elDens]
    rw [Real.log_div (exp_pos _).ne' hZ0.ne', Real.log_exp, hc']
  -- the weak gradient of `h`
  obtain ⟨Kh, hKh⟩ := Top_eq_convDens hyp hμ h
  have hheq : ∀ x, h x = g x + (-1) * convDens W ph x + Kh := fun x => by
    have := hsum x; rw [hKh x] at this; simp only [hph]; linarith
  set gh : Torus d → Fin d → ℝ := fun x k => gg x k - bForceL W ph x k with hgh
  have hhw : IsWeakGrad h gh := by
    have := (hgw.add ((isWeakGrad_convDens' hyp hphi).cmul (-1))).add
      (isWeakGrad_const Kh)
    convert this using 1
    · funext x; exact hheq x
    · funext x k; simp only [hgh, Pi.zero_apply]; ring
  set Bph := Cb * ∫ y, |ph y| ∂haar d
  have hghb : ∀ x k, |gh x k| ≤ Kg + Bph := fun x k =>
    (abs_sub _ _).trans (add_le_add (hgb x k) (hbF x k))
  have hghm : ∀ k, Measurable fun x => gh x k := fun k =>
    (hgm k).sub (measurable_bForceL' hyp hphi k)
  -- `log(1 + t h)`
  obtain ⟨Lc, hLc⟩ := deriv_logCut_bdd hB0 ht
  have hl := isWeakGrad_comp hhw (integrable_of_continuous hc)
    (fun k => integrable_of_bdd (hghm k) fun x => hghb x k) (contDiff_logCut hB0 ht) hLc
  have hderiv : ∀ x, deriv (logCut B hB0 t) (h x) = t / (1 + t * h x) := fun x =>
    deriv_logCut hB0 ht (hB' x)
  -- `F = log r`
  have hV := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp)
  have hCp := isWeakGrad_convDens' hyp hpi
  set F : Torus d → ℝ := fun x => -V x - convDens W p x - Real.log Z + logCut B hB0 t (h x)
    with hF
  set GF : Torus d → Fin d → ℝ := fun x k =>
    -lipGrad V x k - bForceL W p x k + deriv (logCut B hB0 t) (h x) * gh x k with hGF
  have hFw : IsWeakGrad F GF := by
    have := (((hV.cmul (-1)).add (hCp.cmul (-1))).add (isWeakGrad_const (-Real.log Z))).add hl
    convert this using 1
    · funext x; simp only [hF]; ring
    · funext x k; simp only [hGF, Pi.zero_apply]; ring
  have hFeq : ∀ x, F x = Real.log (r x) := fun x => by
    simp only [hF, hr]
    rw [Real.log_mul (hp0 x).ne' (by linarith [hpos x]), hlogp x, logCut_eq hB0 ht (hB' x)]
  have hFc : Continuous F := by
    rw [show F = fun x => Real.log (r x) from funext hFeq]; exact hrc.log fun x => (hr0 x).ne'
  set M := |Real.log (cl / 2)| + |Real.log (Cu * (3 / 2))| with hM
  have hM0 : 0 ≤ M := by positivity
  have hFM : ∀ x, |F x| ≤ M := fun x => by
    rw [hFeq]
    have hlo : cl / 2 ≤ r x := by
      have := mul_le_mul (hpb x).1 (hpos x) (by norm_num) (hp0 x).le
      simp only [hr]; linarith
    have hhi : r x ≤ Cu * (3 / 2) :=
      mul_le_mul (hpb x).2 (hup x) (by linarith [hpos x]) ((hp0 x).le.trans (hpb x).2)
    have h1 := Real.log_le_log (by positivity) hlo
    have h2 := Real.log_le_log (hr0 x) hhi
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (cl / 2)), abs_nonneg (Real.log (Cu * (3 / 2)))]
    · linarith [le_abs_self (Real.log (Cu * (3 / 2))), abs_nonneg (Real.log (cl / 2))]
  set LV : ℝ := (Real.toNNReal (KV * Fintype.card (Fin d) / 2) : ℝ)
  set Bp := Cbp * ∫ y, |p y| ∂haar d
  have hGFb : ∀ x k, |GF x k| ≤ LV + Bp + |Lc| * (Kg + Bph) := fun x k => by
    simp only [hGF]
    refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ (hbFp x k))) ?_)
    · rw [abs_neg]; exact abs_lipGrad_le (lipschitz_V hyp) x k
    · rw [abs_mul]
      exact mul_le_mul ((hLc _).trans (le_abs_self _)) (hghb x k) (abs_nonneg _) (abs_nonneg _)
  have hGFm : ∀ k, Measurable fun x => GF x k := fun k =>
    (((measurable_lipGrad hyp.continuous_V k).neg).sub (measurable_bForceL' hyp hpi k)).add
      ((((contDiff_logCut hB0 ht).continuous_deriv le_rfl).measurable.comp hc.measurable).mul
        (hghm k))
  have hFi : Integrable F volume := integrable_of_continuous hFc
  have hGi : ∀ k, Integrable (fun x => GF x k) volume := fun k =>
    integrable_of_bdd (hGFm k) fun x => hGFb x k
  obtain ⟨Le, hLe⟩ := deriv_expCut_bdd M hM0
  have hS0 := isWeakGrad_comp hFw hFi hGi ((contDiff_expCut M hM0).of_le (by simp)) hLe
  have hsqrt : ∀ x, Real.exp (F x / 2) = Real.sqrt (r x) := fun x => by
    rw [hFeq, ← Real.log_sqrt (hr0 x).le, Real.exp_log (Real.sqrt_pos.mpr (hr0 x))]
  have hS : IsWeakGrad (fun x => Real.sqrt (r x))
      (fun x k => Real.sqrt (r x) / 2 * GF x k) := by
    convert hS0 using 1
    · funext x; rw [expCut_eq hM0 (hFM x), hsqrt]
    · funext x k; rw [deriv_expCut hM0 (hFM x), hsqrt]
  have hVW : IsWeakGrad (fun x => V x + convDens W r x)
      (fun x k => lipGrad V x k + bForceL W r x k) := hV.add (isWeakGrad_convDens' hyp hri)
  -- `√r ∈ H¹`
  set Rs := Real.sqrt (Cu * (3 / 2))
  have hsqb : ∀ x, Real.sqrt (r x) ≤ Rs := fun x => Real.sqrt_le_sqrt
    (mul_le_mul (hpb x).2 (hup x) (by linarith [hpos x]) ((hp0 x).le.trans (hpb x).2))
  set BG := LV + Bp + |Lc| * (Kg + Bph)
  have hGSb : ∀ x k, |Real.sqrt (r x) / 2 * GF x k| ≤ Rs / 2 * BG := fun x k => by
    rw [abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg _), abs_two]
    exact mul_le_mul (div_le_div_of_nonneg_right (hsqb x) (by norm_num)) (hGFb x k)
      (abs_nonneg _) (by positivity)
  have hGSm : ∀ k, Measurable fun x => Real.sqrt (r x) / 2 * GF x k := fun k =>
    ((hrc.measurable.sqrt).div_const 2).mul (hGFm k)
  have hH1 : MemH1 (haar d) (fun x => Real.sqrt (r x)) := by
    refine ⟨⟨_, hS⟩, ?_, ?_⟩
    · exact MemLp.of_bound hrc.sqrt.aestronglyMeasurable Rs (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]; exact hsqb x)
    · have hm : MemLp (fun x => Real.sqrt (sqNorm (fun k => Real.sqrt (r x) / 2 * GF x k))) 2
          (haar d) := by
        refine MemLp.of_bound ?_ (Real.sqrt (Fintype.card (Fin d) * (Rs / 2 * BG) ^ 2))
          (Eventually.of_forall fun x => ?_)
        · exact (Measurable.sqrt (Finset.measurable_sum _ fun k _ => (hGSm k).pow_const 2)
            ).aestronglyMeasurable
        · rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
          refine Real.sqrt_le_sqrt ?_
          unfold sqNorm
          calc ∑ k, (Real.sqrt (r x) / 2 * GF x k) ^ 2 ≤ ∑ _k : Fin d, (Rs / 2 * BG) ^ 2 :=
                Finset.sum_le_sum fun k _ => by
                  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hGSb x k) 2
            _ = _ := by simp
      refine hm.ae_eq ?_
      filter_upwards [weakGrad_ae_eq hS] with x hx
      rw [hx]
  -- the pointwise identity
  have hbr : ∀ x k, bForceL W r x k = bForceL W p x k + t * bForceL W ph x k := fun x k => by
    rw [hreq, bForceL_add hyp hpi hphi 1 t x k]; ring
  have hpt : ∀ x, ∑ k, (2 * (Real.sqrt (r x) / 2 * GF x k) +
      Real.sqrt (r x) * (lipGrad V x k + bForceL W r x k)) ^ 2 =
        t ^ 2 * (p x * dissIntG W p h gg t x) := fun x => by
    have hne : 1 + t * h x ≠ 0 := by linarith [hpos x]
    have e : ∀ k, 2 * (Real.sqrt (r x) / 2 * GF x k) +
        Real.sqrt (r x) * (lipGrad V x k + bForceL W r x k) =
        Real.sqrt (r x) * (t * (gg x k + t * h x * bForceL W ph x k) / (1 + t * h x)) :=
      fun k => by
        simp only [hGF, hgh, hbr, hderiv]
        field_simp
        ring
    calc ∑ k, (2 * (Real.sqrt (r x) / 2 * GF x k) +
          Real.sqrt (r x) * (lipGrad V x k + bForceL W r x k)) ^ 2
        = ∑ k, (r x * t ^ 2 / (1 + t * h x) ^ 2) *
            (gg x k + t * h x * bForceL W ph x k) ^ 2 :=
          Finset.sum_congr rfl fun k _ => by
            rw [e k, mul_pow, Real.sq_sqrt (hr0 x).le, div_pow, mul_pow]; ring
      _ = t ^ 2 * (p x * dissIntG W p h gg t x) := by
          rw [← Finset.mul_sum]
          simp only [hr, dissIntG, hph]
          field_simp
  -- the integral
  obtain ⟨K, hK⟩ := dissIntG_bounds hyp (W := W) hpi hc hgb hgm hB'
  obtain ⟨hKm, hKb⟩ := hK t ht
  have hint : Integrable (fun x => t ^ 2 * (p x * dissIntG W p h gg t x)) (haar d) := by
    refine (integrable_of_bdd (hpm.mul hKm) (C := Cu * K) fun x => ?_).const_mul _
    rw [Pi.mul_apply, abs_mul, abs_of_nonneg (hp0 x).le, abs_of_nonneg (hKb x).1]
    exact mul_le_mul (hpb x).2 (hKb x).2 (hKb x).1 ((hp0 x).le.trans (hpb x).2)
  unfold dissipation
  rw [if_pos ⟨hH1, ⟨_, hVW⟩⟩]
  calc ∫⁻ x, ENNReal.ofReal (∑ k, (2 * weakGrad (fun y => Real.sqrt (r y)) x k +
        Real.sqrt (r x) * weakGrad (fun y => V y + convDens W r y) x k) ^ 2) ∂haar d
      = ∫⁻ x, ENNReal.ofReal (t ^ 2 * (p x * dissIntG W p h gg t x)) ∂haar d := by
        refine lintegral_congr_ae ?_
        filter_upwards [weakGrad_ae_eq hS, weakGrad_ae_eq hVW] with x h1 h2
        rw [h1, h2, hpt x]
    _ = ENNReal.ofReal (∫ x, t ^ 2 * (p x * dissIntG W p h gg t x) ∂haar d) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x =>
          mul_nonneg (sq_nonneg _) (mul_nonneg (hp0 x).le (hKb x).1))).symm
    _ = _ := by
        rw [integral_const_mul, integral_minimizer hyp hμ]

/-- **`D(ρ_t)/t² → ∫ |∇g|² dμ`** (dominated convergence, uniformly bounded integrands). -/
theorem tendsto_diss_pertG {h : Torus d → ℝ} {gg : Torus d → Fin d → ℝ} (hc : Continuous h)
    {Kg : ℝ} (hgb : ∀ x k, |gg x k| ≤ Kg) (hgm : ∀ k, Measurable fun x => gg x k)
    {B : ℝ} (hB' : ∀ x, |h x| ≤ B) :
    Tendsto (fun t => ∫ x, dissIntG W (elDens V W (μ : Measure (Torus d))) h gg t x
        ∂(μ : Measure (Torus d))) (𝓝 0)
      (𝓝 (∫ x, ∑ k, gg x k ^ 2 ∂(μ : Measure (Torus d)))) := by
  set μm := (μ : Measure (Torus d))
  set p := elDens V W μm
  obtain ⟨-, -, hp1⟩ := elDensity_props hyp μm
  have hpi : Integrable p (haar d) := integrable_of_integral_eq_one' hp1
  obtain ⟨K, hK⟩ := dissIntG_bounds hyp (W := W) hpi hc hgb hgm hB'
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), |t| * (B + 2) ≤ 1 / 2 := by
    have : Tendsto (fun t : ℝ => |t| * (B + 2)) (𝓝 0) (𝓝 0) := by
      exact (continuous_abs.mul continuous_const : Continuous fun t : ℝ => |t| * (B + 2)).tendsto' 0 0
        (by simp)
    exact this.eventually (ge_mem_nhds (by norm_num))
  have hlim : ∀ x, Tendsto (fun t => dissIntG W p h gg t x) (𝓝 0) (𝓝 (∑ k, gg x k ^ 2)) :=
    fun x => by
      have : ContinuousAt (fun t : ℝ => dissIntG W p h gg t x) 0 := by
        unfold dissIntG
        exact (continuous_finsetSum _ fun k _ => (continuous_const.add
          ((continuous_id.mul continuous_const).mul continuous_const)).pow 2).continuousAt.div
          (continuous_const.add (continuous_id.mul continuous_const)).continuousAt (by simp)
      simpa [dissIntG] using this.tendsto
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => K) ?_ ?_ (integrable_const K)
    (Eventually.of_forall hlim)
  · filter_upwards [hsmall] with t ht
    exact (hK t ht).1.aestronglyMeasurable
  · filter_upwards [hsmall] with t ht
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((hK t ht).2 x).1]; exact ((hK t ht).2 x).2

end diss

end SharpLSI
