import SharpSymmetricLSI.Paper.GaussLSI4
import SharpSymmetricLSI.Paper.LyapSchmidt11
import SharpSymmetricLSI.Paper.NBody2

/-!
# (8.13) (lane s42), step 3: the dissipation along the test perturbation

Let `μ = p m` be a minimizer, `h` continuous with `|h| ≤ B` and `h + T h = g`, `g ∈ C¹`.
For `ρ_t = p (1 + t h)` and `|t| (B + 2) ≤ 1/2`:
`log ρ_t + V + W*ρ_t = const + log(1 + t h) + t T h`, so (weak gradients, with
`∇(T h) = b_{ph} = ∇(W * (p h))` and `∇h = ∇g - b_{ph}`)
`2∇√ρ_t + √ρ_t ∇(V + W*ρ_t) = t √ρ_t (∇g + t h b_{ph}) / (1 + t h)`, hence
`D(ρ_t) = t² ∫ |∇g + t h b_{ph}|² / (1 + t h) dμ` (`dissipation_pert`), and
`D(ρ_t)/t² → ∫ |∇g|² dμ` by dominated convergence (`tendsto_diss_pert`); the bound is uniform
in small `t` because `b_{ph}` is bounded everywhere.
-/

noncomputable section
open MeasureTheory Filter Topology Finset Real

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-! ### A smooth cutoff of `s ↦ log(1 + t s)` -/

/-- The bump `1` on `[-B-1, B+1]`, `0` off `(-B-2, B+2)`. -/
def bumpB (B : ℝ) (hB : 0 ≤ B) : ContDiffBump (0 : ℝ) := ⟨B + 1, B + 2, by linarith, by linarith⟩

/-- `log(1 + t s bump(s))`, equal to `log(1 + t s)` near `[-B, B]`. -/
def logCut (B : ℝ) (hB : 0 ≤ B) (t s : ℝ) : ℝ := Real.log (1 + t * (s * bumpB B hB s))

theorem abs_mul_bumpB_le (B : ℝ) (hB : 0 ≤ B) (s : ℝ) : |s * bumpB B hB s| ≤ B + 2 := by
  by_cases hs : |s| ≤ B + 2
  · rw [abs_mul, abs_of_nonneg ((bumpB B hB).nonneg)]
    calc |s| * bumpB B hB s ≤ |s| * 1 :=
          mul_le_mul_of_nonneg_left (bumpB B hB).le_one (abs_nonneg _)
      _ ≤ B + 2 := by rw [mul_one]; exact hs
  · rw [(bumpB B hB).zero_of_le_dist (by
      rw [Real.dist_eq, sub_zero]; exact (not_le.mp hs).le), mul_zero, abs_zero]
    linarith

section cut
variable {B : ℝ} (hB : 0 ≤ B) {t : ℝ} (ht : |t| * (B + 2) ≤ 1 / 2)
include ht

theorem one_add_logCut_arg (s : ℝ) : 1 / 2 ≤ 1 + t * (s * bumpB B hB s) := by
  have h1 : |t * (s * bumpB B hB s)| ≤ 1 / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (abs_mul_bumpB_le B hB s) (abs_nonneg t)).trans ht
  linarith [(abs_le.mp h1).1]

theorem contDiff_logCut : ContDiff ℝ 1 (logCut B hB t) :=
  (contDiff_const.add (contDiff_const.mul (contDiff_id.mul (bumpB B hB).contDiff))).log
    fun s => by have := one_add_logCut_arg hB ht s; simp only [id]; linarith

theorem logCut_eventuallyEq {s : ℝ} (hs : |s| ≤ B) :
    logCut B hB t =ᶠ[𝓝 s] fun s => Real.log (1 + t * s) := by
  have hball : Metric.ball (0 : ℝ) (B + 1) ∈ 𝓝 s :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith)
  filter_upwards [hball] with s' hs'
  simp only [logCut]
  rw [(bumpB B hB).one_of_mem_closedBall (Metric.ball_subset_closedBall hs'), mul_one]

theorem logCut_eq {s : ℝ} (hs : |s| ≤ B) : logCut B hB t s = Real.log (1 + t * s) :=
  (logCut_eventuallyEq hB ht hs).eq_of_nhds

theorem deriv_logCut {s : ℝ} (hs : |s| ≤ B) : deriv (logCut B hB t) s = t / (1 + t * s) := by
  rw [(logCut_eventuallyEq hB ht hs).deriv_eq]
  have hpos : 0 < 1 + t * s := by
    have h1 : |t * s| ≤ 1 / 2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hs (abs_nonneg t)).trans
        ((mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)).trans ht)
    linarith [(abs_le.mp h1).1]
  have h : HasDerivAt (fun s : ℝ => Real.log (1 + t * s)) (t * 1 / (1 + t * s)) s :=
    (((hasDerivAt_id s).const_mul t).const_add 1).log hpos.ne'
  rw [h.deriv, mul_one]

theorem deriv_logCut_bdd : ∃ L, ∀ s, |deriv (logCut B hB t) s| ≤ L := by
  have hc : HasCompactSupport (logCut B hB t) := by
    refine (bumpB B hB).hasCompactSupport.mono' fun s hs => subset_tsupport _ ?_
    intro h0
    apply hs
    simp only [logCut, h0, mul_zero, add_zero, Real.log_one]
  obtain ⟨L, hL⟩ := hc.deriv.exists_bound_of_continuous
    ((contDiff_logCut hB ht).continuous_deriv le_rfl)
  exact ⟨L, fun s => by rw [← Real.norm_eq_abs]; exact hL s⟩

end cut

/-! ### The dissipation -/

section diss
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
include hyp hμ

/-- The integrand `|∇g + t h b_{ph}|² / (1 + t h)`. -/
def dissInt (W : Torus d → Torus d → ℝ) (p h g : Torus d → ℝ) (t : ℝ) (x : Torus d) : ℝ :=
  (∑ k, (cgrad g x k + t * h x * bForceL W (fun y => p y * h y) x k) ^ 2) / (1 + t * h x)

omit hyp hμ in
theorem integrable_mul_cont {p h : Torus d → ℝ} (hpi : Integrable p (haar d)) (hc : Continuous h) :
    Integrable (fun y => p y * h y) (haar d) := by
  obtain ⟨B, hB⟩ := exists_bound_of_continuous hc
  exact (hpi.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]; exact hB y)).congr (Eventually.of_forall fun y => mul_comm _ _)

omit hμ in
theorem abs_bForceL_le_int {u : Torus d → ℝ} (hu : Integrable u (haar d)) :
    ∃ Cb, 0 ≤ Cb ∧ ∀ x k, |bForceL W u x k| ≤ Cb * ∫ y, |u y| ∂haar d := by
  obtain ⟨Cb₀, hCb₀⟩ := bGrad_bdd hyp (W := W)
  refine ⟨max Cb₀ 0, le_max_right _ _, fun x k => ?_⟩
  unfold bForceL
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
    (hu.abs.const_mul _) (Eventually.of_forall fun y => ?_)
  show |bGrad W x y k * u y| ≤ max Cb₀ 0 * |u y|
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right ((hCb₀ x y k).trans (le_max_left _ _)) (abs_nonneg _)

omit hμ in
theorem dissInt_bounds {p h g : Torus d → ℝ} (hpi : Integrable p (haar d))
    (hc : Continuous h) (hg : ContDiff ℝ 1 (g ∘ liftT)) {B : ℝ} (hB' : ∀ x, |h x| ≤ B) :
    ∃ K, ∀ t, |t| * (B + 2) ≤ 1 / 2 → Measurable (dissInt W p h g t) ∧
      ∀ x, 0 ≤ dissInt W p h g t x ∧ dissInt W p h g t x ≤ K := by
  obtain ⟨Kg, hKg⟩ := exists_bound_cgrad hg
  have hphi := integrable_mul_cont hpi hc
  obtain ⟨Cb, hCb0, hbF⟩ := abs_bForceL_le_int hyp hphi
  set Bp := Cb * ∫ y, |p y * h y| ∂haar d
  set A := |Kg| + Bp / 2
  refine ⟨2 * (Fintype.card (Fin d) * A ^ 2), fun t ht => ⟨?_, fun x => ?_⟩⟩
  · exact (Finset.measurable_sum _ fun k _ => ((measurable_cgrad hg k).add
      ((measurable_const.mul hc.measurable).mul (measurable_bForceL' hyp hphi k))).pow_const 2).div
      (measurable_const.add (measurable_const.mul hc.measurable))
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB' 0)
  have hth : |t * h x| ≤ 1 / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hB' x) (abs_nonneg t)).trans
      ((mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)).trans ht)
  have hpos : 1 / 2 ≤ 1 + t * h x := by linarith [(abs_le.mp hth).1]
  have hBp : 0 ≤ Bp := mul_nonneg hCb0 (integral_nonneg fun _ => abs_nonneg _)
  have hak : ∀ k, |cgrad g x k + t * h x * bForceL W (fun y => p y * h y) x k| ≤ A := fun k => by
    refine (abs_add_le _ _).trans (add_le_add ((hKg x k).trans (le_abs_self _)) ?_)
    rw [abs_mul]
    calc |t * h x| * |bForceL W (fun y => p y * h y) x k| ≤ 1 / 2 * Bp :=
          mul_le_mul hth (hbF x k) (abs_nonneg _) (by norm_num)
      _ = Bp / 2 := by ring
  have hS : ∑ k, (cgrad g x k + t * h x * bForceL W (fun y => p y * h y) x k) ^ 2 ≤
      Fintype.card (Fin d) * A ^ 2 := by
    calc _ ≤ ∑ _k : Fin d, A ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hak k) 2
      _ = _ := by simp
  have hS0 : 0 ≤ ∑ k, (cgrad g x k + t * h x * bForceL W (fun y => p y * h y) x k) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨div_nonneg hS0 (by linarith), ?_⟩
  unfold dissInt
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg (Fintype.card (Fin d)) : (0 : ℝ) ≤ _)
    (sq_nonneg A)) (by linarith : (0 : ℝ) ≤ 1 + t * h x - 1 / 2)]

/-- **`D(p(1+th)) = t² ∫ |∇g + t h b_{ph}|²/(1+th) dμ`.** -/
theorem dissipation_pert {h g : Torus d → ℝ} (hc : Continuous h) (hg : ContDiff ℝ 1 (g ∘ liftT))
    (hsum : ∀ x, h x + Top W (μ : Measure (Torus d)) h x = g x) {B : ℝ} (hB' : ∀ x, |h x| ≤ B)
    {t : ℝ} (ht : |t| * (B + 2) ≤ 1 / 2) :
    dissipation V W (fun x => elDens V W (μ : Measure (Torus d)) x * (1 + t * h x)) =
      ENNReal.ofReal (t ^ 2 * ∫ x, dissInt W (elDens V W (μ : Measure (Torus d))) h g t x
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
  set gh : Torus d → Fin d → ℝ := fun x k => cgrad g x k - bForceL W ph x k with hgh
  have hhw : IsWeakGrad h gh := by
    have := ((isWeakGrad_of_contDiff hg).add ((isWeakGrad_convDens' hyp hphi).cmul (-1))).add
      (isWeakGrad_const Kh)
    convert this using 1
    · funext x; exact hheq x
    · funext x k; simp only [hgh, cgrad, Pi.zero_apply]; ring
  obtain ⟨Kg, hKg⟩ := exists_bound_cgrad hg
  set Bph := Cb * ∫ y, |ph y| ∂haar d
  have hghb : ∀ x k, |gh x k| ≤ Kg + Bph := fun x k =>
    (abs_sub _ _).trans (add_le_add (hKg x k) (hbF x k))
  have hghm : ∀ k, Measurable fun x => gh x k := fun k =>
    (measurable_cgrad hg k).sub (measurable_bForceL' hyp hphi k)
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
        t ^ 2 * (p x * dissInt W p h g t x) := fun x => by
    have hne : 1 + t * h x ≠ 0 := by linarith [hpos x]
    have e : ∀ k, 2 * (Real.sqrt (r x) / 2 * GF x k) +
        Real.sqrt (r x) * (lipGrad V x k + bForceL W r x k) =
        Real.sqrt (r x) * (t * (cgrad g x k + t * h x * bForceL W ph x k) / (1 + t * h x)) :=
      fun k => by
        simp only [hGF, hgh, hbr, hderiv]
        field_simp
        ring
    calc ∑ k, (2 * (Real.sqrt (r x) / 2 * GF x k) +
          Real.sqrt (r x) * (lipGrad V x k + bForceL W r x k)) ^ 2
        = ∑ k, (r x * t ^ 2 / (1 + t * h x) ^ 2) *
            (cgrad g x k + t * h x * bForceL W ph x k) ^ 2 :=
          Finset.sum_congr rfl fun k _ => by
            rw [e k, mul_pow, Real.sq_sqrt (hr0 x).le, div_pow, mul_pow]; ring
      _ = t ^ 2 * (p x * dissInt W p h g t x) := by
          rw [← Finset.mul_sum]
          simp only [hr, dissInt, hph]
          field_simp
  -- the integral
  obtain ⟨K, hK⟩ := dissInt_bounds hyp (W := W) hpi hc hg hB'
  obtain ⟨hKm, hKb⟩ := hK t ht
  have hint : Integrable (fun x => t ^ 2 * (p x * dissInt W p h g t x)) (haar d) := by
    refine (integrable_of_bdd (hpm.mul hKm) (C := Cu * K) fun x => ?_).const_mul _
    rw [Pi.mul_apply, abs_mul, abs_of_nonneg (hp0 x).le, abs_of_nonneg (hKb x).1]
    exact mul_le_mul (hpb x).2 (hKb x).2 (hKb x).1 ((hp0 x).le.trans (hpb x).2)
  unfold dissipation
  rw [if_pos ⟨hH1, ⟨_, hVW⟩⟩]
  calc ∫⁻ x, ENNReal.ofReal (∑ k, (2 * weakGrad (fun y => Real.sqrt (r y)) x k +
        Real.sqrt (r x) * weakGrad (fun y => V y + convDens W r y) x k) ^ 2) ∂haar d
      = ∫⁻ x, ENNReal.ofReal (t ^ 2 * (p x * dissInt W p h g t x)) ∂haar d := by
        refine lintegral_congr_ae ?_
        filter_upwards [weakGrad_ae_eq hS, weakGrad_ae_eq hVW] with x h1 h2
        rw [h1, h2, hpt x]
    _ = ENNReal.ofReal (∫ x, t ^ 2 * (p x * dissInt W p h g t x) ∂haar d) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x =>
          mul_nonneg (sq_nonneg _) (mul_nonneg (hp0 x).le (hKb x).1))).symm
    _ = _ := by
        rw [integral_const_mul, integral_minimizer hyp hμ]

/-- **`D(ρ_t)/t² → ∫ |∇g|² dμ`** (dominated convergence, uniformly bounded integrands). -/
theorem tendsto_diss_pert {h g : Torus d → ℝ} (hc : Continuous h) (hg : ContDiff ℝ 1 (g ∘ liftT))
    {B : ℝ} (hB' : ∀ x, |h x| ≤ B) :
    Tendsto (fun t => ∫ x, dissInt W (elDens V W (μ : Measure (Torus d))) h g t x
        ∂(μ : Measure (Torus d))) (𝓝 0)
      (𝓝 (∫ x, ∑ k, cgrad g x k ^ 2 ∂(μ : Measure (Torus d)))) := by
  set μm := (μ : Measure (Torus d))
  set p := elDens V W μm
  obtain ⟨-, -, hp1⟩ := elDensity_props hyp μm
  have hpi : Integrable p (haar d) := integrable_of_integral_eq_one' hp1
  obtain ⟨K, hK⟩ := dissInt_bounds hyp (W := W) hpi hc hg hB'
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), |t| * (B + 2) ≤ 1 / 2 := by
    have : Tendsto (fun t : ℝ => |t| * (B + 2)) (𝓝 0) (𝓝 0) := by
      exact (continuous_abs.mul continuous_const : Continuous fun t : ℝ => |t| * (B + 2)).tendsto' 0 0
        (by simp)
    exact this.eventually (ge_mem_nhds (by norm_num))
  have hlim : ∀ x, Tendsto (fun t => dissInt W p h g t x) (𝓝 0) (𝓝 (∑ k, cgrad g x k ^ 2)) :=
    fun x => by
      have : ContinuousAt (fun t : ℝ => dissInt W p h g t x) 0 := by
        unfold dissInt
        exact (continuous_finsetSum _ fun k _ => (continuous_const.add
          ((continuous_id.mul continuous_const).mul continuous_const)).pow 2).continuousAt.div
          (continuous_const.add (continuous_id.mul continuous_const)).continuousAt (by simp)
      simpa [dissInt] using this.tendsto
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => K) ?_ ?_ (integrable_const K)
    (Eventually.of_forall hlim)
  · filter_upwards [hsmall] with t ht
    exact (hK t ht).1.aestronglyMeasurable
  · filter_upwards [hsmall] with t ht
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((hK t ht).2 x).1]; exact ((hK t ht).2 x).2

end diss

end SharpLSI
