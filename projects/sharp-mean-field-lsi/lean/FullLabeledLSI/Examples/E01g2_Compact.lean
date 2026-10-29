import FullLabeledLSI.Examples.E01a_Common
import SharpSymmetricLSI.Paper.FourierSynth
import SharpSymmetricLSI.Paper.CircleNear
import SharpSymmetricLSI.Paper.CircleLSIExt
import SharpSymmetricLSI.Paper.AppAEvol2
import SharpSymmetricLSI.Paper.DensMeasure
import SharpSymmetricLSI.Paper.CircleSobolev
import SharpSymmetricLSI.Paper.AppAPos5
import SharpSymmetricLSI.Paper.CosineExpansion
import SharpSymmetricLSI.Paper.AscoliSeq
import SharpSymmetricLSI.Infra.ChainRule

/-!
# Lane D, Task C (E01g2): uniform `H¹(𝕋)` compactness of nonnegative continuous functions

Pieces copied from lane C (`FullLabeledLSI/Examples/Paper/Sec9DeficitCompact.lean`,
`Sec9RegularityA.lean`, branch `origin/claude/flx-lane-c-6amts1`), themselves copied from
Prop 8.2 lane B / lane C (`B1Convergence`, `B2Fisher`, `B4Attainment`, `CCircle`): marked
"copied from lane C / Prop 8.2 lane B" below.
-/

open MeasureTheory InformationTheory Filter Topology Set
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI UnitAddTorus

/-! ### copied from lane C / Prop 8.2 lane C (`CCircle`): continuous representative -/


theorem lineT_secT (y : Torus 1) : lineT (secT y 0) = y := by
  unfold lineT; rw [← secT_eq_lineF]; exact liftT_secT y

theorem lineT_add_one (x : ℝ) : lineT (x + 1) = lineT x := by
  simpa using lineT_add_int x 1

theorem periodic_lineT : Function.Periodic lineT 1 := lineT_add_one

theorem secT_mem_Icc (y : Torus 1) : secT y 0 ∈ Icc (0 : ℝ) 1 := by
  have := (AddCircle.measurableEquivIoc 1 0 (y 0)).2
  have h2 : ((AddCircle.measurableEquivIoc 1 0 (y 0) : ℝ)) ≤ 1 := by simpa using this.2
  exact ⟨this.1.le, h2⟩

theorem secT_lineT_sub (r : ℝ) : ∃ m : ℤ, secT (lineT r) 0 = r + m := by
  obtain ⟨m, hm⟩ := secT_liftT_eq (lineF r)
  refine ⟨m 0, ?_⟩
  have := congrFun hm 0
  simpa [lineT, lineF, intVec] using this

/-- A property holding a.e. on the circle holds for a.e. real `r` along `lineT`. -/
theorem ae_real_of_ae_torus {p : Torus 1 → Prop} (h : ∀ᵐ y ∂haar 1, p y) :
    ∀ᵐ r : ℝ, p (lineT r) := by
  have h0 := ae_lineT h
  have hall : ∀ n : ℤ, ∀ᵐ r ∂(volume : Measure ℝ).restrict (Ioc (n : ℝ) (n + 1)), p (lineT r) := by
    intro n
    have hmp := (measurePreserving_sub_right (volume : Measure ℝ) (n : ℝ)).restrict_preimage_emb
      (measurableEmbedding_subRight (n : ℝ)) (Ioc (0 : ℝ) 1)
    have hpre : (fun r : ℝ => r - n) ⁻¹' Ioc (0 : ℝ) 1 = Ioc (n : ℝ) (n + 1) := by
      ext r; simp only [mem_preimage, mem_Ioc]; constructor <;> intro hr <;> constructor <;> linarith [hr.1, hr.2]
    rw [hpre] at hmp
    have := hmp.quasiMeasurePreserving.ae h0
    filter_upwards [this] with r hr
    have e : lineT (r - n) = lineT r := by
      have := lineT_add_int (r - n) n
      simpa using this.symm
    rwa [e] at hr
  have : ∀ᵐ r ∂(volume : Measure ℝ).restrict (⋃ n : ℤ, Ioc (n : ℝ) (n + 1)), p (lineT r) :=
    (ae_restrict_iUnion_iff _ _).2 hall
  rwa [iUnion_Ioc_intCast, Measure.restrict_univ] at this

theorem intervalIntegrable_lineT_all {g : Torus 1 → ℝ} (hg : Integrable g (haar 1)) (a b : ℝ) :
    IntervalIntegrable (fun r => g (lineT r)) volume a b :=
  (periodic_lineT.comp g).intervalIntegrable₀ one_ne_zero (intervalIntegrable_lineT hg) a b

/-- FTC for the mollifications. -/
theorem moll_sub_eq_integral {f g : Torus 1 → ℝ} (hw : IsWeakGrad f (fun y _ => g y))
    (hf : Integrable f (haar 1)) (n : ℕ) (s t : ℝ) :
    moll n f (lineT t) - moll n f (lineT s) = ∫ r in s..t, moll n g (lineT r) := by
  set Φ := moll n f ∘ liftT with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ := moll_comp_liftT_contDiff n hf
  set V : ℝ → ℝ := fun s => Φ (lineF s) with hV
  have hline : ∀ s, HasDerivAt (fun r : ℝ => lineF r) (Pi.single 0 1) s := by
    intro s
    have : (fun r : ℝ => lineF r) = fun r => r • (Pi.single 0 1 : Fin 1 → ℝ) := by
      funext r i; rw [Subsingleton.elim i 0]; simp [lineF]
    rw [this]
    simpa using (hasDerivAt_id s).smul_const (Pi.single 0 1 : Fin 1 → ℝ)
  have hVd : ∀ s, HasDerivAt V (fderiv ℝ Φ (lineF s) (Pi.single 0 1)) s := fun s =>
    ((hΦ.differentiable (by simp)) (lineF s)).hasFDerivAt.comp_hasDerivAt s (hline s)
  have hder : ∀ s, fderiv ℝ Φ (lineF s) (Pi.single 0 1) = moll n g (lineT s) := by
    intro s
    rw [hΦdef, moll_comp_liftT, fderiv_mollL_of_isWeakGrad hw n (lineF s) 0]
    exact (congrFun (moll_comp_liftT n g) (lineF s)).symm
  have hcont : Continuous fun s => moll n g (lineT s) := by
    have : (fun s => moll n g (lineT s)) = fun s => mollL n (g ∘ liftT) (lineF s) := by
      funext s
      have := congrFun (moll_comp_liftT n g) (lineF s)
      simpa [lineT] using this
    rw [this]
    exact ((contDiff_mollL n (hw.locInt_grad 0)).continuous).comp
      (continuous_pi fun _ => continuous_id)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => by
      simpa [hder r] using hVd r) (hcont.intervalIntegrable s t)
  rw [this]
  rfl

theorem abs_integral_lineT_le {h : Torus 1 → ℝ} (hh : Integrable h (haar 1)) {c d : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) (hd : d ∈ Icc (0 : ℝ) 1) :
    |∫ r in c..d, h (lineT r)| ≤ ∫ y, |h y| ∂haar 1 := by
  have habs : Integrable (fun y => |h y|) (haar 1) := hh.abs
  have key : ∀ c d : ℝ, c ∈ Icc (0 : ℝ) 1 → d ∈ Icc (0 : ℝ) 1 → c ≤ d →
      |∫ r in c..d, h (lineT r)| ≤ ∫ y, |h y| ∂haar 1 := by
    intro c d hc hd hcd
    have h1 : |∫ r in c..d, h (lineT r)| ≤ ∫ r in c..d, |h (lineT r)| :=
      intervalIntegral.abs_integral_le_integral_abs hcd
    refine h1.trans ?_
    rw [← intervalIntegral_lineT habs.aestronglyMeasurable]
    exact intervalIntegral.integral_mono_interval hc.1 hcd hd.2
      (Eventually.of_forall fun r => abs_nonneg _) (intervalIntegrable_lineT habs)
  rcases le_total c d with hcd | hdc
  · exact key c d hc hd hcd
  · rw [intervalIntegral.integral_symm, abs_neg]; exact key d c hd hc hdc

theorem tendsto_moll_integral {g : Torus 1 → ℝ} (hg : Integrable g (haar 1)) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => ∫ r in s..t, moll n g (lineT r)) atTop (𝓝 (∫ r in s..t, g (lineT r))) := by
  have hmi : ∀ n, Integrable (moll n g) (haar 1) := fun n => integrable_moll n hg
  have hbd : ∀ n, |(∫ r in s..t, moll n g (lineT r)) - ∫ r in s..t, g (lineT r)| ≤
      ∫ y, |moll n g y - g y| ∂haar 1 := by
    intro n
    rw [← intervalIntegral.integral_sub (intervalIntegrable_lineT_all (hmi n) s t)
      (intervalIntegrable_lineT_all hg s t)]
    exact abs_integral_lineT_le (h := fun y => moll n g y - g y) ((hmi n).sub hg) hs ht
  have hlim : Tendsto (fun n => ∫ y, |moll n g y - g y| ∂haar 1) atTop (𝓝 0) := by
    have h0 := tendsto_moll hg
    have h1 : Tendsto (fun n => (∫⁻ y, ‖moll n g y - g y‖ₑ).toReal) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
    refine h1.congr fun n => ?_
    have := integral_norm_eq_lintegral_enorm ((hmi n).sub hg).aestronglyMeasurable
    simpa [Real.norm_eq_abs] using this.symm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  simpa [Real.norm_eq_abs] using hbd n


/-- Key identity: for a.e. pair of points, `f x - f y = ∫_{secT y}^{secT x} g ∘ lineT`. -/
theorem exists_good_set {f g : Torus 1 → ℝ} (hw : IsWeakGrad f (fun y _ => g y))
    (hf : Integrable f (haar 1)) (hg : Integrable g (haar 1)) :
    ∃ G : Set (Torus 1), (∀ᵐ y ∂haar 1, y ∈ G) ∧ ∀ x ∈ G, ∀ y ∈ G,
      f x - f y = ∫ r in secT y 0..secT x 0, g (lineT r) := by
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_of_tendsto_lintegral
    (fun n => (measurable_moll n hf).aestronglyMeasurable) hf.aestronglyMeasurable
    (tendsto_moll hf)
  refine ⟨{y | Tendsto (fun k => moll (ns k) f y) atTop (𝓝 (f y))}, hae, ?_⟩
  intro x hx y hy
  have h1 : Tendsto (fun k => moll (ns k) f (lineT (secT x 0)) - moll (ns k) f (lineT (secT y 0)))
      atTop (𝓝 (f x - f y)) := by
    rw [lineT_secT, lineT_secT]; exact hx.sub hy
  have h2 : Tendsto (fun k => ∫ r in secT y 0..secT x 0, moll (ns k) g (lineT r)) atTop
      (𝓝 (∫ r in secT y 0..secT x 0, g (lineT r))) :=
    (tendsto_moll_integral hg (secT_mem_Icc y) (secT_mem_Icc x)).comp hns.tendsto_atTop
  refine tendsto_nhds_unique h1 (h2.congr fun k => ?_)
  rw [moll_sub_eq_integral hw hf]

theorem exists_continuous_rep {f g : Torus 1 → ℝ} (hw : IsWeakGrad f (fun y _ => g y))
    (hf : Integrable f (haar 1)) (hg : Integrable g (haar 1)) :
    ∃ F : ℝ → ℝ, Continuous F ∧ Function.Periodic F 1 ∧
      (∀ s t, F t - F s = ∫ r in s..t, g (lineT r)) ∧
      (∀ᵐ y ∂haar 1, f y = F (secT y 0)) ∧ ∀ᵐ r : ℝ, f (lineT r) = F r := by
  obtain ⟨G, hG, hGp⟩ := exists_good_set hw hf hg
  obtain ⟨y0, hy0⟩ := hG.exists
  set b0 := secT y0 0 with hb0
  set F : ℝ → ℝ := fun t => f y0 + ∫ r in b0..t, g (lineT r) with hF
  have hint := intervalIntegrable_lineT_all hg
  have hdiff : ∀ s t, F t - F s = ∫ r in s..t, g (lineT r) := by
    intro s t
    simp only [hF]
    rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
  have hcont : Continuous F :=
    continuous_const.add (intervalIntegral.continuous_primitive hint b0)
  have hper : Function.Periodic F 1 := by
    intro t
    have h1 := hdiff t (t + 1)
    have h2 : ∫ r in t..t + 1, g (lineT r) = 0 := by
      have hp := (periodic_lineT.comp g).intervalIntegral_add_eq t 0
      simp only [Function.comp_apply, zero_add] at hp
      rw [hp, intervalIntegral_lineT hg.aestronglyMeasurable]
      exact integral_weakGrad_eq_zero hw hf (fun _ => hg) 0
    linarith
  have hae : ∀ᵐ y ∂haar 1, f y = F (secT y 0) := by
    filter_upwards [hG] with x hx
    have := hGp x hx y0 hy0
    simp only [hF, hb0]
    linarith
  refine ⟨F, hcont, hper, hdiff, hae, ?_⟩
  filter_upwards [ae_real_of_ae_torus hae] with r hr
  obtain ⟨m, hm⟩ := secT_lineT_sub r
  rw [hr, hm]
  simpa using hper.int_mul m r



/-! ### FTC for continuous `H¹` functions -/

theorem continuous_lineT : Continuous lineT :=
  continuous_liftT.comp (continuous_pi fun _ => continuous_id)

theorem ftc_cont {u : Torus 1 → ℝ} (hc : Continuous u) (hH : MemH1 (haar 1) u) (s t : ℝ) :
    u (lineT t) - u (lineT s) = ∫ r in s..t, weakGrad u (lineT r) 0 := by
  have hw : IsWeakGrad u (fun y _ => weakGrad u y 0) := by
    have e : (fun y (_ : Fin 1) => weakGrad u y 0) = weakGrad u := by
      funext y i; rw [Subsingleton.elim i 0]
    rw [e]; exact isWeakGrad_weakGrad hH.1
  have hf : Integrable u (haar 1) := hH.2.1.integrable one_le_two
  have hg : Integrable (fun y => weakGrad u y 0) (haar 1) :=
    (memLp_weakGrad_zero hH).integrable one_le_two
  obtain ⟨F, hF, -, hdiff, -, hae⟩ := exists_continuous_rep hw hf hg
  have hcont : Continuous (fun r => u (lineT r)) := hc.comp continuous_lineT
  have heq : (fun r => u (lineT r)) = F :=
    (Continuous.ae_eq_iff_eq (volume : Measure ℝ) hcont hF).mp hae
  have h1 : u (lineT t) = F t := congrFun heq t
  have h2 : u (lineT s) = F s := congrFun heq s
  rw [h1, h2, hdiff]

/-- `|∫_s^t a| ≤ D/(2λ) + λ|t-s|/2` for `s, t ∈ [0,1]`. -/
theorem abs_integral_lineT_le_sq {g : Torus 1 → ℝ} (hg : MemLp g 2 (haar 1)) {D : ℝ}
    (hD : ∫ y, g y ^ 2 ∂haar 1 ≤ D) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    {l : ℝ} (hl : 0 < l) :
    |∫ r in s..t, g (lineT r)| ≤ D / (2 * l) + l * |t - s| / 2 := by
  have hgi : Integrable g (haar 1) := hg.integrable one_le_two
  have hg2 : Integrable (fun y => g y ^ 2) (haar 1) := hg.integrable_sq
  have key : ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → s ≤ t →
      |∫ r in s..t, g (lineT r)| ≤ D / (2 * l) + l * (t - s) / 2 := by
    intro s t hs ht hst
    have hI : ∀ a b, IntervalIntegrable (fun r => g (lineT r)) volume a b := fun a b =>
      (periodic_lineT.comp g).intervalIntegrable₀ one_ne_zero (intervalIntegrable_lineT hgi) a b
    have hI2 : ∀ a b, IntervalIntegrable (fun r => g (lineT r) ^ 2) volume a b := fun a b =>
      (periodic_lineT.comp (fun y => g y ^ 2)).intervalIntegrable₀ one_ne_zero
        (intervalIntegrable_lineT hg2) a b
    have h1 : |∫ r in s..t, g (lineT r)| ≤ ∫ r in s..t, |g (lineT r)| :=
      intervalIntegral.abs_integral_le_integral_abs hst
    have h2 : ∫ r in s..t, |g (lineT r)| ≤
        ∫ r in s..t, (g (lineT r) ^ 2 / (2 * l) + l / 2) := by
      refine intervalIntegral.integral_mono_on hst (hI s t).abs
        (((hI2 s t).div_const (2 * l)).add intervalIntegrable_const) (fun r _ => ?_)
      have : 0 ≤ (|g (lineT r)| - l) ^ 2 := sq_nonneg _
      rw [div_add_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_abs (g (lineT r))]
    have h3 : ∫ r in s..t, (g (lineT r) ^ 2 / (2 * l) + l / 2) =
        (∫ r in s..t, g (lineT r) ^ 2) / (2 * l) + (t - s) * (l / 2) := by
      rw [intervalIntegral.integral_add ((hI2 s t).div_const (2 * l)) intervalIntegrable_const,
        intervalIntegral.integral_div]
      simp only [intervalIntegral.integral_const, smul_eq_mul]
    have h4 : ∫ r in s..t, g (lineT r) ^ 2 ≤ D := by
      refine le_trans ?_ hD
      rw [← intervalIntegral_lineT hg2.aestronglyMeasurable]
      exact intervalIntegral.integral_mono_interval hs.1 hst ht.2
        (Eventually.of_forall fun r => sq_nonneg _) (hI2 0 1)
    have h5 : (∫ r in s..t, g (lineT r) ^ 2) / (2 * l) ≤ D / (2 * l) :=
      div_le_div_of_nonneg_right h4 (by positivity)
    nlinarith
  rcases le_total s t with hst | hts
  · rw [abs_of_nonneg (sub_nonneg.mpr hst)]; exact key s t hs ht hst
  · rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonpos (sub_nonpos.mpr hts)]
    have := key t s ht hs hts
    linarith

theorem holder_cont {u : Torus 1 → ℝ} (hc : Continuous u) (hH : MemH1 (haar 1) u) {D : ℝ}
    (hD : ∫ y, weakGrad u y 0 ^ 2 ∂haar 1 ≤ D) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) {l : ℝ} (hl : 0 < l) :
    |u (lineT t) - u (lineT s)| ≤ D / (2 * l) + l * |t - s| / 2 := by
  rw [ftc_cont hc hH s t]
  exact abs_integral_lineT_le_sq (memLp_weakGrad_zero hH) hD hs ht hl
/-! ### copied from lane C / Prop 8.2 lane B (`B1Convergence`, `B2Fisher`, `B4Attainment`) -/

/-- A.e. convergent subsequence from `L²` convergence (copy of `B1Convergence.exists_ae_subseq_of_L2`). -/
theorem exists_ae_subseq_of_L2 {f : ℕ → Torus 1 → Real} {u : Torus 1 → Real}
    (hf : ∀ n, MemLp (f n) 2 (haar 1)) (hu : MemLp u 2 (haar 1))
    (h : Tendsto (fun n => ∫ x, (f n x - u x) ^ 2 ∂haar 1) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ x ∂haar 1, Tendsto (fun n => f (φ n) x) atTop (𝓝 (u x)) := by
  have he : Tendsto (fun n => eLpNorm (f n - u) 2 (haar 1)) atTop (𝓝 0) := by
    have key : ∀ n, eLpNorm (f n - u) 2 (haar 1) =
        ENNReal.ofReal (Real.sqrt (∫ x, (f n x - u x) ^ 2 ∂haar 1)) := by
      intro n
      have hm := (hf n).sub hu
      rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      congr 1
      rw [Real.sqrt_eq_rpow]
      simp only [ENNReal.toReal_ofNat, Pi.sub_apply, Real.norm_eq_abs]
      norm_num
    simp_rw [key]
    have := ((Real.continuous_sqrt.tendsto 0).comp h)
    rw [Real.sqrt_zero] at this
    simpa using ENNReal.tendsto_ofReal this
  exact (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero he).exists_seq_tendsto_ae

theorem integrable_mul_of_memLp_two {f g : Torus 1 → Real} (hf : MemLp f 2 (haar 1))
    (hg : MemLp g 2 (haar 1)) : Integrable (fun x => f x * g x) (haar 1) := by
  refine Integrable.mono' (hf.integrable_sq.add hg.integrable_sq)
    (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_le, Pi.add_apply]
  constructor <;> nlinarith [sq_nonneg (f x + g x), sq_nonneg (f x - g x)]

/-- Weak lower semicontinuity of the `L²` norm along a sequence whose squared norms converge. -/
theorem sq_integral_le_of_weak_tendsto {w : ℕ → Torus 1 → Real} {g : Torus 1 → Real}
    (hw : ∀ n, MemLp (w n) 2 (haar 1)) (hg : MemLp g 2 (haar 1))
    (hweak : ∀ h : Torus 1 → Real, MemLp h 2 (haar 1) →
      Tendsto (fun n => ∫ x, w n x * h x ∂haar 1) atTop (𝓝 (∫ x, g x * h x ∂haar 1)))
    {L : Real} (hL : Tendsto (fun n => ∫ x, w n x ^ 2 ∂haar 1) atTop (𝓝 L)) :
    ∫ x, g x ^ 2 ∂haar 1 ≤ L := by
  have hlim : Tendsto (fun n => 2 * ∫ x, w n x * g x ∂haar 1 - ∫ x, g x ^ 2 ∂haar 1)
      atTop (𝓝 (2 * ∫ x, g x * g x ∂haar 1 - ∫ x, g x ^ 2 ∂haar 1)) :=
    ((hweak g hg).const_mul 2).sub_const _
  have hgg : ∫ x, g x * g x ∂haar 1 = ∫ x, g x ^ 2 ∂haar 1 := by
    congr 1; funext x; ring
  rw [hgg] at hlim
  have hle : ∀ n, 2 * ∫ x, w n x * g x ∂haar 1 - ∫ x, g x ^ 2 ∂haar 1 ≤
      ∫ x, w n x ^ 2 ∂haar 1 := by
    intro n
    have i1 := (hw n).integrable_sq
    have i2 := hg.integrable_sq
    have i3 := integrable_mul_of_memLp_two (hw n) hg
    have h0 : 0 ≤ ∫ x, (w n x - g x) ^ 2 ∂haar 1 := integral_nonneg fun x => sq_nonneg _
    have e : ∫ x, (w n x - g x) ^ 2 ∂haar 1 =
        ∫ x, w n x ^ 2 ∂haar 1 - 2 * ∫ x, w n x * g x ∂haar 1 + ∫ x, g x ^ 2 ∂haar 1 := by
      have : ∀ x, (w n x - g x) ^ 2 = (w n x ^ 2 - 2 * (w n x * g x)) + g x ^ 2 :=
        fun x => by ring
      simp_rw [this]
      rw [integral_add (f := fun x => w n x ^ 2 - 2 * (w n x * g x))
        (g := fun x => g x ^ 2) (i1.sub (i3.const_mul 2)) i2,
        integral_sub (f := fun x => w n x ^ 2) (g := fun x => 2 * (w n x * g x)) i1
          (i3.const_mul 2), integral_const_mul]
    linarith
  have := le_of_tendsto_of_tendsto' hlim hL hle
  linarith

/-- The weak limit is an `H¹` square root (copy of `B4Attainment.limit_memH1`). -/
theorem limit_memH1 {u : Torus 1 → Real} {g : Torus 1 → Fin 1 → Real}
    (hu : MemLp u 2 (haar 1)) (hg : ∀ j, MemLp (fun x => g x j) 2 (haar 1))
    (hw : IsWeakGrad u g) (hu0 : ∀ᵐ x ∂haar 1, 0 ≤ u x) :
    MemH1 (haar 1) (fun x => Real.sqrt (u x ^ 2)) ∧
      (∀ᵐ x ∂haar 1, weakGrad (fun y => Real.sqrt (u y ^ 2)) x 0 = g x 0) := by
  have hae : (fun x => Real.sqrt (u x ^ 2)) =ᵐ[haar 1] u := by
    filter_upwards [hu0] with x hx
    exact Real.sqrt_sq hx
  have hgu : weakGrad u =ᵐ[haar 1] g :=
    weakGrad_ae_unique (isWeakGrad_weakGrad ⟨g, hw⟩) hw
  have hU : MemH1 (haar 1) u := by
    refine ⟨⟨g, hw⟩, hu, ?_⟩
    have h1 : MemLp (fun x => Real.sqrt (sqNorm (g x))) 2 (haar 1) := by
      have : (fun x => Real.sqrt (sqNorm (g x))) = fun x => |g x 0| := by
        funext x
        simp [sqNorm, Real.sqrt_sq_eq_abs]
      rw [this]
      exact (hg 0).abs
    refine h1.ae_eq ?_
    filter_upwards [hgu] with x hx
    rw [hx]
  have hV : MemH1 (haar 1) (fun x => Real.sqrt (u x ^ 2)) := appA_memH1_congr_ae hae.symm hU
  refine ⟨hV, ?_⟩
  have h2 := appA_weakGrad_congr_ae hae hV.1
  filter_upwards [h2, hgu] with x hx1 hx2
  rw [hx1, hx2]


/-! ### Sequential Arzelà–Ascoli under uniform equicontinuity (adapted from `AscoliSeq`) -/

open BoundedContinuousFunction in
theorem exists_subseq_unif_eqc {X : Type*} [MetricSpace X] [CompactSpace X] (u : ℕ → X → ℝ)
    {C : ℝ} (hb : ∀ n x, |u n x| ≤ C) (hc : ∀ n, Continuous (u n))
    (heq : ∀ ε > 0, ∃ δ > 0, ∀ n x y, dist x y < δ → dist (u n x) (u n y) < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : X → ℝ, Continuous v ∧
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ x, |u (φ n) x - v x| ≤ ε := by
  set f : ℕ → X →ᵇ ℝ := fun n => mkOfCompact ⟨u n, hc n⟩ with hf
  set A : Set (X →ᵇ ℝ) := Set.range f
  have hin : ∀ (g : X →ᵇ ℝ) (x : X), g ∈ A → g x ∈ Set.Icc (-C) C := by
    rintro g x ⟨n, rfl⟩
    exact abs_le.mp (hb n x)
  have heq' : Equicontinuous ((↑) : A → X → ℝ) := by
    refine UniformEquicontinuous.equicontinuous ?_
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := heq ε hε
    refine ⟨δ, hδ, fun x y hxy g => ?_⟩
    obtain ⟨n, hn⟩ := g.2
    have : (g : X → ℝ) = u n := by rw [← hn]; rfl
    rw [this]
    exact h n x y hxy
  have hK := arzela_ascoli (Set.Icc (-C) C) isCompact_Icc A hin heq'
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := f) fun n => subset_closure ⟨n, rfl⟩
  refine ⟨φ, hφ, a, a.continuous, fun ε hε => ?_⟩
  have := (Metric.tendsto_atTop.mp hlim) ε hε
  obtain ⟨N, hN⟩ := this
  refine eventually_atTop.mpr ⟨N, fun n hn x => ?_⟩
  have h1 := hN n hn
  have h2 : |f (φ n) x - a x| ≤ dist (f (φ n)) a := by
    rw [← Real.dist_eq]; exact dist_coe_le_dist x
  exact h2.trans h1.le

/-! ### Uniform bound and uniform equicontinuity on the circle -/

theorem unif_bound {u : Torus 1 → ℝ} (hc : Continuous u) (hH : MemH1 (haar 1) u) {D : ℝ}
    (h1 : ∫ x, u x ^ 2 ∂haar 1 = 1)
    (hD : ∫ y, weakGrad u y 0 ^ 2 ∂haar 1 ≤ D) (x : Torus 1) : |u x| ≤ 1 + (D + 1) / 2 := by
  obtain ⟨y0, hy0⟩ := exists_le_integral (μ := haar 1) (f := fun x => u x ^ 2)
    hH.2.1.integrable_sq
  rw [h1] at hy0
  have hy1 : |u y0| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; exact hy0
  have h := holder_cont hc hH hD (s := secT y0 0) (t := secT x 0) (secT_mem_Icc y0)
    (secT_mem_Icc x) (l := 1) one_pos
  rw [lineT_secT, lineT_secT] at h
  have hts : |secT x 0 - secT y0 0| ≤ 1 := by
    have := secT_mem_Icc x; have := secT_mem_Icc y0
    rw [abs_le]; constructor <;> linarith [(secT_mem_Icc x).1, (secT_mem_Icc x).2,
      (secT_mem_Icc y0).1, (secT_mem_Icc y0).2]
  have : |u x| ≤ |u y0| + |u x - u y0| := by
    have := abs_add_le (u y0) (u x - u y0)
    simpa using this
  have h' : D / (2 * 1) + 1 * |secT x 0 - secT y0 0| / 2 ≤ (D + 1) / 2 := by
    nlinarith
  linarith

theorem equicont_cont {u : Torus 1 → ℝ} (hc : Continuous u) (hH : MemH1 (haar 1) u) {D : ℝ}
    (hD0 : 0 ≤ D) (hD : ∫ y, weakGrad u y 0 ^ 2 ∂haar 1 ≤ D) {ε : ℝ} (hε : 0 < ε) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : |t - s| < ε ^ 2 / (D + 1)) :
    |u (lineT t) - u (lineT s)| < ε := by
  have hD1 : 0 < D + 1 := by linarith
  have hl : 0 < (D + 1) / ε := by positivity
  have h := holder_cont hc hH hD hs ht hl
  have e1 : D / (2 * ((D + 1) / ε)) ≤ ε / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    field_simp
    nlinarith
  have e2 : (D + 1) / ε * |t - s| / 2 < ε / 2 := by
    have : |t - s| * ((D + 1) / ε) < ε ^ 2 / (D + 1) * ((D + 1) / ε) :=
      mul_lt_mul_of_pos_right hst hl
    have e : ε ^ 2 / (D + 1) * ((D + 1) / ε) = ε := by field_simp
    rw [e] at this
    nlinarith
  linarith

/-- A sequence of continuous nonnegative `u_n ∈ H¹(𝕋)` with `∫ u_n² = 1` and `∫ (u_n')² ≤ D` has a
subsequence converging uniformly to a continuous `f ≥ 0` with `f ∈ H¹`, `∫ f² = 1`, with weak
convergence of the gradients in `L²` (hence weakly in `H¹`), and the Dirichlet energies of the
subsequence converge to some `L ≥ ∫ (f')²`. -/
theorem h1_unif_compact {u : ℕ → Torus 1 → ℝ} {D : ℝ} (hc : ∀ n, Continuous (u n))
    (h0 : ∀ n x, 0 ≤ u n x) (hH : ∀ n, MemH1 (haar 1) (u n))
    (h1 : ∀ n, ∫ x, u n x ^ 2 ∂haar 1 = 1)
    (hD : ∀ n, ∫ x, weakGrad (u n) x 0 ^ 2 ∂haar 1 ≤ D) :
    ∃ (φ : ℕ → ℕ) (f : Torus 1 → ℝ) (L : ℝ), StrictMono φ ∧ Continuous f ∧ (∀ x, 0 ≤ f x) ∧
      ∫ x, f x ^ 2 ∂haar 1 = 1 ∧ MemH1 (haar 1) f ∧
      TendstoUniformly (fun n x => u (φ n) x) f atTop ∧
      (∀ g : Torus 1 → ℝ, MemLp g 2 (haar 1) →
        Tendsto (fun n => ∫ x, weakGrad (u (φ n)) x 0 * g x ∂haar 1) atTop
          (𝓝 (∫ x, weakGrad f x 0 * g x ∂haar 1))) ∧
      (∀ g : Torus 1 → ℝ, MemH1 (haar 1) g →
        Tendsto (fun n => ∫ x, u (φ n) x * g x ∂haar 1 +
            ∫ x, weakGrad (u (φ n)) x 0 * weakGrad g x 0 ∂haar 1) atTop
          (𝓝 (∫ x, f x * g x ∂haar 1 + ∫ x, weakGrad f x 0 * weakGrad g x 0 ∂haar 1))) ∧
      Tendsto (fun n => ∫ x, weakGrad (u (φ n)) x 0 ^ 2 ∂haar 1) atTop (𝓝 L) ∧
      ∫ x, weakGrad f x 0 ^ 2 ∂haar 1 ≤ L := by
  have hD0 : 0 ≤ D := (integral_nonneg fun x => sq_nonneg _).trans (hD 0)
  have hw : ∀ n, IsWeakGrad (u n) (weakGrad (u n)) := fun n => isWeakGrad_weakGrad (hH n).1
  have hg : ∀ n j, MemLp (fun x => weakGrad (u n) x j) 2 (haar 1) := by
    intro n j
    have : j = 0 := Subsingleton.elim _ _
    subst this
    exact memLp_weakGrad_zero (hH n)
  have hB : ∀ n, (∫ y, u n y ^ 2) + ∑ j : Fin 1, ∫ y, weakGrad (u n) y j ^ 2 ≤ 1 + D := by
    intro n
    simp only [Fin.sum_univ_one, h1 n]
    linarith [hD n]
  obtain ⟨φ0, hφ0, fI, G, hfI, hG, hwf, hL2, hwlim⟩ :=
    rellich_torus hw (fun n => (hH n).2.1) hg hB
  -- uniform bound
  set C : ℝ := 1 + (D + 1) / 2 with hCdef
  have hC : ∀ n x, |u n x| ≤ C := fun n x => unif_bound (hc n) (hH n) (h1 n) (hD n) x
  -- Arzelà–Ascoli on `[0,1]`
  set w : ℕ → Icc (0 : ℝ) 1 → ℝ := fun n t => u (φ0 n) (lineT t.1) with hwdef
  have hwb : ∀ n x, |w n x| ≤ C := fun n x => hC _ _
  have hwc : ∀ n, Continuous (w n) := fun n =>
    (hc _).comp (continuous_lineT.comp continuous_subtype_val)
  have hweq : ∀ ε > 0, ∃ δ > 0, ∀ n x y, dist x y < δ → dist (w n x) (w n y) < ε := by
    intro ε hε
    refine ⟨ε ^ 2 / (D + 1), by positivity, fun n x y hxy => ?_⟩
    rw [Real.dist_eq]
    have := equicont_cont (hc (φ0 n)) (hH (φ0 n)) hD0 (hD (φ0 n)) hε (s := y.1) (t := x.1)
      y.2 x.2 (by simpa [Subtype.dist_eq, Real.dist_eq] using hxy)
    exact this
  obtain ⟨ψ1, hψ1, W, hW, hWlim⟩ := exists_subseq_unif_eqc w hwb hwc hweq
  set f : Torus 1 → ℝ := fun x => W ⟨secT x 0, secT_mem_Icc x⟩ with hfdef
  set θ : ℕ → ℕ := fun n => φ0 (ψ1 n) with hθdef
  have hθ : StrictMono θ := hφ0.comp hψ1
  have hunif : TendstoUniformly (fun n x => u (θ n) x) f atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hWlim (ε / 2) (half_pos hε)] with n hn x
    have := hn ⟨secT x 0, secT_mem_Icc x⟩
    simp only [hwdef, lineT_secT] at this
    rw [Real.dist_eq, abs_sub_comm]
    simp only [hθdef, hfdef]
    linarith
  have hpt : ∀ x, Tendsto (fun n => u (θ n) x) atTop (𝓝 (f x)) := fun x => hunif.tendsto_at x
  have hfc : Continuous f := hunif.continuous (Eventually.of_forall fun n => hc (θ n)).frequently
  have hf0 : ∀ x, 0 ≤ f x := fun x => ge_of_tendsto' (hpt x) fun n => h0 _ x
  have hfC : ∀ x, |f x| ≤ C := fun x =>
    le_of_tendsto' ((continuous_abs.tendsto _).comp (hpt x)) fun n => hC _ x
  -- identification with the `L²` limit
  have hL2θ : Tendsto (fun n => ∫ x, (u (θ n) x - fI x) ^ 2 ∂haar 1) atTop (𝓝 0) :=
    hL2.comp hψ1.tendsto_atTop
  obtain ⟨ψ2, hψ2, hae0⟩ := exists_ae_subseq_of_L2 (f := fun n x => u (θ n) x)
    (fun n => (hH _).2.1) hfI hL2θ
  have hfae : f =ᵐ[haar 1] fI := by
    filter_upwards [hae0] with x hx
    exact tendsto_nhds_unique ((hpt x).comp hψ2.tendsto_atTop) hx
  have hfI0 : ∀ᵐ x ∂haar 1, 0 ≤ fI x := by
    filter_upwards [hfae] with x hx
    rw [← hx]; exact hf0 x
  obtain ⟨hMU, hgrad⟩ := limit_memH1 hfI hG hwf hfI0
  have hfU : f =ᵐ[haar 1] fun x => Real.sqrt (fI x ^ 2) := by
    filter_upwards [hfae, hfI0] with x hx hx0
    rw [Real.sqrt_sq hx0, hx]
  have hMf : MemH1 (haar 1) f := appA_memH1_congr_ae hfU.symm hMU
  have hgf : ∀ᵐ x ∂haar 1, weakGrad f x 0 = G x 0 := by
    have h2 := appA_weakGrad_congr_ae hfU.symm hMU.1
    filter_upwards [h2, hgrad] with x hx1 hx2
    rw [← hx1, hx2]
  -- mass
  have hmass : ∫ x, f x ^ 2 ∂haar 1 = 1 := by
    have hlim : Tendsto (fun n => ∫ x, u (θ n) x ^ 2 ∂haar 1) atTop
        (𝓝 (∫ x, f x ^ 2 ∂haar 1)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => C ^ 2) (fun n => ?_)
        (integrable_const _) (fun n => ?_) ?_
      · exact (hH _).2.1.integrable_sq.aestronglyMeasurable
      · refine Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hC _ x) 2
      · exact Eventually.of_forall fun x => (hpt x).pow 2
    simp only [h1] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  -- convergent subsequence of the Dirichlet energies
  obtain ⟨L, -, χ, hχ, hLχ⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (0 : ℝ) D)
    (x := fun k => ∫ x, weakGrad (u (θ k)) x 0 ^ 2 ∂haar 1)
    (fun k => ⟨integral_nonneg fun x => sq_nonneg _, hD _⟩)
  have hψχ : StrictMono (ψ1 ∘ χ) := hψ1.comp hχ
  have hweakθ : ∀ g : Torus 1 → ℝ, MemLp g 2 (haar 1) →
      Tendsto (fun n => ∫ x, weakGrad (u (θ n)) x 0 * g x ∂haar 1) atTop
        (𝓝 (∫ x, weakGrad f x 0 * g x ∂haar 1)) := by
    intro g hg2
    have := (hwlim 0 g hg2).comp hψ1.tendsto_atTop
    have e : ∫ x, weakGrad f x 0 * g x ∂haar 1 = ∫ x, G x 0 * g x ∂haar 1 :=
      integral_congr_ae (hgf.mono fun x hx => by simp only; rw [hx])
    rw [e]
    exact this
  refine ⟨fun k => θ (χ k), f, L, hθ.comp hχ, hfc, hf0, hmass, hMf, ?_, ?_, ?_, hLχ, ?_⟩
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    exact hχ.tendsto_atTop.eventually (Metric.tendstoUniformly_iff.mp hunif ε hε)
  · intro g hg2
    exact (hweakθ g hg2).comp hχ.tendsto_atTop
  · intro g hgH
    have hgg : MemLp g 2 (haar 1) := hgH.2.1
    have hgg' : MemLp (fun x => weakGrad g x 0) 2 (haar 1) := memLp_weakGrad_zero hgH
    have h1' : Tendsto (fun n => ∫ x, u (θ n) x * g x ∂haar 1) atTop
        (𝓝 (∫ x, f x * g x ∂haar 1)) := by
      refine tendsto_integral_of_dominated_convergence (fun x => C * |g x|) (fun n => ?_)
        ((hgg.integrable one_le_two).abs.const_mul C) (fun n => ?_) ?_
      · exact (hH _).2.1.aestronglyMeasurable.mul hgg.aestronglyMeasurable
      · refine Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hC _ x) (abs_nonneg _)
      · exact Eventually.of_forall fun x => (hpt x).mul_const _
    have := (h1'.add (hweakθ _ hgg')).comp hχ.tendsto_atTop
    exact this
  · have hw' : ∀ n, MemLp (fun x => weakGrad (u (θ (χ n))) x 0) 2 (haar 1) :=
      fun n => memLp_weakGrad_zero (hH _)
    have hlsc := sq_integral_le_of_weak_tendsto
      (w := fun n x => weakGrad (u (θ (χ n))) x 0) (g := fun x => G x 0) hw' (hG 0)
      (fun h hh => (hwlim 0 h hh).comp hψχ.tendsto_atTop) hLχ
    have : ∫ x, weakGrad f x 0 ^ 2 ∂haar 1 = ∫ x, G x 0 ^ 2 ∂haar 1 :=
      integral_congr_ae (hgf.mono fun x hx => by simp only; rw [hx])
    rw [this]
    exact hlsc

end SharpLSI.FL.Ex.LaneD
