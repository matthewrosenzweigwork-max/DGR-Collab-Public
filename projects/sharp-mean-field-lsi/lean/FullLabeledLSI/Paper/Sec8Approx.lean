import FullLabeledLSI.Paper.Sec8Smooth
import FullLabeledLSI.Defs.F02_Constants
import SharpSymmetricLSI.Paper.UpperApprox
import SharpSymmetricLSI.Paper.AppARStar1
import SharpSymmetricLSI.Paper.EntFinite
import SharpSymmetricLSI.Paper.ProductEntropy
import SharpSymmetricLSI.Paper.DensMeasure

/-!
# Section 8.2: smooth test functions for the Poincare constant

If the ordinary Poincare constant of a smooth positive density `rho` is below `R`, there is a smooth
mean-zero `k` with `int rho |grad k|^2 < R int rho k^2`.  Proof: mollify an `H^1(rho)` test function
(`rho` is bounded above and below, so `H^1(rho)` and `H^1(haar)` coincide).
-/

open MeasureTheory Filter Topology SharpLSI
open scoped ENNReal ContDiff

namespace SharpLSI.FL
namespace Sec8

variable {d : ℕ}

theorem exists_pos_bounds {ρ : Torus d → ℝ} (hc : Continuous ρ) (hp : ∀ x, 0 < ρ x) :
    ∃ m M : ℝ, 0 < m ∧ (∀ x, m ≤ ρ x) ∧ (∀ x, ρ x ≤ M) := by
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn (s := (Set.univ : Set (Torus d)))
    Set.univ_nonempty hc.continuousOn
  obtain ⟨M, hM⟩ := SharpLSI.exists_bound_of_continuous hc
  exact ⟨ρ x0, M, hp x0, fun x => hx0 (Set.mem_univ x), fun x => (le_abs_self _).trans (hM x)⟩

theorem densMeasure_le_smul {ρ : Torus d → ℝ} {M : ℝ} (hM : ∀ x, ρ x ≤ M) :
    densMeasure ρ ≤ ENNReal.ofReal M • haar d := by
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [densMeasure, withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hM x)

theorem haar_le_smul_densMeasure {ρ : Torus d → ℝ} {m : ℝ} (hm : 0 < m) (hρ : ∀ x, m ≤ ρ x) :
    haar d ≤ ENNReal.ofReal m⁻¹ • densMeasure ρ := by
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul, densMeasure, withDensity_apply _ hs,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc haar d s = ∫⁻ _x in s, 1 ∂haar d := by simp
    _ ≤ _ := by
      refine lintegral_mono fun x => ?_
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hm.le), ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by
        rw [inv_mul_eq_div, le_div_iff₀ hm]; linarith [hρ x])

theorem lintegral_enorm_sq_ne_top {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : α → ℝ}
    (hu : MemLp u 2 μ) : ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ ≠ ⊤ := by
  have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hu.aestronglyMeasurable).1 hu.eLpNorm_lt_top
  simpa [ENNReal.rpow_two] using this.ne

theorem L2Tendsto.of_le_smul {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (hle : μ ≤ c • ν) {f : ℕ → α → ℝ} {g : α → ℝ} (h : L2Tendsto ν f g) :
    L2Tendsto μ f g := by
  have h1 : Tendsto (fun n => c * ∫⁻ x, ‖f n x - g x‖ₑ ^ 2 ∂ν) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul h (Or.inr hc)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le) ?_
  intro n
  calc ∫⁻ x, ‖f n x - g x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x, ‖f n x - g x‖ₑ ^ 2 ∂(c • ν) := lintegral_mono' hle le_rfl
    _ = _ := lintegral_smul_measure _ _

theorem dirichlet_eq_sum {P : Measure (Torus d)} (hP : P ≪ haar d) {f : Torus d → ℝ}
    {g : Torus d → Fin d → ℝ} (hw : IsWeakGrad f g) :
    dirichlet P f = ∑ k, ∫⁻ x, ‖g x k‖ₑ ^ 2 ∂P := by
  unfold dirichlet
  have hae : weakGrad f =ᵐ[P] g := hP.ae_eq (weakGrad_ae_eq hw)
  rw [← lintegral_finsetSum']
  · refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
    unfold sqNorm
    rw [ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
    exact Finset.sum_congr rfl fun k _ => ofReal_sq_eq_enorm_sq _
  · exact fun k _ => (((hw.aestronglyMeasurable_grad k).aemeasurable.mono_ac hP).enorm.pow_const 2)

theorem exists_smooth_seq {ρ : Torus d → ℝ} (hρc : Continuous ρ) (hρp : ∀ x, 0 < ρ x)
    {h : Torus d → ℝ} (hh : MemH1 (densMeasure ρ) h) :
    ∃ f : ℕ → Torus d → ℝ, (∀ n, IsSmoothT (f n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖f n x - h x‖ₑ ^ 2 ∂densMeasure ρ) atTop (𝓝 0) ∧
      Tendsto (fun n => dirichlet (densMeasure ρ) (f n)) atTop
        (𝓝 (dirichlet (densMeasure ρ) h)) ∧
      ∀ᵐ x ∂densMeasure ρ, Tendsto (fun n => f n x) atTop (𝓝 (h x)) := by
  obtain ⟨m, M, hm, hmρ, hρM⟩ := exists_pos_bounds hρc hρp
  set P := densMeasure ρ with hP
  have hPle := densMeasure_le_smul hρM
  have hvle := haar_le_smul_densMeasure hm hmρ
  have hPac : P ≪ haar d := withDensity_absolutelyContinuous _ _
  have hw := isWeakGrad_weakGrad hh.1
  set g := weakGrad h with hg
  have h2 : MemLp h 2 (haar d) := hh.2.1.of_measure_le_smul ENNReal.ofReal_ne_top hvle
  have hgkP : ∀ k, MemLp (fun y => g y k) 2 P := fun k =>
    hh.2.2.of_le ((hw.aestronglyMeasurable_grad k).mono_ac hPac)
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact abs_le_sqrt_sqNorm _ k)
  have hgk : ∀ k, MemLp (fun y => g y k) 2 (haar d) := fun k =>
    (hgkP k).of_measure_le_smul ENNReal.ofReal_ne_top hvle
  have hint : Integrable h volume := h2.integrable one_le_two
  have hgint : ∀ k, Integrable (fun y => g y k) volume := fun k => (hgk k).integrable one_le_two
  obtain ⟨ns, hns, hae⟩ := exists_subseq_moll_ae hint hgint
  have hae1 : ∀ᵐ y ∂(volume : Measure (Torus d)),
      Tendsto (fun j => moll (ns j) h y) atTop (𝓝 (h y)) := hae.mono fun y hy => hy.1
  have hae2 : ∀ k, ∀ᵐ y ∂(volume : Measure (Torus d)),
      Tendsto (fun j => moll (ns j) (fun z => g z k) y) atTop (𝓝 (g y k)) :=
    fun k => hae.mono fun y hy => hy.2 k
  have L0 := L2Tendsto_moll hint (lintegral_enorm_sq_ne_top h2) hae1
  have Lk := fun k => L2Tendsto_moll (hgint k) (lintegral_enorm_sq_ne_top (hgk k)) (hae2 k)
  refine ⟨fun j => moll (ns j) h, fun j => moll_comp_liftT_contDiff (ns j) hint,
    L2Tendsto.of_le_smul ENNReal.ofReal_ne_top hPle L0, ?_, hPac.ae_le hae1⟩
  have hdir : ∀ j, dirichlet P (moll (ns j) h) =
      ∑ k, ∫⁻ x, ‖moll (ns j) (fun z => g z k) x‖ₑ ^ 2 ∂P := fun j =>
    dirichlet_eq_sum hPac (isWeakGrad_moll hw hint (ns j))
  show Tendsto (fun j => dirichlet P (moll (ns j) h)) atTop _
  simp_rw [hdir]
  rw [dirichlet_eq_sum hPac hw]
  refine tendsto_finsetSum _ fun k _ => ?_
  exact (L2Tendsto.of_le_smul ENNReal.ofReal_ne_top hPle (Lk k)).tendsto_lintegral_sq
    (fun j => ((measurable_moll _ (hgint k)).aemeasurable.mono_ac hPac))
    ((hw.aestronglyMeasurable_grad k).aemeasurable.mono_ac hPac)
    (hPac.ae_le (hae2 k)) (lintegral_enorm_sq_ne_top (hgkP k))

theorem tendsto_integral_of_L2 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : ℕ → α → ℝ} {g : α → ℝ} (hf : ∀ n, Integrable (f n) μ)
    (hg : Integrable g μ) (h : L2Tendsto μ f g) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  refine tendsto_integral_of_L1 g hg.aestronglyMeasurable (Eventually.of_forall hf) ?_
  have h22 : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hb : ∀ n, ∫⁻ x, ‖f n x - g x‖ₑ ∂μ ≤
      (∫⁻ x, ‖f n x - g x‖ₑ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) := fun n => by
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ h22 (f := fun x => ‖f n x - g x‖ₑ)
      (g := fun _ => 1) (((hf n).aemeasurable.sub hg.aemeasurable).enorm) aemeasurable_const
    simpa [ENNReal.rpow_two] using hH
  have h1 : Tendsto (fun n => (∫⁻ x, ‖f n x - g x‖ₑ ^ 2 ∂μ) ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp h
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le) hb

theorem dT_sub_const (f : Torus d → ℝ) (c : ℝ) (j : Fin d) (x : Torus d) :
    Gross.dT (fun y => f y - c) j x = Gross.dT f j x := by
  unfold Gross.dT
  show fderiv ℝ (fun z => (f ∘ liftT) z - c) _ _ = _
  rw [fderiv_sub_const]

theorem gradSq_sub_const (f : Torus d → ℝ) (c : ℝ) (x : Torus d) :
    gradSq (fun y => f y - c) x = gradSq f x := by
  unfold gradSq; simp_rw [dT_sub_const]

theorem gradSq_measurable {f : Torus d → ℝ} (hf : IsSmoothT f) : Measurable (gradSq f) := by
  unfold gradSq
  exact Finset.measurable_sum _ fun j _ => ((c1T_of_smooth hf).dT_measurable j).pow_const 2

theorem gradSq_bdd {f : Torus d → ℝ} (hf : IsSmoothT f) : ∃ K, ∀ x, |gradSq f x| ≤ K := by
  have hb : ∀ j, ∃ K, ∀ y, |Gross.dT f j y| ≤ K := fun j => (c1T_of_smooth hf).dT_bounded j
  choose K hK using hb
  refine ⟨∑ j, K j ^ 2, fun x => ?_⟩
  rw [abs_of_nonneg (gradSq_nonneg f x)]
  exact Finset.sum_le_sum fun j _ => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hK j x) 2

variable {ρ : Torus d → ℝ}

theorem dirichlet_smooth (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1) {f : Torus d → ℝ}
    (hf : IsSmoothT f) :
    dirichlet (densMeasure ρ) f = ENNReal.ofReal (∫ x, ρ x * gradSq f x ∂haar d) := by
  haveI := isProbabilityMeasure_densMeasure' hρ0 hρ1
  have hPac : densMeasure ρ ≪ haar d := withDensity_absolutelyContinuous _ _
  have hae := hPac.ae_eq (Gross.weakGrad_ae_eq_dT (c1T_of_smooth hf))
  obtain ⟨K, hK⟩ := gradSq_bdd hf
  have hint : Integrable (gradSq f) (densMeasure ρ) :=
    Integrable.of_bound (gradSq_measurable hf).aestronglyMeasurable K
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hK x)
  unfold dirichlet
  calc ∫⁻ x, ENNReal.ofReal (sqNorm (weakGrad f x)) ∂densMeasure ρ
      = ∫⁻ x, ENNReal.ofReal (gradSq f x) ∂densMeasure ρ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with x hx
        rw [hx]; rfl
    _ = ENNReal.ofReal (∫ x, gradSq f x ∂densMeasure ρ) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun x => gradSq_nonneg f x)).symm
    _ = _ := by rw [integral_densMeasure' hρ0 hρ1]

theorem var_smooth (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1) {f : Torus d → ℝ}
    (hf : IsSmoothT f) (c : ℝ) :
    ∫⁻ x, ‖f x - c‖ₑ ^ 2 ∂densMeasure ρ = ENNReal.ofReal (∫ x, ρ x * (f x - c) ^ 2 ∂haar d) := by
  haveI := isProbabilityMeasure_densMeasure' hρ0 hρ1
  have hc := continuous_of_smooth hf
  obtain ⟨K, hK⟩ := SharpLSI.exists_bound_of_continuous ((hc.sub continuous_const).pow 2)
  have hint : Integrable (fun x => (f x - c) ^ 2) (densMeasure ρ) :=
    Integrable.of_bound ((hc.sub continuous_const).pow 2).aestronglyMeasurable K
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hK x)
  simp_rw [← ofReal_sq_eq_enorm_sq]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => sq_nonneg _),
    integral_densMeasure' hρ0 hρ1]

theorem isSmoothT_sub_const {f : Torus d → ℝ} (hf : IsSmoothT f) (c : ℝ) :
    IsSmoothT (fun x => f x - c) := ContDiff.sub hf contDiff_const

/-- A smooth, mean-zero test function with Rayleigh quotient below `R`. -/
theorem exists_smooth_test (hρs : IsSmoothT ρ) (hρp : ∀ x, 0 < ρ x)
    (hρ1 : ∫ x, ρ x ∂haar d = 1) {R : ℝ} (hP : poincareConst (densMeasure ρ) < ENNReal.ofReal R) :
    ∃ k : Torus d → ℝ, IsSmoothT k ∧ ∫ x, ρ x * k x ∂haar d = 0 ∧
      0 < ∫ x, ρ x * k x ^ 2 ∂haar d ∧
      ∫ x, ρ x * gradSq k x ∂haar d < R * ∫ x, ρ x * k x ^ 2 ∂haar d := by
  have hρc := continuous_of_smooth hρs
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hρp x).le
  set P := densMeasure ρ with hPdef
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_densMeasure' hρ0 hρ1
  simp only [poincareConst, iInf_lt_iff] at hP
  obtain ⟨h, ⟨hH, hvar⟩, hq⟩ := hP
  have hVfin : var P h ≠ ⊤ := (hH.2.1.evariance_lt_top).ne
  have hD : dirichlet P h < ENNReal.ofReal R * var P h :=
    (ENNReal.div_lt_iff (Or.inl hvar.ne') (Or.inl hVfin)).1 hq
  obtain ⟨f, hfs, hL2, hdir, hae⟩ := exists_smooth_seq hρc hρp hH
  have hfint : ∀ n, Integrable (f n) P := fun n =>
    SharpLSI.integrable_of_continuous (continuous_of_smooth (hfs n))
  have hhint : Integrable h P := hH.2.1.integrable one_le_two
  have han : Tendsto (fun n => ∫ x, f n x ∂P) atTop (𝓝 (∫ x, h x ∂P)) :=
    tendsto_integral_of_L2 hfint hhint hL2
  set a := ∫ x, h x ∂P with ha
  set an : ℕ → ℝ := fun n => ∫ x, f n x ∂P with han_def
  have hL2c : L2Tendsto P (fun n x => f n x - an n) (fun x => h x - a) := by
    have hc : L2Tendsto P (fun n (_ : Torus d) => -an n) (fun _ => -a) := by
      unfold L2Tendsto
      have e : ∀ n, ∫⁻ x, ‖-an n - -a‖ₑ ^ 2 ∂P = ENNReal.ofReal ((-an n - -a) ^ 2) := fun n => by
        rw [lintegral_const, measure_univ, mul_one, ofReal_sq_eq_enorm_sq]
      simp_rw [e]
      have : Tendsto (fun n => (-an n - -a) ^ 2) atTop (𝓝 0) := by
        have h1 := ((han.neg).sub_const (-a)).pow 2
        simpa using h1
      simpa using ENNReal.tendsto_ofReal this
    have := L2Tendsto.add hL2 hc (fun n => (hfint n).aemeasurable.sub hhint.aemeasurable)
    simpa [sub_eq_add_neg] using this
  have hV : Tendsto (fun n => var P (f n)) atTop (𝓝 (var P h)) := by
    refine L2Tendsto.tendsto_lintegral_sq hL2c
      (fun n => (hfint n).aemeasurable.sub aemeasurable_const)
      (hhint.aemeasurable.sub aemeasurable_const) ?_ hVfin
    filter_upwards [hae] with x hx
    exact hx.sub han
  have hlim : Tendsto (fun n => ENNReal.ofReal R * var P (f n)) atTop
      (𝓝 (ENNReal.ofReal R * var P h)) :=
    ENNReal.Tendsto.const_mul hV (Or.inr ENNReal.ofReal_ne_top)
  obtain ⟨n, hn⟩ := (hdir.eventually_lt hlim hD).exists
  have hkn : IsSmoothT (fun x => f n x - an n) := isSmoothT_sub_const (hfs n) _
  have hvn : var P (f n) = ENNReal.ofReal (∫ x, ρ x * (f n x - an n) ^ 2 ∂haar d) :=
    var_smooth hρ0 hρ1 (hfs n) (an n)
  have hdn : dirichlet P (f n) = ENNReal.ofReal (∫ x, ρ x * gradSq (fun x => f n x - an n) x ∂haar d) := by
    simp_rw [gradSq_sub_const]
    exact dirichlet_smooth hρ0 hρ1 (hfs n)
  rw [hvn, hdn] at hn
  have hR : 0 < R := by
    by_contra hR
    rw [ENNReal.ofReal_of_nonpos (not_lt.1 hR), zero_mul] at hn
    exact absurd hn (not_lt.2 zero_le)
  have hVpos : 0 < ∫ x, ρ x * (f n x - an n) ^ 2 ∂haar d := by
    by_contra hV0
    rw [ENNReal.ofReal_of_nonpos (not_lt.1 hV0), mul_zero] at hn
    exact absurd hn (not_lt.2 zero_le)
  refine ⟨fun x => f n x - an n, hkn, ?_, hVpos, ?_⟩
  · have := integral_densMeasure' hρ0 hρ1 (fun x => f n x - an n)
    rw [← this, integral_sub (hfint n) (integrable_const _)]
    simp [han_def]
  · rw [← ENNReal.ofReal_mul hR.le] at hn
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hn

end Sec8
end SharpLSI.FL
