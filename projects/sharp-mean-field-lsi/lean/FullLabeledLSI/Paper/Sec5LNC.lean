import FullLabeledLSI.Paper.Sec5LNB

/-!
# Large-N assembly C: L1, the per-level mean-field inequality
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-! ## 3. L1: the per-level mean-field inequality -/

section L1aux
variable {N : ℕ} {Q : Config N d → ℝ} {c C : ℝ}

/-- `ρ̄_S` is a probability density (for `Sᶜ` nonempty). -/
theorem barDensS_props (hQ : IsBddDens Q c C) {S : Finset (Fin N)} (hne : Sᶜ.Nonempty)
    (a : S → Torus d) :
    (∀ x, 0 ≤ barDensS Q S a x) ∧ ∫ x, barDensS Q S a x ∂haar d = 1 := by
  have hcard : 0 < Sᶜ.card := Finset.card_pos.mpr hne
  have hnpos : (0 : ℝ) < (Sᶜ.card : ℝ) := by exact_mod_cast hcard
  have hC : 0 < C := hQ.pos.trans_le ((hQ.lower 0).trans (hQ.upper 0))
  have hnn : ∀ x, 0 ≤ barDensS Q S a x := fun x => by
    unfold barDensS
    refine mul_nonneg (inv_nonneg.mpr hnpos.le) (Finset.sum_nonneg fun j _ => ?_)
    exact (div_pos hQ.pos hC).le.trans (condDensS_bounds hQ S j _ x).1
  refine ⟨hnn, ?_⟩
  unfold barDensS
  rw [integral_const_mul, integral_finsetSum _ fun j _ =>
    integrable_of_integral_eq_one' (integral_condDensS hQ S j a)]
  simp only [integral_condDensS hQ S _ a, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ hnpos.ne'

theorem measurable_barDensS (hQ : IsBddDens Q c C) (S : Finset (Fin N)) :
    Measurable (fun p : (S → Torus d) × Torus d => barDensS Q S p.1 p.2) := by
  unfold barDensS
  exact (Finset.measurable_sum _ fun i _ => measurable_condDensS hQ S i).const_mul _

theorem barCond_ae_prob (hQ : IsBddDens Q c C) {ν : Measure (Config N d)} [IsFiniteMeasure ν]
    (hν : ν = qMeasure Q) {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) :
    ∀ᵐ X ∂ν, IsProbabilityMeasure (barCond ν S X) := by
  have hne : Sᶜ.Nonempty := ⟨i, Finset.mem_compl.mpr hi⟩
  filter_upwards [barCond_ae_eq_densMeasure hQ hν (S := S)] with X hX
  rw [hX]
  obtain ⟨h0, h1⟩ := barDensS_props hQ hne (restrictS S X)
  exact isProbabilityMeasure_densMeasure' h0 h1

/-- The entropy of the explicit conditional densities relative to the minimizer is measurable in
the revealed values and uniformly bounded. -/
theorem klcond_props (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) (hQ : IsBddDens Q c C) (S : Finset (Fin N)) (i : Fin N) :
    Measurable (fun a => klDiv (densMeasure (condDensS Q S i a)) (μ : Measure (Torus d))) ∧
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a, klDiv (densMeasure (condDensS Q S i a)) (μ : Measure (Torus d)) ≤
      ENNReal.ofReal M := by
  obtain ⟨cm, cp, Lq, hcm, hB⟩ := elDensity_bounds (d := d) hyp
  obtain ⟨hqb, hqL⟩ := hB (μ : Measure (Torus d)) inferInstance
  have hμq : (μ : Measure (Torus d)) = densMeasure (elDens V W (μ : Measure (Torus d))) :=
    minimizer_eq_elDensity hyp hμ
  have hq1 : ∫ x, elDens V W (μ : Measure (Torus d)) x ∂haar d = 1 :=
    (elDensity_props hyp (μ : Measure (Torus d))).2.2
  generalize elDens V W (μ : Measure (Torus d)) = q at hqb hqL hμq hq1
  have hC : 0 < C := hQ.pos.trans_le ((hQ.lower 0).trans (hQ.upper 0))
  have hqm : Measurable q := hqL.continuous.measurable
  have hq0 : ∀ x, 0 < q x := fun x => hcm.trans_le (hqb x).1
  have hρ0 : ∀ a x, 0 ≤ condDensS Q S i a x := fun a x =>
    (div_pos hQ.pos hC).le.trans (condDensS_bounds hQ S i a x).1
  haveI : IsProbabilityMeasure (densMeasure q) :=
    isProbabilityMeasure_densMeasure' (fun x => (hq0 x).le) hq1
  set KLp : (S → Torus d) → ℝ≥0∞ := fun a =>
    ∫⁻ x, ENNReal.ofReal (klFun (condDensS Q S i a x / q x)) ∂densMeasure q with hKLp
  have hEq : ∀ a, klDiv (densMeasure (condDensS Q S i a)) (μ : Measure (Torus d)) = KLp a :=
    fun a => by
      rw [hμq]
      exact klDiv_densMeasure_eq_lintegral ((measurable_condDensS hQ S i).of_uncurry_left) hqm
        (hρ0 a) hq0 (integral_condDensS hQ S i a) hq1
  have hKLm : Measurable KLp :=
    ((measurable_klFun.comp ((measurable_condDensS hQ S i).div
      (hqm.comp measurable_snd))).ennreal_ofReal).lintegral_prod_right'
  set Bρ := max ((C / c) / cm) 1 with hBρ
  refine ⟨by simpa only [hEq] using hKLm, Bρ * Real.log Bρ + 1,
    add_nonneg (mul_nonneg (zero_le_one.trans (le_max_right _ _))
      (Real.log_nonneg (le_max_right _ _))) zero_le_one, fun a => ?_⟩
  rw [hEq]
  calc KLp a ≤ ∫⁻ _, ENNReal.ofReal (Bρ * Real.log Bρ + 1) ∂densMeasure q :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (klFun_le_of_le
          (div_nonneg (hρ0 a x) (hq0 x).le)
          ((div_le_div₀ (div_pos hC hQ.pos).le (condDensS_bounds hQ S i a x).2 hcm
            (hqb x).1).trans (le_max_left _ _)) (le_max_right _ _))
    _ = _ := by simp

/-- Per-`(S,i)` finiteness and real form of the entropy of the conditional law. -/
theorem lintegral_kl_cond (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {ν : Measure (Config N d)} [IsProbabilityMeasure ν]
    (hQ : IsBddDens Q c C) (hν : ν = qMeasure Q) {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) :
    ∫⁻ X, klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d)) ∂ν ≠ ⊤ ∧
    (∫⁻ X, klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d)) ∂ν).toReal =
      ∫ X, (klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d))).toReal ∂ν := by
  obtain ⟨hm, M, -, hM⟩ := klcond_props hyp hμ hQ S i
  have hae := condLawS_ae_eq_X hQ hi hν
  set G : Config N d → ℝ≥0∞ := fun X =>
    klDiv (densMeasure (condDensS Q S i (restrictS S X))) (μ : Measure (Torus d)) with hG
  have hGm : Measurable G := hm.comp (measurable_restrictS S)
  have h1 : ∀ᵐ X ∂ν, klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d)) = G X := by
    filter_upwards [hae] with X hX
    rw [hX]
  have hGlt : ∀ X, G X < ⊤ := fun X => (hM _).trans_lt ENNReal.ofReal_lt_top
  have hfin : ∫⁻ X, G X ∂ν ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal M ∂ν) (by simp) ?_
    exact lintegral_mono fun X => hM _
  refine ⟨by rwa [lintegral_congr_ae h1], ?_⟩
  rw [lintegral_congr_ae h1, ← integral_toReal hGm.aemeasurable (Eventually.of_forall hGlt)]
  exact integral_congr_ae (h1.mono fun X hX => by simp only [hX])

theorem condDensS_nonneg (hQ : IsBddDens Q c C) (S : Finset (Fin N)) (i : Fin N)
    (a : S → Torus d) (x : Torus d) : 0 ≤ condDensS Q S i a x := by
  have hC : 0 < C := hQ.pos.trans_le ((hQ.lower 0).trans (hQ.upper 0))
  exact (div_pos hQ.pos hC).le.trans (condDensS_bounds hQ S i a x).1

theorem klcond_integrable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) (hQ : IsBddDens Q c C) {ν : Measure (Config N d)}
    [IsFiniteMeasure ν] (S : Finset (Fin N)) (i : Fin N) :
    Integrable (fun X => (klDiv (densMeasure (condDensS Q S i (restrictS S X)))
      (μ : Measure (Torus d))).toReal) ν := by
  obtain ⟨hm, M, hM0, hM⟩ := klcond_props hyp hμ hQ S i
  refine Integrable.of_bound ((hm.comp (measurable_restrictS S)).ennreal_toReal.aestronglyMeasurable)
    M (Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_le_of_le_ofReal hM0 (hM _)

theorem measurable_Jfun_barDens (hyp : Hyp V W KV KW) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (hQ : IsBddDens Q c C) {S : Finset (Fin N)} (hne : Sᶜ.Nonempty) :
    Measurable fun a : S → Torus d => Jfun W μ (densMeasure (barDensS Q S a)) := by
  have hm : Measurable (Function.uncurry fun (a : S → Torus d) (x : Torus d) =>
      ENNReal.ofReal (barDensS Q S a x)) :=
    ENNReal.measurable_ofReal.comp (measurable_barDensS hQ S)
  let κ : Kernel (S → Torus d) (Torus d) :=
    Kernel.withDensity (Kernel.const _ (haar d)) (fun a x => ENNReal.ofReal (barDensS Q S a x))
  have hκ : ∀ a, κ a = densMeasure (barDensS Q S a) := fun a => by
    show Kernel.withDensity _ _ a = _
    rw [Kernel.withDensity_apply _ hm, Kernel.const_apply]
    rfl
  haveI : IsMarkovKernel κ := ⟨fun a => by
    rw [hκ]
    exact isProbabilityMeasure_densMeasure' (barDensS_props hQ hne a).1 (barDensS_props hQ hne a).2⟩
  have := measurable_Jfun_kernel hyp μ κ
  simpa only [hκ] using this

theorem Jfun_barDens_integrable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hQ : IsBddDens Q c C) {ν : Measure (Config N d)} [IsFiniteMeasure ν]
    {S : Finset (Fin N)} (hne : Sᶜ.Nonempty) :
    Integrable (fun X => Jfun W (μ : Measure (Torus d))
      (densMeasure (barDensS Q S (restrictS S X)))) ν := by
  obtain ⟨BK, hBK⟩ := centeredKernel_bdd hyp (μ : Measure (Torus d))
  refine Integrable.of_bound
    (((measurable_Jfun_barDens hyp (μ : Measure (Torus d)) hQ hne).comp
      (measurable_restrictS S)).aestronglyMeasurable) (BK / 2) (Eventually.of_forall fun X => ?_)
  obtain ⟨h0, h1⟩ := barDensS_props hQ hne (restrictS S X)
  haveI := isProbabilityMeasure_densMeasure' h0 h1
  rw [Real.norm_eq_abs]
  exact abs_Jfun_le_of_bdd hyp _ hBK _

end L1aux

section L1core
variable {N : ℕ} {ν : Measure (Config N d)} {Q : Config N d → ℝ} {c C : ℝ}
  {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} {s : Fin N → Fin d → Config N d → ℝ}
  {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}

theorem measurable_bMean_pair (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) (hQ : IsBddDens Q c C) (S : Finset (Fin N)) (k : Fin d) :
    Measurable (fun p : (S → Torus d) × Torus d =>
      bMean W (μ : Measure (Torus d)) (barDensS Q S p.1) p.2 k) := by
  have hac := minimizer_ac hyp hμ
  obtain ⟨hbm, -⟩ := bfixF_props hyp hac (μ := (μ : Measure (Torus d)))
  have hb2 : Measurable (fun q : Torus d × Torus d =>
      bfixF W (μ : Measure (Torus d)) q.1 q.2 k) := hbm k
  have hA := hb2.comp (show Measurable (fun q : ((S → Torus d) × Torus d) × Torus d =>
      (q.1.2, q.2)) from (measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hB := (measurable_barDensS hQ S).comp (show Measurable
      (fun q : ((S → Torus d) × Torus d) × Torus d => (q.1.1, q.2)) from
      (measurable_fst.comp measurable_fst).prodMk measurable_snd)
  simp only [Function.comp_def] at hA hB
  have h3 := ((hA.mul hB).stronglyMeasurable.integral_prod_right' (ν := haar d)).measurable
  unfold bMean
  exact h3

/-- The squared mean-field score integrand `∑ₖ (g/ρ + ∇Φ + bMean)²` at `(a, x)`. -/
noncomputable def mfH (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (Q : Config N d → ℝ) (GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ)
    (S : Finset (Fin N)) (i : Fin N) (a : S → Torus d) (x : Torus d) : ℝ :=
  ∑ k, (gradCondS Q GQ S i a x k / condDensS Q S i a x + lipGrad (PhiMF V W μ) x k +
    bMean W μ (barDensS Q S a) x k) ^ 2

theorem measurable_mfH (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) (hQ : IsBddDens Q c C)
    (hGm : ∀ p, Measurable fun y => GQ y p) (S : Finset (Fin N)) (i : Fin N) :
    Measurable (Function.uncurry (mfH V W (μ : Measure (Torus d)) Q GQ S i)) := by
  show Measurable fun p : (S → Torus d) × Torus d => ∑ k, (gradCondS Q GQ S i p.1 p.2 k /
    condDensS Q S i p.1 p.2 + lipGrad (PhiMF V W (μ : Measure (Torus d))) p.2 k +
    bMean W (μ : Measure (Torus d)) (barDensS Q S p.1) p.2 k) ^ 2
  refine Finset.measurable_sum _ fun k _ => ?_
  have h1 := measurable_gradCondS (S := S) (i := i) hQ hGm k
  have h2 := measurable_condDensS hQ S i
  have h3 : Measurable fun p : (S → Torus d) × Torus d =>
      lipGrad (PhiMF V W (μ : Measure (Torus d))) p.2 k :=
    (measurable_lipGrad (continuous_PhiMF hyp) k).comp measurable_snd
  have h4 := measurable_bMean_pair hyp hμ hQ S k
  exact (((h1.div h2).add h3).add h4).pow_const 2

theorem elDiss_eq_mfH (hQ : IsBddDens Q c C) (μ : Measure (Torus d)) (S : Finset (Fin N))
    (i : Fin N) (a : S → Torus d) :
    elDiss V W μ (condDensS Q S i a) (gradCondS Q GQ S i a) (barDensS Q S a) =
      ∫⁻ x, ENNReal.ofReal (condDensS Q S i a x) *
        ENNReal.ofReal (mfH V W μ Q GQ S i a x) ∂haar d := by
  unfold elDiss
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_mul (condDensS_nonneg hQ S i a x)]
  rfl

theorem measurable_elDiss_cond (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) (hQ : IsBddDens Q c C)
    (hGm : ∀ p, Measurable fun y => GQ y p) (S : Finset (Fin N)) (i : Fin N) :
    Measurable fun a : S → Torus d => elDiss V W (μ : Measure (Torus d)) (condDensS Q S i a)
      (gradCondS Q GQ S i a) (barDensS Q S a) := by
  have : (fun a : S → Torus d => elDiss V W (μ : Measure (Torus d)) (condDensS Q S i a)
      (gradCondS Q GQ S i a) (barDensS Q S a)) = fun a => ∫⁻ x, ENNReal.ofReal (condDensS Q S i a x) *
        ENNReal.ofReal (mfH V W (μ : Measure (Torus d)) Q GQ S i a x) ∂haar d :=
    funext fun a => elDiss_eq_mfH hQ _ S i a
  rw [this]
  exact ((ENNReal.measurable_ofReal.comp (measurable_condDensS hQ S i)).mul
    (ENNReal.measurable_ofReal.comp (measurable_mfH hyp hμ hQ hGm S i))).lintegral_prod_right'

theorem measurable_pair_restrict (S : Finset (Fin N)) (i : Fin N)
    {F : (S → Torus d) → Torus d → ℝ} (hF : Measurable (Function.uncurry F)) :
    Measurable fun X : Config N d => F (restrictS S X) (X i) :=
  hF.comp ((measurable_restrictS S).prodMk (measurable_pi_apply i))

/-- **(ii) The `ν`-average of the conditional dissipation is the mean-field score energy.** -/
theorem integral_elDiss_toReal (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) [IsProbabilityMeasure ν]
    (hS : ScoreData V W (μ : Measure (Torus d)) ν Q c C GQ s bF bΔ Bb)
    {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) :
    Integrable (fun X => (elDiss V W (μ : Measure (Torus d)) (condDensS Q S i (restrictS S X))
      (gradCondS Q GQ S i (restrictS S X)) (barDensS Q S (restrictS S X))).toReal) ν ∧
    ∫ X, (elDiss V W (μ : Measure (Torus d)) (condDensS Q S i (restrictS S X))
      (gradCondS Q GQ S i (restrictS S X)) (barDensS Q S (restrictS S X))).toReal ∂ν =
    ∫ X, ∑ k : Fin d, (condExp (revSigma S i) ν
        (fun Y => s i k Y - Gpart bF bΔ N Y i k) X + BS bF ν S X (X i) k) ^ 2 ∂ν := by
  classical
  have hQ := hS.dens
  have hν := hS.eq
  obtain ⟨H, hH⟩ : ∃ H : (S → Torus d) → Torus d → ℝ,
      H = mfH V W (μ : Measure (Torus d)) Q GQ S i := ⟨_, rfl⟩
  have hHm : Measurable (Function.uncurry H) := by
    rw [hH]; exact measurable_mfH hyp hμ hQ hS.gradM S i
  set T : Config N d → ℝ := fun X => ∑ k : Fin d, (condExp (revSigma S i) ν
        (fun Y => s i k Y - Gpart bF bΔ N Y i k) X + BS bF ν S X (X i) k) ^ 2 with hT
  have hHX : Measurable fun X : Config N d => H (restrictS S X) (X i) :=
    measurable_pair_restrict S i hHm
  have hk : ∀ᵐ X ∂ν, ∀ k, gradCondS Q GQ S i (restrictS S X) (X i) k /
      condDensS Q S i (restrictS S X) (X i) +
      lipGrad (PhiMF V W (μ : Measure (Torus d))) (X i) k =
      condExp (revSigma S i) ν (fun Y => s i k Y - Gpart bF bΔ N Y i k) X := by
    rw [ae_all_iff]
    exact fun k => condScore_ae_eq hyp hμ hS hi k
  have hTH : T =ᵐ[ν] fun X => H (restrictS S X) (X i) := by
    filter_upwards [hk, bMean_ae_eq_BS hyp hμ hS hi] with X h1 h2
    simp only [hT, hH, mfH]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h2 k, h1 k]
  have hsm : ∀ k, MemLp (fun Y => s i k Y - Gpart bF bΔ N Y i k) 2 ν := fun k => by
    have h1 : MemLp (s i k) 2 ν :=
      (memLp_two_iff_integrable_sq (hS.sM i k).aestronglyMeasurable).mpr (hS.sL2 i k)
    have h2 : MemLp (fun Y => Gpart bF bΔ N Y i k) 2 ν :=
      MemLp.of_bound (measurable_Gpart hS.force i k).aestronglyMeasurable
        ((N : ℝ)⁻¹ * ((N : ℝ) * Bb + Bb)) (Eventually.of_forall fun X => by
          rw [Real.norm_eq_abs]; exact abs_Gpart_le hS.force X i k)
    exact h1.sub h2
  have hu : ∀ k, MemLp (condExp (revSigma S i) ν
      (fun Y => s i k Y - Gpart bF bΔ N Y i k)) 2 ν := fun k => (hsm k).condExp one_le_two
  have hw : ∀ k, Measurable fun X : Config N d =>
      bMean W (μ : Measure (Torus d)) (barDensS Q S (restrictS S X)) (X i) k := fun k =>
    measurable_pair_restrict S i
      (F := fun a x => bMean W (μ : Measure (Torus d)) (barDensS Q S a) x k)
      (measurable_bMean_pair hyp hμ hQ S k)
  have hBSb : ∀ᵐ X ∂ν, ∀ k, |BS bF ν S X (X i) k| ≤ Bb := by
    filter_upwards [barCond_ae_prob hQ hν hi] with X hX k
    have := hX
    exact abs_integral_le_of_prob (barCond ν S X) _ (fun y => hS.force.bound _ y k)
  have hv : ∀ k, MemLp (fun X => BS bF ν S X (X i) k) 2 ν := fun k => by
    refine MemLp.of_bound ?_ Bb ?_
    · exact (hw k).aestronglyMeasurable.congr
        ((bMean_ae_eq_BS hyp hμ hS hi).mono fun X hX => hX k)
    · filter_upwards [hBSb] with X hX
      rw [Real.norm_eq_abs]
      exact hX k
  have hTi : Integrable T ν :=
    integrable_finsetSum _ fun k _ => ((hu k).add (hv k)).integrable_sq
  have hnonnegT : 0 ≤ᵐ[ν] T :=
    Eventually.of_forall fun X => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hF : Measurable (Function.uncurry fun a x => ENNReal.ofReal (H a x)) :=
    ENNReal.measurable_ofReal.comp hHm
  have hpair : ∫⁻ X, ENNReal.ofReal (H (restrictS S X) (X i)) ∂ν =
      ∫⁻ X, elDiss V W (μ : Measure (Torus d)) (condDensS Q S i (restrictS S X))
        (gradCondS Q GQ S i (restrictS S X)) (barDensS Q S (restrictS S X)) ∂ν :=
    (lintegral_pair_eq_lintegral_condDensS hQ hν hi hF).trans
      (lintegral_congr fun X => by rw [hH]; exact (elDiss_eq_mfH hQ _ S i (restrictS S X)).symm)
  have hEDX : Measurable fun X : Config N d => elDiss V W (μ : Measure (Torus d))
      (condDensS Q S i (restrictS S X)) (gradCondS Q GQ S i (restrictS S X))
      (barDensS Q S (restrictS S X)) :=
    (measurable_elDiss_cond hyp hμ hQ hS.gradM S i).comp (measurable_restrictS S)
  have hTl : ∫⁻ X, ENNReal.ofReal (T X) ∂ν = ∫⁻ X, ENNReal.ofReal (H (restrictS S X) (X i)) ∂ν :=
    lintegral_congr_ae (hTH.mono fun X hX => congrArg ENNReal.ofReal hX)
  have hfin : ∫⁻ X, elDiss V W (μ : Measure (Torus d)) (condDensS Q S i (restrictS S X))
        (gradCondS Q GQ S i (restrictS S X)) (barDensS Q S (restrictS S X)) ∂ν ≠ ⊤ := by
    rw [← hpair, ← hTl]
    exact hTi.lintegral_lt_top.ne
  refine ⟨integrable_toReal_of_lintegral_ne_top hEDX.aemeasurable hfin, ?_⟩
  rw [integral_toReal hEDX.aemeasurable (ae_lt_top hEDX hfin),
    integral_eq_lintegral_of_nonneg_ae hnonnegT hTi.aestronglyMeasurable, hTl, hpair]

end L1core

section L1
variable {N : ℕ} {ν : Measure (Config N d)} {Q : Config N d → ℝ} {c C : ℝ}
  {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} {s : Fin N → Fin d → Config N d → ℝ}
  {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}

/-- **`hRev` in real form:** for `j < N`,
`(hRev ν μ j).toReal = avg1R N j (fun S i => ∫ (klDiv (condLawS ν S i X_S) μ).toReal dν)`.
Proof: unfold `hRev`; `klDiv (condLawS …) μ ≤ ofReal (B log B + 1) < ⊤` ν-a.e. (use `condLawS_ae_eq_X`,
`klDiv_densMeasure_eq_lintegral`/`klFun_le_of_le` of Defective25, with the density of `μ`
bounded below: `elDensity_bounds`, `minimizer_eq_elDensity`), then `integral_toReal` and
`ENNReal.toReal_sum`/`toReal_mul`.  Same argument as `integral_gap_eq` (Defective25).  ~60 lines. -/
theorem hRev_toReal_eq (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) [IsProbabilityMeasure ν]
    (hS : ScoreData V W (μ : Measure (Torus d)) ν Q c C GQ s bF bΔ Bb) {j : ℕ} (hj : j < N) :
    (hRev ν (μ : Measure (Torus d)) j).toReal =
      avg1R N j fun S i => ∫ X, (klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d))).toReal ∂ν := by
  classical
  have hQ := hS.dens
  have hν := hS.eq
  have hne : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, Sᶜ.Nonempty := by
    intro S hS'
    rw [Finset.mem_powersetCard] at hS'
    rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin, hS'.2]
    omega
  have hℓ : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∀ i ∈ Sᶜ,
      (∫⁻ X, klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d)) ∂ν ≠ ⊤) ∧
      (∫⁻ X, klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d)) ∂ν).toReal =
        ∫ X, (klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d))).toReal ∂ν :=
    fun S _ i hi => lintegral_kl_cond hyp hμ hQ hν (Finset.mem_compl.mp hi)
  have hterm : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
      (((Sᶜ.card : ℝ≥0∞)⁻¹) * ∑ i ∈ Sᶜ,
        ∫⁻ X, klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d)) ∂ν) ≠ ⊤ := by
    intro S hS'
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr
      (by exact_mod_cast (Finset.card_pos.mpr (hne S hS')).ne'))
      (ENNReal.sum_ne_top.mpr fun i hi => (hℓ S hS' i hi).1)
  unfold hRev avg1R
  rw [if_pos hj, ENNReal.toReal_mul, ENNReal.toReal_sum hterm, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  congr 1
  refine Finset.sum_congr rfl fun S hS' => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum fun i hi => (hℓ S hS' i hi).1]
  congr 1
  exact Finset.sum_congr rfl fun i hi => (hℓ S hS' i hi).2

/-- `cps_j = condMeanS ν 2 (Bk W μ) j = E_S E_ν J(ρ̄_S)`.
Proof: `Jfun_eq_pi` (needs `IsProbabilityMeasure (barCond ν S X)` ν-a.e., from
`barCond_ae_eq_densMeasure`+`integral_barDensS`/`isProbabilityMeasure_densMeasure'`), then
`avg1R N j (fun S _ => F S) = (choose N j)⁻¹ ∑_S F S` when `Sᶜ ≠ ∅` (`j < N`).  ~40 lines. -/
theorem condMeanS_eq_avg1R_Jfun (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) [IsProbabilityMeasure ν]
    (hS : ScoreData V W (μ : Measure (Torus d)) ν Q c C GQ s bF bΔ Bb) {j : ℕ} (hj : j < N) :
    condMeanS ν 2 (Bk W (μ : Measure (Torus d))) j =
      avg1R N j fun S _ => ∫ X, Jfun W (μ : Measure (Torus d)) (barCond ν S X) ∂ν := by
  classical
  have hQ := hS.dens
  have hν := hS.eq
  unfold condMeanS avg1R
  congr 1
  refine Finset.sum_congr rfl fun S hS' => ?_
  rw [Finset.mem_powersetCard] at hS'
  have hne : Sᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin, hS'.2]
    omega
  obtain ⟨i, hi⟩ := hne
  have hn : (Sᶜ.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨i, hi⟩).ne'
  have e : ∫ X, (∫ z, Bk W (μ : Measure (Torus d)) z ∂Measure.pi
        (fun _ : Fin 2 => barCond ν S X)) ∂ν =
      ∫ X, Jfun W (μ : Measure (Torus d)) (barCond ν S X) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [barCond_ae_prob hQ hν (Finset.mem_compl.mp hi)] with X hX
    have := hX
    rw [Jfun_eq_pi hyp (μ : Measure (Torus d)) (barCond ν S X)]
    rfl
  rw [e, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- **Mean-field inequality for one revealed set `S`.**  For `1 ≤ |Sᶜ|`, `r₀ ≤ r_ms`:
`2 r₀ ( n⁻¹ Σ_{i∈Sᶜ} E_ν H(ρ_{S,i}(X_S)|μ) + E_ν J(ρ̄_S) ) ≤
   n⁻¹ Σ_{i∈Sᶜ} E_ν |E[s_i - G_i | X_S, X_i] + B_S(X_i)|²`,   `n = |Sᶜ|`.
Proof: for a.e. `a`, `two_r_meanfield_real_le hyp hμ hr₀ hrr hR (h := ae_isBddH1Dens_condDensS)` with
`R = Sᶜ`, `ρ i = condDensS Q S i a`, `g i = gradCondS Q GQ S i a`; the `avgDens` is `barDensS` (by `rfl`).
Evaluate at `a = X_S`, integrate in `ν` (`ae_restrictS_of_ae_volume`), and identify:
(i) `condLawS = densMeasure (condDensS …)` (`condLawS_ae_eq_X`), `barCond = densMeasure barDensS`
(`barCond_ae_eq_densMeasure`); (ii) `∫ν (elDiss …(X_S)).toReal = ∫ν Σ_k (g/ρ + ∇Φ + bMean)²(X_S, X_i)` by
`lintegral_pair_eq_lintegral_condDensS` (convert `ofReal`/`toReal`, all finite since bounded);
(iii) `g/ρ + ∇Φ = E[s-G|𝒢]` by `condScore_ae_eq`, `bMean = BS` by `bMean_ae_eq_BS`.
Integrability of each term is by boundedness.  Estimate: ~150 lines (the heaviest piece; if too large,
split (ii) as `integral_elDiss_toReal` with the displayed statement). -/
theorem meanfield_S (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) [IsProbabilityMeasure ν]
    (hS : ScoreData V W (μ : Measure (Torus d)) ν Q c C GQ s bF bΔ Bb)
    {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hrr : ENNReal.ofReal r₀ ≤ rMs V W)
    (S : Finset (Fin N)) (hS1 : 1 ≤ Sᶜ.card) :
    2 * r₀ * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
        ∫ X, (klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d))).toReal ∂ν +
      ∫ X, Jfun W (μ : Measure (Torus d)) (barCond ν S X) ∂ν) ≤
    (Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ, ∫ X, ∑ k : Fin d,
      (condExp (revSigma S i) ν (fun Y => s i k Y - Gpart bF bΔ N Y i k) X +
        BS bF ν S X (X i) k) ^ 2 ∂ν := by
  classical
  have hQ := hS.dens
  have hν := hS.eq
  obtain ⟨i0, hi0⟩ : Sᶜ.Nonempty := Finset.card_pos.mp hS1
  have hne : Sᶜ.Nonempty := ⟨i0, hi0⟩
  have hn : 0 < (Sᶜ.card : ℝ) := by exact_mod_cast hS1
  -- Step A: the pointwise mean-field inequality for a.e. revealed values
  have hA : ∀ᵐ a ∂(volume : Measure (S → Torus d)),
      2 * r₀ * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
        (klDiv (densMeasure (condDensS Q S i a)) (μ : Measure (Torus d))).toReal +
        Jfun W (μ : Measure (Torus d)) (densMeasure (barDensS Q S a))) ≤
      (Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ, (elDiss V W (μ : Measure (Torus d)) (condDensS Q S i a)
        (gradCondS Q GQ S i a) (barDensS Q S a)).toReal := by
    filter_upwards [ae_isBddH1Dens_condDensS hS S] with a ha
    exact two_r_meanfield_real_le hyp hμ hr₀ hrr hne ha
  have hB : ∀ᵐ X ∂ν,
      2 * r₀ * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
        (klDiv (densMeasure (condDensS Q S i (restrictS S X))) (μ : Measure (Torus d))).toReal +
        Jfun W (μ : Measure (Torus d)) (densMeasure (barDensS Q S (restrictS S X)))) ≤
      (Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ, (elDiss V W (μ : Measure (Torus d))
        (condDensS Q S i (restrictS S X)) (gradCondS Q GQ S i (restrictS S X))
        (barDensS Q S (restrictS S X))).toReal := by
    have hB' := ae_restrictS_of_ae_volume S hQ.meas hA
    rw [hν]
    exact hB'
  -- integrability
  have hKLi : ∀ i ∈ Sᶜ, Integrable (fun X => (klDiv (densMeasure (condDensS Q S i (restrictS S X)))
      (μ : Measure (Torus d))).toReal) ν := fun i _ => klcond_integrable hyp hμ hQ S i
  have hJi := Jfun_barDens_integrable (ν := ν) hyp (μ := μ) hQ (S := S) hne
  have hED : ∀ i ∈ Sᶜ, _ := fun i hi =>
    integral_elDiss_toReal hyp hμ hS (Finset.mem_compl.mp hi)
  have hLi : Integrable (fun X => 2 * r₀ * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
        (klDiv (densMeasure (condDensS Q S i (restrictS S X))) (μ : Measure (Torus d))).toReal +
        Jfun W (μ : Measure (Torus d)) (densMeasure (barDensS Q S (restrictS S X))))) ν :=
    (((integrable_finsetSum _ hKLi).const_mul _).add hJi).const_mul _
  have hRi : Integrable (fun X => (Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ, (elDiss V W (μ : Measure (Torus d))
        (condDensS Q S i (restrictS S X)) (gradCondS Q GQ S i (restrictS S X))
        (barDensS Q S (restrictS S X))).toReal) ν :=
    (integrable_finsetSum _ fun i hi => (hED i hi).1).const_mul _
  have hL : ∫ X, 2 * r₀ * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
        (klDiv (densMeasure (condDensS Q S i (restrictS S X))) (μ : Measure (Torus d))).toReal +
        Jfun W (μ : Measure (Torus d)) (densMeasure (barDensS Q S (restrictS S X)))) ∂ν =
      2 * r₀ * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ, ∫ X,
        (klDiv (densMeasure (condDensS Q S i (restrictS S X))) (μ : Measure (Torus d))).toReal ∂ν +
        ∫ X, Jfun W (μ : Measure (Torus d)) (densMeasure (barDensS Q S (restrictS S X))) ∂ν) := by
    rw [integral_const_mul, integral_add ((integrable_finsetSum _ hKLi).const_mul _) hJi,
      integral_const_mul, integral_finsetSum _ hKLi]
  have hR : ∫ X, (Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ, (elDiss V W (μ : Measure (Torus d))
        (condDensS Q S i (restrictS S X)) (gradCondS Q GQ S i (restrictS S X))
        (barDensS Q S (restrictS S X))).toReal ∂ν =
      (Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ, ∫ X, (elDiss V W (μ : Measure (Torus d))
        (condDensS Q S i (restrictS S X)) (gradCondS Q GQ S i (restrictS S X))
        (barDensS Q S (restrictS S X))).toReal ∂ν := by
    rw [integral_const_mul, integral_finsetSum _ fun i hi => (hED i hi).1]
  -- identification of the pieces
  have e1 : ∀ i ∈ Sᶜ, ∫ X, (klDiv (condLawS ν S i (restrictS S X))
      (μ : Measure (Torus d))).toReal ∂ν = ∫ X,
        (klDiv (densMeasure (condDensS Q S i (restrictS S X))) (μ : Measure (Torus d))).toReal ∂ν :=
    fun i hi => integral_congr_ae
      ((condLawS_ae_eq_X hQ (Finset.mem_compl.mp hi) hν).mono fun X hX => by simp only [hX])
  have e2 : ∫ X, Jfun W (μ : Measure (Torus d)) (barCond ν S X) ∂ν =
      ∫ X, Jfun W (μ : Measure (Torus d)) (densMeasure (barDensS Q S (restrictS S X))) ∂ν :=
    integral_congr_ae
      ((barCond_ae_eq_densMeasure hQ hν (S := S)).mono fun X hX => by simp only [hX])
  calc 2 * r₀ * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
        ∫ X, (klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d))).toReal ∂ν +
        ∫ X, Jfun W (μ : Measure (Torus d)) (barCond ν S X) ∂ν)
      = 2 * r₀ * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ, ∫ X,
        (klDiv (densMeasure (condDensS Q S i (restrictS S X))) (μ : Measure (Torus d))).toReal ∂ν +
        ∫ X, Jfun W (μ : Measure (Torus d)) (densMeasure (barDensS Q S (restrictS S X))) ∂ν) := by
        rw [Finset.sum_congr rfl e1, e2]
    _ = _ := hL.symm
    _ ≤ _ := integral_mono_ae hLi hRi hB
    _ = _ := hR
    _ = _ := by rw [Finset.sum_congr rfl fun i hi => (hED i hi).2]

/-- **L1.  The per-level mean-field inequality in Section-5 quantities.**  For `j < N`, `r₀ ≥ 0`,
`ofReal r₀ ≤ r_ms`:
`2 r₀ (h_j + cps_j) ≤ mfDiss j`,  `h_j = (hRev ν μ j).toReal`, `cps_j = condMeanS ν 2 (Bk W μ) j`.
Proof: average `meanfield_S` over `S ∈ powersetCard j` (`avg1R` is a positive linear functional:
`Finset.mul_sum`, `Finset.sum_le_sum`) and rewrite with `hRev_toReal_eq`, `condMeanS_eq_avg1R_Jfun`
(with `avg1R_const`-type lemma `avg1R N j (fun S _ => x) = x`).  ~40 lines. -/
theorem level_meanfield (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) [IsProbabilityMeasure ν]
    (hS : ScoreData V W (μ : Measure (Torus d)) ν Q c C GQ s bF bΔ Bb)
    {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hrr : ENNReal.ofReal r₀ ≤ rMs V W) {j : ℕ} (hj : j < N) :
    2 * r₀ * ((hRev ν (μ : Measure (Torus d)) j).toReal +
        condMeanS ν 2 (Bk W (μ : Measure (Torus d))) j) ≤ mfDiss bF bΔ ν s j := by
  classical
  rw [hRev_toReal_eq hyp hμ hS hj, condMeanS_eq_avg1R_Jfun hyp hμ hS hj]
  unfold mfDiss avg1R
  have hkey : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
      2 * r₀ * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
          ∫ X, (klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d))).toReal ∂ν +
        ∫ X, Jfun W (μ : Measure (Torus d)) (barCond ν S X) ∂ν) ≤
      (Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ, ∫ X, ∑ k : Fin d,
        (condExp (revSigma S i) ν (fun Y => s i k Y - Gpart bF bΔ N Y i k) X +
          BS bF ν S X (X i) k) ^ 2 ∂ν := by
    intro S hS'
    rw [Finset.mem_powersetCard] at hS'
    refine meanfield_S hyp hμ hS hr₀ hrr S ?_
    rw [Finset.card_compl, Fintype.card_fin, hS'.2]
    omega
  have hcn : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, (Sᶜ.card : ℝ) ≠ 0 := by
    intro S hS'
    rw [Finset.mem_powersetCard] at hS'
    have : 0 < Sᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin, hS'.2]; omega
    exact_mod_cast this.ne'
  have hconst : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∀ x : ℝ,
      (Sᶜ.card : ℝ)⁻¹ * ∑ _i ∈ Sᶜ, x = x := by
    intro S hS' x
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp [hcn S hS']
  beta_reduce
  rw [Finset.sum_congr rfl fun S hS' => hconst S hS' (∫ X, Jfun W (μ : Measure (Torus d))
    (barCond ν S X) ∂ν), ← mul_add, ← Finset.sum_add_distrib]
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hkey)
    (inv_nonneg.2 (Nat.cast_nonneg _)))
  rw [← Finset.mul_sum]
  ring

end L1


end SharpLSI.FL
