import SharpSymmetricLSI.Paper.EnergyParseval2

/-!
# Parseval for the Dirichlet form, conclusion (Phase 3, lane D; R24)
-/

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

theorem norm_toLp_sub_sq {f g : Torus d → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp - hg.toLp‖ ^ 2 = ∫ x, (f x - g x) ^ 2 ∂μ := by
  rw [← MemLp.toLp_sub, ← real_inner_self_eq_norm_sq, inner_toLp (hf.sub hg) (hf.sub hg)]
  congr 1; funext x; simp [sq]

theorem norm_toLp_sub_Lp_sq {f : Torus d → ℝ} (hf : MemLp f 2 μ) (w : Lp ℝ 2 μ) :
    ‖hf.toLp - w‖ ^ 2 = ∫ x, (f x - w x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub hf.toLp w, hf.coeFn_toLp] with x h1 h2
  rw [h1, Pi.sub_apply, h2, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
  simp [sq]

/-- `L²(μ)` convergence gives `L¹(m)` convergence when `m ≤ C μ`. -/
theorem lintegral_le_of_L2 {C : ℝ} (hlow : (haar d) ≤ ENNReal.ofReal C • μ) {h : Torus d → ℝ}
    (hh : MemLp h 2 μ) :
    ∫⁻ y, ‖h y‖ₑ ∂haar d ≤ ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt (∫ y, h y ^ 2 ∂μ)) := by
  calc ∫⁻ y, ‖h y‖ₑ ∂haar d ≤ ∫⁻ y, ‖h y‖ₑ ∂(ENNReal.ofReal C • μ) := lintegral_mono' hlow le_rfl
    _ = ENNReal.ofReal C * ∫⁻ y, ‖h y‖ₑ ∂μ := by rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ _ := by
        gcongr
        rw [← ofReal_integral_norm_eq_lintegral_enorm (hh.integrable one_le_two)]
        exact ENNReal.ofReal_le_ofReal (by
          simp_rw [Real.norm_eq_abs]; exact integral_abs_le_sqrt' hh)

section main
variable (hac : μ ≪ haar d) {C : ℝ} (hlow : haar d ≤ ENNReal.ofReal C • μ)
  (he : IsRefEigenbasis μ e lam)
include hac hlow he

/-- **Parseval for the Dirichlet form**: `∫|∇f|² dμ = ∑ λᵢ ⟨f,eᵢ⟩²`. -/
theorem energy_parseval {f : Torus d → ℝ} (hf : MemH1 μ f) :
    HasSum (fun i => lam i * (∫ y, f y * e i y ∂μ) ^ 2)
      (dirPair μ (weakGrad f) (weakGrad f)) := by
  set c : ℕ → ℝ := fun i => ∫ y, f y * e i y ∂μ with hc
  have hge := eig_memLp hac he
  have hgf : ∀ k, MemLp (fun x => weakGrad f x k) 2 μ := memLp_grad_comp hac hf
  have hlamnn : ∀ i, 0 ≤ lam i * c i ^ 2 := fun i => mul_nonneg (lam_nonneg hac he i) (sq_nonneg _)
  set S : ℕ → Torus d → Fin d → ℝ := fun n x k => ∑ i ∈ Finset.range n, c i * weakGrad (e i) x k
    with hSdef
  have hS : ∀ n k, MemLp (fun x => S n x k) 2 μ := fun n k =>
    memLp_finset_sum _ fun i _ => (hge i k).const_mul (c i)
  have hdef := defect_identity hac he hf
  -- Bessel and summability
  have hbes : ∀ n, ∑ i ∈ Finset.range n, lam i * c i ^ 2 ≤ dirPair μ (weakGrad f) (weakGrad f) :=
    fun n => by
      have h0 : 0 ≤ dirPair μ (fun x k => weakGrad f x k - S n x k)
          (fun x k => weakGrad f x k - S n x k) :=
        integral_nonneg fun x => Finset.sum_nonneg fun k _ => mul_self_nonneg _
      have := hdef n
      linarith
  have hsum : Summable fun i => lam i * c i ^ 2 := summable_of_sum_range_le hlamnn hbes
  -- the gradient partial sums are Cauchy in `L²(μ)`, componentwise
  have hcauchy : ∀ k, CauchySeq fun n => (hS n k).toLp := by
    intro k
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have ht := hsum.tendsto_sum_tsum_nat
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ht) (ε ^ 2 / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    have hsq : ‖(hS n k).toLp - (hS N k).toLp‖ ^ 2 ≤
        ∑ i ∈ Finset.Ico N n, lam i * c i ^ 2 := by
      rw [norm_toLp_sub_sq]
      have hdiff : ∀ x, S n x k - S N x k = ∑ i ∈ Finset.Ico N n, c i * weakGrad (e i) x k :=
        fun x => by
          simp only [hSdef]
          rw [← Finset.sum_range_add_sum_Ico _ hn]; ring
      simp_rw [hdiff]
      rw [← dirPair_eigsum hac he c (Finset.Ico N n)]
      unfold dirPair
      refine integral_mono (((memLp_finset_sum _ fun i _ => (hge i k).const_mul (c i))).integrable_sq)
        (dirPair_integrable (fun k => memLp_finset_sum _ fun i _ => (hge i k).const_mul (c i))
          (fun k => memLp_finset_sum _ fun i _ => (hge i k).const_mul (c i))) fun x => ?_
      rw [sq]
      exact Finset.single_le_sum (f := fun k' => (∑ i ∈ Finset.Ico N n, c i * weakGrad (e i) x k') *
        (∑ i ∈ Finset.Ico N n, c i * weakGrad (e i) x k')) (fun k' _ => mul_self_nonneg _)
        (Finset.mem_univ k)
    have htail : ∑ i ∈ Finset.Ico N n, lam i * c i ^ 2 < ε ^ 2 := by
      have h1 := hN n hn
      have h2 := hN N le_rfl
      rw [Real.dist_eq] at h1 h2
      rw [Finset.sum_Ico_eq_sub _ hn]
      have := abs_sub_lt_iff.mp h1
      have := abs_sub_lt_iff.mp h2
      linarith
    have := hsq.trans_lt htail
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).mp this
  choose w hw using fun k => cauchySeq_tendsto_of_complete (hcauchy k)
  -- `∫ (S_n - w)² → 0`
  have hSw : ∀ k, Tendsto (fun n => ∫ x, (S n x k - w k x) ^ 2 ∂μ) atTop (𝓝 0) := by
    intro k
    have h1 : Tendsto (fun n => ‖(hS n k).toLp - w k‖ ^ 2) atTop (𝓝 0) := by
      have := ((continuous_pow 2).tendsto _).comp ((tendsto_iff_norm_sub_tendsto_zero.mp (hw k)))
      simpa [Function.comp_def] using this
    have e1 : ∀ n, ‖(hS n k).toLp - w k‖ ^ 2 = ∫ x, (S n x k - w k x) ^ 2 ∂μ := fun n =>
      norm_toLp_sub_Lp_sq (hS n k) (w k)
    simpa [e1] using h1
  -- closedness: `∇f = w` a.e.
  have hlowi : ∀ {h : Torus d → ℝ}, MemLp h 2 μ → Integrable h (haar d) := fun {h} hh =>
    ((hh.integrable one_le_two).smul_measure ENNReal.ofReal_ne_top).mono_measure hlow
  set F : ℕ → Torus d → ℝ := fun n x => f x - ∑ i ∈ Finset.range n, c i * e i x
  have hFL : ∀ n, MemLp (F n) 2 μ := fun n =>
    hf.2.1.sub (memLp_finset_sum _ fun i _ => (he.memLp i).const_mul (c i))
  have hFw : ∀ n, IsWeakGrad (F n) (fun x k => weakGrad f x k - S n x k) := fun n => by
    have h1 := isWeakGrad_finsetSum (Finset.range n) fun i _ =>
      (isWeakGrad_weakGrad (he.memH1 i).1).cmul (c i)
    have h2 := (isWeakGrad_weakGrad hf.1).add (h1.cmul (-1))
    convert h2 using 1
    · funext x; simp only [F]; ring
    · funext x k; simp only [hSdef]; ring
  have hwL : ∀ k, MemLp (fun x => w k x) 2 μ := fun k => Lp.memLp (w k)
  have hlim := isWeakGrad_of_tendsto (F := F) (G := fun n x k => weakGrad f x k - S n x k)
    (f := fun _ => (0 : ℝ)) (g := fun x k => weakGrad f x k - w k x) hFw
    (fun n => hlowi (hFL n)) (fun n k => hlowi ((hgf k).sub (hS n k)))
    (integrable_const _) (fun k => hlowi ((hgf k).sub (hwL k)))
    (by
      have ht := tendsto_partial_sum he hf.2.1
      have hup : Tendsto (fun n => ENNReal.ofReal C *
          ENNReal.ofReal (Real.sqrt (∫ y, (F n y) ^ 2 ∂μ))) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C)
          ((ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_sqrt.tendsto _).comp ht))
          (Or.inr ENNReal.ofReal_ne_top)
        simpa [Function.comp_def] using this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun n => bot_le) (fun n => ?_)
      have := lintegral_le_of_L2 hlow (hFL n)
      refine le_of_eq_of_le (lintegral_congr fun y => ?_) this
      simp)
    (fun k => by
      have hup : Tendsto (fun n => ENNReal.ofReal C *
          ENNReal.ofReal (Real.sqrt (∫ y, (S n y k - w k y) ^ 2 ∂μ))) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C)
          ((ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_sqrt.tendsto _).comp (hSw k)))
          (Or.inr ENNReal.ofReal_ne_top)
        simpa [Function.comp_def] using this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun n => bot_le) (fun n => ?_)
      have := lintegral_le_of_L2 hlow ((hS n k).sub (hwL k))
      refine le_of_eq_of_le (lintegral_congr fun y => ?_) this
      simp only [Pi.sub_apply]
      rw [← enorm_neg]; congr 1; ring)
  have hgw : (fun x k => weakGrad f x k - w k x) =ᵐ[haar d] 0 :=
    weakGrad_ae_unique hlim (isWeakGrad_const 0)
  have hgwμ := hac.ae_le hgw
  -- the defect tends to zero
  have hD : Tendsto (fun n => dirPair μ (fun x k => weakGrad f x k - S n x k)
      (fun x k => weakGrad f x k - S n x k)) atTop (𝓝 0) := by
    have e1 : ∀ n, dirPair μ (fun x k => weakGrad f x k - S n x k)
        (fun x k => weakGrad f x k - S n x k) = ∑ k, ∫ x, (S n x k - w k x) ^ 2 ∂μ := fun n => by
      unfold dirPair
      show ∫ x, ∑ k, (weakGrad f x k - S n x k) * (weakGrad f x k - S n x k) ∂μ = _
      rw [← integral_finset_sum (f := fun k x => (S n x k - w k x) ^ 2) _ fun k _ =>
        ((hS n k).sub (hwL k)).integrable_sq]
      refine integral_congr_ae ?_
      filter_upwards [hgwμ] with x hx
      refine Finset.sum_congr rfl fun k _ => ?_
      have := congrFun hx k
      simp only [Pi.zero_apply, sub_eq_zero] at this
      rw [this]; ring
    simp_rw [e1]
    have := tendsto_finset_sum (Finset.univ : Finset (Fin d)) fun k _ => hSw k
    simpa using this
  rw [hasSum_iff_tendsto_nat_of_nonneg hlamnn]
  have h2 : Tendsto (fun n => dirPair μ (weakGrad f) (weakGrad f) -
      dirPair μ (fun x k => weakGrad f x k - S n x k) (fun x k => weakGrad f x k - S n x k))
      atTop (𝓝 (dirPair μ (weakGrad f) (weakGrad f) - 0)) := tendsto_const_nhds.sub hD
  rw [sub_zero] at h2
  refine h2.congr fun n => ?_
  rw [hdef n]; ring

end main

end SharpLSI
