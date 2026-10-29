import SharpSymmetricLSI.Paper.Defective24
import SharpSymmetricLSI.Paper.Sec5_6

/-!
# R03 (Proposition 2.2), part 25: the conditional gaps in real form

For the regularized law `ν` and `j < N`: `E_ν G(ρ_j) = h_j + E_ν J(ρ_j)` with both terms finite
(`integral_gap_eq`), hence (with part 22)
`2r₀ (h_j + E_ν B(ρ_j^{⊗2})) ≤ (1+ε) E_ν |s_j|² + (1+1/ε) fcTerm j` (`two_r_gap_real_le`).
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `H(ρ|q) = ∫ klFun(ρ/q) dq` for densities. -/
theorem klDiv_densMeasure_eq_lintegral {ρ q : Torus d → ℝ} (hρm : Measurable ρ) (hqm : Measurable q)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hq0 : ∀ x, 0 < q x) (hρ1 : ∫ x, ρ x ∂haar d = 1)
    (hq1 : ∫ x, q x ∂haar d = 1) :
    klDiv (densMeasure ρ) (densMeasure q) =
      ∫⁻ x, ENNReal.ofReal (klFun (ρ x / q x)) ∂densMeasure q := by
  haveI := isProbabilityMeasure_densMeasure' (fun x => (hq0 x).le) hq1
  haveI := isProbabilityMeasure_densMeasure' hρ0 hρ1
  have hmρq : Measurable fun x => ENNReal.ofReal (ρ x / q x) := (hρm.div hqm).ennreal_ofReal
  have hdq : densMeasure ρ = (densMeasure q).withDensity fun x => ENNReal.ofReal (ρ x / q x) := by
    unfold densMeasure
    rw [← withDensity_mul _ ((hqm).ennreal_ofReal) hmρq]
    congr 1; funext x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hq0 x).le, mul_div_cancel₀ _ (hq0 x).ne']
  have hrn : (densMeasure ρ).rnDeriv (densMeasure q) =ᵐ[densMeasure q]
      fun x => ENNReal.ofReal (ρ x / q x) := by
    rw [hdq]; exact Measure.rnDeriv_withDensity _ hmρq
  have hac : densMeasure ρ ≪ densMeasure q := by rw [hdq]; exact withDensity_absolutelyContinuous _ _
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  refine lintegral_congr_ae ?_
  filter_upwards [hrn] with x hx
  rw [hx, ENNReal.toReal_ofReal (div_nonneg (hρ0 x) (hq0 x).le)]

theorem klFun_le_of_le {t B : ℝ} (ht0 : 0 ≤ t) (htB : t ≤ B) (hB : 1 ≤ B) :
    klFun t ≤ B * Real.log B + 1 := by
  unfold klFun
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have h1 : t * Real.log t ≤ B * Real.log B := by
    rcases le_total t 1 with h | h
    · exact (Real.mul_log_nonpos ht0 h).trans (mul_nonneg (by linarith) hlogB)
    · exact mul_le_mul htB (Real.log_le_log (by linarith) htB) (Real.log_nonneg h) (by linarith)
  linarith

theorem integral_le_toReal_lintegral_ofReal {α : Type*} [MeasurableSpace α] {P : Measure α}
    {f : α → ℝ} (hf : Integrable f P) : ∫ x, f x ∂P ≤ (∫⁻ x, ENNReal.ofReal (f x) ∂P).toReal := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  linarith [ENNReal.toReal_nonneg (a := ∫⁻ x, ENNReal.ofReal (-f x) ∂P)]

theorem ereal_toReal_coe_add {a : ℝ≥0∞} (ha : a ≠ ⊤) (b : ℝ) :
    ((a : EReal) + (b : EReal)).toReal = a.toReal + b := by
  rw [← ENNReal.ofReal_toReal ha, EReal.coe_ennreal_ofReal, max_eq_left ENNReal.toReal_nonneg,
    ← EReal.coe_add, EReal.toReal_coe, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

section jfun
variable (hyp : Hyp V W KV KW)
include hyp

theorem Jfun_eq_pi (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (ρ : Measure (Torus d))
    [IsProbabilityMeasure ρ] :
    Jfun W μ ρ = ∫ z, centeredKernel W μ (z 0) (z 1) / 2 ∂Measure.pi (fun _ : Fin 2 => ρ) := by
  obtain ⟨BK, hBK⟩ := centeredKernel_bdd hyp μ
  have hm : Measurable (Function.uncurry fun x y => centeredKernel W μ x y / 2) :=
    (measurable_centeredKernel hyp μ).div_const 2
  rw [integral_pi_two_S5 (F := fun x y => centeredKernel W μ x y / 2) hm (B := |BK| / 2)
    fun x y => by
      rw [abs_div, abs_two]
      exact div_le_div_of_nonneg_right ((hBK x y).trans (le_abs_self _)) zero_le_two]
  unfold Jfun interE
  simp_rw [integral_div]

theorem measurable_Jfun_kernel (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {α : Type*}
    [MeasurableSpace α] (κ : Kernel α (Torus d)) [IsMarkovKernel κ] :
    Measurable fun a => Jfun W μ (κ a) := by
  have hB : Measurable fun z : Fin 2 → Torus d => centeredKernel W μ (z 0) (z 1) / 2 := by
    have h := (measurable_centeredKernel hyp μ).comp
      (show Measurable fun z : Fin 2 → Torus d => (z 0, z 1) from
        (measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
    simp only [Function.comp_def, Function.uncurry_apply_pair] at h
    exact h.div_const 2
  have h0 : Measurable fun p : α × (Fin 2 → Torus d) => centeredKernel W μ (p.2 0) (p.2 1) / 2 := by
    have h1 := hB.comp (measurable_snd : Measurable (Prod.snd : α × (Fin 2 → Torus d) → Fin 2 → Torus d))
    simp only [Function.comp_def] at h1
    exact h1
  have h := h0.stronglyMeasurable.integral_kernel_prod_right' (κ := piK κ 2)
  have e : (fun a => Jfun W μ (κ a)) = fun a => ∫ z, centeredKernel W μ (z 0) (z 1) / 2 ∂(piK κ 2 a) := by
    funext a; rw [piK_apply, Jfun_eq_pi hyp]
  rw [e]
  exact h.measurable

theorem abs_Jfun_le_of_bdd (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {BK : ℝ}
    (hBK : ∀ x y, |centeredKernel W μ x y| ≤ BK) (ρ : Measure (Torus d)) [IsProbabilityMeasure ρ] :
    |Jfun W μ ρ| ≤ BK / 2 := by
  unfold Jfun interE
  rw [abs_div, abs_two]
  exact div_le_div_of_nonneg_right (abs_integral_le_of_bdd fun y => abs_integral_le_of_bdd
    fun x => hBK x y) zero_le_two

end jfun

section gapreal
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {N : ℕ} (hN : 1 ≤ N) {f : Config N d → ℝ} (hfm : Measurable f) (hf : MemH1C (gibbs V W N) f)
  {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (hw : IsWeakGrad (f ∘ unflat) g)
  (hgm : ∀ p, Measurable fun y => g y p) (hg2 : ∀ p, MemLp (fun y => g y p) 2 volume)
  (hgi : ∀ p, Integrable (fun y => g y p) volume) (n : ℕ) {j : ℕ} (hj : j < N)

include hyp hμ hfm hf in
/-- **`E_ν G(ρ_j) = h_j + E_ν J(ρ_j)`**, all terms finite. -/
theorem integral_gap_eq :
    haveI := isProbabilityMeasure_Qreg hyp hf hfm n
    Integrable (fun X => (gap V W (condNext ((volume : Measure (Config N d)).withDensity
        fun X => ENNReal.ofReal (Qreg V W n f X)) j hj (past j hj.le X))).toReal)
        ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)) ∧
    ∫ X, (gap V W (condNext ((volume : Measure (Config N d)).withDensity
        fun X => ENNReal.ofReal (Qreg V W n f X)) j hj (past j hj.le X))).toReal
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)) =
      (hCondT ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X))
          (μ : Measure (Torus d)) j).toReal +
        condProductMean ((volume : Measure (Config N d)).withDensity
          fun X => ENNReal.ofReal (Qreg V W n f X)) 2
          (fun z => 1 * centeredKernel W μ (z 0) (z 1) / 2) j := by
  haveI := isProbabilityMeasure_Qreg hyp hf hfm n
  obtain ⟨c, C, hc, hb⟩ := Qreg_bounds hyp hf hfm n
  have hQm := measurable_Qreg hyp hf hfm n
  have hQc : ∀ X, c ≤ Qreg V W n f X := fun X => (hb X).1
  have hQC : ∀ X, Qreg V W n f X ≤ C := fun X => (hb X).2
  have hC : 0 < C := hc.trans_le ((hb (Classical.arbitrary _)).1.trans (hb _).2)
  set Q := Qreg V W n f with hQdef
  set ν := (volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Q X) with hνdef
  -- the minimizer's density
  obtain ⟨cm, cp, Lq, hcm, hB⟩ := elDensity_bounds hyp
  obtain ⟨hqb, hqL⟩ := hB (μ : Measure (Torus d)) inferInstance
  have hμq : (μ : Measure (Torus d)) = densMeasure (elDens V W (μ : Measure (Torus d))) :=
    minimizer_eq_elDensity hyp hμ
  have hq1 : ∫ x, elDens V W (μ : Measure (Torus d)) x ∂haar d = 1 :=
    (elDensity_props hyp (μ : Measure (Torus d))).2.2
  generalize hqdef : elDens V W (μ : Measure (Torus d)) = q at hqb hqL hμq hq1
  have hq0 : ∀ x, 0 < q x := fun x => hcm.trans_le (hqb x).1
  have hqm : Measurable q := hqL.continuous.measurable
  haveI : IsProbabilityMeasure (densMeasure q) := isProbabilityMeasure_densMeasure' (fun x => (hq0 x).le) hq1
  -- the entropy of the slices as a measurable bounded function of the past
  set KLp : Config j d → ℝ≥0∞ := fun p =>
    ∫⁻ x, ENNReal.ofReal (klFun (condDens hj Q p x / q x)) ∂densMeasure q with hKLp
  have hKLpm : Measurable KLp :=
    ((measurable_klFun.comp ((measurable_condDens hj hQm).div
      (hqm.comp measurable_snd))).ennreal_ofReal).lintegral_prod_right'
  set Bρ := max ((C / c) / cm) 1
  have hKLpb : ∀ p, KLp p ≤ ENNReal.ofReal (Bρ * Real.log Bρ + 1) := fun p => by
    calc KLp p ≤ ∫⁻ _, ENNReal.ofReal (Bρ * Real.log Bρ + 1) ∂densMeasure q :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (klFun_le_of_le
            (div_nonneg ((div_pos hc hC).le.trans (condDens_bounds hj hQm hc hQc hQC p x).1) (hq0 x).le)
            ((div_le_div₀ (by positivity) (condDens_bounds hj hQm hc hQc hQC p x).2 hcm (hqb x).1).trans
              (le_max_left _ _)) (le_max_right _ _))
      _ = _ := by simp
  have hKLpt : ∀ p, KLp p ≠ ⊤ := fun p => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hKLpb p)
  have hcn : ∀ᵐ X ∂ν, condNext ν j hj (past j hj.le X) = densMeasure (condDens hj Q (past j hj.le X)) :=
    ae_of_ae_map (measurable_past hj.le).aemeasurable (condNext_ae_eq hj hQm hc hQc hQC)
  have hKL : ∀ᵐ X ∂ν, klDiv (condNext ν j hj (past j hj.le X)) (μ : Measure (Torus d)) =
      KLp (past j hj.le X) := by
    filter_upwards [hcn] with X hX
    rw [hX, hμq]
    exact klDiv_densMeasure_eq_lintegral ((measurable_condDens hj hQm).of_uncurry_left)
      hqm (fun x => (div_pos hc hC).le.trans (condDens_bounds hj hQm hc hQc hQC _ x).1) hq0
      (integral_condDens hj hQm hc hQc hQC _) hq1
  -- the interaction part
  obtain ⟨BK, hBK⟩ := centeredKernel_bdd hyp (μ : Measure (Torus d))
  have hJm : Measurable fun X => Jfun W μ (condNext ν j hj (past j hj.le X)) := by
    have h := (measurable_Jfun_kernel hyp (μ : Measure (Torus d)) (condNext ν j hj)).comp
      (measurable_past hj.le)
    simp only [Function.comp_def] at h
    exact h
  have hJi : Integrable (fun X => Jfun W μ (condNext ν j hj (past j hj.le X))) ν :=
    integrable_of_bdd hJm fun X => abs_Jfun_le_of_bdd hyp _ hBK _
  have hKi : Integrable (fun X => (KLp (past j hj.le X)).toReal) ν :=
    integrable_of_bdd ((hKLpm.comp (measurable_past hj.le)).ennreal_toReal) fun X => by
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal (add_nonneg (mul_nonneg
        (zero_le_one.trans (le_max_right _ _)) (Real.log_nonneg (le_max_right _ _))) zero_le_one)
        (hKLpb _)
  have hgapae : (fun X => (gap V W (condNext ν j hj (past j hj.le X))).toReal) =ᵐ[ν]
      fun X => (KLp (past j hj.le X)).toReal + Jfun W μ (condNext ν j hj (past j hj.le X)) := by
    filter_upwards [hKL] with X hX
    have e : gap V W (condNext ν j hj (past j hj.le X)) =
        ((klDiv (condNext ν j hj (past j hj.le X)) (μ : Measure (Torus d)) : ℝ≥0∞) : EReal) +
          ((Jfun W (μ : Measure (Torus d)) (condNext ν j hj (past j hj.le X)) : ℝ) : EReal) :=
      gap_eq_aux hyp hμ ⟨condNext ν j hj (past j hj.le X), inferInstance⟩
    rw [e, hX, ereal_toReal_coe_add (hKLpt _)]
  refine ⟨(hKi.add hJi).congr hgapae.symm, ?_⟩
  rw [integral_congr_ae hgapae, integral_add hKi hJi, integral_toReal
    (show Measurable fun X : Config N d => KLp (past j hj.le X) from
      hKLpm.comp (measurable_past hj.le)).aemeasurable (Eventually.of_forall fun X => (hKLpt _).lt_top),
    condProductMean_eq_J hyp (μ : Measure (Torus d)) 1 ν hj]
  simp only [one_mul]
  congr 1
  unfold hCondT hCond
  rw [dif_pos hj, lintegral_congr_ae hKL]

include hyp hμ hN hfm hf hw hgm hg2 hgi in
/-- **`2r₀ (h_j + E_ν B(ρ_j^{⊗2})) ≤ (1+ε) E_ν |s_j|² + (1+1/ε) fcTerm j`.** -/
theorem two_r_gap_real_le {r₀ ε : ℝ} (hr₀ : 0 ≤ r₀) (hrr : ENNReal.ofReal r₀ ≤ rStar V W)
    (hε : 0 < ε)
    (hfin : ∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g ⟨j, hj⟩ k X ^ 2)
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)) ≠ ⊤) :
    haveI := isProbabilityMeasure_Qreg hyp hf hfm n
    2 * r₀ * ((hCondT ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X))
          (μ : Measure (Torus d)) j).toReal +
        condProductMean ((volume : Measure (Config N d)).withDensity
          fun X => ENNReal.ofReal (Qreg V W n f X)) 2
          (fun z => 1 * centeredKernel W μ (z 0) (z 1) / 2) j) ≤
      (1 + ε) * (∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g ⟨j, hj⟩ k X ^ 2)
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X))).toReal +
      (1 + 1 / ε) * fcTerm W μ ((volume : Measure (Config N d)).withDensity
        fun X => ENNReal.ofReal (Qreg V W n f X)) j := by
  haveI := isProbabilityMeasure_Qreg hyp hf hfm n
  obtain ⟨hint, heq⟩ := integral_gap_eq hyp hμ hfm hf n hj
  rw [← heq, ← integral_const_mul]
  have hfc0 : 0 ≤ fcTerm W μ ((volume : Measure (Config N d)).withDensity
      fun X => ENNReal.ofReal (Qreg V W n f X)) j := by
    unfold fcTerm; rw [dif_pos hj]
    exact integral_nonneg fun X => Finset.sum_nonneg fun k _ => sq_nonneg _
  refine (integral_le_toReal_lintegral_ofReal (hint.const_mul _)).trans ?_
  refine (ENNReal.toReal_mono ?_ (lintegral_two_r_gap_le hyp hμ hN hfm hf hw hgm hg2 hgi n hj hr₀ hrr hε)).trans
    (le_of_eq ?_)
  · exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
  · rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hfc0]

end gapreal

end SharpLSI
