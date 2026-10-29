import FullLabeledLSI.Paper.Sec3Pos2
import SharpSymmetricLSI.Paper.Occ15

/-!
# Hybrid LSI inputs: `0 < rLS μ` and `rLS μ ≤ λ₁`

* `rLS_ofReal_le`, `rLS_pos`: `rLS μ` is positive for the minimizer (`reference_lsi` via `rLS_lower`).
* `rLS_le_lam_one`: `rLS μ ≤ ofReal (lam 1)`, by the test functions `f_t = 1 + t e₁`
  (`Ent(f_t²) = 2 t² + O(t³)`, `∫|∇f_t|² = t² λ₁`).
* `rLS_lt_top`: hence `rLS μ < ⊤`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ}

/-- Third-order expansion of `(1+x)² log (1+x)²` for `|x| ≤ 1/2`. -/
theorem psi_bound {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |(1 + x) ^ 2 * Real.log ((1 + x) ^ 2) - 2 * x - 3 * x ^ 2| ≤ 10 * |x| ^ 3 := by
  have hx1 : |x| < 1 := by linarith
  have hneg : |-x| < 1 := by rwa [abs_neg]
  have h1 := Real.abs_log_sub_add_sum_range_le hneg 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg] at h1
  have hlog : |(-x) ^ 1 / ((0 : ℕ) + 1 : ℝ) + (-x) ^ 2 / (((1 : ℕ) : ℝ) + 1) + Real.log (1 - -x)|
      ≤ |x| ^ 3 / (1 - |x|) := by
    simpa using h1
  have hlog' : |Real.log (1 + x) - (x - x ^ 2 / 2)| ≤ 2 * |x| ^ 3 := by
    have e : (-x) ^ 1 / ((0 : ℕ) + 1 : ℝ) + (-x) ^ 2 / (((1 : ℕ) : ℝ) + 1) + Real.log (1 - -x)
        = Real.log (1 + x) - (x - x ^ 2 / 2) := by
      push_cast; rw [sub_neg_eq_add]; ring
    rw [e] at hlog
    refine hlog.trans ?_
    have hpos : (0 : ℝ) < 1 - |x| := by linarith
    rw [div_le_iff₀ hpos]
    have : 0 ≤ |x| ^ 3 := by positivity
    nlinarith
  set ρ := Real.log (1 + x) - (x - x ^ 2 / 2) with hρ
  have hx0 : 0 < 1 + x := by
    have := neg_abs_le x; linarith
  have hL : Real.log ((1 + x) ^ 2) = 2 * (x - x ^ 2 / 2 + ρ) := by
    rw [Real.log_pow]; push_cast; rw [hρ]; ring
  have heq : (1 + x) ^ 2 * Real.log ((1 + x) ^ 2) - 2 * x - 3 * x ^ 2 =
      2 * (1 + x) ^ 2 * ρ - x ^ 4 := by
    rw [hL]; ring
  rw [heq]
  have h2 : (1 + x) ^ 2 ≤ 9 / 4 := by
    have := abs_le.mp hx; nlinarith
  have h3 : |2 * (1 + x) ^ 2 * ρ| ≤ 9 * |x| ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (1 + x)), abs_two]
    have : |ρ| * 1 ≤ |ρ| * 1 := le_rfl
    calc 2 * (1 + x) ^ 2 * |ρ| ≤ 2 * (9 / 4) * (2 * |x| ^ 3) := by
          gcongr
      _ = 9 * |x| ^ 3 := by ring
  have h4 : x ^ 4 ≤ |x| ^ 3 / 2 := by
    have : x ^ 4 = |x| ^ 3 * |x| := by
      rw [← pow_succ]; exact (Even.pow_abs (by decide) x).symm
    rw [this]
    have : 0 ≤ |x| ^ 3 := by positivity
    nlinarith
  have h5 : |x ^ 4| = x ^ 4 := abs_of_nonneg (by positivity)
  calc |2 * (1 + x) ^ 2 * ρ - x ^ 4| ≤ |2 * (1 + x) ^ 2 * ρ| + |x ^ 4| := abs_sub _ _
    _ ≤ 10 * |x| ^ 3 := by rw [h5]; nlinarith


/-- Affine images `a + t f` of an `H¹(P)` function (for `P ≪ volume`), with `∇(a + t f) = t ∇f`. -/
theorem memH1_const_add_smul {P : Measure (Torus d)} [IsFiniteMeasure P] (hac : P ≪ volume)
    {f : Torus d → ℝ} (hf : MemH1 P f) (a t : ℝ) :
    MemH1 P (fun y => a + t * f y) ∧
      weakGrad (fun y => a + t * f y) =ᵐ[P] fun y k => t * weakGrad f y k := by
  have hw := isWeakGrad_weakGrad hf.1
  have hw' : IsWeakGrad (fun y => a + t * f y) (fun y k => t * weakGrad f y k) := by
    have := (isWeakGrad_const (ι := Fin d) a).add (hw.cmul t)
    simpa using this
  have hae : weakGrad (fun y => a + t * f y) =ᵐ[P] fun y k => t * weakGrad f y k :=
    hac.ae_le (weakGrad_ae_eq hw')
  refine ⟨⟨⟨_, hw'⟩, (memLp_const a).add (hf.2.1.const_mul t), ?_⟩, hae⟩
  have h2 : MemLp (fun y => |t| * Real.sqrt (sqNorm (weakGrad f y))) 2 P := hf.2.2.const_mul _
  refine h2.ae_eq (hae.mono fun y hy => ?_)
  simp only
  rw [hy]
  unfold sqNorm
  simp_rw [mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]

/-- The Dirichlet energy of an eigenfunction. -/
theorem integral_sqNorm_weakGrad_eigen {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis μ e lam) (j : ℕ) :
    ∫ x, sqNorm (weakGrad (e j) x) ∂μ = lam j := by
  have h := he.eigen j (e j) (he.memH1 j)
  simp only [he.orthonormal j j, ↓reduceIte, mul_one] at h
  rw [← h]
  unfold sqNorm
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact Finset.sum_congr rfl fun k _ => sq _

theorem integrable_sqNorm_weakGrad {μ : Measure (Torus d)} [IsFiniteMeasure μ] {f : Torus d → ℝ}
    (h : MemH1 μ f) : Integrable (fun x => sqNorm (weakGrad f x)) μ := by
  have hm : AEStronglyMeasurable (fun x => Real.sqrt (sqNorm (weakGrad f x))) μ :=
    h.2.2.aestronglyMeasurable
  have := (memLp_two_iff_integrable_sq hm).1 h.2.2
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [Real.sq_sqrt (sqNorm_nonneg _)]

theorem dirichlet_eq_ofReal {μ : Measure (Torus d)} [IsFiniteMeasure μ] {f : Torus d → ℝ}
    (h : MemH1 μ f) : dirichlet μ f = ENNReal.ofReal (∫ x, sqNorm (weakGrad f x) ∂μ) := by
  unfold dirichlet
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_sqNorm_weakGrad h)
    (Filter.Eventually.of_forall fun x => sqNorm_nonneg _)]


/-- The quotient bound for the test function `1 + t e₁`. -/
theorem rLS_le_quot {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ volume)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis μ e lam) {M : ℝ} (hM1 : 1 ≤ M)
    (hM : ∀ᵐ x ∂μ, |e 1 x| ≤ M) {t : ℝ} (ht0 : 0 < t) (ht : t * M ≤ 1 / 2)
    (htK : t * (10 * M + 1) < 2) :
    rLS μ ≤ ENNReal.ofReal (2 * t ^ 2 * lam 1 / (t ^ 2 * (2 - t * (10 * M + 1)))) := by
  have hE : MemLp (e 1) 2 μ := (he.memH1 1).2.1
  have hEm : AEStronglyMeasurable (e 1) μ := hE.aestronglyMeasurable
  have hint1 : Integrable (e 1) μ := hE.integrable one_le_two
  have hint2 : Integrable (fun x => e 1 x * e 1 x) μ := by
    have := (memLp_two_iff_integrable_sq hEm).1 hE
    simpa [sq] using this
  have hI0 : ∫ x, e 1 x ∂μ = 0 := by
    have h := he.orthonormal 0 1
    simpa [he.zero] using h
  have hI2 : ∫ x, e 1 x * e 1 x ∂μ = 1 := by simpa using he.orthonormal 1 1
  have hlam0 : 0 ≤ lam 1 := by
    rw [← integral_sqNorm_weakGrad_eigen he 1]
    exact integral_nonneg fun x => sqNorm_nonneg _
  have hM0 : 0 < M := by linarith
  have ht1 : t ≤ 1 / 2 := by nlinarith
  set f : Torus d → ℝ := fun x => 1 + t * e 1 x with hf
  obtain ⟨hfH, hgrad⟩ := memH1_const_add_smul hac (he.memH1 1) 1 t
  -- a.e. bound
  have hb : ∀ᵐ x ∂μ, |t * e 1 x| ≤ 1 / 2 := by
    filter_upwards [hM] with x hx
    rw [abs_mul, abs_of_pos ht0]
    nlinarith [abs_nonneg (e 1 x)]
  -- the square
  have hu : (fun x => f x ^ 2) = fun x => 1 + 2 * t * e 1 x + t ^ 2 * (e 1 x * e 1 x) := by
    funext x; simp only [hf]; ring
  have hui : Integrable (fun x => f x ^ 2) μ := by
    rw [hu]
    exact ((integrable_const 1).add (hint1.const_mul (2 * t))).add (hint2.const_mul _)
  have hintu : ∫ x, f x ^ 2 ∂μ = 1 + t ^ 2 := by
    have hA : Integrable (fun x => (1 : ℝ) + 2 * t * e 1 x) μ :=
      (integrable_const 1).add (hint1.const_mul _)
    have hB : Integrable (fun x => t ^ 2 * (e 1 x * e 1 x)) μ := hint2.const_mul _
    rw [hu, integral_add hA hB, integral_add (integrable_const (1 : ℝ)) (hint1.const_mul (2 * t)),
      integral_const_mul, integral_const_mul, hI0, hI2]
    simp
  have hfm : AEStronglyMeasurable f μ := aestronglyMeasurable_const.add (hEm.const_mul t)
  have hlogm : AEStronglyMeasurable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ :=
    (hfm.pow 2).mul (Real.measurable_log.comp_aemeasurable (hfm.pow 2).aemeasurable).aestronglyMeasurable
  have hlogb : ∀ᵐ x ∂μ, ‖f x ^ 2 * Real.log (f x ^ 2)‖ ≤ 4 := by
    filter_upwards [hb] with x hx
    have h1 := psi_bound hx
    have h2 : f x ^ 2 * Real.log (f x ^ 2) = (1 + t * e 1 x) ^ 2 * Real.log ((1 + t * e 1 x) ^ 2) :=
      rfl
    rw [Real.norm_eq_abs, h2]
    set y := t * e 1 x
    have hy := abs_le.mp hx
    have h3 : |2 * y + 3 * y ^ 2| ≤ 2 := by
      rw [abs_le]; constructor <;> nlinarith [hy.1, hy.2]
    have h4 : 10 * |y| ^ 3 ≤ 10 / 8 := by
      have : |y| ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hx 3
      linarith
    have h5 := abs_sub_abs_le_abs_sub ((1 + y) ^ 2 * Real.log ((1 + y) ^ 2)) (2 * y + 3 * y ^ 2)
    have h6 : |(1 + y) ^ 2 * Real.log ((1 + y) ^ 2) - (2 * y + 3 * y ^ 2)| ≤ 10 * |y| ^ 3 := by
      have := h1; rwa [sub_sub] at this
    linarith [abs_nonneg (2 * y + 3 * y ^ 2)]
  have hlog_int : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ :=
    Integrable.of_bound hlogm 4 hlogb
  -- lower bound for the entropy integral
  have hlow : ∀ᵐ x ∂μ, 2 * t * e 1 x + (3 * t ^ 2 - 10 * t ^ 3 * M) * (e 1 x * e 1 x) ≤
      f x ^ 2 * Real.log (f x ^ 2) := by
    filter_upwards [hb, hM] with x hx hxM
    have h1 := psi_bound hx
    have h2 : f x ^ 2 * Real.log (f x ^ 2) = (1 + t * e 1 x) ^ 2 * Real.log ((1 + t * e 1 x) ^ 2) :=
      rfl
    rw [h2]
    have h3 := (abs_le.mp h1).1
    have h4 : |t * e 1 x| ^ 3 ≤ t ^ 3 * M * (e 1 x * e 1 x) := by
      rw [abs_mul, abs_of_pos ht0, mul_pow]
      have : |e 1 x| ^ 3 = |e 1 x| * (e 1 x * e 1 x) := by
        rw [pow_succ, sq_abs]; ring
      rw [this, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxM (mul_self_nonneg _))
        (pow_pos ht0 3).le
    nlinarith [h3, h4]
  have hlowint : Integrable (fun x => 2 * t * e 1 x + (3 * t ^ 2 - 10 * t ^ 3 * M) *
      (e 1 x * e 1 x)) μ := (hint1.const_mul _).add (hint2.const_mul _)
  have hlowval : ∫ x, (2 * t * e 1 x + (3 * t ^ 2 - 10 * t ^ 3 * M) * (e 1 x * e 1 x)) ∂μ =
      3 * t ^ 2 - 10 * t ^ 3 * M := by
    rw [integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul,
      integral_const_mul, hI0, hI2]
    ring
  have hmono := integral_mono_ae hlowint hlog_int hlow
  rw [hlowval] at hmono
  -- the entropy
  have hent := ent_eq_formula μ (fun x => f x ^ 2) (fun x => sq_nonneg _) hui hlog_int
  rw [hintu] at hent
  set X := ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ - (1 + t ^ 2) * Real.log (1 + t ^ 2) with hX
  have hlogle : Real.log (1 + t ^ 2) ≤ t ^ 2 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + t ^ 2 by positivity)
    linarith
  have hXY : t ^ 2 * (2 - t * (10 * M + 1)) ≤ X := by
    have h1 : (1 + t ^ 2) * Real.log (1 + t ^ 2) ≤ (1 + t ^ 2) * t ^ 2 :=
      mul_le_mul_of_nonneg_left hlogle (by positivity)
    have h2 : t ^ 4 ≤ t ^ 3 := by
      have : t ^ 4 = t ^ 3 * t := by ring
      rw [this]; nlinarith [pow_pos ht0 3]
    rw [hX]; nlinarith
  have hYpos : 0 < t ^ 2 * (2 - t * (10 * M + 1)) := mul_pos (by positivity) (by linarith)
  have hXpos : 0 < X := lt_of_lt_of_le hYpos hXY
  -- the Dirichlet energy
  have hD : dirichlet μ f = ENNReal.ofReal (t ^ 2 * lam 1) := by
    rw [dirichlet_eq_ofReal hfH]
    congr 1
    rw [← integral_sqNorm_weakGrad_eigen he 1, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hgrad] with x hx
    rw [hx]
    unfold sqNorm
    simp_rw [mul_pow, ← Finset.mul_sum]
  -- put together
  have hmem : f ∈ {f : Torus d → ℝ | MemH1 μ f ∧ 0 < ent μ (fun x => f x ^ 2)} := by
    refine ⟨hfH, ?_⟩
    rw [hent]
    exact ENNReal.ofReal_pos.2 hXpos
  have h1 : rLS μ ≤ 2 * dirichlet μ f / ent μ (fun x => f x ^ 2) := by
    unfold rLS
    exact iInf₂_le f hmem
  refine h1.trans ?_
  rw [hent, hD, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_div_of_pos hXpos]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_assoc 2 (t ^ 2)]
  rw [div_le_div_iff₀ hXpos hYpos]
  have : 0 ≤ 2 * (t ^ 2 * lam 1) := by positivity
  exact mul_le_mul_of_nonneg_left hXY this


/-- `rLS μ ≤ λ₁` for a probability `μ ≪ volume` with a reference eigenbasis whose first
eigenfunction is essentially bounded. -/
theorem rLS_le_lam_one_of_bdd {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ volume)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis μ e lam) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, |e 1 x| ≤ C) : rLS μ ≤ ENNReal.ofReal (lam 1) := by
  have hlam0 : 0 ≤ lam 1 := by
    rw [← integral_sqNorm_weakGrad_eigen he 1]
    exact integral_nonneg fun x => sqNorm_nonneg _
  set M := max C 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM : ∀ᵐ x ∂μ, |e 1 x| ≤ M := hC.mono fun x hx => hx.trans (le_max_left _ _)
  have hM0 : 0 < M := by linarith
  set K := 10 * M + 1 with hK
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 < K := by linarith
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  set t := min (1 / K) (δ / (K * (lam 1 + 1))) with ht
  have ht0 : 0 < t := lt_min (by positivity) (by positivity)
  have htK : t * K ≤ 1 := by
    have : t ≤ 1 / K := min_le_left _ _
    calc t * K ≤ 1 / K * K := by gcongr
      _ = 1 := by field_simp
  have htM : t * M ≤ 1 / 2 := by nlinarith
  have hq := rLS_le_quot hac he hM1 hM ht0 htM (by linarith)
  refine hq.trans ?_
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add hlam0 (NNReal.coe_nonneg δ)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h2 : 0 < 2 - t * K := by linarith
  have e1 : 2 * t ^ 2 * lam 1 / (t ^ 2 * (2 - t * K)) = 2 * lam 1 / (2 - t * K) := by
    field_simp
  rw [show 10 * M + 1 = K from rfl, e1, div_le_iff₀ h2]
  have h3 : t ≤ δ / (K * (lam 1 + 1)) := min_le_right _ _
  have h4 : t * (K * (lam 1 + 1)) ≤ δ := by
    rwa [le_div_iff₀ (by positivity)] at h3
  have h5 : lam 1 * (t * K) ≤ δ := by
    nlinarith [mul_nonneg ht0.le hK0.le]
  nlinarith [mul_nonneg hlam0 (mul_nonneg ht0.le hK0.le)]

section minimizer
variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `rLS μ ≤ λ₁` for the minimizer. -/
theorem rLS_le_lam_one (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    rLS (μ : Measure (Torus d)) ≤ ENNReal.ofReal (lam 1) := by
  obtain ⟨C, hC⟩ := refEigen_bounded hyp hμ he 1
  obtain ⟨c, hc, hle⟩ := minimizer_le_smul_haar hyp hμ
  exact rLS_le_lam_one_of_bdd (Measure.absolutelyContinuous_of_le_smul hle) he hC

/-- `rLS μ < ⊤` for the minimizer. -/
theorem rLS_lt_top (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    rLS (μ : Measure (Torus d)) < ⊤ :=
  lt_of_le_of_lt (rLS_le_lam_one hyp hμ he) ENNReal.ofReal_lt_top

/-- `rLS μ ≥ cm/cp` for the density bounds of the minimizer (`reference_lsi`). -/
theorem rLS_ofReal_le (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) :
    ∃ cm cp : ℝ, 0 < cm ∧ 0 < cp ∧ ENNReal.ofReal (cm / cp) ≤ rLS (μ : Measure (Torus d)) := by
  obtain ⟨cq, Cq, L, hcq, hbq, hLq⟩ := elDens_data hyp hμ
  obtain ⟨hqm, hqpos, hq1⟩ := elDensity_props hyp (W := W) (μ : Measure (Torus d))
  have hμq : (μ : Measure (Torus d)) = densMeasure (elDens V W (μ : Measure (Torus d))) :=
    minimizer_eq_elDensity hyp hμ
  have h := rLS_lower hcq hbq hq1 hqm
  rw [← congrArg rLS hμq] at h
  exact ⟨cq, Cq, hcq, (hcq.trans_le (hbq 0).1).trans_le (hbq 0).2, h⟩

/-- `0 < rLS μ` for the minimizer. -/
theorem rLS_pos (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) : 0 < rLS (μ : Measure (Torus d)) := by
  obtain ⟨cm, cp, hcm, hcp, h⟩ := rLS_ofReal_le hyp hμ
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 (div_pos hcm hcp)) h

/-- `ofReal (rLS.toReal) = rLS` for the minimizer. -/
theorem ofReal_rLS_toReal (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    ENNReal.ofReal (rLS (μ : Measure (Torus d))).toReal = rLS (μ : Measure (Torus d)) :=
  ENNReal.ofReal_toReal (rLS_lt_top hyp hμ he).ne

/-- `0 < (rLS μ).toReal` for the minimizer. -/
theorem rLS_toReal_pos (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    0 < (rLS (μ : Measure (Torus d))).toReal :=
  ENNReal.toReal_pos (rLS_pos hyp hμ).ne' (rLS_lt_top hyp hμ he).ne

/-- `(rLS μ).toReal ≤ lam 1`. -/
theorem rLS_toReal_le_lam_one (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    (rLS (μ : Measure (Torus d))).toReal ≤ lam 1 := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (rLS_le_lam_one hyp hμ he)
  have hl : 0 ≤ lam 1 := by
    have := he.eigen 1 (e 1) (he.memH1 1)
    simp only [he.orthonormal 1 1, ↓reduceIte, mul_one] at this
    rw [← this]
    exact integral_nonneg fun x => Finset.sum_nonneg fun k _ => mul_self_nonneg _
  rwa [ENNReal.toReal_ofReal hl] at h

end minimizer

end SharpLSI.FL
