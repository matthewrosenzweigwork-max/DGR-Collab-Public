import DGPS.Foundations.CompactSobolev
import DGPS.Foundations.PeriodicSmoothing
import DGPS.Foundations.WeakContractions

/-!
# FOU008: weighted form Hilbert closure

For a fixed measurable density `0 < c ≤ w ≤ C < ∞` on the unit torus, the weighted Dirichlet form
`E_w(u,v) = ∫ ⟨∇u,∇v⟩ w dm` on periodic `H¹` is comparable to the unweighted `H¹` norm, hence
closed (complete form norm), densely defined (smooth periodic functions form a core and are dense
in `L²(w m)`), symmetric, nonnegative and Markov; its form ball is relatively compact in
`L²(w m)`; and constants are exactly the zero-energy kernel.  The form is written on weak-gradient
fields (`weightedForm`), with an a.e.-independence lemma.  Canonical output:
`DGPS.Analysis.weighted_form_hilbert_closure`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS

variable {d : ℕ} {w : Torus d → ℝ} {c C : ℝ}

/-- The weighted Dirichlet form `E_w(u,v) = ∫ ⟨∇u,∇v⟩ w dm`, written on weak gradients. -/
noncomputable def weightedForm (w : Torus d → ℝ) (g h : Torus d → Tangent d) : ℝ :=
  ∫ x, inner ℝ (g x) (h x) * w x ∂haar d

theorem weightedForm_comm (g h : Torus d → Tangent d) :
    weightedForm w g h = weightedForm w h g := by
  unfold weightedForm
  simp_rw [real_inner_comm]

theorem weightedForm_self (g : Torus d → Tangent d) :
    weightedForm w g g = ∫ x, ‖g x‖ ^ 2 * w x ∂haar d := by
  unfold weightedForm
  simp_rw [real_inner_self_eq_norm_sq]

theorem weightedForm_nonneg (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) (hc : 0 < c)
    (g : Torus d → Tangent d) : 0 ≤ weightedForm w g g := by
  rw [weightedForm_self]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hwb] with x hx
  have := hc.le.trans hx.1
  positivity

theorem integrable_inner_of_memLp {g h : Torus d → Tangent d} (hg : MemLp g 2 (haar d))
    (hh : MemLp h 2 (haar d)) : Integrable (fun x => inner ℝ (g x) (h x)) (haar d) := by
  have hg2 : Integrable (fun x => ‖g x‖ ^ 2) (haar d) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hh2 : Integrable (fun x => ‖h x‖ ^ 2) (haar d) :=
    (memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).mp hh
  refine Integrable.mono' (hg2.add hh2) ?_ (Eventually.of_forall fun x => ?_)
  · exact hg.aestronglyMeasurable.inner hh.aestronglyMeasurable
  · calc ‖inner ℝ (g x) (h x)‖ ≤ ‖g x‖ * ‖h x‖ := norm_inner_le_norm _ _
      _ ≤ ‖g x‖ ^ 2 + ‖h x‖ ^ 2 := by nlinarith [sq_nonneg (‖g x‖ - ‖h x‖), norm_nonneg (g x), norm_nonneg (h x)]

theorem integrable_inner_mul_weight (hw : Measurable w) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (hc : 0 < c) {g h : Torus d → Tangent d} (hg : MemLp g 2 (haar d)) (hh : MemLp h 2 (haar d)) :
    Integrable (fun x => inner ℝ (g x) (h x) * w x) (haar d) := by
  refine integrable_mul_weight ?_ hw hwb hc
  exact integrable_inner_of_memLp hg hh

theorem weightedForm_add_left (hw : Measurable w) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (hc : 0 < c) {g₁ g₂ h : Torus d → Tangent d} (h₁ : MemLp g₁ 2 (haar d))
    (h₂ : MemLp g₂ 2 (haar d)) (hh : MemLp h 2 (haar d)) :
    weightedForm w (fun x => g₁ x + g₂ x) h = weightedForm w g₁ h + weightedForm w g₂ h := by
  unfold weightedForm
  rw [← integral_add (integrable_inner_mul_weight hw hwb hc h₁ hh)
    (integrable_inner_mul_weight hw hwb hc h₂ hh)]
  congr 1; funext x
  rw [inner_add_left, add_mul]

theorem weightedForm_smul_left (a : ℝ) (g h : Torus d → Tangent d) :
    weightedForm w (fun x => a • g x) h = a * weightedForm w g h := by
  unfold weightedForm
  rw [← integral_const_mul]
  congr 1; funext x
  rw [inner_smul_left]; simp [mul_assoc]


/-! ### Norm comparison -/

theorem weighted_norm_comparison (hw : Measurable w) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (hc : 0 < c) {u : Torus d → ℝ} {g : Torus d → Tangent d} (h : IsWeakGradient u g) :
    c * (∫ x, u x ^ 2 ∂haar d + ∫ x, ‖g x‖ ^ 2 ∂haar d) ≤
        ∫ x, u x ^ 2 * w x ∂haar d + ∫ x, ‖g x‖ ^ 2 * w x ∂haar d ∧
      ∫ x, u x ^ 2 * w x ∂haar d + ∫ x, ‖g x‖ ^ 2 * w x ∂haar d ≤
        C * (∫ x, u x ^ 2 ∂haar d + ∫ x, ‖g x‖ ^ 2 ∂haar d) := by
  have hi : Integrable (fun x => u x ^ 2) (haar d) := h.memLp.integrable_sq
  have hig : Integrable (fun x => ‖g x‖ ^ 2) (haar d) :=
    (memLp_two_iff_integrable_sq_norm h.memLp_grad.aestronglyMeasurable).mp h.memLp_grad
  have a1 := mul_integral_le_integral_mul_weight hi (fun x => sq_nonneg _) hw hwb hc
  have a2 := mul_integral_le_integral_mul_weight hig (fun x => by positivity) hw hwb hc
  have b1 := integral_mul_weight_le hi (fun x => sq_nonneg _) hw hwb hc
  have b2 := integral_mul_weight_le hig (fun x => by positivity) hw hwb hc
  constructor <;> linarith

/-! ### Markov property -/

theorem integral_norm_sq_mul_weight_le_of_le (hw : Measurable w)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) (hc : 0 < c) {G g : Torus d → Tangent d}
    (hG : MemLp G 2 (haar d)) (hg : MemLp g 2 (haar d)) (h : ∀ x, ‖G x‖ ≤ ‖g x‖) :
    ∫ x, ‖G x‖ ^ 2 * w x ∂haar d ≤ ∫ x, ‖g x‖ ^ 2 * w x ∂haar d := by
  refine integral_mono_ae
    (integrable_mul_weight ((memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG)
      hw hwb hc)
    (integrable_mul_weight ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg)
      hw hwb hc) ?_
  filter_upwards [hwb] with x hx
  have hw0 : 0 ≤ w x := hc.le.trans hx.1
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (h x) 2) hw0

theorem markov_unit_contraction (hw : Measurable w) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (hc : 0 < c) {u : Torus d → ℝ} {g : Torus d → Tangent d} (h : IsWeakGradient u g) :
    ∃ g' : Torus d → Tangent d, IsWeakGradient (fun x => min (max (u x) 0) 1) g' ∧
      ∫ x, ‖g' x‖ ^ 2 * w x ∂haar d ≤ ∫ x, ‖g x‖ ^ 2 * w x ∂haar d := by
  have h1 := h.max_const 0
  have h2 := h1.min_const 1
  refine ⟨_, h2, ?_⟩
  refine integral_norm_sq_mul_weight_le_of_le hw hwb hc h2.memLp_grad h.memLp_grad fun x => ?_
  by_cases ha : max (u x) 0 < 1 <;> by_cases hb : 0 < u x <;> simp [ha, hb]

/-! ### The zero-energy kernel -/

theorem ae_eq_zero_of_energy_zero (hw : Measurable w) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (hc : 0 < c) {g : Torus d → Tangent d} (hg : MemLp g 2 (haar d))
    (h0 : ∫ x, ‖g x‖ ^ 2 * w x ∂haar d = 0) : g =ᵐ[haar d] 0 := by
  have hint := integrable_mul_weight
    ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg) hw hwb hc
  have hnn : 0 ≤ᵐ[haar d] fun x => ‖g x‖ ^ 2 * w x := by
    filter_upwards [hwb] with x hx
    have := hc.le.trans hx.1
    positivity
  have := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp h0
  filter_upwards [this, hwb] with x hx hwx
  have hw0 : 0 < w x := hc.trans_le hwx.1
  have : ‖g x‖ ^ 2 = 0 := by
    simpa [hw0.ne'] using hx
  simpa using this

theorem energy_zero_iff (hw : Measurable w) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (hc : 0 < c) {u : Torus d → ℝ} {g : Torus d → Tangent d} (h : IsWeakGradient u g) :
    ∫ x, ‖g x‖ ^ 2 * w x ∂haar d = 0 ↔ ∃ a : ℝ, u =ᵐ[haar d] fun _ => a := by
  constructor
  · intro h0
    have hg0 := ae_eq_zero_of_energy_zero hw hwb hc h.memLp_grad h0
    have hP := SharpLSI.poincare_torus h.isWeakGrad h.memLp (memLp_coord h.memLp_grad)
    have hz : ∑ j, ∫ y, g y j ^ 2 ∂haar d = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hg0] with x hx
      simp [hx]
    rw [hz] at hP
    have hP' : 4 * Real.pi ^ 2 * ProbabilityTheory.variance u (haar d) ≤ 0 := hP
    have hp : (0 : ℝ) < 4 * Real.pi ^ 2 := by positivity
    have hv : ProbabilityTheory.variance u (haar d) = 0 :=
      le_antisymm (nonpos_of_mul_nonpos_right hP' hp) (ProbabilityTheory.variance_nonneg _ _)
    exact ⟨_, ProbabilityTheory.ae_eq_integral_of_variance_eq_zero h.memLp hv⟩
  · rintro ⟨a, ha⟩
    have h1 : IsWeakGradient u (fun _ => 0) :=
      (isWeakGradient_const (d := d) a).congr_ae ha.symm (Eventually.of_forall fun _ => rfl)
    have hg0 := h.ae_eq h1
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hg0] with x hx
    simp [hx]

/-! ### Completeness of the form norm -/

theorem Lp_norm_sq_eq_integral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure (Torus d)} (F : Lp E 2 μ) : ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

/-- The graph point `(u, ∇u)` of a weak-gradient pair. -/
noncomputable def graphPoint {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) : H1Ambient d :=
  WithLp.toLp 2 (h.memLp.toLp u, h.memLp_grad.toLp g)

theorem graphPoint_mem {u : Torus d → ℝ} {g : Torus d → Tangent d} (h : IsWeakGradient u g) :
    graphPoint h ∈ h1Graph d :=
  mem_h1Graph.mpr (h.congr_ae h.memLp.coeFn_toLp.symm h.memLp_grad.coeFn_toLp.symm)

theorem norm_sq_graphPoint_sub {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) (P : H1Ambient d) :
    ‖graphPoint h - P‖ ^ 2 =
      ∫ x, (u x - (P.ofLp.1 : Torus d → ℝ) x) ^ 2 ∂haar d +
        ∫ x, ‖g x - (P.ofLp.2 : Torus d → Tangent d) x‖ ^ 2 ∂haar d := by
  rw [h1Ambient_norm_sq, Lp_norm_sq_eq_integral, Lp_norm_sq_eq_integral]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (h.memLp.toLp u) P.ofLp.1, h.memLp.coeFn_toLp] with x h1 h2
    simp only [graphPoint, WithLp.ofLp_sub, Prod.fst_sub, h1, Pi.sub_apply, h2, Real.norm_eq_abs,
      sq_abs]
  · refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (h.memLp_grad.toLp g) P.ofLp.2, h.memLp_grad.coeFn_toLp] with x h1 h2
    simp only [graphPoint, WithLp.ofLp_sub, Prod.snd_sub, h1, Pi.sub_apply, h2]

theorem norm_sq_graphPoint_sub_graphPoint {u v : Torus d → ℝ} {g k : Torus d → Tangent d}
    (h : IsWeakGradient u g) (h' : IsWeakGradient v k) :
    ‖graphPoint h - graphPoint h'‖ ^ 2 =
      ∫ x, (u x - v x) ^ 2 ∂haar d + ∫ x, ‖g x - k x‖ ^ 2 ∂haar d := by
  rw [norm_sq_graphPoint_sub]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [h'.memLp.coeFn_toLp] with x hx
    simp only [graphPoint, WithLp.ofLp_toLp, hx]
  · refine integral_congr_ae ?_
    filter_upwards [h'.memLp_grad.coeFn_toLp] with x hx
    simp only [graphPoint, WithLp.ofLp_toLp, hx]

theorem integrable_norm_sq_of_memLp {g : Torus d → Tangent d} (hg : MemLp g 2 (haar d)) :
    Integrable (fun x => ‖g x‖ ^ 2) (haar d) :=
  (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg

/-- Weighted and unweighted `H¹` quantities of a difference of two weak-gradient pairs. -/
theorem weighted_diff_comparison (hw : Measurable w) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (hc : 0 < c) {u v : Torus d → ℝ} {g k : Torus d → Tangent d} (h : IsWeakGradient u g)
    (h' : IsWeakGradient v k) :
    c * (∫ x, (u x - v x) ^ 2 ∂haar d + ∫ x, ‖g x - k x‖ ^ 2 ∂haar d) ≤
        ∫ x, (u x - v x) ^ 2 * w x ∂haar d + ∫ x, ‖g x - k x‖ ^ 2 * w x ∂haar d ∧
      ∫ x, (u x - v x) ^ 2 * w x ∂haar d + ∫ x, ‖g x - k x‖ ^ 2 * w x ∂haar d ≤
        C * (∫ x, (u x - v x) ^ 2 ∂haar d + ∫ x, ‖g x - k x‖ ^ 2 ∂haar d) := by
  have hi : Integrable (fun x => (u x - v x) ^ 2) (haar d) := (h.memLp.sub h'.memLp).integrable_sq
  have hig : Integrable (fun x => ‖g x - k x‖ ^ 2) (haar d) :=
    integrable_norm_sq_of_memLp (h.memLp_grad.sub h'.memLp_grad)
  have a1 := mul_integral_le_integral_mul_weight hi (fun x => sq_nonneg _) hw hwb hc
  have a2 := mul_integral_le_integral_mul_weight hig (fun x => by positivity) hw hwb hc
  have b1 := integral_mul_weight_le hi (fun x => sq_nonneg _) hw hwb hc
  have b2 := integral_mul_weight_le hig (fun x => by positivity) hw hwb hc
  constructor <;> linarith

theorem weighted_form_complete (hw : Measurable w) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (hc : 0 < c) {u : ℕ → Torus d → ℝ} {g : ℕ → Torus d → Tangent d}
    (h : ∀ n, IsWeakGradient (u n) (g n))
    (hcau : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, N ≤ n →
      ∫ x, (u n x - u m x) ^ 2 * w x ∂haar d + ∫ x, ‖g n x - g m x‖ ^ 2 * w x ∂haar d < ε) :
    ∃ (v : Torus d → ℝ) (G : Torus d → Tangent d), IsWeakGradient v G ∧
      Tendsto (fun n => ∫ x, (u n x - v x) ^ 2 * w x ∂haar d +
        ∫ x, ‖g n x - G x‖ ^ 2 * w x ∂haar d) atTop (𝓝 0) := by
  let P : ℕ → h1Graph d := fun n => ⟨graphPoint (h n), graphPoint_mem (h n)⟩
  have hP : CauchySeq P := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcau (c * ε ^ 2) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have h1 : ‖P m - P n‖ ^ 2 < ε ^ 2 := by
      have e : ‖P m - P n‖ ^ 2 = ∫ x, (u m x - u n x) ^ 2 ∂haar d +
          ∫ x, ‖g m x - g n x‖ ^ 2 ∂haar d := norm_sq_graphPoint_sub_graphPoint (h m) (h n)
      have := (weighted_diff_comparison hw hwb hc (h m) (h n)).1
      have h2 := hN n hn m hm
      have h3 : ∫ x, (u m x - u n x) ^ 2 * w x ∂haar d = ∫ x, (u n x - u m x) ^ 2 * w x ∂haar d := by
        congr 1; funext x; ring
      have h4 : ∫ x, ‖g m x - g n x‖ ^ 2 * w x ∂haar d = ∫ x, ‖g n x - g m x‖ ^ 2 * w x ∂haar d := by
        congr 1; funext x; rw [norm_sub_rev]
      rw [e]
      by_contra hcon
      replace hcon := not_lt.mp hcon
      have := mul_le_mul_of_nonneg_left hcon hc.le
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h1
  obtain ⟨Q, hQ⟩ := cauchySeq_tendsto_of_complete hP
  have hQg : IsWeakGradient (Q.1.ofLp.1 : Torus d → ℝ) (Q.1.ofLp.2 : Torus d → Tangent d) :=
    mem_h1Graph.mp Q.2
  refine ⟨_, _, hQg, ?_⟩
  have hT : Tendsto (fun n => ‖P n - Q‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hQ
  have hT2 : Tendsto (fun n => C * ‖P n - Q‖ ^ 2) atTop (𝓝 0) := by
    simpa using (hT.pow 2).const_mul C
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hT2
  · refine add_nonneg (integral_nonneg_of_ae ?_) (integral_nonneg_of_ae ?_) <;>
      filter_upwards [hwb] with x hx <;> have := hc.le.trans hx.1 <;> positivity
  · have e : ‖P n - Q‖ ^ 2 = ‖graphPoint (h n) - Q.1‖ ^ 2 := rfl
    rw [e, norm_sq_graphPoint_sub]
    exact (weighted_diff_comparison hw hwb hc (h n) hQg).2

/-! ### Well-definedness, density, closedness in `L²(w m)` -/

theorem weightedForm_congr_ae {g g' h h' : Torus d → Tangent d} (hg : g =ᵐ[haar d] g')
    (hh : h =ᵐ[haar d] h') : weightedForm w g h = weightedForm w g' h' := by
  unfold weightedForm
  refine integral_congr_ae ?_
  filter_upwards [hg, hh] with x h1 h2
  rw [h1, h2]

theorem weightedForm_wellDefined {u v : Torus d → ℝ} {g g' k k' : Torus d → Tangent d}
    (h1 : IsWeakGradient u g) (h2 : IsWeakGradient u g') (h3 : IsWeakGradient v k)
    (h4 : IsWeakGradient v k') : weightedForm w g k = weightedForm w g' k' :=
  weightedForm_congr_ae (h1.ae_eq h2) (h3.ae_eq h4)

theorem integral_sq_mul_weight_le_of_memLp (hw : Measurable w)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) (hc : 0 < c) {f : Torus d → ℝ}
    (hf : MemLp f 2 (haar d)) : ∫ x, f x ^ 2 * w x ∂haar d ≤ C * ∫ x, f x ^ 2 ∂haar d :=
  integral_mul_weight_le hf.integrable_sq (fun _ => sq_nonneg _) hw hwb hc

theorem weighted_L2_density (hw : Measurable w) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (hc : 0 < c) {f : Torus d → ℝ} (hf : MemLp f 2 (haar d)) :
    ∃ v : ℕ → Torus d → ℝ, (∀ n, IsSmoothPeriodic (v n)) ∧
      (∀ n, IsWeakGradient (v n) (smoothGrad (v n))) ∧
      Tendsto (fun n => ∫ x, (v n x - f x) ^ 2 * w x ∂haar d) atTop (𝓝 0) := by
  refine ⟨fun n => fourierCutoff f n, fun n => isSmoothPeriodic_psum _ _,
    fun n => (isSmoothPeriodic_psum _ _).isWeakGradient, ?_⟩
  have hT : Tendsto (fun n : ℕ => C * ∫ y, (fourierCutoff f (n : ℝ) y - f y) ^ 2 ∂haar d)
      atTop (𝓝 0) := by
    simpa using ((tendsto_integral_sq_fourierCutoff_sub hf).comp
      tendsto_natCast_atTop_atTop).const_mul C
  refine squeeze_zero (fun n => integral_nonneg_of_ae ?_) (fun n => ?_) hT
  · filter_upwards [hwb] with x hx
    have := hc.le.trans hx.1
    positivity
  · exact integral_sq_mul_weight_le_of_memLp hw hwb hc ((memLp_fourierCutoff f n).sub hf)

theorem weighted_core_density (hw : Measurable w) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (hc : 0 < c) {u : Torus d → ℝ} {g : Torus d → Tangent d} (h : IsWeakGradient u g) :
    ∃ v : ℕ → Torus d → ℝ, (∀ n, IsSmoothPeriodic (v n)) ∧
      (∀ n, IsWeakGradient (v n) (smoothGrad (v n))) ∧
      Tendsto (fun n => ∫ x, (v n x - u x) ^ 2 * w x ∂haar d +
        ∫ x, ‖smoothGrad (v n) x - g x‖ ^ 2 * w x ∂haar d) atTop (𝓝 0) := by
  refine ⟨fun n => fourierCutoff u n, fun n => isSmoothPeriodic_psum _ _,
    fun n => (isSmoothPeriodic_psum _ _).isWeakGradient, ?_⟩
  have e : ∀ n : ℕ, smoothGrad (fourierCutoff u (n : ℝ)) = fourierCutoffGrad g (n : ℝ) := by
    intro n; funext x
    ext j
    rw [smoothGrad_apply, fourierCutoffGrad_apply h]
  have hT : Tendsto (fun n : ℕ => C * (∫ y, (fourierCutoff u (n : ℝ) y - u y) ^ 2 ∂haar d +
      ∫ x, ‖fourierCutoffGrad g (n : ℝ) x - g x‖ ^ 2 ∂haar d)) atTop (𝓝 0) := by
    have := ((tendsto_integral_sq_fourierCutoff_sub h.memLp).add
      (tendsto_integral_norm_sq_cutoffGrad_sub h.memLp_grad)).comp tendsto_natCast_atTop_atTop
    simpa using this.const_mul C
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hT
  · refine add_nonneg (integral_nonneg_of_ae ?_) (integral_nonneg_of_ae ?_) <;>
      filter_upwards [hwb] with x hx <;> have := hc.le.trans hx.1 <;> positivity
  · rw [e n]
    have h1 := integral_mul_weight_le (((memLp_fourierCutoff u n).sub h.memLp).integrable_sq)
      (fun x => sq_nonneg _) hw hwb hc
    have h2 := integral_mul_weight_le
      (integrable_norm_sq_of_memLp ((isWeakGradient_fourierCutoff h n).memLp_grad.sub h.memLp_grad))
      (fun x => by positivity) hw hwb hc
    simp only [Pi.sub_apply] at h1 h2
    linarith

/-- Closedness in the `L²(w m)` sense. -/
theorem weighted_form_closed (hw : Measurable w) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (hc : 0 < c) {u : ℕ → Torus d → ℝ} {g : ℕ → Torus d → Tangent d} {f : Torus d → ℝ}
    (h : ∀ n, IsWeakGradient (u n) (g n)) (hf : MemLp f 2 (haar d))
    (hlim : Tendsto (fun n => ∫ x, (u n x - f x) ^ 2 * w x ∂haar d) atTop (𝓝 0))
    (hcau : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, N ≤ n →
      ∫ x, (u n x - u m x) ^ 2 * w x ∂haar d + ∫ x, ‖g n x - g m x‖ ^ 2 * w x ∂haar d < ε) :
    ∃ G : Torus d → Tangent d, IsWeakGradient f G ∧
      Tendsto (fun n => ∫ x, (u n x - f x) ^ 2 * w x ∂haar d +
        ∫ x, ‖g n x - G x‖ ^ 2 * w x ∂haar d) atTop (𝓝 0) := by
  obtain ⟨v, G, hvG, hT⟩ := weighted_form_complete hw hwb hc h hcau
  have hu1 : Tendsto (fun n => ∫ x, (u n x - v x) ^ 2 * w x ∂haar d) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg_of_ae (by
      filter_upwards [hwb] with x hx
      have := hc.le.trans hx.1
      positivity)) (fun n => le_add_of_nonneg_right (integral_nonneg_of_ae (by
      filter_upwards [hwb] with x hx
      have := hc.le.trans hx.1
      positivity))) hT
  have hbd : ∀ n, ∫ x, (v x - f x) ^ 2 * w x ∂haar d ≤
      2 * ∫ x, (u n x - v x) ^ 2 * w x ∂haar d + 2 * ∫ x, (u n x - f x) ^ 2 * w x ∂haar d := by
    intro n
    have i1 : Integrable (fun x => (u n x - v x) ^ 2 * w x) (haar d) :=
      integrable_mul_weight ((((h n).memLp.sub hvG.memLp).integrable_sq)) hw hwb hc
    have i2 : Integrable (fun x => (u n x - f x) ^ 2 * w x) (haar d) :=
      integrable_mul_weight ((((h n).memLp.sub hf).integrable_sq)) hw hwb hc
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul 2) (i2.const_mul 2)]
    refine integral_mono_ae (integrable_mul_weight ((hvG.memLp.sub hf).integrable_sq) hw hwb hc)
      ((i1.const_mul 2).add (i2.const_mul 2)) ?_
    filter_upwards [hwb] with x hx
    have hw0 := hc.le.trans hx.1
    have : (v x - f x) ^ 2 ≤ 2 * (u n x - v x) ^ 2 + 2 * (u n x - f x) ^ 2 := by
      nlinarith [sq_nonneg (2 * u n x - v x - f x)]
    nlinarith [mul_le_mul_of_nonneg_right this hw0]
  have hlim2 : Tendsto (fun n => 2 * ∫ x, (u n x - v x) ^ 2 * w x ∂haar d +
      2 * ∫ x, (u n x - f x) ^ 2 * w x ∂haar d) atTop (𝓝 0) := by
    simpa using (hu1.const_mul 2).add (hlim.const_mul 2)
  have hle : ∫ x, (v x - f x) ^ 2 * w x ∂haar d ≤ 0 :=
    ge_of_tendsto hlim2 (Eventually.of_forall hbd)
  have hz : ∫ x, (v x - f x) ^ 2 * w x ∂haar d = 0 :=
    le_antisymm hle (integral_nonneg_of_ae (by
      filter_upwards [hwb] with x hx
      have := hc.le.trans hx.1
      positivity))
  have hnn : 0 ≤ᵐ[haar d] fun x => (v x - f x) ^ 2 * w x := by
    filter_upwards [hwb] with x hx
    have := hc.le.trans hx.1
    positivity
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn
    (integrable_mul_weight ((hvG.memLp.sub hf).integrable_sq) hw hwb hc)).mp hz
  have hvf : v =ᵐ[haar d] f := by
    filter_upwards [hae, hwb] with x hx hwx
    have hw0 : 0 < w x := hc.trans_le hwx.1
    have : (v x - f x) ^ 2 = 0 := by simpa [hw0.ne'] using hx
    have := pow_eq_zero_iff (two_ne_zero) |>.mp this
    linarith
  refine ⟨G, hvG.congr_ae hvf (Eventually.of_forall fun _ => rfl), ?_⟩
  have hint : ∀ n, ∫ x, (u n x - f x) ^ 2 * w x ∂haar d = ∫ x, (u n x - v x) ^ 2 * w x ∂haar d := by
    intro n
    refine integral_congr_ae ?_
    filter_upwards [hvf] with x hx
    rw [hx]
  simp_rw [hint]
  exact hT

end DGPS

namespace DGPS.Analysis

open DGPS

/-- FOU008: weighted form Hilbert closure.  For a fixed measurable density `0 < c ≤ w ≤ C`
(a.e.), the form `E_w(u,v) = ∫ ⟨∇u,∇v⟩ w dm` on periodic `H¹` (written on weak-gradient fields)
is comparable to the unweighted `H¹` norm, well defined, symmetric, nonnegative and bilinear;
smooth periodic functions are dense in `L²(w m)` and form cores; the form is closed (the form
norm is complete, and `L²(w m)`-limits of form-Cauchy sequences lie in `H¹`); it is Markov
(unit contraction does not increase the energy); its form ball
`{∫ u² w + E_w(u,u) ≤ M}` is sequentially relatively compact in `L²(w m)`; and constants are
exactly its zero-energy kernel. -/
theorem weighted_form_hilbert_closure (d : ℕ) (w : Torus d → ℝ) (c C : ℝ)
    (hw : Measurable w) (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) :
    -- norm comparison with the unweighted `H¹` norm
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g →
      c * (∫ x, u x ^ 2 ∂haar d + ∫ x, ‖g x‖ ^ 2 ∂haar d) ≤
          ∫ x, u x ^ 2 * w x ∂haar d + weightedForm w g g ∧
        ∫ x, u x ^ 2 * w x ∂haar d + weightedForm w g g ≤
          C * (∫ x, u x ^ 2 ∂haar d + ∫ x, ‖g x‖ ^ 2 ∂haar d)) ∧
    -- the form is independent of the chosen weak gradients
    (∀ (u v : Torus d → ℝ) (g g' k k' : Torus d → Tangent d), IsWeakGradient u g →
      IsWeakGradient u g' → IsWeakGradient v k → IsWeakGradient v k' →
      weightedForm w g k = weightedForm w g' k') ∧
    -- symmetric, nonnegative, bilinear
    (∀ g k : Torus d → Tangent d, weightedForm w g k = weightedForm w k g) ∧
    (∀ g : Torus d → Tangent d, 0 ≤ weightedForm w g g) ∧
    (∀ g₁ g₂ k : Torus d → Tangent d, MemLp g₁ 2 (haar d) → MemLp g₂ 2 (haar d) →
      MemLp k 2 (haar d) →
      weightedForm w (fun x => g₁ x + g₂ x) k = weightedForm w g₁ k + weightedForm w g₂ k) ∧
    (∀ (a : ℝ) (g k : Torus d → Tangent d),
      weightedForm w (fun x => a • g x) k = a * weightedForm w g k) ∧
    -- density: smooth periodic functions are dense in `L²(w m)`
    (∀ f : Torus d → ℝ, MemLp f 2 (haar d) → ∃ v : ℕ → Torus d → ℝ,
      (∀ n, IsSmoothPeriodic (v n)) ∧ (∀ n, IsWeakGradient (v n) (smoothGrad (v n))) ∧
      Tendsto (fun n => ∫ x, (v n x - f x) ^ 2 * w x ∂haar d) atTop (𝓝 0)) ∧
    -- density: smooth periodic functions form a core for the form
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g →
      ∃ v : ℕ → Torus d → ℝ, (∀ n, IsSmoothPeriodic (v n)) ∧
        (∀ n, IsWeakGradient (v n) (smoothGrad (v n))) ∧
        Tendsto (fun n => ∫ x, (v n x - u x) ^ 2 * w x ∂haar d +
          weightedForm w (fun x => smoothGrad (v n) x - g x) (fun x => smoothGrad (v n) x - g x))
          atTop (𝓝 0)) ∧
    -- closed: the form norm is complete
    (∀ (u : ℕ → Torus d → ℝ) (g : ℕ → Torus d → Tangent d), (∀ n, IsWeakGradient (u n) (g n)) →
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, N ≤ n →
        ∫ x, (u n x - u m x) ^ 2 * w x ∂haar d + ∫ x, ‖g n x - g m x‖ ^ 2 * w x ∂haar d < ε) →
      ∃ (v : Torus d → ℝ) (G : Torus d → Tangent d), IsWeakGradient v G ∧
        Tendsto (fun n => ∫ x, (u n x - v x) ^ 2 * w x ∂haar d +
          ∫ x, ‖g n x - G x‖ ^ 2 * w x ∂haar d) atTop (𝓝 0)) ∧
    -- closed: `L²(w m)`-limits of form-Cauchy sequences lie in `H¹`
    (∀ (u : ℕ → Torus d → ℝ) (g : ℕ → Torus d → Tangent d) (f : Torus d → ℝ),
      (∀ n, IsWeakGradient (u n) (g n)) → MemLp f 2 (haar d) →
      Tendsto (fun n => ∫ x, (u n x - f x) ^ 2 * w x ∂haar d) atTop (𝓝 0) →
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, N ≤ n →
        ∫ x, (u n x - u m x) ^ 2 * w x ∂haar d + ∫ x, ‖g n x - g m x‖ ^ 2 * w x ∂haar d < ε) →
      ∃ G : Torus d → Tangent d, IsWeakGradient f G ∧
        Tendsto (fun n => ∫ x, (u n x - f x) ^ 2 * w x ∂haar d +
          ∫ x, ‖g n x - G x‖ ^ 2 * w x ∂haar d) atTop (𝓝 0)) ∧
    -- Markov: the unit contraction does not increase the energy
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g →
      ∃ g' : Torus d → Tangent d, IsWeakGradient (fun x => min (max (u x) 0) 1) g' ∧
        weightedForm w g' g' ≤ weightedForm w g g) ∧
    -- relative compactness of the form ball in `L²(w m)`
    (∀ (u : ℕ → Torus d → ℝ) (g : ℕ → Torus d → Tangent d) (M : ℝ),
      (∀ n, IsWeakGradient (u n) (g n)) →
      (∀ n, ∫ x, u n x ^ 2 * w x ∂haar d + weightedForm w (g n) (g n) ≤ M) →
      ∃ (φ : ℕ → ℕ) (v : Torus d → ℝ), StrictMono φ ∧ MemLp v 2 (haar d) ∧
        Tendsto (fun n => ∫ x, (u (φ n) x - v x) ^ 2 * w x ∂haar d) atTop (𝓝 0)) ∧
    -- constants are exactly the zero-energy kernel
    (∀ a : ℝ, IsWeakGradient (fun _ : Torus d => a) (fun _ => 0) ∧
      weightedForm w (fun _ => (0 : Tangent d)) (fun _ => 0) = 0) ∧
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g →
      (weightedForm w g g = 0 ↔ ∃ a : ℝ, u =ᵐ[haar d] fun _ => a)) := by
  refine ⟨fun u g h => ?_, fun u v g g' k k' h1 h2 h3 h4 => weightedForm_wellDefined h1 h2 h3 h4,
    fun g k => weightedForm_comm g k, fun g => weightedForm_nonneg hwb hc g,
    fun g₁ g₂ k h₁ h₂ hk => weightedForm_add_left hw hwb hc h₁ h₂ hk,
    fun a g k => weightedForm_smul_left a g k,
    fun f hf => weighted_L2_density hw hwb hc hf, fun u g h => ?_, fun u g h hcau => ?_,
    fun u g f h hf hlim hcau => weighted_form_closed hw hwb hc h hf hlim hcau,
    fun u g h => ?_, fun u g M h hM => ?_, fun a => ?_, fun u g h => ?_⟩
  · simpa only [weightedForm_self] using weighted_norm_comparison hw hwb hc h
  · obtain ⟨v, hv, hvg, hT⟩ := weighted_core_density hw hwb hc h
    exact ⟨v, hv, hvg, by simpa only [weightedForm_self] using hT⟩
  · exact weighted_form_complete hw hwb hc h hcau
  · obtain ⟨g', hg', hle⟩ := markov_unit_contraction hw hwb hc h
    exact ⟨g', hg', by simpa only [weightedForm_self] using hle⟩
  · exact exists_subseq_tendsto_weighted_of_h1_bounded u g M hw hwb hc h
      (fun n => by simpa only [weightedForm_self] using hM n)
  · refine ⟨isWeakGradient_const a, ?_⟩
    simp [weightedForm]
  · rw [weightedForm_self]
    exact energy_zero_iff hw hwb hc h

end DGPS.Analysis
