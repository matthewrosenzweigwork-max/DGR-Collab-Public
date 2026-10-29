import DGPS.Analysis.BoundedPerturbation
import DGPS.Analysis.CircleLSI

/-!
# Frozen Gibbs map: uniform bounds, weak continuity, and the frozen rate (STR001)

Source: `campaign/frozen_gibbs_rate_comparison.md` §2, `campaign/stationary_criterion_exact_manuscript_regularity.md`
§1.  For continuous (and, where stated, direct Lipschitz) data `A = (V, W)` and EVERY Borel
probability `ν` on `𝕋^d` (singular `ν` included), `p_ν = exp(-V - W*ν) / ∫ exp(-V - W*ν) dm`
(`DGPS.frozenGibbs`, with `(W*ν)(x) = ∫ W x y dν(y)` evaluated pointwise through the continuous
representative, never through an a.e. weak gradient).  With `M = osc V + osc W`
(`DGPS.totalOscillation`):

* `frozenGibbs_uniform_bounds`: `e^{-M} ≤ p_ν ≤ e^{M}`, `sup p_ν ≤ e^{M} inf p_ν`, and one Lipschitz
  constant for all `p_ν`;
* `frozenGibbs_weak_to_uniform`: weak convergence `ν_n → ν` (along any filter) implies
  `p_{ν_n} → p_ν` uniformly;
* `frozenLSRateInf_ge_lowerBound`: `0 < ℓ₀ := 4π² e^{-M} ≤ ℓ := inf_ν r_LS(P_ν) < ∞` for `d ≥ 1`.
  `ℓ` is `DGPS.frozenLSRateInf A` and `ℓ₀` is the explicit real number; they are separate objects.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace DGPS.Structural

variable {d : ℕ}

/-! ### Uniform two-sided, oscillation and Lipschitz bounds -/

/-- **STR001 (uniform bounds).**  For every probability `ν` (singular allowed) the frozen density
satisfies `e^{-M} ≤ p_ν ≤ e^{M}` and `sup p_ν ≤ e^{M} inf p_ν`, `M = osc V + osc W`; for direct
Lipschitz data all `p_ν` are Lipschitz with one constant. -/
theorem frozenGibbs_uniform_bounds (A : InteractionData d) (hLip : LipschitzData A) :
    (∀ (ν : ProbabilityMeasure (Torus d)) (x : Torus d),
      Real.exp (-totalOscillation A) ≤ (frozenGibbs A ν).density x ∧
        (frozenGibbs A ν).density x ≤ Real.exp (totalOscillation A)) ∧
    (∀ ν : ProbabilityMeasure (Torus d),
      sSup (Set.range (frozenGibbs A ν).density) ≤
        Real.exp (totalOscillation A) * sInf (Set.range (frozenGibbs A ν).density)) ∧
    (∃ L : ℝ, 0 ≤ L ∧ ∀ ν : ProbabilityMeasure (Torus d),
      TorusLipschitzWith L (frozenGibbs A ν).density) := by
  have hratio : ∀ (ν : ProbabilityMeasure (Torus d)) (x y : Torus d),
      (frozenGibbs A ν).density x ≤
        Real.exp (totalOscillation A) * (frozenGibbs A ν).density y := by
    intro ν x y
    have hZ := frozenPartition_pos A (ν : Measure (Torus d))
    show frozenDensity A (ν : Measure (Torus d)) x ≤
      Real.exp (totalOscillation A) * frozenDensity A (ν : Measure (Torus d)) y
    unfold frozenDensity
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hZ, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by
      linarith [frozenPotential_oscillation_le A (ν : Measure (Torus d)) y x])
  have hbd : ∀ (ν : ProbabilityMeasure (Torus d)) (x : Torus d),
      Real.exp (-totalOscillation A) ≤ (frozenGibbs A ν).density x ∧
        (frozenGibbs A ν).density x ≤ Real.exp (totalOscillation A) := by
    intro ν x
    have hZ := frozenPartition_pos A (ν : Measure (Torus d))
    have hint := integrable_exp_neg_frozenPotential A (ν : Measure (Torus d))
    have hup : frozenPartition A (ν : Measure (Torus d)) ≤
        Real.exp (-frozenPotential A (ν : Measure (Torus d)) x) *
          Real.exp (totalOscillation A) := by
      have := integral_mono hint (integrable_const (Real.exp (-frozenPotential A
        (ν : Measure (Torus d)) x) * Real.exp (totalOscillation A)))
        (fun y => by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.2 (by
            linarith [frozenPotential_oscillation_le A (ν : Measure (Torus d)) x y]))
      simpa [frozenPartition] using this
    have hlo : Real.exp (-frozenPotential A (ν : Measure (Torus d)) x) *
        Real.exp (-totalOscillation A) ≤ frozenPartition A (ν : Measure (Torus d)) := by
      have := integral_mono (integrable_const (Real.exp (-frozenPotential A
        (ν : Measure (Torus d)) x) * Real.exp (-totalOscillation A))) hint
        (fun y => by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.2 (by
            linarith [frozenPotential_oscillation_le A (ν : Measure (Torus d)) y x]))
      simpa [frozenPartition] using this
    have hpos := Real.exp_pos (-frozenPotential A (ν : Measure (Torus d)) x)
    show Real.exp (-totalOscillation A) ≤
        frozenDensity A (ν : Measure (Torus d)) x ∧
      frozenDensity A (ν : Measure (Torus d)) x ≤ Real.exp (totalOscillation A)
    unfold frozenDensity
    constructor
    · rw [le_div_iff₀ hZ]
      calc Real.exp (-totalOscillation A) * frozenPartition A (ν : Measure (Torus d))
          ≤ Real.exp (-totalOscillation A) * (Real.exp (-frozenPotential A
              (ν : Measure (Torus d)) x) * Real.exp (totalOscillation A)) :=
            mul_le_mul_of_nonneg_left hup (Real.exp_pos _).le
        _ = Real.exp (-frozenPotential A (ν : Measure (Torus d)) x) := by
            have e1 : Real.exp (-totalOscillation A) * Real.exp (totalOscillation A) = 1 := by
              rw [← Real.exp_add]; simp
            linear_combination (Real.exp (-frozenPotential A (ν : Measure (Torus d)) x)) * e1
    · rw [div_le_iff₀ hZ]
      calc Real.exp (-frozenPotential A (ν : Measure (Torus d)) x)
          = Real.exp (totalOscillation A) * (Real.exp (-frozenPotential A
              (ν : Measure (Torus d)) x) * Real.exp (-totalOscillation A)) := by
            have e1 : Real.exp (-totalOscillation A) * Real.exp (totalOscillation A) = 1 := by
              rw [← Real.exp_add]; simp
            linear_combination (-Real.exp (-frozenPotential A (ν : Measure (Torus d)) x)) * e1
        _ ≤ Real.exp (totalOscillation A) * frozenPartition A (ν : Measure (Torus d)) :=
            mul_le_mul_of_nonneg_left hlo (Real.exp_pos _).le
  refine ⟨hbd, fun ν => ?_, ?_⟩
  · have hne : (Set.range (frozenGibbs A ν).density).Nonempty := Set.range_nonempty _
    refine csSup_le hne ?_
    rintro _ ⟨x, rfl⟩
    rw [← div_le_iff₀' (Real.exp_pos _)]
    refine le_csInf hne ?_
    rintro _ ⟨y, rfl⟩
    rw [div_le_iff₀' (Real.exp_pos _)]
    exact hratio ν x y
  · obtain ⟨L, hL0, hL⟩ := frozenGibbs_lipschitz A hLip
    exact ⟨L, hL0, hL⟩

/-! ### Weak convergence implies uniform convergence of the frozen densities -/

/-- Convolution against a continuous kernel is uniformly continuous in the point, uniformly in the
probability measure: for `|W x y - W x' y| ≤ c` for every `y`, the potentials differ by `≤ c`. -/
theorem abs_integral_W_sub_le (A : InteractionData d) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] {x x' : Torus d} {c : ℝ} (h : ∀ y, |A.W x y - A.W x' y| ≤ c) :
    |(∫ y, A.W x y ∂μ) - ∫ y, A.W x' y ∂μ| ≤ c := by
  have hint : ∀ x : Torus d, Integrable (fun z => A.W x z) μ := fun x =>
    (A.W_continuous_right x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub (hint x) (hint x')]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => A.W x y - A.W x' y) (C := c)
    (Eventually.of_forall fun y => by simpa using h y)
  simpa using this

/-- Weak convergence `ν_n → ν` makes the potentials `x ↦ ∫ W x y dν_n(y)` converge uniformly
(finite uniform net of the compact equicontinuous family `y ↦ W(x, y)`). -/
theorem eventually_abs_integral_W_sub_lt (A : InteractionData d) {ι : Type*} {l : Filter ι}
    {νs : ι → ProbabilityMeasure (Torus d)} {ν : ProbabilityMeasure (Torus d)}
    (h : Tendsto νs l (𝓝 ν)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in l, ∀ x : Torus d,
      |(∫ y, A.W x y ∂(νs n : Measure (Torus d))) - ∫ y, A.W x y ∂(ν : Measure (Torus d))| < ε := by
  have huc : UniformContinuous (fun p : Torus d × Torus d => A.W p.1 p.2) :=
    CompactSpace.uniformContinuous_of_continuous A.W_continuous
  obtain ⟨δ, hδ, hδW⟩ := Metric.uniformContinuous_iff.1 huc (ε / 3) (by positivity)
  obtain ⟨t, -, htfin, htcov⟩ := finite_cover_balls_of_compact
    (isCompact_univ (X := Torus d)) hδ
  have hclose : ∀ {x x' : Torus d}, dist x x' < δ → ∀ y, |A.W x y - A.W x' y| ≤ ε / 3 := by
    intro x x' hxx y
    have hd : dist (x, y) (x', y) < δ := by
      rw [Prod.dist_eq]
      simpa using hxx
    have := hδW hd
    rw [Real.dist_eq] at this
    exact this.le
  have hconv : ∀ i ∈ t, ∀ᶠ n in l,
      |(∫ y, A.W i y ∂(νs n : Measure (Torus d))) - ∫ y, A.W i y ∂(ν : Measure (Torus d))| <
        ε / 3 := by
    intro i _
    have hT := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h)
      (BoundedContinuousFunction.mkOfCompact ⟨fun y => A.W i y, A.W_continuous_right i⟩)
    have := Metric.tendsto_nhds.1 hT (ε / 3) (by positivity)
    filter_upwards [this] with n hn
    simpa [Real.dist_eq] using hn
  filter_upwards [(Filter.eventually_all_finite htfin).2 hconv] with n hn x
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (htcov (Set.mem_univ x))
  have hxi' : dist x i < δ := hxi
  have h1 := abs_integral_W_sub_le A (νs n : Measure (Torus d)) (hclose hxi')
  have h2 := abs_integral_W_sub_le A (ν : Measure (Torus d)) (hclose hxi')
  have h3 := hn i hi
  calc _ = |((∫ y, A.W x y ∂(νs n : Measure (Torus d))) - ∫ y, A.W i y ∂(νs n : Measure (Torus d)))
          + ((∫ y, A.W i y ∂(νs n : Measure (Torus d))) - ∫ y, A.W i y ∂(ν : Measure (Torus d)))
          - ((∫ y, A.W x y ∂(ν : Measure (Torus d))) - ∫ y, A.W i y ∂(ν : Measure (Torus d)))| := by
        congr 1; ring
    _ ≤ |(∫ y, A.W x y ∂(νs n : Measure (Torus d))) - ∫ y, A.W i y ∂(νs n : Measure (Torus d))|
          + |(∫ y, A.W i y ∂(νs n : Measure (Torus d))) - ∫ y, A.W i y ∂(ν : Measure (Torus d))|
          + |(∫ y, A.W x y ∂(ν : Measure (Torus d))) - ∫ y, A.W i y ∂(ν : Measure (Torus d))| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ < ε := by linarith

/-- Pure real-number step: the quotient `a / Zm` is Lipschitz in `(a, Zm)` on the relevant range. -/
theorem quotient_sub_le {a b Zm Zn E δ : ℝ} (hE : 0 < E) (hδ : 0 ≤ δ) (hZm : E⁻¹ ≤ Zm)
    (hZn : E⁻¹ ≤ Zn) (hb0 : 0 ≤ b) (hb : b ≤ E) (hab : |a - b| ≤ E * δ)
    (hZ : |Zn - Zm| ≤ E * δ) :
    |a / Zm - b / Zn| ≤ (E ^ 2 + E ^ 4) * δ := by
  have hEi : 0 < E⁻¹ := inv_pos.2 hE
  have hZm0 : 0 < Zm := lt_of_lt_of_le hEi hZm
  have hZn0 : 0 < Zn := lt_of_lt_of_le hEi hZn
  have e : a / Zm - b / Zn = (a - b) / Zm + b * (Zn - Zm) / (Zm * Zn) := by
    field_simp
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have t1 : |(a - b) / Zm| ≤ E ^ 2 * δ := by
    rw [abs_div, abs_of_pos hZm0]
    calc |a - b| / Zm ≤ (E * δ) / E⁻¹ :=
          div_le_div₀ (by positivity) hab hEi hZm
      _ = E ^ 2 * δ := by field_simp
  have t2 : |b * (Zn - Zm) / (Zm * Zn)| ≤ E ^ 4 * δ := by
    rw [abs_div, abs_of_pos (mul_pos hZm0 hZn0), abs_mul, abs_of_nonneg hb0]
    calc b * |Zn - Zm|
        / (Zm * Zn) ≤ (E * (E * δ)) / (E⁻¹ * E⁻¹) := by
          refine div_le_div₀ (by positivity) (mul_le_mul hb hZ (abs_nonneg _) hE.le)
            (by positivity) (mul_le_mul hZm hZn hEi.le hZm0.le)
      _ = E ^ 4 * δ := by field_simp
  linarith

/-- Deterministic stability: two frozen densities whose potentials are `δ`-close are `C δ`-close,
with `C` depending only on the sup bound of the data. -/
theorem frozenDensity_sub_le (A : InteractionData d) (μ ν : Measure (Torus d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {δ : ℝ} (hδ : 0 ≤ δ)
    (hpot : ∀ x, |frozenPotential A μ x - frozenPotential A ν x| ≤ δ) (x : Torus d) :
    |frozenDensity A μ x - frozenDensity A ν x| ≤
      (Real.exp (frozenSupBound A) ^ 2 + Real.exp (frozenSupBound A) ^ 4) * δ := by
  set K := frozenSupBound A with hK
  have hEpos : 0 < Real.exp K := Real.exp_pos K
  have hinv : (Real.exp K)⁻¹ = Real.exp (-K) := (Real.exp_neg K).symm
  have hexp : ∀ y, |Real.exp (-frozenPotential A μ y) - Real.exp (-frozenPotential A ν y)| ≤
      Real.exp K * δ := by
    intro y
    have h1 := abs_le.1 (abs_frozenPotential_le A μ y)
    have h2 := abs_le.1 (abs_frozenPotential_le A ν y)
    exact (abs_exp_neg_sub_exp_neg_le (K := K) (by linarith) (by linarith)).trans
      (mul_le_mul_of_nonneg_left (hpot y) hEpos.le)
  have hZ : |frozenPartition A ν - frozenPartition A μ| ≤ Real.exp K * δ := by
    unfold frozenPartition
    rw [← integral_sub (integrable_exp_neg_frozenPotential A ν)
      (integrable_exp_neg_frozenPotential A μ)]
    have := norm_integral_le_of_norm_le_const (μ := haar d)
      (f := fun y => Real.exp (-frozenPotential A ν y) - Real.exp (-frozenPotential A μ y))
      (C := Real.exp K * δ) (Eventually.of_forall fun y => by
        simpa [abs_sub_comm] using hexp y)
    simpa using this
  have hZm := (frozenPartition_bounds A μ).1
  have hZn := (frozenPartition_bounds A ν).1
  have hb := exp_neg_frozenPotential_bounds A ν x
  unfold frozenDensity
  exact quotient_sub_le hEpos hδ (by rwa [hinv]) (by rwa [hinv]) (Real.exp_pos _).le hb.2
    (hexp x) hZ

/-- **STR001 (weak convergence gives uniform convergence).**  If `ν_n → ν` weakly (along any
filter; `ν_n`, `ν` arbitrary Borel probabilities, singular allowed), then
`‖p_{ν_n} - p_ν‖_∞ → 0`. -/
theorem frozenGibbs_weak_to_uniform (A : InteractionData d) {ι : Type*} {l : Filter ι}
    (νs : ι → ProbabilityMeasure (Torus d)) (ν : ProbabilityMeasure (Torus d))
    (h : Tendsto νs l (𝓝 ν)) :
    TendstoUniformly (fun n x => (frozenGibbs A (νs n)).density x)
      (frozenGibbs A ν).density l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  set C : ℝ := Real.exp (frozenSupBound A) ^ 2 + Real.exp (frozenSupBound A) ^ 4 with hC
  have hCpos : 0 < C := by positivity
  filter_upwards [eventually_abs_integral_W_sub_lt A h (ε := ε / (2 * C)) (by positivity)]
    with n hn x
  have hpot : ∀ y, |frozenPotential A (νs n : Measure (Torus d)) y -
      frozenPotential A (ν : Measure (Torus d)) y| ≤ ε / (2 * C) := by
    intro y
    have : frozenPotential A (νs n : Measure (Torus d)) y -
        frozenPotential A (ν : Measure (Torus d)) y =
        (∫ z, A.W y z ∂(νs n : Measure (Torus d))) - ∫ z, A.W y z ∂(ν : Measure (Torus d)) := by
      unfold frozenPotential
      ring
    rw [this]
    exact (hn y).le
  have key := frozenDensity_sub_le A (νs n : Measure (Torus d)) (ν : Measure (Torus d))
    (by positivity) hpot x
  rw [Real.dist_eq, abs_sub_comm]
  show |frozenDensity A (νs n : Measure (Torus d)) x - frozenDensity A (ν : Measure (Torus d)) x| < ε
  calc _ ≤ C * (ε / (2 * C)) := key
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-! ### The actual frozen rate is finite and bounded below by `4π² e^{-M}` -/

/-- Zero relative entropy for a.e.-constant nonnegative functions. -/
theorem homogeneousEntropy_eq_zero_of_ae_const {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {v : Torus d → ℝ} (hv : 0 ≤ᵐ[μ] v) (hm : AEMeasurable v μ) {c : ℝ}
    (h : v =ᵐ[μ] fun _ => c) : homogeneousEntropy μ v = 0 := by
  have hint : ∫ x, v x ∂μ = c := by
    rw [integral_congr_ae h]
    simp
  by_cases hc : c = 0
  · exact homogeneousEntropy_of_integral_eq_zero (by rw [hint, hc])
  · have hcpos : 0 < c := lt_of_le_of_ne (by rw [← hint]; exact integral_nonneg_of_ae hv)
      (Ne.symm hc)
    exact (homogeneousEntropy_eq_zero_iff hv hm (by rw [hint]; exact hcpos)).2 (by
      rw [hint]; exact h)

/-- For `d ≥ 1`, every bounded positive reference has a finite ordinary LS rate: the sharpness of
the Haar LSI supplies one `H¹` competitor of positive entropy (then it also has positive entropy
for the equivalent measure `P`). -/
theorem ordinaryLSRate_lt_top (hd : 0 < d) (P : BoundedPositiveReference d) :
    ordinaryLSRate P < ⊤ := by
  have hn : ¬ Analysis.HaarLSI d (4 * Real.pi ^ 2 + 1) := fun H => by
    have := (haar_lsi_sharp hd).2.1 _ H
    linarith
  unfold Analysis.HaarLSI at hn
  push Not at hn
  obtain ⟨f, g, hfg, hlt⟩ := hn
  have hEntm : homogeneousEntropy (haar d) (fun x => f x ^ 2) ≠ 0 := by
    intro h0
    rw [h0] at hlt
    exact absurd hlt (not_lt.2 bot_le)
  have hm : AEMeasurable (fun x => f x ^ 2) (haar d) :=
    (hfg.memLp.aestronglyMeasurable.aemeasurable).pow_const 2
  have hnn : 0 ≤ᵐ[haar d] fun x => f x ^ 2 := Eventually.of_forall fun x => sq_nonneg (f x)
  have hW := (isWeightedWeakGradient_iff P).2 hfg
  have hfH : f ∈ WeightedH1 P := ⟨g, hW⟩
  have hpos : 0 < homogeneousEntropy P.measure (fun x => f x ^ 2) := by
    rw [pos_iff_ne_zero]
    intro h0
    have hmP : AEMeasurable (fun x => f x ^ 2) P.measure := hm.mono_ac P.measure_ac_haar
    have hnnP : 0 ≤ᵐ[P.measure] fun x => f x ^ 2 := P.measure_ac_haar.ae_le hnn
    have hiP : Integrable (fun x => f x ^ 2) P.measure := hW.memLp.integrable_sq
    by_cases hI : ∫ x, f x ^ 2 ∂P.measure = 0
    · have hz : (fun x => f x ^ 2) =ᵐ[P.measure] 0 :=
        (integral_eq_zero_iff_of_nonneg_ae hnnP hiP).1 hI
      exact hEntm (homogeneousEntropy_eq_zero_of_ae_const hnn hm (c := 0)
        (P.haar_ac_measure.ae_le hz))
    · have hIpos : 0 < ∫ x, f x ^ 2 ∂P.measure :=
        lt_of_le_of_ne (integral_nonneg_of_ae hnnP) (Ne.symm hI)
      have hc := (homogeneousEntropy_eq_zero_iff hnnP hmP hIpos).1 h0
      exact hEntm (homogeneousEntropy_eq_zero_of_ae_const hnn hm
        (P.haar_ac_measure.ae_le hc))
  have hW' := isWeightedWeakGradient_weightedGradient P hfH
  have hEtop : ∫⁻ x, ‖weightedGradient P f hfH x‖ₑ ^ 2 ∂P.measure ≠ ⊤ := by
    have hi : Integrable (fun x => ‖weightedGradient P f hfH x‖ ^ 2) P.measure :=
      hW'.memLp_grad.norm.integrable_sq
    have := hi.lintegral_lt_top
    refine ne_of_lt (lt_of_eq_of_lt (lintegral_congr fun x => ?_) this)
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  unfold ordinaryLSRate
  refine lt_of_le_of_lt (iInf_le_of_le ⟨f, hfH, hpos⟩ le_rfl) ?_
  exact ENNReal.div_lt_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hEtop) hpos.ne'

/-- **STR001 (the actual frozen rate).**  For `d ≥ 1` and all continuous data `A`:
`0 < ℓ₀ := 4π² e^{-M}`, `ℓ₀ ≤ ℓ := inf_ν r_LS(P_ν)` over every Borel probability `ν`, and
`ℓ < ∞`.  (`ℓ = frozenLSRateInf A` and the explicit real number `ℓ₀` are separate objects.) -/
theorem frozenLSRateInf_ge_lowerBound (hd : 0 < d) (A : InteractionData d) :
    0 < 4 * Real.pi ^ 2 * Real.exp (-totalOscillation A) ∧
      ENNReal.ofReal (4 * Real.pi ^ 2 * Real.exp (-totalOscillation A)) ≤ frozenLSRateInf A ∧
      frozenLSRateInf A < ⊤ := by
  refine ⟨by positivity, ?_, ?_⟩
  · have := frozenLSRateInf_lower_bound d hd A
    simpa [a0] using this
  · exact lt_of_le_of_lt (frozenLSRateInf_le A ⟨haar d, inferInstance⟩)
      (ordinaryLSRate_lt_top hd _)

end DGPS.Structural
