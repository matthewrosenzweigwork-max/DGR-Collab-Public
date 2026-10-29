import DGPS.Examples.RoughBoundary.Feature
import DGPS.Examples.RoughBoundary.FeatureMoments
import DGPS.Examples.RoughBoundary.ThreeState

/-!
# Pushforward convergence to three states (RUF020)

Source `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 3.1.  The densities `Q_L` concentrate
at `0, 1/3, 2/3`; `A_L(s) → 1/6` on `(0, 1/3)` (with `A_L(1/6) = 1/6` by evenness and a
Laplace-type bound); by `A_L(s + 1/3) = A_L(s) + 1/3` the phase `A_L(2x) - 1/6` converges to
`⌊6x⌋/3` almost everywhere, and bounded convergence gives the weak limit of `(U_{L,ε_L})_# m`.

Main result: `DGPS.Examples.RoughBoundary.Landscape.pushforward_convergence_to_three_states`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff BoundedContinuousFunction ENNReal

namespace DGPS.Examples.RoughBoundary.Landscape

open DGPS.Examples.RoughBoundary.Feature
open DGPS.Examples.RoughBoundary.Spikes (gT pt hMean)
open DGPS.Examples.RoughBoundary.ThreeState

lemma qdens_reflect (L t : ℝ) : Qdens L (1 / 3 - t) = Qdens L t := by
  unfold Qdens
  have : Real.cos (6 * π * (1 / 3 - t)) = Real.cos (6 * π * t) := by
    have : 6 * π * (1 / 3 - t) = 2 * π - 6 * π * t := by ring
    rw [this, Real.cos_two_pi_sub]
  rw [this]

lemma aprim_sixth {L : ℝ} (hL : 0 < L) : Aprim L (1 / 6) = 1 / 6 := by
  have h1 : ∫ t in (0 : ℝ)..1 / 6, Qdens L t = ∫ t in (1 / 6 : ℝ)..1 / 3, Qdens L t := by
    have := intervalIntegral.integral_comp_sub_left (fun t => Qdens L t) (a := (0 : ℝ))
      (b := 1 / 6) (1 / 3)
    simp only [qdens_reflect] at this
    rw [this]; norm_num
  have h2 := intervalIntegral.integral_add_adjacent_intervals (qdens_ii L 0 (1 / 6))
    (qdens_ii L (1 / 6) (1 / 3))
  rw [integral_qdens_third hL] at h2
  unfold Aprim
  linarith

lemma cos_le_of_mem {m t : ℝ} (hm : 0 < m) (hm6 : m ≤ 1 / 6) (h1 : m ≤ t) (h2 : t ≤ 1 / 3 - m) :
    Real.cos (6 * π * t) ≤ Real.cos (6 * π * m) := by
  rcases le_total t (1 / 6) with h | h
  · apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos]) 
    nlinarith [Real.pi_pos]
  · have : Real.cos (6 * π * t) = Real.cos (6 * π * (1 / 3 - t)) := by
      have : 6 * π * (1 / 3 - t) = 2 * π - 6 * π * t := by ring
      rw [this, Real.cos_two_pi_sub]
    rw [this]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]) 
    nlinarith [Real.pi_pos]

lemma zpart_ge {L : ℝ} (hL : 0 < L) {δ : ℝ} (hδ : 0 < δ) (hδ6 : δ ≤ 1 / 6) :
    δ * Real.exp (L * Real.cos (6 * π * δ)) ≤ Zpart L := by
  unfold Zpart
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => Real.exp (L * Real.cos (6 * π * t))) volume a b :=
    fun a b => (continuous_expcos L).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 δ) (hi δ 1)]
  have h2 : 0 ≤ ∫ t in δ..1, Real.exp (L * Real.cos (6 * π * t)) :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => (Real.exp_pos _).le
  have h1 : ∫ t in (0:ℝ)..δ, Real.exp (L * Real.cos (6 * π * δ)) ≤
      ∫ t in (0:ℝ)..δ, Real.exp (L * Real.cos (6 * π * t)) := by
    apply intervalIntegral.integral_mono_on hδ.le intervalIntegrable_const (hi 0 δ)
    intro t ht
    apply Real.exp_le_exp.2
    apply mul_le_mul_of_nonneg_left _ hL.le
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith [ht.1, Real.pi_pos]) (by nlinarith [Real.pi_pos]) 
    nlinarith [ht.2, Real.pi_pos]
  simp at h1
  linarith

lemma qdens_small {L : ℝ} (hL : 0 < L) {m t : ℝ} (hm : 0 < m) (hm6 : m ≤ 1 / 6) (h1 : m ≤ t)
    (h2 : t ≤ 1 / 3 - m) :
    Qdens L t ≤ 2 / m * Real.exp (-(L * (Real.cos (3 * π * m) - Real.cos (6 * π * m)))) := by
  have hz := zpart_ge hL (δ := m / 2) (by positivity) (by linarith)
  have hzp : 0 < Zpart L := zpart_pos hL
  have hc := cos_le_of_mem hm hm6 h1 h2
  unfold Qdens
  have e : 6 * π * (m / 2) = 3 * π * m := by ring
  rw [e] at hz
  rw [div_le_iff₀ hzp]
  have : Real.exp (L * Real.cos (6 * π * t)) ≤ Real.exp (L * Real.cos (6 * π * m)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hc hL.le)
  have e2 : Real.exp (L * Real.cos (6 * π * m)) =
      Real.exp (-(L * (Real.cos (3 * π * m) - Real.cos (6 * π * m)))) *
        Real.exp (L * Real.cos (3 * π * m)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp (L * Real.cos (6 * π * t)) ≤ _ := this
    _ = 2 / m * Real.exp (-(L * (Real.cos (3 * π * m) - Real.cos (6 * π * m)))) *
        (m / 2 * Real.exp (L * Real.cos (3 * π * m))) := by
      rw [e2]; field_simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left hz (by positivity)

lemma aprim_tendsto {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 3)) :
    Tendsto (fun L => Aprim L s) atTop (𝓝 (1 / 6)) := by
  obtain ⟨hs0, hs1⟩ := hs
  set m := min s (1 / 3 - s) with hm
  have hm0 : 0 < m := lt_min hs0 (by linarith)
  have hm6 : m ≤ 1 / 6 := by
    rcases le_total s (1 / 6) with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)
  have hms : m ≤ s := min_le_left _ _
  have hms' : m ≤ 1 / 3 - s := min_le_right _ _
  set c := Real.cos (3 * π * m) - Real.cos (6 * π * m) with hc
  have hcpos : 0 < c := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 3 * π * m) (y := 6 * π * m)
      (by positivity) (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    rw [hc]; linarith
  have hlim : Tendsto (fun L : ℝ => 2 / m * Real.exp (-(L * c)) * (1 / 3)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun L : ℝ => -(L * c)) atTop atBot := by
      apply tendsto_neg_atTop_atBot.comp
      exact tendsto_id.atTop_mul_const hcpos
    have h2 := Real.tendsto_exp_atBot.comp h1
    have := (h2.const_mul (2 / m)).mul_const (1 / 3 : ℝ)
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with L hL
  have hdiff : Aprim L s - 1 / 6 = ∫ t in (1 / 6 : ℝ)..s, Qdens L t := by
    have h6 := aprim_sixth hL
    unfold Aprim at h6 ⊢
    have := intervalIntegral.integral_add_adjacent_intervals (qdens_ii L 0 (1 / 6))
      (qdens_ii L (1 / 6) s)
    linarith
  rw [Real.norm_eq_abs, ← Real.norm_eq_abs, hdiff]
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 / 6 : ℝ)) (b := s) (f := Qdens L)
    (C := 2 / m * Real.exp (-(L * c))) (by
      intro t ht
      rw [Set.uIoc, Set.mem_Ioc] at ht
      rw [Real.norm_eq_abs, abs_of_pos (qdens_pos hL t)]
      have hb : m ≤ t ∧ t ≤ 1 / 3 - m := by
        rcases le_total (1 / 6) s with h | h
        · rw [min_eq_left h, max_eq_right h] at ht
          constructor <;> [linarith [ht.1]; linarith [ht.2]]
        · rw [min_eq_right h, max_eq_left h] at ht
          constructor <;> [linarith [ht.1]; linarith [ht.2]]
      exact qdens_small hL hm0 hm6 hb.1 hb.2)
  refine this.trans ?_
  have : |s - 1 / 6| ≤ 1 / 3 := by
    rw [abs_le]; constructor <;> linarith
  nlinarith [Real.exp_pos (-(L * c)), mul_pos (by positivity : (0:ℝ) < 2 / m) (Real.exp_pos (-(L * c)))]


/-- The point `(cos 2πa, sin 2πa)` of the unit circle. -/
noncomputable def circ (a : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.cos (2 * π * a), Real.sin (2 * π * a)]

@[simp] lemma circ_zero (a : ℝ) : circ a 0 = Real.cos (2 * π * a) := by simp [circ]

@[simp] lemma circ_one (a : ℝ) : circ a 1 = Real.sin (2 * π * a) := by simp [circ]

lemma continuous_circ : Continuous circ := by
  unfold circ
  fun_prop

lemma ureal_eq_circ (L ε x : ℝ) : Ureal L ε x = circ (theta L ε x) := rfl

lemma norm_circ_sub_le (α β : ℝ) : ‖circ α - circ β‖ ≤ 2 * π * |α - β| := by
  set u := 2 * π * α
  set v := 2 * π * β
  have h2 : ‖circ α - circ β‖ ^ 2 = 2 - 2 * Real.cos (u - v) := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
    simp only [Fin.sum_univ_two, PiLp.sub_apply, circ_zero, circ_one, Real.norm_eq_abs, sq_abs]
    simp only [u, v]
    rw [Real.cos_sub]
    nlinarith [Real.sin_sq_add_cos_sq (2 * π * α), Real.sin_sq_add_cos_sq (2 * π * β)]
  have h3 : 2 - 2 * Real.cos (u - v) ≤ (u - v) ^ 2 := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := u - v)]
  have e : u - v = 2 * π * (α - β) := by simp only [u, v]; ring
  have h4 : ‖circ α - circ β‖ ^ 2 ≤ (2 * π * |α - β|) ^ 2 := by
    rw [h2, mul_pow, sq_abs]
    calc 2 - 2 * Real.cos (u - v) ≤ (u - v) ^ 2 := h3
      _ = _ := by rw [e]; ring
  exact le_of_sq_le_sq h4 (by positivity)

/-- The limiting law `ν∞ = (δ_{v₁} + δ_{v₂} + δ_{v₃}) / 3` on `ℝ²`. -/
noncomputable def limitLaw : Measure (EuclideanSpace ℝ (Fin 2)) :=
  (3 : ENNReal)⁻¹ • ∑ i : Fin 3, Measure.dirac (vertex i)

instance : IsProbabilityMeasure limitLaw := by
  constructor
  simp only [limitLaw, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  simp only [nsmul_eq_mul, mul_one, Nat.cast_ofNat]
  exact ENNReal.inv_mul_cancel (by norm_num) (by simp)

lemma integral_limitLaw (f : EuclideanSpace ℝ (Fin 2) →ᵇ ℝ) :
    ∫ u, f u ∂limitLaw = 1 / 3 * ∑ i, f (vertex i) := by
  unfold limitLaw
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac]
  · intro i _
    exact integrable_dirac enorm_lt_top

lemma circ_third (j : ℕ) : circ ((j : ℝ) / 3) = vertex ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩ := by
  have h : (j : ℝ) = 3 * ((j / 3 : ℕ) : ℝ) + ((j % 3 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod j 3).symm
  have e : 2 * π * ((j : ℝ) / 3) = 2 * π * (((j % 3 : ℕ) : ℝ) / 3) + ((j / 3 : ℕ) : ℝ) * (2 * π) := by
    rw [h]; ring
  unfold circ vertex
  simp only [e, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]
  congr 2 <;> ring_nf

lemma tendsto_theta {ε : ℝ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (j : ℕ) {x : ℝ}
    (hx : x ∈ Ioo ((j : ℝ) / 6) (((j : ℝ) + 1) / 6)) :
    Tendsto (fun L => theta L (ε L) x) atTop (𝓝 ((j : ℝ) / 3)) := by
  set s := 2 * x - j * (1 / 3) with hs
  have hs' : s ∈ Ioo (0 : ℝ) (1 / 3) := by
    constructor <;> [nlinarith [hx.1]; nlinarith [hx.2]]
  have h1 := aprim_tendsto hs'
  have h2 : Tendsto (fun L => ε L * gT (pt (6 * x))) atTop (𝓝 0) := by
    simpa using hε.mul_const (gT (pt (6 * x)))
  have h3 := ((h1.add_const ((j : ℝ) * (1 / 3))).sub_const (1 / 6)).add h2
  have e : (1 / 6 : ℝ) + j * (1 / 3) - 1 / 6 + 0 = (j : ℝ) / 3 := by ring
  rw [e] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with L hL
  have := aprim_add_nat_third hL s j
  have e2 : s + j * (1 / 3) = 2 * x := by rw [hs]; ring
  rw [e2] at this
  unfold theta
  rw [this]

lemma piece_tendsto (f : EuclideanSpace ℝ (Fin 2) →ᵇ ℝ) {ε : ℝ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (j : ℕ) :
    Tendsto (fun L : ℝ => ∫ x in ((j : ℝ) / 6)..(((j : ℝ) + 1) / 6), f (Ureal L (ε L) x))
      atTop (𝓝 (1 / 6 * f (circ ((j : ℝ) / 3)))) := by
  have hab : (j : ℝ) / 6 ≤ ((j : ℝ) + 1) / 6 := by linarith
  have hD := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := (j : ℝ) / 6) (b := ((j : ℝ) + 1) / 6) (l := atTop)
    (F := fun L x => f (Ureal L (ε L) x)) (f := fun _ => f (circ ((j : ℝ) / 3)))
    (bound := fun _ => ‖f‖) ?_ ?_ ?_ ?_
  · have e : ((j : ℝ) + 1) / 6 - (j : ℝ) / 6 = 1 / 6 := by ring
    simp only [intervalIntegral.integral_const, smul_eq_mul, e] at hD
    exact hD
  · exact Eventually.of_forall fun L =>
      (f.continuous.comp (continuous_Ureal L (ε L))).aestronglyMeasurable
  · exact Eventually.of_forall fun L => Eventually.of_forall fun x _ => by
      simpa using f.norm_coe_le_norm (Ureal L (ε L) x)
  · exact intervalIntegrable_const
  · have hne : ∀ᵐ x : ℝ, x ≠ ((j : ℝ) + 1) / 6 := by
      rw [ae_iff]; simp only [ne_eq, not_not]; exact measure_singleton (μ := (volume : Measure ℝ)) (((j : ℝ) + 1) / 6)
    filter_upwards [hne] with x hx hxI
    rw [Set.uIoc_of_le hab] at hxI
    have hxo : x ∈ Ioo ((j : ℝ) / 6) (((j : ℝ) + 1) / 6) := ⟨hxI.1, lt_of_le_of_ne hxI.2 hx⟩
    have := tendsto_theta hε j hxo
    exact (f.continuous.comp continuous_circ).continuousAt.tendsto.comp this

lemma sum_circ_third (f : EuclideanSpace ℝ (Fin 2) →ᵇ ℝ) :
    ∑ j ∈ Finset.range 6, 1 / 6 * f (circ ((j : ℝ) / 3)) = 1 / 3 * ∑ i, f (vertex i) := by
  simp only [circ_third, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Fin.sum_univ_three]
  have h0 : (⟨0 % 3, by norm_num⟩ : Fin 3) = 0 := rfl
  have h1 : (⟨1 % 3, by norm_num⟩ : Fin 3) = 1 := rfl
  have h2 : (⟨2 % 3, by norm_num⟩ : Fin 3) = 2 := rfl
  simp only [h0, h1, h2]
  ring

lemma integral_feature_tendsto (f : EuclideanSpace ℝ (Fin 2) →ᵇ ℝ) {ε : ℝ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun L : ℝ => ∫ y, f (Ufeat L (ε L) y) ∂haar 1) atTop
      (𝓝 (1 / 3 * ∑ i, f (vertex i))) := by
  have hsum : Tendsto (fun L : ℝ => ∑ j ∈ Finset.range 6,
      ∫ x in ((j : ℝ) / 6)..(((j : ℝ) + 1) / 6), f (Ureal L (ε L) x)) atTop
      (𝓝 (∑ j ∈ Finset.range 6, 1 / 6 * f (circ ((j : ℝ) / 3)))) :=
    tendsto_finsetSum _ fun j _ => piece_tendsto f hε j
  rw [sum_circ_third] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with L hL
  have hm : Measurable fun x : ℝ => f (Ureal L (ε L) x) :=
    (f.continuous.comp (continuous_Ureal L (ε L))).measurable
  have hper : Function.Periodic (fun x : ℝ => f (Ureal L (ε L) x)) 1 := fun x => by
    simp only [Ureal_periodic hL (ε L) x]
  have h1 : ∫ y, f (Ufeat L (ε L) y) ∂haar 1 = ∫ t in (0 : ℝ)..1, f (Ureal L (ε L) t) :=
    integral_haar_secT hm hper
  rw [h1]
  have := intervalIntegral.sum_integral_adjacent_intervals (a := fun j : ℕ => (j : ℝ) / 6)
    (μ := volume) (f := fun x => f (Ureal L (ε L) x)) (n := 6) (fun k _ =>
      (f.continuous.comp (continuous_Ureal L (ε L))).intervalIntegrable _ _)
  simp only [Nat.cast_zero, zero_div] at this
  have e : ((6 : ℕ) : ℝ) / 6 = 1 := by norm_num
  rw [e] at this
  rw [← this]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  rfl

lemma tendsto_pushforward (f : EuclideanSpace ℝ (Fin 2) →ᵇ ℝ) {ε : ℝ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun L : ℝ => ∫ u, f u ∂(Measure.map (Ufeat L (ε L)) (haar 1))) atTop
      (𝓝 (∫ u, f u ∂limitLaw)) := by
  rw [integral_limitLaw]
  refine (integral_feature_tendsto f hε).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with L hL
  rw [integral_map (continuous_Ufeat hL (ε L)).measurable.aemeasurable
    f.continuous.aestronglyMeasurable]

/-- **RUF020, pushforward convergence to three states.** Let `g` be the rough phase profile
(`gT`), `U_{L,ε}` the unit feature (`Ufeat`), `m` the Haar probability measure on the circle and
`ν∞ = (δ_{v₁} + δ_{v₂} + δ_{v₃}) / 3` (`limitLaw`).  Then `ν∞` is a probability measure with
`∫ f dν∞ = (1/3) ∑ᵢ f(vᵢ)`; `‖U_{L,ε} - U_{L,0}‖∞ ≤ 2π |ε| ‖g‖∞` for all `L, ε`; and as `L → ∞`
the pushforward `(U_{L,ε_L})_# m` converges weakly (against every bounded continuous test function
on `ℝ²`) to `ν∞`, for `ε_L = 0`, for `ε_L = 1/L`, and for every `ε_L → 0`. -/
theorem pushforward_convergence_to_three_states :
    IsProbabilityMeasure limitLaw ∧
    (∀ f : EuclideanSpace ℝ (Fin 2) →ᵇ ℝ, ∫ u, f u ∂limitLaw = 1 / 3 * ∑ i, f (vertex i)) ∧
    (∀ (L ε : ℝ) (y : Torus 1),
      ‖Ufeat L ε y - Ufeat L 0 y‖ ≤ 2 * π * |ε| * ⨆ z : Torus 1, |gT z|) ∧
    (∀ f : EuclideanSpace ℝ (Fin 2) →ᵇ ℝ,
      Tendsto (fun L : ℝ => ∫ u, f u ∂(Measure.map (Ufeat L 0) (haar 1))) atTop
        (𝓝 (∫ u, f u ∂limitLaw))) ∧
    (∀ ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) → ∀ f : EuclideanSpace ℝ (Fin 2) →ᵇ ℝ,
      Tendsto (fun L : ℝ => ∫ u, f u ∂(Measure.map (Ufeat L (ε L)) (haar 1))) atTop
        (𝓝 (∫ u, f u ∂limitLaw))) ∧
    (∀ f : EuclideanSpace ℝ (Fin 2) →ᵇ ℝ,
      Tendsto (fun L : ℝ => ∫ u, f u ∂(Measure.map (Ufeat L (1 / L)) (haar 1))) atTop
        (𝓝 (∫ u, f u ∂limitLaw))) := by
  refine ⟨inferInstance, integral_limitLaw, ?_, fun f => tendsto_pushforward f (ε := fun _ => 0) tendsto_const_nhds,
    fun ε hε f => tendsto_pushforward f hε, fun f => tendsto_pushforward f (ε := fun L => 1 / L) ?_⟩
  · intro L ε y
    have hb : BddAbove (Set.range fun z : Torus 1 => |gT z|) :=
      ⟨hMean, by rintro _ ⟨z, rfl⟩; exact Spikes.abs_gT_le z⟩
    have h1 : Ufeat L ε y - Ufeat L 0 y = circ (theta L ε (SharpLSI.secT y 0)) -
        circ (theta L 0 (SharpLSI.secT y 0)) := rfl
    have h2 : theta L ε (SharpLSI.secT y 0) - theta L 0 (SharpLSI.secT y 0) =
        ε * gT (pt (6 * SharpLSI.secT y 0)) := by unfold theta; ring
    rw [h1]
    refine (norm_circ_sub_le _ _).trans ?_
    rw [h2, abs_mul]
    have hg := le_ciSup hb (pt (6 * SharpLSI.secT y 0))
    have := mul_le_mul_of_nonneg_left hg (abs_nonneg ε)
    have hpi : (0 : ℝ) ≤ 2 * π := by positivity
    calc 2 * π * (|ε| * |gT (pt (6 * SharpLSI.secT y 0))|)
        ≤ 2 * π * (|ε| * ⨆ z : Torus 1, |gT z|) := mul_le_mul_of_nonneg_left this hpi
      _ = _ := by ring
  · simp only [one_div]
    exact tendsto_inv_atTop_zero

end DGPS.Examples.RoughBoundary.Landscape
