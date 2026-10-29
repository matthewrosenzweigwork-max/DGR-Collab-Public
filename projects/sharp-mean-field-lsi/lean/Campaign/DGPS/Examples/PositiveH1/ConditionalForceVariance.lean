import Mathlib
import DGPS.Examples.PositiveH1.FiniteFamilyRecovery
import DGPS.Examples.PositiveH1.Dissipation

/-!
# H1018: finite family conditional force variance

For the fixed finite species family, conditioning on the label `X_i = x` under the product law
removes the self-label contribution `(κ/N) R′ * ρ_s` from the conditional mean of the force, and the
conditional variance of the remaining labels is bounded by `B ‖R′‖₂² / N`.  Summing over labels:
`4 E_N(f_N) / N = ∑_s p_s ∫ ρ_s |s_s + κ R′ * ρ̄_N - (κ/N) R′ * ρ_s|² dm + e_N` with
`0 ≤ e_N ≤ κ² B ‖R′‖₂² / N`, and hence `4 E_N(f_N) / N → D_θ` (the species dissipation).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace DGPS.Examples.PositiveH1.Recovery
open DGPS DGPS.Particle DGPS.Examples.PositiveH1.Particle DGPS.Examples.PositiveH1.Fourier
  DGPS.Examples.PositiveH1.Nonlinear DGPS.Examples.PositiveH1.Model

theorem cfv_integrable_densityMeasure_iff (ρ : AbsoluteDensity 1) (f : Torus 1 → ℝ) :
    Integrable f (densityMeasure ρ : Measure (Torus 1)) ↔
      Integrable (fun x => ρ.density x * f x) (haar 1) := by
  rw [densityMeasure_coe]
  change Integrable f ((haar 1).withDensity fun x => ENNReal.ofReal (ρ.density x)) ↔ _
  rw [integrable_withDensity_iff_integrable_smul₀'
    (aemeasurable_density ρ).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (ρ.density_nonneg x)]

theorem cfv_exists_bound (ρ : AbsoluteDensity 1) : ∃ B : ℝ, ∀ᵐ y ∂haar 1, ρ.density y ≤ B := by
  obtain ⟨⟨U, -, ⟨M, hM⟩, hUae, -⟩, -, -⟩ := density_regular ρ
  refine ⟨M ^ 2, ?_⟩
  filter_upwards [hUae] with y hy
  have : ρ.density y = U y ^ 2 := by rw [AbsoluteDensity.density, ← hy]
  rw [this]
  exact sq_le_sq' (abs_le.1 (hM y)).1 (abs_le.1 (hM y)).2

theorem cfv_memLp_dR_sub (ρ : AbsoluteDensity 1) {B : ℝ} (hB : ∀ᵐ y ∂haar 1, ρ.density y ≤ B)
    (t : Torus 1) : MemLp (fun y => dR (t - y)) 2 (densityMeasure ρ : Measure (Torus 1)) := by
  have hm : AEStronglyMeasurable (fun y => dR (t - y)) (densityMeasure ρ : Measure (Torus 1)) := by
    rw [densityMeasure_coe]
    exact ((memLp_sub_left memLp_dR t).aestronglyMeasurable).mono_ac
      (withDensity_absolutelyContinuous _ _)
  rw [memLp_two_iff_integrable_sq hm, cfv_integrable_densityMeasure_iff]
  have h2 : Integrable (fun y => dR (t - y) ^ 2) (haar 1) := (memLp_sub_left memLp_dR t).integrable_sq
  refine (h2.const_mul B).mono' ?_ ?_
  · exact (aemeasurable_density ρ).aestronglyMeasurable.mul h2.aestronglyMeasurable
  · filter_upwards [hB] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ρ.density_nonneg y) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right hy (sq_nonneg _)


theorem cfv_fixed {n : ℕ} (μ : Fin n → Measure (Torus 1)) [∀ k, IsProbabilityMeasure (μ k)]
    (i : Fin n) (G : Torus 1 → ℝ) (hG : ∀ j, MemLp G 2 (μ j)) (a c : ℝ) :
    ∫ x, (a + c * ∑ j ∈ Finset.univ.erase i, G (x j)) ^ 2 ∂Measure.pi μ =
      (a + c * ∑ j ∈ Finset.univ.erase i, ∫ y, G y ∂μ j) ^ 2
        + c ^ 2 * ∑ j ∈ Finset.univ.erase i, Var[G; μ j] := by
  set X : Fin n → Torus 1 → ℝ := fun j y => if j = i then 0 else G y with hXdef
  have hX : ∀ j, MemLp (X j) 2 (μ j) := by
    intro j
    by_cases h : j = i
    · simp only [hXdef, h, ite_true]; exact MemLp.zero
    · simp only [hXdef, h, ite_false]; exact hG j
  have hS : ∀ x : Fin n → Torus 1, ∑ j ∈ Finset.univ.erase i, G (x j) = ∑ j, X j (x j) := by
    intro x
    rw [← Finset.sum_erase Finset.univ (f := fun j => X j (x j)) (a := i) (by simp [hXdef])]
    exact Finset.sum_congr rfl fun j hj => by
      simp [hXdef, (Finset.mem_erase.1 hj).1]
  set S : (Fin n → Torus 1) → ℝ := ∑ j, fun ω => X j (ω j) with hSdef
  have hSapp : ∀ x, S x = ∑ j, X j (x j) := fun x => by simp [hSdef]
  have hmem : ∀ j, MemLp (fun ω : Fin n → Torus 1 => X j (ω j)) 2 (Measure.pi μ) := fun j =>
    (hX j).comp_measurePreserving (measurePreserving_eval μ j)
  have hSmem : MemLp S 2 (Measure.pi μ) := by
    rw [hSdef]; exact memLp_finsetSum' _ fun j _ => hmem j
  have hES : ∫ x, S x ∂Measure.pi μ = ∑ j ∈ Finset.univ.erase i, ∫ y, G y ∂μ j := by
    simp_rw [hSapp]
    rw [integral_finsetSum _ fun j _ => (hmem j).integrable one_le_two]
    rw [← Finset.sum_erase Finset.univ (f := fun j => ∫ x, X j (x j) ∂Measure.pi μ) (a := i)
      (by simp [hXdef])]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := (Finset.mem_erase.1 hj).1
    have := (measurePreserving_eval μ j).map_eq
    have h2 : ∫ x, X j (x j) ∂Measure.pi μ = ∫ y, X j y ∂μ j := by
      rw [← integral_map (measurable_pi_apply j).aemeasurable (by rw [this]; exact (hX j).aestronglyMeasurable), this]
    rw [h2]
    simp [hXdef, hj']
  have hVS : Var[S; Measure.pi μ] = ∑ j ∈ Finset.univ.erase i, Var[G; μ j] := by
    rw [hSdef, variance_sum_pi hX]
    rw [← Finset.sum_erase Finset.univ (f := fun j => Var[X j; μ j]) (a := i)
      (by simp [hXdef]; exact variance_zero _)]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp [hXdef, (Finset.mem_erase.1 hj).1]
  have hY : MemLp (fun x => a + c * S x) 2 (Measure.pi μ) :=
    (memLp_const a).add (hSmem.const_mul c)
  have hvar := variance_eq_sub hY
  have hVY : Var[fun x => a + c * S x; Measure.pi μ] = c ^ 2 * Var[S; Measure.pi μ] := by
    rw [show (fun x => a + c * S x) = fun x => c * S x + a from funext fun x => add_comm _ _,
      variance_add_const (hSmem.const_mul c).aestronglyMeasurable, variance_const_mul]
  have hEY : ∫ x, (a + c * S x) ∂Measure.pi μ = a + c * ∫ x, S x ∂Measure.pi μ := by
    rw [integral_add (integrable_const _) (hSmem.integrable one_le_two |>.const_mul c),
      integral_const_mul]; simp
  simp only [Pi.pow_apply] at hvar
  have hvar' : ∫ x, (a + c * S x) ^ 2 ∂Measure.pi μ =
      Var[fun x => a + c * S x; Measure.pi μ] + (∫ x, (a + c * S x) ∂Measure.pi μ) ^ 2 := by
    have : (Measure.pi μ)[fun x => a + c * S x] = ∫ x, (a + c * S x) ∂Measure.pi μ := rfl
    rw [hvar, this]; ring
  simp_rw [hS]
  have e : ∀ x, ∑ j, X j (x j) = S x := fun x => (hSapp x).symm
  simp_rw [e]
  rw [hvar', hVY, hEY, hES, hVS]; ring

theorem cfv_measurable_upd {n : ℕ} (i : Fin n) :
    Measurable fun p : Torus 1 × (Fin n → Torus 1) => Function.update p.2 i p.1 :=
  measurable_update'.comp (measurable_snd.prodMk measurable_fst)

theorem cfv_map_update {n : ℕ} (μ : Fin n → Measure (Torus 1)) [∀ k, IsProbabilityMeasure (μ k)]
    (i : Fin n) :
    ((μ i).prod (Measure.pi μ)).map
      (fun p : Torus 1 × (Fin n → Torus 1) => Function.update p.2 i p.1) = Measure.pi μ := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (cfv_measurable_upd i) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : Torus 1 × (Fin n → Torus 1) => Function.update p.2 i p.1) ⁻¹'
      (Set.pi Set.univ s) = s i ×ˢ Set.pi Set.univ (Function.update s i Set.univ) := by
    ext ⟨t, x⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨by simpa using h i, fun k => ?_⟩
      by_cases hk : k = i
      · subst hk; simp
      · simpa [Function.update_of_ne hk] using h k
    · rintro ⟨h1, h2⟩ k
      by_cases hk : k = i
      · subst hk; simpa using h1
      · simpa [hk] using h2 k
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have : ∀ k, μ k (Function.update s i Set.univ k) =
      Function.update (fun k => μ k (s k)) i 1 k := by
    intro k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  simp_rw [this]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i), one_mul,
    Finset.prod_eq_prod_sdiff_singleton_mul (Finset.mem_univ i), mul_comm]

theorem cfv_B_nonneg (ρ : AbsoluteDensity 1) {B : ℝ} (hB : ∀ᵐ y ∂haar 1, ρ.density y ≤ B) :
    0 ≤ B := by
  obtain ⟨y, hy⟩ := hB.exists
  exact (ρ.density_nonneg y).trans hy

/-- `ρ (s_ρ + W)² = (2 g + √ρ W)²` a.e., hence integrable for continuous `W`. -/
theorem cfv_main_ae (ρ : AbsoluteDensity 1) (W : Torus 1 → ℝ) :
    (fun y => ρ.density y * (score ρ y + W y) ^ 2) =ᵐ[haar 1]
      fun y => (2 * weakGradient ρ.sqrt ρ.sqrt_mem y 0 + ρ.sqrt y * W y) ^ 2 := by
  filter_upwards [weakGradient_zero_on_zero_set ρ.sqrt_mem] with y hy
  by_cases h : ρ.sqrt y = 0
  · rw [hy h]
    simp [AbsoluteDensity.density, score, h]
  · simp only [AbsoluteDensity.density, score]
    field_simp

theorem cfv_main_integrable (ρ : AbsoluteDensity 1) {W : Torus 1 → ℝ} (hW : Continuous W) :
    Integrable (fun y => ρ.density y * (score ρ y + W y) ^ 2) (haar 1) := by
  have hg : MemLp (fun y => weakGradient ρ.sqrt ρ.sqrt_mem y 0) 2 (haar 1) :=
    memLp_coord_of_memLp (isWeakGradient_weakGradient ρ.sqrt_mem).memLp_grad 0
  have hw : MemLp (fun y => ρ.sqrt y * W y) 2 (haar 1) := by
    have h : MemLp (ρ.sqrt * W) 2 (haar 1) := ρ.memLp_sqrt.smul (memLp_of_cont hW ⊤)
    exact h
  have := ((hg.const_mul 2).add hw).integrable_sq
  exact this.congr (cfv_main_ae ρ W).symm

theorem cfv_integrable_F (κ : ℝ) (N : ℕ+) (r : Fin N → AbsoluteDensity 1) (i : Fin N) :
    Integrable (fun x : ParticleSpace 1 N => (score (r i) (x i) + κ / (N : ℝ) *
      ∑ j ∈ Finset.univ.erase i, dR (x i - x j)) ^ 2) (labeledProduct r) := by
  rw [integrable_labeled_iff]
  have h := (integrable_p_mul_grad_sq κ r i).const_mul 4
  refine h.congr ?_
  filter_upwards [pointwise_energy κ r i] with x hx
  rw [hx, roughForce_apply]

theorem cfv_mean (ρ : AbsoluteDensity 1) (t : Torus 1) :
    ∫ y, dR (t - y) ∂(densityMeasure ρ : Measure (Torus 1)) = conv dR ρ.density t := by
  rw [integral_densityMeasure, conv_comm]
  rfl

theorem cfv_integrable_rho_mul (ρ : AbsoluteDensity 1) {B : ℝ}
    (hB : ∀ᵐ y ∂haar 1, ρ.density y ≤ B) (t : Torus 1) :
    Integrable (fun y => ρ.density y * dR (t - y) ^ 2) (haar 1) := by
  have h2 : Integrable (fun y => dR (t - y) ^ 2) (haar 1) :=
    (memLp_sub_left memLp_dR t).integrable_sq
  refine (h2.const_mul B).mono' ?_ ?_
  · exact (aemeasurable_density ρ).aestronglyMeasurable.mul h2.aestronglyMeasurable
  · filter_upwards [hB] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ρ.density_nonneg y) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right hy (sq_nonneg _)

theorem cfv_var_bounds (ρ : AbsoluteDensity 1) {B : ℝ} (hB : ∀ᵐ y ∂haar 1, ρ.density y ≤ B)
    (t : Torus 1) :
    0 ≤ Var[fun y => dR (t - y); (densityMeasure ρ : Measure (Torus 1))] ∧
    Var[fun y => dR (t - y); (densityMeasure ρ : Measure (Torus 1))] ≤
      B * ∫ y, dR y ^ 2 ∂haar 1 := by
  refine ⟨variance_nonneg _ _, ?_⟩
  refine (variance_le_expectation_sq (cfv_memLp_dR_sub ρ hB t).aestronglyMeasurable).trans ?_
  have e : ((densityMeasure ρ : Measure (Torus 1))[(fun y => dR (t - y)) ^ 2]) =
      ∫ y, dR (t - y) ^ 2 ∂(densityMeasure ρ : Measure (Torus 1)) := by
    simp only [Pi.pow_apply]
  rw [e, integral_densityMeasure, ← integral_sq_sub_left dR t, ← integral_const_mul]
  have h2 : Integrable (fun y => dR (t - y) ^ 2) (haar 1) :=
    (memLp_sub_left memLp_dR t).integrable_sq
  refine integral_mono_ae (cfv_integrable_rho_mul ρ hB t) (h2.const_mul B) ?_
  filter_upwards [hB] with y hy
  exact mul_le_mul_of_nonneg_right hy (sq_nonneg _)

theorem cfv_label (κ : ℝ) (N : ℕ+) (r : Fin N → AbsoluteDensity 1) {B : ℝ}
    (hB : ∀ j, ∀ᵐ y ∂haar 1, (r j).density y ≤ B) (i : Fin N) :
    ∫ y, (r i).density y * (score (r i) y + κ / (N : ℝ) *
        ∑ j ∈ Finset.univ.erase i, conv dR (r j).density y) ^ 2 ∂haar 1 ≤
      ∫ x, (score (r i) (x i) + κ / (N : ℝ) *
        ∑ j ∈ Finset.univ.erase i, dR (x i - x j)) ^ 2 ∂labeledProduct r ∧
    ∫ x, (score (r i) (x i) + κ / (N : ℝ) *
        ∑ j ∈ Finset.univ.erase i, dR (x i - x j)) ^ 2 ∂labeledProduct r ≤
      ∫ y, (r i).density y * (score (r i) y + κ / (N : ℝ) *
        ∑ j ∈ Finset.univ.erase i, conv dR (r j).density y) ^ 2 ∂haar 1 +
      (κ / (N : ℝ)) ^ 2 * ((N : ℝ) * (B * ∫ y, dR y ^ 2 ∂haar 1)) := by
  set c : ℝ := κ / (N : ℝ) with hc
  set μ : Fin N → Measure (Torus 1) := fun j => (densityMeasure (r j) : Measure (Torus 1)) with hμ
  have hν : labeledProduct r = Measure.pi μ := rfl
  set F : (Fin N → Torus 1) → ℝ := fun x => (score (r i) (x i) + c *
        ∑ j ∈ Finset.univ.erase i, dR (x i - x j)) ^ 2 with hF
  have hFint : Integrable F (Measure.pi μ) := by
    rw [← hν]; exact cfv_integrable_F κ N r i
  have hmap := cfv_map_update μ i
  have hFmap : Integrable F (((μ i).prod (Measure.pi μ)).map
      (fun p : Torus 1 × (Fin N → Torus 1) => Function.update p.2 i p.1)) := by
    rw [hmap]; exact hFint
  have hint2 : Integrable (fun p : Torus 1 × (Fin N → Torus 1) => F (Function.update p.2 i p.1))
      ((μ i).prod (Measure.pi μ)) :=
    (integrable_map_measure hFmap.aestronglyMeasurable (cfv_measurable_upd i).aemeasurable).1 hFmap
  have hLHS : ∫ x, F x ∂Measure.pi μ =
      ∫ t, ∫ x, F (Function.update x i t) ∂Measure.pi μ ∂μ i := by
    conv_lhs => rw [← hmap]
    rw [integral_map (cfv_measurable_upd i).aemeasurable (by rw [hmap]; exact hFint.1),
      integral_prod _ hint2]
  set a : Torus 1 → ℝ := score (r i) with ha
  set W : Torus 1 → ℝ := fun t => c * ∑ j ∈ Finset.univ.erase i, conv dR (r j).density t with hW
  have hWc : Continuous W :=
    continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_driftField (r j))
  set A : Torus 1 → ℝ := fun t => (a t + W t) ^ 2 with hA
  set V : Torus 1 → ℝ := fun t => c ^ 2 * ∑ j ∈ Finset.univ.erase i,
      Var[fun y => dR (t - y); μ j] with hV
  have hT : ∀ t, ∫ x, F (Function.update x i t) ∂Measure.pi μ = A t + V t := by
    intro t
    have h1 : ∀ x : Fin N → Torus 1, F (Function.update x i t) =
        (a t + c * ∑ j ∈ Finset.univ.erase i, dR (t - x j)) ^ 2 := by
      intro x
      simp only [hF, ha, Function.update_self]
      congr 3
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.mem_erase.1 hj).1]
    simp_rw [h1]
    rw [cfv_fixed μ i (fun y => dR (t - y)) (fun j => cfv_memLp_dR_sub (r j) (hB j) t) (a t) c]
    simp only [hA, hW, hV, hμ, cfv_mean]
  have hAint : Integrable A (μ i) := by
    have := cfv_main_integrable (r i) hWc
    rw [← cfv_integrable_densityMeasure_iff] at this
    exact this
  have hTint : Integrable (fun t => ∫ x, F (Function.update x i t) ∂Measure.pi μ) (μ i) :=
    hint2.integral_prod_left
  have hVint : Integrable V (μ i) := by
    have := hTint.sub hAint
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply, hT]; ring
  have hI0 : 0 ≤ ∫ y, dR y ^ 2 ∂haar 1 := integral_nonneg fun y => sq_nonneg _
  have hB0 : 0 ≤ B := cfv_B_nonneg (r i) (hB i)
  have hVnn : ∀ t, 0 ≤ V t := fun t =>
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => (cfv_var_bounds (r j) (hB j) t).1)
  have hVle : ∀ t, V t ≤ c ^ 2 * ((N : ℝ) * (B * ∫ y, dR y ^ 2 ∂haar 1)) := by
    intro t
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    calc ∑ j ∈ Finset.univ.erase i, Var[fun y => dR (t - y); μ j]
        ≤ ∑ j ∈ Finset.univ.erase i, (B * ∫ y, dR y ^ 2 ∂haar 1) :=
          Finset.sum_le_sum fun j _ => (cfv_var_bounds (r j) (hB j) t).2
      _ = ((Finset.univ.erase i).card : ℝ) * (B * ∫ y, dR y ^ 2 ∂haar 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (B * ∫ y, dR y ^ 2 ∂haar 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hB0 hI0)
          rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
          simp
  have hMA : ∫ t, A t ∂μ i = ∫ y, (r i).density y * (score (r i) y + c *
      ∑ j ∈ Finset.univ.erase i, conv dR (r j).density y) ^ 2 ∂haar 1 :=
    integral_densityMeasure (r i) A
  have hsplit : ∫ x, F x ∂Measure.pi μ = ∫ t, A t ∂μ i + ∫ t, V t ∂μ i := by
    rw [hLHS]
    simp_rw [hT]
    exact integral_add hAint hVint
  show _ ≤ ∫ x, F x ∂Measure.pi μ ∧ ∫ x, F x ∂Measure.pi μ ≤ _
  rw [hsplit, ← hMA]
  have hVI : ∫ t, V t ∂μ i ≤ c ^ 2 * ((N : ℝ) * (B * ∫ y, dR y ^ 2 ∂haar 1)) := by
    calc ∫ t, V t ∂μ i ≤ ∫ t, c ^ 2 * ((N : ℝ) * (B * ∫ y, dR y ^ 2 ∂haar 1)) ∂μ i :=
          integral_mono hVint (integrable_const _) hVle
      _ = _ := by simp
  have hV0 : 0 ≤ ∫ t, V t ∂μ i := integral_nonneg hVnn
  exact ⟨by linarith, by linarith⟩

theorem cfv_conv_sum {n : ℕ} (w : Fin n → ℝ) (ρ : Fin n → AbsoluteDensity 1) (y : Torus 1) :
    conv dR (fun z => ∑ t, w t * (ρ t).density z) y = ∑ t, w t * conv dR (ρ t).density y := by
  unfold conv
  have hi : ∀ t ∈ Finset.univ, Integrable (fun z => dR z * (w t * (ρ t).density (y - z)))
      (haar 1) := by
    intro t _
    have := (memLp_dR.integrable_mul (memLp_sub_left (memLp_density_two (ρ t)) y)).const_mul (w t)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.mul_apply]; ring
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ hi]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only; ring

theorem cfv_frac_nonneg {n : ℕ} {N : ℕ+} (σ : Fin N → Fin n) (s : Fin n) : 0 ≤ frac σ s :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem cfv_cnt_eq {n : ℕ} {N : ℕ+} (σ : Fin N → Fin n) (s : Fin n) :
    cnt σ s = (N : ℝ) * frac σ s := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  unfold frac
  field_simp

theorem cfv_frac_le_one {n : ℕ} {N : ℕ+} (σ : Fin N → Fin n) (s : Fin n) : frac σ s ≤ 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  unfold frac cnt
  rw [div_le_one hN]
  exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)

/-- The pointwise identity for the conditional force. -/
theorem cfv_pt (κ : ℝ) (N : ℕ+) (F : SpeciesFamily 1) (σ : Fin N → Fin F.count) (i : Fin N)
    (y : Torus 1) :
    κ / (N : ℝ) * ∑ j ∈ Finset.univ.erase i, conv dR (F.density (σ j)).density y =
      κ * conv dR (fun z => ∑ t, frac σ t * (F.density t).density z) y
        - κ / (N : ℝ) * conv dR (F.density (σ i)).density y := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  rw [cfv_conv_sum, Finset.sum_erase_eq_sub (Finset.mem_univ i),
    sum_fiber σ (fun s => conv dR (F.density s).density y)]
  simp_rw [cfv_cnt_eq σ]
  have : ∑ s, (N : ℝ) * frac σ s * conv dR (F.density s).density y =
      (N : ℝ) * ∑ s, frac σ s * conv dR (F.density s).density y := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [this]
  field_simp

theorem cfv_finite (κ : ℝ) (F : SpeciesFamily 1) (N : ℕ+) (σ : Fin N → Fin F.count) {B : ℝ}
    (hB : ∀ s, ∀ᵐ y ∂haar 1, (F.density s).density y ≤ B) :
    ∃ e : ℝ,
      4 * particleEnergy (kernelData κ) N
          ⟨root κ fun i => F.density (σ i),
            (finite_species_rough_product_admissibility κ N σ F.density).1⟩ / N =
        ∑ s, frac σ s * ∫ y, (F.density s).density y * (score (F.density s) y
          + κ * conv dR (fun z => ∑ t, frac σ t * (F.density t).density z) y
          - κ / (N : ℝ) * conv dR (F.density s).density y) ^ 2 ∂haar 1 + e ∧
      0 ≤ e ∧ e ≤ κ ^ 2 * B * (∫ y, dR y ^ 2 ∂haar 1) / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hadm := finite_species_rough_product_admissibility κ N σ F.density
  have hE := hadm.2.2.2.2.2.2 hadm.1
  set φ : Fin F.count → ℝ := fun s => ∫ y, (F.density s).density y * (score (F.density s) y
          + κ * conv dR (fun z => ∑ t, frac σ t * (F.density t).density z) y
          - κ / (N : ℝ) * conv dR (F.density s).density y) ^ 2 ∂haar 1 with hφ
  set L : Fin N → ℝ := fun i => ∫ x, (score (F.density (σ i)) (x i) + κ / (N : ℝ) *
        ∑ j ∈ Finset.univ.erase i, dR (x i - x j)) ^ 2 ∂labeledProduct fun i => F.density (σ i)
    with hL
  set K : ℝ := (κ / (N : ℝ)) ^ 2 * ((N : ℝ) * (B * ∫ y, dR y ^ 2 ∂haar 1)) with hK
  have hlab : ∀ i, φ (σ i) ≤ L i ∧ L i ≤ φ (σ i) + K := by
    intro i
    have h := cfv_label κ N (fun i => F.density (σ i)) (fun j => hB (σ j)) i
    have hM : ∫ y, (F.density (σ i)).density y * (score (F.density (σ i)) y + κ / (N : ℝ) *
        ∑ j ∈ Finset.univ.erase i, conv dR (F.density (σ j)).density y) ^ 2 ∂haar 1 = φ (σ i) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show _ = (F.density (σ i)).density y * (score (F.density (σ i)) y
          + κ * conv dR (fun z => ∑ t, frac σ t * (F.density t).density z) y
          - κ / (N : ℝ) * conv dR (F.density (σ i)).density y) ^ 2
      beta_reduce
      rw [cfv_pt, add_sub_assoc]
    rw [hM] at h
    exact h
  have hsum : ∑ i, φ (σ i) = (N : ℝ) * ∑ s, frac σ s * φ s := by
    rw [sum_fiber σ φ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [cfv_cnt_eq σ]; ring
  have hlow : ∑ i, φ (σ i) ≤ ∑ i, L i := Finset.sum_le_sum fun i _ => (hlab i).1
  have hup : ∑ i, L i ≤ ∑ i, (φ (σ i) + K) := Finset.sum_le_sum fun i _ => (hlab i).2
  have hup' : ∑ i, (φ (σ i) + K) = (N : ℝ) * ∑ s, frac σ s * φ s + (N : ℝ) * K := by
    rw [Finset.sum_add_distrib, hsum]; simp
  have hKe : K = κ ^ 2 * B * (∫ y, dR y ^ 2 ∂haar 1) / N := by
    rw [hK]; field_simp
  refine ⟨(∑ i, L i) / N - ∑ s, frac σ s * φ s, ?_, ?_, ?_⟩
  · rw [hE]; ring
  · rw [sub_nonneg, le_div_iff₀ hN]
    nlinarith
  · rw [← hKe, sub_le_iff_le_add, div_le_iff₀ hN]
    nlinarith

theorem cfv_phi_tendsto (κ : ℝ) (F : SpeciesFamily 1)
    (σ : ∀ N : ℕ+, Fin N → Fin F.count)
    (hσ : ∀ s, Tendsto (fun N : ℕ+ => frac (σ N) s) atTop (𝓝 (F.weight s))) (s : Fin F.count) :
    Tendsto (fun N : ℕ+ => ∫ y, (F.density s).density y * (score (F.density s) y
        + κ * conv dR (fun z => ∑ t, frac (σ N) t * (F.density t).density z) y
        - κ / (N : ℝ) * conv dR (F.density s).density y) ^ 2 ∂haar 1) atTop
      (𝓝 (∫ y, (F.density s).density y * (score (F.density s) y
        + κ * ∑ t, F.weight t * conv dR (F.density t).density y) ^ 2 ∂haar 1)) := by
  set c : Fin F.count → Torus 1 → ℝ := fun t => conv dR (F.density t).density with hc
  have hcc : ∀ t, Continuous (c t) := fun t => continuous_driftField (F.density t)
  set W : ℕ+ → Torus 1 → ℝ := fun N y => κ * ∑ t, frac (σ N) t * c t y
      - κ / (N : ℝ) * c s y with hW
  have hWc : ∀ N, Continuous (W N) := fun N => by
    simp only [hW]
    exact (continuous_const.mul (continuous_finsetSum _ fun t _ => continuous_const.mul (hcc t))).sub
      (continuous_const.mul (hcc s))
  set M : ℝ := ∑ t, Real.sqrt (∫ y, dR y ^ 2 ∂haar 1) *
      Real.sqrt (∫ y, (F.density t).density y ^ 2 ∂haar 1) with hM
  have hcb : ∀ t y, |c t y| ≤ M := by
    intro t y
    refine (conv_bound memLp_dR (memLp_density_two (F.density t)) y).trans ?_
    exact Finset.single_le_sum (f := fun t => Real.sqrt (∫ y, dR y ^ 2 ∂haar 1) *
      Real.sqrt (∫ y, (F.density t).density y ^ 2 ∂haar 1))
      (fun t _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Finset.mem_univ t)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hcb s 0)
  have hWb : ∀ N y, |W N y| ≤ 2 * (|κ| * M) := by
    intro N y
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
    have h1 : |∑ t, frac (σ N) t * c t y| ≤ M := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ t, |frac (σ N) t * c t y| ≤ ∑ t, |c t y| := by
            refine Finset.sum_le_sum fun t _ => ?_
            rw [abs_mul, abs_of_nonneg (cfv_frac_nonneg _ _)]
            exact mul_le_of_le_one_left (abs_nonneg _) (cfv_frac_le_one _ _)
        _ ≤ ∑ t, Real.sqrt (∫ y, dR y ^ 2 ∂haar 1) *
            Real.sqrt (∫ y, (F.density t).density y ^ 2 ∂haar 1) := by
            refine Finset.sum_le_sum fun t _ => ?_
            exact conv_bound memLp_dR (memLp_density_two (F.density t)) y
    have h2 : |κ / (N : ℝ) * c s y| ≤ |κ| * M := by
      rw [abs_mul, abs_div, abs_of_pos (by linarith : (0 : ℝ) < N)]
      have : |κ| / N ≤ |κ| := div_le_self (abs_nonneg _) hN
      exact mul_le_mul this (hcb s y) (abs_nonneg _) (abs_nonneg _)
    have h3 : |κ * ∑ t, frac (σ N) t * c t y| ≤ |κ| * M := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    calc |W N y| ≤ |κ * ∑ t, frac (σ N) t * c t y| + |κ / (N : ℝ) * c s y| := abs_sub _ _
      _ ≤ 2 * (|κ| * M) := by linarith
  have hrho : Integrable (F.density s).density (haar 1) := (F.density s).integrable_density
  have hsc : Integrable (fun y => (F.density s).density y * (score (F.density s) y) ^ 2)
      (haar 1) := by
    simpa using cfv_main_integrable (F.density s) (W := fun _ => 0) continuous_const
  have hbd : Integrable (fun y => 2 * ((F.density s).density y * (score (F.density s) y) ^ 2)
      + 2 * (2 * (|κ| * M)) ^ 2 * (F.density s).density y) (haar 1) :=
    (hsc.const_mul 2).add (hrho.const_mul _)
  have hrew : ∀ N y, (F.density s).density y * (score (F.density s) y
        + κ * conv dR (fun z => ∑ t, frac (σ N) t * (F.density t).density z) y
        - κ / (N : ℝ) * conv dR (F.density s).density y) ^ 2
      = (F.density s).density y * (score (F.density s) y + W N y) ^ 2 := by
    intro N y
    rw [cfv_conv_sum]
    simp only [hW, hc]
    ring
  simp_rw [hrew]
  have hlim : ∫ y, (F.density s).density y * (score (F.density s) y
        + κ * ∑ t, F.weight t * conv dR (F.density t).density y) ^ 2 ∂haar 1
      = ∫ y, (F.density s).density y * (score (F.density s) y
        + (κ * ∑ t, F.weight t * c t y)) ^ 2 ∂haar 1 := rfl
  rw [hlim]
  refine tendsto_integral_filter_of_dominated_convergence _
    (Eventually.of_forall fun N : ℕ+ => (cfv_main_integrable (F.density s) (hWc N)).aestronglyMeasurable)
    (Eventually.of_forall fun N : ℕ+ => Eventually.of_forall fun y => ?_) hbd
    (Eventually.of_forall fun y => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ((F.density s).density_nonneg y) (sq_nonneg _))]
    have h := hWb N y
    have hρ := (F.density s).density_nonneg y
    have hsq : W N y ^ 2 ≤ (2 * (|κ| * M)) ^ 2 := sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
    have : (score (F.density s) y + W N y) ^ 2 ≤ 2 * score (F.density s) y ^ 2
        + 2 * (2 * (|κ| * M)) ^ 2 := by nlinarith [sq_nonneg (score (F.density s) y - W N y)]
    nlinarith [mul_le_mul_of_nonneg_left this hρ]
  · have hN : Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop
    have hinv : Tendsto (fun N : ℕ+ => κ / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hN
    have h1 : Tendsto (fun N : ℕ+ => W N y) atTop (𝓝 (κ * ∑ t, F.weight t * c t y)) := by
      have a := (tendsto_finsetSum Finset.univ fun t _ => (hσ t).mul_const (c t y)).const_mul κ
      have b := hinv.mul_const (c s y)
      simpa [hW] using a.sub b
    exact tendsto_const_nhds.mul ((tendsto_const_nhds.add h1).pow 2)


theorem cfv_species_term (F : SpeciesFamily 1) (s : Fin F.count) :
    ∫⁻ x, ENNReal.ofReal (‖(2 : ℝ) • F.sqrtGradient s x
        + (F.density s).sqrt x • positiveH1Drift.force (barycenter F) x‖ ^ 2) ∂haar 1 =
      ENNReal.ofReal (∫ y, (F.density s).density y * (score (F.density s) y
        + kappa * ∑ t, F.weight t * conv dR (F.density t).density y) ^ 2 ∂haar 1) := by
  have hbar : (barycenter F).density = fun z => ∑ t, F.weight t * (F.density t).density z :=
    funext fun x => F.barycenter_density_apply x
  set W : Torus 1 → ℝ := fun y => kappa * ∑ t, F.weight t * conv dR (F.density t).density y
    with hW
  have hWc : Continuous W :=
    continuous_const.mul (continuous_finsetSum _ fun t _ =>
      continuous_const.mul (continuous_driftField (F.density t)))
  have hWe : ∀ y, kappa * conv dR (barycenter F).density y = W y := by
    intro y
    rw [hbar, cfv_conv_sum]
  obtain ⟨-, -, -, -, -, -, -, hforce, -⟩ := admissibleRegularity (barycenter F)
  have hae : ∀ᵐ y ∂haar 1, ‖(2 : ℝ) • F.sqrtGradient s y
        + (F.density s).sqrt y • positiveH1Drift.force (barycenter F) y‖ ^ 2
      = (F.density s).density y * (score (F.density s) y + W y) ^ 2 := by
    filter_upwards [cfv_main_ae (F.density s) W] with y hy
    rw [hy, h1011_norm_sq, hforce y]
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul,
      ← hWe y]
    rfl
  have hI := cfv_main_integrable (F.density s) hWc
  rw [lintegral_congr_ae (hae.mono fun y hy => by rw [hy]),
    ← ofReal_integral_eq_lintegral_ofReal hI
      (Eventually.of_forall fun y => mul_nonneg ((F.density s).density_nonneg y) (sq_nonneg _))]


theorem cfv_dissipation_eq (F : SpeciesFamily 1) :
    speciesDissipation positiveH1 positiveH1Drift F = ENNReal.ofReal
      (∑ s, F.weight s * ∫ y, (F.density s).density y * (score (F.density s) y
        + kappa * ∑ t, F.weight t * conv dR (F.density t).density y) ^ 2 ∂haar 1) := by
  unfold speciesDissipation
  have hnn : ∀ s, 0 ≤ ∫ y, (F.density s).density y * (score (F.density s) y
        + kappa * ∑ t, F.weight t * conv dR (F.density t).density y) ^ 2 ∂haar 1 :=
    fun s => integral_nonneg fun y => mul_nonneg ((F.density s).density_nonneg y) (sq_nonneg _)
  rw [ENNReal.ofReal_sum_of_nonneg fun s _ => mul_nonneg (F.weight_nonneg s) (hnn s)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ENNReal.ofReal_mul (F.weight_nonneg s)]
  exact congrArg _ (cfv_species_term F s)

/-- **H1018.** Finite family conditional force variance. -/
theorem finite_family_conditional_force_variance (κ : ℝ) (F : SpeciesFamily 1) {B : ℝ}
    (hB : ∀ s, ∀ᵐ y ∂haar 1, (F.density s).density y ≤ B) :
    (∀ (N : ℕ+) (σ : Fin N → Fin F.count), ∃ e : ℝ,
      4 * particleEnergy (kernelData κ) N
          ⟨root κ fun i => F.density (σ i),
            (finite_species_rough_product_admissibility κ N σ F.density).1⟩ / N =
        ∑ s, frac σ s * ∫ y, (F.density s).density y * (score (F.density s) y
          + κ * conv dR (fun z => ∑ t, frac σ t * (F.density t).density z) y
          - κ / (N : ℝ) * conv dR (F.density s).density y) ^ 2 ∂haar 1 + e ∧
      0 ≤ e ∧ e ≤ κ ^ 2 * B * (∫ y, dR y ^ 2 ∂haar 1) / N) ∧
    (κ = kappa → speciesDissipation positiveH1 positiveH1Drift F ≠ ⊤ ∧
      ∀ σ : ∀ N : ℕ+, Fin N → Fin F.count,
        (∀ s, Tendsto (fun N : ℕ+ => frac (σ N) s) atTop (𝓝 (F.weight s))) →
        Tendsto (fun N : ℕ+ =>
          4 * particleEnergy (kernelData κ) N
            ⟨root κ fun i => F.density (σ N i),
              (finite_species_rough_product_admissibility κ N (σ N) F.density).1⟩ / N) atTop
          (𝓝 (speciesDissipation positiveH1 positiveH1Drift F).toReal)) := by
  refine ⟨fun N σ => cfv_finite κ F N σ hB, fun hκ => ⟨?_, ?_⟩⟩
  · rw [cfv_dissipation_eq]; exact ENNReal.ofReal_ne_top
  intro σ hσ
  subst hκ
  choose e he using fun N : ℕ+ => cfv_finite kappa F N (σ N) hB
  have hnn : 0 ≤ ∑ s, F.weight s * ∫ y, (F.density s).density y * (score (F.density s) y
        + kappa * ∑ t, F.weight t * conv dR (F.density t).density y) ^ 2 ∂haar 1 :=
    Finset.sum_nonneg fun s _ => mul_nonneg (F.weight_nonneg s)
      (integral_nonneg fun y => mul_nonneg ((F.density s).density_nonneg y) (sq_nonneg _))
  rw [cfv_dissipation_eq, ENNReal.toReal_ofReal hnn]
  have hN : Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop
  have hinv : Tendsto (fun N : ℕ+ => kappa ^ 2 * B * (∫ y, dR y ^ 2 ∂haar 1) / (N : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hN
  have he0 : Tendsto e atTop (𝓝 0) :=
    squeeze_zero (fun N => (he N).2.1) (fun N => (he N).2.2) hinv
  have hmain := (tendsto_finsetSum Finset.univ fun s _ =>
    (hσ s).mul (cfv_phi_tendsto kappa F σ hσ s)).add he0
  rw [add_zero] at hmain
  exact hmain.congr fun N => ((he N).1).symm


end DGPS.Examples.PositiveH1.Recovery
