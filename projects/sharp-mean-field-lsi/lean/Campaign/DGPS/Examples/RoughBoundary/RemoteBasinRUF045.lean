import DGPS.Examples.RoughBoundary.BasinSupportRUF044

/-!
# Remote basin exponential lower bound (RUF045)

For the smooth statistic `Y_N(x) = N⁻¹ Σ Φ(x_i)` built from the RUF043 feature `Φ`, the basin
`A = {|Y_N - z_*| < r/2}` (with `r = R/4`, `z_* = κ⁻¹ t_*`) carries exponentially small but
uniformly positive particle probability `c_A e^{-NΔ}` with `c_A = (2 C_Z)⁻¹`.

The normalizer bound `1 ≤ Z_N ≤ C_Z` is derived for the feature parameter `L` from the RUF039
Gaussian representation and the RUF040 three-region estimate; its local and annulus data are
obtained from the landscape certificate and the exact moments of `Ufeat` (RUF022).
-/

open MeasureTheory
open scoped ENNReal ContDiff

namespace DGPS.Examples.RoughBoundary.Bottleneck

open DGPS.Examples.RoughBoundary.Feature
open DGPS.Examples.RoughBoundary.FreeEnergy
open DGPS.Examples.RoughBoundary.Model
open DGPS.Examples.RoughBoundary.Particle
open DGPS.Examples.RoughBoundary.Semicontinuity
open DGPS.Examples.RoughBoundary.Landscape
open Metric

lemma integral_pi_marginal_RUF045 {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {N : ℕ} (i : Fin N) (F : α → ℝ) :
    ∫ x, F (x i) ∂(Measure.pi fun _ : Fin N => ν) = ∫ y, F y ∂ν := by
  let h : Fin N → α → ℝ := fun k => if k = i then F else fun _ => 1
  have hprod : ∀ x : Fin N → α, F (x i) = ∏ k, h k (x k) := by
    intro x
    rw [Finset.prod_eq_single i]
    · simp [h]
    · intro b _ hb; simp [h, hb]
    · intro hi; exact absurd (Finset.mem_univ _) hi
  have hfac : ∏ k, ∫ y, h k y ∂ν = ∫ y, F y ∂ν := by
    rw [Finset.prod_eq_single i]
    · simp [h]
    · intro b _ hb; simp [h, hb]
    · intro hi; exact absurd (Finset.mem_univ _) hi
  rw [integral_congr_ae (ae_of_all _ hprod), integral_fintype_prod_eq_prod h, hfac]

lemma integral_pi_pair_RUF045 {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {N : ℕ} {i j : Fin N} (hij : i ≠ j) (F G : α → ℝ) :
    ∫ x, F (x i) * G (x j) ∂(Measure.pi fun _ : Fin N => ν) =
      (∫ y, F y ∂ν) * ∫ y, G y ∂ν := by
  classical
  let h : Fin N → α → ℝ := fun k => if k = i then F else if k = j then G else fun _ => 1
  have hij' : j ≠ i := hij.symm
  have hprod : ∀ x : Fin N → α, F (x i) * G (x j) = ∏ k, h k (x k) := by
    intro x
    rw [Finset.prod_eq_mul (s := Finset.univ) i j hij]
    · simp [h, hij']
    · intro c _ hc
      simp [h, hc.1, hc.2]
    · intro hi; exact absurd (Finset.mem_univ _) hi
    · intro hj; exact absurd (Finset.mem_univ _) hj
  have hfac : ∏ k, ∫ y, h k y ∂ν = (∫ y, F y ∂ν) * ∫ y, G y ∂ν := by
    rw [Finset.prod_eq_mul (s := Finset.univ) i j hij]
    · simp [h, hij']
    · intro c _ hc
      simp [h, hc.1, hc.2]
    · intro hi; exact absurd (Finset.mem_univ _) hi
    · intro hj; exact absurd (Finset.mem_univ _) hj
  rw [integral_congr_ae (ae_of_all _ hprod), integral_fintype_prod_eq_prod h, hfac]

lemma integrable_bdd_pi_RUF045 {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {N : ℕ} {F : (Fin N → α) → ℝ} (hF : Measurable F) {C : ℝ}
    (hb : ∀ x, ‖F x‖ ≤ C) : Integrable F (Measure.pi fun _ : Fin N => ν) :=
  Integrable.mono' (integrable_const C) hF.aestronglyMeasurable (ae_of_all _ hb)

lemma inner_expand_RUF045 (a b : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ a b = a 0 * b 0 + a 1 * b 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

lemma coord_measurable_RUF045 (c : Fin 2) :
    Measurable fun y : EuclideanSpace ℝ (Fin 2) => y c := by
  fun_prop

lemma integrable_inner_pair_RUF045 {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {N : ℕ} (g : α → EuclideanSpace ℝ (Fin 2)) (hg : Measurable g)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖g y‖ ≤ C) (i j : Fin N) :
    Integrable (fun x : Fin N → α => inner ℝ (g (x i)) (g (x j)))
      (Measure.pi fun _ : Fin N => ν) := by
  refine integrable_bdd_pi_RUF045 ν (hg.comp (measurable_pi_apply i)
    |>.inner (hg.comp (measurable_pi_apply j))) (C := C * C) fun x => ?_
  rw [Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hC _) (hC _) (norm_nonneg _) hC0)

lemma norm_coord_le_RUF045 (a : EuclideanSpace ℝ (Fin 2)) (c : Fin 2) : ‖a c‖ ≤ ‖a‖ :=
  PiLp.norm_apply_le a c

lemma integral_inner_pair_zero_RUF045 {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    (g : α → EuclideanSpace ℝ (Fin 2)) (hg : Measurable g) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y, ‖g y‖ ≤ C) (hmean : ∫ y, g y ∂ν = 0) :
    ∫ x, inner ℝ (g (x i)) (g (x j)) ∂(Measure.pi fun _ : Fin N => ν) = 0 := by
  have hgint : Integrable g ν :=
    Integrable.mono' (integrable_const C) hg.aestronglyMeasurable (ae_of_all _ hC)
  have hcoord : ∀ c : Fin 2, ∫ y, g y c ∂ν = 0 := by
    intro c
    have h := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj c) hgint
    simpa [hmean] using h
  have hexp : ∀ x : Fin N → α,
      inner ℝ (g (x i)) (g (x j)) = ∑ c : Fin 2, g (x i) c * g (x j) c := by
    intro x
    rw [inner_expand_RUF045, Fin.sum_univ_two]
  simp_rw [hexp]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun c _ => ?_
    rw [integral_pi_pair_RUF045 ν hij (fun y => g y c) (fun y => g y c), hcoord c, zero_mul]
  · intro c _
    refine integrable_bdd_pi_RUF045 ν (C := C * C) ?_ fun x => ?_
    · exact ((coord_measurable_RUF045 c).comp (hg.comp (measurable_pi_apply i))).mul
        ((coord_measurable_RUF045 c).comp (hg.comp (measurable_pi_apply j)))
    · rw [norm_mul]
      exact mul_le_mul ((norm_coord_le_RUF045 _ c).trans (hC _))
        ((norm_coord_le_RUF045 _ c).trans (hC _)) (norm_nonneg _) hC0

lemma integral_sq_norm_sum_RUF045 {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {N : ℕ} (g : α → EuclideanSpace ℝ (Fin 2)) (hg : Measurable g)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖g y‖ ≤ C) (hmean : ∫ y, g y ∂ν = 0) :
    ∫ x : Fin N → α, ‖∑ i, g (x i)‖ ^ 2 ∂(Measure.pi fun _ : Fin N => ν) =
      (N : ℝ) * ∫ y, ‖g y‖ ^ 2 ∂ν := by
  have hpt : ∀ x : Fin N → α, ‖∑ i, g (x i)‖ ^ 2 = ∑ i, ∑ j, inner ℝ (g (x i)) (g (x j)) := by
    intro x
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => integrable_inner_pair_RUF045 ν g hg hC0 hC i j))]
  have hi : ∀ i : Fin N, ∫ x : Fin N → α, ∑ j, inner ℝ (g (x i)) (g (x j))
      ∂(Measure.pi fun _ : Fin N => ν) = ∫ y, ‖g y‖ ^ 2 ∂ν := by
    intro i
    rw [integral_finsetSum _ (fun j _ => integrable_inner_pair_RUF045 ν g hg hC0 hC i j)]
    rw [Finset.sum_eq_single i]
    · simp only [real_inner_self_eq_norm_sq]
      exact integral_pi_marginal_RUF045 ν i (fun y => ‖g y‖ ^ 2)
    · intro j _ hj
      exact integral_inner_pair_zero_RUF045 ν hj.symm g hg hC0 hC hmean
    · intro hi'; exact absurd (Finset.mem_univ _) hi'
  simp [hi]

/-- Chebyshev bound for the empirical mean of a centred bounded feature. -/
lemma prob_mean_norm_ge_RUF045 {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {N : ℕ} (hN : 0 < N) (g : α → EuclideanSpace ℝ (Fin 2))
    (hg : Measurable g) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖g y‖ ≤ C)
    (hmean : ∫ y, g y ∂ν = 0) {r : ℝ} (hr : 0 < r) :
    (Measure.pi fun _ : Fin N => ν).real {x | r ≤ ‖(N : ℝ)⁻¹ • ∑ i, g (x i)‖} ≤
      (∫ y, ‖g y‖ ^ 2 ∂ν) / (N * r ^ 2) := by
  set μ := Measure.pi fun _ : Fin N => ν with hμdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : ∀ x : Fin N → α,
      ‖(N : ℝ)⁻¹ • ∑ i, g (x i)‖ ^ 2 = (N : ℝ)⁻¹ ^ 2 * ‖∑ i, g (x i)‖ ^ 2 := by
    intro x
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hmeas : Measurable fun x : Fin N → α => ‖(N : ℝ)⁻¹ • ∑ i, g (x i)‖ := by
    fun_prop
  have hb : ∀ x : Fin N → α, ‖(N : ℝ)⁻¹ • ∑ i, g (x i)‖ ≤ C := by
    intro x
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hNpos, inv_mul_le_iff₀ hNpos]
    have h1 := (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul Finset.univ
      (fun i => ‖g (x i)‖) C fun i _ => hC (x i))
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    linarith
  have hint : Integrable (fun x : Fin N → α => ‖(N : ℝ)⁻¹ • ∑ i, g (x i)‖ ^ 2) μ := by
    refine integrable_bdd_pi_RUF045 ν (C := C ^ 2) (hmeas.pow_const 2) fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
  have hcheb := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := fun x : Fin N → α =>
    ‖(N : ℝ)⁻¹ • ∑ i, g (x i)‖ ^ 2) (ae_of_all _ fun x => sq_nonneg _) hint (r ^ 2)
  have hsub : {x : Fin N → α | r ≤ ‖(N : ℝ)⁻¹ • ∑ i, g (x i)‖} ⊆
      {x | r ^ 2 ≤ ‖(N : ℝ)⁻¹ • ∑ i, g (x i)‖ ^ 2} := by
    intro x hx
    exact pow_le_pow_left₀ hr.le hx 2
  have hmono := measureReal_mono (μ := μ) hsub
  have hint_val : ∫ x : Fin N → α, ‖(N : ℝ)⁻¹ • ∑ i, g (x i)‖ ^ 2 ∂μ =
      (N : ℝ)⁻¹ ^ 2 * ((N : ℝ) * ∫ y, ‖g y‖ ^ 2 ∂ν) := by
    simp_rw [hsq]
    rw [integral_const_mul, integral_sq_norm_sum_RUF045 ν g hg hC0 hC hmean]
  have h1 : r ^ 2 * μ.real {x : Fin N → α | r ≤ ‖(N : ℝ)⁻¹ • ∑ i, g (x i)‖} ≤
      (N : ℝ)⁻¹ ^ 2 * ((N : ℝ) * ∫ y, ‖g y‖ ^ 2 ∂ν) := by
    rw [← hint_val]
    exact (mul_le_mul_of_nonneg_left hmono (sq_nonneg r)).trans hcheb
  rw [le_div_iff₀ (by positivity)]
  have h2 := mul_le_mul_of_nonneg_left h1 hNpos.le
  have e : (N : ℝ) * ((N : ℝ)⁻¹ ^ 2 * ((N : ℝ) * ∫ y, ‖g y‖ ^ 2 ∂ν)) = ∫ y, ‖g y‖ ^ 2 ∂ν := by
    field_simp
  nlinarith [h2, e]

/-- Basin concentration: for a bounded feature `Φ` whose mean lies within `r/4` of `z`, the empirical
mean of `N` independent draws from `ν` lies in the ball of radius `r/2` about `z` with probability at
least `1/2`, once `N ≥ 128 C² / r²`. -/
theorem basin_concentration_RUF045 {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (Φ : α → EuclideanSpace ℝ (Fin 2)) (hΦ : Measurable Φ)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖Φ y‖ ≤ C) {r : ℝ} (hr : 0 < r)
    {z : EuclideanSpace ℝ (Fin 2)} (hz : ‖(∫ y, Φ y ∂ν) - z‖ < r / 4)
    {N : ℕ} (hN : 0 < N) (hNbig : 128 * C ^ 2 / r ^ 2 ≤ N) :
    1 / 2 ≤ (Measure.pi fun _ : Fin N => ν).real
      {x | ‖((N : ℝ)⁻¹ • ∑ i, Φ (x i)) - z‖ < r / 2} := by
  set μ := Measure.pi fun _ : Fin N => ν with hμdef
  set m := ∫ y, Φ y ∂ν with hm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set g : α → EuclideanSpace ℝ (Fin 2) := fun y => Φ y - m with hgdef
  have hg : Measurable g := hΦ.sub_const m
  have hΦint : Integrable Φ ν :=
    Integrable.mono' (integrable_const C) hΦ.aestronglyMeasurable (ae_of_all _ hC)
  have hmean : ∫ y, g y ∂ν = 0 := by
    rw [hgdef, integral_sub hΦint (integrable_const m)]
    simp [hm]
  have hmC : ‖m‖ ≤ C := by
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := Φ) (C := C) (ae_of_all _ hC)
    simpa using this
  have hgb : ∀ y, ‖g y‖ ≤ 2 * C := by
    intro y
    rw [hgdef]
    calc ‖Φ y - m‖ ≤ ‖Φ y‖ + ‖m‖ := norm_sub_le _ _
      _ ≤ 2 * C := by linarith [hC y]
  have hV : ∫ y, ‖g y‖ ^ 2 ∂ν ≤ 4 * C ^ 2 := by
    have hint : Integrable (fun y => ‖g y‖ ^ 2) ν :=
      Integrable.mono' (integrable_const ((2 * C) ^ 2)) (hg.norm.pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hgb y) 2)
    calc ∫ y, ‖g y‖ ^ 2 ∂ν ≤ ∫ _y, (2 * C) ^ 2 ∂ν :=
          integral_mono hint (integrable_const _) fun y => pow_le_pow_left₀ (norm_nonneg _) (hgb y) 2
      _ = 4 * C ^ 2 := by simp; ring
  have hbad := prob_mean_norm_ge_RUF045 ν hN g hg (by linarith [hC0] : (0 : ℝ) ≤ 2 * C)
    hgb hmean (by positivity : (0 : ℝ) < r / 4)
  have hNr : 128 * C ^ 2 ≤ N * r ^ 2 := by
    rwa [div_le_iff₀ (by positivity)] at hNbig
  have hbound : (∫ y, ‖g y‖ ^ 2 ∂ν) / (N * (r / 4) ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hV, hNr]
  have hkey : ∀ x : Fin N → α,
      ((N : ℝ)⁻¹ • ∑ i, Φ (x i)) - z = ((N : ℝ)⁻¹ • ∑ i, g (x i)) + (m - z) := by
    intro x
    have hsm : (N : ℝ)⁻¹ • ∑ _i : Fin N, m = m := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
        smul_smul, inv_mul_cancel₀ hNpos.ne', one_smul]
    rw [hgdef]
    simp only
    rw [Finset.sum_sub_distrib, smul_sub, hsm]
    abel
  have hmeasg : Measurable fun x : Fin N → α => ‖(N : ℝ)⁻¹ • ∑ i, g (x i)‖ := by
    fun_prop
  have hBm : MeasurableSet {x : Fin N → α | r / 4 ≤ ‖(N : ℝ)⁻¹ • ∑ i, g (x i)‖} :=
    measurableSet_le measurable_const hmeasg
  have hcompl : {x : Fin N → α | ‖(N : ℝ)⁻¹ • ∑ i, g (x i)‖ < r / 4} =
      {x : Fin N → α | r / 4 ≤ ‖(N : ℝ)⁻¹ • ∑ i, g (x i)‖}ᶜ := by
    ext x; simp
  have hsum := measureReal_add_measureReal_compl (μ := μ) hBm
  rw [probReal_univ] at hsum
  have hincl : {x : Fin N → α | ‖(N : ℝ)⁻¹ • ∑ i, g (x i)‖ < r / 4} ⊆
      {x | ‖((N : ℝ)⁻¹ • ∑ i, Φ (x i)) - z‖ < r / 2} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [hkey x]
    have := norm_add_le ((N : ℝ)⁻¹ • ∑ i, g (x i)) (m - z)
    linarith [hz]
  have hmono := measureReal_mono (μ := μ) hincl
  rw [hcompl] at hmono
  linarith [hbad, hbound, hsum, hmono]

/-- RUF045 normalizer upper bound at an arbitrary feature parameter `L`: the three-region estimate of
RUF040, with the Gaussian representation of RUF039 supplied for general `L`. -/
lemma particle_normalizer_upper_RUF045 {L : ℝ} (hL : 0 < L) {a r₀ R₀ b₀ : ℝ} (ha : 0 < a)
    (hb₀ : 0 < b₀) (hR : max r₀ (4 * kappa0) < R₀)
    (hloc : ∀ t : EuclideanSpace ℝ (Fin 2), ‖t‖ ≤ r₀ →
      a * ‖t‖ ^ 2 ≤ featurePotential kappa0 (Ufeat L (1 / L)) t)
    (hmin : IsLeast ((fun t : EuclideanSpace ℝ (Fin 2) =>
      featurePotential kappa0 (Ufeat L (1 / L)) t) ''
        {t : EuclideanSpace ℝ (Fin 2) | r₀ ≤ ‖t‖ ∧ ‖t‖ ≤ R₀}) b₀)
    (N : ℕ+) :
    (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N) ≤
      (2 * kappa0 * a)⁻¹ + 2 + R₀ ^ 2 / (2 * kappa0 * Real.exp 1 * b₀) := by
  have hκ : (0 : ℝ) < kappa0 := kappa0_pos_RUF039
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hfun : (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N) =
      ∫ x : ParticleSpace 1 N,
        Real.exp ((N : ℝ) * kappa0 * ‖(N : ℝ)⁻¹ • ∑ i, Ufeat L (1 / L) (x i)‖ ^ 2 / 2)
          ∂particleHaar 1 N := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [roughB, featureSum, kappa_eq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    congr 1
    field_simp
  rw [hfun, exact_gaussian_representation_general_RUF039 (ε := 1 / L) hL hκ N]
  have hbound := integral_exp_neg_bound_RUF040 (ε := 1 / L) hL hκ N ha hb₀ hR hloc hmin
  have hNE : (N : ℝ) * Real.exp (-((N : ℝ) * b₀)) ≤ Real.exp (-1) / b₀ := by
    rw [le_div_iff₀ hb₀]
    have hx := mul_exp_neg_le_RUF040 ((N : ℝ) * b₀)
    calc (N : ℝ) * Real.exp (-((N : ℝ) * b₀)) * b₀
        = (N : ℝ) * b₀ * Real.exp (-((N : ℝ) * b₀)) := by ring
      _ ≤ Real.exp (-1) := hx
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have key : (N : ℝ) / (2 * Real.pi * kappa0) *
      (Real.pi / ((N : ℝ) * a) + Real.pi * R₀ ^ 2 * Real.exp (-((N : ℝ) * b₀)) +
        Real.pi / ((N : ℝ) / (4 * kappa0))) =
      (2 * kappa0 * a)⁻¹ + 2 +
        ((N : ℝ) * Real.exp (-((N : ℝ) * b₀))) * (R₀ ^ 2 / (2 * kappa0)) := by
    field_simp
    ring
  have hfin : (N : ℝ) * Real.exp (-((N : ℝ) * b₀)) * (R₀ ^ 2 / (2 * kappa0)) ≤
      Real.exp (-1) / b₀ * (R₀ ^ 2 / (2 * kappa0)) :=
    mul_le_mul_of_nonneg_right hNE (by positivity)
  have hexp : Real.exp (-1) / b₀ * (R₀ ^ 2 / (2 * kappa0)) =
      R₀ ^ 2 / (2 * kappa0 * Real.exp 1 * b₀) := by
    rw [Real.exp_neg]
    field_simp
  calc (N : ℝ) / (2 * Real.pi * kappa0) * ∫ t : EuclideanSpace ℝ (Fin 2),
        Real.exp (-(N : ℝ) * featurePotential kappa0 (Ufeat L (1 / L)) t)
      ≤ (N : ℝ) / (2 * Real.pi * kappa0) *
          (Real.pi / ((N : ℝ) * a) + Real.pi * R₀ ^ 2 * Real.exp (-((N : ℝ) * b₀)) +
            Real.pi / ((N : ℝ) / (4 * kappa0))) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (2 * kappa0 * a)⁻¹ + 2 +
        ((N : ℝ) * Real.exp (-((N : ℝ) * b₀))) * (R₀ ^ 2 / (2 * kappa0)) := key
    _ ≤ (2 * kappa0 * a)⁻¹ + 2 + R₀ ^ 2 / (2 * kappa0 * Real.exp 1 * b₀) := by
        linarith [hfin, hexp]

/-- The normalizer data of RUF040 follow from the rough-landscape certificate: the local quadratic
lower bound near `0` comes from the exact first two moments of `Ufeat` (RUF022, `h/4 = 1/88` on
`‖t‖ ≤ h/16`), and the annulus minimum is positive since `Ψ ≥ 0` vanishes only at `0`. -/
lemma normalizer_data_RUF045 {L : ℝ} (hL : 0 < L)
    (hcert : RoughLandscapeCertificate (Ufeat L (1 / L))) :
    ∃ a r₁ R₀ b₀ : ℝ, 0 < a ∧ 0 < r₁ ∧
      (∀ t : EuclideanSpace ℝ (Fin 2), ‖t‖ ≤ r₁ →
        a * ‖t‖ ^ 2 ≤ featurePotential kappa0 (Ufeat L (1 / L)) t) ∧
      max r₁ (4 * kappa0) < R₀ ∧ 0 < b₀ ∧
      IsLeast ((fun t : EuclideanSpace ℝ (Fin 2) =>
        featurePotential kappa0 (Ufeat L (1 / L)) t) ''
          {t : EuclideanSpace ℝ (Fin 2) | r₁ ≤ ‖t‖ ∧ ‖t‖ ≤ R₀}) b₀ := by
  obtain ⟨hcd, -, hnn, hzero, -⟩ := hcert
  have hmom := exact_shift_symmetries_and_feature_moments hL (1 / L)
  have hloc := (uniform_convex_neighborhood_of_zero (measurable_Ufeat hL (1 / L))
    (fun y => (norm_Ufeat L (1 / L) y).le) hmom.1.2.2.1 hmom.1.2.2.2).2.2.2.2.2.2
  set r₁ : ℝ := (1 / 22 : ℝ) / 16 with hr₁
  have hr₁pos : 0 < r₁ := by rw [hr₁]; norm_num
  set R₀ : ℝ := max r₁ (4 * kappa0) + 1 with hR₀
  have hR : max r₁ (4 * kappa0) < R₀ := by rw [hR₀]; linarith
  set K : Set (EuclideanSpace ℝ (Fin 2)) := {t | r₁ ≤ ‖t‖ ∧ ‖t‖ ≤ R₀} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin 2))) (r := R₀)).subset ?_
      intro t ht
      rw [mem_closedBall_zero_iff]
      exact ht.2
  have hne : K.Nonempty := by
    refine ⟨EuclideanSpace.single 0 r₁, ?_, ?_⟩
    · rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos hr₁pos]
    · rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos hr₁pos]
      exact (le_max_left _ _).trans hR.le
  obtain ⟨x, hxK, hxmin⟩ := hKc.exists_isMinOn hne hcd.continuous.continuousOn
  have hx0 : x ≠ 0 := by
    intro h
    have := hxK.1
    rw [h, norm_zero] at this
    linarith
  have hbpos : 0 < featurePotential kappa0 (Ufeat L (1 / L)) x :=
    lt_of_le_of_ne (hnn x) (fun h => hx0 ((hzero x).1 h.symm))
  exact ⟨(1 / 22 : ℝ) / 4, r₁, R₀, _, by norm_num, hr₁pos, hloc, hR, hbpos,
    ⟨x, hxK, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hxmin hy⟩

/-- RUF045, the remote basin exponential lower bound.

Hypotheses: the RUF043 bottleneck data at the critical point `t_*` (with `z_* = κ⁻¹ t_*`, remote level
`Δ = remoteLevel_RUF043`); the normalizer data (local quadratic lower bound and a positive minimum
on the annulus) are derived from `hcert` and the moments of `Ufeat` (`normalizer_data_RUF045`). Conclusion: a smooth feature `Φ` within `η` of
`Ufeat` and a uniform bound `1 ≤ Z_N ≤ C_Z`, with the basin lower bound
`P_N(Y_N ∈ ball(z_*, R/8)) ≥ (2 C_Z)⁻¹ e^{-NΔ}` for all `N ≥ N_A`. -/
theorem remote_basin_exponential_lower_bound {L : ℝ} (hL : 0 < L)
    (hcert : RoughLandscapeCertificate (Ufeat L (1 / L)))
    (tstar : EuclideanSpace ℝ (Fin 2)) (r₀ lam : ℝ) (hr₀ : 0 < r₀) (hlam : 0 < lam)
    (hcrit : fderiv ℝ (featurePotential kappa0 (Ufeat L (1 / L))) tstar = 0)
    (h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∉ closedBall tstar r₀)
    (hH : ∀ x ∈ closedBall tstar r₀, ∀ v : EuclideanSpace ℝ (Fin 2),
      lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (featurePotential kappa0 (Ufeat L (1 / L)))) x v v)
:
    ∃ R : ℝ, 0 < R ∧
      ∃ η : ℝ, 0 < η ∧ η < (R / 4) / 4 ∧
      ∃ Φ : Torus 1 → EuclideanSpace ℝ (Fin 2), ContDiff ℝ ∞ (Φ ∘ DGPS.torusLift) ∧
        (∀ y, ‖Φ y - Ufeat L (1 / L) y‖ ≤ η) ∧
      ∃ C_Z : ℝ, 0 < C_Z ∧
        (∀ N : ℕ+, (1 ≤ (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N) ∧
          (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N) ≤ C_Z)) ∧
        ∃ N_A : ℕ, ∀ N : ℕ+, N_A ≤ (N : ℕ) →
          ENNReal.ofReal ((2 * C_Z)⁻¹ *
              Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar))) ≤
            particleLaw (modelData hL (1 / L)) N
              {x | smoothMean_RUF043 Φ N x ∈ Metric.ball (remoteCentre_RUF043 tstar) ((R / 4) / 2)} := by
  obtain ⟨a, r₁, R₀, b₀, ha, hr₁, hloc, hR, hb₀, hmin⟩ := normalizer_data_RUF045 hL hcert
  obtain ⟨R, hRpos, -, -, -, -, η, hηpos, hηR, Φ, hΦcd, hΦapp, -⟩ :=
    fixed_smooth_bottleneck_feature_and_compatible_neighborhoods hL (1 / L) hcert tstar r₀ lam
      hr₀ hlam hcrit h0 hH
  have hk : (0 : ℝ) < kappa := kappa_pos
  have hself := critical_selfconsistent hL (1 / L) tstar hcrit
  have hν : IsProbabilityMeasure (gibbsMeasure L (1 / L) tstar) :=
    isProbabilityMeasure_gibbs hL (1 / L) tstar
  -- self-consistency: the Gibbs mean at `t_*` is the remote centre `z_*`
  have hcentre : meanFeature L (1 / L) (gibbsMeasure L (1 / L) tstar) =
      remoteCentre_RUF043 tstar := by
    have h1 : kappa • remoteCentre_RUF043 tstar =
        kappa • meanFeature L (1 / L) (gibbsMeasure L (1 / L) tstar) := by
      rw [kappa_smul_centre_RUF043]
      exact hself
    exact (smul_right_injective _ hk.ne' h1).symm
  have hU' : ∫ y, Ufeat L (1 / L) y ∂(gibbsMeasure L (1 / L) tstar) =
      remoteCentre_RUF043 tstar := hcentre
  have hUint : Integrable (Ufeat L (1 / L)) (gibbsMeasure L (1 / L) tstar) :=
    integrable_U hL (1 / L) _
  have hΦcont : Continuous Φ := DGPS.continuous_of_comp_torusLift hΦcd.continuous
  obtain ⟨C₀, hC₀⟩ := isCompact_univ.exists_bound_of_continuousOn hΦcont.continuousOn
  have hC0 : (0 : ℝ) ≤ max C₀ 0 := le_max_right _ _
  have hC : ∀ y, ‖Φ y‖ ≤ max C₀ 0 := fun y =>
    (hC₀ y (Set.mem_univ y)).trans (le_max_left _ _)
  have hΦint : Integrable Φ (gibbsMeasure L (1 / L) tstar) :=
    Integrable.mono' (integrable_const (max C₀ 0)) hΦcont.aestronglyMeasurable (ae_of_all _ hC)
  have hmeanΦ : ‖(∫ y, Φ y ∂(gibbsMeasure L (1 / L) tstar)) - remoteCentre_RUF043 tstar‖ <
      (R / 4) / 4 := by
    have hdiff : (∫ y, Φ y ∂(gibbsMeasure L (1 / L) tstar)) - remoteCentre_RUF043 tstar =
        ∫ y, (Φ y - Ufeat L (1 / L) y) ∂(gibbsMeasure L (1 / L) tstar) := by
      rw [integral_sub hΦint hUint, hU']
    have hb : ‖∫ y, (Φ y - Ufeat L (1 / L) y) ∂(gibbsMeasure L (1 / L) tstar)‖ ≤ η := by
      have h0 := norm_integral_le_of_norm_le_const (μ := gibbsMeasure L (1 / L) tstar)
        (f := fun y => Φ y - Ufeat L (1 / L) y) (C := η) (ae_of_all _ hΦapp)
      simp only [probReal_univ, mul_one] at h0
      exact h0
    rw [hdiff]
    exact lt_of_le_of_lt hb hηR
  have hr4 : (0 : ℝ) < R / 4 := by linarith
  -- the uniform normalizer constant
  obtain ⟨Cz, hCzdef⟩ : ∃ Cz : ℝ,
      Cz = (2 * kappa0 * a)⁻¹ + 2 + R₀ ^ 2 / (2 * kappa0 * Real.exp 1 * b₀) := ⟨_, rfl⟩
  have hZ : ∀ N : ℕ+,
      1 ≤ (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N) ∧
      (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N) ≤ Cz :=
    fun N => ⟨one_le_normalizer_RUF042 hL N, by
      rw [hCzdef]; exact particle_normalizer_upper_RUF045 hL ha hb₀ hR hloc hmin N⟩
  have hCzpos : 0 < Cz := lt_of_lt_of_le one_pos ((hZ 1).1.trans (hZ 1).2)
  refine ⟨R, hRpos, η, hηpos, hηR, Φ, hΦcd, hΦapp, Cz, hCzpos, fun N => hZ N,
    ⌈128 * (max C₀ 0) ^ 2 / (R / 4) ^ 2⌉₊, ?_⟩
  intro N hNA
  have hNpos : 0 < (N : ℕ) := N.pos
  have hbig : 128 * (max C₀ 0) ^ 2 / (R / 4) ^ 2 ≤ ((N : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hNA)
  have hbasin := basin_concentration_RUF045 (gibbsMeasure L (1 / L) tstar) Φ hΦcont.measurable
    hC0 hC hr4 hmeanΦ hNpos hbig
  have hset : {x : ParticleSpace 1 N | smoothMean_RUF043 Φ N x ∈
      Metric.ball (remoteCentre_RUF043 tstar) ((R / 4) / 2)} =
      {x : ParticleSpace 1 N | ‖((N : ℝ)⁻¹ • ∑ i, Φ (x i)) - remoteCentre_RUF043 tstar‖ <
        (R / 4) / 2} := by
    ext x
    simp [smoothMean_RUF043, Metric.mem_ball, dist_eq_norm]
  rw [hset]
  -- tilt identity (RUF044), with `κ • z_* = t_*` in the Gibbs parameter
  have hT := tilt_identity_RUF044 hL N (remoteCentre_RUF043 tstar)
  have hν' : gibbsMeasure L (1 / L) (kappa • remoteCentre_RUF043 tstar) =
      gibbsMeasure L (1 / L) tstar := by
    rw [kappa_smul_centre_RUF043]
  have hD := hT.2.1
  rw [hν'] at hD
  -- pointwise lower bound of the tilted density: the square term is nonnegative
  have hpt : ∀ x : ParticleSpace 1 N,
      -((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar) ≤
        (N : ℝ) * (kappa / 2 * ‖(N : ℝ)⁻¹ • featureSum L (1 / L) N x -
            remoteCentre_RUF043 tstar‖ ^ 2 -
          featurePotential kappa0 (Ufeat L (1 / L)) (kappa • remoteCentre_RUF043 tstar)) := by
    intro x
    have hA : 0 ≤ kappa / 2 * ‖(N : ℝ)⁻¹ • featureSum L (1 / L) N x -
        remoteCentre_RUF043 tstar‖ ^ 2 :=
      mul_nonneg (by linarith [kappa_pos]) (sq_nonneg _)
    have hNn : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hΔ : remoteLevel_RUF043 L (1 / L) tstar =
        featurePotential kappa0 (Ufeat L (1 / L)) (kappa • remoteCentre_RUF043 tstar) := rfl
    rw [hΔ, mul_sub]
    linarith [mul_nonneg hNn hA]
  -- the basin set and the Gibbs product measure
  set P := Measure.pi fun _ : Fin (N : ℕ) => gibbsMeasure L (1 / L) tstar with hPdef
  set S : Set (ParticleSpace 1 N) := {x : ParticleSpace 1 N |
      ‖((N : ℝ)⁻¹ • ∑ i, Φ (x i)) - remoteCentre_RUF043 tstar‖ < (R / 4) / 2} with hSdef
  have hcontS : Continuous (fun x : ParticleSpace 1 N =>
      ‖((N : ℝ)⁻¹ • ∑ i, Φ (x i)) - remoteCentre_RUF043 tstar‖) := by
    fun_prop
  have hSm : MeasurableSet S :=
    measurableSet_lt hcontS.measurable measurable_const
  have h1 := congrArg (fun μ : Measure (ParticleSpace 1 N) => μ S) hD
  simp only [withDensity_apply _ hSm] at h1
  have hlow : ENNReal.ofReal (Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar))) * P S ≤
      ∫⁻ x in S, ENNReal.ofReal (Real.exp (roughB L (1 / L) N x)) ∂particleHaar 1 N := by
    refine le_of_le_of_eq ?_ h1.symm
    rw [← setLIntegral_const]
    exact setLIntegral_mono' hSm fun x _ =>
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hpt x))
  have hZpos : 0 < (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N) :=
    lt_of_lt_of_le one_pos (hZ N).1
  -- particle law on the basin: the normalizer factors out
  have hLaw : particleLaw (modelData hL (1 / L)) N S =
      ENNReal.ofReal (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N)⁻¹ *
        ∫⁻ x in S, ENNReal.ofReal (Real.exp (roughB L (1 / L) N x)) ∂particleHaar 1 N := by
    rw [hT.2.2, withDensity_apply _ hSm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun x => ENNReal.ofReal_mul (inv_nonneg.mpr hZpos.le)
  have hp : (1 / 2 : ℝ) ≤ P.real S := hbasin
  have hZi : Cz⁻¹ ≤ (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N)⁻¹ :=
    inv_anti₀ hZpos (hZ N).2
  have hep : 0 ≤ Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar)) := (Real.exp_pos _).le
  have hpoint : (2 * Cz)⁻¹ * Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar)) ≤
      (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N)⁻¹ *
        (Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar)) * P.real S) := by
    have h2 : (2 * Cz)⁻¹ * Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar)) =
        Cz⁻¹ * (Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar)) * (1 / 2)) := by
      rw [mul_inv]; ring
    rw [h2]
    exact mul_le_mul hZi (mul_le_mul_of_nonneg_left hp hep)
      (mul_nonneg hep (by norm_num)) (inv_nonneg.mpr hZpos.le)
  have hPS : P S = ENNReal.ofReal (P.real S) := by
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hLaw]
  calc ENNReal.ofReal ((2 * Cz)⁻¹ *
        Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar)))
      ≤ ENNReal.ofReal ((∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N)⁻¹ *
          (Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar)) * P.real S)) :=
        ENNReal.ofReal_le_ofReal hpoint
    _ = ENNReal.ofReal (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N)⁻¹ *
          (ENNReal.ofReal (Real.exp (-((N : ℝ) * remoteLevel_RUF043 L (1 / L) tstar))) * P S) := by
        rw [hPS, ENNReal.ofReal_mul (inv_nonneg.mpr hZpos.le),
          ENNReal.ofReal_mul hep]
    _ ≤ ENNReal.ofReal (∫ x : ParticleSpace 1 N, Real.exp (roughB L (1 / L) N x) ∂particleHaar 1 N)⁻¹ *
          ∫⁻ x in S, ENNReal.ofReal (Real.exp (roughB L (1 / L) N x)) ∂particleHaar 1 N :=
        mul_le_mul_of_nonneg_left hlow bot_le

end DGPS.Examples.RoughBoundary.Bottleneck
