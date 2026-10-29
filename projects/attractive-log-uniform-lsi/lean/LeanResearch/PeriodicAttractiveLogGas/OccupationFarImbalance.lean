import LeanResearch.PeriodicAttractiveLogGas.StationaryIsoperimetricReduction
import LeanResearch.PeriodicAttractiveLogGas.StationaryFixedPointRegularity
import LeanResearch.PeriodicAttractiveLogGas.OccupationFarCompactness
import LeanResearch.PeriodicAttractiveLogGas.OccupationCoercivity

/-!
# Actual stationary uniqueness and uniform far occupation imbalance

The supplied source is lines 1577–1668 and 1928–1958. The only independent
geometric input is sharp physical superlevel isoperimetry for smooth
functions on the actual torus. Normalization, original-Green fixed-point
uniqueness and the uniform counterexample-sequence argument are proved
below. The development record distinguishes restricted development checks
from root semantic review and protected verification.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators

namespace PeriodicAttractiveLogGas.OccupationFarImbalance

open MeshCells LabelOccupations DiscreteOccupationIdentities ConditionalLawEstimates
  OccupationNearContraction OccupationNearImbalance OccupationDrift
  StationaryIsoperimetricReduction StationaryLevelGeometry

/-- The literal subtraction made in the supplied stationary proof. -/
def normalizedStationary (u : Torus → ℝ) (z : Torus) : ℝ :=
  u z - Real.log (∫ x, Real.exp (u x) ∂torusMeasure)

theorem exponential_integrable {u : Torus → ℝ} (hu : Continuous u) :
    Integrable (fun x ↦ Real.exp (u x)) torusMeasure :=
  integrable_continuous_torus torusMeasure (Real.continuous_exp.comp hu)

theorem exponential_integral_pos {u : Torus → ℝ} (hu : Continuous u) :
    0 < ∫ x, Real.exp (u x) ∂torusMeasure :=
  integral_exp_pos (exponential_integrable hu)

theorem normalizedStationary_exp {u : Torus → ℝ} (hu : Continuous u) (z : Torus) :
    Real.exp (normalizedStationary u z) =
      Real.exp (u z) / (∫ x, Real.exp (u x) ∂torusMeasure) := by
  rw [normalizedStationary, Real.exp_sub, Real.exp_log (exponential_integral_pos hu)]

theorem normalizedStationary_mass {u : Torus → ℝ} (hu : Continuous u) :
    (∫ z, Real.exp (normalizedStationary u z) ∂torusMeasure) = 1 := by
  simp_rw [normalizedStationary_exp hu]
  rw [integral_div]
  exact div_self (exponential_integral_pos hu).ne'

theorem normalizedStationary_contDiff {u : Torus → ℝ}
    (hu : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ u (torusQuotient x))) :
    ContDiff ℝ ∞ (fun x : PlanarSpace ↦ normalizedStationary u (torusQuotient x)) :=
  hu.sub contDiff_const

theorem normalizedStationary_laplacian {u : Torus → ℝ}
    (hu : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ u (torusQuotient x))) (x : PlanarSpace) :
    Laplacian.laplacian (fun y : PlanarSpace ↦ normalizedStationary u (torusQuotient y)) x =
      Laplacian.laplacian (fun y : PlanarSpace ↦ u (torusQuotient y)) x := by
  have h2 : ContDiffAt ℝ 2 (fun y : PlanarSpace ↦ u (torusQuotient y)) x :=
    hu.contDiffAt.of_le (by simp)
  have hc : ContDiffAt ℝ 2
      (fun _ : PlanarSpace ↦ Real.log (∫ z, Real.exp (u z) ∂torusMeasure)) x := contDiffAt_const
  change Laplacian.laplacian
    ((fun y : PlanarSpace ↦ u (torusQuotient y)) -
      fun _ : PlanarSpace ↦ Real.log (∫ z, Real.exp (u z) ∂torusMeasure)) x = _
  rw [h2.laplacian_sub hc, InnerProductSpace.laplacian_const, Pi.zero_apply, sub_zero]

theorem normalizedStationary_equation {u : Torus → ℝ} {ρ : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ u (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      Laplacian.laplacian (fun y : PlanarSpace ↦ u (torusQuotient y)) x +
        ρ * (Real.exp (u (torusQuotient x)) / (∫ z, Real.exp (u z) ∂torusMeasure) - 1) = 0)
    (x : PlanarSpace) :
    -Laplacian.laplacian (fun y : PlanarSpace ↦ normalizedStationary u (torusQuotient y)) x =
      ρ * (Real.exp (normalizedStationary u (torusQuotient x)) - 1) := by
  have hc := continuous_of_contDiff_lift (hu.of_le (by simp))
  rw [normalizedStationary_laplacian hu x, normalizedStationary_exp hc]
  linarith only [hpde x]

/-- Exact source normalization and rigidity for an arbitrary actual smooth
stationary solution. The only geometric premise concerns its literal
normalized superlevels; no normalization or Laplacian identity is assumed. -/
theorem normalizedStationary_eq_zero {u : Torus → ℝ} {ρ : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ u (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      Laplacian.laplacian (fun y : PlanarSpace ↦ u (torusQuotient y)) x +
        ρ * (Real.exp (u (torusQuotient x)) / (∫ z, Real.exp (u z) ∂torusMeasure) - 1) = 0)
    (hρ : 0 ≤ ρ) (hρmax : ρ ≤ 8 * Real.pi)
    (hiso : SharpPhysicalSuperlevelIsoperimetry (normalizedStationary u)) :
    ∀ z, normalizedStationary u z = 0 :=
  eq_zero_of_sharp_isoperimetry (normalizedStationary_contDiff hu)
    (normalizedStationary_equation hu hpde)
    (normalizedStationary_mass (continuous_of_contDiff_lift (hu.of_le (by simp))))
    hiso hρ hρmax

theorem stationary_constant {u : Torus → ℝ} {ρ : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ u (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      Laplacian.laplacian (fun y : PlanarSpace ↦ u (torusQuotient y)) x +
        ρ * (Real.exp (u (torusQuotient x)) / (∫ z, Real.exp (u z) ∂torusMeasure) - 1) = 0)
    (hρ : 0 ≤ ρ) (hρmax : ρ ≤ 8 * Real.pi)
    (hiso : SharpPhysicalSuperlevelIsoperimetry (normalizedStationary u)) :
    ∀ z, u z = Real.log (∫ x, Real.exp (u x) ∂torusMeasure) := by
  intro z
  exact sub_eq_zero.mp (normalizedStationary_eq_zero hu hpde hρ hρmax hiso z)

/-- The existing scaled sup deviation is controlled by the literal
Euclidean profile norm. This is independent of any probability constraint. -/
theorem profileDeviation_le_euclidean {J : ℕ} (hJ : 0 < J)
    (θ : MeshIndex J → ℝ) :
    profileDeviation θ ≤ (J : ℝ) ^ 2 *
      Real.sqrt (∑ a, (θ a - ((J : ℝ) ^ 2)⁻¹) ^ 2) := by
  classical
  let S : ℝ := ∑ a, (θ a - ((J : ℝ) ^ 2)⁻¹) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hJ2 : 0 < (J : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr hJ) 2
  change ‖fun a ↦ (J : ℝ) ^ 2 * θ a - 1‖ ≤ (J : ℝ) ^ 2 * Real.sqrt S
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hJ2.le (Real.sqrt_nonneg S))).mpr
  intro a
  have ha : (θ a - ((J : ℝ) ^ 2)⁻¹) ^ 2 ≤ S :=
    Finset.single_le_sum (fun b _ ↦ sq_nonneg (θ b - ((J : ℝ) ^ 2)⁻¹))
      (Finset.mem_univ a)
  have habs : |θ a - ((J : ℝ) ^ 2)⁻¹| ≤ Real.sqrt S := by
    nlinarith [Real.sq_sqrt hS, sq_abs (θ a - ((J : ℝ) ^ 2)⁻¹),
      abs_nonneg (θ a - ((J : ℝ) ^ 2)⁻¹), Real.sqrt_nonneg S]
  have he : (J : ℝ) ^ 2 * θ a - 1 =
      (J : ℝ) ^ 2 * (θ a - ((J : ℝ) ^ 2)⁻¹) := by
    rw [mul_sub, mul_inv_cancel₀ hJ2.ne']
  rw [Real.norm_eq_abs, he, abs_mul, abs_of_pos hJ2]
  exact mul_le_mul_of_nonneg_left habs hJ2.le

/-- The exact conversion used for the complement of the established near
neighborhood; no positive lower bound on any cell mass is required. -/
theorem euclidean_far_of_profileDeviation {J : ℕ} (hJ : 0 < J)
    {θ : MeshIndex J → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hfar : δ < profileDeviation θ) :
    (δ / (J : ℝ) ^ 2) ^ 2 ≤ ∑ a, (θ a - ((J : ℝ) ^ 2)⁻¹) ^ 2 := by
  have hJ2 : 0 < (J : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr hJ) 2
  have hS : 0 ≤ ∑ a, (θ a - ((J : ℝ) ^ 2)⁻¹) ^ 2 :=
    Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hh := hfar.le.trans (profileDeviation_le_euclidean hJ θ)
  have hd : δ / (J : ℝ) ^ 2 ≤ Real.sqrt (∑ a, (θ a - ((J : ℝ) ^ 2)⁻¹) ^ 2) := by
    apply (div_le_iff₀ hJ2).mpr
    nlinarith only [hh]
  exact (pow_le_pow_left₀ (div_nonneg hδ hJ2.le) hd 2).trans_eq (Real.sq_sqrt hS)

section SharpGeometry

variable (hiso : ∀ v : Torus → ℝ,
  ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)) →
    SharpPhysicalSuperlevelIsoperimetry v)

include hiso

/-- The source fixed-point corollary for the literal original Green
representative. L4, mass one and the fixed-point equation are the only
analytic input data; the smooth lift and PDE are constructed upstream.
The beta-zero and beta-four endpoints are both retained. -/
theorem original_fixedPoint_eq_one {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure)
    (hmass : (∫ x, f x ∂torusMeasure) = 1) {β : ℝ} (hβ : 0 ≤ β) (hβ4 : β ≤ 4)
    (hfix : f =ᵐ[torusMeasure] fun x ↦
      Real.exp (β * ∫ y, greenRealRepresentative (x - y) * f y ∂torusMeasure) /
        (∫ z, Real.exp (β * ∫ y, greenRealRepresentative (z - y) * f y ∂torusMeasure)
          ∂torusMeasure)) :
    f =ᵐ[torusMeasure] (fun _ ↦ (1 : ℝ)) := by
  have he := StationaryFixedPointRegularity.original_fixedPoint_ae hf β hfix
  let u := StationaryFixedPointRegularity.solution β f
  have hu : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ u (torusQuotient x)) :=
    StationaryFixedPointRegularity.contDiff_solution_of_fixedPoint hf β he
  have hpde := StationaryFixedPointRegularity.fixedPoint_meanField_lift hf hmass β he
  have hρ := StationaryFixedPointRegularity.source_parameter_range hβ hβ4
  have hz := normalizedStationary_eq_zero hu hpde hρ.1 hρ.2
    (hiso (normalizedStationary u) (normalizedStationary_contDiff hu))
  have hc : Continuous u := StationaryFixedPointRegularity.continuous_solution hf β
  have hr (x : Torus) : StationaryFixedPointRegularity.representative β f x = 1 := by
    change Real.exp (u x) / (∫ z, Real.exp (u z) ∂torusMeasure) = 1
    rw [← normalizedStationary_exp hc, hz x, Real.exp_zero]
  exact he.trans (Eventually.of_forall hr)

theorem original_L4_fixedPoint_eq_one {f : L4}
    (hmass : (∫ x, f x ∂torusMeasure) = 1) {β : ℝ} (hβ : 0 ≤ β) (hβ4 : β ≤ 4)
    (hfix : f =ᵐ[torusMeasure] fun x ↦
      Real.exp (β * ∫ y, greenRealRepresentative (x - y) * f y ∂torusMeasure) /
        (∫ z, Real.exp (β * ∫ y, greenRealRepresentative (z - y) * f y ∂torusMeasure)
          ∂torusMeasure)) :
    f = oneL4 := by
  apply Lp.ext
  exact (original_fixedPoint_eq_one hiso (Lp.memLp f) hmass hβ hβ4 hfix).trans oneL4_ae.symm

open OccupationFarCompactness

/-- A literal far sequence with vanishing normalized original imbalance
is impossible. The actual limiting law, its original Green equation and
its nonuniformity are all obtained from the proved compactness mechanism. -/
theorem far_sequence_contradiction {J : ℕ} {β₀ t ε : ℝ} (hsub : β₀ < 4)
    (htC : t ≤ occupationBound β₀) (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (hε : 0 < ε) (s : ℕ → Sample J β₀ t)
    (hm : ∀ k, (s k).state.val ∈ cappedOccupations J ((s k).n + 1) (3 * t / 4))
    (hmargin : ∀ k, 4 ≤ t * ((s k).n + 1 : ℕ))
    (hN : Tendsto (fun k ↦ ((s k).n + 1 : ℝ)) atTop atTop)
    (hfar : ∀ k, ε ^ 2 ≤ ∑ a, ((s k).profile a - ((J : ℝ) ^ 2)⁻¹) ^ 2)
    (hD : Tendsto (fun k ↦ imbalance (mesh_pos hmesh) (s k).beta (s k).state
      (hm k) (hmargin k) / ((s k).n + 1 : ℝ)) atTop (𝓝 0)) : False := by
  obtain ⟨β, f, hβ, _hf0, hmass, hne, hfix⟩ :=
    nonuniform_original_global_fixedPoint_of_far_sequence hsub htC hmesh hε
      s hm hmargin hN hfar hD
  exact hne (original_L4_fixedPoint_eq_one hiso hmass hβ.1.le (hβ.2.trans hsub.le) hfix)

/-- Compactness gives a positive uniform lower bound and one particle
threshold for every original sample at fixed mesh, cap and coupling range.
The proof constructs the counterexample sequence itself; no vanishing
sequence, limiting-rate formula or desired lower bound is a premise. -/
theorem exists_sample_far_lower {J : ℕ} {β₀ t ε : ℝ} (hsub : β₀ < 4)
    (htC : t ≤ occupationBound β₀) (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ s : Sample J β₀ t, N₀ ≤ s.n + 1 →
      ∀ (hm : s.state.val ∈ cappedOccupations J (s.n + 1) (3 * t / 4))
        (hmargin : 4 ≤ t * (s.n + 1 : ℕ)),
        ε ^ 2 ≤ ∑ a, (s.profile a - ((J : ℝ) ^ 2)⁻¹) ^ 2 →
          c * (s.n + 1 : ℝ) ≤ imbalance (mesh_pos hmesh) s.beta s.state hm hmargin := by
  classical
  by_contra hbound
  have hex (k : ℕ) : ∃ s : Sample J β₀ t, k + 2 ≤ s.n + 1 ∧
      ∃ (hm : s.state.val ∈ cappedOccupations J (s.n + 1) (3 * t / 4))
        (hmargin : 4 ≤ t * (s.n + 1 : ℕ)),
        (ε ^ 2 ≤ ∑ a, (s.profile a - ((J : ℝ) ^ 2)⁻¹) ^ 2) ∧
          imbalance (mesh_pos hmesh) s.beta s.state hm hmargin <
            (1 / ((k : ℝ) + 1)) * (s.n + 1 : ℝ) := by
    by_contra hn
    apply hbound
    refine ⟨1 / ((k : ℝ) + 1), by positivity, k + 2, ?_⟩
    intro s hs hm hmargin hfar
    apply le_of_not_gt
    intro hsmall
    exact hn ⟨s, hs, hm, hmargin, hfar, hsmall⟩
  choose s hs hm hmargin hfar hsmall using hex
  have hcount (k : ℕ) : (k : ℝ) ≤ ((s k).n + 1 : ℝ) := by
    have hk : k ≤ (s k).n + 1 := by have := hs k; omega
    exact_mod_cast hk
  have hN : Tendsto (fun k ↦ ((s k).n + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_mono hcount (tendsto_natCast_atTop_atTop (R := ℝ))
  have hD : Tendsto (fun k ↦ imbalance (mesh_pos hmesh) (s k).beta (s k).state
      (hm k) (hmargin k) / ((s k).n + 1 : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun k ↦ div_nonneg
        (OccupationCoercivity.imbalance_nonneg (mesh_pos hmesh) (s k).beta
          (s k).state (hm k) (hmargin k)) (by positivity))
      (fun k ↦ ?_) (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (s k).n + 1)).mpr (hsmall k).le
  exact far_sequence_contradiction hiso hsub htC hmesh hε s hm hmargin hN hfar hD

/-- Source far imbalance with the original particle number and the actual
Euclidean profile-square criterion. The constants are independent of the
coupling, the occupation and N; the source proof is nonnumerical. -/
theorem exists_far_lower {J : ℕ} {β₀ t ε : ℝ} (hsub : β₀ < 4)
    (htC : t ≤ occupationBound β₀) (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (N : ℕ), N₀ ≤ N → ∀ (β : ℝ), 0 ≤ β → β ≤ β₀ →
        ∀ (m : OccupationState J N t) (hm : m.val ∈ cappedOccupations J N (3 * t / 4))
          (hmargin : 4 ≤ t * N),
          ε ^ 2 ≤ ∑ a, (stateProfile m a - ((J : ℝ) ^ 2)⁻¹) ^ 2 →
            c * N ≤ imbalance (mesh_pos hmesh) β m hm hmargin := by
  obtain ⟨c, hc, N₀, hb⟩ := exists_sample_far_lower hiso hsub htC hmesh hε
  refine ⟨c, hc, max N₀ 2, le_max_right _ _, ?_⟩
  intro N hlarge β hβ hβ₀ m hm hmargin hfar
  have hN : 2 ≤ N := (le_max_right _ _).trans hlarge
  have hN₀ : N₀ ≤ N := (le_max_left _ _).trans hlarge
  cases N with
  | zero => omega
  | succ n =>
    let s : Sample J β₀ t :=
      ⟨n, β, m, hN, hβ, hβ₀⟩
    have hh := hb s hN₀ hm hmargin hfar
    simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one] using hh

/-- Genuine positive far constant and one uniform particle threshold for
the literal downstream predicate. The threshold itself supplies N ≥ 2 and
the move margin. Only sharp physical superlevel isoperimetry remains an
independent analytic input. No lower coupling bound or positive cell-mass
condition is imposed. -/
theorem exists_FarImbalance {J : ℕ} {β₀ t : ℝ} (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J) :
    ∃ cFar : ℝ, 0 < cFar ∧ ∃ NFar : ℕ, 2 ≤ NFar ∧
      ∀ N : ℕ, NFar ≤ N → 4 ≤ t * N ∧
        ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
          OccupationCoercivity.FarImbalance (N := N) (t := t)
            (mesh_pos hmesh) β β₀ cFar := by
  have hJ := mesh_pos hmesh
  have hJ2 : 0 < (J : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr hJ) 2
  have hε : 0 < nearNeighborhood β₀ / (J : ℝ) ^ 2 :=
    div_pos (nearNeighborhood_pos hsub) hJ2
  obtain ⟨c, hc, N₀, hN₀, hb⟩ := exists_far_lower hiso hsub htC hmesh hε
  refine ⟨c, hc, max N₀ ⌈4 / t⌉₊, hN₀.trans (le_max_left _ _), ?_⟩
  intro N hlarge
  have hN : N₀ ≤ N := (le_max_left _ _).trans hlarge
  have hceil : ⌈4 / t⌉₊ ≤ N := (le_max_right _ _).trans hlarge
  have hdiv : 4 / t ≤ (N : ℝ) := Nat.ceil_le.mp hceil
  have hmargin : 4 ≤ t * N := by
    have hh := (div_le_iff₀ ht).mp hdiv
    nlinarith only [hh]
  refine ⟨hmargin, ?_⟩
  intro β hβ hβ₀ m hm hmove hfar
  apply hb N hN β hβ hβ₀ m hm hmove
  exact euclidean_far_of_profileDeviation hJ (nearNeighborhood_pos hsub).le hfar

end SharpGeometry

end PeriodicAttractiveLogGas.OccupationFarImbalance
