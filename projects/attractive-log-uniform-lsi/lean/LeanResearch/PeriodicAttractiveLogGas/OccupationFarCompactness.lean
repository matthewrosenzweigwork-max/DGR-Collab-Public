import LeanResearch.PeriodicAttractiveLogGas.OccupationNearContraction
import LeanResearch.PeriodicAttractiveLogGas.OccupationChemicalCoercivity
import LeanResearch.PeriodicAttractiveLogGas.OccupationDrift
import LeanResearch.PeriodicAttractiveLogGas.PermutationPathComparison
import LeanResearch.PeriodicAttractiveLogGas.ReferenceMapCompactness

/-! The actual occupation-limit compactness mechanism, source 1928--1958.
The development record tracks the stronger L4-to-Lipschitz compactness
adaptation and the separate stationary-uniqueness dependency. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

namespace PeriodicAttractiveLogGas.OccupationFarCompactness
open MeshCells MeshAdjacentCells LabelOccupations LabelRatioTransport
  DiscreteOccupationIdentities ConditionalLawEstimates OccupationNearContraction
  OccupationReverseRates OccupationDrift

/-- One original finite-particle sample. Every field is primitive source
data: particle count, coupling interval, and an actual capped occupation.
No analytic limit or approximation property is included. -/
structure Sample (J : ℕ) (β₀ t : ℝ) where
  n : ℕ
  beta : ℝ
  state : OccupationState J (n + 1) t
  two_le : 2 ≤ n + 1
  beta_nonneg : 0 ≤ beta
  beta_le : beta ≤ β₀

def Sample.profile {J : ℕ} {β₀ t : ℝ} (s : Sample J β₀ t) : MeshIndex J → ℝ :=
  occupationProfile (labelOfState s.state).val

theorem Sample.profile_apply {J : ℕ} {β₀ t : ℝ} (s : Sample J β₀ t) (a : MeshIndex J) :
    s.profile a = (s.state.val a : ℝ) / (s.n + 1 : ℕ) := by
  simp only [Sample.profile, occupationProfile, labelOfState,
    OccupationProbability.occupation_labelOfProfile]

theorem Sample.profile_nonneg {J : ℕ} {β₀ t : ℝ} (s : Sample J β₀ t) (a : MeshIndex J) :
    0 ≤ s.profile a := occupationProfile_nonneg (labelOfState s.state).val a

theorem Sample.profile_mass {J : ℕ} {β₀ t : ℝ} (s : Sample J β₀ t) : ∑ a, s.profile a = 1 :=
  occupationProfile_mass (by omega) (labelOfState s.state).val

theorem Sample.profile_le_one {J : ℕ} {β₀ t : ℝ} (s : Sample J β₀ t) (a : MeshIndex J) :
    s.profile a ≤ 1 := by
  have hh := Finset.single_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (MeshIndex J))) => s.profile_nonneg b)
    (Finset.mem_univ a)
  rwa [s.profile_mass] at hh

theorem Sample.cap {J : ℕ} {β₀ t : ℝ} (s : Sample J β₀ t) :
    OccupationCap t (labelOfState s.state).val := (labelOfState s.state).property

def densityBound (J : ℕ) (β₀ : ℝ) : ℝ :=
  (densityNormBound β₀ ^ 4 * (J : ℝ) ^ 6) ^ (1 / 4 : ℝ)

theorem densityBound_nonneg (J : ℕ) (β₀ : ℝ) : 0 ≤ densityBound J β₀ := by
  unfold densityBound
  exact Real.rpow_nonneg (mul_nonneg (pow_nonneg (densityNormBound_pos β₀).le _) (pow_nonneg (Nat.cast_nonneg _) _)) _

/-- The continuous representative of the actual unscaled Green potential
of an arbitrary L4 density, without a near-uniformity restriction. -/
def potential (f : L4) : BoundedContinuousFunction Torus ℝ :=
  ContinuousMap.linearIsometryBoundedOfCompact Torus ℝ ℝ
    ⟨densityPotential f, continuous_densityPotential (Lp.memLp f)⟩

@[simp] theorem potential_apply (f : L4) (x : Torus) : potential f x = densityPotential f x := rfl

theorem potential_bound (f : L4) (x : Torus) :
    |potential f x| ≤ ‖f‖ * lpNorm regularGreenRepresentative GreenConditionalInfluence.conjugateExponent torusMeasure := by
  simpa only [potential_apply, lpNorm_coe] using densityPotential_bound (Lp.memLp f) x

theorem potential_lipschitz (f : L4) :
    LipschitzWith ⟨convolutionLipschitzConstant * ‖f‖ * Real.sqrt 2,
      mul_nonneg (mul_nonneg convolutionLipschitzConstant_pos.le (norm_nonneg _)) (Real.sqrt_nonneg _)⟩
      (potential f) := by
  change LipschitzWith _ (densityPotential f)
  simpa only [lpNorm_coe, NNReal.coe_mk] using! ReferenceMapCompactness.lipschitzWith_of_physical_lift
    (lipschitzWith_densityPotential (Lp.memLp f))

section Actual
variable {J : ℕ} {β₀ t : ℝ} (hsub : β₀ < 4)
  (htC : t ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)

/-- The already constructed equivalence class of the average of the
original prescribed-label Gibbs marginals. -/
def sampleDensity (s : Sample J β₀ t) : L4 :=
  averageMarginalL4 s.two_le s.beta_nonneg s.beta_le hsub htC hmesh
    (labelOfState s.state).val s.cap

theorem sampleDensity_nonneg (s : Sample J β₀ t) : 0 ≤ sampleDensity hsub htC hmesh s :=
  averageMarginalL4_nonneg s.two_le s.beta_nonneg s.beta_le hsub htC hmesh
    (labelOfState s.state).val s.cap

theorem sampleDensity_mass (s : Sample J β₀ t) :
    (∫ x, sampleDensity hsub htC hmesh s x ∂torusMeasure) = 1 :=
  averageMarginalL4_mass s.two_le s.beta_nonneg s.beta_le hsub htC hmesh
    (labelOfState s.state).val s.cap

theorem sampleDensity_bound (s : Sample J β₀ t) : ‖sampleDensity hsub htC hmesh s‖ ≤ densityBound J β₀ := by
  rw [sampleDensity, averageMarginalL4_norm s.two_le s.beta_nonneg s.beta_le hsub htC hmesh
    (labelOfState s.state).val s.cap]
  exact (OccupationFieldL2.averageDensity_L4 s.two_le s.beta_nonneg s.beta_le hsub htC hmesh
    (labelOfState s.state).val s.cap).2.1

theorem sample_potential_eq_original (s : Sample J β₀ t) (x : Torus) :
    potential (sampleDensity hsub htC hmesh s) x =
      OccupationFieldL2.meanPotential (mesh_pos hmesh) (labelOfState s.state).val s.beta x := by
  rw [potential_apply, sampleDensity, densityPotential_congr_ae
    (averageMarginalL4_ae s.two_le s.beta_nonneg s.beta_le hsub htC hmesh
      (labelOfState s.state).val s.cap),
    densityPotential_eq_original
      (OccupationFieldL2.averageDensity_L4 s.two_le s.beta_nonneg s.beta_le hsub htC hmesh
        (labelOfState s.state).val s.cap).1]
  rfl

/-- Genuine relative compactness of all the original potentials at fixed
J, beta0 and cap, uniformly in particle number and in the actual coupling. -/
theorem isCompact_closure_sample_potential :
    IsCompact (closure (Set.range (fun s : Sample J β₀ t => potential (sampleDensity hsub htC hmesh s)))) := by
  apply ReferenceMapCompactness.isCompact_closure_lipschitz_range
    (M := densityBound J β₀ * lpNorm regularGreenRepresentative GreenConditionalInfluence.conjugateExponent torusMeasure)
    (K := ⟨convolutionLipschitzConstant * densityBound J β₀ * Real.sqrt 2, by
      have := convolutionLipschitzConstant_pos.le
      have := densityBound_nonneg J β₀
      positivity⟩)
  · intro s x
    exact (potential_bound _ x).trans (mul_le_mul_of_nonneg_right (sampleDensity_bound hsub htC hmesh s) lpNorm_nonneg)
  · intro s
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro x y
    have hh := lipschitzWith_iff_norm_sub_le.mp (potential_lipschitz (sampleDensity hsub htC hmesh s)) x y
    apply hh.trans
    change convolutionLipschitzConstant * ‖sampleDensity hsub htC hmesh s‖ * Real.sqrt 2 * ‖x - y‖ ≤
      convolutionLipschitzConstant * densityBound J β₀ * Real.sqrt 2 * ‖x - y‖
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sampleDensity_bound hsub htC hmesh s) convolutionLipschitzConstant_pos.le)
        (Real.sqrt_nonneg _)) (norm_nonneg _)

/-- Simultaneous actual subsequence extraction. The potential convergence
is in the uniform norm, while beta and the finite profile use their usual
finite-dimensional topology. -/
theorem exists_sample_subsequence (s : ℕ → Sample J β₀ t) :
    ∃ (β : ℝ) (θ : MeshIndex J → ℝ) (U : BoundedContinuousFunction Torus ℝ)
      (r : ℕ → ℕ), StrictMono r ∧ β ∈ Icc 0 β₀ ∧ θ ∈ Icc 0 1 ∧
      Tendsto (fun k => (s (r k)).beta) atTop (𝓝 β) ∧
      Tendsto (fun k => (s (r k)).profile) atTop (𝓝 θ) ∧
      Tendsto (fun k => potential (sampleDensity hsub htC hmesh (s (r k)))) atTop (𝓝 U) := by
  let K : Set (BoundedContinuousFunction Torus ℝ) :=
    closure (Set.range (fun z : Sample J β₀ t => potential (sampleDensity hsub htC hmesh z)))
  have hK : IsCompact K := isCompact_closure_sample_potential hsub htC hmesh
  have hC : IsCompact ((Icc (0 : ℝ) β₀) ×ˢ ((Icc (0 : MeshIndex J → ℝ) 1) ×ˢ K)) :=
    isCompact_Icc.prod (isCompact_Icc.prod hK)
  let w := fun k => ((s k).beta, ((s k).profile, potential (sampleDensity hsub htC hmesh (s k))))
  have hw (k : ℕ) : w k ∈ ((Icc (0 : ℝ) β₀) ×ˢ ((Icc (0 : MeshIndex J → ℝ) 1) ×ˢ K)) :=
    ⟨⟨(s k).beta_nonneg, (s k).beta_le⟩,
      ⟨⟨(s k).profile_nonneg, (s k).profile_le_one⟩, subset_closure ⟨s k, rfl⟩⟩⟩
  obtain ⟨z, hz, r, hr, hlim⟩ := hC.tendsto_subseq hw
  refine ⟨z.1, z.2.1, z.2.2, r, hr, hz.1, hz.2.1, ?_, ?_, ?_⟩
  · exact (continuous_fst.tendsto z).comp hlim
  · exact (continuous_fst.tendsto z.2).comp ((continuous_snd.tendsto z).comp hlim)
  · exact (continuous_snd.tendsto z.2).comp ((continuous_snd.tendsto z).comp hlim)

end Actual

theorem potential_sub_apply (f g : L4) (x : Torus) :
    potential (f - g) x = potential f x - potential g x := by
  rw [potential_apply, densityPotential_congr_ae (Lp.coeFn_sub f g),
    densityPotential_sub (Lp.memLp f) (Lp.memLp g)]
  rfl

theorem potential_norm_sub (f g : L4) :
    ‖potential f - potential g‖ ≤
      lpNorm regularGreenRepresentative GreenConditionalInfluence.conjugateExponent torusMeasure * ‖f - g‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg lpNorm_nonneg (norm_nonneg _))).mpr
  intro x
  change |potential f x - potential g x| ≤ _
  rw [← potential_sub_apply]
  simpa only [mul_comm] using potential_bound (f - g) x

theorem continuous_potential : Continuous potential := by
  have h : LipschitzWith ⟨lpNorm regularGreenRepresentative GreenConditionalInfluence.conjugateExponent torusMeasure,
      lpNorm_nonneg⟩ potential := lipschitzWith_iff_norm_sub_le.mpr potential_norm_sub
  exact h.continuous

/-- The literal cell-normalized density at a prescribed continuous field.
It agrees with the existing occupation map when the field is beta times
the actual Green potential. -/
def fieldDensityValue {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (U : BoundedContinuousFunction Torus ℝ) (x : Torus) : ℝ :=
  ∑ a, (J : ℝ) ^ 2 * θ a * (meshCell J hJ a).indicator (cellDensity hJ U a) x

theorem fieldDensityValue_memLp {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (U : BoundedContinuousFunction Torus ℝ) : MemLp (fieldDensityValue hJ θ U) 4 torusMeasure := by
  apply memLp_finsetSum
  intro a _
  exact ((memLp_continuous_torus torusMeasure (continuous_cellDensity hJ U.continuous a) 4).indicator
    (measurableSet_meshCell J hJ a)).const_mul _

def fieldDensity {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (U : BoundedContinuousFunction Torus ℝ) : L4 :=
  (fieldDensityValue_memLp hJ θ U).toLp (fieldDensityValue hJ θ U)

theorem fieldDensity_ae {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (U : BoundedContinuousFunction Torus ℝ) :
    fieldDensity hJ θ U =ᵐ[torusMeasure] fieldDensityValue hJ θ U :=
  (fieldDensityValue_memLp hJ θ U).coeFn_toLp

theorem fieldDensityValue_apply {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (U : BoundedContinuousFunction Torus ℝ) (x : Torus) :
    fieldDensityValue hJ θ U x = (J : ℝ) ^ 2 * θ (meshLabel J hJ x) *
      cellDensity hJ U (meshLabel J hJ x) x := by
  classical
  rw [fieldDensityValue, Finset.sum_eq_single (meshLabel J hJ x)]
  · rw [indicator_of_mem (show x ∈ meshCell J hJ (meshLabel J hJ x) from rfl)]
  · intro a _ ha
    rw [indicator_of_notMem (show x ∉ meshCell J hJ a from fun hx => ha hx.symm), mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem bounded_field_oscillation (U : BoundedContinuousFunction Torus ℝ) {M : ℝ}
    (hU : ‖U‖ ≤ M) (x y : Torus) : |U x - U y| ≤ 2 * M := by
  have hx : |U x| ≤ M := (U.norm_coe_le_norm x).trans hU
  have hy : |U y| ≤ M := (U.norm_coe_le_norm y).trans hU
  exact (abs_sub _ _).trans ((add_le_add hx hy).trans_eq (by ring))

theorem bounded_field_interpolation_oscillation
    (U V : BoundedContinuousFunction Torus ℝ) {M r : ℝ}
    (hU : ‖U‖ ≤ M) (hV : ‖V‖ ≤ M) (hr : r ∈ Icc (0 : ℝ) 1) (x y : Torus) :
    |(V x + r * (U x - V x)) - (V y + r * (U y - V y))| ≤ 2 * M := by
  have he : (V x + r * (U x - V x)) - (V y + r * (U y - V y)) =
      (1 - r) * (V x - V y) + r * (U x - U y) := by ring
  rw [he]
  calc
    _ ≤ |(1 - r) * (V x - V y)| + |r * (U x - U y)| := abs_add_le _ _
    _ = (1 - r) * |V x - V y| + r * |U x - U y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hr.1, abs_of_nonneg (sub_nonneg.mpr hr.2)]
    _ ≤ (1 - r) * (2 * M) + r * (2 * M) := add_le_add
      (mul_le_mul_of_nonneg_left (bounded_field_oscillation V hV x y) (sub_nonneg.mpr hr.2))
      (mul_le_mul_of_nonneg_left (bounded_field_oscillation U hU x y) hr.1)
    _ = _ := by ring

theorem cellDensity_uniform_difference {J : ℕ} (hJ : 0 < J)
    (U V : BoundedContinuousFunction Torus ℝ) {M : ℝ} (hU : ‖U‖ ≤ M) (hV : ‖V‖ ≤ M)
    (a : MeshIndex J) {x : Torus} (hx : x ∈ meshCell J hJ a) :
    |cellDensity hJ U a x - cellDensity hJ V a x| ≤ Real.exp (2 * M) * (2 * ‖U - V‖) := by
  have hh := cellDensity_interpolation_bound hJ a V.continuous (U.continuous.sub V.continuous)
    (show 0 ≤ 2 * ‖U - V‖ by positivity)
    (fun r hr y _ z _ => bounded_field_interpolation_oscillation U V hU hV hr y z)
    (fun y _ z _ => bounded_field_oscillation (U - V) le_rfl y z) hx
  change |cellDensity hJ (fun y => V y + (U y - V y)) a x - cellDensity hJ V a x| ≤ _ at hh
  have he : (fun y => V y + (U y - V y)) = (U : Torus → ℝ) := by funext y; ring
  rwa [he] at hh

theorem fieldDensityValue_difference {J : ℕ} (hJ : 0 < J) (θ ψ : MeshIndex J → ℝ)
    (U V : BoundedContinuousFunction Torus ℝ) {M : ℝ} (hU : ‖U‖ ≤ M) (hV : ‖V‖ ≤ M)
    (x : Torus) :
    |fieldDensityValue hJ θ U x - fieldDensityValue hJ ψ V x| ≤
      (J : ℝ) ^ 2 * Real.exp (2 * M) * (2 * ‖θ‖ * ‖U - V‖ + ‖θ - ψ‖) := by
  let a := meshLabel J hJ x
  have hx : x ∈ meshCell J hJ a := rfl
  have hB := (cellDensity_bounds hJ V.continuous a (fun y _ z _ => bounded_field_oscillation V hV y z) hx).2
  have hB0 := (cellDensity_pos hJ V.continuous a x).le
  have hdiff := cellDensity_uniform_difference hJ U V hU hV a hx
  have hθ : |θ a| ≤ ‖θ‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm θ a
  have hθψ : |θ a - ψ a| ≤ ‖θ - ψ‖ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (θ - ψ) a
  rw [fieldDensityValue_apply, fieldDensityValue_apply]
  change |(J : ℝ) ^ 2 * θ a * cellDensity hJ U a x - (J : ℝ) ^ 2 * ψ a * cellDensity hJ V a x| ≤ _
  have he : (J : ℝ) ^ 2 * θ a * cellDensity hJ U a x - (J : ℝ) ^ 2 * ψ a * cellDensity hJ V a x =
      (J : ℝ) ^ 2 * (θ a * (cellDensity hJ U a x - cellDensity hJ V a x) +
        (θ a - ψ a) * cellDensity hJ V a x) := by ring
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg _)]
  apply (mul_le_mul_of_nonneg_left (abs_add_le _ _) (sq_nonneg _)).trans
  have h1 : |θ a * (cellDensity hJ U a x - cellDensity hJ V a x)| ≤
      ‖θ‖ * (Real.exp (2 * M) * (2 * ‖U - V‖)) := by
    rw [abs_mul]
    exact mul_le_mul hθ hdiff (abs_nonneg _) (norm_nonneg _)
  have h2 : |(θ a - ψ a) * cellDensity hJ V a x| ≤ ‖θ - ψ‖ * Real.exp (2 * M) := by
    rw [abs_mul, abs_of_nonneg hB0]
    exact mul_le_mul hθψ hB hB0 (norm_nonneg _)
  exact (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (sq_nonneg _)).trans_eq (by ring)

theorem fieldDensity_norm_difference {J : ℕ} (hJ : 0 < J) (θ ψ : MeshIndex J → ℝ)
    (U V : BoundedContinuousFunction Torus ℝ) {M : ℝ} (hU : ‖U‖ ≤ M) (hV : ‖V‖ ≤ M) :
    ‖fieldDensity hJ θ U - fieldDensity hJ ψ V‖ ≤
      (J : ℝ) ^ 2 * Real.exp (2 * M) * (2 * ‖θ‖ * ‖U - V‖ + ‖θ - ψ‖) := by
  apply L4_norm_le_of_ae_bound _ (by positivity)
  filter_upwards [Lp.coeFn_sub (fieldDensity hJ θ U) (fieldDensity hJ ψ V),
    fieldDensity_ae hJ θ U, fieldDensity_ae hJ ψ V] with x hs hx hy
  rw [hs, Pi.sub_apply, hx, hy]
  exact fieldDensityValue_difference hJ θ ψ U V hU hV x

theorem continuous_fieldDensity {J : ℕ} (hJ : 0 < J) :
    Continuous (fun p : (MeshIndex J → ℝ) × BoundedContinuousFunction Torus ℝ =>
      fieldDensity hJ p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let B := fun q : (MeshIndex J → ℝ) × BoundedContinuousFunction Torus ℝ =>
    (J : ℝ) ^ 2 * Real.exp (2 * max ‖q.2‖ ‖p.2‖) *
      (2 * ‖q.1‖ * ‖q.2 - p.2‖ + ‖q.1 - p.1‖)
  have hB : Continuous B := by unfold B; fun_prop
  have hB0 : Tendsto B (𝓝 p) (𝓝 0) := by
    simpa only [B, sub_self, norm_zero, mul_zero, add_zero] using hB.tendsto p
  exact squeeze_zero (fun q => norm_nonneg _)
    (fun q => fieldDensity_norm_difference hJ q.1 p.1 q.2 p.2
      (le_max_left _ _) (le_max_right _ _)) hB0

theorem fieldDensity_tendsto {J : ℕ} (hJ : 0 < J)
    {θn : ℕ → MeshIndex J → ℝ} {Un : ℕ → BoundedContinuousFunction Torus ℝ}
    {θ : MeshIndex J → ℝ} {U : BoundedContinuousFunction Torus ℝ}
    (hθ : Tendsto θn atTop (𝓝 θ)) (hU : Tendsto Un atTop (𝓝 U)) :
    Tendsto (fun k => fieldDensity hJ (θn k) (Un k)) atTop (𝓝 (fieldDensity hJ θ U)) := by
  have hp : Tendsto (fun k => (θn k, Un k)) atTop (𝓝 (θ, U)) := hθ.prodMk_nhds hU
  simpa only [Function.comp_apply] using! ((continuous_fieldDensity hJ).tendsto (θ, U)).comp hp

theorem fieldDensity_eq_occupationMap {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (β : ℝ) (f : L4) :
    fieldDensity hJ θ (β • potential f) = occupationMap hJ θ β f := by
  apply Lp.ext
  filter_upwards [fieldDensity_ae hJ θ (β • potential f), occupationMap_ae hJ θ β f] with x hx hy
  rw [hx, hy]
  rfl

/-- All cell masses of the limiting density are literal Haar-cell masses,
including cells with zero limiting occupation. -/
theorem fieldDensity_cell_mass {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (U : BoundedContinuousFunction Torus ℝ) (a : MeshIndex J) :
    (∫ x in meshCell J hJ a, fieldDensity hJ θ U x ∂torusMeasure) = θ a := by
  rw [integral_congr_ae (ae_restrict_of_ae (fieldDensity_ae hJ θ U))]
  have he : (∫ x in meshCell J hJ a, fieldDensityValue hJ θ U x ∂torusMeasure) =
      ∫ x in meshCell J hJ a, (J : ℝ) ^ 2 * θ a * cellDensity hJ U a x ∂torusMeasure := by
    apply setIntegral_congr_fun (measurableSet_meshCell J hJ a)
    intro x hx
    rw [fieldDensityValue_apply, show meshLabel J hJ x = a from hx]
  rw [he, integral_const_mul]
  have hm := cellDensity_haar_mass hJ U.continuous a
  rw [integral_indicator (measurableSet_meshCell J hJ a)] at hm
  nlinarith only [congrArg (fun r : ℝ => θ a * r) hm]

section ActualLimit
variable {J : ℕ} {β₀ t : ℝ} (hsub : β₀ < 4)
  (htC : t ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)

theorem sample_residual (s : Sample J β₀ t) (hlarge : 8 * β₀ ≤ (s.n + 1 : ℝ)) :
    ‖sampleDensity hsub htC hmesh s -
      fieldDensity (mesh_pos hmesh) s.profile (s.beta • potential (sampleDensity hsub htC hmesh s))‖ ≤
      OccupationFieldApproximation.approximationConstant J β₀ / Real.sqrt (s.n + 1 : ℝ) := by
  rw [fieldDensity_eq_occupationMap]
  exact averageMarginalL4_map_residual_L4 s.two_le s.beta_nonneg s.beta_le hsub htC hmesh
    (labelOfState s.state).val s.cap (by simpa only [Nat.cast_add, Nat.cast_one] using hlarge)

theorem inverse_sqrt_tendsto_zero {ν : ℕ → ℝ} (hν : Tendsto ν atTop atTop) (C : ℝ) :
    Tendsto (fun k => C / Real.sqrt (ν k)) atTop (𝓝 0) := by
  have hh := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hν)
  simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using hh.const_mul C

/-- Uniform field convergence and the proved original marginal residual
force strong L4 convergence. The final equality identifies the limiting
field with the actual Green convolution, rather than a new kernel. -/
theorem strong_limit_of_parameters (s : ℕ → Sample J β₀ t)
    (hN : Tendsto (fun k => ((s k).n + 1 : ℝ)) atTop atTop)
    {β : ℝ} {θ : MeshIndex J → ℝ} {U : BoundedContinuousFunction Torus ℝ}
    (hβ : Tendsto (fun k => (s k).beta) atTop (𝓝 β))
    (hθ : Tendsto (fun k => (s k).profile) atTop (𝓝 θ))
    (hU : Tendsto (fun k => potential (sampleDensity hsub htC hmesh (s k))) atTop (𝓝 U)) :
    Tendsto (fun k => sampleDensity hsub htC hmesh (s k)) atTop
      (𝓝 (fieldDensity (mesh_pos hmesh) θ (β • U))) ∧
      U = potential (fieldDensity (mesh_pos hmesh) θ (β • U)) := by
  let d := fun k => sampleDensity hsub htC hmesh (s k)
  let F := fun k => fieldDensity (mesh_pos hmesh) (s k).profile ((s k).beta • potential (d k))
  let f := fieldDensity (mesh_pos hmesh) θ (β • U)
  have hs : Tendsto (fun k => (s k).beta • potential (d k)) atTop (𝓝 (β • U)) := by
    simpa only [Pi.smul_apply] using! hβ.smul hU
  have hF : Tendsto F atTop (𝓝 f) := fieldDensity_tendsto (mesh_pos hmesh) hθ hs
  have hl : ∀ᶠ k in atTop, 8 * β₀ ≤ ((s k).n + 1 : ℝ) :=
    hN.eventually (eventually_ge_atTop _)
  have hres : Tendsto (fun k => ‖d k - F k‖) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      (hl.mono fun k hk => sample_residual hsub htC hmesh (s k) hk)
      (inverse_sqrt_tendsto_zero hN (OccupationFieldApproximation.approximationConstant J β₀))
  have hf : Tendsto d atTop (𝓝 f) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
      (by simpa only [add_zero] using hres.add (tendsto_iff_norm_sub_tendsto_zero.mp hF))
    calc
      ‖d k - f‖ = ‖(d k - F k) + (F k - f)‖ := by congr 1; abel
      _ ≤ ‖d k - F k‖ + ‖F k - f‖ := norm_add_le _ _
  exact ⟨hf, tendsto_nhds_unique hU ((continuous_potential.tendsto f).comp hf)⟩

/-- Actual strong compactness and self-consistency for any particle numbers
tending to infinity. Neither the residual nor a limiting fixed-point
equation is a hypothesis. The cap may contain empty cells. -/
theorem exists_strong_sample_subsequence (s : ℕ → Sample J β₀ t)
    (hN : Tendsto (fun k => ((s k).n + 1 : ℝ)) atTop atTop) :
    ∃ (β : ℝ) (θ : MeshIndex J → ℝ) (f : L4) (r : ℕ → ℕ),
      StrictMono r ∧ β ∈ Icc 0 β₀ ∧ θ ∈ Icc 0 1 ∧
      (∑ a, θ a = 1) ∧ 0 ≤ f ∧ (∫ x, f x ∂torusMeasure) = 1 ∧
      Tendsto (fun k => (s (r k)).beta) atTop (𝓝 β) ∧
      Tendsto (fun k => (s (r k)).profile) atTop (𝓝 θ) ∧
      Tendsto (fun k => sampleDensity hsub htC hmesh (s (r k))) atTop (𝓝 f) ∧
      Tendsto (fun k => potential (sampleDensity hsub htC hmesh (s (r k)))) atTop (𝓝 (potential f)) ∧
      f = occupationMap (mesh_pos hmesh) θ β f ∧
      (∀ a, (∫ x in meshCell J (mesh_pos hmesh) a, f x ∂torusMeasure) = θ a) := by
  obtain ⟨β, θ, U, r, hr, hβ, hθ, hβlim, hθlim, hUlim⟩ :=
    exists_sample_subsequence hsub htC hmesh s
  let f := fieldDensity (mesh_pos hmesh) θ (β • U)
  obtain ⟨hf, hUf⟩ := strong_limit_of_parameters hsub htC hmesh (s ∘ r)
    (hN.comp hr.tendsto_atTop) hβlim hθlim hUlim
  have hθmass : ∑ a, θ a = 1 :=
    (isClosed_eq (by fun_prop : Continuous (fun ψ : MeshIndex J → ℝ => ∑ a, ψ a))
      continuous_const).mem_of_tendsto hθlim
        (Eventually.of_forall (fun k => (s (r k)).profile_mass))
  have hcone : IsClosed ({g : L4 | 0 ≤ g} : Set L4) := isClosed_Ici
  have hf0 : 0 ≤ f := hcone.mem_of_tendsto hf
    (Eventually.of_forall (fun k => sampleDensity_nonneg hsub htC hmesh (s (r k))))
  have hfmass : (∫ x, f x ∂torusMeasure) = 1 :=
    (isClosed_eq integral_lipschitz.continuous continuous_const).mem_of_tendsto hf
      (Eventually.of_forall (fun k => sampleDensity_mass hsub htC hmesh (s (r k))))
  refine ⟨β, θ, f, r, hr, hβ, hθ, hθmass, hf0, hfmass, hβlim, hθlim, hf, ?_, ?_, ?_⟩
  · have he : U = potential f := hUf
    rw [← he]
    exact hUlim
  · calc
      f = fieldDensity (mesh_pos hmesh) θ (β • potential f) := by
        change fieldDensity (mesh_pos hmesh) θ (β • U) = _
        rw [hUf]
      _ = occupationMap (mesh_pos hmesh) θ β f := fieldDensity_eq_occupationMap _ _ _ _
  · exact fieldDensity_cell_mass (mesh_pos hmesh) θ (β • U)

end ActualLimit

/-- Log odds formed from the literal Haar-cell exponential integrals. -/
def cellLogOdds {J : ℕ} (hJ : 0 < J) (U : BoundedContinuousFunction Torus ℝ)
    (a b : MeshIndex J) : ℝ := Real.log (cellIntegral hJ U b / cellIntegral hJ U a)

theorem cellLogOdds_eq_normalizer_logs {J : ℕ} (hJ : 0 < J)
    (U : BoundedContinuousFunction Torus ℝ) (a b : MeshIndex J) :
    cellLogOdds hJ U a b = Real.log (OccupationNearContraction.cellNormalizer hJ U b) -
      Real.log (OccupationNearContraction.cellNormalizer hJ U a) := by
  rw [cellLogOdds, ← cellNormalizer_ratio_eq_haar hJ U.continuous,
    Real.log_div (cellNormalizer_pos hJ U.continuous b).ne' (cellNormalizer_pos hJ U.continuous a).ne']

theorem cellLogOdds_lipschitz {J : ℕ} (hJ : 0 < J) (a b : MeshIndex J) :
    LipschitzWith 2 (fun U : BoundedContinuousFunction Torus ℝ => cellLogOdds hJ U a b) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro U V
  have hb : ∀ x, |U x - V x| ≤ ‖U - V‖ := fun x => (U - V).norm_coe_le_norm x
  have ha := cellNormalizer_log_difference hJ U.continuous V.continuous hb a
  have hb' := cellNormalizer_log_difference hJ U.continuous V.continuous hb b
  simp only [Real.norm_eq_abs, NNReal.coe_ofNat, cellLogOdds_eq_normalizer_logs]
  calc
    _ = |(Real.log (OccupationNearContraction.cellNormalizer hJ U b) -
        Real.log (OccupationNearContraction.cellNormalizer hJ V b)) -
      (Real.log (OccupationNearContraction.cellNormalizer hJ U a) -
        Real.log (OccupationNearContraction.cellNormalizer hJ V a))| := by congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans ((add_le_add hb' ha).trans_eq (by ring))

theorem sigmoid_cellLogOdds {J : ℕ} (hJ : 0 < J)
    (U : BoundedContinuousFunction Torus ℝ) (a b : MeshIndex J) :
    Real.sigmoid (cellLogOdds hJ U a b) = cellIntegral hJ U b /
      (cellIntegral hJ U a + cellIntegral hJ U b) := by
  rw [cellLogOdds, Real.log_div (cellIntegral_pos hJ U.continuous b).ne'
    (cellIntegral_pos hJ U.continuous a).ne',
    CrossingLogistic.sigmoid_log_sub (cellIntegral_pos hJ U.continuous b)
      (cellIntegral_pos hJ U.continuous a)]
  rw [add_comm]

/-- Normalization by the original particle count; this is the existing
outer-graph rate, not an auxiliary limiting chain. -/
def normalizedRate {J : ℕ} {β₀ t : ℝ} (hJ : 0 < J) (s : Sample J β₀ t)
    (hm : s.state.val ∈ cappedOccupations J (s.n + 1) (3 * t / 4))
    (hmargin : 4 ≤ t * (s.n + 1 : ℕ)) (a b : MeshIndex J) : ℝ :=
  directionRate hJ s.beta s.state hm hmargin a b / (s.n + 1 : ℝ)

theorem normalizedRate_eq_logistic {J : ℕ} {β₀ t : ℝ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (hsub : β₀ < 4) (s : Sample J β₀ t)
    (hm : s.state.val ∈ cappedOccupations J (s.n + 1) (3 * t / 4))
    (hmargin : 4 ≤ t * (s.n + 1 : ℕ)) (a b : MeshIndex J)
    (hab : EdgeAdjacent J hJ a b) (ha : 1 ≤ s.state.val a) :
    normalizedRate hJ s hm hmargin a b = s.profile a *
      Real.sigmoid (Real.log (qWeight hJ s.beta (movedState s.state hm hmargin a b ha) /
        qWeight hJ s.beta s.state)) := by
  have hp : PermittedMove hJ s.state (movedState s.state hm hmargin a b ha) a b := ⟨hab, ha, rfl⟩
  have hq := qWeight_pos hJ s.two_le s.beta_nonneg (s.beta_le.trans_lt hsub) s.state
  have hq' := qWeight_pos hJ s.two_le s.beta_nonneg (s.beta_le.trans_lt hsub)
    (movedState s.state hm hmargin a b ha)
  rw [normalizedRate, directionRate, dite_eq_left ha, occupationRate_of_move hJ hJ2 s.beta hp,
    Real.log_div hq'.ne' hq.ne', CrossingLogistic.sigmoid_log_sub hq' hq, Sample.profile_apply]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [add_comm (qWeight hJ s.beta (movedState s.state hm hmargin a b ha))]
  ring

section ActualRates
variable {J : ℕ} {β₀ t : ℝ} (hsub : β₀ < 4)
  (htC : t ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)

theorem sample_field_apply (s : Sample J β₀ t) (x : Torus) :
    (s.beta • potential (sampleDensity hsub htC hmesh s)) x =
      s.beta * OccupationFieldL2.meanPotential (mesh_pos hmesh) (labelOfState s.state).val s.beta x := by
  change s.beta * potential (sampleDensity hsub htC hmesh s) x = _
  rw [sample_potential_eq_original]

theorem sample_Q_log_ratio (s : Sample J β₀ t)
    (hlarge : OccupationPartitionTransport.ratioThreshold J β₀ ≤ s.n + 1)
    {m' : OccupationState J (s.n + 1) t} {a b : MeshIndex J}
    (hm : PermittedMove (mesh_pos hmesh) s.state m' a b) :
    |Real.log (qWeight (mesh_pos hmesh) s.beta m' / qWeight (mesh_pos hmesh) s.beta s.state) -
      cellLogOdds (mesh_pos hmesh) (s.beta • potential (sampleDensity hsub htC hmesh s)) a b| ≤
      OccupationPartitionTransport.logarithmicRatioConstant J β₀ / Real.sqrt (s.n + 1 : ℝ) := by
  have hocc : occupation (labelOfState s.state).val = s.state.val :=
    congrArg Subtype.val (profile_labelOfState s.state)
  have ha : 1 ≤ occupation (labelOfState s.state).val a := by rw [hocc]; exact hm.2.1
  have hh := OccupationPartitionTransport.occupation_Q_log_ratio_cells hlarge
    s.beta_nonneg s.beta_le hsub htC hmesh (labelOfState s.state).val s.cap a b ha
  rw [hocc, hm.2.2] at hh
  simpa only [qWeight, cellLogOdds, cellIntegral, sample_field_apply] using! hh

/-- A uniform approximation of every original normalized direction rate.
The zero source count is handled by its exact zero branch, so no positivity
of the limiting cell masses is required. -/
theorem normalizedRate_error (s : Sample J β₀ t)
    (hm : s.state.val ∈ cappedOccupations J (s.n + 1) (3 * t / 4))
    (hmargin : 4 ≤ t * (s.n + 1 : ℕ))
    (hlarge : OccupationPartitionTransport.ratioThreshold J β₀ ≤ s.n + 1)
    (a b : MeshIndex J) (hab : EdgeAdjacent J (mesh_pos hmesh) a b) :
    |normalizedRate (mesh_pos hmesh) s hm hmargin a b - s.profile a *
      Real.sigmoid (cellLogOdds (mesh_pos hmesh)
        (s.beta • potential (sampleDensity hsub htC hmesh s)) a b)| ≤
      (OccupationPartitionTransport.logarithmicRatioConstant J β₀ / 4) / Real.sqrt (s.n + 1 : ℝ) := by
  by_cases ha : 1 ≤ s.state.val a
  · have hp : PermittedMove (mesh_pos hmesh) s.state (movedState s.state hm hmargin a b ha) a b :=
      ⟨hab, ha, rfl⟩
    have hq := sample_Q_log_ratio hsub htC hmesh s hlarge hp
    have hh := (logistic_probability_difference
      (Real.log (qWeight (mesh_pos hmesh) s.beta (movedState s.state hm hmargin a b ha) /
        qWeight (mesh_pos hmesh) s.beta s.state))
      (cellLogOdds (mesh_pos hmesh) (s.beta • potential (sampleDensity hsub htC hmesh s)) a b)).trans
        (mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 1 / 4))
    rw [normalizedRate_eq_logistic (mesh_pos hmesh) (mesh_two_le hmesh) hsub s hm hmargin a b hab ha,
      ← mul_sub, abs_mul, abs_of_nonneg (s.profile_nonneg a)]
    exact (mul_le_mul (s.profile_le_one a) hh (abs_nonneg _) zero_le_one).trans_eq (by ring)
  · have hz : s.state.val a = 0 := by omega
    have hC := OccupationPartitionTransport.logarithmicRatioConstant_nonneg J
      (s.beta_nonneg.trans s.beta_le)
    have hr : normalizedRate (mesh_pos hmesh) s hm hmargin a b = 0 := by
      rw [normalizedRate, directionRate, dite_eq_right ha, zero_div]
    have hp : s.profile a = 0 := by rw [Sample.profile_apply, hz, Nat.cast_zero, zero_div]
    rw [hr, hp, zero_mul, sub_zero, abs_zero]
    exact div_nonneg (div_nonneg hC (by norm_num : (0 : ℝ) ≤ 4)) (Real.sqrt_nonneg (s.n + 1 : ℝ))

/-- The genuine rate limit holds even when either limiting occupation is
zero. The fixed-point equation is not needed to obtain this limit. -/
theorem normalizedRate_tendsto (s : ℕ → Sample J β₀ t)
    (hm : ∀ k, (s k).state.val ∈ cappedOccupations J ((s k).n + 1) (3 * t / 4))
    (hmargin : ∀ k, 4 ≤ t * ((s k).n + 1 : ℕ))
    (hN : Tendsto (fun k => ((s k).n + 1 : ℝ)) atTop atTop)
    {β : ℝ} {θ : MeshIndex J → ℝ} {U : BoundedContinuousFunction Torus ℝ}
    (hβ : Tendsto (fun k => (s k).beta) atTop (𝓝 β))
    (hθ : Tendsto (fun k => (s k).profile) atTop (𝓝 θ))
    (hU : Tendsto (fun k => potential (sampleDensity hsub htC hmesh (s k))) atTop (𝓝 U))
    (a b : MeshIndex J) (hab : EdgeAdjacent J (mesh_pos hmesh) a b) :
    Tendsto (fun k => normalizedRate (mesh_pos hmesh) (s k) (hm k) (hmargin k) a b) atTop
      (𝓝 (θ a * cellIntegral (mesh_pos hmesh) (β • U) b /
        (cellIntegral (mesh_pos hmesh) (β • U) a + cellIntegral (mesh_pos hmesh) (β • U) b))) := by
  let u := fun k => (s k).beta • potential (sampleDensity hsub htC hmesh (s k))
  have hu : Tendsto u atTop (𝓝 (β • U)) := by
    simpa only [Pi.smul_apply] using! hβ.smul hU
  have ho : Tendsto (fun k => cellLogOdds (mesh_pos hmesh) (u k) a b) atTop
      (𝓝 (cellLogOdds (mesh_pos hmesh) (β • U) a b)) :=
    ((cellLogOdds_lipschitz (mesh_pos hmesh) a b).continuous.tendsto (β • U)).comp hu
  have hsig := (CrossingLogistic.sigmoid_lipschitz.continuous.tendsto
    (cellLogOdds (mesh_pos hmesh) (β • U) a b)).comp ho
  have hθa : Tendsto (fun k => (s k).profile a) atTop (𝓝 (θ a)) :=
    (continuous_apply a).tendsto θ |>.comp hθ
  let R := θ a * Real.sigmoid (cellLogOdds (mesh_pos hmesh) (β • U) a b)
  let r := fun k => normalizedRate (mesh_pos hmesh) (s k) (hm k) (hmargin k) a b
  let z := fun k => (s k).profile a * Real.sigmoid (cellLogOdds (mesh_pos hmesh) (u k) a b)
  have hz : Tendsto z atTop (𝓝 R) := by
    simpa only [Function.comp_apply] using hθa.mul hsig
  have hl : ∀ᶠ k in atTop, OccupationPartitionTransport.ratioThreshold J β₀ ≤ (s k).n + 1 := by
    filter_upwards [hN.eventually_ge_atTop (OccupationPartitionTransport.ratioThreshold J β₀ : ℝ)] with k hk
    exact_mod_cast hk
  have he : Tendsto (fun k => ‖r k - z k‖) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      (hl.mono fun k hk => by
        simpa only [Real.norm_eq_abs] using normalizedRate_error hsub htC hmesh (s k)
          (hm k) (hmargin k) hk a b hab)
      (inverse_sqrt_tendsto_zero hN (OccupationPartitionTransport.logarithmicRatioConstant J β₀ / 4))
  have hr : Tendsto r atTop (𝓝 R) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
      (by simpa only [add_zero] using he.add (tendsto_iff_norm_sub_tendsto_zero.mp hz))
    calc
      ‖r k - R‖ = ‖(r k - z k) + (z k - R)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hcoe : (β • (U : Torus → ℝ)) = (fun x => β • U x) := rfl
  simpa only [R, r, sigmoid_cellLogOdds, mul_div_assoc, BoundedContinuousFunction.coe_smul, hcoe] using hr

end ActualRates

/-- The source's normalized square-root expression, using the literal
Haar-cell exponential integrals on each original unordered cell edge. -/
def limitingImbalance {J : ℕ} (hJ : 0 < J) (θ : MeshIndex J → ℝ)
    (U : BoundedContinuousFunction Torus ℝ) : ℝ :=
  unorderedSum hJ (fun a b =>
    (Real.sqrt (θ a * cellIntegral hJ U b) - Real.sqrt (θ b * cellIntegral hJ U a)) ^ 2 /
      (cellIntegral hJ U a + cellIntegral hJ U b))

theorem sqrt_rate_difference_identity {A B D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    (Real.sqrt (A / D) - Real.sqrt (B / D)) ^ 2 =
      (Real.sqrt A - Real.sqrt B) ^ 2 / D := by
  rw [Real.sqrt_div hA, Real.sqrt_div hB, ← sub_div, div_pow, Real.sq_sqrt hD]

theorem sample_directionRate_nonneg {J : ℕ} {β₀ t : ℝ} (hJ : 0 < J) (s : Sample J β₀ t)
    (hm : s.state.val ∈ cappedOccupations J (s.n + 1) (3 * t / 4))
    (hmargin : 4 ≤ t * (s.n + 1 : ℕ)) (a b : MeshIndex J) :
    0 ≤ directionRate hJ s.beta s.state hm hmargin a b := by
  unfold directionRate
  split_ifs
  · exact occupationRate_nonneg _ _ _ _
  · exact le_rfl

theorem normalized_imbalance_identity {J : ℕ} {β₀ t : ℝ} (hJ : 0 < J) (s : Sample J β₀ t)
    (hm : s.state.val ∈ cappedOccupations J (s.n + 1) (3 * t / 4))
    (hmargin : 4 ≤ t * (s.n + 1 : ℕ)) :
    imbalance hJ s.beta s.state hm hmargin / (s.n + 1 : ℝ) =
      unorderedSum hJ (fun a b =>
        (Real.sqrt (normalizedRate hJ s hm hmargin a b) -
          Real.sqrt (normalizedRate hJ s hm hmargin b a)) ^ 2) := by
  classical
  unfold imbalance unorderedSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  by_cases he : cellRank a < cellRank b ∧ EdgeAdjacent J hJ a b
  · simp only [ite_eq_left he, normalizedRate]
    exact (sqrt_rate_difference_identity
      (sample_directionRate_nonneg hJ s hm hmargin a b)
      (sample_directionRate_nonneg hJ s hm hmargin b a)
      (by positivity : (0 : ℝ) ≤ s.n + 1)).symm
  · simp only [ite_eq_right he, zero_div]

theorem normalized_imbalance_tendsto {J : ℕ} {β₀ t : ℝ} (hsub : β₀ < 4)
    (htC : t ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (s : ℕ → Sample J β₀ t)
    (hm : ∀ k, (s k).state.val ∈ cappedOccupations J ((s k).n + 1) (3 * t / 4))
    (hmargin : ∀ k, 4 ≤ t * ((s k).n + 1 : ℕ))
    (hN : Tendsto (fun k => ((s k).n + 1 : ℝ)) atTop atTop)
    {β : ℝ} {θ : MeshIndex J → ℝ} {U : BoundedContinuousFunction Torus ℝ}
    (hβ : Tendsto (fun k => (s k).beta) atTop (𝓝 β))
    (hθ : Tendsto (fun k => (s k).profile) atTop (𝓝 θ))
    (hU : Tendsto (fun k => potential (sampleDensity hsub htC hmesh (s k))) atTop (𝓝 U)) :
    Tendsto (fun k => imbalance (mesh_pos hmesh) (s k).beta (s k).state (hm k) (hmargin k) /
      ((s k).n + 1 : ℝ)) atTop (𝓝 (limitingImbalance (mesh_pos hmesh) θ (β • U))) := by
  classical
  have hcone : IsClosed ({ψ : MeshIndex J → ℝ | 0 ≤ ψ} : Set (MeshIndex J → ℝ)) := isClosed_Ici
  have hθ0 : 0 ≤ θ := hcone.mem_of_tendsto hθ
    (Eventually.of_forall (fun k => (s k).profile_nonneg))
  simp_rw [normalized_imbalance_identity]
  unfold limitingImbalance unorderedSum
  apply tendsto_finsetSum Finset.univ
  intro a _
  apply tendsto_finsetSum Finset.univ
  intro b _
  by_cases he : cellRank a < cellRank b ∧ EdgeAdjacent J (mesh_pos hmesh) a b
  · simp only [ite_eq_left he]
    have ha := normalizedRate_tendsto hsub htC hmesh s hm hmargin hN hβ hθ hU a b he.2
    have hb := normalizedRate_tendsto hsub htC hmesh s hm hmargin hN hβ hθ hU b a he.2.symm
    have hh := ((Real.continuous_sqrt.tendsto _).comp ha).sub
      ((Real.continuous_sqrt.tendsto _).comp hb)
    have hh' := hh.pow 2
    have hcoe : (β • (U : Torus → ℝ)) = (fun x => β • U x) := rfl
    have hid := sqrt_rate_difference_identity
      (mul_nonneg (hθ0 a) (cellIntegral_pos (mesh_pos hmesh) (β • U).continuous b).le)
      (mul_nonneg (hθ0 b) (cellIntegral_pos (mesh_pos hmesh) (β • U).continuous a).le)
      (add_nonneg
        (cellIntegral_pos (mesh_pos hmesh) (β • U).continuous a).le
        (cellIntegral_pos (mesh_pos hmesh) (β • U).continuous b).le)
    rw [add_comm (cellIntegral (mesh_pos hmesh) (β • U) b)] at hh'
    simp only [BoundedContinuousFunction.coe_smul] at hid
    simp only [hcoe] at hh'
    rw [hid] at hh'
    simpa only [Function.comp_apply, BoundedContinuousFunction.coe_smul] using hh'
  · simp only [ite_eq_right he]
    exact tendsto_const_nhds

theorem unordered_term_le {J : ℕ} (hJ : 0 < J) (F : MeshIndex J → MeshIndex J → ℝ)
    (hF : ∀ a b, 0 ≤ F a b) {a b : MeshIndex J}
    (hab : cellRank a < cellRank b ∧ EdgeAdjacent J hJ a b) : F a b ≤ unorderedSum hJ F := by
  classical
  have hp (c d : MeshIndex J) : 0 ≤
      if cellRank c < cellRank d ∧ EdgeAdjacent J hJ c d then F c d else 0 := by
    split_ifs
    · exact hF c d
    · exact le_rfl
  calc
    F a b = if cellRank a < cellRank b ∧ EdgeAdjacent J hJ a b then F a b else 0 := by rw [ite_eq_left hab]
    _ ≤ ∑ d, if cellRank a < cellRank d ∧ EdgeAdjacent J hJ a d then F a d else 0 :=
      Finset.single_le_sum (fun d _ => hp a d) (Finset.mem_univ b)
    _ ≤ unorderedSum hJ F := Finset.single_le_sum
      (fun c _ => Finset.sum_nonneg (fun d _ => hp c d)) (Finset.mem_univ a)

/-- A zero literal unordered limit forces equality of every adjacent
chemical ratio, without assuming either occupation is positive. -/
theorem adjacent_ratios_of_limitingImbalance_zero {J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    {θ : MeshIndex J → ℝ} (hθ : ∀ a, 0 ≤ θ a) (U : BoundedContinuousFunction Torus ℝ)
    (hz : limitingImbalance hJ θ U = 0) {a b : MeshIndex J} (hab : EdgeAdjacent J hJ a b) :
    θ a / cellIntegral hJ U a = θ b / cellIntegral hJ U b := by
  have hI (c : MeshIndex J) : 0 < cellIntegral hJ U c := cellIntegral_pos hJ U.continuous c
  have hord (c d : MeshIndex J) (hr : cellRank c < cellRank d) (he : EdgeAdjacent J hJ c d) :
      θ c / cellIntegral hJ U c = θ d / cellIntegral hJ U d := by
    have hn (i j : MeshIndex J) : 0 ≤
        (Real.sqrt (θ i * cellIntegral hJ U j) - Real.sqrt (θ j * cellIntegral hJ U i)) ^ 2 /
          (cellIntegral hJ U i + cellIntegral hJ U j) :=
      div_nonneg (sq_nonneg _) (add_nonneg (hI i).le (hI j).le)
    have ht := unordered_term_le hJ _ hn ⟨hr, he⟩
    change _ ≤ limitingImbalance hJ θ U at ht
    rw [hz] at ht
    have heq := le_antisymm ht (hn c d)
    have hnum := congrArg (fun r : ℝ => r * (cellIntegral hJ U c + cellIntegral hJ U d)) heq
    rw [div_mul_cancel₀ _ (add_pos (hI c) (hI d)).ne', zero_mul] at hnum
    have hs : Real.sqrt (θ c * cellIntegral hJ U d) = Real.sqrt (θ d * cellIntegral hJ U c) :=
      sub_eq_zero.mp (sq_eq_zero_iff.mp hnum)
    have hs2 := congrArg (fun r : ℝ => r ^ 2) hs
    rw [Real.sq_sqrt (mul_nonneg (hθ c) (hI d).le), Real.sq_sqrt (mul_nonneg (hθ d) (hI c).le)] at hs2
    exact (div_eq_div_iff (hI c).ne' (hI d).ne').mpr hs2
  rcases lt_trichotomy (cellRank a) (cellRank b) with hr | hr | hr
  · exact hord a b hr hab
  · have he : a = b := (Fintype.equivFin (MeshIndex J)).injective hr
    exact False.elim ((hab.ne hJ2) he)
  · exact (hord b a hr hab.symm).symm

/-- Connectivity is supplied by the constructed shortest paths in the
actual periodic cell graph. It is not an input to the final limit theorem. -/
theorem all_ratios_of_limitingImbalance_zero {J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    {θ : MeshIndex J → ℝ} (hθ : ∀ a, 0 ≤ θ a) (U : BoundedContinuousFunction Torus ℝ)
    (hz : limitingImbalance hJ θ U = 0) (a b : MeshIndex J) :
    θ a / cellIntegral hJ U a = θ b / cellIntegral hJ U b := by
  have hwalk {c d : MeshIndex J} (p : (PermutationPathComparison.cellGraph hJ hJ2).Walk c d) :
      θ c / cellIntegral hJ U c = θ d / cellIntegral hJ U d := by
    induction p with
    | nil => rfl
    | cons he p ih => exact (adjacent_ratios_of_limitingImbalance_zero hJ hJ2 hθ U hz he).trans ih
  exact hwalk (PermutationPathComparison.cellPath hJ hJ2 a b)

theorem sum_cellIntegral {J : ℕ} (hJ : 0 < J) (U : BoundedContinuousFunction Torus ℝ) :
    (∑ a, cellIntegral hJ U a) = ∫ x, Real.exp (U x) ∂torusMeasure :=
  OccupationChemicalCoercivity.sum_cell_integrals hJ
    (integrable_continuous_torus torusMeasure (Real.continuous_exp.comp U.continuous))

theorem global_normalizer_pos {J : ℕ} (hJ : 0 < J) (U : BoundedContinuousFunction Torus ℝ) :
    0 < ∫ x, Real.exp (U x) ∂torusMeasure := by
  rw [← sum_cellIntegral hJ U]
  exact (cellIntegral_pos hJ U.continuous (meshLabel J hJ 0)).trans_le
    (Finset.single_le_sum (fun a _ => (cellIntegral_pos hJ U.continuous a).le)
      (Finset.mem_univ _))

theorem equal_ratios_value {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ}
    (hθ : ∑ a, θ a = 1) (U : BoundedContinuousFunction Torus ℝ)
    (hrel : ∀ a b, θ a / cellIntegral hJ U a = θ b / cellIntegral hJ U b) (a : MeshIndex J) :
    θ a / cellIntegral hJ U a = 1 / (∫ x, Real.exp (U x) ∂torusMeasure) := by
  have hrow (b : MeshIndex J) : θ b =
      (θ a / cellIntegral hJ U a) * cellIntegral hJ U b :=
    (div_eq_iff (cellIntegral_pos hJ U.continuous b).ne').mp (hrel b a)
  have hs : (θ a / cellIntegral hJ U a) * (∫ x, Real.exp (U x) ∂torusMeasure) = 1 := by
    rw [← sum_cellIntegral hJ U, Finset.mul_sum]
    simpa only [← hrow] using hθ
  exact (eq_div_iff (global_normalizer_pos hJ U).ne').mpr hs

theorem fieldDensityValue_global {J : ℕ} (hJ : 0 < J) {θ : MeshIndex J → ℝ}
    (hθ : ∑ a, θ a = 1) (U : BoundedContinuousFunction Torus ℝ)
    (hrel : ∀ a b, θ a / cellIntegral hJ U a = θ b / cellIntegral hJ U b) (x : Torus) :
    fieldDensityValue hJ θ U x = Real.exp (U x) / (∫ y, Real.exp (U y) ∂torusMeasure) := by
  rw [fieldDensityValue_apply]
  let a := meshLabel J hJ x
  change (J : ℝ) ^ 2 * θ a * cellDensity hJ U a x = _
  calc
    _ = θ a * ((J : ℝ) ^ 2 * cellDensity hJ U a x) := by ring
    _ = θ a * (Real.exp (U x) / cellIntegral hJ U a) := by rw [cellDensity_haar hJ U.continuous]
    _ = (θ a / cellIntegral hJ U a) * Real.exp (U x) := by ring
    _ = _ := by rw [equal_ratios_value hJ hθ U hrel]; ring

theorem potential_eq_original (f : L4) (x : Torus) :
    potential f x = ∫ y, greenRealRepresentative (x - y) * f y ∂torusMeasure :=
  densityPotential_eq_original (Lp.memLp f) x

/-- The vanishing original edge imbalance turns the actual cell fixed
point into the global original-Green fixed-point equation. This is the
last step before the separate stationary-uniqueness theorem. -/
theorem original_global_fixedPoint {J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    {θ : MeshIndex J → ℝ} (hθ0 : ∀ a, 0 ≤ θ a) (hθ1 : ∑ a, θ a = 1)
    (β : ℝ) (f : L4) (hfix : f = occupationMap hJ θ β f)
    (hz : limitingImbalance hJ θ (β • potential f) = 0) :
    f =ᵐ[torusMeasure] fun x =>
      Real.exp (β * ∫ y, greenRealRepresentative (x - y) * f y ∂torusMeasure) /
        (∫ z, Real.exp (β * ∫ y, greenRealRepresentative (z - y) * f y ∂torusMeasure) ∂torusMeasure) := by
  let U := β • potential f
  have hr := all_ratios_of_limitingImbalance_zero hJ hJ2 hθ0 U hz
  have he : f = fieldDensity hJ θ U := hfix.trans (fieldDensity_eq_occupationMap hJ θ β f).symm
  have hfEq : (f : Torus → ℝ) =ᵐ[torusMeasure] (fieldDensity hJ θ U : Torus → ℝ) :=
    Eventually.of_forall (fun x => congrArg (fun g : L4 => g x) he)
  have hrep : f =ᵐ[torusMeasure] fieldDensityValue hJ θ U :=
    hfEq.trans (fieldDensity_ae hJ θ U)
  have hp (x : Torus) : U x = β * ∫ y, greenRealRepresentative (x - y) * f y ∂torusMeasure := by
    change β * potential f x = _
    rw [potential_eq_original]
  filter_upwards [hrep] with x hx
  rw [hx]
  simpa only [hp] using fieldDensityValue_global hJ hθ1 U hr x

/-- Complete compactness mechanism for the actual original occupations.
The only vanishing hypothesis concerns their literal normalized imbalance;
all marginal, potential, rate and fixed-point limits are derived. -/
theorem exists_original_global_limit {J : ℕ} {β₀ t : ℝ} (hsub : β₀ < 4)
    (htC : t ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (s : ℕ → Sample J β₀ t)
    (hm : ∀ k, (s k).state.val ∈ cappedOccupations J ((s k).n + 1) (3 * t / 4))
    (hmargin : ∀ k, 4 ≤ t * ((s k).n + 1 : ℕ))
    (hN : Tendsto (fun k => ((s k).n + 1 : ℝ)) atTop atTop)
    (hD : Tendsto (fun k => imbalance (mesh_pos hmesh) (s k).beta (s k).state (hm k) (hmargin k) /
      ((s k).n + 1 : ℝ)) atTop (𝓝 0)) :
    ∃ (β : ℝ) (θ : MeshIndex J → ℝ) (f : L4) (r : ℕ → ℕ),
      StrictMono r ∧ β ∈ Icc 0 β₀ ∧ θ ∈ Icc 0 1 ∧
      (∑ a, θ a = 1) ∧ 0 ≤ f ∧ (∫ x, f x ∂torusMeasure) = 1 ∧
      Tendsto (fun k => (s (r k)).beta) atTop (𝓝 β) ∧
      Tendsto (fun k => (s (r k)).profile) atTop (𝓝 θ) ∧
      Tendsto (fun k => sampleDensity hsub htC hmesh (s (r k))) atTop (𝓝 f) ∧
      Tendsto (fun k => potential (sampleDensity hsub htC hmesh (s (r k)))) atTop (𝓝 (potential f)) ∧
      (∀ a, (∫ x in meshCell J (mesh_pos hmesh) a, f x ∂torusMeasure) = θ a) ∧
      (f =ᵐ[torusMeasure] fun x =>
        Real.exp (β * ∫ y, greenRealRepresentative (x - y) * f y ∂torusMeasure) /
          (∫ z, Real.exp (β * ∫ y, greenRealRepresentative (z - y) * f y ∂torusMeasure) ∂torusMeasure)) := by
  obtain ⟨β, θ, f, r, hr, hβ, hθ, hθmass, hf0, hfmass, hβlim, hθlim, hflim, hUlim, hfix, hcell⟩ :=
    exists_strong_sample_subsequence hsub htC hmesh s hN
  have hlim := normalized_imbalance_tendsto hsub htC hmesh (s ∘ r)
    (fun k => hm (r k)) (fun k => hmargin (r k)) (hN.comp hr.tendsto_atTop) hβlim hθlim hUlim
  have hzero : limitingImbalance (mesh_pos hmesh) θ (β • potential f) = 0 :=
    tendsto_nhds_unique hlim (hD.comp hr.tendsto_atTop)
  exact ⟨β, θ, f, r, hr, hβ, hθ, hθmass, hf0, hfmass, hβlim, hθlim, hflim, hUlim, hcell,
    original_global_fixedPoint (mesh_pos hmesh) (mesh_two_le hmesh) hθ.1 hθmass β f hfix hzero⟩

theorem original_global_fixedPoint_zero_eq_one {f : L4}
    (hf : f =ᵐ[torusMeasure] fun x =>
      Real.exp (0 * ∫ y, greenRealRepresentative (x - y) * f y ∂torusMeasure) /
        (∫ z, Real.exp (0 * ∫ y, greenRealRepresentative (z - y) * f y ∂torusMeasure) ∂torusMeasure)) :
    f = oneL4 := by
  apply Lp.ext
  have he : f =ᵐ[torusMeasure] fun _ => (1 : ℝ) := by
    simpa only [zero_mul, Real.exp_zero, integral_const, probReal_univ, one_smul, div_one] using hf
  exact he.trans oneL4_ae.symm

/-- Exact remaining obstruction in the source's far-region contradiction:
an actual far sequence of vanishing original imbalance produces a
nonuniform L4 probability fixed point for the original Green kernel.
Stationary uniqueness, and consequently unconditional far coercivity,
are not asserted by this theorem. -/
theorem nonuniform_original_global_fixedPoint_of_far_sequence
    {J : ℕ} {β₀ t ε : ℝ} (hsub : β₀ < 4)
    (htC : t ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J) (hε : 0 < ε)
    (s : ℕ → Sample J β₀ t)
    (hm : ∀ k, (s k).state.val ∈ cappedOccupations J ((s k).n + 1) (3 * t / 4))
    (hmargin : ∀ k, 4 ≤ t * ((s k).n + 1 : ℕ))
    (hN : Tendsto (fun k => ((s k).n + 1 : ℝ)) atTop atTop)
    (hfar : ∀ k, ε ^ 2 ≤ ∑ a, ((s k).profile a - ((J : ℝ) ^ 2)⁻¹) ^ 2)
    (hD : Tendsto (fun k => imbalance (mesh_pos hmesh) (s k).beta (s k).state (hm k) (hmargin k) /
      ((s k).n + 1 : ℝ)) atTop (𝓝 0)) :
    ∃ (β : ℝ) (f : L4), β ∈ Ioc 0 β₀ ∧ 0 ≤ f ∧ (∫ x, f x ∂torusMeasure) = 1 ∧
      f ≠ oneL4 ∧
      (f =ᵐ[torusMeasure] fun x =>
        Real.exp (β * ∫ y, greenRealRepresentative (x - y) * f y ∂torusMeasure) /
          (∫ z, Real.exp (β * ∫ y, greenRealRepresentative (z - y) * f y ∂torusMeasure) ∂torusMeasure)) := by
  obtain ⟨β, θ, f, r, _hr, hβ, _hθ, _hθmass, hf0, hfmass, _hβlim, hθlim,
    _hflim, _hUlim, hcell, hglobal⟩ := exists_original_global_limit hsub htC hmesh s hm hmargin hN hD
  have hcont : Continuous (fun ψ : MeshIndex J → ℝ => ∑ a, (ψ a - ((J : ℝ) ^ 2)⁻¹) ^ 2) := by
    fun_prop
  have hfarθ : ε ^ 2 ≤ ∑ a, (θ a - ((J : ℝ) ^ 2)⁻¹) ^ 2 :=
    (isClosed_le continuous_const hcont).mem_of_tendsto hθlim
      (Eventually.of_forall (fun k => hfar (r k)))
  have hneq : f ≠ oneL4 := by
    intro hf1
    have hθ1 (a : MeshIndex J) : θ a = ((J : ℝ) ^ 2)⁻¹ := by
      rw [← hcell a, hf1, integral_congr_ae (ae_restrict_of_ae oneL4_ae)]
      simp only [setIntegral_const, Measure.real, torusMeasure_meshCell, ENNReal.toReal_inv,
        ENNReal.toReal_pow, ENNReal.toReal_natCast, smul_eq_mul, mul_one]
    have hz : (∑ a, (θ a - ((J : ℝ) ^ 2)⁻¹) ^ 2) = 0 := by simp only [hθ1, sub_self, zero_pow two_ne_zero, Finset.sum_const_zero]
    rw [hz] at hfarθ
    exact (not_le_of_gt (pow_pos hε 2)) hfarθ
  have hβpos : 0 < β := by
    by_contra hn
    have he : β = 0 := le_antisymm (le_of_not_gt hn) hβ.1
    subst β
    exact hneq (original_global_fixedPoint_zero_eq_one hglobal)
  exact ⟨β, f, ⟨hβpos, hβ.2⟩, hf0, hfmass, hneq, hglobal⟩

end PeriodicAttractiveLogGas.OccupationFarCompactness
