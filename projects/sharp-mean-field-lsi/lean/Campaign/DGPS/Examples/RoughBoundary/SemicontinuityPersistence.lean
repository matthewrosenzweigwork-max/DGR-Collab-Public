import DGPS.Examples.RoughBoundary.LandscapeSelection
import DGPS.Examples.RoughBoundary.SemicontinuityPotential
import DGPS.Examples.RoughBoundary.SymmetryRetention
import DGPS.Examples.RoughBoundary.FeatureMoments
import DGPS.Examples.RoughBoundary.SmallAmplitude
import DGPS.Analysis.PeriodicMollificationHolder

/-!
# SEM009: global Haar and remote wells persist for smooth approximants

Inputs: RUF026 (`local_selection`, the selection of the tolerances `R`, `η`), RUF021--RUF025
(`compact_uniform_convergence_of_parameter_derivatives`, `global_three_region_positivity_persists`,
and the margin/contraction machinery packaged in `local_selection`), SEM003 (mollification and its
sup-norm/Hölder control), SEM007 (`symmetry_retained_by_all_smoothing_and_amplitude_families`)
and SEM008 (`feature_sup_distance_controls_c2_parameter_potential_distance`).

The proof is a *robustness* statement (`robust_certificate`): there are `δ₀ > 0` and `L₀` such that
every unit-circle feature `U` with the exact `R_{2π/3}` shift symmetry and exact moments which is
uniformly `δ₀`-close to the smooth base `U_{L,0}` (`L ≥ L₀`) carries the full landscape
certificate.  SEM008 turns the uniform feature distance into a `C²(B̄_R)` bound for the
parameter potential, RUF021 gives `Λ_{U_{L,0}} → logPartition` in `C²(B̄_R)`, and the two are fed
to `global_three_region_positivity_persists` and `local_selection`.  The features `U_j` with
the mollified profile `g_{h_j}` and amplitude `1/L` are uniformly `2π ‖g_{h_j}‖_∞ / L`-close to
`U_{L,0}`, and `‖g_h‖_∞ ≤ ‖g‖_∞` for every mollification width, so the persistence is uniform in
the width.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff Real

namespace DGPS.Examples.RoughBoundary.Semicontinuity

open DGPS.Examples.RoughBoundary.Landscape
open DGPS.Examples.RoughBoundary.Feature (Ufeat rot120 UtorGen measurable_UtorGen norm_Ufeat)
open DGPS.Analysis.PeriodicMollification

/-! ### `C²` seminorm bounds from pointwise bounds -/

lemma norm_fderiv_sub_eq (f g : E2 → ℝ) (t : E2) :
    ‖fderiv ℝ f t - fderiv ℝ g t‖ = ‖gradient f t - gradient g t‖ := by
  unfold gradient
  rw [← map_sub, LinearIsometryEquiv.norm_map]

lemma ckBound_two_sub {F G : E2 → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) {S : Set E2}
    {M : ℝ} (h0 : ∀ t ∈ S, |F t - G t| ≤ M)
    (h1 : ∀ t ∈ S, ‖fderiv ℝ F t - fderiv ℝ G t‖ ≤ M)
    (h2 : ∀ t ∈ S, ‖fderiv ℝ (fderiv ℝ F) t - fderiv ℝ (fderiv ℝ G) t‖ ≤ M) :
    ckBound S 2 (fun t => F t - G t) M := by
  have hFd : ∀ t, DifferentiableAt ℝ F t := fun t => hF.differentiable (by simp) t
  have hGd : ∀ t, DifferentiableAt ℝ G t := fun t => hG.differentiable (by simp) t
  have hd1 : fderiv ℝ (fun t => F t - G t) = fun t => fderiv ℝ F t - fderiv ℝ G t :=
    funext fun t => fderiv_sub (hFd t) (hGd t)
  have hFd' : ∀ t, DifferentiableAt ℝ (fderiv ℝ F) t := fun t =>
    ((hF.fderiv_right (m := 1) (by simp)).differentiable (by simp)) t
  have hGd' : ∀ t, DifferentiableAt ℝ (fderiv ℝ G) t := fun t =>
    ((hG.fderiv_right (m := 1) (by simp)).differentiable (by simp)) t
  have hd2 : fderiv ℝ (fderiv ℝ fun t => F t - G t) =
      fun t => fderiv ℝ (fderiv ℝ F) t - fderiv ℝ (fderiv ℝ G) t := by
    rw [hd1]; exact funext fun t => fderiv_sub (hFd' t) (hGd' t)
  refine ckBound_of_fderiv (k := 1) (fun t ht => by simpa [Real.norm_eq_abs] using h0 t ht)
    (ckBound_of_fderiv (k := 0) ?_ ?_)
  · intro t ht
    rw [hd1]; exact h1 t ht
  · intro t ht j hj
    have : j = 0 := by omega
    subst this
    rw [norm_iteratedFDeriv_zero, hd2]
    exact h2 t ht

/-- SEM008 as a `C²(B̄_R)` seminorm bound for the difference of the log partitions. -/
lemma ckBound_logPartition_dist {U V : Torus 1 → E2} (hUm : Measurable U) (hVm : Measurable V)
    (hU1 : ∀ y, ‖U y‖ ≤ 1) (hV1 : ∀ y, ‖V y‖ ≤ 1) {δ R : ℝ} (hδ0 : 0 ≤ δ) (hR0 : 0 ≤ R)
    (hδ : ∀ y, ‖U y - V y‖ ≤ δ) :
    ckBound (closedBall (0 : E2) R) 2
      (fun t => featureLogPartition U t - featureLogPartition V t) ((4 + 6 * R) * δ) := by
  have hUc : ContDiff ℝ ∞ (featureLogPartition U) :=
    contDiff_logPart (μ := DGPS.haar 1) hUm (Filter.Eventually.of_forall hU1)
  have hVc : ContDiff ℝ ∞ (featureLogPartition V) :=
    contDiff_logPart (μ := DGPS.haar 1) hVm (Filter.Eventually.of_forall hV1)
  refine ckBound_two_sub hUc hVc (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
  all_goals
    have ht' : ‖t‖ ≤ R := mem_closedBall_zero_iff.1 ht
    obtain ⟨a, b, c⟩ := feature_sup_distance_controls_c2_parameter_potential_distance hUm hVm
      (Filter.Eventually.of_forall hU1) (Filter.Eventually.of_forall hV1)
      (Filter.Eventually.of_forall hδ) ht'
    have e1 : R * δ ≤ (4 + 6 * R) * δ := by nlinarith
    have e2 : (1 + 2 * R) * δ ≤ (4 + 6 * R) * δ := by nlinarith
  · exact a.trans e1
  · rw [norm_fderiv_sub_eq]; exact b.trans e2
  · exact c

/-! ### The robust certificate -/

/-- Perturbation of the order potential by a log-partition difference bounded in `C²(B̄_R)`,
for an arbitrary feature `U` with the exact shift symmetry. -/
lemma perturbed_certificate_gen {U : Torus 1 → E2} {s : Torus 1}
    (hs : ∀ y, U (y + s) = rot120 (U y)) {R η M : ℝ}
    (hb : ckBound (closedBall (0 : E2) R) 2
      (fun t => featureLogPartition U t - logPartition t) M)
    (hM : M ≤ η / 2) (hcd : ContDiff ℝ ∞ (featureLogPartition U)) :
    ContDiff ℝ ∞ (featurePotential kappa0 U) ∧
    (∀ x, featurePotential kappa0 U (rot120 x) = featurePotential kappa0 U x) ∧
    (∀ t ∈ closedBall (0 : E2) R, |featurePotential kappa0 U t - orderPotential t| ≤ η / 2) ∧
    (∀ t ∈ closedBall (0 : E2) R,
      ‖fderiv ℝ (featurePotential kappa0 U) t - fderiv ℝ orderPotential t‖ ≤ η / 2) ∧
    (∀ t ∈ closedBall (0 : E2) R,
      ‖fderiv ℝ (fderiv ℝ (featurePotential kappa0 U)) t -
        fderiv ℝ (fderiv ℝ orderPotential) t‖ ≤ η / 2) ∧
    ContDiff ℝ 2 (featurePotential kappa0 U) := by
  have hg : featurePotential kappa0 U =
      fun t => orderPotential t - (featureLogPartition U t - logPartition t) := by
    funext t
    unfold featurePotential orderPotential
    ring
  have hh : ContDiff ℝ ∞ (fun t => featureLogPartition U t - logPartition t) :=
    hcd.sub contDiff_logPartition
  obtain ⟨h2, h0, h1, h2'⟩ := perturb_bounds contDiff_orderPotential hh hg hb
  refine ⟨?_, fun x => ?_, fun t ht => (h0 t ht).trans hM,
    fun t ht => (h1 t ht).trans hM, fun t ht => (h2' t ht).trans hM, h2⟩
  · rw [hg]
    have : ContDiff ℝ ∞ orderPotential := by
      unfold orderPotential
      exact ((contDiff_norm_sq ℝ).div_const _).sub contDiff_logPartition
    exact this.sub hh
  · unfold featurePotential
    rw [featureLogPartition_rot hs x, norm_rot120]

/-- **Robustness.**  There are `δ₀ > 0` and `L₀ ≥ 1` such that every circle feature `U` with the exact
shift symmetry `U(y + 1/6) = R_{2π/3} U(y)`, the exact moments `0`, `I₂/2`, `‖U‖ ≤ 1`, which is
uniformly `δ₀`-close to the smooth base `U_{L,0}` with `L ≥ L₀`, carries the landscape certificate. -/
theorem robust_certificate :
    ∃ δ₀ L₀ : ℝ, 0 < δ₀ ∧ 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ U : Torus 1 → E2,
      Measurable U → (∀ y, ‖U y‖ ≤ 1) →
      (∀ y, U (y + Spikes.pt (1 / 6)) = rot120 (U y)) →
      ∫ y, U y ∂DGPS.haar 1 = 0 →
      (∀ i j : Fin 2, ∫ y, U y i * U y j ∂DGPS.haar 1 = if i = j then 1 / 2 else 0) →
      (∀ y, ‖U y - Ufeat L 0 y‖ ≤ δ₀) → RoughLandscapeCertificate U := by
  obtain ⟨R, hR, η, hη, hloc⟩ := local_selection
  obtain ⟨γ, -, hγ, hglob⟩ := global_three_region_positivity_persists hR
  obtain ⟨hP1, -, -⟩ := compact_uniform_convergence_of_parameter_derivatives
  have hR0 : 0 < R := by have : 0 < kappa0 := kappa0_pos; linarith
  set η1 : ℝ := min η (γ / 2) with hη1def
  have hη10 : 0 < η1 := lt_min hη (by positivity)
  have hη1a : η1 ≤ η := min_le_left _ _
  have hη1b : η1 ≤ γ / 2 := min_le_right _ _
  set δ₀ : ℝ := η1 / (4 * (4 + 6 * R)) with hδ₀def
  have hδ₀ : 0 < δ₀ := by positivity
  have hδ₀b : (4 + 6 * R) * δ₀ = η1 / 4 := by
    rw [hδ₀def]; field_simp
  obtain ⟨L1, hL1⟩ := hP1 2 R (η1 / 4) (by positivity)
  refine ⟨δ₀, max 1 L1, hδ₀, le_max_left _ _, ?_⟩
  intro L hL U hUm hU1 hrotU hm1 hm2 hclose
  have hL1' : 1 ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1'
  have hLL1 : L1 ≤ L := (le_max_right _ _).trans hL
  have hUc : ContDiff ℝ ∞ (featureLogPartition U) :=
    contDiff_logPart (μ := DGPS.haar 1) hUm (Filter.Eventually.of_forall hU1)
  have hcd0 : ContDiff ℝ ∞ (featureLogPartition (Ufeat L 0)) :=
    contDiff_logPart (μ := DGPS.haar 1) (measurable_Ufeat hLpos 0)
      (Filter.Eventually.of_forall fun y => (norm_Ufeat L 0 y).le)
  have hb1 := ckBound_logPartition_dist (R := R) hUm (measurable_Ufeat hLpos 0) hU1
    (fun y => (norm_Ufeat L 0 y).le) hδ₀.le hR0.le hclose
  rw [hδ₀b] at hb1
  have hb0 := hL1 L hLL1
  have hbsum := ckBound_add (hUc.sub hcd0) (hcd0.sub contDiff_logPartition) hb1 hb0
  have e : (fun t => featureLogPartition U t - logPartition t) =
      fun t => (featureLogPartition U t - featureLogPartition (Ufeat L 0) t) +
        (featureLogPartition (Ufeat L 0) t - logPartition t) :=
    funext fun t => by ring
  have hb : ckBound (closedBall (0 : E2) R) 2
      (fun t => featureLogPartition U t - logPartition t) (η1 / 2) := by
    rw [e]
    exact ckBound_mono hbsum (by linarith)
  obtain ⟨hcont, hrot, hv, hd1, hd2, hc2⟩ :=
    perturbed_certificate_gen hrotU hb le_rfl hUc
  obtain ⟨g1, g2, g3, g4⟩ := hglob U hUm hU1 hm1 hm2 (fun t ht => by
    have := hv t (mem_closedBall_zero_iff.2 ht)
    linarith)
  refine ⟨hcont, hrot, g1, g2, g3, g4, hloc _ hc2 hrot (fun t ht => ?_) (fun t ht => ?_)
    (fun t ht => ?_)⟩
  · exact (hv t ht).trans (by linarith)
  · exact (hd1 t ht).trans (by linarith)
  · exact (hd2 t ht).trans (by linarith)

/-! ### The smooth approximants -/

/-- The mollified rough profile is bounded by `hMean` for every width. -/
lemma abs_mollify_gT_le {h : ℝ} (hh : 0 < h) (y : Torus 1) :
    |mollify h Spikes.gT y| ≤ Spikes.hMean := by
  unfold mollify
  exact abs_integral_phiH_mul_le hh fun s _ => Spikes.abs_gT_le _

lemma continuous_mollify_gT {h : ℝ} (hh : 0 < h) : Continuous (mollify h Spikes.gT) := by
  have hg := holder_gT (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  obtain ⟨K, hK0, hK⟩ := hg
  exact continuous_of_holderBdd (by norm_num : (0 : ℝ) < 1 / 2)
    ⟨K, hK0, abs_mollify_sub_le hh continuous_gT hK⟩

/-- A profile bounded by `B` gives a feature uniformly `2π |η| B`-close to the smooth base. -/
lemma norm_UfeatF_sub_base_le (L η : ℝ) {f : Torus 1 → ℝ} {B : ℝ} (hf : ∀ y, |f y| ≤ B)
    (y : Torus 1) : ‖UfeatF L η f y - Ufeat L 0 y‖ ≤ 2 * π * (|η| * B) := by
  have h := norm_Efun_le L η (fun _ => (0 : ℝ)) f y
  have e : Efun L η (fun _ => (0 : ℝ)) f y = UfeatF L η f y - Ufeat L 0 y := by
    unfold Efun; rw [UfeatF_zero]
  rw [e] at h
  refine h.trans ?_
  unfold phaseDiff
  have : |η * (f ((6 : ℤ) • y) - (fun _ => (0 : ℝ)) ((6 : ℤ) • y))| ≤ |η| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by simpa using hf _) (abs_nonneg _)
  gcongr

/-- Persistence of the certificate for features `U_{L,1/L}` built on any measurable profile bounded by
`hMean`: uniform in the profile once `L` is large. -/
theorem certificate_of_bounded_profile :
    ∃ L₁ : ℝ, 1 ≤ L₁ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ f : Torus 1 → ℝ, Measurable f →
      (∀ y, |f y| ≤ Spikes.hMean) → RoughLandscapeCertificate (UfeatF L (1 / L) f) := by
  obtain ⟨δ₀, L₀, hδ₀, hL₀, hrob⟩ := robust_certificate
  refine ⟨max L₀ (2 * π * Spikes.hMean / δ₀), hL₀.trans (le_max_left _ _), ?_⟩
  intro L hL f hfm hfb
  have hL0 : L₀ ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := lt_of_lt_of_le one_pos (hL₀.trans hL0)
  have hLd : 2 * π * Spikes.hMean / δ₀ ≤ L := (le_max_right _ _).trans hL
  have hφ : Measurable (fun s : ℝ => f (Spikes.pt s)) := hfm.comp measurable_pt
  have hUm : Measurable (UfeatF L (1 / L) f) := measurable_UtorGen hφ L (1 / L)
  obtain ⟨-, -, -, hm0, hm2⟩ := symmetry_retained_by_all_smoothing_and_amplitude_families
    hLpos (1 / L) hfm
  obtain ⟨-, ⟨hsix, -⟩, -, -, -⟩ := symmetry_retained_by_all_smoothing_and_amplitude_families
    hLpos (1 / L) hfm
  refine hrob L hL0 _ hUm (fun y => (norm_UfeatF L _ f y).le) hsix hm0 hm2 (fun y => ?_)
  refine (norm_UfeatF_sub_base_le L (1 / L) hfb y).trans ?_
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / L)]
  have hMean0 : 0 ≤ Spikes.hMean := Spikes.hMean_pos.le
  have : 2 * π * Spikes.hMean ≤ δ₀ * L := by
    rw [div_le_iff₀ hδ₀] at hLd; linarith
  calc 2 * π * (1 / L * Spikes.hMean) = 2 * π * Spikes.hMean / L := by ring
    _ ≤ δ₀ := by rw [div_le_iff₀ hLpos]; linarith

/-- Unique global minimality of the Haar point and a nonzero positive critical well, extracted from
the landscape certificate. -/
lemma haar_and_well_of_certificate {U : Torus 1 → E2} (hU : RoughLandscapeCertificate U) :
    (∀ t : E2, IsMinOn (featurePotential kappa0 U) univ t ↔ t = 0) ∧
    ∃ t : E2, t ≠ 0 ∧ fderiv ℝ (featurePotential kappa0 U) t = 0 ∧
      0 < featurePotential kappa0 U t := by
  obtain ⟨-, -, h0, huniq, -, -, hloc⟩ := hU
  have hΨ0 : featurePotential kappa0 U 0 = 0 := (huniq 0).2 rfl
  obtain ⟨Δ, B, aM, aS, hΔ, hΔB, -, -, hcM, -, -, -, -, -, -, -, hlow, -⟩ := hloc
  refine ⟨fun t => ⟨fun hmin => ?_, fun ht => ?_⟩, aM 0, ?_, hcM 0, ?_⟩
  · have h1 : featurePotential kappa0 U t ≤ featurePotential kappa0 U 0 := hmin (mem_univ 0)
    exact (huniq t).1 (le_antisymm (hΨ0 ▸ h1) (h0 t))
  · subst ht
    intro x _
    show featurePotential kappa0 U 0 ≤ featurePotential kappa0 U x
    rw [hΨ0]; exact h0 x
  · intro h
    have := hlow 0
    rw [h, hΨ0] at this
    linarith
  · have := hlow 0
    linarith

/-- **SEM009.**  Fix the permanently selected `L` (any `L ≥ 1` large enough that the primary feature
`U_{L,1/L}` carries the landscape certificate; the same smallness of `1/L` works for all the
approximants).  For every sequence of mollification widths `h_j → 0+`, for all large `j` the feature
`U_j = U_{L,1/L}[g_{h_j}]` (smooth profile `g_{h_j}` in place of `g`, amplitude `1/L`) has: Haar
(`t = 0`) as its unique global free-energy minimizer, a nonzero critical point `t_j` of
`Ψ_j(t) = ‖t‖²/(2κ) - Λ_{U_j}(t)` with `Ψ_j(t_j) > 0`, and the full landscape certificate, in
particular the exact `R_{2π/3}`-rotated triples of nondegenerate remote minima and saddles with
the positive value gaps. -/
theorem global_haar_and_remote_wells_persist_for_smooth_approximants :
    ∃ L : ℝ, 1 ≤ L ∧ RoughLandscapeCertificate (Ufeat L (1 / L)) ∧
      ∀ h : ℕ → ℝ, (∀ j, 0 < h j) → Tendsto h atTop (𝓝 0) →
        ∀ᶠ j in atTop,
          (∀ t : E2, IsMinOn (featurePotential kappa0
              (UfeatF L (1 / L) (mollify (h j) Spikes.gT))) univ t ↔ t = 0) ∧
          (∃ t : E2, t ≠ 0 ∧
              fderiv ℝ (featurePotential kappa0
                (UfeatF L (1 / L) (mollify (h j) Spikes.gT))) t = 0 ∧
              0 < featurePotential kappa0 (UfeatF L (1 / L) (mollify (h j) Spikes.gT)) t) ∧
          RoughLandscapeCertificate (UfeatF L (1 / L) (mollify (h j) Spikes.gT)) := by
  obtain ⟨L₁, hL₁, hcert⟩ := certificate_of_bounded_profile
  have hLpos : 0 < L₁ := lt_of_lt_of_le one_pos hL₁
  refine ⟨L₁, hL₁, ?_, fun h hh _ => Filter.Eventually.of_forall fun j => ?_⟩
  · have := hcert L₁ le_rfl Spikes.gT continuous_gT.measurable Spikes.abs_gT_le
    exact this
  · have hc := hcert L₁ le_rfl (mollify (h j) Spikes.gT)
      (continuous_mollify_gT (hh j)).measurable (abs_mollify_gT_le (hh j))
    exact ⟨(haar_and_well_of_certificate hc).1, (haar_and_well_of_certificate hc).2, hc⟩

end DGPS.Examples.RoughBoundary.Semicontinuity
