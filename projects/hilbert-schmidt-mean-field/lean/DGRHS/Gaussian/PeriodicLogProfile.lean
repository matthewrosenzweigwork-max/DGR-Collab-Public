import DGRHS.Commutator.SourceLogGaussianShortDerivative
import DGRHS.Gaussian.PeriodicProfileLatticeSum

/-!
Packet P9h, unit 3 (LOG, part 1): the lattice sum of the LOG Gaussian short-range profile
`P_η(y) = ∫_{0<t≤η} t^{-1} e^{-|y|²/(2t²)} dt = gaussianLogShortRange η y` (the `s = 0` profile).

All-order derivative bounds of `P_η` away from the origin with Gaussian decay, local summable bounds for
the translates, termwise iterated differentiation of the lattice sum `y ↦ Σ_m P_η(y+m)` off the lattice
and `C^N` regularity there (the `s = 0` counterpart of `PeriodicProfileLattice`/`PeriodicProfileLatticeSum`,
which need `s > 0`; built here from the Euclidean LOG short-range derivative formula).
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped NNReal Topology
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma integrableOn_Ioc_rpow_exp (q a η : ℝ) (hq : 0 ≤ q) (ha : 0 < a) (hη : 0 < η) :
    IntegrableOn (fun t : ℝ => t ^ (-q - 1) * Real.exp (-a / t ^ 2)) (Ioc 0 η) := by
  have h := (DGRHS.Gaussian.integrableOn_gaussianRiesz_full_scale (q + 1) a (by linarith) ha).mono_set
    (fun t (ht : t ∈ Ioc (0 : ℝ) η) => (ht.1 : (0 : ℝ) < t))
  refine (h.const_mul η).mono' ?_ ?_
  · exact (by fun_prop : Measurable (fun t : ℝ => t ^ (-q - 1) * Real.exp (-a / t ^ 2))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    have hp : t ^ (-q - 1) = t ^ (-(q + 1) - 1) * t := by
      rw [← Real.rpow_add_one ht0.ne']
      congr 1; ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le), hp]
    have hn : 0 ≤ t ^ (-(q + 1) - 1) * Real.exp (-a / t ^ 2) :=
      mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le
    nlinarith [ht.2, hn]

/-- All-order derivative bound of the LOG short-range profile away from the origin, with Gaussian
decay at infinity. -/
lemma gaussianLogShortRange_iteratedFDeriv_bound (η r : ℝ) (hη : 0 < η) (hr : 0 < r) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : E, r ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ k (gaussianLogShortRange η) y‖ ≤ B * Real.exp (-‖y‖ ^ 2 / (16 * η ^ 2)) := by
  set Ck := sourceRieszGaussianDerivativeConstant k with hCk
  have hCk0 : 0 ≤ Ck := (sourceRieszGaussianDerivativeConstant_pos k).le
  set J : ℝ := ∫ t in Ioc 0 η, t ^ (-(k : ℝ) - 1) * Real.exp (-(r ^ 2 / 16) / t ^ 2) with hJ
  have hJint : IntegrableOn (fun t : ℝ => t ^ (-(k : ℝ) - 1) * Real.exp (-(r ^ 2 / 16) / t ^ 2))
      (Ioc 0 η) := integrableOn_Ioc_rpow_exp k (r ^ 2 / 16) η (Nat.cast_nonneg k) (by positivity) hη
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioc (fun t ht =>
    mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.exp_pos _).le)
  refine ⟨Ck * J, by positivity, ?_⟩
  intro y hy
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy; linarith
  rw [sourceLogShortRange_iteratedFDeriv_formula k η hη hy0]
  have hi := integrable_sourceLogGaussian_derivative_scale k η hη hy0
  have hpt : ∀ t ∈ Ioc 0 η, ‖t⁻¹ • iteratedFDeriv ℝ k (sourceRieszGaussianScale t) y‖ ≤
      Ck * (t ^ (-(k : ℝ) - 1) * Real.exp (-(r ^ 2 / 16) / t ^ 2)) *
        Real.exp (-‖y‖ ^ 2 / (16 * η ^ 2)) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htη : t ≤ η := ht.2
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr ht0.le)]
    have hb := sourceRieszGaussian_iteratedFDeriv_unweighted_bound k t ht0 y
    have hexp : Real.exp (-‖y‖ ^ 2 / (8 * t ^ 2)) ≤
        Real.exp (-(r ^ 2 / 16) / t ^ 2) * Real.exp (-‖y‖ ^ 2 / (16 * η ^ 2)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : r ^ 2 ≤ ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
      have h2 : ‖y‖ ^ 2 / (16 * η ^ 2) ≤ ‖y‖ ^ 2 / (16 * t ^ 2) := by
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        nlinarith
      have h3 : (r ^ 2 / 16) / t ^ 2 ≤ ‖y‖ ^ 2 / (16 * t ^ 2) := by
        rw [div_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
      have h4 : -‖y‖ ^ 2 / (8 * t ^ 2) = -(‖y‖ ^ 2 / (16 * t ^ 2)) - ‖y‖ ^ 2 / (16 * t ^ 2) := by
        field_simp; ring
      have h5 : -(r ^ 2 / 16) / t ^ 2 = -((r ^ 2 / 16) / t ^ 2) := by ring
      rw [h4, h5, show -‖y‖ ^ 2 / (16 * η ^ 2) = -(‖y‖ ^ 2 / (16 * η ^ 2)) by ring]
      linarith
    have hp : t⁻¹ * (t⁻¹) ^ k = t ^ (-(k : ℝ) - 1) := by
      have h1 : t ^ (-(k : ℝ) - 1) = (t ^ (k + 1))⁻¹ := by
        rw [show (-(k : ℝ) - 1) = -((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg ht0.le,
          Real.rpow_natCast]
      rw [h1, ← inv_pow, pow_succ']
    calc t⁻¹ * ‖iteratedFDeriv ℝ k (sourceRieszGaussianScale t) y‖
        ≤ t⁻¹ * ((t⁻¹) ^ k * Ck * Real.exp (-‖y‖ ^ 2 / (8 * t ^ 2))) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ht0.le)
      _ = Ck * (t ^ (-(k : ℝ) - 1) * Real.exp (-‖y‖ ^ 2 / (8 * t ^ 2))) := by
          rw [← hp]; ring
      _ ≤ Ck * (t ^ (-(k : ℝ) - 1) * (Real.exp (-(r ^ 2 / 16) / t ^ 2) *
            Real.exp (-‖y‖ ^ 2 / (16 * η ^ 2)))) := by
          gcongr
      _ = _ := by ring
  have hmajor : IntegrableOn (fun t : ℝ => Ck * (t ^ (-(k : ℝ) - 1) *
      Real.exp (-(r ^ 2 / 16) / t ^ 2)) * Real.exp (-‖y‖ ^ 2 / (16 * η ^ 2))) (Ioc 0 η) :=
    (hJint.const_mul Ck).mul_const _
  calc ‖∫ t in Ioc 0 η, t⁻¹ • iteratedFDeriv ℝ k (sourceRieszGaussianScale t) y‖
      ≤ ∫ t in Ioc 0 η, ‖t⁻¹ • iteratedFDeriv ℝ k (sourceRieszGaussianScale t) y‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioc 0 η, Ck * (t ^ (-(k : ℝ) - 1) * Real.exp (-(r ^ 2 / 16) / t ^ 2)) *
          Real.exp (-‖y‖ ^ 2 / (16 * η ^ 2)) :=
        setIntegral_mono_on hi.norm hmajor measurableSet_Ioc hpt
    _ = Ck * J * Real.exp (-‖y‖ ^ 2 / (16 * η ^ 2)) := by
        rw [integral_mul_const, integral_const_mul]

lemma gaussianLogShortRange_differentiableAt_iteratedFDeriv (η : ℝ) (hη : 0 < η) (n : ℕ) {z : E}
    (hz : z ≠ 0) : DifferentiableAt ℝ (iteratedFDeriv ℝ n (gaussianLogShortRange η)) z := by
  have he : iteratedFDeriv ℝ n (gaussianLogShortRange η) =ᶠ[𝓝 z]
      fun y => ∫ t in Ioc 0 η, t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) y := by
    filter_upwards [eventually_ne_nhds hz] with y hy
    exact sourceLogShortRange_iteratedFDeriv_formula n η hη hy
  refine DifferentiableAt.congr_of_eventuallyEq ?_ he
  exact (hasFDerivAt_sourceLogGaussian_scale_integral n η hη hz).differentiableAt

/-- The lattice sum of the LOG short-range profile. -/
def periodicLogProfileSum (η : ℝ) (y : E) : ℝ :=
  ∑' m : PeriodicFrequency ι, gaussianLogShortRange η (y + periodicFrequencyVector m)

/-- Local summable all-order derivative bounds for the translates of the LOG profile. -/
lemma periodicLogProfile_translate_local_bounds (η : ℝ) (hη : 0 < η) (z : E)
    (hz : z ∈ (periodicOffLattice : Set E)) :
    ∃ r : ℝ, 0 < r ∧ ball z r ⊆ (periodicOffLattice : Set E) ∧ ∀ k : ℕ,
      ∃ u : PeriodicFrequency ι → ℝ, Summable u ∧ ∀ m : PeriodicFrequency ι,
      ∀ y ∈ ball z r, ‖iteratedFDeriv ℝ k (gaussianLogShortRange η)
        (y + periodicFrequencyVector m)‖ ≤ u m := by
  obtain ⟨δ, hδ, hgap⟩ := exists_lattice_gap hz
  refine ⟨δ / 2, by positivity, ball_subset_periodicOffLattice (ι := ι) hδ hgap, fun k => ?_⟩
  obtain ⟨B, hB, hbd⟩ := gaussianLogShortRange_iteratedFDeriv_bound (ι := ι) η (δ / 2) hη
    (by positivity) k
  refine ⟨fun m => B * Real.exp ((δ / 2) ^ 2 / (16 * η ^ 2)) *
    Real.exp (-(1 / (32 * η ^ 2)) * ‖z + periodicFrequencyVector m‖ ^ 2), ?_, ?_⟩
  · exact (summable_exp_neg_lattice (ι := ι) (1 / (32 * η ^ 2)) (by positivity) z).mul_left _
  · intro m y hy
    have hd : ‖y - z‖ < δ / 2 := by simpa only [mem_ball, dist_eq_norm] using hy
    have hlow : δ / 2 ≤ ‖y + periodicFrequencyVector m‖ := by
      have h1 : ‖z + periodicFrequencyVector m‖ ≤ ‖y + periodicFrequencyVector m‖ + ‖y - z‖ := by
        calc ‖z + periodicFrequencyVector m‖ = ‖(y + periodicFrequencyVector m) - (y - z)‖ := by
              congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      linarith [hgap m]
    refine (hbd _ hlow).trans ?_
    dsimp only
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
    have h2 : ‖z + periodicFrequencyVector m‖ ≤ ‖y + periodicFrequencyVector m‖ + ‖y - z‖ := by
      calc ‖z + periodicFrequencyVector m‖ = ‖(y + periodicFrequencyVector m) - (y - z)‖ := by
            congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    have h3 : ‖z + periodicFrequencyVector m‖ ^ 2 ≤ 2 * ‖y + periodicFrequencyVector m‖ ^ 2 + 2 * (δ / 2) ^ 2 := by
      have hb : ‖y - z‖ ≤ δ / 2 := hd.le
      nlinarith [norm_nonneg (y + periodicFrequencyVector m), norm_nonneg (y - z),
        norm_nonneg (z + periodicFrequencyVector m)]
    have h4 : (0 : ℝ) < 16 * η ^ 2 := by positivity
    have h5 : -(‖y + periodicFrequencyVector m‖ ^ 2) / (16 * η ^ 2) ≤
        (δ / 2) ^ 2 / (16 * η ^ 2) + -(1 / (32 * η ^ 2)) * ‖z + periodicFrequencyVector m‖ ^ 2 := by
      rw [div_add' _ _ _ h4.ne', le_div_iff₀ h4]
      field_simp
      nlinarith [h3]
    simpa only [neg_div] using h5

lemma summable_gaussianLogShortRange_translate (η : ℝ) (hη : 0 < η) {z : E}
    (hz : z ∈ (periodicOffLattice : Set E)) :
    Summable fun m : PeriodicFrequency ι => gaussianLogShortRange η (z + periodicFrequencyVector m) := by
  obtain ⟨r, hr, -, hk⟩ := periodicLogProfile_translate_local_bounds η hη z hz
  obtain ⟨u, hu, hub⟩ := hk 0
  refine Summable.of_norm_bounded hu (fun m => ?_)
  have := hub m z (mem_ball_self hr)
  simpa only [norm_iteratedFDeriv_zero] using this

/-- Termwise iterated differentiation of the LOG profile lattice sum off the lattice. -/
theorem periodicLogProfileSum_iteratedFDeriv (η : ℝ) (hη : 0 < η) (k : ℕ) {z : E}
    (hz : z ∈ (periodicOffLattice : Set E)) :
    iteratedFDeriv ℝ k (periodicLogProfileSum (ι := ι) η) z =
      ∑' m : PeriodicFrequency ι,
        iteratedFDeriv ℝ k (gaussianLogShortRange η) (z + periodicFrequencyVector m) := by
  have h := iteratedFDeriv_tsum_of_local_bounds
    (fun (m : PeriodicFrequency ι) (y : E) => gaussianLogShortRange η (y + periodicFrequencyVector m))
    (periodicOffLattice : Set E) isOpen_periodicOffLattice k
    (fun m y hy j _ => by
      have h1 := gaussianLogShortRange_differentiableAt_iteratedFDeriv η hη j (hy m)
      have h2 : iteratedFDeriv ℝ j (fun y => gaussianLogShortRange η (y + periodicFrequencyVector m)) =
          fun y => iteratedFDeriv ℝ j (gaussianLogShortRange η) (y + periodicFrequencyVector m) :=
        iteratedFDeriv_comp_add_right' j (periodicFrequencyVector m)
      rw [h2]
      exact h1.comp y (differentiableAt_id.add_const _))
    (fun y hy => by
      obtain ⟨r, hr, hsub, hk⟩ := periodicLogProfile_translate_local_bounds η hη y hy
      refine ⟨r, hr, hsub, fun j _ => ?_⟩
      obtain ⟨u, hu, hub⟩ := hk j
      refine ⟨u, hu, fun m y' hy' => ?_⟩
      rw [iteratedFDeriv_comp_add_right]
      exact hub m y' hy') k le_rfl z hz
  simp only [iteratedFDeriv_comp_add_right] at h
  exact h

/-- The lattice sum of the LOG profile is `C^N` off the lattice. -/
theorem periodicLogProfileSum_contDiffAt (η : ℝ) (hη : 0 < η) (N : ℕ) {z : E}
    (hz : z ∈ (periodicOffLattice : Set E)) : ContDiffAt ℝ N (periodicLogProfileSum (ι := ι) η) z := by
  have hdf : ∀ (m : PeriodicFrequency ι), ∀ y ∈ (periodicOffLattice : Set E), ∀ k : ℕ, k < N + 1 →
      DifferentiableAt ℝ (iteratedFDeriv ℝ k
        (fun y : E => gaussianLogShortRange η (y + periodicFrequencyVector m))) y := by
    intro m y hy j _
    have h1 := gaussianLogShortRange_differentiableAt_iteratedFDeriv η hη j (hy m)
    have h2 : iteratedFDeriv ℝ j (fun y => gaussianLogShortRange η (y + periodicFrequencyVector m)) =
        fun y => iteratedFDeriv ℝ j (gaussianLogShortRange η) (y + periodicFrequencyVector m) :=
      iteratedFDeriv_comp_add_right' j (periodicFrequencyVector m)
    rw [h2]
    exact h1.comp y (differentiableAt_id.add_const _)
  have hb : ∀ z ∈ (periodicOffLattice : Set E), ∃ r : ℝ, 0 < r ∧ ball z r ⊆ (periodicOffLattice : Set E) ∧
      ∀ k : ℕ, k ≤ N + 1 → ∃ u : PeriodicFrequency ι → ℝ, Summable u ∧ ∀ i : PeriodicFrequency ι,
        ∀ y ∈ ball z r, ‖iteratedFDeriv ℝ k
          (fun y : E => gaussianLogShortRange η (y + periodicFrequencyVector i)) y‖ ≤ u i := by
    intro y hy
    obtain ⟨r, hr, hsub, hk⟩ := periodicLogProfile_translate_local_bounds η hη y hy
    refine ⟨r, hr, hsub, fun j _ => ?_⟩
    obtain ⟨u, hu, hub⟩ := hk j
    refine ⟨u, hu, fun m y' hy' => ?_⟩
    rw [iteratedFDeriv_comp_add_right]
    exact hub m y' hy'
  have hdiff := differentiableAt_iteratedFDeriv_tsum_of_local_bounds
    (fun (m : PeriodicFrequency ι) (y : E) => gaussianLogShortRange η (y + periodicFrequencyVector m))
    (periodicOffLattice : Set E) isOpen_periodicOffLattice (N + 1) hdf hb
  have hco : ContDiffOn ℝ (N : ℕ∞) (periodicLogProfileSum (ι := ι) η) (periodicOffLattice : Set E) := by
    refine contDiffOn_of_differentiableOn (fun m hm => ?_)
    intro y hy
    have hm' : m < N + 1 := by
      have : (m : ℕ∞) ≤ (N : ℕ∞) := hm
      exact Nat.lt_succ_of_le (by exact_mod_cast this)
    have hop : IsOpen (periodicOffLattice : Set E) := isOpen_periodicOffLattice
    exact ((hdiff m hm' y hy).differentiableWithinAt).congr
      (fun y' hy' => iteratedFDerivWithin_of_isOpen m hop hy')
      (iteratedFDerivWithin_of_isOpen m hop hy)
  exact (hco.contDiffAt (isOpen_periodicOffLattice.mem_nhds hz) :)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLogProfileSum_iteratedFDeriv
#print axioms DGRHS.Periodic.periodicLogProfileSum_contDiffAt
