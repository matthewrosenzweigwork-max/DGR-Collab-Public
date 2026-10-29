import DGRHS.Gaussian.PeriodicProfileLattice

/-!
Packet P9h, unit 2 (part 4): lattice sums of Gaussian-scale profiles off the lattice.

The complement `U` of the lattice `-ℤ^d ⊂ ℝ^d` is open; on a ball around each point of `U` the
translates `y ↦ profile(y + m)` have summable all-order derivative bounds, so the iterated derivatives
of the lattice sum are the lattice sums of the iterated derivatives (`iteratedFDeriv_tsum_of_local_bounds`).
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped NNReal Topology
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The points of `ℝ^d` that are not (minus) lattice points. -/
def periodicOffLattice : Set (EuclideanSpace ℝ ι) :=
  {z | ∀ m : PeriodicFrequency ι, z + periodicFrequencyVector m ≠ 0}

/-- Every point off the lattice has a positive distance gap to all lattice translates. -/
lemma exists_lattice_gap {z : E} (hz : z ∈ (periodicOffLattice : Set E)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : PeriodicFrequency ι, δ ≤ ‖z + periodicFrequencyVector m‖ := by
  let zhat : E := WithLp.toLp 2 fun i => z i - (round (z i) : ℝ)
  refine ⟨‖zhat‖, ?_, ?_⟩
  · rw [norm_pos_iff]
    intro h
    apply hz (fun i => -round (z i))
    ext i
    have := congrArg (fun w : E => w i) h
    simp only [zhat, PiLp.zero_apply] at this
    simp only [PiLp.add_apply, periodicFrequencyVector_apply, PiLp.zero_apply]
    push_cast
    linarith
  · intro m
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    simp only [Real.norm_eq_abs, sq_abs, zhat, PiLp.add_apply, periodicFrequencyVector_apply]
    have hr : |z i - (round (z i) : ℝ)| ≤ 1 / 2 := abs_sub_round (z i)
    have hn := abs_le_abs_add_int hr (round (z i) + m i)
    have he : z i - (round (z i) : ℝ) + ((round (z i) + m i : ℤ) : ℝ) = z i + (m i : ℝ) := by
      push_cast; ring
    rw [he] at hn
    exact sq_le_sq.mpr (by simpa only [abs_abs] using hn)

lemma ball_subset_periodicOffLattice {z : E} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ m : PeriodicFrequency ι, δ ≤ ‖z + periodicFrequencyVector m‖) :
    ball z (δ / 2) ⊆ (periodicOffLattice : Set E) := by
  intro y hy m h
  have hd : ‖y - z‖ < δ / 2 := by simpa only [mem_ball, dist_eq_norm] using hy
  have h1 : ‖z + periodicFrequencyVector m‖ ≤ ‖y + periodicFrequencyVector m‖ + ‖y - z‖ := by
    calc ‖z + periodicFrequencyVector m‖ = ‖(y + periodicFrequencyVector m) - (y - z)‖ := by
          congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  rw [h, norm_zero] at h1
  linarith [hgap m]

lemma isOpen_periodicOffLattice : IsOpen (periodicOffLattice : Set E) := by
  rw [Metric.isOpen_iff]
  intro z hz
  obtain ⟨δ, hδ, hgap⟩ := exists_lattice_gap hz
  exact ⟨δ / 2, by positivity, ball_subset_periodicOffLattice (ι := ι) hδ hgap⟩

lemma summable_exp_neg_lattice (a : ℝ) (ha : 0 < a) (z : E) :
    Summable fun m : PeriodicFrequency ι =>
      Real.exp (-a * ‖z + periodicFrequencyVector m‖ ^ 2) := by
  have h := periodicGaussian_spatial_series_summable (ι := ι) (a / Real.pi) (div_pos ha Real.pi_pos) z
  refine h.congr (fun m => ?_)
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, mul_zero]
  field_simp

/-- Local summable all-order derivative bounds for the translates of a profile, on a ball around
every point off the lattice. -/
lemma periodicProfile_translate_local_bounds (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (S : Set ℝ) (hSm : MeasurableSet S) (hS : S ⊆ Ioc 0 η) (z : E)
    (hz : z ∈ (periodicOffLattice : Set E)) :
    ∃ r : ℝ, 0 < r ∧ ball z r ⊆ (periodicOffLattice : Set E) ∧ ∀ k : ℕ,
      ∃ u : PeriodicFrequency ι → ℝ, Summable u ∧ ∀ m : PeriodicFrequency ι,
      ∀ y ∈ ball z r, ‖iteratedFDeriv ℝ k (periodicProfile c s S) (y + periodicFrequencyVector m)‖ ≤ u m := by
  obtain ⟨δ, hδ, hgap⟩ := exists_lattice_gap hz
  refine ⟨δ / 2, by positivity, ball_subset_periodicOffLattice (ι := ι) hδ hgap, fun k => ?_⟩
  obtain ⟨B, hB, hbd⟩ := periodicProfile_iteratedFDeriv_bound (ι := ι) c s η (δ / 2) hc hs hη (by positivity)
    S hSm hS k
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
    -- (a + b)^2 ≤ 2 a^2 + 2 b^2 with a = ‖y+m‖, b = ‖y - z‖
    have h3 : ‖z + periodicFrequencyVector m‖ ^ 2 ≤ 2 * ‖y + periodicFrequencyVector m‖ ^ 2 + 2 * (δ / 2) ^ 2 := by
      have hb : ‖y - z‖ ≤ δ / 2 := hd.le
      nlinarith [norm_nonneg (y + periodicFrequencyVector m), norm_nonneg (y - z),
        norm_nonneg (z + periodicFrequencyVector m)]
    have h4 : (0 : ℝ) < 16 * η ^ 2 := by positivity
    have h5 : -(‖y + periodicFrequencyVector m‖ ^ 2) / (16 * η ^ 2) ≤
        (δ / 2) ^ 2 / (16 * η ^ 2) + -(1 / (32 * η ^ 2)) * ‖z + periodicFrequencyVector m‖ ^ 2 := by
      have : -(‖y + periodicFrequencyVector m‖ ^ 2) / (16 * η ^ 2) =
          -(‖y + periodicFrequencyVector m‖ ^ 2) / (16 * η ^ 2) := rfl
      rw [div_add' _ _ _ h4.ne', le_div_iff₀ h4]
      field_simp
      nlinarith [h3]
    simpa only [neg_div] using h5

/-- Termwise iterated differentiation of the lattice sum of a profile off the lattice. -/
theorem periodicProfileSum_iteratedFDeriv (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (S : Set ℝ) (hSm : MeasurableSet S) (hS : S ⊆ Ioc 0 η) (k : ℕ) {z : E}
    (hz : z ∈ (periodicOffLattice : Set E)) :
    iteratedFDeriv ℝ k (periodicProfileSum c s S) z =
      ∑' m : PeriodicFrequency ι,
        iteratedFDeriv ℝ k (periodicProfile c s S) (z + periodicFrequencyVector m) := by
  have hS0 : S ⊆ Ioi 0 := fun t ht => (hS ht).1
  have h := iteratedFDeriv_tsum_of_local_bounds
    (fun (m : PeriodicFrequency ι) (y : E) => periodicProfile c s S (y + periodicFrequencyVector m))
    (periodicOffLattice : Set E) isOpen_periodicOffLattice k
    (fun m y hy j _ => by
      have h1 := periodicProfile_differentiableAt_iteratedFDeriv c s S hSm hS0 hs j (hy m)
      have h2 : iteratedFDeriv ℝ j (fun y => periodicProfile c s S (y + periodicFrequencyVector m)) =
          fun y => iteratedFDeriv ℝ j (periodicProfile c s S) (y + periodicFrequencyVector m) :=
        iteratedFDeriv_comp_add_right' j (periodicFrequencyVector m)
      rw [h2]
      exact h1.comp y (differentiableAt_id.add_const _))
    (fun y hy => by
      obtain ⟨r, hr, hsub, hk⟩ := periodicProfile_translate_local_bounds c s η hc hs hη S hSm hS y hy
      refine ⟨r, hr, hsub, fun j _ => ?_⟩
      obtain ⟨u, hu, hub⟩ := hk j
      refine ⟨u, hu, fun m y' hy' => ?_⟩
      rw [iteratedFDeriv_comp_add_right]
      exact hub m y' hy') k le_rfl z hz
  simp only [iteratedFDeriv_comp_add_right] at h
  exact h


/-- Hypotheses of the local termwise-derivative lemmas for the translates of a profile. -/
lemma periodicProfile_translate_hdf (c s : ℝ) (hs : 0 < s) (S : Set ℝ) (hSm : MeasurableSet S)
    (hS0 : S ⊆ Ioi 0) (N : ℕ) :
    ∀ (m : PeriodicFrequency ι), ∀ y ∈ (periodicOffLattice : Set E), ∀ k : ℕ, k < N →
      DifferentiableAt ℝ (iteratedFDeriv ℝ k
        (fun y : E => periodicProfile c s S (y + periodicFrequencyVector m))) y := by
  intro m y hy j _
  have h1 := periodicProfile_differentiableAt_iteratedFDeriv c s S hSm hS0 hs j (hy m)
  have h2 : iteratedFDeriv ℝ j (fun y => periodicProfile c s S (y + periodicFrequencyVector m)) =
      fun y => iteratedFDeriv ℝ j (periodicProfile c s S) (y + periodicFrequencyVector m) :=
    iteratedFDeriv_comp_add_right' j (periodicFrequencyVector m)
  rw [h2]
  exact h1.comp y (differentiableAt_id.add_const _)

lemma periodicProfile_translate_hb (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η) (S : Set ℝ)
    (hSm : MeasurableSet S) (hS : S ⊆ Ioc 0 η) (N : ℕ) :
    ∀ z ∈ (periodicOffLattice : Set E), ∃ r : ℝ, 0 < r ∧ ball z r ⊆ (periodicOffLattice : Set E) ∧
      ∀ k : ℕ, k ≤ N → ∃ u : PeriodicFrequency ι → ℝ, Summable u ∧ ∀ i : PeriodicFrequency ι,
        ∀ y ∈ ball z r, ‖iteratedFDeriv ℝ k
          (fun y : E => periodicProfile c s S (y + periodicFrequencyVector i)) y‖ ≤ u i := by
  intro y hy
  obtain ⟨r, hr, hsub, hk⟩ := periodicProfile_translate_local_bounds c s η hc hs hη S hSm hS y hy
  refine ⟨r, hr, hsub, fun j _ => ?_⟩
  obtain ⟨u, hu, hub⟩ := hk j
  refine ⟨u, hu, fun m y' hy' => ?_⟩
  rw [iteratedFDeriv_comp_add_right]
  exact hub m y' hy'

/-- The lattice sum of a profile is `C^N` off the lattice. -/
theorem periodicProfileSum_contDiffAt (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (S : Set ℝ) (hSm : MeasurableSet S) (hS : S ⊆ Ioc 0 η) (N : ℕ) {z : E}
    (hz : z ∈ (periodicOffLattice : Set E)) : ContDiffAt ℝ N (periodicProfileSum c s S) z := by
  have hS0 : S ⊆ Ioi 0 := fun t ht => (hS ht).1
  have hdf := periodicProfile_translate_hdf (ι := ι) c s hs S hSm hS0 (N + 1)
  have hb := periodicProfile_translate_hb (ι := ι) c s η hc hs hη S hSm hS (N + 1)
  have hdiff := differentiableAt_iteratedFDeriv_tsum_of_local_bounds
    (fun (m : PeriodicFrequency ι) (y : E) => periodicProfile c s S (y + periodicFrequencyVector m))
    (periodicOffLattice : Set E) isOpen_periodicOffLattice (N + 1) hdf hb
  have hco : ContDiffOn ℝ (N : ℕ∞) (periodicProfileSum c s S) (periodicOffLattice : Set E) := by
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
#print axioms DGRHS.Periodic.periodicProfileSum_contDiffAt
