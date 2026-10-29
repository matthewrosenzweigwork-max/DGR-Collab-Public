import DGRHS.Gaussian.PeriodicRieszShortLongTransport
import DGRHS.Gaussian.PeriodicShortHeatLatticeSum

/-!
Packet P9h, unit 2 (part 14): pointwise bounds of the short and long transport kernels.

* `|κ^{short}_η| ≤ A_n K^n f_{2η}` with `f_η = Σ_m F K₀ ∫_{(0,η]} ...` the short Riesz profile sum;
* `|κ^{long}_η| ≤ K^n (A_n Ψ + B_n d^n)` uniformly in `η ≤ τ₀`;
* the diagonal cap `|κ^{long}_η| ≤ C K^n η^{-s}` (lattice Gaussian sums are uniformly bounded).
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The short pair kernel `f_η(z) = F K₀ Σ_m ∫_{(0,η]} t^{-s-1} e^{-|z+m|²/(2t²)} dt`. -/
def periodicRieszShortSum (s η : ℝ) (z : E) : ℝ :=
  periodicProfileSum (periodicRieszSmoothCoeff ι s) s (Ioc 0 η) z

lemma periodicRieszShortSum_nonneg (s η : ℝ) (hs : 0 < s) (z : E) : 0 ≤ periodicRieszShortSum s η z := by
  unfold periodicRieszShortSum periodicProfileSum
  exact tsum_nonneg fun m => periodicProfile_nonneg _ s _ (periodicRieszSmoothCoeff_pos s hs).le
    measurableSet_Ioc (fun t ht => ht.1) _

lemma periodicRieszMajorant_eq_short (s : ℝ) (z : E) :
    periodicRieszMajorant s z = periodicRieszShortSum s 1 z := rfl

/-- Scalar-sum version of the transport bound. -/
lemma periodicProfileSum_transport_bound_scalar (n : ℕ) (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s)
    (hη : 0 < η) (S : Set ℝ) (hSm : MeasurableSet S) (hS : S ⊆ Ioc 0 η) (K : ℝ≥0) {z : E}
    (hz : z ∈ (periodicOffLattice : Set E)) {w : E}
    (hw : ∀ m : PeriodicFrequency ι, ‖w‖ ≤ K * ‖z + periodicFrequencyVector m‖) :
    |∑' m : PeriodicFrequency ι,
        iteratedFDeriv ℝ n (periodicProfile c s S) (z + periodicFrequencyVector m) (fun _ => w)| ≤
      c * sourceRieszGaussianDerivativeConstant n * (K : ℝ) ^ n *
        ((2 : ℝ) ^ s * periodicProfileSum 1 s (Ioc 0 (2 * η)) z) := by
  obtain ⟨r, hr, -, hk⟩ := periodicProfile_translate_local_bounds c s η hc hs hη S hSm hS z hz
  obtain ⟨u, hu, hub⟩ := hk n
  have hsumD : Summable (fun m : PeriodicFrequency ι =>
      iteratedFDeriv ℝ n (periodicProfile c s S) (z + periodicFrequencyVector m)) :=
    Summable.of_norm_bounded hu (fun m => hub m z (mem_ball_self hr))
  rw [← ContinuousMultilinearMap.tsum_eval hsumD]
  exact periodicProfileSum_transport_bound n c s η hc hs hη S hSm hS K hz hw

/-- Short transport bound `|κ^{short}_η| ≤ A_n K^n f_{2η}`. -/
theorem periodicRieszShortTransport_bound (n : ℕ) (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    |periodicRieszShortTransport n s η v p| ≤ sourceRieszGaussianDerivativeConstant n * (2 : ℝ) ^ s *
      (K : ℝ) ^ n * periodicRieszShortSum s (2 * η) (periodicCenteredLift (p.1 - p.2)) := by
  have hc0 := (periodicRieszSmoothCoeff_pos (ι := ι) s hs).le
  have hCn := (sourceRieszGaussianDerivativeConstant_pos n).le
  by_cases hp : p.1 = p.2
  · simp only [periodicRieszShortTransport, ite_eq_left hp, abs_zero]
    have := periodicRieszShortSum_nonneg s (2 * η) hs (periodicCenteredLift (p.1 - p.2))
    positivity
  simp only [periodicRieszShortTransport, ite_eq_right hp]
  have hsub : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
  have hz := periodicCenteredLift_mem_offLattice (ι := ι) hsub
  have hw : ∀ m : PeriodicFrequency ι, ‖v p.1 - v p.2‖ ≤
      K * ‖periodicCenteredLift (p.1 - p.2) + periodicFrequencyVector m‖ :=
    fun m => norm_sub_le_of_lipschitz hv p.1 p.2 m
  have h := periodicProfileSum_transport_bound_scalar n _ s η hc0 hs hη (Ioc 0 η) measurableSet_Ioc
    (subset_refl _) K hz hw
  refine h.trans (le_of_eq ?_)
  unfold periodicRieszShortSum
  rw [show periodicProfileSum (periodicRieszSmoothCoeff ι s) s (Ioc 0 (2 * η)) (periodicCenteredLift (p.1 - p.2)) =
      periodicRieszSmoothCoeff ι s * periodicProfileSum 1 s (Ioc 0 (2 * η)) (periodicCenteredLift (p.1 - p.2)) by
    rw [periodicProfileSum_const_mul, mul_one]]
  ring


/-- Bound of the derivative of the smooth long kernel against a transported vector. -/
lemma periodicRieszLongKernel_apply_bound (n : ℕ) (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    |iteratedFDeriv ℝ n (periodicRieszLongKernel (ι := ι) s (periodicHeatCut periodicRieszTau))
      (periodicCenteredLift (p.1 - p.2)) (fun _ => v p.1 - v p.2)| ≤
      periodicRieszLongBound (ι := ι) s n * (Fintype.card ι : ℝ) ^ n * (K : ℝ) ^ n := by
  refine (norm_apply_const_le _ (v p.1 - v p.2)).trans ?_
  have hL := norm_iteratedFDeriv_periodicRieszLongKernel_le (ι := ι) s (periodicHeatCut periodicRieszTau)
    hs hs2 (periodicHeatCut_pos periodicRieszTau_pos) n (periodicCenteredLift (p.1 - p.2))
  have hL' : ‖iteratedFDeriv ℝ n (periodicRieszLongKernel (ι := ι) s (periodicHeatCut periodicRieszTau))
      (periodicCenteredLift (p.1 - p.2))‖ ≤ periodicRieszLongBound (ι := ι) s n := hL
  have hw0 : ‖v p.1 - v p.2‖ ≤ K * Fintype.card ι := by
    have := norm_sub_le_of_lipschitz hv p.1 p.2 0
    simp only [periodicFrequencyVector_zero, add_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left (norm_periodicCenteredLift_le _) K.coe_nonneg)
  calc _ ≤ periodicRieszLongBound (ι := ι) s n * ((K : ℝ) * Fintype.card ι) ^ n :=
        mul_le_mul hL' (pow_le_pow_left₀ (norm_nonneg _) hw0 n) (by positivity)
          (periodicRieszLongBound_nonneg s hs n)
    _ = _ := by rw [mul_pow]; ring

/-- Long transport bound uniform in the scale. -/
theorem periodicRieszLongTransport_bound (n : ℕ) (s η : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hητ : η ≤ periodicRieszTau)
    {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    |periodicRieszLongTransport n s η v p| ≤ (K : ℝ) ^ n *
      (sourceRieszGaussianDerivativeConstant n * (2 : ℝ) ^ s *
          periodicRieszMajorant s (periodicCenteredLift (p.1 - p.2)) +
        periodicRieszLongBound (ι := ι) s n * (Fintype.card ι : ℝ) ^ n) := by
  have hc0 := (periodicRieszSmoothCoeff_pos (ι := ι) s hs).le
  have hCn := (sourceRieszGaussianDerivativeConstant_pos n).le
  have hτ := periodicRieszTau_pos
  by_cases hp : p.1 = p.2
  · simp only [periodicRieszLongTransport, ite_eq_left hp, abs_zero]
    have h1 := periodicRieszMajorant_nonneg s hs (periodicCenteredLift (p.1 - p.2))
    have h2 := periodicRieszLongBound_nonneg (ι := ι) s hs n
    positivity
  simp only [periodicRieszLongTransport, ite_eq_right hp]
  have hsub : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
  have hz := periodicCenteredLift_mem_offLattice (ι := ι) hsub
  have hw : ∀ m : PeriodicFrequency ι, ‖v p.1 - v p.2‖ ≤
      K * ‖periodicCenteredLift (p.1 - p.2) + periodicFrequencyVector m‖ :=
    fun m => norm_sub_le_of_lipschitz hv p.1 p.2 m
  have hband : Ioc η periodicRieszTau ⊆ Ioc 0 periodicRieszTau := fun t ht => ⟨lt_of_lt_of_le hη ht.1.le, ht.2⟩
  have h1 := periodicProfileSum_transport_bound_scalar n _ s periodicRieszTau hc0 hs hτ (Ioc η periodicRieszTau)
    measurableSet_Ioc hband K hz hw
  rw [periodicRieszTau_double] at h1
  have h2 := periodicRieszLongKernel_apply_bound n s hs hs2 hv p
  refine (abs_add_le _ _).trans ?_
  have h3 : periodicRieszMajorant s (periodicCenteredLift (p.1 - p.2)) =
      periodicRieszSmoothCoeff ι s * periodicProfileSum 1 s (Ioc 0 1) (periodicCenteredLift (p.1 - p.2)) := by
    unfold periodicRieszMajorant
    rw [periodicProfileSum_const_mul, mul_one]
  calc _ ≤ periodicRieszSmoothCoeff ι s * sourceRieszGaussianDerivativeConstant n * (K : ℝ) ^ n *
        ((2 : ℝ) ^ s * periodicProfileSum 1 s (Ioc 0 1) (periodicCenteredLift (p.1 - p.2))) +
      periodicRieszLongBound (ι := ι) s n * (Fintype.card ι : ℝ) ^ n * (K : ℝ) ^ n := add_le_add h1 h2
    _ = _ := by rw [h3]; ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicRieszShortTransport_bound
#print axioms DGRHS.Periodic.periodicRieszLongTransport_bound
