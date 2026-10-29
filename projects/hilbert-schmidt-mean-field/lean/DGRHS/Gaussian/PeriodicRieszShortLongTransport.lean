import DGRHS.Gaussian.PeriodicRieszTransportBounds

/-!
Packet P9h, unit 2 (part 13): short/long splitting of the torus transport kernel at the scale `η`.

For `0 < η ≤ τ₀ = 1/2` and `n ≥ 1`:
`κ_n = κ^{short}_η + κ^{long}_η` pointwise, where `κ^{short}_η` is the lattice sum of the derivatives of
the scale-`(0,η]` profile and `κ^{long}_η` the lattice sum of the derivatives of the band `(η,τ₀]`
profile plus the derivative of the smooth long kernel.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Short transport kernel at scale `η`. -/
def periodicRieszShortTransport (n : ℕ) (s η : ℝ) (v : PeriodicTorus ι → E)
    (p : PeriodicTorus ι × PeriodicTorus ι) : ℝ :=
  if p.1 = p.2 then 0 else
    ∑' m : PeriodicFrequency ι, iteratedFDeriv ℝ n
      (periodicProfile (periodicRieszSmoothCoeff ι s) s (Ioc 0 η))
      (periodicCenteredLift (p.1 - p.2) + periodicFrequencyVector m) (fun _ => v p.1 - v p.2)

/-- Long transport kernel at scale `η`. -/
def periodicRieszLongTransport (n : ℕ) (s η : ℝ) (v : PeriodicTorus ι → E)
    (p : PeriodicTorus ι × PeriodicTorus ι) : ℝ :=
  if p.1 = p.2 then 0 else
    (∑' m : PeriodicFrequency ι, iteratedFDeriv ℝ n
      (periodicProfile (periodicRieszSmoothCoeff ι s) s (Ioc η periodicRieszTau))
      (periodicCenteredLift (p.1 - p.2) + periodicFrequencyVector m) (fun _ => v p.1 - v p.2)) +
    iteratedFDeriv ℝ n (periodicRieszLongKernel (ι := ι) s (periodicHeatCut periodicRieszTau))
      (periodicCenteredLift (p.1 - p.2)) (fun _ => v p.1 - v p.2)

/-- The derivatives of a profile at a point are additive in the (disjoint) scale sets. -/
lemma periodicProfile_iteratedFDeriv_union (c s : ℝ) (hs : 0 < s) (n : ℕ) {A B : Set ℝ}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hA : A ⊆ Ioi 0) (hB : B ⊆ Ioi 0)
    (hdisj : Disjoint A B) {a : E} (ha : a ≠ 0) :
    iteratedFDeriv ℝ n (periodicProfile c s (A ∪ B)) a =
      iteratedFDeriv ℝ n (periodicProfile c s A) a + iteratedFDeriv ℝ n (periodicProfile c s B) a := by
  have hAB : A ∪ B ⊆ Ioi 0 := union_subset hA hB
  rw [periodicProfile_iteratedFDeriv_formula c s _ (hAm.union hBm) hAB hs n ha,
    periodicProfile_iteratedFDeriv_formula c s _ hAm hA hs n ha,
    periodicProfile_iteratedFDeriv_formula c s _ hBm hB hs n ha, ← smul_add]
  congr 1
  rw [setIntegral_union hdisj hBm (integrable_sourceRieszGaussian_scale_on n s A hAm hA hs ha)
    (integrable_sourceRieszGaussian_scale_on n s B hBm hB hs ha)]


/-- Scalar summability of the transported profile derivatives over the lattice. -/
lemma summable_profile_transport_apply (n : ℕ) (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (S : Set ℝ) (hSm : MeasurableSet S) (hS : S ⊆ Ioc 0 η) {z : E}
    (hz : z ∈ (periodicOffLattice : Set E)) (w : E) :
    Summable fun m : PeriodicFrequency ι =>
      iteratedFDeriv ℝ n (periodicProfile c s S) (z + periodicFrequencyVector m) (fun _ => w) := by
  obtain ⟨r, hr, -, hk⟩ := periodicProfile_translate_local_bounds c s η hc hs hη S hSm hS z hz
  obtain ⟨u, hu, hub⟩ := hk n
  refine Summable.of_norm_bounded (hu.mul_right (‖w‖ ^ n)) (fun m => ?_)
  rw [Real.norm_eq_abs]
  exact (norm_apply_const_le _ w).trans (mul_le_mul_of_nonneg_right (hub m z (mem_ball_self hr))
    (by positivity))

lemma periodicRieszTau_le_double_bound : (1 / 2 : ℝ) = periodicRieszTau := rfl

lemma periodicRieszTransportKernel_split (n : ℕ) (hn : 1 ≤ n) (s η : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hητ : η ≤ periodicRieszTau)
    (v : PeriodicTorus ι → E) (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicRieszTransportKernel n s v p =
      periodicRieszShortTransport n s η v p + periodicRieszLongTransport n s η v p := by
  by_cases hp : p.1 = p.2
  · simp [periodicRieszTransportKernel, periodicRieszShortTransport, periodicRieszLongTransport, hp]
  simp only [periodicRieszTransportKernel, periodicRieszShortTransport, periodicRieszLongTransport,
    ite_eq_right hp]
  have hsub : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
  have hz := periodicCenteredLift_mem_offLattice (ι := ι) hsub
  set z := periodicCenteredLift (p.1 - p.2) with hzdef
  set w := v p.1 - v p.2 with hwdef
  have hc0 := (periodicRieszSmoothCoeff_pos (ι := ι) s hs).le
  have hτ := periodicRieszTau_pos
  set cF := periodicRieszSmoothCoeff ι s with hcF
  rw [periodicRieszSmooth_iteratedFDeriv s hs hs2 n hn hz, add_apply]
  -- summability of the full derivative series
  obtain ⟨r, hr, -, hk⟩ := periodicProfile_translate_local_bounds cF s periodicRieszTau hc0 hs hτ
    (Ioc 0 periodicRieszTau) measurableSet_Ioc (subset_refl _) z hz
  obtain ⟨u, hu, hub⟩ := hk n
  have hsumD : Summable (fun m : PeriodicFrequency ι =>
      iteratedFDeriv ℝ n (periodicProfile cF s (Ioc 0 periodicRieszTau)) (z + periodicFrequencyVector m)) :=
    Summable.of_norm_bounded hu (fun m => hub m z (mem_ball_self hr))
  rw [ContinuousMultilinearMap.tsum_eval hsumD]
  have hunion : Ioc 0 η ∪ Ioc η periodicRieszTau = Ioc 0 periodicRieszTau := Ioc_union_Ioc_eq_Ioc hη.le hητ
  have hterm : ∀ m : PeriodicFrequency ι,
      iteratedFDeriv ℝ n (periodicProfile cF s (Ioc 0 periodicRieszTau)) (z + periodicFrequencyVector m) (fun _ => w) =
        iteratedFDeriv ℝ n (periodicProfile cF s (Ioc 0 η)) (z + periodicFrequencyVector m) (fun _ => w) +
        iteratedFDeriv ℝ n (periodicProfile cF s (Ioc η periodicRieszTau)) (z + periodicFrequencyVector m) (fun _ => w) := by
    intro m
    rw [← hunion, periodicProfile_iteratedFDeriv_union cF s hs n measurableSet_Ioc measurableSet_Ioc
      (fun t ht => ht.1) (fun t ht => lt_of_lt_of_le hη ht.1.le)
      (Ioc_disjoint_Ioc_of_le (le_refl η)) (hz m), add_apply]
  have hs1 := summable_profile_transport_apply n cF s η hc0 hs hη (Ioc 0 η) measurableSet_Ioc
    (subset_refl _) hz w
  have hs2' := summable_profile_transport_apply n cF s periodicRieszTau hc0 hs hτ (Ioc η periodicRieszTau)
    measurableSet_Ioc (fun t ht => ⟨lt_of_lt_of_le hη ht.1.le, ht.2⟩) hz w
  rw [tsum_congr hterm, hs1.tsum_add hs2']
  ring

end DGRHS.Periodic
