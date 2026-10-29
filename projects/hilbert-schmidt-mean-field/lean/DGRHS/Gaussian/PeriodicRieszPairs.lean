import DGRHS.Gaussian.PeriodicRieszShortLongBounds
import DGRHS.Gaussian.PeriodicRieszDiagonalCap

/-!
Packet P9h, unit 2 (part 16): pair kernels on `𝕋^d × 𝕋^d` (full, short, long) of the periodic Riesz
kernel and their bounds: the decomposition `W = f_η + g_η`, positivity of `f_η`, and the diagonal caps
`|g_η| ≤ C η^{-s}`, `|κ^{long}_η| ≤ C K^n η^{-s}`.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The (smooth) full pair kernel on the torus, totalized by `0` on the diagonal. -/
def periodicRieszPair (s : ℝ) (p : PeriodicTorus ι × PeriodicTorus ι) : ℝ :=
  if p.1 = p.2 then 0 else periodicRieszSmooth s (periodicCenteredLift (p.1 - p.2))

/-- The short pair kernel `f_η` (positive). -/
def periodicRieszShortPair (s η : ℝ) (p : PeriodicTorus ι × PeriodicTorus ι) : ℝ :=
  if p.1 = p.2 then 0 else periodicRieszShortSum s η (periodicCenteredLift (p.1 - p.2))

/-- The long pair kernel `g_η = W - f_η`: the band `(η,τ₀]` lattice profile sum plus the smooth long
kernel minus the constant. -/
def periodicRieszLongPair (s η : ℝ) (p : PeriodicTorus ι × PeriodicTorus ι) : ℝ :=
  if p.1 = p.2 then 0 else
    periodicProfileSum (periodicRieszSmoothCoeff ι s) s (Ioc η periodicRieszTau)
        (periodicCenteredLift (p.1 - p.2)) +
      periodicRieszLongKernel s (periodicHeatCut periodicRieszTau) (periodicCenteredLift (p.1 - p.2)) -
      periodicRieszMellinFactor ι s * (periodicHeatCut periodicRieszTau) ^ (((Fintype.card ι : ℝ) - s) / 2) /
        (((Fintype.card ι : ℝ) - s) / 2)

lemma periodicProfile_union (c s : ℝ) (hs : 0 < s) {A B : Set ℝ} (hAm : MeasurableSet A)
    (hBm : MeasurableSet B) (hA : A ⊆ Ioi 0) (hB : B ⊆ Ioi 0) (hdisj : Disjoint A B) {y : E}
    (hy : y ≠ 0) :
    periodicProfile c s (A ∪ B) y = periodicProfile c s A y + periodicProfile c s B y := by
  have hi : IntegrableOn (fun t : ℝ => t ^ (-s - 1) * sourceRieszGaussianScale t y) (Ioi 0) :=
    DGRHS.Gaussian.integrableOn_gaussianRieszEuclidean_full_scale s hs y hy
  unfold periodicProfile
  rw [setIntegral_union hdisj hBm (hi.mono_set hA) (hi.mono_set hB), mul_add]

lemma periodicProfileSum_union (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η) {A B : Set ℝ}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hA : A ⊆ Ioc 0 η) (hB : B ⊆ Ioc 0 η)
    (hdisj : Disjoint A B) {z : E} (hz : z ∈ (periodicOffLattice : Set E)) :
    periodicProfileSum c s (A ∪ B) z = periodicProfileSum c s A z + periodicProfileSum c s B z := by
  have hA0 : A ⊆ Ioi 0 := fun t ht => (hA ht).1
  have hB0 : B ⊆ Ioi 0 := fun t ht => (hB ht).1
  have hAB : A ∪ B ⊆ Ioc 0 η := union_subset hA hB
  have h1 := summable_periodicProfile_translate c s η hc hs hη A hAm hA hz
  have h2 := summable_periodicProfile_translate c s η hc hs hη B hBm hB hz
  unfold periodicProfileSum
  rw [← h1.tsum_add h2]
  exact tsum_congr fun m => periodicProfile_union c s hs hAm hBm hA0 hB0 hdisj (hz m)

lemma periodicRieszPair_split (s η : ℝ) (hs : 0 < s) (hη : 0 < η) (hητ : η ≤ periodicRieszTau)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicRieszPair s p = periodicRieszShortPair s η p + periodicRieszLongPair s η p := by
  by_cases hp : p.1 = p.2
  · simp [periodicRieszPair, periodicRieszShortPair, periodicRieszLongPair, hp]
  simp only [periodicRieszPair, periodicRieszShortPair, periodicRieszLongPair, ite_eq_right hp]
  have hsub : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
  have hz := periodicCenteredLift_mem_offLattice (ι := ι) hsub
  have hc0 := (periodicRieszSmoothCoeff_pos (ι := ι) s hs).le
  have hunion : Ioc 0 η ∪ Ioc η periodicRieszTau = Ioc 0 periodicRieszTau := Ioc_union_Ioc_eq_Ioc hη.le hητ
  have h := periodicProfileSum_union (periodicRieszSmoothCoeff ι s) s periodicRieszTau hc0 hs
    periodicRieszTau_pos (A := Ioc 0 η) (B := Ioc η periodicRieszTau) measurableSet_Ioc measurableSet_Ioc
    (fun t ht => ⟨ht.1, ht.2.trans hητ⟩) (fun t ht => ⟨lt_of_lt_of_le hη ht.1.le, ht.2⟩)
    (Ioc_disjoint_Ioc_of_le (le_refl η)) hz
  rw [hunion] at h
  unfold periodicRieszSmooth
  rw [periodicRieszSmoothLift_eq, h]
  unfold periodicRieszShortSum
  ring


lemma periodicProfile_transport_bound_raw (n : ℕ) (c s : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (S : Set ℝ)
    (hSm : MeasurableSet S) (hS0 : S ⊆ Ioi 0) (K : ℝ≥0) {a w : E} (ha : a ≠ 0)
    (hw : ‖w‖ ≤ K * ‖a‖) :
    |iteratedFDeriv ℝ n (periodicProfile c s S) a (fun _ => w)| ≤
      c * sourceRieszGaussianDerivativeConstant n * (K : ℝ) ^ n *
        ∫ t in S, t ^ (-s - 1) * Real.exp (-‖a‖ ^ 2 / (8 * t ^ 2)) := by
  have hlip := periodicRankOneField_lipschitz ha hw
  have h := sourceRieszGaussian_scale_integral_transport_bound n c s S hc hs hSm hS0 hlip
    (x := a) (y := 0) ha
  simp only [sub_zero, map_zero, periodicRankOneField_self ha] at h
  exact h

lemma periodicRieszLongPair_cap (s η : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hη : 0 < η) (hητ : η ≤ periodicRieszTau) (p : PeriodicTorus ι × PeriodicTorus ι) :
    |periodicRieszLongPair s η p| ≤
      periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι * (η ^ (-s) / s) +
        periodicRieszLongBound (ι := ι) s 0 +
        periodicRieszMellinFactor ι s * (periodicHeatCut periodicRieszTau) ^ (((Fintype.card ι : ℝ) - s) / 2) /
          (((Fintype.card ι : ℝ) - s) / 2) := by
  have hc0 := (periodicRieszSmoothCoeff_pos (ι := ι) s hs).le
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hF := periodicRieszMellinFactor_pos (ι := ι) s hs
  have hconst : 0 ≤ periodicRieszMellinFactor ι s * (periodicHeatCut periodicRieszTau) ^ (((Fintype.card ι : ℝ) - s) / 2) /
      (((Fintype.card ι : ℝ) - s) / 2) := by
    have := periodicHeatCut_pos periodicRieszTau_pos
    have : 0 < ((Fintype.card ι : ℝ) - s) / 2 := by linarith
    positivity
  have hB0 := periodicRieszLongBound_nonneg (ι := ι) s hs 0
  have hΛ := periodicLatticeGaussConst_pos (ι := ι)
  have hcap0 : 0 ≤ periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι * (η ^ (-s) / s) := by
    have := Real.rpow_nonneg hη.le (-s); positivity
  by_cases hp : p.1 = p.2
  · simp only [periodicRieszLongPair, ite_eq_left hp, abs_zero]
    linarith
  simp only [periodicRieszLongPair, ite_eq_right hp]
  have hsub : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
  have hz := periodicCenteredLift_mem_offLattice (ι := ι) hsub
  set z := periodicCenteredLift (p.1 - p.2) with hzdef
  have hzc : ∀ i, |z i| ≤ 1 / 2 := fun i => periodicCenteredLift_abs_le _ i
  obtain ⟨hsum, hbound⟩ := periodic_band_lattice_integral_le 2 (by norm_num) (by norm_num) s η hs hη z hzc hz
  have hband0 : 0 ≤ periodicProfileSum (periodicRieszSmoothCoeff ι s) s (Ioc η periodicRieszTau) z := by
    unfold periodicProfileSum
    exact tsum_nonneg fun m => periodicProfile_nonneg _ s _ hc0 measurableSet_Ioc
      (fun t ht => lt_of_lt_of_le hη ht.1.le) _
  have hband : periodicProfileSum (periodicRieszSmoothCoeff ι s) s (Ioc η periodicRieszTau) z ≤
      periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι * (η ^ (-s) / s) := by
    unfold periodicProfileSum periodicProfile
    rw [tsum_mul_left]
    have hI : ∀ m : PeriodicFrequency ι, ∫ t in Ioc η periodicRieszTau,
        t ^ (-s - 1) * sourceRieszGaussianScale t (z + periodicFrequencyVector m) ≤
        ∫ t in Ioc η (1 / 2 : ℝ), t ^ (-s - 1) *
          Real.exp (-‖z + periodicFrequencyVector m‖ ^ 2 / (2 * t ^ 2)) := fun m => le_of_eq rfl
    have h1 : ∑' m : PeriodicFrequency ι, (∫ t in Ioc η periodicRieszTau,
        t ^ (-s - 1) * sourceRieszGaussianScale t (z + periodicFrequencyVector m)) ≤
        periodicLatticeGaussConst ι * (η ^ (-s) / s) := hbound
    calc _ ≤ periodicRieszSmoothCoeff ι s * (periodicLatticeGaussConst ι * (η ^ (-s) / s)) :=
          mul_le_mul_of_nonneg_left h1 hc0
      _ = _ := by ring
  have hL : |periodicRieszLongKernel s (periodicHeatCut periodicRieszTau) z| ≤
      periodicRieszLongBound (ι := ι) s 0 := by
    have := norm_iteratedFDeriv_periodicRieszLongKernel_le (ι := ι) s (periodicHeatCut periodicRieszTau)
      hs hs2 (periodicHeatCut_pos periodicRieszTau_pos) 0 z
    simpa [norm_iteratedFDeriv_zero, periodicRieszLongBound] using this
  calc _ ≤ |periodicProfileSum (periodicRieszSmoothCoeff ι s) s (Ioc η periodicRieszTau) z +
        periodicRieszLongKernel s (periodicHeatCut periodicRieszTau) z| +
      |periodicRieszMellinFactor ι s * (periodicHeatCut periodicRieszTau) ^ (((Fintype.card ι : ℝ) - s) / 2) /
        (((Fintype.card ι : ℝ) - s) / 2)| := abs_sub _ _
    _ ≤ (periodicProfileSum (periodicRieszSmoothCoeff ι s) s (Ioc η periodicRieszTau) z +
        |periodicRieszLongKernel s (periodicHeatCut periodicRieszTau) z|) +
      periodicRieszMellinFactor ι s * (periodicHeatCut periodicRieszTau) ^ (((Fintype.card ι : ℝ) - s) / 2) /
        (((Fintype.card ι : ℝ) - s) / 2) := by
        rw [abs_of_nonneg hconst]
        gcongr
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_nonneg hband0]
    _ ≤ _ := by linarith


/-- Diagonal cap of the long transport kernel. -/
lemma periodicRieszLongTransport_cap (n : ℕ) (s η : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hητ : η ≤ periodicRieszTau)
    {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    |periodicRieszLongTransport n s η v p| ≤ (K : ℝ) ^ n *
      (periodicRieszSmoothCoeff ι s * sourceRieszGaussianDerivativeConstant n *
          periodicLatticeGaussConst ι * (η ^ (-s) / s) +
        periodicRieszLongBound (ι := ι) s n * (Fintype.card ι : ℝ) ^ n) := by
  have hc0 := (periodicRieszSmoothCoeff_pos (ι := ι) s hs).le
  have hCn := (sourceRieszGaussianDerivativeConstant_pos n).le
  have hτ := periodicRieszTau_pos
  have hΛ := periodicLatticeGaussConst_pos (ι := ι)
  have hB := periodicRieszLongBound_nonneg (ι := ι) s hs n
  have hη' : 0 ≤ η ^ (-s) := Real.rpow_nonneg hη.le _
  by_cases hp : p.1 = p.2
  · simp only [periodicRieszLongTransport, ite_eq_left hp, abs_zero]
    positivity
  simp only [periodicRieszLongTransport, ite_eq_right hp]
  have hsub : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
  have hz := periodicCenteredLift_mem_offLattice (ι := ι) hsub
  set z := periodicCenteredLift (p.1 - p.2) with hzdef
  set w := v p.1 - v p.2 with hwdef
  have hzc : ∀ i, |z i| ≤ 1 / 2 := fun i => periodicCenteredLift_abs_le _ i
  have hw : ∀ m : PeriodicFrequency ι, ‖w‖ ≤ K * ‖z + periodicFrequencyVector m‖ :=
    fun m => norm_sub_le_of_lipschitz hv p.1 p.2 m
  have hband : Ioc η periodicRieszTau ⊆ Ioc 0 periodicRieszTau :=
    fun t ht => ⟨lt_of_lt_of_le hη ht.1.le, ht.2⟩
  obtain ⟨hsum8, hbound8⟩ := periodic_band_lattice_integral_le 8 (by norm_num) le_rfl s η hs hη z hzc hz
  have hsumA := summable_profile_transport_apply n (periodicRieszSmoothCoeff ι s) s periodicRieszTau hc0 hs hτ
    (Ioc η periodicRieszTau) measurableSet_Ioc hband hz w
  have hterm : ∀ m : PeriodicFrequency ι,
      |iteratedFDeriv ℝ n (periodicProfile (periodicRieszSmoothCoeff ι s) s (Ioc η periodicRieszTau))
          (z + periodicFrequencyVector m) (fun _ => w)| ≤
        periodicRieszSmoothCoeff ι s * sourceRieszGaussianDerivativeConstant n * (K : ℝ) ^ n *
          ∫ t in Ioc η (1 / 2 : ℝ), t ^ (-s - 1) *
            Real.exp (-‖z + periodicFrequencyVector m‖ ^ 2 / (8 * t ^ 2)) := fun m =>
    periodicProfile_transport_bound_raw n _ s hc0 hs (Ioc η periodicRieszTau) measurableSet_Ioc
      (fun t ht => lt_of_lt_of_le hη ht.1.le) K (hz m) (hw m)
  have hsum3 := hsum8.mul_left (periodicRieszSmoothCoeff ι s * sourceRieszGaussianDerivativeConstant n * (K : ℝ) ^ n)
  have hsn : Summable (fun m : PeriodicFrequency ι =>
      |iteratedFDeriv ℝ n (periodicProfile (periodicRieszSmoothCoeff ι s) s (Ioc η periodicRieszTau))
          (z + periodicFrequencyVector m) (fun _ => w)|) :=
    hsum3.of_nonneg_of_le (fun m => abs_nonneg _) hterm
  have h1 : |∑' m : PeriodicFrequency ι,
      iteratedFDeriv ℝ n (periodicProfile (periodicRieszSmoothCoeff ι s) s (Ioc η periodicRieszTau))
          (z + periodicFrequencyVector m) (fun _ => w)| ≤
      periodicRieszSmoothCoeff ι s * sourceRieszGaussianDerivativeConstant n * (K : ℝ) ^ n *
        (periodicLatticeGaussConst ι * (η ^ (-s) / s)) := by
    calc _ ≤ ∑' m : PeriodicFrequency ι, |iteratedFDeriv ℝ n
          (periodicProfile (periodicRieszSmoothCoeff ι s) s (Ioc η periodicRieszTau))
          (z + periodicFrequencyVector m) (fun _ => w)| := by
          simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun m : PeriodicFrequency ι =>
            iteratedFDeriv ℝ n (periodicProfile (periodicRieszSmoothCoeff ι s) s (Ioc η periodicRieszTau))
              (z + periodicFrequencyVector m) (fun _ => w)) (by simpa only [Real.norm_eq_abs] using hsn)
      _ ≤ ∑' m : PeriodicFrequency ι, periodicRieszSmoothCoeff ι s * sourceRieszGaussianDerivativeConstant n *
          (K : ℝ) ^ n * ∫ t in Ioc η (1 / 2 : ℝ), t ^ (-s - 1) *
            Real.exp (-‖z + periodicFrequencyVector m‖ ^ 2 / (8 * t ^ 2)) := hsn.tsum_le_tsum hterm hsum3
      _ = periodicRieszSmoothCoeff ι s * sourceRieszGaussianDerivativeConstant n * (K : ℝ) ^ n *
          ∑' m : PeriodicFrequency ι, ∫ t in Ioc η (1 / 2 : ℝ), t ^ (-s - 1) *
            Real.exp (-‖z + periodicFrequencyVector m‖ ^ 2 / (8 * t ^ 2)) := by rw [tsum_mul_left]
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound8 (by positivity)
  have h2 := periodicRieszLongKernel_apply_bound n s hs hs2 hv p
  refine (abs_add_le _ _).trans ?_
  calc _ ≤ periodicRieszSmoothCoeff ι s * sourceRieszGaussianDerivativeConstant n * (K : ℝ) ^ n *
        (periodicLatticeGaussConst ι * (η ^ (-s) / s)) +
      periodicRieszLongBound (ι := ι) s n * (Fintype.card ι : ℝ) ^ n * (K : ℝ) ^ n := add_le_add h1 h2
    _ = _ := by ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicRieszLongTransport_cap
