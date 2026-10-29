import DGRHS.Gaussian.PeriodicRieszEntropicTransfer
import DGRHS.Gaussian.PeriodicLogEntropicTransfer
import DGRHS.Gaussian.GaussianRieszPhysicalPotential
import DGRHS.Gaussian.GaussianLogScaleSplit

/-!
Packet P11a, unit 2 (sign lemma): on the torus the smooth pair representatives of the periodic Riesz
and LOG kernels are unbounded above on collision-free pairs, hence the modulated energy `F_2` is
unbounded above on collision-free two-particle configurations (torus versions of
`sourceRiesz_twoParticle_energy_unbounded_collisionFree` and
`sourceLog_twoParticle_energy_unbounded_collisionFree`).  This derives the sign `0 ≤ C_pw` of
Corollary 7.3 (TeX 3547-3565) instead of assuming it.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal Topology
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-! ### Two-particle energy -/

lemma offDiagonalSum_two {S : Type*} (W : S → S → ℝ) (x y : S) :
    DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry W) ![x, y] = W x y + W y x := by
  classical
  have hdiag : (Finset.univ : Finset (Fin 2)).offDiag = {(0, 1), (1, 0)} := by
    ext ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp
  unfold DGRHS.CanonicalVariance.offDiagonalSum
  rw [hdiag]
  simp [Function.uncurry]

/-- Lower bound of the two-particle modulated energy by the pair kernel, a potential bound and an
interaction lower bound. -/
lemma periodic_twoParticle_energy_lower (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (k : PeriodicTorus ι × PeriodicTorus ι → ℝ) (hk : ∀ a b, k (a, b) = k (b, a))
    (pk I0 : ℝ) (hpot : ∀ x, |DGRHS.potential μ (fun a b => k (a, b)) x| ≤ pk)
    (hI : I0 ≤ DGRHS.interactionEnergy μ (fun a b => k (a, b))) (x y : PeriodicTorus ι) :
    k (x, y) / 4 - pk + I0 ≤ DGRHS.CLT.sourceCanonicalModulatedEnergy (hoeffdingCentered μ k)
      (DGRHS.potential μ (fun a b => k (a, b)))
      (DGRHS.interactionEnergy μ (fun a b => k (a, b))) 2 ![x, y] := by
  have hraw := DGRHS.CLT.sourceCanonicalModulatedEnergy_raw μ (fun a b => k (a, b))
    (fun a b => hk a b) 2 (by norm_num) ![x, y]
  have hsum := offDiagonalSum_two (fun a b => k (a, b)) x y
  change k (x, y) / 4 - pk + I0 ≤ DGRHS.CLT.sourceCanonicalModulatedEnergy
    (fun p => DGRHS.centeredKernel μ (fun a b => k (a, b)) p.1 p.2)
    (DGRHS.potential μ (fun a b => k (a, b)))
    (DGRHS.interactionEnergy μ (fun a b => k (a, b))) 2 ![x, y]
  rw [hraw, hsum, ← hk y x]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1 := (abs_le.mp (hpot x)).2
  have h2 := (abs_le.mp (hpot y)).2
  norm_num
  linarith

lemma periodicTwoParticle_collisionFree (x y : PeriodicTorus ι) (hxy : x ≠ y) :
    ∀ i j : Fin 2, i ≠ j → (![x, y] : Fin 2 → PeriodicTorus ι) i ≠ (![x, y] : Fin 2 → PeriodicTorus ι) j := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · simpa using hxy
  · simpa using hxy.symm
  · exact absurd rfl hij

/-! ### Lattice sums dominate their terms -/

lemma periodicProfileSum_ge_term (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η) (y0 : E)
    (hz : y0 ∈ (periodicOffLattice : Set E)) (m : PeriodicFrequency ι) :
    periodicProfile c s (Ioc 0 η) (y0 + periodicFrequencyVector m) ≤
      periodicProfileSum c s (Ioc 0 η) y0 := by
  obtain ⟨r, hr, -, hk⟩ := periodicProfile_translate_local_bounds c s η hc hs hη (Ioc 0 η)
    measurableSet_Ioc (subset_refl _) y0 hz
  obtain ⟨u, hu, hub⟩ := hk 0
  have hsum : Summable (fun m : PeriodicFrequency ι =>
      periodicProfile c s (Ioc 0 η) (y0 + periodicFrequencyVector m)) := by
    refine Summable.of_norm_bounded hu (fun m => ?_)
    have := hub m y0 (mem_ball_self hr)
    simpa only [norm_iteratedFDeriv_zero] using this
  unfold periodicProfileSum
  exact hsum.le_tsum m (fun j _ => periodicProfile_nonneg c s _ hc measurableSet_Ioc
    (fun t ht => ht.1) _)

lemma gaussianLogProfileSum_ge_term (η : ℝ) (hη : 0 < η) (y0 : E)
    (hz : y0 ∈ (periodicOffLattice : Set E)) (m : PeriodicFrequency ι) :
    gaussianLogShortRange η (y0 + periodicFrequencyVector m) ≤ periodicLogProfileSum η y0 := by
  have hsum := summable_gaussianLogShortRange_translate (ι := ι) η hη hz
  unfold periodicLogProfileSum
  exact hsum.le_tsum m (fun j _ => gaussianLogShortRange_nonneg _ _)

/-! ### Points of the torus close to the origin -/

/-- The lift to the torus of a small vector along a coordinate axis. -/
def periodicSmallPoint (i : ι) (r : ℝ) : PeriodicTorus ι := periodicLift (EuclideanSpace.single i r)

lemma exists_centeredLift_lift (w : E) :
    ∃ m : PeriodicFrequency ι, periodicCenteredLift (periodicLift w) = w + periodicFrequencyVector m := by
  have h : ∀ i, ∃ n : ℤ, periodicCenteredLift (periodicLift w) i - w i = (n : ℝ) := by
    intro i
    have h1 : (((periodicCenteredLift (periodicLift w) i - w i : ℝ)) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub]
      simp only [periodicCenteredLift_apply, circleCentered_coe]
      simp [periodicLift]
    rw [AddCircle.coe_eq_zero_iff] at h1
    obtain ⟨n, hn⟩ := h1
    exact ⟨n, by simpa using hn.symm⟩
  choose m hm using h
  refine ⟨m, ?_⟩
  ext i
  simp only [PiLp.add_apply, periodicFrequencyVector_apply]
  linarith [hm i]

lemma periodicSmallPoint_ne_zero (i : ι) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    periodicSmallPoint i r ≠ 0 := by
  intro h
  have h1 := congrFun h i
  simp only [periodicSmallPoint, periodicLift, PiLp.single_apply, ite_true,
    Pi.zero_apply] at h1
  rw [AddCircle.coe_eq_zero_iff] at h1
  obtain ⟨n, hn⟩ := h1
  have hn' : (n : ℝ) = r := by simpa using hn
  have hpos : (0 : ℤ) < n := by
    have : (0 : ℝ) < (n : ℝ) := by rw [hn']; exact hr0
    exact_mod_cast this
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpos
  linarith

/-! ### Riesz: unboundedness of the smooth pair kernel -/

lemma periodicRieszPair_unbounded (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (R : ℝ) : ∃ x y : PeriodicTorus ι, x ≠ y ∧ R < periodicRieszPair s (x, y) := by
  classical
  let i : ι := Classical.arbitrary ι
  set c := periodicRieszSmoothCoeff ι s with hcdef
  have hc : 0 < c := periodicRieszSmoothCoeff_pos s hs
  have hce := gaussianRieszSourceCoefficient_pos s hs
  set e := gaussianRieszSourceCoefficient s with hedef
  have hτ := periodicRieszTau_pos
  set τ := periodicRieszTau with hτdef
  -- the cap of the long part
  set B := periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι * (τ ^ (-s) / s) +
    periodicRieszLongBound (ι := ι) s 0 +
    periodicRieszMellinFactor ι s * (periodicHeatCut periodicRieszTau) ^
      (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2) with hB
  -- target
  set Y := R + B + c / e * (e / s * τ ^ (-s)) + 1 with hY
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, Y * s * e / c ≤ r ^ (-s) :=
    (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hs)).eventually
      (Filter.eventually_ge_atTop (Y * s * e / c))
  have hrpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  have hrsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < τ := by
    have : ∀ᶠ r : ℝ in 𝓝 0, r < τ := (continuous_id.tendsto 0).eventually (gt_mem_nhds hτ)
    exact nhdsWithin_le_nhds this
  obtain ⟨r, hr, hpow, hrτ⟩ : ∃ r : ℝ, 0 < r ∧ Y * s * e / c ≤ r ^ (-s) ∧ r < τ := by
    obtain ⟨r, h1, h2, h3⟩ := (hrpos.and (hev.and hrsmall)).exists
    exact ⟨r, h1, h2, h3⟩
  have hτ1 : τ < 1 := by rw [hτdef]; unfold periodicRieszTau; norm_num
  let w : E := EuclideanSpace.single i r
  let x : PeriodicTorus ι := periodicSmallPoint i r
  have hx : x ≠ 0 := periodicSmallPoint_ne_zero i r hr (hrτ.trans hτ1)
  have hw : ‖w‖ = r := by simp [w, PiLp.norm_single, abs_of_pos hr]
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; linarith
  refine ⟨x, 0, hx, ?_⟩
  have hsplit := periodicRieszPair_split s τ hs hτ le_rfl (x, 0)
  have hlong := (abs_le.mp (periodicRieszLongPair_cap s τ hs hs2 hτ le_rfl (x, 0))).1
  have hshort : periodicRieszShortPair s τ (x, 0) = periodicRieszShortSum s τ (periodicCenteredLift x) := by
    simp [periodicRieszShortPair, ite_eq_right hx]
  -- the centred lift of `x`
  obtain ⟨m0, hm0⟩ := exists_centeredLift_lift w
  have hxlift : periodicCenteredLift x = w + periodicFrequencyVector m0 := hm0
  have hoff : periodicCenteredLift x ∈ (periodicOffLattice : Set E) :=
    periodicCenteredLift_mem_offLattice hx
  have hterm := periodicProfileSum_ge_term c s τ hc.le hs hτ (periodicCenteredLift x) hoff (-m0)
  have hw' : periodicCenteredLift x + periodicFrequencyVector (-m0) = w := by
    rw [hxlift, periodicFrequencyVector_neg']
    abel
  rw [hw'] at hterm
  have hshortsum : periodicRieszShortSum s τ (periodicCenteredLift x) =
      periodicProfileSum c s (Ioc 0 τ) (periodicCenteredLift x) := rfl
  -- lower bound of the profile
  have hprof : periodicProfile c s (Ioc 0 τ) w = c / e * gaussianRieszEuclideanShortRange s τ w := by
    unfold periodicProfile gaussianRieszEuclideanShortRange sourceRieszGaussianScale
    rw [← hedef]
    field_simp [hce.ne']
  have hrem := gaussianRieszEuclideanShortRange_eq_remainder s τ hs hτ w hw0
  have htr := gaussianRieszEuclideanTruncation_le_diagonal s τ hs hτ w
  have htr' : gaussianRieszEuclideanTruncation s τ w ≤ e / s * τ ^ (-s) :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using htr)
  have hlow : ‖w‖ ^ (-s) / s - e / s * τ ^ (-s) ≤ gaussianRieszEuclideanShortRange s τ w := by
    rw [hrem]; linarith
  rw [hw] at hlow
  have hq : Y * s * e / c ≤ r ^ (-s) := hpow
  have hmain : c / e * (r ^ (-s) / s) ≥ Y := by
    have h1 : Y ≤ c / e * (r ^ (-s) / s) := by
      have : Y * s * e / c ≤ r ^ (-s) := hq
      rw [div_le_iff₀ hc] at this
      rw [show c / e * (r ^ (-s) / s) = c * r ^ (-s) / (e * s) by field_simp]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [this]
    exact h1
  have hprof2 : c / e * (r ^ (-s) / s - e / s * τ ^ (-s)) ≤ periodicProfile c s (Ioc 0 τ) w := by
    rw [hprof]
    exact mul_le_mul_of_nonneg_left hlow (by positivity)
  have hexpand : c / e * (r ^ (-s) / s - e / s * τ ^ (-s)) =
      c / e * (r ^ (-s) / s) - c / e * (e / s * τ ^ (-s)) := by ring
  have hS : periodicProfile c s (Ioc 0 τ) w ≤ periodicRieszShortSum s τ (periodicCenteredLift x) := by
    rw [hshortsum]; exact hterm
  rw [hsplit, hshort]
  have hlong' : -B ≤ periodicRieszLongPair s τ (x, 0) := by
    have := hlong
    rw [hB]
    linarith
  linarith

/-! ### LOG: unboundedness of the smooth pair kernel -/

lemma gaussianLogShortRange_lower (η : ℝ) (hη : 0 < η) (y : E) (hy : y ≠ 0) (hr : ‖y‖ ≤ η) :
    Real.exp (-1 / 2) * (Real.log η - Real.log ‖y‖) ≤ gaussianLogShortRange η y := by
  have hr0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
  set r := ‖y‖ with hrdef
  have hi := integrableOn_gaussianLog_profile_short η r hη hr0
  have hsub : Ioc r η ⊆ Ioc 0 η := Ioc_subset_Ioc_left hr0.le
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 η)] fun t : ℝ => t⁻¹ * Real.exp (-r ^ 2 / (2 * t ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (inv_nonneg.mpr ht.1.le) (Real.exp_pos _).le
  have h1 : ∫ t in Ioc r η, t⁻¹ * Real.exp (-r ^ 2 / (2 * t ^ 2)) ≤
      ∫ t in Ioc 0 η, t⁻¹ * Real.exp (-r ^ 2 / (2 * t ^ 2)) :=
    setIntegral_mono_set hi hnn (Filter.Eventually.of_forall hsub)
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume r η := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ continuousOn_id
    intro t ht
    rw [Set.uIcc_of_le hr] at ht
    exact (lt_of_lt_of_le hr0 ht.1).ne'
  have hinvI : IntegrableOn (fun t : ℝ => t⁻¹) (Ioc r η) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mp hinv
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-1 / 2) * t⁻¹) (Ioc r η) := hinvI.const_mul _
  have hf : IntegrableOn (fun t : ℝ => t⁻¹ * Real.exp (-r ^ 2 / (2 * t ^ 2))) (Ioc r η) := hi.mono_set hsub
  have h2 : ∫ t in Ioc r η, Real.exp (-1 / 2) * t⁻¹ ≤
      ∫ t in Ioc r η, t⁻¹ * Real.exp (-r ^ 2 / (2 * t ^ 2)) := by
    refine setIntegral_mono_on hg hf measurableSet_Ioc (fun t ht => ?_)
    have ht0 : 0 < t := lt_of_lt_of_le hr0 ht.1.le
    have hexp : Real.exp (-1 / 2) ≤ Real.exp (-r ^ 2 / (2 * t ^ 2)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [ht.1, hr0]
    calc Real.exp (-1 / 2) * t⁻¹ = t⁻¹ * Real.exp (-1 / 2) := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr ht0.le)
  have h3 : ∫ t in Ioc r η, Real.exp (-1 / 2) * t⁻¹ =
      Real.exp (-1 / 2) * (Real.log η - Real.log r) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hr, integral_inv_of_pos hr0 hη,
      Real.log_div hη.ne' hr0.ne']
  unfold gaussianLogShortRange
  rw [← h3]
  exact h2.trans (h1)

lemma periodicLogPair_unbounded (R : ℝ) :
    ∃ x y : PeriodicTorus ι, x ≠ y ∧ R < periodicLogPair (x, y) := by
  classical
  let i : ι := Classical.arbitrary ι
  have hc := periodicLogSmoothCoeff_pos (ι := ι)
  set c := periodicLogSmoothCoeff ι with hcdef
  have hτ := periodicRieszTau_pos
  set τ := periodicRieszTau with hτdef
  have hτ1 : τ < 1 := by rw [hτdef]; unfold periodicRieszTau; norm_num
  set Bl := ∑' k : PeriodicFrequency ι, periodicLogLCCoeff (periodicHeatCut periodicRieszTau) k
    with hBl
  set K0 := periodicLogMellinFactor ι * (periodicHeatCut periodicRieszTau) ^ ((Fintype.card ι : ℝ) / 2) /
    ((Fintype.card ι : ℝ) / 2) with hK0
  have hex := Real.exp_pos (-1 / 2)
  set q := Real.exp (-1 / 2) with hq
  set Y := R + Bl + K0 + 1 with hY
  set L := max (Y / (q * c)) 0 with hL
  have hL0 : 0 ≤ L := le_max_right _ _
  have hLY : Y / (q * c) ≤ L := le_max_left _ _
  set r := τ * Real.exp (-L) with hrdef
  have hr : 0 < r := by positivity
  have hrτ : r ≤ τ := by
    have : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  let w : E := EuclideanSpace.single i r
  let x : PeriodicTorus ι := periodicSmallPoint i r
  have hx : x ≠ 0 := periodicSmallPoint_ne_zero i r hr (hrτ.trans_lt hτ1)
  have hw : ‖w‖ = r := by simp [w, PiLp.norm_single, abs_of_pos hr]
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; linarith
  refine ⟨x, 0, hx, ?_⟩
  have hpair : periodicLogPair (x, 0) = periodicLogSmooth (periodicCenteredLift x) := by
    simp [periodicLogPair, periodicLogPairFun, ite_eq_right hx]
  obtain ⟨m0, hm0⟩ := exists_centeredLift_lift w
  have hxlift : periodicCenteredLift x = w + periodicFrequencyVector m0 := hm0
  have hoff : periodicCenteredLift x ∈ (periodicOffLattice : Set E) :=
    periodicCenteredLift_mem_offLattice hx
  have hterm := gaussianLogProfileSum_ge_term τ hτ (periodicCenteredLift x) hoff (-m0)
  have hw' : periodicCenteredLift x + periodicFrequencyVector (-m0) = w := by
    rw [hxlift, periodicFrequencyVector_neg']
    abel
  rw [hw'] at hterm
  have hlow := gaussianLogShortRange_lower τ hτ w hw0 (by rw [hw]; exact hrτ)
  rw [hw] at hlow
  have hlogr : Real.log r = Real.log τ - L := by
    rw [hrdef, Real.log_mul hτ.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hlong : -Bl ≤ periodicLogLongKernel (periodicHeatCut periodicRieszTau) (periodicCenteredLift x) := by
    have hL' := norm_iteratedFDeriv_periodicLogLongKernel_le (ι := ι) (periodicHeatCut periodicRieszTau)
      (periodicHeatCut_pos periodicRieszTau_pos) 0 (periodicCenteredLift x)
    simp only [norm_iteratedFDeriv_zero, pow_zero, mul_one, Real.norm_eq_abs] at hL'
    exact (abs_le.mp hL').1
  have hqL : Y ≤ q * c * L := by
    have := (div_le_iff₀ (by positivity : 0 < q * c)).mp hLY
    linarith
  rw [hpair]
  change R < c * periodicLogProfileSum τ (periodicCenteredLift x) +
    periodicLogLongKernel (periodicHeatCut periodicRieszTau) (periodicCenteredLift x) - K0
  have h1 : c * (q * L) ≤ c * periodicLogProfileSum τ (periodicCenteredLift x) := by
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    have : q * (Real.log τ - Real.log r) ≤ gaussianLogShortRange τ w := hlow
    rw [hlogr] at this
    have e1 : q * (Real.log τ - (Real.log τ - L)) = q * L := by ring
    rw [e1] at this
    exact this.trans hterm
  nlinarith

end DGRHS.Periodic
#print axioms DGRHS.Periodic.offDiagonalSum_two
#print axioms DGRHS.Periodic.periodic_twoParticle_energy_lower
#print axioms DGRHS.Periodic.periodicProfileSum_ge_term
#print axioms DGRHS.Periodic.gaussianLogProfileSum_ge_term
#print axioms DGRHS.Periodic.exists_centeredLift_lift
#print axioms DGRHS.Periodic.periodicSmallPoint_ne_zero
#print axioms DGRHS.Periodic.periodicRieszPair_unbounded
#print axioms DGRHS.Periodic.gaussianLogShortRange_lower
#print axioms DGRHS.Periodic.periodicLogPair_unbounded
