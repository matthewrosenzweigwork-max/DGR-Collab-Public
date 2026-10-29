import SharpSymmetricLSI.Paper.Sec42Flow1
import SharpSymmetricLSI.Paper.LyapSchmidt14

/-!
# Section 4.2 (lane s42; R15): the contraction (4.12) of the minimizer set

Manuscript: for `μ₀ ∈ 𝒮` and `ρ₀ = (1-s) ν + s μ₀` (`ν ∈ 𝒮`, `s ∈ [0,1]`) let `R(ρ₀)` be the
limit of the mean-field flow. `R` is continuous (uniform convergence with the rate `tailR` and
finite-time `L¹` stability (A.3)), `R(ν) = ν` on `𝒮`, `R(μ₀) = μ₀`, so (4.12) contracts `𝒮`.

The family is parametrised by `𝒫(𝕋^d) × [0,1]` (`ν` need not be a minimizer for the flow part);
`p_ν = e^{-V - W*ν}/Z` is continuous in `ν` with values in `C(𝕋^d)` (Paper/LyapSchmidt14), so
the initial data depend continuously on the parameters in the sup norm.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal unitInterval

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The minimizer set `𝒮` with the weak topology. -/
abbrev MinSet (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) :=
  {ν : ProbabilityMeasure (Torus d) // IsMinimizer V W ν}

/-- A uniform bound on the gap of densities bounded by `C`. -/
theorem exists_gap_bound (hyp : Hyp V W KV KW) (C : ℝ) : ∃ G : ℝ, 0 ≤ G ∧
    ∀ f : Torus d → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ C) →
      ∫ x, f x ∂haar d = 1 → (gap V W (densMeasure f)).toENNReal ≤ ENNReal.ofReal G := by
  haveI := haar_isProbabilityMeasure d
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  set c := (Fstar V W).toReal
  have hFs : Fstar V W = (c : EReal) := Fstar_eq_coe hyp
  refine ⟨max ((C + 1) ^ 2 + BV + BW / 2 - c) 0, le_max_right _ _,
    fun f hfm hf0 hfC hf1 => ?_⟩
  haveI := isProbabilityMeasure_densMeasure' hf0 hf1
  obtain ⟨hkl, hkl'⟩ := klDiv_densMeasure_bdd hfm hf0 hf1 hfC
  have hF := freeEnergy_eq (V := V) (W := W) (densMeasure f) hkl
  have hint : ∫ x, klFun (f x) ∂haar d ≤ (C + 1) ^ 2 := by
    calc ∫ x, klFun (f x) ∂haar d ≤ ∫ _x, (C + 1) ^ 2 ∂haar d :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => klFun_nonneg (hf0 x))
            (integrable_const _) (Eventually.of_forall fun x => by
              have h1 : klFun (f x) ≤ (f x - 1) ^ 2 := by
                rw [klFun_apply]
                rcases (hf0 x).eq_or_lt with h | h
                · rw [← h]; simp
                · have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h) (hf0 x)
                  nlinarith
              have h2 := hf0 x
              have h3 := hfC x
              nlinarith)
      _ = (C + 1) ^ 2 := by simp
  have hE : energyMF V W (densMeasure f) ≤ BV + BW / 2 := by
    unfold energyMF
    have h1 := abs_potE_le hBV (ρ := densMeasure f)
    have hBW' : ∀ x y, |W x y| ≤ BW := fun x y => hBW (x, y)
    have h2 := abs_interE_le hBW' hyp.continuous_W (ρ := densMeasure f)
      (η := densMeasure f)
    linarith [(abs_le.mp h1).2, (abs_le.mp h2).2]
  unfold gap
  rw [hF, hFs, ← EReal.coe_sub, ereal_toENNReal_coe]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hkl']
  exact (by linarith [hint, hE] : _ ≤ (C + 1) ^ 2 + BV + BW / 2 - c).trans (le_max_left _ _)

section family
variable (hyp : Hyp V W KV KW) (μ₀ : ProbabilityMeasure (Torus d))

/-- `p_ν` as an element of `C(𝕋^d)`. -/
noncomputable def pC (ν : ProbabilityMeasure (Torus d)) : CT d := elC hyp (convC hyp.continuous_W ν)

theorem continuous_pC : Continuous (pC hyp) :=
  (continuous_elC hyp).comp (continuous_convC hyp.continuous_W)

theorem pC_apply (ν : ProbabilityMeasure (Torus d)) (x : Torus d) :
    pC hyp ν x = elDens V W (ν : Measure (Torus d)) x := elC_convC hyp ν x

/-- The initial datum `(1-s) p_ν + s p_{μ₀}`. -/
noncomputable def dens0 (z : ProbabilityMeasure (Torus d) × I) : CT d :=
  (1 - (z.2 : ℝ)) • pC hyp z.1 + (z.2 : ℝ) • pC hyp μ₀

theorem continuous_dens0 : Continuous (dens0 hyp μ₀) := by
  unfold dens0
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
    ((continuous_pC hyp).comp continuous_fst)).add
    ((continuous_subtype_val.comp continuous_snd).smul continuous_const)

theorem dens0_apply (z : ProbabilityMeasure (Torus d) × I) (x : Torus d) :
    dens0 hyp μ₀ z x = (1 - (z.2 : ℝ)) * elDens V W (z.1 : Measure (Torus d)) x +
      (z.2 : ℝ) * elDens V W (μ₀ : Measure (Torus d)) x := by
  simp [dens0, pC_apply]

theorem dens0_nonneg (z : ProbabilityMeasure (Torus d) × I) (x : Torus d) :
    0 ≤ dens0 hyp μ₀ z x := by
  rw [dens0_apply]
  have h1 := (elDensity_props hyp (z.1 : Measure (Torus d))).2.1 x
  have h2 := (elDensity_props hyp (μ₀ : Measure (Torus d))).2.1 x
  have hs0 := z.2.2.1
  have hs1 := z.2.2.2
  have : 0 ≤ 1 - (z.2 : ℝ) := by linarith
  positivity

theorem integral_dens0 (z : ProbabilityMeasure (Torus d) × I) :
    ∫ x, dens0 hyp μ₀ z x ∂haar d = 1 := by
  obtain ⟨hm1, -, hi1⟩ := elDensity_props hyp (z.1 : Measure (Torus d))
  obtain ⟨hm2, -, hi2⟩ := elDensity_props hyp (μ₀ : Measure (Torus d))
  simp_rw [dens0_apply]
  rw [integral_add ((integrable_of_integral_eq_one' hi1).const_mul _)
    ((integrable_of_integral_eq_one' hi2).const_mul _), integral_const_mul, integral_const_mul,
    hi1, hi2]
  ring

theorem exists_dens0_bound : ∃ C : ℝ, ∀ z x, dens0 hyp μ₀ z x ≤ C := by
  obtain ⟨c, C, L, hc, hb⟩ := elDensity_bounds hyp
  refine ⟨C, fun z x => ?_⟩
  rw [dens0_apply]
  have h1 := ((hb (z.1 : Measure (Torus d)) inferInstance).1 x).2
  have h2 := ((hb (μ₀ : Measure (Torus d)) inferInstance).1 x).2
  have hs0 := z.2.2.1
  have hs1 := z.2.2.2
  nlinarith

end family

section contraction
variable (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) (μ₀ : ProbabilityMeasure (Torus d))

theorem dens0_hyps (z : ProbabilityMeasure (Torus d) × I) :
    Measurable (dens0 hyp μ₀ z) ∧ (∀ x, 0 ≤ dens0 hyp μ₀ z x) ∧
      ∫ x, dens0 hyp μ₀ z x ∂haar d = 1 ∧ ∃ B, ∀ x, dens0 hyp μ₀ z x ≤ B :=
  ⟨(dens0 hyp μ₀ z).continuous.measurable, dens0_nonneg hyp μ₀ z, integral_dens0 hyp μ₀ z,
    (exists_dens0_bound hyp μ₀).choose, (exists_dens0_bound hyp μ₀).choose_spec z⟩

/-- The mean-field flow from `dens0 z`. -/
noncomputable def solZ (z : ProbabilityMeasure (Torus d) × I) : ℝ → Torus d → ℝ :=
  (mf_evolution hd hyp (dens0_hyps hyp μ₀ z).1 (dens0_hyps hyp μ₀ z).2.1
    (dens0_hyps hyp μ₀ z).2.2.1 (dens0_hyps hyp μ₀ z).2.2.2).1.choose

theorem solZ_spec (z : ProbabilityMeasure (Torus d) × I) :
    IsMildSolution V W (dens0 hyp μ₀ z) (solZ hd hyp μ₀ z) :=
  (mf_evolution hd hyp (dens0_hyps hyp μ₀ z).1 (dens0_hyps hyp μ₀ z).2.1
    (dens0_hyps hyp μ₀ z).2.2.1 (dens0_hyps hyp μ₀ z).2.2.2).1.choose_spec

/-- The uniform gap bound on the family. -/
noncomputable def GZ : ℝ :=
  (exists_gap_bound hyp (exists_dens0_bound hyp μ₀).choose).choose

theorem GZ_spec : 0 ≤ GZ hyp μ₀ ∧ ∀ z : ProbabilityMeasure (Torus d) × I,
    (gap V W (densMeasure (dens0 hyp μ₀ z))).toENNReal ≤ ENNReal.ofReal (GZ hyp μ₀) := by
  obtain ⟨h0, h⟩ := (exists_gap_bound hyp (exists_dens0_bound hyp μ₀).choose).choose_spec
  exact ⟨h0, fun z => h _ (dens0_hyps hyp μ₀ z).1 (dens0_hyps hyp μ₀ z).2.1
    ((exists_dens0_bound hyp μ₀).choose_spec z) (dens0_hyps hyp μ₀ z).2.2.1⟩

/-- The flow at time `t` as a probability measure. -/
noncomputable def flowPM (z : ProbabilityMeasure (Torus d) × I) (t : ℝ) :
    ProbabilityMeasure (Torus d) :=
  pmOf μ₀ (solZ hd hyp μ₀ z t)

/-- `R(ρ₀)`. -/
noncomputable def RZ (z : ProbabilityMeasure (Torus d) × I) : ProbabilityMeasure (Torus d) :=
  (exists_flow_limit hd hyp hr (dens0_hyps hyp μ₀ z).1 (dens0_hyps hyp μ₀ z).2.1
    (dens0_hyps hyp μ₀ z).2.2.1 (dens0_hyps hyp μ₀ z).2.2.2 (solZ_spec hd hyp μ₀ z) μ₀
    (GZ_spec hyp μ₀).1 ((GZ_spec hyp μ₀).2 z)).choose

theorem RZ_spec (z : ProbabilityMeasure (Torus d) × I) :
    ∀ t, 0 ≤ t → dLip (flowPM hd hyp μ₀ z t) (RZ hd hyp hr μ₀ z) ≤ tailR V W (GZ hyp μ₀) t :=
  (exists_flow_limit hd hyp hr (dens0_hyps hyp μ₀ z).1 (dens0_hyps hyp μ₀ z).2.1
    (dens0_hyps hyp μ₀ z).2.2.1 (dens0_hyps hyp μ₀ z).2.2.2 (solZ_spec hd hyp μ₀ z) μ₀
    (GZ_spec hyp μ₀).1 ((GZ_spec hyp μ₀).2 z)).choose_spec

theorem RZ_min (z : ProbabilityMeasure (Torus d) × I) : IsMinimizer V W (RZ hd hyp hr μ₀ z) :=
  flow_limit_minimizer hd hyp hr (dens0_hyps hyp μ₀ z).1 (dens0_hyps hyp μ₀ z).2.1
    (dens0_hyps hyp μ₀ z).2.2.1 (dens0_hyps hyp μ₀ z).2.2.2 (solZ_spec hd hyp μ₀ z) μ₀
    (GZ_spec hyp μ₀).1 ((GZ_spec hyp μ₀).2 z) (RZ_spec hd hyp hr μ₀ z)

theorem tendsto_flowPM (z : ProbabilityMeasure (Torus d) × I) :
    Tendsto (fun n : ℕ => flowPM hd hyp μ₀ z n) atTop (𝓝 (RZ hd hyp hr μ₀ z)) :=
  tendsto_of_dLip_le ((tendsto_tailR (V := V) (W := W) _).comp tendsto_natCast_atTop_atTop)
    (fun n => RZ_spec hd hyp hr μ₀ z n (Nat.cast_nonneg n))

theorem flowPM_coe (z : ProbabilityMeasure (Torus d) × I) {t : ℝ} (ht : 0 ≤ t) :
    (flowPM hd hyp μ₀ z t : Measure (Torus d)) = densMeasure (solZ hd hyp μ₀ z t) :=
  pmOf_coe μ₀ ((solZ_spec hd hyp μ₀ z).1 t ht).1 ((solZ_spec hd hyp μ₀ z).1 t ht).2

/-- If the initial datum is a minimizer `ν`, then `R = ν`. -/
theorem RZ_of_min (z : ProbabilityMeasure (Torus d) × I) {ν : ProbabilityMeasure (Torus d)}
    (hν : IsMinimizer V W ν) (hz : (ν : Measure (Torus d)) = densMeasure (dens0 hyp μ₀ z)) :
    RZ hd hyp hr μ₀ z = ν := by
  set c := (Fstar V W).toReal
  have hFs : Fstar V W = (c : EReal) := Fstar_eq_coe hyp
  have hG : (gap V W (densMeasure (dens0 hyp μ₀ z))).toENNReal ≤ ENNReal.ofReal 0 := by
    rw [← hz, ENNReal.ofReal_zero, nonpos_iff_eq_zero, EReal.toENNReal_eq_zero_iff]
    unfold gap
    rw [hν, hFs, ← EReal.coe_sub, sub_self, EReal.coe_zero]
  have h0 := (dens0_hyps hyp μ₀ z)
  have hconst : ∀ n : ℕ, flowPM hd hyp μ₀ z n = flowPM hd hyp μ₀ z 0 := fun n => by
    have := dLip_flow_le hd hyp hr h0.1 h0.2.1 h0.2.2.1 h0.2.2.2 (solZ_spec hd hyp μ₀ z) μ₀
      le_rfl hG le_rfl (Nat.cast_nonneg n)
    have h' : tailR V W 0 0 = 0 := by simp [tailR]
    rw [h'] at this
    exact (eq_of_dLip_eq_zero (le_antisymm this (dLip_nonneg _ _))).symm
  have h00 : flowPM hd hyp μ₀ z 0 = ν := by
    apply Subtype.ext
    show (flowPM hd hyp μ₀ z 0 : Measure (Torus d)) = ν
    rw [flowPM_coe hd hyp μ₀ z le_rfl, (solZ_spec hd hyp μ₀ z).2.2.1, hz]
  have := tendsto_flowPM hd hyp hr μ₀ z
  simp_rw [hconst, h00] at this
  exact tendsto_nhds_unique this tendsto_const_nhds

/-- Finite-time continuity: `d_Lip` of the flows at time `t` is controlled by the sup distance
of the initial data. -/
theorem dLip_flowPM_le (t : ℝ) (ht : 0 ≤ t) : ∃ K : ℝ, ∀ z z' : ProbabilityMeasure (Torus d) × I,
    dLip (flowPM hd hyp μ₀ z t) (flowPM hd hyp μ₀ z' t) ≤
      K * ‖dens0 hyp μ₀ z - dens0 hyp μ₀ z'‖ := by
  haveI := haar_isProbabilityMeasure d
  obtain ⟨B₀, L₀, hDB⟩ := exists_driftBounds hyp
  obtain ⟨C, hC⟩ := flow_stability d t B₀ L₀
  refine ⟨Real.sqrt d * max C 0, fun z z' => ?_⟩
  have hs := solZ_spec hd hyp μ₀ z
  have hs' := solZ_spec hd hyp μ₀ z'
  have hst := hC V W KV KW hyp hDB _ _ _ _ hs hs' t ⟨ht, le_rfl⟩
  have hi : Integrable (solZ hd hyp μ₀ z t) (haar d) := integrable_of_integral_eq_one' (hs.1 t ht).2
  have hi' : Integrable (solZ hd hyp μ₀ z' t) (haar d) :=
    integrable_of_integral_eq_one' (hs'.1 t ht).2
  refine (dLip_le_L1 (flowPM_coe hd hyp μ₀ z ht) (flowPM_coe hd hyp μ₀ z' ht) hi hi'
    (hs.1 t ht).1 (hs'.1 t ht).1).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  -- `L¹` norms
  have hL1 : ∫ x, |solZ hd hyp μ₀ z t x - solZ hd hyp μ₀ z' t x| ∂haar d =
      (eLpNorm (fun x => solZ hd hyp μ₀ z t x - solZ hd hyp μ₀ z' t x) 1 (haar d)).toReal := by
    have hm : AEStronglyMeasurable (fun x => solZ hd hyp μ₀ z t x - solZ hd hyp μ₀ z' t x)
        (haar d) := (hi.sub hi').aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm hm]
    all_goals first | exact hm | simp only [Real.norm_eq_abs]
  have h0 : eLpNorm (fun x => dens0 hyp μ₀ z x - dens0 hyp μ₀ z' x) 1 (haar d) ≤
      ENNReal.ofReal ‖dens0 hyp μ₀ z - dens0 hyp μ₀ z'‖ := by
    refine (eLpNorm_le_of_ae_bound (C := ‖dens0 hyp μ₀ z - dens0 hyp μ₀ z'‖) ((dens0 hyp μ₀ z).continuous.sub
      (dens0 hyp μ₀ z').continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)).trans (by simp)
    have := ContinuousMap.norm_coe_le_norm (dens0 hyp μ₀ z - dens0 hyp μ₀ z') x
    simpa using this
  have h1 : eLpNorm (fun x => solZ hd hyp μ₀ z t x - solZ hd hyp μ₀ z' t x) 1 (haar d) ≤
      ENNReal.ofReal (max C 0 * ‖dens0 hyp μ₀ z - dens0 hyp μ₀ z'‖) := by
    refine hst.trans ?_
    rw [ENNReal.ofReal_mul (le_max_right _ _)]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) h0
  rw [hL1]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h1

/-- **`R` is continuous** on `𝒫(𝕋^d) × [0,1]`. -/
theorem continuous_RZ : Continuous (RZ hd hyp hr μ₀) := by
  rw [continuous_iff_seqContinuous]
  intro zs z hz
  refine (dLip_metrizes _ _).2 ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- a time with small tail
  obtain ⟨t, ht0, htail⟩ : ∃ t : ℝ, 0 ≤ t ∧ tailR V W (GZ hyp μ₀) t < ε / 3 := by
    have := (tendsto_tailR (V := V) (W := W) (GZ hyp μ₀)).eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 3))
    obtain ⟨t, ht⟩ := (this.and (eventually_ge_atTop 0)).exists
    exact ⟨t, ht.2, ht.1⟩
  obtain ⟨K, hK⟩ := dLip_flowPM_le hd hyp μ₀ t ht0
  have hcz := ((continuous_dens0 hyp μ₀).tendsto z).comp hz
  have hcz' : Tendsto (fun n => (max K 1) * ‖dens0 hyp μ₀ (zs n) - dens0 hyp μ₀ z‖) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hcz).const_mul (max K 1)
    simpa using this
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hcz' (ε / 3) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (dLip_nonneg _ _)]
  have h1 := RZ_spec hd hyp hr μ₀ (zs n) t ht0
  have h2 := RZ_spec hd hyp hr μ₀ z t ht0
  have h3 : dLip (flowPM hd hyp μ₀ (zs n) t) (flowPM hd hyp μ₀ z t) < ε / 3 := by
    have hn' := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hn'
    refine lt_of_le_of_lt ((hK (zs n) z).trans ?_) hn'
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  calc dLip (RZ hd hyp hr μ₀ (zs n)) (RZ hd hyp hr μ₀ z)
      ≤ dLip (RZ hd hyp hr μ₀ (zs n)) (flowPM hd hyp μ₀ (zs n) t) +
          dLip (flowPM hd hyp μ₀ (zs n) t) (RZ hd hyp hr μ₀ z) := dLip_triangle _ _ _
    _ ≤ dLip (RZ hd hyp hr μ₀ (zs n)) (flowPM hd hyp μ₀ (zs n) t) +
          (dLip (flowPM hd hyp μ₀ (zs n) t) (flowPM hd hyp μ₀ z t) +
            dLip (flowPM hd hyp μ₀ z t) (RZ hd hyp hr μ₀ z)) :=
        add_le_add le_rfl (dLip_triangle _ _ _)
    _ < ε / 3 + (ε / 3 + ε / 3) := by
        rw [dLip_comm] at h1
        gcongr
        · exact lt_of_le_of_lt h1 htail
        · exact lt_of_le_of_lt h2 htail
    _ = ε := by ring

include hd hyp hr in
/-- **(4.12): `𝒮` is contractible.** -/
theorem contractible_minSet (hμ₀ : IsMinimizer V W μ₀) : ContractibleSpace (MinSet V W) := by
  -- `R` restricted to `I × 𝒮`
  have hcont : Continuous fun p : I × MinSet V W =>
      (⟨RZ hd hyp hr μ₀ (p.2.1, p.1), RZ_min hd hyp hr μ₀ _⟩ : MinSet V W) :=
    ((continuous_RZ hd hyp hr μ₀).comp
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)).subtype_mk _
  have h0 : ∀ ν : MinSet V W, RZ hd hyp hr μ₀ (ν.1, 0) = ν.1 := fun ν => by
    refine RZ_of_min hd hyp hr μ₀ _ ν.2 ?_
    have : dens0 hyp μ₀ (ν.1, 0) = pC hyp ν.1 := by
      ext x; simp [dens0]
    rw [this, minimizer_eq_elDensity hyp ν.2]
    congr 1; funext x; rw [pC_apply]
  have h1 : ∀ ν : MinSet V W, RZ hd hyp hr μ₀ (ν.1, 1) = μ₀ := fun ν => by
    refine RZ_of_min hd hyp hr μ₀ _ hμ₀ ?_
    have : dens0 hyp μ₀ (ν.1, 1) = pC hyp μ₀ := by
      ext x; simp [dens0]
    rw [this, minimizer_eq_elDensity hyp hμ₀]
    congr 1; funext x; rw [pC_apply]
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨⟨μ₀, hμ₀⟩, ⟨{ toFun := fun p => ⟨RZ hd hyp hr μ₀ (p.2.1, p.1), RZ_min hd hyp hr μ₀ _⟩
                        continuous_toFun := hcont
                        map_zero_left := fun ν => Subtype.ext (h0 ν)
                        map_one_left := fun ν => Subtype.ext (h1 ν) }⟩⟩

end contraction

end SharpLSI
