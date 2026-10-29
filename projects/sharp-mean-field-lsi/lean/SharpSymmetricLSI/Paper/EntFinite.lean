import SharpSymmetricLSI.Paper.Gibbs
import SharpSymmetricLSI.Infra.SobolevTorus

/-!
# Entropy finiteness on `H¹(P_N)` (Phase 2, I1, milestone 7)

Under (1.2) the density of `P_N` is bounded above and below, so `H¹(P_N)` functions give
weak-gradient pairs in `L²` of the Haar measure on the flattened torus `𝕋^{N×d}`
(`memH1C_data`, `lintegral_haar_le_gibbs`, `lintegral_gibbs_le_haar`). The torus Sobolev
inequality then puts `f` in `L^{2p}(P_N)` for some `p > 1` (`exists_lintegral_rpow_lt_top`), and
`Ent_{P_N}(f²) < ⊤` follows from `klFun t ≤ 1 + t^p/(p-1)` (`ent_sq_lt_top_aux`). This proves the
D9 sanity lemma `ent_sq_lt_top`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}
/-! ### Lower density bound and Haar integrability -/

theorem exists_gibbsDensity_lower {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) (N : ℕ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ X : Config N d,
      c ≤ gibbsDensity (volume : Measure (Config N d)) (hamiltonian V W N) X := by
  have hH := continuous_hamiltonian hyp N
  obtain ⟨X₀, -, hX₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hH.continuousOn
  have hZ := partition_pos_of_continuous (volume : Measure (Config N d)) hH
  refine ⟨ENNReal.ofReal (Real.exp (-hamiltonian V W N X₀) /
    ∫ y, Real.exp (-hamiltonian V W N y)), ?_, ENNReal.ofReal_ne_top, fun X => ?_⟩
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  · unfold gibbsDensity
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ hZ.le
    exact Real.exp_le_exp.mpr (neg_le_neg (hX₀ (mem_univ X)))

/-- `∫⁻ F dm^{⊗(N×d)} ≤ C ∫⁻ F d(P_N ∘ flat⁻¹)`. -/
theorem lintegral_haar_le_gibbs {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) (N : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ F : UnitAddTorus (Fin N × Fin d) → ℝ≥0∞, AEMeasurable F volume →
      ∫⁻ y, F y ≤ C * ∫⁻ y, F y ∂((gibbs V W N).map flat) := by
  obtain ⟨c, hc0, hct, hc⟩ := exists_gibbsDensity_lower hyp N
  refine ⟨c⁻¹, ENNReal.inv_ne_top.mpr hc0, fun F hF => ?_⟩
  have hFm : AEMeasurable F ((volume : Measure (Config N d)).map flat) := by
    rwa [map_flat_volume]
  have hFg : AEMeasurable F ((gibbs V W N).map flat) := hF.mono_ac (gibbs_map_flat_ac hyp N).1
  rw [← map_flat_volume N, lintegral_map' hFm measurable_flat.aemeasurable,
    lintegral_map' hFg measurable_flat.aemeasurable]
  have hρ : AEMeasurable (gibbsDensity (volume : Measure (Config N d)) (hamiltonian V W N))
      volume := (measurable_gibbsDensity _ (continuous_hamiltonian hyp N)).aemeasurable
  rw [show gibbs V W N = (volume : Measure (Config N d)).withDensity
      (gibbsDensity volume (hamiltonian V W N)) from rfl,
    lintegral_withDensity_eq_lintegral_mul₀ (g := fun a => F (flat a)) hρ
      (hFm.comp_aemeasurable measurable_flat.aemeasurable),
    ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hc0)]
  refine lintegral_mono fun X => ?_
  simp only [Pi.mul_apply]
  calc F (flat X) = 1 * F (flat X) := (one_mul _).symm
    _ ≤ (c⁻¹ * gibbsDensity volume (hamiltonian V W N) X) * F (flat X) := by
        gcongr
        rw [← ENNReal.inv_mul_cancel hc0 hct]
        gcongr
        exact hc X
    _ = _ := by ring

/-- `L²(P_N ∘ flat⁻¹)` functions are Haar-integrable. -/
theorem integrable_haar_of_memLp {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) {N : ℕ} {u : UnitAddTorus (Fin N × Fin d) → ℝ}
    (hu : MemLp u 2 ((gibbs V W N).map flat)) (hum : AEStronglyMeasurable u volume) :
    Integrable u volume := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  have : IsProbabilityMeasure ((gibbs V W N).map flat) :=
    inferInstance
  have h1 : Integrable u ((gibbs V W N).map flat) :=
    memLp_one_iff_integrable.mp (hu.mono_exponent (by norm_num))
  obtain ⟨C, hC, hle⟩ := lintegral_haar_le_gibbs hyp N
  exact ⟨hum, (hle _ hum.enorm).trans_lt (ENNReal.mul_lt_top hC.lt_top h1.2)⟩

/-! ### Weak gradients: measurability and the chosen gradient -/

section Torus

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem IsWeakGrad.aestronglyMeasurable_fun {u : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad u g) : AEStronglyMeasurable u volume := by
  have := h.locInt.aestronglyMeasurable.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_secT (ι := ι))
  refine this.congr (Eventually.of_forall fun y => ?_)
  simp [Function.comp, liftT_secT]

theorem IsWeakGrad.aestronglyMeasurable_grad {u : UnitAddTorus ι → ℝ}
    {g : UnitAddTorus ι → ι → ℝ} (h : IsWeakGrad u g) (k : ι) :
    AEStronglyMeasurable (fun y => g y k) volume := by
  have := (h.locInt_grad k).aestronglyMeasurable.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_secT (ι := ι))
  refine this.congr (Eventually.of_forall fun y => ?_)
  simp [Function.comp, liftT_secT]

theorem IsWeakGrad.aestronglyMeasurable_sqNorm {u : UnitAddTorus ι → ℝ}
    {g : UnitAddTorus ι → ι → ℝ} (h : IsWeakGrad u g) :
    AEStronglyMeasurable (fun y => sqNorm (g y)) volume := by
  unfold sqNorm
  exact Finset.aestronglyMeasurable_fun_sum _ fun k _ => (h.aestronglyMeasurable_grad k).pow 2

theorem isWeakGrad_weakGrad {u : UnitAddTorus ι → ℝ} (h : HasWeakGrad u) :
    IsWeakGrad u (weakGrad u) := by
  have : weakGrad u = h.choose := by simp [weakGrad, h]
  rw [this]; exact h.choose_spec

theorem weakGrad_ae_eq {u : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad u g) : weakGrad u =ᵐ[volume] g :=
  weakGrad_ae_unique (isWeakGrad_weakGrad ⟨g, h⟩) h

omit [DecidableEq ι] in
theorem abs_le_sqrt_sqNorm (v : ι → ℝ) (k : ι) : |v k| ≤ Real.sqrt (sqNorm v) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => v j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ k))

omit [DecidableEq ι] in
theorem sqNorm_nonneg (v : ι → ℝ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq ι] in
theorem sqNorm_ite_left (p : Prop) [Decidable p] (v : ι → ℝ) :
    sqNorm (fun k => if p then v k else 0) = if p then sqNorm v else 0 := by
  by_cases h : p <;> simp [h, sqNorm]

omit [DecidableEq ι] in
theorem sqNorm_ite_right (p : Prop) [Decidable p] (v : ι → ℝ) :
    sqNorm (fun k => if p then 0 else v k) = if p then 0 else sqNorm v := by
  by_cases h : p <;> simp [h, sqNorm]

omit [DecidableEq ι] in
theorem sqNorm_neg (v : ι → ℝ) : sqNorm (fun k => -v k) = sqNorm v := by simp [sqNorm]

end Torus

/-! ### `H¹(P_N)` data -/

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- An `H¹(P_N)` function gives a Haar-integrable weak-gradient pair on `𝕋^{N×d}`. -/
theorem memH1C_data (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) :
    IsWeakGrad (f ∘ unflat) (weakGrad (f ∘ unflat)) ∧ Integrable (f ∘ unflat) volume ∧
      ∀ k, Integrable (fun y => weakGrad (f ∘ unflat) y k) volume := by
  have hw := isWeakGrad_weakGrad hf.1
  have hac := (gibbs_map_flat_ac hyp N).1
  refine ⟨hw, integrable_haar_of_memLp hyp hf.2.1 hw.aestronglyMeasurable_fun, fun k => ?_⟩
  refine integrable_haar_of_memLp hyp ?_ (hw.aestronglyMeasurable_grad k)
  refine hf.2.2.of_le ((hw.aestronglyMeasurable_grad k).mono_ac hac)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact abs_le_sqrt_sqNorm _ k

/-! ### Upper density bound -/

theorem exists_gibbsDensity_upper (hyp : Hyp V W KV KW) (N : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ X : Config N d,
      gibbsDensity (volume : Measure (Config N d)) (hamiltonian V W N) X ≤ C := by
  have hH := continuous_hamiltonian hyp N
  obtain ⟨X₀, -, hX₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty hH.continuousOn
  have hZ := partition_pos_of_continuous (volume : Measure (Config N d)) hH
  refine ⟨ENNReal.ofReal (Real.exp (-hamiltonian V W N X₀) /
    ∫ y, Real.exp (-hamiltonian V W N y)), ENNReal.ofReal_ne_top, fun X => ?_⟩
  unfold gibbsDensity
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ hZ.le
  exact Real.exp_le_exp.mpr (neg_le_neg (hX₀ (mem_univ X)))

/-- `∫⁻ F d(P_N ∘ flat⁻¹) ≤ C ∫⁻ F dm^{⊗(N×d)}`. -/
theorem lintegral_gibbs_le_haar (hyp : Hyp V W KV KW) (N : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ F : UnitAddTorus (Fin N × Fin d) → ℝ≥0∞, AEMeasurable F volume →
      ∫⁻ y, F y ∂((gibbs V W N).map flat) ≤ C * ∫⁻ y, F y := by
  obtain ⟨C, hCt, hC⟩ := exists_gibbsDensity_upper hyp N
  refine ⟨C, hCt, fun F hF => ?_⟩
  have hFm : AEMeasurable F ((volume : Measure (Config N d)).map flat) := by
    rwa [map_flat_volume]
  have hFg : AEMeasurable F ((gibbs V W N).map flat) := hF.mono_ac (gibbs_map_flat_ac hyp N).1
  rw [← map_flat_volume N, lintegral_map' hFm measurable_flat.aemeasurable,
    lintegral_map' hFg measurable_flat.aemeasurable]
  have hρ : AEMeasurable (gibbsDensity (volume : Measure (Config N d)) (hamiltonian V W N))
      volume := (measurable_gibbsDensity _ (continuous_hamiltonian hyp N)).aemeasurable
  rw [show gibbs V W N = (volume : Measure (Config N d)).withDensity
      (gibbsDensity volume (hamiltonian V W N)) from rfl,
    lintegral_withDensity_eq_lintegral_mul₀ (g := fun a => F (flat a)) hρ
      (hFm.comp_aemeasurable measurable_flat.aemeasurable),
    ← lintegral_const_mul' _ _ hCt]
  refine lintegral_mono fun X => ?_
  simp only [Pi.mul_apply]
  gcongr
  exact hC X

/-- `L²(P_N ∘ flat⁻¹)` functions are in `L²` of the Haar measure. -/
theorem lintegral_sq_haar_lt_top (hyp : Hyp V W KV KW) {N : ℕ}
    {u : UnitAddTorus (Fin N × Fin d) → ℝ} (hu : MemLp u 2 ((gibbs V W N).map flat))
    (hum : AEStronglyMeasurable u volume) : ∫⁻ y, ‖u y‖ₑ ^ 2 < ⊤ := by
  obtain ⟨C, hC, hle⟩ := lintegral_haar_le_gibbs hyp N
  refine (hle _ (hum.enorm.pow_const 2)).trans_lt (ENNReal.mul_lt_top hC.lt_top ?_)
  have := hu.integrable_sq.2
  simpa [HasFiniteIntegral, enorm_pow] using this

/-- `f ∈ H¹(P_N)` lies in `L^{2p}(P_N)` for some `p > 1`. -/
theorem exists_lintegral_rpow_lt_top (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) :
    ∃ p : ℝ, 1 < p ∧ ∫⁻ X, ‖f X‖ₑ ^ (2 * p) ∂gibbs V W N < ⊤ := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  rcases isEmpty_or_nonempty (Fin N × Fin d) with hι | hι
  · -- `Config N d` is a point
    have hX : ∀ X Y : Config N d, X = Y := fun X Y => by
      funext i k; exact (hι.false (i, k)).elim
    obtain ⟨X₀⟩ : Nonempty (Config N d) := ⟨fun _ _ => 0⟩
    refine ⟨2, one_lt_two, ?_⟩
    have : ∀ X, ‖f X‖ₑ ^ (2 * (2 : ℝ)) = ‖f X₀‖ₑ ^ (2 * (2 : ℝ)) := fun X => by rw [hX X X₀]
    simp_rw [this]
    rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) enorm_ne_top
  · obtain ⟨hw, hfi, hgi⟩ := memH1C_data hyp hf
    set u := f ∘ unflat
    refine ⟨sobExp (Fin N × Fin d), one_lt_sobExp, ?_⟩
    have hum := hw.aestronglyMeasurable_fun
    have hac := (gibbs_map_flat_ac hyp N).1
    have hS := lintegral_rpow_le_of_isWeakGrad hw hfi hgi
    obtain ⟨C, hC, hle⟩ := lintegral_gibbs_le_haar hyp N
    have hmap : ∫⁻ X, ‖f X‖ₑ ^ (2 * sobExp (Fin N × Fin d)) ∂gibbs V W N =
        ∫⁻ y, ‖u y‖ₑ ^ (2 * sobExp (Fin N × Fin d)) ∂((gibbs V W N).map flat) := by
      rw [lintegral_map' ((hum.enorm.pow_const _).mono_ac hac) measurable_flat.aemeasurable]
      rfl
    rw [hmap]
    refine (hle _ (hum.enorm.pow_const _)).trans_lt (ENNReal.mul_lt_top hC.lt_top ?_)
    refine hS.trans_lt (ENNReal.mul_lt_top sobConst_lt_top (ENNReal.rpow_lt_top_of_nonneg
      (by linarith [one_lt_sobExp (ι := Fin N × Fin d)]) ?_))
    refine ENNReal.add_ne_top.mpr ⟨(lintegral_sq_haar_lt_top hyp hf.2.1 hum).ne, ?_⟩
    refine ENNReal.sum_ne_top.mpr fun k _ => ?_
    refine (lintegral_sq_haar_lt_top hyp ?_ (hw.aestronglyMeasurable_grad k)).ne
    refine hf.2.2.of_le ((hw.aestronglyMeasurable_grad k).mono_ac hac)
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact abs_le_sqrt_sqNorm _ k

/-! ### Entropy finiteness -/

theorem mul_log_le_rpow {p : ℝ} (hp : 1 < p) {t : ℝ} (ht : 0 ≤ t) :
    t * Real.log t ≤ t ^ p / (p - 1) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [Real.log_zero, mul_zero]
    rw [Real.zero_rpow (by linarith)]; simp
  have hp1 : 0 < p - 1 := by linarith
  have h1 : Real.log (t ^ (p - 1)) ≤ t ^ (p - 1) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht _)
  rw [Real.log_rpow ht] at h1
  have h2 : Real.log t ≤ t ^ (p - 1) / (p - 1) := by
    rw [le_div_iff₀ hp1]; linarith
  have h3 : t ^ p = t * t ^ (p - 1) := by
    rw [← Real.rpow_one_add' ht.le (by linarith)]; ring_nf
  calc t * Real.log t ≤ t * (t ^ (p - 1) / (p - 1)) := mul_le_mul_of_nonneg_left h2 ht.le
    _ = t ^ p / (p - 1) := by rw [h3]; ring

theorem klFun_le_rpow {p : ℝ} (hp : 1 < p) {t : ℝ} (ht : 0 ≤ t) :
    InformationTheory.klFun t ≤ 1 + t ^ p / (p - 1) := by
  rw [InformationTheory.klFun_apply]
  linarith [mul_log_le_rpow hp ht]

/-- `Ent_P(u) < ⊤` for `0 ≤ u ∈ L^p(P)`, `p > 1`. -/
theorem ent_lt_top_of_lintegral_rpow {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] {u : α → ℝ} (hu0 : ∀ x, 0 ≤ u x) (hint : Integrable u P)
    {p : ℝ} (hp : 1 < p) (h : ∫⁻ x, ‖u x‖ₑ ^ p ∂P < ⊤) : ent P u < ⊤ := by
  unfold ent
  rw [if_pos hint]
  set m := ∫ y, u y ∂P
  have hm : 0 ≤ m := integral_nonneg hu0
  have hp1 : 0 < p - 1 := by linarith
  set K : ℝ := m * (m ^ p)⁻¹ / (p - 1)
  have hK : 0 ≤ K := by positivity
  have hpt : ∀ x, ENNReal.ofReal (m * InformationTheory.klFun (u x / m)) ≤
      ENNReal.ofReal m + ENNReal.ofReal K * ‖u x‖ₑ ^ p := by
    intro x
    rw [Real.enorm_of_nonneg (hu0 x), ENNReal.ofReal_rpow_of_nonneg (hu0 x) (by linarith),
      ← ENNReal.ofReal_mul hK,
      ← ENNReal.ofReal_add hm (mul_nonneg hK (Real.rpow_nonneg (hu0 x) _))]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases hm.eq_or_lt with hm0 | hm0
    · rw [← hm0]; simp only [zero_mul, zero_add]
      simp only [K, ← hm0, zero_mul, zero_div]; simp
    · have := klFun_le_rpow hp (div_nonneg (hu0 x) hm)
      calc m * InformationTheory.klFun (u x / m) ≤ m * (1 + (u x / m) ^ p / (p - 1)) :=
            mul_le_mul_of_nonneg_left this hm
        _ = m + K * u x ^ p := by
            simp only [K]
            rw [Real.div_rpow (hu0 x) hm]
            field_simp
  calc ∫⁻ x, ENNReal.ofReal (m * InformationTheory.klFun (u x / m)) ∂P
      ≤ ∫⁻ x, (ENNReal.ofReal m + ENNReal.ofReal K * ‖u x‖ₑ ^ p) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal m + ENNReal.ofReal K * ∫⁻ x, ‖u x‖ₑ ^ p ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top h⟩

/-- **D9 sanity lemma.** Under (1.2), `Ent_{P_N}(f²) < ⊤` for `f ∈ H¹(P_N)`. -/
theorem ent_sq_lt_top_aux (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) : ent (gibbs V W N) (fun X => f X ^ 2) < ⊤ := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  obtain ⟨p, hp, hfp⟩ := exists_lintegral_rpow_lt_top hyp hf
  have hL2 : MemLp f 2 (gibbs V W N) := by
    have h : MemLp (f ∘ unflat) 2 ((gibbs V W N).map flat) := hf.2.1
    rw [show f = (f ∘ unflat) ∘ flat from rfl]
    exact h.comp_of_map measurable_flat.aemeasurable
  refine ent_lt_top_of_lintegral_rpow (fun X => sq_nonneg _) hL2.integrable_sq hp ?_
  simpa only [enorm_sq_rpow] using hfp

end SharpLSI
