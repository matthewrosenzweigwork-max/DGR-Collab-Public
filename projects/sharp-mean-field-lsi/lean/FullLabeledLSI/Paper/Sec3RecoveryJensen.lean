import SharpSymmetricLSI.Infra.MollifyL2
import SharpSymmetricLSI.Paper.UpperBound

/-!
# Jensen-type facts for the torus mollification `moll n`

* `moll_nonneg`, `moll_sq_le_moll_sq` (pointwise Cauchy–Schwarz), `integral_moll` (mass
  preservation), and the convex-integrand contraction `lintegral_convex_moll_le`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SharpLSI.FL

open SharpLSI

section Generic

variable {ι : Type*} [Fintype ι]

/-- The probability measure on `ℝ^ι` with density `φ_n`. -/
def mollMeasure (n : ℕ) : Measure (ι → ℝ) :=
  (volume : Measure (ι → ℝ)).withDensity fun s => ((phiSeq n s).toNNReal : ℝ≥0∞)

theorem measurable_toNNReal_phiSeq (n : ℕ) :
    Measurable fun s : ι → ℝ => (phiSeq n s).toNNReal :=
  (contDiff_phiSeq n).continuous.measurable.real_toNNReal

instance (n : ℕ) : IsProbabilityMeasure (mollMeasure (ι := ι) n) :=
  ⟨by
    rw [mollMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact lintegral_ofReal_phiSeq n⟩

theorem integral_mollMeasure (n : ℕ) (g : (ι → ℝ) → ℝ) :
    ∫ s, g s ∂mollMeasure n = ∫ s, phiSeq n s * g s := by
  rw [mollMeasure, integral_withDensity_eq_integral_smul (measurable_toNNReal_phiSeq n)]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (phiSeq_nonneg n s)]

theorem integrable_mollMeasure_iff (n : ℕ) (g : (ι → ℝ) → ℝ) :
    Integrable g (mollMeasure n) ↔ Integrable (fun s => phiSeq n s * g s) volume := by
  rw [mollMeasure, integrable_withDensity_iff_integrable_smul (measurable_toNNReal_phiSeq n)]
  refine integrable_congr (Eventually.of_forall fun s => ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (phiSeq_nonneg n s)]

theorem lintegral_mollMeasure (n : ℕ) {g : (ι → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ s, g s ∂mollMeasure n = ∫⁻ s, ENNReal.ofReal (phiSeq n s) * g s := by
  rw [mollMeasure, lintegral_withDensity_eq_lintegral_mul _
    (measurable_toNNReal_phiSeq n).coe_nnreal_ennreal hg]
  rfl

/-- Integrability of the convolution integrand. -/
theorem integrable_phiSeq_mul (n : ℕ) {u : UnitAddTorus ι → ℝ} (hu : Integrable u volume)
    (x : ι → ℝ) : Integrable (fun s => phiSeq n s * u (liftT (x - s))) volume := by
  have := ((hasCompactSupport_phiSeq n).convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_comp_liftT hu) (contDiff_phiSeq n).continuous x).integrable
  have h2 : Integrable (fun t => u (liftT t) * phiSeq n (x - t)) volume := this
  have h3 := h2.comp_sub_left x
  refine h3.congr (Eventually.of_forall fun s => ?_)
  simp only [sub_sub_cancel]
  ring

theorem mollL_comp_liftT_eq_integral (n : ℕ) (u : UnitAddTorus ι → ℝ) (x : ι → ℝ) :
    mollL n (u ∘ liftT) x = ∫ s, u (liftT (x - s)) ∂mollMeasure n := by
  rw [integral_mollMeasure, mollL_apply']
  rfl

/-- The Tonelli/translation step, as an identity. -/
theorem lintegral_unitBox_phiSeq_mul {H : UnitAddTorus ι → ℝ≥0∞} (hH : Measurable H) (n : ℕ) :
    ∫⁻ x in unitBox ι, ∫⁻ s, ENNReal.ofReal (phiSeq n s) * H (liftT (x - s)) = ∫⁻ y, H y := by
  have hφm : Measurable fun s : ι → ℝ => ENNReal.ofReal (phiSeq n s) :=
    ENNReal.measurable_ofReal.comp (contDiff_phiSeq n).continuous.measurable
  have hmeas : Measurable (Function.uncurry fun (x s : ι → ℝ) =>
      ENNReal.ofReal (phiSeq n s) * H (liftT (x - s))) :=
    (hφm.comp measurable_snd).mul (hH.comp (measurable_liftT.comp
      (measurable_fst.sub measurable_snd)))
  calc ∫⁻ x in unitBox ι, ∫⁻ s, ENNReal.ofReal (phiSeq n s) * H (liftT (x - s))
      = ∫⁻ s, ∫⁻ x in unitBox ι, ENNReal.ofReal (phiSeq n s) * H (liftT (x - s)) :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ s, ENNReal.ofReal (phiSeq n s) * ∫⁻ y, H y := by
        refine lintegral_congr fun s => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_unitBox_sub hH s
    _ = ∫⁻ y, H y := by
        rw [lintegral_mul_const _ hφm, lintegral_ofReal_phiSeq, one_mul]

theorem lintegral_le_of_lift_le (n : ℕ) {G H : UnitAddTorus ι → ℝ≥0∞} (hG : Measurable G)
    (hH : Measurable H)
    (hle : ∀ x, G (liftT x) ≤ ∫⁻ s, ENNReal.ofReal (phiSeq n s) * H (liftT (x - s))) :
    ∫⁻ y, G y ≤ ∫⁻ y, H y := by
  rw [← (measurePreserving_liftT (ι := ι)).lintegral_comp hG,
    ← lintegral_unitBox_phiSeq_mul hH n]
  exact lintegral_mono hle

theorem lintegral_eq_of_lift_eq (n : ℕ) {G H : UnitAddTorus ι → ℝ≥0∞} (hG : Measurable G)
    (hH : Measurable H)
    (hle : ∀ x, G (liftT x) = ∫⁻ s, ENNReal.ofReal (phiSeq n s) * H (liftT (x - s))) :
    ∫⁻ y, G y = ∫⁻ y, H y := by
  rw [← (measurePreserving_liftT (ι := ι)).lintegral_comp hG,
    ← lintegral_unitBox_phiSeq_mul hH n]
  exact lintegral_congr hle

end Generic

variable {d : ℕ}

theorem moll_nonneg (n : ℕ) {f : Torus d → ℝ} (hf0 : ∀ x, 0 ≤ f x) (y : Torus d) :
    0 ≤ moll n f y := by
  rw [moll, mollL_apply']
  exact integral_nonneg fun s => mul_nonneg (phiSeq_nonneg n s) (hf0 _)

theorem moll_sq_le_moll_sq (n : ℕ) {u : Torus d → ℝ} (hu : Integrable u (haar d))
    (hu2 : Integrable (fun x => u x ^ 2) (haar d)) (y : Torus d) :
    (moll n u y) ^ 2 ≤ moll n (fun x => u x ^ 2) y := by
  have hi1 : Integrable (fun s => u (liftT (secT y - s))) (mollMeasure n) :=
    (integrable_mollMeasure_iff n _).mpr (integrable_phiSeq_mul n hu _)
  have hi2 : Integrable (fun s => u (liftT (secT y - s)) ^ 2) (mollMeasure n) :=
    (integrable_mollMeasure_iff n _).mpr (integrable_phiSeq_mul n hu2 _)
  have h := (Even.convexOn_pow (by decide : Even 2)).map_integral_le (μ := mollMeasure n)
    (f := fun s => u (liftT (secT y - s))) (continuousOn_id.pow 2) isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _) hi1 hi2
  simp only [moll, mollL_comp_liftT_eq_integral]
  exact h

theorem integral_moll_of_nonneg_measurable (n : ℕ) {f : Torus d → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hfm : Measurable f) (hfi : Integrable f (haar d)) :
    ∫ y, moll n f y ∂haar d = ∫ y, f y ∂haar d := by
  have hm : Measurable (moll n f) := measurable_moll n hfi
  have heq : ∫⁻ y, ENNReal.ofReal (moll n f y) = ∫⁻ y, ENNReal.ofReal (f y) := by
    refine lintegral_eq_of_lift_eq n (ENNReal.measurable_ofReal.comp hm)
      (ENNReal.measurable_ofReal.comp hfm) fun x => ?_
    have := integrable_phiSeq_mul n hfi x
    rw [show moll n f (liftT x) = mollL n (f ∘ liftT) x from congrFun (moll_comp_liftT n f) x,
      mollL_apply']
    simp only [Function.comp_apply]
    rw [ofReal_integral_eq_lintegral_ofReal this
        (Eventually.of_forall fun s => mul_nonneg (phiSeq_nonneg n s) (hf0 _))]
    refine lintegral_congr fun s => ?_
    rw [ENNReal.ofReal_mul (phiSeq_nonneg n s)]
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (moll_nonneg n hf0))
      hm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfm.aestronglyMeasurable, heq]

theorem integral_moll_of_measurable (n : ℕ) {f : Torus d → ℝ} (hfm : Measurable f)
    (hf : Integrable f (haar d)) : ∫ y, moll n f y ∂haar d = ∫ y, f y ∂haar d := by
  set p : Torus d → ℝ := fun z => max (f z) 0 with hp
  set q : Torus d → ℝ := fun z => max (-f z) 0 with hq
  have hpm : Measurable p := hfm.max measurable_const
  have hqm : Measurable q := hfm.neg.max measurable_const
  have hpi : Integrable p (haar d) := hf.pos_part
  have hqi : Integrable q (haar d) := hf.neg_part
  have hfpq : f = fun z => p z - q z := by
    funext z; simp only [hp, hq]
    rcases le_total 0 (f z) with h | h
    · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
  have mi : ∀ {g : Torus d → ℝ}, Measurable g → Integrable g (haar d) →
      Integrable (moll n g) (haar d) := fun hg hgi =>
    ⟨(measurable_moll n hgi).aestronglyMeasurable,
      (lintegral_moll_le n hgi).trans_lt hgi.2⟩
  rw [hfpq] at hf ⊢
  have e : moll n (fun z => p z - q z) = fun y => moll n p y - moll n q y :=
    funext fun y => moll_sub n hpi hqi y
  rw [e, integral_sub (mi hpm hpi) (mi hqm hqi), integral_sub hpi hqi,
    integral_moll_of_nonneg_measurable n (fun z => le_max_right _ _) hpm hpi,
    integral_moll_of_nonneg_measurable n (fun z => le_max_right _ _) hqm hqi]

theorem integral_moll (n : ℕ) {f : Torus d → ℝ} (hf : Integrable f (haar d)) :
    ∫ y, moll n f y ∂haar d = ∫ y, f y ∂haar d := by
  set v := hf.aestronglyMeasurable.mk f with hv
  have hfv : f =ᵐ[haar d] v := hf.aestronglyMeasurable.ae_eq_mk
  rw [moll_congr_ae n hfv, integral_congr_ae hfv]
  exact integral_moll_of_measurable n
    hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable (hf.congr hfv)

/-- Pointwise Jensen for a probability measure and a nonnegative integrable function. -/
theorem ofReal_map_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {Φ : ℝ → ℝ} (hΦc : ConvexOn ℝ (Set.Ici 0) Φ)
    (hΦcont : Continuous Φ) (hΦ0 : ∀ x, 0 ≤ x → 0 ≤ Φ x) {g : α → ℝ} (hg0 : ∀ s, 0 ≤ g s)
    (hgi : Integrable g μ) :
    ENNReal.ofReal (Φ (∫ s, g s ∂μ)) ≤ ∫⁻ s, ENNReal.ofReal (Φ (g s)) ∂μ := by
  by_cases htop : ∫⁻ s, ENNReal.ofReal (Φ (g s)) ∂μ = ⊤
  · rw [htop]; exact le_top
  have hmeas : AEStronglyMeasurable (fun s => Φ (g s)) μ :=
    hΦcont.comp_aestronglyMeasurable hgi.aestronglyMeasurable
  have hgΦ : Integrable (fun s => Φ (g s)) μ := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun s => hΦ0 _ (hg0 s))]
    exact lt_top_iff_ne_top.mpr htop
  have hJ := hΦc.map_integral_le hΦcont.continuousOn isClosed_Ici
    (Eventually.of_forall fun s => hg0 s) hgi hgΦ
  rw [← ofReal_integral_eq_lintegral_ofReal hgΦ (Eventually.of_forall fun s => hΦ0 _ (hg0 s))]
  exact ENNReal.ofReal_le_ofReal hJ

theorem lintegral_convex_moll_le (n : ℕ) {Φ : ℝ → ℝ} (hΦc : ConvexOn ℝ (Set.Ici 0) Φ)
    (hΦcont : Continuous Φ) (hΦ0 : ∀ x, 0 ≤ x → 0 ≤ Φ x) {f : Torus d → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfm : Measurable f) (hfi : Integrable f (haar d)) :
    ∫⁻ y, ENNReal.ofReal (Φ (moll n f y)) ∂haar d ≤ ∫⁻ y, ENNReal.ofReal (Φ (f y)) ∂haar d := by
  have hm : Measurable (moll n f) := measurable_moll n hfi
  refine lintegral_le_of_lift_le n (ENNReal.measurable_ofReal.comp (hΦcont.measurable.comp hm))
    (ENNReal.measurable_ofReal.comp (hΦcont.measurable.comp hfm)) fun x => ?_
  rw [show moll n f (liftT x) = mollL n (f ∘ liftT) x from congrFun (moll_comp_liftT n f) x,
    mollL_comp_liftT_eq_integral]
  have hgi : Integrable (fun s => f (liftT (x - s))) (mollMeasure n) :=
    (integrable_mollMeasure_iff n _).mpr (integrable_phiSeq_mul n hfi x)
  refine (ofReal_map_integral_le (mollMeasure n) hΦc hΦcont hΦ0 (fun s => hf0 _) hgi).trans ?_
  have hgm : Measurable fun s : Fin d → ℝ => ENNReal.ofReal (Φ (f (liftT (x - s)))) :=
    ENNReal.measurable_ofReal.comp (hΦcont.measurable.comp
      (hfm.comp (measurable_liftT.comp (measurable_const.sub measurable_id))))
  exact (lintegral_mollMeasure n hgm).le

end SharpLSI.FL
