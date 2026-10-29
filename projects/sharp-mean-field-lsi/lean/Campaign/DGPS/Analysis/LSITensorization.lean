import DGPS.Ported.TorusLSI
import DGPS.FiniteN.Tools.Rothaus
import DGPS.Foundations.WeakContractions
import DGPS.Analysis.CircleMoments

/-!
# Tensorization of the normalized logarithmic Sobolev inequality (FOU014)

Concrete form on the Haar unit torus: the one-site hypothesis `HaarLSI 1 a` (the normalized LSI
of rate `a` on the circle `𝕋¹`, for every `H¹` function, with nonnormalized `f` and zero entropy
included through `homogeneousEntropy`) tensorizes to every `𝕋^d`, and a one-coordinate lift
gives the converse for `d ≥ 1`, hence equality of the optimal rates.

* `DGPS.Analysis.HaarLSI`
* `DGPS.Analysis.tensorization_of_normalized_lsi`
* `DGPS.Analysis.haarLSI_iff_of_pos`, `DGPS.Analysis.haarLSIRate_eq`
-/

namespace DGPS.Analysis

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

/-- Haar log-Sobolev inequality at rate `a` on `𝕋^d`. -/
def HaarLSI (d : ℕ) (a : ℝ) : Prop :=
  ∀ (f : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient f g →
    homogeneousEntropy (haar d) (fun x => f x ^ 2) ≤
      ENNReal.ofReal (2 / a) * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂haar d

theorem norm_sq_eq_sqNorm {d : ℕ} (v : Tangent d) :
    ‖v‖ ^ 2 = SharpLSI.sqNorm (fun k => v k) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [SharpLSI.sqNorm]

theorem legacy_memH1 {d : ℕ} {f : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient f g) :
    SharpLSI.MemH1 (SharpLSI.haar d) f ∧
      (∀ᵐ x ∂haar d, SharpLSI.weakGrad f x = fun k => g x k) := by
  have hw := h.isWeakGrad
  have hex : SharpLSI.HasWeakGrad f := ⟨_, hw⟩
  have hae : ∀ᵐ x ∂haar d, SharpLSI.weakGrad f x = fun k => g x k := by
    have hsel : SharpLSI.IsWeakGrad f (SharpLSI.weakGrad f) := by
      simp only [SharpLSI.weakGrad, hex, ↓reduceDIte]; exact hex.choose_spec
    exact SharpLSI.weakGrad_ae_unique hsel hw
  refine ⟨⟨hex, h.memLp, ?_⟩, hae⟩
  have := h.memLp_grad.norm
  refine this.ae_eq ?_
  filter_upwards [hae] with x hx
  rw [hx]
  have := norm_sq_eq_sqNorm (g x)
  rw [← Real.sqrt_sq (norm_nonneg (g x)), this]

theorem homogeneousEntropy_le_of_legacy {d : ℕ} {a : ℝ} (ha : 0 < a)
    (hc : DGPS.Ported.TorusLSI.CircleLSI a) : HaarLSI d a := by
  intro f g h
  obtain ⟨hH, hae⟩ := legacy_memH1 h
  have hi : Integrable (fun x => f x ^ 2) (haar d) := h.memLp.integrable_sq
  rw [DGPS.FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hi]
  have := DGPS.Ported.TorusLSI.lsi_torus_H1 ha hc hH
  refine this.trans (le_of_eq ?_)
  unfold SharpLSI.dirichlet
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx, ← norm_sq_eq_sqNorm]


theorem integral_haar1_secT (g : ℝ → ℝ) :
    ∫ y, g (SharpLSI.secT y 0) ∂haar 1 = ∫ t in Ioc (0 : ℝ) 1, g t :=
  SharpLSI.integral_torus1_secT g

open SharpLSI in
theorem circleLSI_of_haarLSI {a : ℝ} (ha : 0 < a) (H : HaarLSI 1 a) :
    DGPS.Ported.TorusLSI.CircleLSI a := by
  intro φ hφ hper hpos
  set u : Torus 1 → ℝ := fun z => φ (secT z 0) with hu
  have hper' : ∀ (t : ℝ) (n : ℤ), φ (t + n) = φ t := fun t n => periodic_int' hper t n
  have hulift : u ∘ torusLift = fun x => φ (x 0) := by
    funext x
    obtain ⟨m, hm⟩ := secT_liftT_eq x
    simp only [Function.comp_apply, hu, torusLift, hm, Pi.add_apply, intVec]
    rw [hper']
  have hus : IsSmoothPeriodic u := by
    unfold IsSmoothPeriodic
    rw [hulift]; exact hφ.comp (contDiff_apply ℝ ℝ (0 : Fin 1))
  have hW := hus.isWeakGradient
  have h := H u _ hW
  have hφc : Continuous φ := hφ.continuous
  -- the gradient
  have hgrad : ∀ x : Torus 1, coordPartial 0 u x = deriv φ (secT x 0) := by
    intro x
    unfold coordPartial
    rw [hulift]
    have h1 : HasDerivAt φ (deriv φ (secT x 0)) (secT x 0) :=
      (hφ.differentiable (by simp) _).hasDerivAt
    have hd := h1.comp_hasFDerivAt (secT x) (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) (secT x))
    rw [show (fun x : Fin 1 → ℝ => φ (x 0)) = φ ∘ (fun f : Fin 1 → ℝ => f 0) from rfl, hd.fderiv]
    simp
  have hnorm : ∀ x : Torus 1, ‖smoothGrad u x‖ ^ 2 = deriv φ (secT x 0) ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    simp [hgrad]
  have hgi : Integrable (fun x => ‖smoothGrad u x‖ ^ 2) (haar 1) := hW.memLp_grad.norm.integrable_sq
  have hR : ∫⁻ x, ENNReal.ofReal (‖smoothGrad u x‖ ^ 2) ∂haar 1 =
      ENNReal.ofReal (∫ t in Ioc (0 : ℝ) 1, deriv φ t ^ 2) := by
    rw [← integral_haar1_secT (fun t => deriv φ t ^ 2),
      ← ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun x => sq_nonneg _)]
    congr 1
    exact integral_congr_ae (Eventually.of_forall hnorm)
  -- the entropy
  have hi : Integrable (fun x => u x ^ 2) (haar 1) := hW.memLp.integrable_sq
  have hmeas : Measurable (fun x => u x ^ 2) :=
    ((hφc.measurable.comp ((measurable_pi_apply 0).comp measurable_secT)).pow_const 2)
  obtain ⟨xm, hxm, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn
    (nonempty_Icc.2 zero_le_one) (hφc.pow 2).continuousOn
  obtain ⟨xM, hxM, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    (nonempty_Icc.2 zero_le_one) (hφc.pow 2).continuousOn
  have hmem : ∀ x : Torus 1, secT x 0 ∈ Icc (0 : ℝ) 1 := fun x => by
    have := (AddCircle.measurableEquivIoc 1 0 (x 0)).2
    simp only [zero_add] at this
    exact ⟨this.1.le, this.2⟩
  rw [DGPS.FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hi,
    ent_eq_ofReal_entR (c := φ xm ^ 2) (C := φ xM ^ 2) hmeas (pow_pos (hpos _) 2)
      (fun x => hmin (hmem x)) (fun x => hmax (hmem x)), hR] at h
  have hent : entR (haar 1) (fun x => u x ^ 2) =
      (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2 * Real.log (φ t ^ 2)) -
        (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2) * Real.log (∫ t in Ioc (0 : ℝ) 1, φ t ^ 2) := by
    unfold entR
    rw [show (fun x : Torus 1 => u x ^ 2 * Real.log (u x ^ 2)) =
      fun x => (fun t => φ t ^ 2 * Real.log (φ t ^ 2)) (secT x 0) from rfl,
      show (fun x : Torus 1 => u x ^ 2) = fun x => (fun t => φ t ^ 2) (secT x 0) from rfl,
      integral_haar1_secT (fun t => φ t ^ 2 * Real.log (φ t ^ 2)), integral_haar1_secT (fun t => φ t ^ 2)]
  rw [hent, ← ENNReal.ofReal_mul (by positivity)] at h
  have hRn : 0 ≤ ∫ t in Ioc (0 : ℝ) 1, deriv φ t ^ 2 := setIntegral_nonneg measurableSet_Ioc
    fun t _ => sq_nonneg _
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h


/-- Projection of `𝕋^d` to the circle `𝕋^1` onto coordinate `p`. -/
def coordProj {d : ℕ} (p : Fin d) (y : Torus d) : Torus 1 := fun _ => y p

theorem measurePreserving_coordProj {d : ℕ} (p : Fin d) :
    MeasurePreserving (coordProj p) (haar d) (haar 1) := by
  have h1 : MeasurePreserving (fun y : Torus d => y p) (haar d) (volume : Measure UnitAddCircle) :=
    measurePreserving_eval (fun _ : Fin d => (volume : Measure UnitAddCircle)) p
  have h2 := (volume_preserving_funUnique (Fin 1) UnitAddCircle).symm
  exact h2.comp h1

theorem coordProj_liftT {d : ℕ} (p : Fin d) (x : Fin d → ℝ) :
    coordProj p (torusLift x) = torusLift (fun _ : Fin 1 => x p) := rfl

theorem isSmoothPeriodic_comp_coordProj {d : ℕ} (p : Fin d) {v : Torus 1 → ℝ}
    (hv : IsSmoothPeriodic v) : IsSmoothPeriodic (v ∘ coordProj p) := by
  unfold IsSmoothPeriodic at *
  have : (v ∘ coordProj p) ∘ torusLift = (v ∘ torusLift) ∘ (fun x : Fin d → ℝ => fun _ : Fin 1 => x p) := rfl
  rw [this]
  exact hv.comp (contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ p)

theorem coordPartial_comp_coordProj {d : ℕ} (p : Fin d) {v : Torus 1 → ℝ}
    (hv : IsSmoothPeriodic v) (j : Fin d) (x : Torus d) :
    coordPartial j (v ∘ coordProj p) x = if j = p then coordPartial 0 v (coordProj p x) else 0 := by
  unfold coordPartial
  have : (v ∘ coordProj p) ∘ torusLift = (v ∘ torusLift) ∘ (fun x : Fin d → ℝ => fun _ : Fin 1 => x p) := rfl
  rw [this]
  have hL : HasFDerivAt (fun x : Fin d → ℝ => fun _ : Fin 1 => x p)
      (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.proj p) (SharpLSI.secT x) :=
    (ContinuousLinearMap.pi fun _ : Fin 1 => (ContinuousLinearMap.proj p : (Fin d → ℝ) →L[ℝ] ℝ)).hasFDerivAt
  have hv' : DifferentiableAt ℝ (v ∘ torusLift) (fun _ : Fin 1 => SharpLSI.secT x p) :=
    (hv.differentiable (by simp)) _
  rw [(hv'.hasFDerivAt.comp _ hL).fderiv]
  have hs : (fun _ : Fin 1 => SharpLSI.secT x p) = SharpLSI.secT (coordProj p x) := rfl
  rw [hs]
  by_cases hj : j = p
  · subst hj
    simp only [↓reduceIte, ContinuousLinearMap.comp_apply]
    congr 1
    funext i
    rw [Subsingleton.elim i 0]
    simp
  · simp only [hj, ↓reduceIte, ContinuousLinearMap.comp_apply]
    have : (ContinuousLinearMap.pi fun _ : Fin 1 => (ContinuousLinearMap.proj p : (Fin d → ℝ) →L[ℝ] ℝ))
        (Pi.single j 1) = 0 := by
      funext i
      simp [Ne.symm hj]
    rw [this, map_zero]


theorem tendsto_lintegral_enorm_of_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {h : ℕ → α → ℝ}
    (hh : ∀ n, AEStronglyMeasurable (h n) μ)
    (ht : Tendsto (fun n => eLpNorm (h n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ y, ‖h n y‖ₑ ∂μ) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun n => zero_le)
    (fun n => ?_)
  rw [← eLpNorm_one_eq_lintegral_enorm (hh n)]
  exact eLpNorm_le_eLpNorm_of_exponent_le (p := 1) (q := 2) (by norm_num)

/-- The lift of an `H¹(𝕋¹)` function to a function of one coordinate of `𝕋^d`. -/
theorem isWeakGradient_comp_coordProj {d : ℕ} (p : Fin d) {f : Torus 1 → ℝ} {g : Torus 1 → Tangent 1}
    (hf : IsWeakGradient f g) :
    IsWeakGradient (f ∘ coordProj p)
      (fun x => g (coordProj p x) 0 • (EuclideanSpace.single p (1 : ℝ) : Tangent d)) := by
  have hP := measurePreserving_coordProj p
  obtain ⟨v, hvs, hvw, hv1, hv2⟩ := exists_smooth_tendsto_H1 hf
  have hg0 : MemLp (fun z => g z 0) 2 (haar 1) := memLp_coord hf.memLp_grad 0
  have hG : MemLp (fun x => g (coordProj p x) 0 • (EuclideanSpace.single p (1 : ℝ) : Tangent d)) 2
      (haar d) :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single p (1 : ℝ) : Tangent d) :
      ℝ →L[ℝ] Tangent d).comp_memLp' (hg0.comp_measurePreserving hP)
  have hFm : MemLp (f ∘ coordProj p) 2 (haar d) := hf.memLp.comp_measurePreserving hP
  have hUm : ∀ n, MemLp (v n ∘ coordProj p) 2 (haar d) := fun n =>
    (hvw n).memLp.comp_measurePreserving hP
  refine IsWeakGradient.of_tendsto_L1 (U := fun n => v n ∘ coordProj p)
    (G := fun n => smoothGrad (v n ∘ coordProj p)) hFm hG
    (fun n => (isSmoothPeriodic_comp_coordProj p (hvs n)).isWeakGradient) ?_ ?_
  · refine tendsto_lintegral_enorm_of_eLpNorm (μ := haar d)
      (h := fun n y => (v n ∘ coordProj p) y - (f ∘ coordProj p) y)
      (fun n => ((hUm n).sub hFm).aestronglyMeasurable) ?_
    refine hv1.congr (fun n => ?_)
    exact (eLpNorm_comp_measurePreserving (g := fun z => v n z - f z)
      (((hvw n).memLp.sub hf.memLp).aestronglyMeasurable) hP).symm
  · intro j
    refine tendsto_lintegral_enorm_of_eLpNorm (μ := haar d)
      (h := fun n y => smoothGrad (v n ∘ coordProj p) y j -
        (g (coordProj p y) 0 • (EuclideanSpace.single p (1 : ℝ) : Tangent d)) j)
      (fun n => ((memLp_coord (isSmoothPeriodic_comp_coordProj p (hvs n)).isWeakGradient.memLp_grad j).sub
        (memLp_coord hG j)).aestronglyMeasurable) ?_
    by_cases hj : j = p
    · subst hj
      refine (hv2 0).congr (fun n => ?_)
      have hm : AEStronglyMeasurable (fun z => smoothGrad (v n) z 0 - g z 0) (haar 1) :=
        ((memLp_coord (hvw n).memLp_grad 0).sub hg0).aestronglyMeasurable
      rw [← eLpNorm_comp_measurePreserving hm hP]
      congr 1
      funext y
      simp [coordPartial_comp_coordProj j (hvs n)]
    · have : ∀ n, (fun y => smoothGrad (v n ∘ coordProj p) y j -
          (g (coordProj p y) 0 • (EuclideanSpace.single p (1 : ℝ) : Tangent d)) j) = 0 := by
        intro n
        funext y
        simp [coordPartial_comp_coordProj p (hvs n), hj]
      simp only [this, eLpNorm_zero]
      exact tendsto_const_nhds


theorem measurable_entropyIntegrand (a : ℝ) : Measurable (entropyIntegrand a) := by
  unfold entropyIntegrand
  fun_prop

theorem homogeneousEntropy_comp_measurePreserving {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} {P : α → β}
    (hP : MeasurePreserving P μ ν) {v : β → ℝ} (hv : AEStronglyMeasurable v ν) :
    homogeneousEntropy μ (fun x => v (P x)) = homogeneousEntropy ν v := by
  have hv' : AEStronglyMeasurable v (Measure.map P μ) := by rw [hP.map_eq]; exact hv
  have hI : ∫ x, v (P x) ∂μ = ∫ y, v y ∂ν := by
    rw [← hP.map_eq, integral_map hP.aemeasurable hv']
  unfold homogeneousEntropy
  rw [hI]
  split_ifs with h0
  · rfl
  · have hm : AEMeasurable (fun y => ENNReal.ofReal (entropyIntegrand (∫ y, v y ∂ν) (v y)))
        (Measure.map P μ) := by
      rw [hP.map_eq]
      exact (ENNReal.measurable_ofReal.comp (measurable_entropyIntegrand _)).comp_aemeasurable
        hv.aemeasurable
    have := lintegral_map' hm hP.aemeasurable
    rw [hP.map_eq] at this
    exact this.symm

theorem haarLSI_one_of_haarLSI {d : ℕ} (hd : 0 < d) {a : ℝ} (H : HaarLSI d a) : HaarLSI 1 a := by
  intro f g hf
  set p : Fin d := ⟨0, hd⟩
  have hP := measurePreserving_coordProj p
  have h := H _ _ (isWeakGradient_comp_coordProj p hf)
  have hsq : AEStronglyMeasurable (fun z => f z ^ 2) (haar 1) := hf.memLp.integrable_sq.aestronglyMeasurable
  have e1 := homogeneousEntropy_comp_measurePreserving hP hsq
  have hn : ∀ x : Torus d, ‖g (coordProj p x) 0 • (EuclideanSpace.single p (1 : ℝ) : Tangent d)‖ ^ 2 =
      ‖g (coordProj p x)‖ ^ 2 := by
    intro x
    rw [norm_smul, mul_pow, EuclideanSpace.norm_sq_eq]
    simp [EuclideanSpace.norm_sq_eq]
  have hg : AEMeasurable (fun z => ENNReal.ofReal (‖g z‖ ^ 2)) (haar 1) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((hf.memLp_grad.aestronglyMeasurable.norm.pow 2).aemeasurable))
  have e2 : ∫⁻ x, ENNReal.ofReal (‖g (coordProj p x)‖ ^ 2) ∂haar d =
      ∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2) ∂haar 1 := by
    rw [← hP.map_eq, lintegral_map' (by rwa [hP.map_eq]) hP.aemeasurable]
  simp only [hn, Function.comp_def] at h
  rw [e2] at h
  exact e1 ▸ h


/-- **Tensorization of the normalized LSI** (FOU014).  If the circle `𝕋¹` obeys
`Ent(f²) ≤ (2/a) ∫ |∇f|²` for all `f ∈ H¹(𝕋¹)` (nonnormalized `f` and zero entropy included,
via `homogeneousEntropy`), then so does every `𝕋^d`, on the full product Sobolev domain. -/
theorem tensorization_of_normalized_lsi {a : ℝ} (ha : 0 < a) (H : HaarLSI 1 a) (d : ℕ) :
    HaarLSI d a :=
  homogeneousEntropy_le_of_legacy ha (circleLSI_of_haarLSI ha H)

/-- A one-coordinate test: for `d ≥ 1`, the LSI on `𝕋^d` at rate `a > 0` is equivalent to the LSI
on the circle at rate `a`. -/
theorem haarLSI_iff_of_pos {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 < a) :
    HaarLSI d a ↔ HaarLSI 1 a :=
  ⟨haarLSI_one_of_haarLSI hd, fun H => tensorization_of_normalized_lsi ha H d⟩

/-- The optimal LSI rate on `𝕋^d`: the supremum of the admissible rates `a > 0`. -/
noncomputable def haarLSIRate (d : ℕ) : ℝ≥0∞ :=
  ⨆ (a : ℝ) (_ : 0 < a ∧ HaarLSI d a), ENNReal.ofReal a

/-- The optimal rate on `𝕋^d`, `d ≥ 1`, equals the optimal rate on the circle; in particular a
one-coordinate test bounds the optimal product rate from above. -/
theorem haarLSIRate_eq {d : ℕ} (hd : 0 < d) : haarLSIRate d = haarLSIRate 1 := by
  unfold haarLSIRate
  refine iSup_congr fun a => ?_
  refine iSup_congr_Prop ?_ fun _ => rfl
  exact ⟨fun h => ⟨h.1, (haarLSI_iff_of_pos hd h.1).1 h.2⟩,
    fun h => ⟨h.1, (haarLSI_iff_of_pos hd h.1).2 h.2⟩⟩

end DGPS.Analysis
