import DGPS.FiniteN.Tools.UniformVonMises
import DGPS.FiniteN.Tools.UnitTorusNormalization

/-!
# Weak angular derivative versus classical derivative (FIN015c)

For smooth `2π`-periodic functions the weak angular derivative chosen by `vmGrad` agrees a.e.
with the classical derivative `angDeriv`, and the product (`TP`) carré-du-champ built from `vmGamma`
agrees a.e. with the squared classical angular partial derivatives `angParticlePartial`.
-/

open MeasureTheory Real Set
open scoped ContDiff ENNReal

namespace DGPS.FiniteN.Tools

open DGPS DGPS.Circle.AngularNormalization DGPS.FiniteN.Tools.UniformVonMises
  DGPS.FiniteN.UnitTorusNormalization DGPS.FiniteN.Tools.BoundedComparison

/-- Smooth periodic functions are in `AngularH1`. -/
theorem angularH1_of_smooth {f : AngCircle → ℝ} (hf : IsSmoothAngular f) : AngularH1 f :=
  ⟨_, smooth_isWeakDeriv hf⟩

/-- Weak angular derivatives are unique a.e. -/
theorem angularWeakDeriv_ae_eq {u g g' : AngCircle → ℝ} (h : IsAngularWeakDeriv u g)
    (h' : IsAngularWeakDeriv u g') : g =ᵐ[angHaar] g' := by
  have h1 := ((isWeakGradient_comp_iff u g).1 h).ae_eq ((isWeakGradient_comp_iff u g').1 h')
  have h2 : (g ∘ angEquiv) =ᵐ[haar 1] (g' ∘ angEquiv) := by
    filter_upwards [h1] with x hx
    have := congrArg (fun v => v 0) hx
    simp only [physGrad_apply] at this
    have hp : (2 * π) ≠ 0 := Real.two_pi_pos.ne'
    exact mul_left_cancel₀ hp this
  have := measurePreserving_angEquiv.symm.quasiMeasurePreserving.ae_eq_comp h2
  simpa [Function.comp_def] using this

/-- (FIN015c, 1) For smooth periodic `f`, `vmGrad f` is the classical derivative a.e. -/
theorem vmGrad_eq_deriv_ae {f : AngCircle → ℝ} (hf : IsSmoothAngular f) :
    vmGrad f =ᵐ[angHaar] angDeriv f :=
  angularWeakDeriv_ae_eq (vmGrad_spec (angularH1_of_smooth hf)) (smooth_isWeakDeriv hf)

/-- (FIN015c, 1) `vmGamma f` is `ofReal (f'^2)` a.e. -/
theorem vmGamma_eq_deriv_ae {f : AngCircle → ℝ} (hf : IsSmoothAngular f) :
    vmGamma f =ᵐ[angHaar] fun θ => ENNReal.ofReal (angDeriv f θ ^ 2) := by
  filter_upwards [vmGrad_eq_deriv_ae hf] with θ hθ
  simp [vmGamma, hθ]


/-! ### Product version -/

lemma angSec_coe_self (θ : AngCircle) : ((angSec θ : ℝ) : AngCircle) = θ := by
  unfold angSec; exact AddCircle.coe_equivIoc

/-- The lift of `F` to `ℝⁿ`. -/
noncomputable def liftAng {n : ℕ} (F : (Fin n → AngCircle) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun s => F fun k => (s k : AngCircle)

lemma slice_eq_comp_update {n : ℕ} (F : (Fin n → AngCircle) → ℝ) (i : Fin n)
    (x : Fin n → AngCircle) (s : ℝ) :
    slice i F x (s : AngCircle) =
      liftAng F (Function.update (fun k => angSec (x k)) i s) := by
  unfold slice liftAng
  congr 1
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [Function.update_of_ne h, angSec_coe_self]

lemma isSmoothAngular_slice {n : ℕ} {F : (Fin n → AngCircle) → ℝ}
    (hF : ContDiff ℝ ∞ (liftAng F)) (i : Fin n) (x : Fin n → AngCircle) :
    IsSmoothAngular (slice i F x) := by
  unfold IsSmoothAngular
  have : (fun s : ℝ => slice i F x (s : AngCircle)) =
      liftAng F ∘ Function.update (fun k => angSec (x k)) i := by
    funext s; exact slice_eq_comp_update F i x s
  rw [this]
  exact hF.comp (contDiff_update _ _ _)

lemma angParticlePartial_eq_angDeriv_slice {N : ℕ+} {F : AngParticleSpace N → ℝ}
    (hF : IsSmoothAngParticle F) (i : Fin N) (x : AngParticleSpace N) :
    angParticlePartial i F x = angDeriv (slice i F x) (x i) := by
  have hF' : ContDiff ℝ ∞ (liftAng F) := hF
  unfold angDeriv angParticlePartial
  have hfun : (fun s : ℝ => slice i F x (s : AngCircle)) =
      liftAng F ∘ Function.update (fun k => angSec (x k)) i := by
    funext s; exact slice_eq_comp_update F i x s
  rw [hfun]
  have hd := hasDerivAt_update (fun k => angSec (x k)) i (angSec (x i))
  have hupd : Function.update (fun k => angSec (x k)) i (angSec (x i)) = fun k => angSec (x k) :=
    Function.update_eq_self _ _
  have hF1 : HasFDerivAt (liftAng F) (fderiv ℝ (liftAng F) fun k => angSec (x k))
      (Function.update (fun k => angSec (x k)) i (angSec (x i))) := by
    rw [hupd]
    exact ((hF'.differentiable (by simp)) _).hasFDerivAt
  have := (hF1.comp_hasDerivAt (angSec (x i)) hd).deriv
  rw [this]
  rfl

theorem ae_eq_pi_of_sections {α : Type*} [MeasurableSpace α] {n : ℕ} (μs : Fin n → Measure α)
    [∀ i, IsProbabilityMeasure (μs i)] (i : Fin n) {E T : (Fin n → α) → ℝ≥0∞}
    (hE : AEMeasurable E (Measure.pi μs)) (hT : Measurable T)
    (hsec : ∀ x : Fin n → α, ∀ᵐ a ∂μs i, E (Function.update x i a) = T (Function.update x i a)) :
    E =ᵐ[Measure.pi μs] T := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
  have : Nonempty α := nonempty_of_isProbabilityMeasure (μs i)
  obtain ⟨a0⟩ := this
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) i with he
  set e2 : (Fin (m + 1) → α) ≃ᵐ (Fin m → α) × α := e.trans MeasurableEquiv.prodComm with he2
  have hmp : MeasurePreserving e (Measure.pi μs)
      ((μs i).prod (Measure.pi fun j => μs (i.succAbove j))) := measurePreserving_piFinSuccAbove μs i
  have hmp2 : MeasurePreserving e2 (Measure.pi μs)
      ((Measure.pi fun j => μs (i.succAbove j)).prod (μs i)) :=
    (Measure.measurePreserving_swap).comp hmp
  have hsymm : ∀ (y : Fin m → α) (a : α), e2.symm (y, a) = Fin.insertNth i a y := fun y a => rfl
  have hupd : ∀ (y : Fin m → α) (a : α),
      e2.symm (y, a) = Function.update (e2.symm (y, a0)) i a := by
    intro y a
    rw [hsymm, hsymm, Fin.update_insertNth]
  have hE2 : AEMeasurable (E ∘ e2.symm) ((Measure.pi fun j => μs (i.succAbove j)).prod (μs i)) :=
    hE.comp_quasiMeasurePreserving (hmp2.symm e2).quasiMeasurePreserving
  set G := hE2.mk (E ∘ e2.symm) with hG
  have hGm : Measurable G := hE2.measurable_mk
  have hEG : (E ∘ e2.symm) =ᵐ[(Measure.pi fun j => μs (i.succAbove j)).prod (μs i)] G :=
    hE2.ae_eq_mk
  obtain ⟨B, hBsub, hBm, hB0⟩ := exists_measurable_superset_of_null (μ :=
    (Measure.pi fun j => μs (i.succAbove j)).prod (μs i)) (s := {z | (E ∘ e2.symm) z ≠ G z}) hEG
  have hB1 := (Measure.measure_prod_null hBm).1 hB0
  have hTm : Measurable (T ∘ e2.symm) := hT.comp e2.symm.measurable
  have hS : MeasurableSet {z | G z ≠ (T ∘ e2.symm) z} := (measurableSet_eq_fun hGm hTm).compl
  have hS0 : ((Measure.pi fun j => μs (i.succAbove j)).prod (μs i)) {z | G z ≠ (T ∘ e2.symm) z} = 0 := by
    rw [Measure.measure_prod_null hS]
    filter_upwards [hB1] with y hy
    have hy' : ∀ᵐ a ∂μs i, (y, a) ∉ B := by
      exact measure_eq_zero_iff_ae_notMem.mp hy
    have hs := hsec (e2.symm (y, a0))
    have key : ∀ᵐ a ∂μs i, G (y, a) = (T ∘ e2.symm) (y, a) := by
      filter_upwards [hy', hs] with a h1 h2
      have h3 : (E ∘ e2.symm) (y, a) = G (y, a) := by
        by_contra hne
        exact h1 (hBsub hne)
      rw [← h3]
      simp only [Function.comp_apply]
      rw [hupd y a] at *
      exact h2
    exact ae_iff.mp key
  have hGT : G =ᵐ[(Measure.pi fun j => μs (i.succAbove j)).prod (μs i)] (T ∘ e2.symm) :=
    measure_eq_zero_iff_ae_notMem.mp hS0 |>.mono fun z hz => by simpa using hz
  have h4 := (hEG.trans hGT)
  have h5 := hmp2.quasiMeasurePreserving.ae_eq_comp h4
  simpa [Function.comp_def] using h5


lemma measurable_liftAng_comp {N : ℕ+} {F : AngParticleSpace N → ℝ} (hF : IsSmoothAngParticle F) :
    Measurable F := by
  have hc : Continuous (liftAng F) := (show ContDiff ℝ ∞ (liftAng F) from hF).continuous
  have h : F = liftAng F ∘ fun θ k => angSec (θ k) := by
    funext θ; unfold liftAng; simp [angSec_coe_self]
  rw [h]
  exact hc.measurable.comp (Measurable.of_eval fun k => measurable_angSec.comp (measurable_pi_apply k))

lemma measurable_angParticlePartial {N : ℕ+} {F : AngParticleSpace N → ℝ}
    (i : Fin N) : Measurable (angParticlePartial i F) := by
  unfold angParticlePartial
  exact (measurable_fderiv_apply_const ℝ (fun s : Fin N → ℝ => F fun k => (s k : AngCircle))
    (Pi.single i 1)).comp
    (Measurable.of_eval fun k => measurable_angSec.comp (measurable_pi_apply k))

lemma exists_bound_angParticle {N : ℕ+} {F : AngParticleSpace N → ℝ}
    (hF : IsSmoothAngParticle F) : ∃ C : ℝ, ∀ θ, ‖F θ‖ ≤ C := by
  have hc : Continuous (liftAng F) := (show ContDiff ℝ ∞ (liftAng F) from hF).continuous
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin N => Set.Icc (0 : ℝ) (2 * π)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun θ => ?_⟩
  have h : F θ = liftAng F fun k => angSec (θ k) := by
    unfold liftAng; simp [angSec_coe_self]
  rw [h]
  refine hC _ fun k _ => ?_
  have := (AddCircle.equivIoc (2 * π) 0 (θ k)).property
  simp only [zero_add] at this
  exact ⟨this.1.le, this.2⟩

/-- Smooth periodic functions on the angular torus are `L²` for every probability product. -/
lemma memLp_of_smooth {N : ℕ+} {F : AngParticleSpace N → ℝ} (hF : IsSmoothAngParticle F)
    (μs : Fin N → Measure AngCircle) [∀ i, IsProbabilityMeasure (μs i)] :
    MemLp F 2 (Measure.pi μs) := by
  obtain ⟨C, hC⟩ := exists_bound_angParticle hF
  exact MemLp.of_bound (measurable_liftAng_comp hF).aestronglyMeasurable C (ae_of_all _ hC)

/-- (FIN015c, 2, pointwise) Along every coordinate and for every `μs i ≪ angHaar`, the
`vmGamma`-density of a smooth periodic `F` is `ofReal (∂ᵢF ^ 2)` a.e. in the product measure,
provided it is a.e.-measurable (the `aem` field of `TP`; this cannot be dropped, since `vmGrad`
is an arbitrary `Classical.choose`). -/
theorem dens_vmGamma_eq_classical_ae {N : ℕ+} (μs : Fin N → Measure AngCircle)
    [∀ i, IsProbabilityMeasure (μs i)] (hac : ∀ i, μs i ≪ angHaar)
    {F : AngParticleSpace N → ℝ} (hF : IsSmoothAngParticle F) (i : Fin N)
    (hE : AEMeasurable (dens vmGamma F i) (Measure.pi μs)) :
    dens vmGamma F i =ᵐ[Measure.pi μs] fun x => ENNReal.ofReal (angParticlePartial i F x ^ 2) := by
  have hF' : ContDiff ℝ ∞ (liftAng F) := hF
  refine ae_eq_pi_of_sections μs i hE
    ((measurable_angParticlePartial i).pow_const 2 |>.ennreal_ofReal) fun x => ?_
  have hsl : ∀ a, slice i F (Function.update x i a) = slice i F x := fun a => by
    unfold slice; funext b; simp
  filter_upwards [(hac i).ae_eq (vmGamma_eq_deriv_ae (isSmoothAngular_slice hF' i x))] with a ha
  have hp := angParticlePartial_eq_angDeriv_slice hF i (Function.update x i a)
  rw [hsl a] at hp
  simp only [Function.update_self] at hp
  unfold dens
  rw [hsl a, hp]
  simpa using ha

/-- A smooth periodic `F` is a `TP AngularH1 vmGamma` test as soon as the carré-du-champ densities
are a.e. measurable (the only `TP` field that is not forced by smoothness). -/
theorem tp_of_smooth {N : ℕ+} (μs : Fin N → Measure AngCircle)
    [∀ i, IsProbabilityMeasure (μs i)] {F : AngParticleSpace N → ℝ} (hF : IsSmoothAngParticle F)
    (haem : ∀ i, AEMeasurable (dens vmGamma F i) (Measure.pi μs)) :
    TP AngularH1 vmGamma μs F where
  meas := measurable_liftAng_comp hF
  memLp := memLp_of_smooth hF μs
  sm := fun x i => angularH1_of_smooth (isSmoothAngular_slice (show ContDiff ℝ ∞ (liftAng F) from hF) i x)
  aem := haem

/-- (FIN015c, 2) For smooth periodic `F` that is a `TP AngularH1 vmGamma` test, the `TP`
carré du champ equals the squared classical angular partial derivatives a.e. -/
theorem tp_vmGamma_eq_classical_ae {N : ℕ+} (μs : Fin N → Measure AngCircle)
    [∀ i, IsProbabilityMeasure (μs i)] (hac : ∀ i, μs i ≪ angHaar)
    {F : AngParticleSpace N → ℝ} (hF : IsSmoothAngParticle F)
    (hT : TP AngularH1 vmGamma μs F) :
    (∀ i, dens vmGamma F i =ᵐ[Measure.pi μs]
        fun x => ENNReal.ofReal (angParticlePartial i F x ^ 2)) ∧
    ((fun x => ∑ i, dens vmGamma F i x) =ᵐ[Measure.pi μs]
        fun x => ENNReal.ofReal (∑ i, angParticlePartial i F x ^ 2)) ∧
    ∫⁻ x, ∑ i, dens vmGamma F i x ∂Measure.pi μs =
      ∫⁻ x, ENNReal.ofReal (∑ i, angParticlePartial i F x ^ 2) ∂Measure.pi μs := by
  have h1 : ∀ i, dens vmGamma F i =ᵐ[Measure.pi μs]
      fun x => ENNReal.ofReal (angParticlePartial i F x ^ 2) :=
    fun i => dens_vmGamma_eq_classical_ae μs hac hF i (hT.aem i)
  have h2 : (fun x => ∑ i, dens vmGamma F i x) =ᵐ[Measure.pi μs]
      fun x => ENNReal.ofReal (∑ i, angParticlePartial i F x ^ 2) := by
    filter_upwards [ae_all_iff.2 h1] with x hx
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
    exact Finset.sum_congr rfl fun i _ => hx i
  exact ⟨h1, h2, lintegral_congr_ae h2⟩

/-- The von Mises law is absolutely continuous with respect to `angHaar`, so the hypothesis
`hac` of `tp_vmGamma_eq_classical_ae` holds for `μs i = vmLaw (w i)`. -/
theorem vmLaw_absolutelyContinuous (w : EuclideanSpace ℝ (Fin 2)) : vmLaw w ≪ angHaar :=
  withDensity_absolutelyContinuous _ _

end DGPS.FiniteN.Tools
