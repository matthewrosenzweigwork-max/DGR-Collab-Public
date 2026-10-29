import FullLabeledLSI.Paper.PermAvgFisher
import SharpSymmetricLSI.Paper.SemiconvexLip2
import SharpSymmetricLSI.Paper.TorusLipschitz
import SharpSymmetricLSI.Paper.EntFinite
import SharpSymmetricLSI.Paper.Defective6

/-!
# Lemma 5.1, Fisher part: concrete gradient fields

Classical/Lipschitz gradient fields on `Config N d` through the flat torus, smoothness of the
permutation average, and the equivariance/chain-rule/averaging facts feeding `pythagoras`.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff NNReal

namespace SharpLSI.FL

variable {N d : ℕ}

/-! ### Lifts and logarithms -/

theorem dist_liftT_le {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    dist (liftT a) (liftT b) ≤ dist a b := by
  refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
  show dist (a i : UnitAddCircle) (b i : UnitAddCircle) ≤ _
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  refine (QuotientAddGroup.norm_mk_le_norm).trans ?_
  rw [Real.norm_eq_abs, ← Real.dist_eq]
  exact dist_le_pi_dist a b i

theorem dist_unflat_le (y y' : UnitAddTorus (Fin N × Fin d)) :
    dist (unflat y) (unflat y') ≤ dist y y' := by
  refine (dist_pi_le_iff dist_nonneg).2 fun i => (dist_pi_le_iff dist_nonneg).2 fun k => ?_
  exact dist_le_pi_dist y y' (i, k)

theorem abs_log_sub_log_le {c a b : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / c := by
  have ha0 : 0 < a := hc.trans_le ha
  have hb0 : 0 < b := hc.trans_le hb
  have key : ∀ {x y : ℝ}, c ≤ x → c ≤ y → Real.log x - Real.log y ≤ |x - y| / c := by
    intro x y hx hy
    have hx0 : 0 < x := hc.trans_le hx
    have hy0 : 0 < y := hc.trans_le hy
    have h1 : Real.log x - Real.log y ≤ x / y - 1 := by
      rw [← Real.log_div hx0.ne' hy0.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    have h2 : x / y - 1 = (x - y) / y := by field_simp
    have h3 : (x - y) / y ≤ |x - y| / c :=
      (div_le_div_of_nonneg_right (le_abs_self _) hy0.le).trans
        (div_le_div_of_nonneg_left (abs_nonneg _) hc hy)
    linarith
  rw [abs_le]
  constructor
  · have := key hb ha
    rw [abs_sub_comm] at this
    linarith
  · exact key ha hb

theorem lipschitz_log_comp {α : Type*} [PseudoMetricSpace α] {f : α → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : ∀ x, c ≤ f x) {L : ℝ≥0} (hL : LipschitzWith L f) :
    LipschitzWith (L * (Real.toNNReal c)⁻¹) (fun x => Real.log (f x)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq]
  refine (abs_log_sub_log_le hc (hf x) (hf y)).trans ?_
  have h1 := hL.dist_le_mul x y
  rw [Real.dist_eq] at h1
  have : ((L * (Real.toNNReal c)⁻¹ : ℝ≥0) : ℝ) = L * c⁻¹ := by
    simp [Real.coe_toNNReal _ hc.le]
  rw [this, div_eq_mul_inv]
  calc |f x - f y| * c⁻¹ ≤ (L * dist x y) * c⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hc.le)
    _ = L * c⁻¹ * dist x y := by ring


/-! ### Smoothness of the permutation average -/

theorem isSmoothC_comp_perm {u : Config N d → ℝ} (hu : IsSmoothC u) (σ : Equiv.Perm (Fin N)) :
    IsSmoothC (fun X => u (X ∘ σ)) := by
  unfold IsSmoothC IsSmoothT at hu ⊢
  have h : ((fun X => u (X ∘ σ)) ∘ unflat) ∘ liftT =
      ((u ∘ unflat) ∘ liftT) ∘ (reidxCLM (permIdx (N := N) (d := d) σ).symm) := by
    funext x
    rfl
  rw [h]
  exact hu.comp (ContinuousLinearMap.contDiff (reidxCLM (permIdx (N := N) (d := d) σ).symm))

theorem isSmoothC_avgDens {u : Config N d → ℝ} (hu : IsSmoothC u) : IsSmoothC (avgDens u) := by
  have h : ∀ σ : Equiv.Perm (Fin N), ContDiff ℝ ∞ (((fun X => u (X ∘ σ)) ∘ unflat) ∘ liftT) :=
    fun σ => isSmoothC_comp_perm hu σ
  unfold IsSmoothC IsSmoothT
  have e : (avgDens u ∘ unflat) ∘ liftT = fun x => ((Nat.factorial N : ℝ))⁻¹ *
      ∑ σ : Equiv.Perm (Fin N), (((fun X => u (X ∘ σ)) ∘ unflat) ∘ liftT) x := by
    funext x
    rfl
  rw [e]
  exact contDiff_const.mul (ContDiff.sum fun σ _ => h σ)


/-! ### Classical gradient fields -/

/-- The classical gradient of a smooth function on `Config N d`, as a vector field. -/
def gradC (f : Config N d → ℝ) : VF N d := fun X q =>
  fderiv ℝ ((f ∘ unflat) ∘ liftT) (secT (flat X)) (Pi.single q 1)

theorem gradC_good {f : Config N d → ℝ} (hf : IsSmoothC f) : (gradC f).Good := by
  have hf' : ContDiff ℝ ∞ ((f ∘ unflat) ∘ liftT) := hf
  refine ⟨fun q => (measurable_smoothGrad hf' q).comp measurable_flat, ?_⟩
  choose C hC using fun q => smoothGrad_bdd hf' q
  exact ⟨∑ q, |C q|, fun X q => (hC q (flat X)).trans
    ((le_abs_self (C q)).trans (Finset.single_le_sum (f := fun q => |C q|)
      (fun q _ => abs_nonneg _) (Finset.mem_univ q)))⟩

theorem isWeakGrad_gradC {f : Config N d → ℝ} (hf : IsSmoothC f) :
    IsWeakGrad (f ∘ unflat) (fun y q => gradC f (unflat y) q) :=
  isWeakGrad_of_contDiff ((show ContDiff ℝ ∞ ((f ∘ unflat) ∘ liftT) from hf).of_le (by simp))

theorem isSmoothC_log {f : Config N d → ℝ} (hf : IsSmoothC f) (h0 : ∀ X, 0 < f X) :
    IsSmoothC (fun X => Real.log (f X)) := by
  unfold IsSmoothC IsSmoothT at hf ⊢
  exact hf.log fun x => (h0 _).ne'

theorem gradC_log_mul {f : Config N d → ℝ} (hf : IsSmoothC f) (h0 : ∀ X, 0 < f X)
    (X : Config N d) (q : Fin N × Fin d) :
    f X * gradC (fun X => Real.log (f X)) X q = gradC f X q := by
  have hf' : ContDiff ℝ ∞ ((f ∘ unflat) ∘ liftT) := hf
  have hd : HasFDerivAt ((f ∘ unflat) ∘ liftT) (fderiv ℝ ((f ∘ unflat) ∘ liftT) (secT (flat X)))
      (secT (flat X)) :=
    (hf'.differentiable (by simp) _).hasFDerivAt
  have hl := hd.log (by
    simp only [Function.comp, liftT_secT]
    exact (h0 _).ne')
  have e : ((fun X => Real.log (f X)) ∘ unflat) ∘ liftT =
      fun x => Real.log (((f ∘ unflat) ∘ liftT) x) := rfl
  unfold gradC
  rw [e, hl.fderiv]
  simp only [smul_apply, smul_eq_mul, Function.comp, liftT_secT]
  have : unflat (flat X) = X := rfl
  rw [this]
  field_simp [(h0 X).ne']


/-! ### Equivariance of gradients of symmetric functions -/

theorem ae_config_of_torus {P : UnitAddTorus (Fin N × Fin d) → Prop}
    (h : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin N × Fin d))), P y) :
    ∀ᵐ X ∂(volume : Measure (Config N d)), P (flat X) :=
  (measurePreserving_flat' N).quasiMeasurePreserving.ae h

/-- A weak gradient of a symmetric function is a.e. equivariant. -/
theorem act_ae_eq_of_symm {F : Config N d → ℝ} (hsym : ∀ (σ : Equiv.Perm (Fin N)) X, F (X ∘ σ) = F X)
    {G : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (h : IsWeakGrad (F ∘ unflat) G)
    (hF : Integrable (F ∘ unflat) volume) (hG : ∀ q, Integrable (fun y => G y q) volume)
    (σ : Equiv.Perm (Fin N)) :
    ∀ᵐ X ∂(volume : Measure (Config N d)), ∀ q,
      VF.act σ (fun X q => G (flat X) q) X q = G (flat X) q := by
  have h1 := isWeakGrad_perm σ h hF hG
  have e : (fun X => F (X ∘ σ)) ∘ unflat = F ∘ unflat := funext fun y => hsym σ _
  rw [e] at h1
  have h2 := weakGrad_ae_unique h1 h
  have h3 := ae_config_of_torus h2
  filter_upwards [h3] with X hX q
  exact congrFun hX q


theorem integrable_torus_of_goodField {V : VF N d} (hV : V.Good) (q : Fin N × Fin d) :
    Integrable (fun y : UnitAddTorus (Fin N × Fin d) => V (unflat y) q) volume := by
  obtain ⟨hm, C, hC⟩ := hV
  exact Integrable.of_bound ((hm q).comp measurable_unflat).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC _ _)

theorem integrable_torus_of_smoothC {u : Config N d → ℝ} (hu : IsSmoothC u) :
    Integrable (u ∘ unflat) (volume : Measure (UnitAddTorus (Fin N × Fin d))) :=
  (continuous_of_isSmoothT hu).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The gradient of the permutation average is the average of the permuted gradients (a.e.). -/
theorem gradC_avgDens_ae {u : Config N d → ℝ} (hu : IsSmoothC u) :
    ∀ᵐ X ∂(volume : Measure (Config N d)), ∀ q, gradC (avgDens u) X q =
      ((Nat.factorial N : ℝ))⁻¹ * ∑ σ : Equiv.Perm (Fin N), VF.act σ (gradC u) X q := by
  have hū := isWeakGrad_gradC (isSmoothC_avgDens hu)
  have hσ : ∀ σ : Equiv.Perm (Fin N), IsWeakGrad ((fun X => u (X ∘ σ)) ∘ unflat)
      (fun y q => VF.act σ (gradC u) (unflat y) q) := fun σ =>
    isWeakGrad_perm σ (isWeakGrad_gradC hu) (integrable_torus_of_smoothC hu)
      (integrable_torus_of_goodField (gradC_good hu))
  have hsum := (isWeakGrad_finsetSum Finset.univ (fun σ _ => hσ σ)).cmul
    ((Nat.factorial N : ℝ))⁻¹
  have e : avgDens u ∘ unflat = fun y => ((Nat.factorial N : ℝ))⁻¹ *
      ∑ σ : Equiv.Perm (Fin N), ((fun X => u (X ∘ σ)) ∘ unflat) y := rfl
  rw [e] at hū
  have h2 := weakGrad_ae_unique hū hsum
  have h3 := ae_config_of_torus h2
  filter_upwards [h3] with X hX q
  exact congrFun hX q


/-! ### The Lipschitz factor `log p` -/

/-- The Lipschitz (Rademacher) gradient field of a function on `Config N d`. -/
def lipField (f : Config N d → ℝ) : VF N d := fun X q => lipGrad (f ∘ unflat) (flat X) q

theorem lipschitz_lift {p : Config N d → ℝ} {L : ℝ≥0} (hL : LipschitzWith L p) :
    LipschitzWith L ((p ∘ unflat) ∘ liftT) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  simp only [Function.comp]
  refine (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ L.2)
  exact (dist_unflat_le _ _).trans (dist_liftT_le a b)

theorem isWeakGrad_logLip {p : Config N d → ℝ} {c : ℝ} (hc : 0 < c) (hpc : ∀ X, c ≤ p X)
    {L : ℝ≥0} (hL : LipschitzWith L p) :
    IsWeakGrad ((fun X => Real.log (p X)) ∘ unflat) (fun y q => lipField (fun X => Real.log (p X)) (unflat y) q) ∧
    (lipField (fun X => Real.log (p X))).Good := by
  have hlip := lipschitz_log_comp (c := c) hc (fun x => hpc _) (lipschitz_lift hL)
  have hcont : Continuous ((fun X => Real.log (p X)) ∘ unflat :
      UnitAddTorus (Fin N × Fin d) → ℝ) := (lipschitzWith_of_liftT hlip).continuous
  refine ⟨isWeakGrad_lipGrad hcont hlip, fun q => ?_, ((L * (Real.toNNReal c)⁻¹ : ℝ≥0) : ℝ), fun X q => ?_⟩
  · exact (measurable_lipGrad hcont q).comp measurable_flat
  · exact abs_lipGrad_le hlip _ q


/-! ### Assembly -/

theorem sqNorm_eq_dot (V : VF N d) (X : Config N d) : sqNorm (V X) = VF.dot V V X := by
  unfold sqNorm VF.dot
  exact Finset.sum_congr rfl fun q _ => pow_two _

theorem VF.dot_self_nonneg (V : VF N d) (X : Config N d) : 0 ≤ VF.dot V V X :=
  Finset.sum_nonneg fun q _ => mul_self_nonneg _

theorem integrable_mul_dot {u : Config N d → ℝ} (hum : Measurable u) {Cu : ℝ}
    (hu0 : ∀ x, 0 < u x) (huC : ∀ x, u x ≤ Cu) {V : VF N d} (hV : V.Good) :
    Integrable (fun X => u X * VF.dot V V X) (volume : Measure (Config N d)) := by
  obtain ⟨hm, B, hB⟩ := hV.dot hV
  exact integrable_bdd (hum.mul hm) (B := Cu * B) fun x => by
    rw [abs_mul, abs_of_pos (hu0 x)]
    exact mul_le_mul (huC x) (hB x) (abs_nonneg _) ((hu0 x).le.trans (huC x))

/-- `∫⁻ u |V|² = ofReal ∫ u |V|²`. -/
theorem lintegral_mul_dot {u : Config N d → ℝ} (hum : Measurable u) {Cu : ℝ}
    (hu0 : ∀ x, 0 < u x) (huC : ∀ x, u x ≤ Cu) {V : VF N d} (hV : V.Good) :
    ∫⁻ X, ENNReal.ofReal (u X * sqNorm (V X)) ∂(volume : Measure (Config N d)) =
      ENNReal.ofReal (∫ X, u X * VF.dot V V X ∂(volume : Measure (Config N d))) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_mul_dot hum hu0 huC hV)
    (Filter.Eventually.of_forall fun X => mul_nonneg (hu0 X).le (VF.dot_self_nonneg V X))]
  refine lintegral_congr fun X => ?_
  rw [sqNorm_eq_dot]


/-- Fisher part (5.2) of Lemma 5.1. -/
theorem permAvg_fisher (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hν : HasSmoothPosDensity ν) (p : Config N d → ℝ) (hp : ∀ X, 0 < p X)
    (hpL : ∃ L, LipschitzWith L p) (hps : IsSymmetric p)
    (hP1 : IsProbabilityMeasure ((volume : Measure (Config N d)).withDensity
      fun X => ENNReal.ofReal (p X))) :
    fisherInfoC ν ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (p X)) =
      fisherInfoC (permAvgAux ν) ((volume : Measure (Config N d)).withDensity
        fun X => ENNReal.ofReal (p X)) + fisherInfoC ν (permAvgAux ν) := by
  obtain ⟨u, hus, hu0, rfl⟩ := hν
  have huc : Continuous u := continuous_of_isSmoothC hus
  have hum : Measurable u := huc.measurable
  obtain ⟨L, hL⟩ := hpL
  have hpc : Continuous p := hL.continuous
  have hpm : Measurable p := hpc.measurable
  obtain ⟨cu, Cu, hcu, hu'⟩ := bdd_of_cont_pos huc hu0
  obtain ⟨cp, Cp, hcp, hp'⟩ := bdd_of_cont_pos hpc hp
  have hū' := avgDens_bounds hu'
  have hū0 : ∀ x, 0 < avgDens u x := fun x => lt_of_lt_of_le hcu (hū' x).1
  have hūm : Measurable (avgDens u) := measurable_avgDens hum
  have hu1b : ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ u x ∧ u x ≤ C := ⟨cu, Cu, hcu, hu'⟩
  have hūb : ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ avgDens u x ∧ avgDens u x ≤ C := ⟨cu, Cu, hcu, hū'⟩
  have hpb : ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ p x ∧ p x ≤ C := ⟨cp, Cp, hcp, hp'⟩
  have huC : ∀ x, u x ≤ Cu := fun x => (hu' x).2
  have hūC : ∀ x, avgDens u x ≤ Cu := fun x => (hū' x).2
  rw [permAvg_withDensity hum fun x => (hu0 x).le]
  -- smooth pieces
  have hūs : IsSmoothC (avgDens u) := isSmoothC_avgDens hus
  have hlogu : IsSmoothC (fun X => Real.log (u X)) := isSmoothC_log hus hu0
  have hlogū : IsSmoothC (fun X => Real.log (avgDens u X)) := isSmoothC_log hūs hū0
  obtain ⟨hlp, hlpG⟩ := isWeakGrad_logLip hcp (fun X => (hp' X).1) hL
  -- gradient fields
  set Du := gradC u with hDu
  set Dū := gradC (avgDens u) with hDū
  set Da := gradC (fun X => Real.log (u X)) with hDa
  set Dā := gradC (fun X => Real.log (avgDens u X)) with hDā
  set ℓ := lipField (fun X => Real.log (p X)) with hℓ
  have hDuG : Du.Good := gradC_good hus
  have hDūG : Dū.Good := gradC_good hūs
  have hDaG : Da.Good := gradC_good hlogu
  have hDāG : Dā.Good := gradC_good hlogū
  -- equivariance
  have hsymlogū : ∀ (σ : Equiv.Perm (Fin N)) X, Real.log (avgDens u (X ∘ σ)) = Real.log (avgDens u X) :=
    fun σ X => by rw [avgDens_symm]
  have hsymlogp : ∀ (σ : Equiv.Perm (Fin N)) X, Real.log (p (X ∘ σ)) = Real.log (p X) :=
    fun σ X => by rw [hps]
  have hāeq := fun σ => act_ae_eq_of_symm hsymlogū (isWeakGrad_gradC hlogū)
    (integrable_torus_of_smoothC hlogū) (integrable_torus_of_goodField hDāG) σ
  have hℓeq := fun σ => act_ae_eq_of_symm hsymlogp hlp
    (by
      have hcont : Continuous ((fun X => Real.log (p X)) ∘ unflat :
          UnitAddTorus (Fin N × Fin d) → ℝ) := by
        exact (hpc.log fun X => (hp X).ne').comp
          (continuous_pi fun i => continuous_pi fun k => continuous_apply (i, k))
      exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (integrable_torus_of_goodField hlpG) σ
  have hℓG : ℓ.Good := hlpG
  have hua : ∀ X q, u X * Da X q = Du X q := fun X q => gradC_log_mul hus hu0 X q
  have hūā : ∀ X q, avgDens u X * Dā X q = Dū X q := fun X q => gradC_log_mul hūs hū0 X q
  have hpy := pythagoras hum hu0 huC hDuG hDaG hDūG hDāG hℓG hua hūā (fun σ => hāeq σ)
    (fun σ => hℓeq σ) (gradC_avgDens_ae hus)
  -- the three Fisher formulas
  have hp1 : ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ p x ∧ p x ≤ C := hpb
  have g1 : IsWeakGrad (fun y => Real.log (u (unflat y) / p (unflat y)))
      (fun y q => (Da - ℓ) (unflat y) q) := by
    have := (isWeakGrad_gradC hlogu).add (hlp.cmul (-1))
    convert this using 1
    · funext y; simp only [Function.comp, Real.log_div (hu0 _).ne' (hp _).ne']; ring
    · funext y q; simp only [Pi.sub_apply]; ring
  have g2 : IsWeakGrad (fun y => Real.log (avgDens u (unflat y) / p (unflat y)))
      (fun y q => (Dā - ℓ) (unflat y) q) := by
    have := (isWeakGrad_gradC hlogū).add (hlp.cmul (-1))
    convert this using 1
    · funext y; simp only [Function.comp, Real.log_div (hū0 _).ne' (hp _).ne']; ring
    · funext y q; simp only [Pi.sub_apply]; ring
  have g3 : IsWeakGrad (fun y => Real.log (u (unflat y) / avgDens u (unflat y)))
      (fun y q => (Da - Dā) (unflat y) q) := by
    have := (isWeakGrad_gradC hlogu).add ((isWeakGrad_gradC hlogū).cmul (-1))
    convert this using 1
    · funext y; simp only [Function.comp, Real.log_div (hu0 _).ne' (hū0 _).ne']; ring
    · funext y q; simp only [Pi.sub_apply]; ring
  have bnd : ∀ {V : VF N d}, V.Good → ∃ Cg : ℝ, ∀ (y : UnitAddTorus (Fin N × Fin d)) q,
      |V (unflat y) q| ≤ Cg := fun {V} hV => by
    obtain ⟨-, C, hC⟩ := hV
    exact ⟨C, fun y q => hC _ _⟩
  have F1 : fisherInfoC ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (u X))
      ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (p X)) =
      ENNReal.ofReal (∫ X, u X * VF.dot (Da - ℓ) (Da - ℓ) X ∂(volume : Measure (Config N d))) :=
    (fisherInfoC_dens hum hpm hu1b hpb g1 (bnd (hDaG.sub hℓG))).trans
      (lintegral_mul_dot hum hu0 huC (hDaG.sub hℓG))
  have F2 : fisherInfoC ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (avgDens u X))
      ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (p X)) =
      ENNReal.ofReal (∫ X, avgDens u X * VF.dot (Dā - ℓ) (Dā - ℓ) X ∂(volume : Measure (Config N d))) :=
    (fisherInfoC_dens hūm hpm hūb hpb g2 (bnd (hDāG.sub hℓG))).trans
      (lintegral_mul_dot hūm hū0 hūC (hDāG.sub hℓG))
  have F3 : fisherInfoC ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (u X))
      ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (avgDens u X)) =
      ENNReal.ofReal (∫ X, u X * VF.dot (Da - Dā) (Da - Dā) X ∂(volume : Measure (Config N d))) :=
    (fisherInfoC_dens hum hūm hu1b hūb g3 (bnd (hDaG.sub hDāG))).trans
      (lintegral_mul_dot hum hu0 huC (hDaG.sub hDāG))
  rw [F1, F2, F3, hpy, ENNReal.ofReal_add]
  · exact integral_nonneg fun X => mul_nonneg (hū0 X).le (VF.dot_self_nonneg _ X)
  · exact integral_nonneg fun X => mul_nonneg (hu0 X).le (VF.dot_self_nonneg _ X)

end SharpLSI.FL
