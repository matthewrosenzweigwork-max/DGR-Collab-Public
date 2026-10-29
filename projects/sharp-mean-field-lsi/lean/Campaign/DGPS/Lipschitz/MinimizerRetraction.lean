import DGPS.Lipschitz.MeanFieldDissipation
import DGPS.Model.ScalarRate
import DGPS.Analysis.WeakConvolution
import DGPS.Lipschitz.MeanFieldGlobalFlow

/-!
# Positive rate flow tails and the limiting minimizer (LIP031)

For `0 < r < r_*` (the DEF010 rate of the interaction data `A` with weak-drift provider `drift`),
the global probability flow `u` of a mean-field model has dissipation `D ≥ 2 r G` a.e., energy
identity, exponential decay of the gap, the tail bound `∫_t^∞ √D ≤ √(2 G(t)/r)`, and converges
weakly to a free-energy minimizer, uniformly in the initial gap (for `1`-Lipschitz tests).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace DGPS.Lipschitz

variable {d : ℕ}

private theorem abs_mul_log_le (x : ℝ) : |x * Real.log x| ≤ x ^ 2 + 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have ht : 0 < |x| := abs_pos.2 hx
  have h1 : |x * Real.log x| = |x| * |Real.log (|x|)| := by
    rw [abs_mul, Real.log_abs]
  rw [h1]
  rcases le_or_gt 1 |x| with h | h
  · have hl : 0 ≤ Real.log |x| := Real.log_nonneg h
    have hl2 : Real.log |x| ≤ |x| - 1 := Real.log_le_sub_one_of_pos ht
    rw [abs_of_nonneg hl, ← sq_abs x]
    nlinarith
  · have hl : Real.log |x| ≤ 0 := Real.log_nonpos ht.le h.le
    have hl2 : Real.log (|x|⁻¹) ≤ |x|⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.2 ht)
    rw [abs_of_nonpos hl]
    have : -Real.log |x| ≤ |x|⁻¹ - 1 := by rwa [Real.log_inv] at hl2
    have h4 : |x| * (-Real.log |x|) ≤ 1 - |x| := by
      calc |x| * (-Real.log |x|) ≤ |x| * (|x|⁻¹ - 1) := mul_le_mul_of_nonneg_left this ht.le
        _ = 1 - |x| := by field_simp
    nlinarith [sq_nonneg x]

private theorem integrable_mul_log_of_memLp {f : Torus d → ℝ} (hf : MemLp f 2 (haar d)) :
    Integrable (fun x => f x * Real.log (f x)) (haar d) := by
  refine Integrable.mono' (hf.integrable_sq.add (integrable_const (1 : ℝ)))
    (Real.continuous_mul_log.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_mul_log_le (f x)


private theorem isProb_withDensity {f : Torus d → ℝ} (hf : MemLp f 2 (haar d))
    (hnn : 0 ≤ᵐ[haar d] f) (hm : ∫ x, f x ∂haar d = 1) :
    IsProbabilityMeasure ((haar d).withDensity fun x => ENNReal.ofReal (f x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hf.integrable one_le_two) hnn, hm, ENNReal.ofReal_one]

/-- The probability measure `f m` of an `L²` probability density. -/
private noncomputable def fProb {f : Torus d → ℝ} (hf : MemLp f 2 (haar d))
    (hnn : 0 ≤ᵐ[haar d] f) (hm : ∫ x, f x ∂haar d = 1) : ProbabilityMeasure (Torus d) :=
  ⟨(haar d).withDensity fun x => ENNReal.ofReal (f x), isProb_withDensity hf hnn hm⟩

private theorem fProb_coe {f : Torus d → ℝ} (hf : MemLp f 2 (haar d))
    (hnn : 0 ≤ᵐ[haar d] f) (hm : ∫ x, f x ∂haar d = 1) :
    (fProb hf hnn hm : Measure (Torus d)) = (haar d).withDensity fun x => ENNReal.ofReal (f x) :=
  rfl

private theorem entropy_fProb {f : Torus d → ℝ} (hf : MemLp f 2 (haar d))
    (hnn : 0 ≤ᵐ[haar d] f) (hm : ∫ x, f x ∂haar d = 1) :
    0 ≤ ∫ x, f x * Real.log (f x) ∂haar d ∧
    relativeEntropy (fProb hf hnn hm : Measure (Torus d)) (haar d) =
      ENNReal.ofReal (∫ x, f x * Real.log (f x) ∂haar d) := by
  have hlog := integrable_mul_log_of_memLp hf
  have hint := hf.integrable one_le_two
  have hF : Integrable (fun x => f x * Real.log (f x) - f x + 1) (haar d) :=
    (hlog.sub hint).add (integrable_const 1)
  have hnn' : 0 ≤ᵐ[haar d] fun x => f x * Real.log (f x) - f x + 1 := by
    filter_upwards [hnn] with x hx
    exact self_mul_log_sub_add_one_nonneg hx
  have hE : ∫ x, (f x * Real.log (f x) - f x + 1) ∂haar d =
      ∫ x, f x * Real.log (f x) ∂haar d := by
    have h2 : Integrable (fun x => f x * Real.log (f x) - f x) (haar d) := hlog.sub hint
    rw [integral_add h2 (integrable_const (1 : ℝ)), integral_sub hlog hint, hm]
    simp
  have h0 : 0 ≤ ∫ x, f x * Real.log (f x) ∂haar d := by
    have := integral_nonneg_of_ae hnn'
    rwa [hE] at this
  refine ⟨h0, ?_⟩
  have h1 : relativeEntropy (fProb hf hnn hm : Measure (Torus d)) (haar d) =
      homogeneousEntropy (haar d) f :=
    relativeEntropy_withDensity hnn hint.aestronglyMeasurable.aemeasurable
  rw [h1, entropy_mass_one hm, ← ofReal_integral_eq_lintegral_ofReal hF hnn', hE]

/-- The bridge: the abstract free energy of `f m` is the Lipschitz-level free energy of `f`. -/
private theorem freeEnergy_fProb (A : InteractionData d) {f : Torus d → ℝ}
    (hf : MemLp f 2 (haar d)) (hnn : 0 ≤ᵐ[haar d] f) (hm : ∫ x, f x ∂haar d = 1) :
    DGPS.freeEnergy A (fProb hf hnn hm) =
      ((Lipschitz.freeEnergy A.V A.W f : ℝ) : EReal) := by
  obtain ⟨h0, hH⟩ := entropy_fProb hf hnn hm
  have hfm : AEMeasurable f (haar d) := hf.aestronglyMeasurable.aemeasurable
  have hP : potentialEnergy A (fProb hf hnn hm) = ∫ x, A.V x * f x ∂haar d := by
    unfold potentialEnergy
    rw [fProb_coe]
    change ∫ x, A.V x ∂(haar d).withDensity (ENNReal.ofReal ∘ f) = _
    rw [integral_withDensity_eq_integral_toReal_smul₀
      (ENNReal.measurable_ofReal.comp_aemeasurable hfm)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae ?_
    filter_upwards [hnn] with x hx
    simp [ENNReal.toReal_ofReal hx, mul_comm]
  have hI : interactionEnergy A (fProb hf hnn hm) = quadE A.W f := by
    unfold interactionEnergy quadE
    rw [fProb_coe]
    have h1 : AEMeasurable (fun x => ENNReal.ofReal (f x)) (haar d) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hfm
    rw [prod_withDensity₀ h1 h1]
    have h3 : AEMeasurable (fun z : Torus d × Torus d => ENNReal.ofReal (f z.1) *
        ENNReal.ofReal (f z.2)) ((haar d).prod (haar d)) :=
      (h1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
        (h1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    rw [integral_withDensity_eq_integral_toReal_smul₀ h3
      (Eventually.of_forall fun x =>
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
    refine integral_congr_ae ?_
    have h4 : ∀ᵐ z ∂(haar d).prod (haar d), 0 ≤ f z.1 :=
      Measure.quasiMeasurePreserving_fst.ae hnn
    have h5 : ∀ᵐ z ∂(haar d).prod (haar d), 0 ≤ f z.2 :=
      Measure.quasiMeasurePreserving_snd.ae hnn
    filter_upwards [h4, h5] with z hz1 hz2
    simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal hz1, ENNReal.toReal_ofReal hz2, mul_comm]
  unfold DGPS.freeEnergy
  rw [hH, hP, hI, EReal.coe_ennreal_ofReal, max_eq_left h0]
  unfold Lipschitz.freeEnergy
  rw [← EReal.coe_add, ← EReal.coe_add]


/-- The provider force of an absolute competitor is `G + B ∗ ρ` a.e. -/
private theorem force_ae_eq (A : InteractionData d) (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : MeanFieldData G B g β) (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ∞ (fun x => A.W x y) (fun x => B x y))
    (ρ : AbsoluteDensity d) :
    drift.force ρ =ᵐ[haar d] fun x => G x + ∫ y, ρ.density y • B x y ∂haar d := by
  have hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2 := hMF.measurable_B
  have hB : MemLp (fun p : Torus d × Torus d => B p.1 p.2) ∞ ((haar d).prod (haar d)) :=
    memLp_top_of_bound hBm.aestronglyMeasurable β
      (Eventually.of_forall fun p => hMF.norm_B_le _ _)
  have hc := isWeakGradientLp_convolution A.W_continuous hBm hB hWB ρ.integrable_density
  obtain ⟨C, hC⟩ := exists_bound_continuous A.V_continuous
  have hVinf : IsWeakGradientLp ∞ A.V G :=
    ⟨memLp_top_of_bound A.V_continuous.aestronglyMeasurable C
        (Eventually.of_forall fun x => by simpa using hC x),
      memLp_top_of_bound hMF.measurable_G.aestronglyMeasurable g
        (Eventually.of_forall hMF.norm_G_le), hV.ibp⟩
  have hs := isWeakGradientLp_add hVinf hc
  have hpot : interactionPotential A ρ = fun x => A.V x + ∫ y, A.W x y * ρ.density y ∂haar d := by
    funext x
    rw [interactionPotential_eq]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
  have h1 : IsWeakGradientLp 1 (interactionPotential A ρ)
      (fun x => G x + ∫ y, ρ.density y • B x y ∂haar d) := by
    rw [hpot]
    exact ⟨hs.memLp.mono_exponent le_top, hs.memLp_grad.mono_exponent le_top, hs.ibp⟩
  exact drift.ae_eq_of_isWeakGradient ρ h1

/-- Supplement to LIP030: for a.e. `r ∈ [0,T]`, every weak gradient `w` of `√u_r` makes the
square-root dissipation integrand integrable. -/
private theorem dissipation_integrable_supplement
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}
    (h : MeanFieldData G B g b) {ρ0 : L2s d} {u : ℝ → L2s d} (hu : IsGlobalProbFlow h ρ0 u)
    {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ}
    (hV : IsWeakGradient V G)
    (hWc : Continuous fun p : Torus d × Torus d => W p.1 p.2)
    (hsym : ∀ x y, W x y = W y x)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ∞ (fun x => W x y) (fun x => B x y))
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ w : Torus d → Tangent d,
      IsWeakGradient (fun x => Real.sqrt (u r x)) w →
      Integrable (fun x => ‖(2 : ℝ) • w x +
        Real.sqrt (u r x) • (G x + ∫ y, u r y • B x y ∂haar d)‖ ^ 2) (haar d) := by
  obtain ⟨A, K, hAm, hA2, hKm, hK2, hSet, hgrad, hKe, hid⟩ :=
    regularised_free_energy_identity h hu hV hWc hsym hWB hT
  have hD : DissData h u T A K :=
    { T_nonneg := hT
      cont := hu.cont.mono fun r hr => hr.1
      nonneg := fun r hr => hu.nonneg r hr.1
      mass := fun r hr => hu.mass r hr.1
      measA := hAm
      measK := hKm
      memA := hA2
      memK := hK2
      setting := hSet
      grad := hgrad
      Ke := hKe }
  have hVint : ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun x => V x * u t x) (haar d) := fun t _ => by
    have := (Lp.memLp (u t)).integrable_mul hV.memLp
    exact this.congr (Eventually.of_forall fun x => mul_comm _ _)
  have hfin : ∫⁻ r in Icc (0 : ℝ) T, Qdis u (fun p => A p + K p) r ≠ ⊤ := by
    obtain ⟨-, hQ⟩ := hD.lintegral_Q hVint hid le_rfl hT le_rfl
    rw [← setLIntegral_congr Ioc_ae_eq_Icc, hQ]
    exact ENNReal.ofReal_ne_top
  have hlt : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), Qdis u (fun p => A p + K p) r < ⊤ :=
    ae_lt_top' hD.aemeas_Q hfin
  filter_upwards [hD.slice, hlt] with r S hQ w hw
  obtain ⟨w0, hw0, hae⟩ := S.sqrt_H1 hQ.ne
  have hint := S.integrable_Q hQ.ne
  have h1 : Integrable (fun x => ‖(2 : ℝ) • w0 x +
      Real.sqrt (u r x) • (G x + Bc B (u r) x)‖ ^ 2) (haar d) :=
    hint.congr (hae.mono fun x hx => hx.symm)
  have hww : w =ᵐ[haar d] w0 := hw.ae_eq hw0
  refine h1.congr ?_
  filter_upwards [hww] with x hx
  rw [hx]
  rfl

open Classical in
/-- The square-root dissipation of the flow at time `t`, defined through a chosen weak gradient
of `√u_t` (`0` when `√u_t ∉ H¹`).  By a.e. uniqueness of weak gradients it does not depend on the
choice (`sqDiss_eq`). -/
private noncomputable def sqDiss (G : Torus d → Tangent d) (B : Torus d → Torus d → Tangent d)
    (u : ℝ → L2s d) (t : ℝ) : ℝ :=
  if hw : ∃ w : Torus d → Tangent d, IsWeakGradient (fun x => Real.sqrt (u t x)) w then
    ∫ x, ‖(2 : ℝ) • hw.choose x +
      Real.sqrt (u t x) • (G x + ∫ y, u t y • B x y ∂haar d)‖ ^ 2 ∂haar d
  else 0

private theorem sqDiss_eq {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d}
    {u : ℝ → L2s d} {t : ℝ} {w : Torus d → Tangent d}
    (hw : IsWeakGradient (fun x => Real.sqrt (u t x)) w) :
    sqDiss G B u t = ∫ x, ‖(2 : ℝ) • w x +
      Real.sqrt (u t x) • (G x + ∫ y, u t y • B x y ∂haar d)‖ ^ 2 ∂haar d := by
  have hex : ∃ w : Torus d → Tangent d, IsWeakGradient (fun x => Real.sqrt (u t x)) w := ⟨w, hw⟩
  unfold sqDiss
  simp only [hex, ↓reduceDIte]
  refine integral_congr_ae ?_
  filter_upwards [hex.choose_spec.ae_eq hw] with x hx
  rw [hx]

private theorem sqDiss_nonneg (G : Torus d → Tangent d) (B : Torus d → Torus d → Tangent d)
    (u : ℝ → L2s d) (t : ℝ) : 0 ≤ sqDiss G B u t := by
  unfold sqDiss
  split_ifs
  · exact integral_nonneg fun x => by positivity
  · exact le_rfl

/-- The global square-root dissipation of the flow: all of LIP030 on every `[0,T]`, glued, plus
a.e. integrability of the dissipation integrand. -/
private theorem global_dissipation
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}
    (h : MeanFieldData G B g b) {ρ0 : L2s d} {u : ℝ → L2s d} (hu : IsGlobalProbFlow h ρ0 u)
    {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ}
    (hV : IsWeakGradient V G)
    (hWc : Continuous fun p : Torus d × Torus d => W p.1 p.2)
    (hsym : ∀ x y, W x y = W y x)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ∞ (fun x => W x y) (fun x => B x y)) :
    (∀ T : ℝ, 0 ≤ T → IntegrableOn (sqDiss G B u) (Icc 0 T)) ∧
    (∀ s t : ℝ, 0 ≤ s → s ≤ t →
      Lipschitz.freeEnergy V W (u t) + ∫ r in s..t, sqDiss G B u r = Lipschitz.freeEnergy V W (u s)) ∧
    (∀ f : Torus d → ℝ, TorusLipschitzWith 1 f → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      |∫ x, u t x * f x ∂haar d - ∫ x, u s x * f x ∂haar d| ≤
        ∫ r in s..t, Real.sqrt (sqDiss G B u r)) ∧
    (∀ᵐ t ∂(volume : Measure ℝ), 0 < t → ∃ w : Torus d → Tangent d,
      IsWeakGradient (fun x => Real.sqrt (u t x)) w ∧
      Integrable (fun x => ‖(2 : ℝ) • w x +
        Real.sqrt (u t x) • (G x + ∫ y, u t y • B x y ∂haar d)‖ ^ 2) (haar d) ∧
      sqDiss G B u t = ∫ x, ‖(2 : ℝ) • w x +
        Real.sqrt (u t x) • (G x + ∫ y, u t y • B x y ∂haar d)‖ ^ 2 ∂haar d) := by
  have key : ∀ T : ℝ, 0 ≤ T → ∃ Dd : ℝ → ℝ,
      (∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), sqDiss G B u r = Dd r ∧
        ∃ w : Torus d → Tangent d, IsWeakGradient (fun x => Real.sqrt (u r x)) w) ∧
      Integrable Dd (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        Lipschitz.freeEnergy V W (u t) + ∫ r in s..t, Dd r = Lipschitz.freeEnergy V W (u s)) ∧
      (∀ f : Torus d → ℝ, TorusLipschitzWith 1 f → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        |∫ x, u t x * f x ∂haar d - ∫ x, u s x * f x ∂haar d| ≤
          ∫ r in s..t, Real.sqrt (Dd r)) := by
    intro T hT
    obtain ⟨Dd, h1, -, -, h4, h5, h6⟩ :=
      exact_free_energy_dissipation_identity_on_the_absolute_domain h hu hV hWc hsym hWB hT
    refine ⟨Dd, ?_, h4, h5, h6⟩
    filter_upwards [h1] with r ⟨w, hw, hDd⟩
    exact ⟨by rw [sqDiss_eq hw, hDd], w, hw⟩
  have hae : ∀ {T : ℝ} {P : ℝ → Prop},
      (∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), P r) → ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Icc (0 : ℝ) T → P r :=
    fun H => (ae_restrict_iff' measurableSet_Icc).1 H
  have hcongr : ∀ {T s t : ℝ} {Dd : ℝ → ℝ}, 0 ≤ s → s ≤ t → t ≤ T →
      (∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), sqDiss G B u r = Dd r) →
      ∀ φ : ℝ → ℝ, ∫ r in s..t, φ (sqDiss G B u r) = ∫ r in s..t, φ (Dd r) := by
    intro T s t Dd hs hst ht H φ
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae H] with r hr hrI
    rw [Set.uIoc_of_le hst] at hrI
    rw [hr ⟨hs.trans hrI.1.le, hrI.2.trans ht⟩]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨Dd, h1, h2, -⟩ := key T hT
    exact h2.congr (h1.mono fun r hr => hr.1.symm)
  · intro s t hs hst
    obtain ⟨Dd, h1, -, h3, -⟩ := key t (hs.trans hst)
    have := hcongr hs hst le_rfl (h1.mono fun r hr => hr.1) id
    simp only [id] at this
    rw [this]
    exact h3 s t hs hst le_rfl
  · intro f hf s t hs hst
    obtain ⟨Dd, h1, -, -, h4⟩ := key t (hs.trans hst)
    have := hcongr hs hst le_rfl (h1.mono fun r hr => hr.1) Real.sqrt
    rw [this]
    exact h4 f hf s t hs hst le_rfl
  · have hn : ∀ n : ℕ, ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Icc (0 : ℝ) n →
        ∃ w : Torus d → Tangent d, IsWeakGradient (fun x => Real.sqrt (u r x)) w := by
      intro n
      obtain ⟨Dd, h1, -⟩ := key n (Nat.cast_nonneg n)
      exact hae (h1.mono fun r hr => hr.2)
    have hn2 : ∀ n : ℕ, ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Icc (0 : ℝ) n →
        ∀ w : Torus d → Tangent d, IsWeakGradient (fun x => Real.sqrt (u r x)) w →
        Integrable (fun x => ‖(2 : ℝ) • w x +
          Real.sqrt (u r x) • (G x + ∫ y, u r y • B x y ∂haar d)‖ ^ 2) (haar d) := fun n =>
      hae (dissipation_integrable_supplement h hu hV hWc hsym hWB (Nat.cast_nonneg n))
    filter_upwards [ae_all_iff.2 hn, ae_all_iff.2 hn2] with r h1 h2 hr
    have hrn : r ∈ Icc (0 : ℝ) (⌈r⌉₊ : ℕ) := ⟨hr.le, Nat.le_ceil r⟩
    obtain ⟨w, hw⟩ := h1 ⌈r⌉₊ hrn
    exact ⟨w, hw, h2 ⌈r⌉₊ hrn w hw, sqDiss_eq hw⟩

/-- A flow slice with `√f ∈ H¹` and integrable dissipation integrand is an absolute density, with
the gap and dissipation of DEF010. -/
private theorem exists_absoluteDensity_of_slice (A : InteractionData d) (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : MeanFieldData G B g β) (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ∞ (fun x => A.W x y) (fun x => B x y))
    {f : L2s d} (hnn : 0 ≤ᵐ[haar d] ⇑f) (hm : ∫ x, f x ∂haar d = 1)
    {w : Torus d → Tangent d} (hw : IsWeakGradient (fun x => Real.sqrt (f x)) w)
    (hint : Integrable (fun x => ‖(2 : ℝ) • w x +
      Real.sqrt (f x) • (G x + ∫ y, f y • B x y ∂haar d)‖ ^ 2) (haar d)) :
    ∃ ρ : AbsoluteDensity d, ρ.density =ᵐ[haar d] ⇑f ∧
      ((scalarGap A ρ : ℝ≥0) : ℝ) = Lipschitz.freeEnergy A.V A.W f - freeEnergyMinimumReal A ∧
      scalarDissipation A drift ρ = ENNReal.ofReal (∫ x, ‖(2 : ℝ) • w x +
        Real.sqrt (f x) • (G x + ∫ y, f y • B x y ∂haar d)‖ ^ 2 ∂haar d) := by
  have hmass : ∫ x, Real.sqrt (f x) ^ 2 ∂haar d = 1 := by
    exact (integral_congr_ae (hnn.mono fun x hx => Real.sq_sqrt hx)).trans hm
  let ρ : AbsoluteDensity d :=
    ⟨fun x => Real.sqrt (f x), ⟨w, hw⟩, Eventually.of_forall fun x => Real.sqrt_nonneg _, hmass⟩
  have hdens : ρ.density =ᵐ[haar d] ⇑f := by
    filter_upwards [hnn] with x hx
    exact Real.sq_sqrt hx
  refine ⟨ρ, hdens, ?_, ?_⟩
  · have hmeas : densityMeasure ρ = fProb (Lp.memLp f) hnn hm := by
      apply Subtype.ext
      show (densityMeasure ρ : Measure (Torus d)) = (fProb (Lp.memLp f) hnn hm : Measure (Torus d))
      rw [densityMeasure_coe, fProb_coe]
      refine withDensity_congr_ae ?_
      filter_upwards [hdens] with x hx
      exact congrArg ENNReal.ofReal hx
    have h1 := coe_densityFreeEnergy A ρ
    rw [hmeas, freeEnergy_fProb A (Lp.memLp f) hnn hm] at h1
    have h2 : densityFreeEnergy A ρ = Lipschitz.freeEnergy A.V A.W f := EReal.coe_eq_coe_iff.1 h1
    rw [coe_scalarGap, h2]
  · have hsc : (scalarScore A drift ρ) =ᵐ[haar d] fun x => (2 : ℝ) • w x +
        Real.sqrt (f x) • (G x + ∫ y, f y • B x y ∂haar d) := by
      have h1 : weakGradient ρ.sqrt ρ.sqrt_mem =ᵐ[haar d] w :=
        (isWeakGradient_weakGradient ρ.sqrt_mem).ae_eq hw
      have h2 := force_ae_eq A drift hMF hV hWB ρ
      have h3 : ∀ x, ∫ y, ρ.density y • B x y ∂haar d = ∫ y, f y • B x y ∂haar d := fun x =>
        integral_congr_ae (hdens.mono fun y hy => congrArg (· • B x y) hy)
      filter_upwards [h1, h2] with x hx1 hx2
      show (2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • drift.force ρ x = _
      rw [hx1, hx2, h3 x]
    unfold scalarDissipation
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by positivity)]
    exact lintegral_congr_ae (hsc.mono fun x hx => congrArg (fun z => ENNReal.ofReal (‖z‖ ^ 2)) hx)


private theorem decay_aux {G : ℝ → ℝ} {r : ℝ}
    (hGc : Continuous G)
    (hsl : ∀ x z, 0 ≤ x → x ≤ z → G z - G x ≤ -(2 * r) * (z - x) * G z) :
    ∀ a b, 0 ≤ a → a ≤ b → G b ≤ Real.exp (-(2 * r * (b - a))) * G a := by
  intro a b ha hab
  set f : ℝ → ℝ := fun t => Real.exp (2 * r * t) * G t with hf
  have hfc : Continuous f :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hGc
  have key : ∀ x ∈ Ico a b, ∀ r' : ℝ, (0 : ℝ) < r' → ∃ᶠ z in 𝓝[>] x, slope f x z < r' := by
    intro x hx r' hr'
    have hx0 : 0 ≤ x := ha.trans hx.1
    have hexp : HasDerivAt (fun y => Real.exp (2 * r * y)) (Real.exp (2 * r * x) * (2 * r)) x := by
      have := ((hasDerivAt_id x).const_mul (2 * r)).exp
      simpa using this
    have hsx := (hasDerivAt_iff_tendsto_slope.mp hexp).mono_left
      (nhdsWithin_mono x (fun y hy => ne_of_gt hy))
    have hGz : Tendsto G (𝓝[>] x) (𝓝 (G x)) := (hGc.tendsto x).mono_left nhdsWithin_le_nhds
    have hEz : Tendsto (fun z => Real.exp (2 * r * z)) (𝓝[>] x) (𝓝 (Real.exp (2 * r * x))) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).tendsto x).mono_left
        nhdsWithin_le_nhds
    have hlim : Tendsto (fun z => -(2 * r) * (Real.exp (2 * r * z) * G z) +
        G x * slope (fun y => Real.exp (2 * r * y)) x z) (𝓝[>] x)
        (𝓝 (-(2 * r) * (Real.exp (2 * r * x) * G x) + G x * (Real.exp (2 * r * x) * (2 * r)))) :=
      (tendsto_const_nhds.mul (hEz.mul hGz)).add (tendsto_const_nhds.mul hsx)
    have h0 : -(2 * r) * (Real.exp (2 * r * x) * G x) +
        G x * (Real.exp (2 * r * x) * (2 * r)) = 0 := by ring
    rw [h0] at hlim
    have hev := hlim.eventually (gt_mem_nhds hr')
    have hev2 : ∀ᶠ z in 𝓝[>] x, x < z := self_mem_nhdsWithin
    refine ((hev.and hev2).mono fun z ⟨h1, h2⟩ => ?_).frequently
    have hpos : 0 < z - x := sub_pos.2 h2
    have e1 : slope f x z = Real.exp (2 * r * z) * ((G z - G x) / (z - x)) +
        G x * slope (fun y => Real.exp (2 * r * y)) x z := by
      simp only [slope_def_field, hf]
      field_simp
      ring
    have e2 : (G z - G x) / (z - x) ≤ -(2 * r) * G z := by
      rw [div_le_iff₀ hpos]
      nlinarith [hsl x z hx0 h2.le]
    have e3 := mul_le_mul_of_nonneg_left e2 (Real.exp_pos (2 * r * z)).le
    calc slope f x z ≤ -(2 * r) * (Real.exp (2 * r * z) * G z) +
          G x * slope (fun y => Real.exp (2 * r * y)) x z := by
          rw [e1]; nlinarith [e3]
      _ < r' := h1
  have hmain := image_le_of_liminf_slope_right_le_deriv_boundary (f := f) (a := a) (b := b)
    hfc.continuousOn (B := fun _ => f a) (B' := fun _ => 0) le_rfl continuousOn_const
    (fun x _ => hasDerivWithinAt_const x _ _) key (x := b) ⟨hab, le_rfl⟩
  have h1 : Real.exp (2 * r * b) * G b ≤ Real.exp (2 * r * a) * G a := hmain
  have h2 : Real.exp (-(2 * r * b)) * Real.exp (2 * r * b) = 1 := by
    rw [← Real.exp_add]; simp
  calc G b = Real.exp (-(2 * r * b)) * (Real.exp (2 * r * b) * G b) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ Real.exp (-(2 * r * b)) * (Real.exp (2 * r * a) * G a) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = Real.exp (-(2 * r * (b - a))) * G a := by
        rw [← mul_assoc, ← Real.exp_add]; congr 2; ring

private theorem tail_aux {G D : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hGanti : Antitone G) (hG0 : ∀ x, 0 ≤ G x) (hD0 : ∀ x, 0 ≤ D x)
    (hDi : LocallyIntegrable D volume)
    (hder : ∀ᵐ x ∂volume, HasDerivAt G (-(D x)) x)
    (hrate : ∀ᵐ x ∂volume, 0 < x → 2 * r * G x ≤ D x) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => Real.sqrt (D x)) volume a b ∧
      ∫ x in a..b, Real.sqrt (D x) ≤ Real.sqrt (2 * G a / r) := by
  set κ : ℝ := Real.sqrt (2 / r) with hκ
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  have hκ2 : κ ^ 2 = 2 / r := Real.sq_sqrt (by positivity)
  set f : ℝ → ℝ := fun x => -Real.sqrt (G x) with hf
  have hfmono : Monotone f := fun x y hxy =>
    neg_le_neg (Real.sqrt_le_sqrt (hGanti hxy))
  have hint := (hfmono.monotoneOn (uIcc a b)).intervalIntegrable_deriv
  have hmem := (hfmono.monotoneOn (uIcc a b)).intervalIntegral_deriv_mem_uIcc
  -- pointwise a.e. bound
  have hpt : ∀ᵐ x ∂volume, 0 < x → Real.sqrt (D x) ≤ κ * deriv f x := by
    filter_upwards [hder, hrate] with x hx1 hx2 hx0
    have hGx := hG0 x
    rcases hGx.eq_or_lt with hz | hpos
    · -- G x = 0: local minimum
      have hmin : IsLocalMin G x := Eventually.of_forall fun y => by rw [← hz]; exact hG0 y
      have hD : -(D x) = 0 := hmin.hasDerivAt_eq_zero hx1
      have hDx : D x = 0 := by linarith
      rw [hDx, Real.sqrt_zero]
      exact mul_nonneg hκ0 hfmono.deriv_nonneg
    · have hs : 0 < Real.sqrt (G x) := Real.sqrt_pos.2 hpos
      have hd := (hx1.sqrt hpos.ne')
      have hdf : HasDerivAt f (D x / (2 * Real.sqrt (G x))) x := by
        have := hd.neg
        convert this using 1
        ring
      rw [hdf.deriv]
      have hDpos : 0 ≤ D x := hD0 x
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      have hs2 : Real.sqrt (G x) ^ 2 = G x := Real.sq_sqrt hpos.le
      have : (κ * (D x / (2 * Real.sqrt (G x)))) ^ 2 = (2 / r) * (D x) ^ 2 / (4 * G x) := by
        rw [mul_pow, hκ2, div_pow, mul_pow, hs2]; ring
      rw [this, le_div_iff₀ (by positivity)]
      have h3 : 2 * r * G x ≤ D x := hx2 hx0
      have h4 : 2 / r * D x ^ 2 = 2 * D x ^ 2 / r := by ring
      rw [mul_comm (D x) (4 * G x), h4, le_div_iff₀ hr]
      nlinarith [mul_le_mul_of_nonneg_left h3 hDpos]
  have hpt' : ∀ᵐ x ∂(volume.restrict (Ioc a b)), Real.sqrt (D x) ≤ κ * deriv f x := by
    filter_upwards [ae_restrict_of_ae hpt, ae_restrict_mem measurableSet_Ioc] with x hx hxm
    exact hx (lt_of_le_of_lt ha hxm.1)
  have hDm : AEStronglyMeasurable D volume := hDi.aestronglyMeasurable
  have hsm : AEStronglyMeasurable (fun x => Real.sqrt (D x)) volume :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hDm
  have hint' : IntervalIntegrable (fun x => κ * deriv f x) volume a b := by
    exact hint.const_mul κ
  have hI : IntervalIntegrable (fun x => Real.sqrt (D x)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    have h2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hint'
    refine h2.mono' (hsm.restrict) ?_
    filter_upwards [hpt'] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hx
  refine ⟨hI, ?_⟩
  have hle : ∫ x in a..b, Real.sqrt (D x) ≤ ∫ x in a..b, κ * deriv f x := by
    refine intervalIntegral.integral_mono_ae_restrict hab hI hint' ?_
    rw [EventuallyLE, ← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact hpt'
  have hm2 : ∫ x in a..b, deriv f x ≤ f b - f a := by
    have hfab : f a ≤ f b := hfmono hab
    rw [uIcc_of_le (sub_nonneg.2 hfab)] at hmem
    exact hmem.2
  rw [intervalIntegral.integral_const_mul] at hle
  have h5 : f b - f a ≤ Real.sqrt (G a) := by
    simp only [hf]; have := Real.sqrt_nonneg (G b); linarith
  calc ∫ x in a..b, Real.sqrt (D x) ≤ κ * ∫ x in a..b, deriv f x := hle
    _ ≤ κ * Real.sqrt (G a) := mul_le_mul_of_nonneg_left (hm2.trans h5) hκ0
    _ = Real.sqrt (2 * G a / r) := by
        rw [hκ, ← Real.sqrt_mul (by positivity)]; congr 1; ring

private noncomputable def extZero (D : ℝ → ℝ) : ℝ → ℝ := (Ioi (0 : ℝ)).indicator D

private theorem extZero_nonneg {D : ℝ → ℝ} (hD0 : ∀ s, 0 ≤ D s) (s : ℝ) : 0 ≤ extZero D s := by
  unfold extZero; exact indicator_nonneg (fun s _ => hD0 s) s

private theorem locallyIntegrable_extZero {D : ℝ → ℝ} (hDi : ∀ T, 0 ≤ T → IntegrableOn D (Icc 0 T)) :
    LocallyIntegrable (extZero D) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨N, hN⟩ := hK.isBounded.subset_closedBall 0
  have hKN : K ⊆ Icc (-|N|) |N| := fun x hx => by
    have := hN hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact ⟨by linarith [neg_abs_le x, le_abs_self N], by linarith [le_abs_self x, le_abs_self N]⟩
  refine IntegrableOn.mono_set ?_ hKN
  unfold extZero
  rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioi]
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioi]
  refine (hDi |N| (abs_nonneg N)).mono_set ?_
  intro x hx
  exact ⟨hx.1.le, hx.2.2⟩


private theorem core_decay_tail {D Γ : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hD0 : ∀ s, 0 ≤ D s)
    (hDi : ∀ T, 0 ≤ T → IntegrableOn D (Icc 0 T))
    (hΓ : ∀ t, 0 ≤ t → Γ t = Γ 0 - ∫ s in (0 : ℝ)..t, D s) (hΓ0 : ∀ t, 0 ≤ t → 0 ≤ Γ t)
    (hrate : ∀ᵐ t ∂volume, 0 < t → 2 * r * Γ t ≤ D t) :
    (∀ a b, 0 ≤ a → a ≤ b → Γ b ≤ Real.exp (-(2 * r * (b - a))) * Γ a) ∧
    (∀ t, 0 ≤ t → IntegrableOn (fun s => Real.sqrt (D s)) (Ioi t) ∧
        ∫ s in Ioi t, Real.sqrt (D s) ≤ Real.sqrt (2 * Γ t / r)) := by
  obtain ⟨E, hEloc, hE0, hED⟩ : ∃ E : ℝ → ℝ, LocallyIntegrable E volume ∧ (∀ s, 0 ≤ E s) ∧
      ∀ s, 0 < s → E s = D s :=
    ⟨extZero D, locallyIntegrable_extZero hDi, extZero_nonneg hD0, fun s hs => by
      simp [extZero, indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs)]⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, ∀ x, G x = Γ 0 - ∫ s in (0 : ℝ)..x, E s := ⟨_, fun _ => rfl⟩
  have hGΓ : ∀ t, 0 ≤ t → G t = Γ t := by
    intro t ht
    rw [hGdef, hΓ t ht]
    congr 1
    rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le ht]
    exact setIntegral_congr_fun measurableSet_Ioc (fun s hs => hED s hs.1)
  have hEii : ∀ a b : ℝ, IntervalIntegrable E volume a b := fun a b => intervalIntegrable_iff.mpr
    ((LocallyIntegrable.integrableOn_isCompact hEloc isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hGc : Continuous G := by
    have : G = fun x => Γ 0 - ∫ s in (0 : ℝ)..x, E s := funext hGdef
    rw [this]
    exact continuous_const.sub (intervalIntegral.continuous_primitive hEii 0)
  have hGsub : ∀ x z, G z - G x = -∫ s in x..z, E s := by
    intro x z
    rw [hGdef, hGdef, ← intervalIntegral.integral_interval_sub_left (hEii 0 z) (hEii 0 x)]
    ring
  have hGanti : Antitone G := by
    intro x y hxy
    have h1 : 0 ≤ ∫ s in x..y, E s := intervalIntegral.integral_nonneg hxy (fun s _ => hE0 s)
    have := hGsub x y
    linarith
  have hG0 : ∀ x, 0 ≤ G x := by
    intro x
    rcases le_total 0 x with hx | hx
    · rw [hGΓ x hx]; exact hΓ0 x hx
    · have := hGanti hx
      rw [hGΓ 0 le_rfl] at this
      exact (hΓ0 0 le_rfl).trans this
  have hder : ∀ᵐ x ∂volume, HasDerivAt G (-(E x)) x := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hEloc] with x hx
    have : G = fun x => Γ 0 - ∫ s in (0 : ℝ)..x, E s := funext hGdef
    rw [this]
    exact (hx 0).const_sub (Γ 0)
  have hrate' : ∀ᵐ x ∂volume, 0 < x → 2 * r * G x ≤ E x := by
    filter_upwards [hrate] with x hx hx0
    rw [hGΓ x hx0.le, hED x hx0]
    exact hx hx0
  have hsl : ∀ x z, 0 ≤ x → x ≤ z → G z - G x ≤ -(2 * r) * (z - x) * G z := by
    intro x z hx hxz
    have hle : ∫ s in x..z, (2 * r * G z) ≤ ∫ s in x..z, E s := by
      refine intervalIntegral.integral_mono_ae_restrict hxz intervalIntegrable_const (hEii x z) ?_
      rw [EventuallyLE, ← Measure.restrict_congr_set Ioc_ae_eq_Icc]
      filter_upwards [ae_restrict_of_ae hrate', ae_restrict_mem measurableSet_Ioc] with s hs hsm
      have h1 := hs (lt_of_le_of_lt hx hsm.1)
      have h2 : G z ≤ G s := hGanti hsm.2
      nlinarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at hle
    rw [hGsub]
    nlinarith
  refine ⟨fun a b ha hab => ?_, fun t ht => ?_⟩
  · have := decay_aux hGc hsl a b ha hab
    rwa [hGΓ a ha, hGΓ b (ha.trans hab)] at this
  · have htail := fun T (hT : t ≤ T) => tail_aux hr hGanti hG0 hE0 hEloc hder hrate' ht hT
    set h : ℝ → ℝ := fun s => Real.sqrt (E s) with hh
    have hnorm : ∀ s, ‖h s‖ = h s := fun s => by
      simp only [hh, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hint : IntegrableOn h (Ioi t) := by
      refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
        (Real.sqrt (2 * G t / r)) t (b := fun T : ℝ => T) (l := atTop) (fun i => ?_)
        tendsto_id ?_
      · rcases le_total t i with hti | hit
        · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hti).1 (htail i hti).1
        · rw [Ioc_eq_empty (not_lt.2 hit)]; exact integrableOn_empty
      · filter_upwards [eventually_ge_atTop t] with i hi
        simp only [hnorm]
        exact (htail i hi).2
    have hlim := intervalIntegral_tendsto_integral_Ioi t hint (tendsto_id (α := ℝ) (x := atTop))
    have hbound : ∫ s in Ioi t, h s ≤ Real.sqrt (2 * G t / r) :=
      le_of_tendsto hlim (by
        filter_upwards [eventually_ge_atTop t] with i hi
        exact (htail i hi).2)
    have heq : EqOn h (fun s => Real.sqrt (D s)) (Ioi t) := fun s hs => by
      simp only [hh]; rw [hED s (lt_of_le_of_lt ht hs)]
    refine ⟨hint.congr_fun heq measurableSet_Ioi, ?_⟩
    rw [← setIntegral_congr_fun measurableSet_Ioi heq, ← hGΓ t ht]
    exact hbound


private theorem torusLip_continuous {f : Torus d → ℝ} (hf : TorusLipschitzWith 1 f) :
    Continuous f := by
  have : LipschitzWith ⟨Real.sqrt d, Real.sqrt_nonneg _⟩ f := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq]
    calc |f x - f y| ≤ 1 * torusDist x y := hf x y
      _ ≤ Real.sqrt d * dist x y := by rw [one_mul]; exact (torusDist_comparison x y).2
  exact this.continuous

private theorem exists_limit (ν : ℝ → ProbabilityMeasure (Torus d)) (ε : ℝ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hν : ∀ f : Torus d → ℝ, TorusLipschitzWith 1 f → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      |∫ x, f x ∂(ν t : Measure (Torus d)) - ∫ x, f x ∂(ν s : Measure (Torus d))| ≤ ε s) :
    ∃ R : ProbabilityMeasure (Torus d),
      (∀ f : Torus d → ℝ, TorusLipschitzWith 1 f → ∀ s : ℝ, 0 ≤ s →
        |∫ x, f x ∂(R : Measure (Torus d)) - ∫ x, f x ∂(ν s : Measure (Torus d))| ≤ ε s) ∧
      Tendsto ν atTop (𝓝 R) := by
  obtain ⟨R, hR⟩ := exists_clusterPt_of_compactSpace (Filter.map ν atTop)
  have key : ∀ f : Torus d → ℝ, TorusLipschitzWith 1 f → ∀ s : ℝ, 0 ≤ s →
      |∫ x, f x ∂(R : Measure (Torus d)) - ∫ x, f x ∂(ν s : Measure (Torus d))| ≤ ε s := by
    intro f hf s hs
    let fb : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨f, torusLip_continuous hf⟩
    have hcont : Continuous fun μ : ProbabilityMeasure (Torus d) =>
        |∫ x, f x ∂(μ : Measure (Torus d)) - ∫ x, f x ∂(ν s : Measure (Torus d))| :=
      ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction fb).sub
        continuous_const).abs
    have hC : IsClosed {μ : ProbabilityMeasure (Torus d) |
        |∫ x, f x ∂(μ : Measure (Torus d)) - ∫ x, f x ∂(ν s : Measure (Torus d))| ≤ ε s} :=
      isClosed_le hcont continuous_const
    have hmem : {μ : ProbabilityMeasure (Torus d) |
        |∫ x, f x ∂(μ : Measure (Torus d)) - ∫ x, f x ∂(ν s : Measure (Torus d))| ≤ ε s} ∈
        Filter.map ν atTop := by
      rw [Filter.mem_map]
      filter_upwards [eventually_ge_atTop s] with t ht
      exact hν f hf s t hs ht
    have := hR.mem_closure_of_mem _ hmem
    rwa [hC.closure_eq] at this
  refine ⟨R, key, ?_⟩
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro f - ⟨K, hK⟩
  set c : ℝ := (K : ℝ) + 1 with hc
  have hcpos : 0 < c := by positivity
  have hf' : TorusLipschitzWith 1 (fun x => f x / c) := by
    intro x y
    have h1 : dist (f x) (f y) ≤ K * dist x y := hK.dist_le_mul x y
    have h2 := (torusDist_comparison x y).1
    have h3 : 0 ≤ dist x y := dist_nonneg
    rw [← sub_div, abs_div, abs_of_pos hcpos, div_le_iff₀ hcpos, Real.dist_eq] at *
    have hK0 : (0 : ℝ) ≤ K := K.2
    nlinarith
  have hbound : ∀ s : ℝ, 0 ≤ s →
      |∫ x, f x ∂(R : Measure (Torus d)) - ∫ x, f x ∂(ν s : Measure (Torus d))| ≤ c * ε s := by
    intro s hs
    have := key _ hf' s hs
    rw [integral_div, integral_div, ← sub_div, abs_div, abs_of_pos hcpos, div_le_iff₀ hcpos] at this
    linarith
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ (by simpa using hε.const_mul c)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  rw [Real.dist_eq, abs_sub_comm]
  exact hbound s hs


private theorem freeEnergyMinimumReal_le_fProb (A : InteractionData d) {f : Torus d → ℝ}
    (hf : MemLp f 2 (haar d)) (hnn : 0 ≤ᵐ[haar d] f) (hm : ∫ x, f x ∂haar d = 1) :
    freeEnergyMinimumReal A ≤ Lipschitz.freeEnergy A.V A.W f := by
  have h : freeEnergyMinimum A ≤ DGPS.freeEnergy A (fProb hf hnn hm) :=
    iInf_le (fun ν : ProbabilityMeasure (Torus d) => DGPS.freeEnergy A ν) _
  rw [← coe_freeEnergyMinimumReal, freeEnergy_fProb] at h
  exact EReal.coe_le_coe_iff.mp h

private theorem integral_fProb {f : Torus d → ℝ} (hf : MemLp f 2 (haar d))
    (hnn : 0 ≤ᵐ[haar d] f) (hm : ∫ x, f x ∂haar d = 1) (h : Torus d → ℝ) :
    ∫ x, h x ∂(fProb hf hnn hm : Measure (Torus d)) = ∫ x, f x * h x ∂haar d := by
  have hfm : AEMeasurable f (haar d) := hf.aestronglyMeasurable.aemeasurable
  rw [fProb_coe]
  change ∫ x, h x ∂(haar d).withDensity (ENNReal.ofReal ∘ f) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (ENNReal.measurable_ofReal.comp_aemeasurable hfm)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hnn] with x hx
  simp [ENNReal.toReal_ofReal hx]

/-- The rate inequality `D ≥ 2 r G` on a flow slice, from `r < r_*`. -/
private theorem rate_ineq (A : InteractionData d) (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : MeanFieldData G B g β) (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ∞ (fun x => A.W x y) (fun x => B x y))
    {r : ℝ} (hr : 0 < r) (hrate : ENNReal.ofReal r < scalarRate A drift)
    {f : L2s d} (hnn : 0 ≤ᵐ[haar d] ⇑f) (hm : ∫ x, f x ∂haar d = 1)
    {w : Torus d → Tangent d} (hw : IsWeakGradient (fun x => Real.sqrt (f x)) w)
    (hint : Integrable (fun x => ‖(2 : ℝ) • w x +
      Real.sqrt (f x) • (G x + ∫ y, f y • B x y ∂haar d)‖ ^ 2) (haar d)) :
    2 * r * (Lipschitz.freeEnergy A.V A.W f - freeEnergyMinimumReal A) ≤
      ∫ x, ‖(2 : ℝ) • w x + Real.sqrt (f x) • (G x + ∫ y, f y • B x y ∂haar d)‖ ^ 2 ∂haar d := by
  obtain ⟨ρ, -, hgap, hD⟩ := exists_absoluteDensity_of_slice A drift hMF hV hWB hnn hm hw hint
  have hD0 : 0 ≤ ∫ x, ‖(2 : ℝ) • w x + Real.sqrt (f x) •
      (G x + ∫ y, f y • B x y ∂haar d)‖ ^ 2 ∂haar d := integral_nonneg fun x => by positivity
  rw [← hgap]
  rcases eq_zero_or_pos (scalarGap A ρ) with h0 | hpos
  · rw [h0]; simpa using hD0
  · have h1 := (hrate.trans_le (scalarRate_le_quotient A drift ρ hpos)).le
    unfold scalarQuotient at h1
    rw [hD] at h1
    have hne0 : (2 * (scalarGap A ρ : ℝ≥0∞)) ≠ 0 := by simpa using hpos.ne'
    have hnt : (2 * (scalarGap A ρ : ℝ≥0∞)) ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top
    have h2 := (ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl hnt)).1 h1
    have e : (2 * (scalarGap A ρ : ℝ≥0∞)) = ENNReal.ofReal (2 * ((scalarGap A ρ : ℝ≥0) : ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_coe_nnreal]; simp
    rw [e, ← ENNReal.ofReal_mul hr.le, ENNReal.ofReal_le_ofReal_iff hD0] at h2
    linarith

/-- The free-energy gap `F(u_t) - F_*` of a flow, on the real level. -/
noncomputable def flowGap (A : InteractionData d) (u : ℝ → L2s d) (t : ℝ) : ℝ :=
  Lipschitz.freeEnergy A.V A.W (u t) - freeEnergyMinimumReal A

/-- LIP031: positive-rate flow tails and the limiting minimizer.  Let `0 < r < r_*`.  For the
global flow `u` of the mean-field model (with `V + W * ρ` driven by the provider `drift`), the
square-root dissipation `D` is locally integrable, satisfies `D ≥ 2 r G` a.e. (with `G` and `D`
the DEF010 gap and dissipation of the slices), the energy identity, the exponential decay
`G(t) ≤ exp(-2r(t-s)) G(s)`, the tail bound `∫_t^∞ √D ≤ √(2 G(t)/r)`, and the flow converges weakly
to a free-energy minimizer `R`, with the explicit rate `√(2 G(t)/r) ≤ exp(-r t) √(2 G(0)/r)`
for `1`-Lipschitz test functions (hence uniformly over families with bounded initial gap). -/
theorem positive_rate_flow_tails_and_limiting_minimizer
    (A : InteractionData d) (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : MeanFieldData G B g β) (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ∞ (fun x => A.W x y) (fun x => B x y))
    {r : ℝ} (hr : 0 < r) (hrate : ENNReal.ofReal r < scalarRate A drift)
    {ρ0 : L2s d} {u : ℝ → L2s d} (hu : IsGlobalProbFlow hMF ρ0 u) :
    ∃ (D : ℝ → ℝ) (R : ProbabilityMeasure (Torus d)),
      (∀ t, 0 ≤ D t) ∧
      (∀ T : ℝ, 0 ≤ T → IntegrableOn D (Icc 0 T)) ∧
      (∀ᵐ t ∂(volume : Measure ℝ), 0 < t → ∃ ρ : AbsoluteDensity d,
        ρ.density =ᵐ[haar d] ⇑(u t) ∧ ((scalarGap A ρ : ℝ≥0) : ℝ) = flowGap A u t ∧
        scalarDissipation A drift ρ = ENNReal.ofReal (D t) ∧ 2 * r * flowGap A u t ≤ D t) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → flowGap A u t + ∫ x in s..t, D x = flowGap A u s) ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ flowGap A u t) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t →
        flowGap A u t ≤ Real.exp (-(2 * r * (t - s))) * flowGap A u s) ∧
      (∀ t : ℝ, 0 ≤ t → IntegrableOn (fun s => Real.sqrt (D s)) (Ioi t) ∧
        ∫ s in Ioi t, Real.sqrt (D s) ≤ Real.sqrt (2 * flowGap A u t / r)) ∧
      DGPS.freeEnergy A R = freeEnergyMinimum A ∧
      (∀ f : Torus d → ℝ, Continuous f →
        Tendsto (fun t : ℝ => ∫ x, u t x * f x ∂haar d) atTop
          (𝓝 (∫ x, f x ∂(R : Measure (Torus d))))) ∧
      (∀ f : Torus d → ℝ, TorusLipschitzWith 1 f → ∀ t : ℝ, 0 ≤ t →
        |∫ x, u t x * f x ∂haar d - ∫ x, f x ∂(R : Measure (Torus d))| ≤
          Real.sqrt (2 * flowGap A u t / r) ∧
        Real.sqrt (2 * flowGap A u t / r) ≤
          Real.exp (-(r * t)) * Real.sqrt (2 * flowGap A u 0 / r)) := by
  obtain ⟨hD1, hD2, hD3, hD4⟩ := global_dissipation hMF hu hV A.W_continuous A.W_symm hWB
  have hΓnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ flowGap A u t := fun t ht =>
    sub_nonneg.2 (freeEnergyMinimumReal_le_fProb A (Lp.memLp (u t)) (hu.nonneg t ht)
      (hu.mass t ht))
  have hrateAE : ∀ᵐ t ∂(volume : Measure ℝ), 0 < t → 2 * r * flowGap A u t ≤ sqDiss G B u t := by
    filter_upwards [hD4] with t ht ht0
    obtain ⟨w, hw, hint, hDeq⟩ := ht ht0
    rw [hDeq]
    exact rate_ineq A drift hMF hV hWB hr hrate (hu.nonneg t ht0.le) (hu.mass t ht0.le) hw hint
  have hen : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      flowGap A u t + ∫ x in s..t, sqDiss G B u x = flowGap A u s := by
    intro s t hs hst
    have := hD2 s t hs hst
    unfold flowGap
    linarith
  obtain ⟨hdecay, htail⟩ := core_decay_tail (D := sqDiss G B u) (Γ := flowGap A u) hr
    (sqDiss_nonneg G B u) hD1
    (fun t ht => by have := hen 0 t le_rfl ht; linarith) hΓnn hrateAE
  have hΓlim : Tendsto (flowGap A u) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 2 * r * t) atTop atTop :=
      tendsto_id.const_mul_atTop (by positivity)
    have hE : Tendsto (fun t : ℝ => Real.exp (-(2 * r * t)) * flowGap A u 0) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).mul_const (flowGap A u 0)
      simpa [Function.comp_def] using this
    refine squeeze_zero' ?_ ?_ hE
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hΓnn t ht
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      simpa using hdecay 0 t le_rfl ht
  have hεlim : Tendsto (fun s : ℝ => Real.sqrt (2 * flowGap A u s / r)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto (2 * 0 / r)).comp ((hΓlim.const_mul 2).div_const r)
    simpa [Function.comp_def] using this
  obtain ⟨ν, hν_int, hν_fe⟩ : ∃ ν : ℝ → ProbabilityMeasure (Torus d),
      (∀ (h : Torus d → ℝ) (t : ℝ), 0 ≤ t →
        ∫ x, h x ∂(ν t : Measure (Torus d)) = ∫ x, u t x * h x ∂haar d) ∧
      (∀ t : ℝ, 0 ≤ t → DGPS.freeEnergy A (ν t) =
        ((Lipschitz.freeEnergy A.V A.W (u t) : ℝ) : EReal)) := by
    refine ⟨fun t => fProb (Lp.memLp (u (max t 0))) (hu.nonneg _ (le_max_right _ _))
      (hu.mass _ (le_max_right _ _)), ?_, ?_⟩
    · intro h t ht
      exact (integral_fProb _ _ _ h).trans (by rw [max_eq_left ht])
    · intro t ht
      exact (freeEnergy_fProb A _ _ _).trans (by rw [max_eq_left ht])
  have hLip : ∀ f : Torus d → ℝ, TorusLipschitzWith 1 f → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      |∫ x, u t x * f x ∂haar d - ∫ x, u s x * f x ∂haar d| ≤
        Real.sqrt (2 * flowGap A u s / r) := by
    intro f hf s t hs hst
    refine (hD3 f hf s t hs hst).trans ?_
    have hI := htail s hs
    calc ∫ x in s..t, Real.sqrt (sqDiss G B u x)
        = ∫ x in Ioc s t, Real.sqrt (sqDiss G B u x) := intervalIntegral.integral_of_le hst
      _ ≤ ∫ x in Ioi s, Real.sqrt (sqDiss G B u x) :=
          setIntegral_mono_set hI.1 (Eventually.of_forall fun x => Real.sqrt_nonneg _)
            (Ioc_subset_Ioi_self.eventuallyLE)
      _ ≤ _ := hI.2
  obtain ⟨R, hR1, hR2⟩ := exists_limit ν (fun s => Real.sqrt (2 * flowGap A u s / r)) hεlim
    (fun f hf s t hs hst => by
      rw [hν_int f t (hs.trans hst), hν_int f s hs]
      exact hLip f hf s t hs hst)
  refine ⟨sqDiss G B u, R, sqDiss_nonneg G B u, hD1, ?_, hen, hΓnn, hdecay, htail, ?_, ?_, ?_⟩
  · filter_upwards [hD4, hrateAE] with t ht hrt ht0
    obtain ⟨w, hw, hint, hDeq⟩ := ht ht0
    obtain ⟨ρ, hρ1, hρ2, hρ3⟩ := exists_absoluteDensity_of_slice A drift hMF hV hWB
      (hu.nonneg t ht0.le) (hu.mass t ht0.le) hw hint
    exact ⟨ρ, hρ1, hρ2, by rw [hDeq]; exact hρ3, hrt ht0⟩
  · refine le_antisymm ?_ (iInf_le (fun μ : ProbabilityMeasure (Torus d) => DGPS.freeEnergy A μ) R)
    by_contra hcon
    rw [not_le, ← coe_freeEnergyMinimumReal] at hcon
    obtain ⟨z, hz1, hz2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    have hev1 : ∀ᶠ t in atTop, ((z : ℝ) : EReal) < DGPS.freeEnergy A (ν t) :=
      hR2.eventually (lowerSemicontinuous_freeEnergy A R _ hz2)
    have hz1' : freeEnergyMinimumReal A < z := EReal.coe_lt_coe_iff.1 hz1
    have hev2 : ∀ᶠ t in atTop, flowGap A u t < z - freeEnergyMinimumReal A :=
      hΓlim.eventually (gt_mem_nhds (sub_pos.2 hz1'))
    obtain ⟨t, h1, h2, h3⟩ := (hev1.and (hev2.and (eventually_ge_atTop (0 : ℝ)))).exists
    rw [hν_fe t h3] at h1
    have h1' := EReal.coe_lt_coe_iff.1 h1
    unfold flowGap at h2
    linarith
  · intro f hf
    have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hR2)
      (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩)
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hν_int f t ht
  · intro f hf t ht
    refine ⟨?_, ?_⟩
    · have := hR1 f hf t ht
      rw [hν_int f t ht] at this
      rwa [abs_sub_comm]
    · have hd := hdecay 0 t le_rfl ht
      have e : Real.exp (-(r * t)) ^ 2 = Real.exp (-(2 * r * (t - 0))) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      calc Real.sqrt (2 * flowGap A u t / r)
          ≤ Real.sqrt (Real.exp (-(r * t)) ^ 2 * (2 * flowGap A u 0 / r)) := by
            refine Real.sqrt_le_sqrt ?_
            rw [e]
            calc 2 * flowGap A u t / r ≤ 2 * (Real.exp (-(2 * r * (t - 0))) * flowGap A u 0) / r := by
                  gcongr
              _ = _ := by ring
        _ = Real.exp (-(r * t)) * Real.sqrt (2 * flowGap A u 0 / r) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]

end DGPS.Lipschitz
