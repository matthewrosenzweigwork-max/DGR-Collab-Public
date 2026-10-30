import DGPS.Examples.PolynomialSpeciesMinimizerScaledCritical

/-! Local origin exclusion for the ACTUAL smooth factor. The implicit-function
argument uses the nondegenerate origin amplitude Hessian and the exact zero
branch. No differentiated value-error estimate or optimizer classification is
assumed. Parameters are field, scaled rate, scaled tilt, in that order. -/
noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization
namespace DGPS.Examples.PolynomialSpecies

abbrev PolynomialAmplitudeParameters := ℝ × ℝ × ℝ
private abbrev Amp := ℝ × ℝ

private def amplitudeValue (ψ : PolynomialRangeParameters → E_STR02969)
    (q : PolynomialAmplitudeParameters × Amp) : ℝ :=
  polynomialScaledDeficitFactor ψ (q.1.1, (q.2.1, q.2.2, q.1.2.1, q.1.2.2))

def polynomialScaledAmplitudeGradient (ψ : PolynomialRangeParameters → E_STR02969)
    (q : PolynomialAmplitudeParameters × Amp) : Amp :=
  (fderiv ℝ (fun x : Amp => amplitudeValue ψ (q.1, x)) q.2 (1, 0),
   fderiv ℝ (fun x : Amp => amplitudeValue ψ (q.1, x)) q.2 (0, 1))

private def quarticGradient (α : ℝ) (x : Amp) : Amp :=
  (a0 * (x.1 / 6 + (3 * x.1 ^ 2 + x.2 ^ 2) / 12 + x.1 ^ 3 / 6 - α * x.1),
   a0 * (x.2 / 6 + x.1 * x.2 / 6 + x.2 ^ 3 / 6 - α * x.2))

private theorem quarticGradient_hasFDerivAt_zero (α : ℝ) :
    HasFDerivAt (quarticGradient α)
      ((a0 * (1 / 6 - α)) • ContinuousLinearMap.id ℝ Amp) 0 := by
  let LA : Amp →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let LB : Amp →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have ha : HasFDerivAt (fun x : Amp => x.1) LA 0 := hasFDerivAt_fst
  have hb : HasFDerivAt (fun x : Amp => x.2) LB 0 := hasFDerivAt_snd
  have h1 := ((((ha.const_mul (1 / 6)).add
    ((((ha.pow 2).const_mul 3).add (hb.pow 2)).const_mul (1 / 12))).add
      ((ha.pow 3).const_mul (1 / 6))).sub (ha.const_mul α)).const_mul a0
  have h2 := ((((hb.const_mul (1 / 6)).add ((ha.mul hb).const_mul (1 / 6))).add
    ((hb.pow 3).const_mul (1 / 6))).sub (hb.const_mul α))
  convert h1.prodMk (h2.const_mul a0) using 1
  · funext x
    apply Prod.ext <;> dsimp only [quarticGradient, Pi.add_apply, Pi.sub_apply, Pi.mul_apply] <;> ring
  · ext v <;> simp [LA, LB, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] <;> ring

private theorem amplitudeGradient_contDiffAt (ψ : PolynomialRangeParameters → E_STR02969)
    (q : PolynomialAmplitudeParameters × Amp)
    (hF : ContDiffAt ℝ ∞ (amplitudeValue ψ) q) :
    ContDiffAt ℝ ∞ (polynomialScaledAmplitudeGradient ψ) q := by
  let lift := fun t : (PolynomialAmplitudeParameters × Amp) × Amp => (t.1.1, t.2)
  have hlift : ContDiff ℝ ∞ lift := by dsimp only [lift]; fun_prop
  have huncurry : ContDiffAt ℝ ∞ (Function.uncurry
      (fun t : PolynomialAmplitudeParameters × Amp => fun x : Amp => amplitudeValue ψ (t.1, x))) (q, q.2) :=
    hF.comp (q, q.2) hlift.contDiffAt
  have hD : ContDiffAt ℝ ∞ (fun t : PolynomialAmplitudeParameters × Amp =>
      fderiv ℝ (fun x : Amp => amplitudeValue ψ (t.1, x)) t.2) q :=
    ContDiffAt.fderiv huncurry contDiffAt_snd (by simp)
  exact (hD.clm_apply contDiffAt_const).prodMk (hD.clm_apply contDiffAt_const)

/-- At every possible limiting rate below the coarse actual trial cutoff and
at every limiting tilt, small nonzero-field critical amplitudes cannot approach
the origin. This is a local statement, ready for compactness/subsequence use. -/
theorem polynomialScaledAmplitudeGradient_origin_exclusion
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (α₀ σ₀ : ℝ) (hα₀ : α₀ ≤ 5 / 48) :
    ∀ᶠ q : PolynomialAmplitudeParameters × Amp in 𝓝 ((0, α₀, σ₀), 0),
      q.1.1 ≠ 0 → polynomialScaledAmplitudeGradient ψ q = 0 → q.2 = 0 := by
  obtain ⟨O, hO, h0O, _hOU, hC, _hfactor, _hz, _hlim⟩ :=
    polynomialScaledDeficitFactor_identified hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
  let p₀ : PolynomialAmplitudeParameters := (0, α₀, σ₀)
  let q₀ : PolynomialAmplitudeParameters × Amp := (p₀, 0)
  let coord := fun q : PolynomialAmplitudeParameters × Amp =>
    (q.1.1, (q.2.1, q.2.2, q.1.2.1, q.1.2.2))
  have hc : ContDiff ℝ ∞ coord := by dsimp only [coord]; fun_prop
  have hFc : ContDiffAt ℝ ∞ (polynomialScaledDeficitFactor ψ) (coord q₀) :=
    hC.contDiffAt (hO.mem_nhds (h0O _))
  have hF : ContDiffAt ℝ ∞ (amplitudeValue ψ) q₀ := hFc.comp q₀ hc.contDiffAt
  have hS := amplitudeGradient_contDiffAt ψ q₀ hF
  have horigin : (fun x : Amp => polynomialScaledAmplitudeGradient ψ (p₀, x)) =
      quarticGradient α₀ := by
    funext x
    have he := polynomialFactorCriticalSystem_origin hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst σ₀ (x, α₀)
    have he' := congrArg Prod.fst he
    exact he'
  have hbase : polynomialScaledAmplitudeGradient ψ q₀ = 0 := by
    change polynomialScaledAmplitudeGradient ψ (p₀, 0) = 0
    rw [congrFun horigin]
    simp [quarticGradient]
  have hcomp := (hS.differentiableAt (by simp)).hasFDerivAt.comp (0 : Amp)
    ((hasFDerivAt_const p₀ (0 : Amp)).prodMk (hasFDerivAt_id (0 : Amp)))
  have hpartial : fderiv ℝ (polynomialScaledAmplitudeGradient ψ) q₀ ∘L
      ContinuousLinearMap.inr ℝ PolynomialAmplitudeParameters Amp =
      (a0 * (1 / 6 - α₀)) • ContinuousLinearMap.id ℝ Amp := by
    calc
      _ = fderiv ℝ (fun x : Amp => polynomialScaledAmplitudeGradient ψ (p₀, x)) 0 := hcomp.fderiv.symm
      _ = _ := by rw [horigin, (quarticGradient_hasFDerivAt_zero α₀).fderiv]
  have hcoef : 0 < a0 * (1 / 6 - α₀) := mul_pos a0_pos (by linarith)
  have hinj : Function.Injective ((a0 * (1 / 6 - α₀)) • ContinuousLinearMap.id ℝ Amp) := by
    intro x y he
    have hz : (a0 * (1 / 6 - α₀)) • (x - y) = 0 := by
      simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_sub, sub_eq_zero] using he
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hcoef.ne')
  have hinvertible : (fderiv ℝ (polynomialScaledAmplitudeGradient ψ) q₀ ∘L
      ContinuousLinearMap.inr ℝ PolynomialAmplitudeParameters Amp).IsInvertible := by
    rw [hpartial]
    have hsurj := LinearMap.injective_iff_surjective.mp hinj
    exact ⟨ContinuousLinearEquiv.ofBijective _
      (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj), rfl⟩
  let β := hS.implicitFunction (by simp) hinvertible
  have huniq : ∀ᶠ q in 𝓝 q₀, polynomialScaledAmplitudeGradient ψ q = 0 ↔ β q.1 = q.2 := by
    simpa only [hbase] using hS.eventually_apply_eq_iff_implicitFunction (by simp) hinvertible
  have hzmap : Continuous (fun q : PolynomialAmplitudeParameters × Amp => (q.1, (0 : Amp))) := by fun_prop
  have huniq0 : ∀ᶠ q in 𝓝 q₀,
      polynomialScaledAmplitudeGradient ψ (q.1, 0) = 0 ↔ β q.1 = 0 :=
    (hzmap.continuousAt (x := q₀)).tendsto.eventually huniq
  obtain ⟨V, hV, h0V, hzeroV⟩ := polynomialScaledDeficitFactor_amplitude_origin
    hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
  have hvmap : Continuous (fun q : PolynomialAmplitudeParameters × Amp =>
      (q.1.1, ((0 : ℝ), (0 : ℝ), q.1.2.1, q.1.2.2))) := by fun_prop
  have hmem : ∀ᶠ q in 𝓝 q₀, (q.1.1, ((0 : ℝ), (0 : ℝ), q.1.2.1, q.1.2.2)) ∈ V :=
    hvmap.continuousAt.tendsto.eventually (hV.mem_nhds (h0V (0, 0, α₀, σ₀)))
  filter_upwards [huniq, huniq0, hmem] with q hq hq0 hqV
  intro hh hcrit
  have hdz := (hzeroV q.1.1 q.1.2.1 q.1.2.2 hh hqV).2
  have hg0 : polynomialScaledAmplitudeGradient ψ (q.1, 0) = 0 := by
    change ((fderiv ℝ (fun x : Amp => polynomialScaledDeficitFactor ψ
      (q.1.1, (x.1, x.2, q.1.2.1, q.1.2.2))) 0 (1, 0)),
      (fderiv ℝ (fun x : Amp => polynomialScaledDeficitFactor ψ
      (q.1.1, (x.1, x.2, q.1.2.1, q.1.2.2))) 0 (0, 1))) = 0
    rw [hdz]
    rfl
  exact (hq.mp hcrit).symm.trans (hq0.mp hg0)

/-- Sequence form of actual origin exclusion, convenient after compact extraction. -/
theorem polynomialScaledAmplitudeGradient_no_origin_sequence
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (α₀ σ₀ : ℝ) (hα₀ : α₀ ≤ 5 / 48)
    (h α σ : ℕ → ℝ) (x : ℕ → ℝ × ℝ)
    (hh : Tendsto h atTop (𝓝 0)) (hα : Tendsto α atTop (𝓝 α₀))
    (hσ : Tendsto σ atTop (𝓝 σ₀)) (hx : Tendsto x atTop (𝓝 0))
    (hfield : ∀ n, h n ≠ 0) (hamp : ∀ n, x n ≠ 0)
    (hcrit : ∀ n, polynomialScaledAmplitudeGradient ψ ((h n, α n, σ n), x n) = 0) :
    False := by
  have hq : Tendsto (fun n => ((h n, α n, σ n), x n)) atTop (𝓝 ((0, α₀, σ₀), 0)) :=
    (hh.prodMk_nhds (hα.prodMk_nhds hσ)).prodMk_nhds hx
  have he := hq.eventually (polynomialScaledAmplitudeGradient_origin_exclusion
    hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst α₀ σ₀ hα₀)
  obtain ⟨n, hn⟩ := he.exists
  exact hamp n (hn (hfield n) (hcrit n))

end DGPS.Examples.PolynomialSpecies
