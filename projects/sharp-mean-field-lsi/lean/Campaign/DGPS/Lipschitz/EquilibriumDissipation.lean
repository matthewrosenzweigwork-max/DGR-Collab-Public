import DGPS.Lipschitz.EquilibriumPotential
import DGPS.Lipschitz.WeightedGenerator
import DGPS.Model.ScalarRate

open MeasureTheory
open scoped ContDiff RealInnerProductSpace ENNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

section Helpers

theorem lip034_lipschitz_abs {f : Torus d → ℝ} {L : ℝ} (hf : TorusLipschitzWith L f) :
    TorusLipschitzWith |L| f := fun x y => by
  have h0 : 0 ≤ torusDist x y := Real.sqrt_nonneg _
  exact (hf x y).trans (mul_le_mul_of_nonneg_right (le_abs_self L) h0)

theorem lip034_lipschitz_const_add {f : Torus d → ℝ} {L : ℝ} (hf : TorusLipschitzWith L f)
    (κ : ℝ) : TorusLipschitzWith L fun x => κ + f x := fun x y => by
  simpa using hf x y

theorem lip034_isWeakGradient_of_top {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradientLp ∞ u g) : IsWeakGradient u g :=
  isWeakGradient_iff_isWeakGradientLp.mpr
    ⟨h.memLp.mono_exponent (by simp), h.memLp_grad.mono_exponent (by simp), h.ibp⟩

theorem lip034_isWeakGradientLp_one_of_top {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradientLp ∞ u g) : IsWeakGradientLp 1 u g :=
  ⟨h.memLp.mono_exponent le_top, h.memLp_grad.mono_exponent le_top, h.ibp⟩

theorem lip034_log_gibbsDensity (A : InteractionData d) (m : Measure (Torus d))
    [IsProbabilityMeasure m] (x : Torus d) :
    Real.log (gibbsDensity A m x) =
      -equilibriumPotential A m x - Real.log (gibbsPartition A m) := by
  have hZ := gibbsPartition_pos A m
  unfold gibbsDensity
  rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]

end Helpers

section Potential

variable {A : InteractionData d} {μ : ProbabilityMeasure (Torus d)}

/-- Along a perturbation `ν = (1 + h) μ` of an equilibrium, the interaction potential is
`Φ + T h` up to the constant `∫ h (W * μ) dμ`. -/
theorem lip034_interactionPotential_eq {h : C(Torus d, ℝ)} (hpos : ∀ x, 0 < 1 + h x)
    (h0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) (ρ : AbsoluteDensity d)
    (hρ : (densityMeasure ρ : Measure (Torus d)) =
      perturb (μ : Measure (Torus d)) (fun x => 1 + h x)) (x : Torus d) :
    interactionPotential A ρ x = equilibriumPotential A (μ : Measure (Torus d)) x +
      centeredOperatorC A (μ : Measure (Torus d)) h x +
        ∫ y, h y * interactionConvolution A (μ : Measure (Torus d)) y ∂(μ : Measure (Torus d)) := by
  set m : Measure (Torus d) := (μ : Measure (Torus d)) with hm
  have hu : Continuous fun y => 1 + h y := continuous_const.add h.continuous
  have hc := continuous_interactionConvolution A m
  have hcI : Integrable (fun y => interactionConvolution A m y) m :=
    integrable_of_continuous_torus hc m
  have hhI : Integrable (fun y => h y) m := integrable_of_continuous_torus h.continuous m
  have hhcI : Integrable (fun y => h y * interactionConvolution A m y) m :=
    integrable_of_continuous_torus (h.continuous.mul hc) m
  have hKx : Continuous fun y => centeredKernel A m x y :=
    (centeredKernel_continuous A m).comp (continuous_const.prodMk continuous_id)
  have hKI : Integrable (fun y => centeredKernel A m x y) m := integrable_of_continuous_torus hKx m
  have hKhI : Integrable (fun y => centeredKernel A m x y * h y) m :=
    integrable_of_continuous_torus (hKx.mul h.continuous) m
  have hE : ∫ y, interactionConvolution A m y ∂m = interactionEnergy A m := by
    rw [← interactionPairing_self, interactionPairing_eq_integral]
  have hW : ∀ y, A.W x y = centeredKernel A m x y + interactionConvolution A m x +
      interactionConvolution A m y - interactionEnergy A m := fun y => by
    unfold centeredKernel; ring
  have key : ∀ y, (1 + h y) * A.W x y =
      (centeredKernel A m x y + centeredKernel A m x y * h y) +
        ((interactionConvolution A m x - interactionEnergy A m) +
          (interactionConvolution A m x - interactionEnergy A m) * h y) +
        (interactionConvolution A m y + h y * interactionConvolution A m y) := fun y => by
    rw [hW y]; ring
  unfold interactionPotential
  rw [hρ, integral_perturb hu (fun y => (hpos y).le)]
  simp_rw [key]
  rw [lip034_T_apply (A := A) m h x]
  unfold Tfun equilibriumPotential
  have i1 : Integrable (fun y => centeredKernel A m x y + centeredKernel A m x y * h y) m :=
    hKI.add hKhI
  have i2 : Integrable (fun y => (interactionConvolution A m x - interactionEnergy A m) +
      (interactionConvolution A m x - interactionEnergy A m) * h y) m :=
    (integrable_const _).add (hhI.const_mul _)
  have i3 : Integrable (fun y => interactionConvolution A m y +
      h y * interactionConvolution A m y) m := hcI.add hhcI
  have i12 : Integrable (fun y => (centeredKernel A m x y + centeredKernel A m x y * h y) +
      (interactionConvolution A m x - interactionEnergy A m +
        (interactionConvolution A m x - interactionEnergy A m) * h y)) m := i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2, integral_add hKI hKhI,
    integral_add (integrable_const _) (hhI.const_mul _), integral_add hcI hhcI,
    integral_const_mul, integral_const, h0, hE, integral_centeredKernel_right]
  simp only [mul_zero, add_zero, probReal_univ, smul_eq_mul, zero_add]
  rw [mul_comm]
  ring

end Potential

section Core

variable {A : InteractionData d} {μ : ProbabilityMeasure (Torus d)}

/-- The core of S7: along an Euler solution `log (1 + h) + T h = c + ∑ bᵢ φᵢ`, the density
`q (1 + h)` is an absolute density whose dissipation is at most `(∑ |bᵢ| Lᵢ)²`. -/
theorem lip034_dissipation_core (hA : LipschitzData A) {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν)
    {Lφ : Fin k → ℝ} (hLφ : ∀ i, 0 ≤ Lφ i ∧ TorusLipschitzWith (Lφ i) fun x => φ i x)
    {h : C(Torus d, ℝ)} (hpos : ∀ x, 0 < 1 + h x)
    (h0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) (b : Par k) (c : ℝ)
    (heq : ∀ x, Real.log (1 + h x) + centeredOperatorC A (μ : Measure (Torus d)) h x =
      c + ∑ i, b i * φ i x) :
    ∃ ρ : AbsoluteDensity d, (densityMeasure ρ : Measure (Torus d)) =
        perturb (μ : Measure (Torus d)) (fun x => 1 + h x) ∧
      ∀ drift : AbsoluteDrift A,
        scalarDissipation A drift ρ ≤ ENNReal.ofReal ((∑ i, |b i| * Lφ i) ^ 2) := by
  set m : Measure (Torus d) := (μ : Measure (Torus d)) with hm
  obtain ⟨LΦ, hLΦ0, hΦ'⟩ := lipschitz_equilibriumPotential A hA
  have hΦ : TorusLipschitzWith LΦ (equilibriumPotential A m) := hΦ' m
  obtain ⟨LT, hT'⟩ := lip034_centeredOperatorC_lipschitz (μ := μ) hA h
  have hT : TorusLipschitzWith |LT| fun x => centeredOperatorC A m h x := lip034_lipschitz_abs hT'
  have hZ := gibbsPartition_pos A m
  obtain ⟨S, hSdef⟩ : ∃ S : Torus d → ℝ, ∀ x, S x = ∑ i, b i * φ i x := ⟨_, fun _ => rfl⟩
  have hS : TorusLipschitzWith (∑ i, |b i| * Lφ i) S := by
    rw [show S = fun x => ∑ i, b i * φ i x from funext hSdef]
    exact lip034_lipschitz_sum (fun i => lip034_lipschitz_smul (hLφ i).2 (b i))
  have hLc : 0 ≤ ∑ i, |b i| * Lφ i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hLφ i).1
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ∫ y, h y * interactionConvolution A m y ∂m := ⟨_, rfl⟩
  obtain ⟨Wf, hWfdef⟩ : ∃ Wf : Torus d → ℝ, ∀ x, Wf x = (c - Real.log (gibbsPartition A m)) +
      (S x + (-1 * equilibriumPotential A m x + -1 * centeredOperatorC A m h x)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨LW, hLW0, hWl⟩ : ∃ LW, 0 ≤ LW ∧ TorusLipschitzWith LW Wf := by
    have h1 := lip034_lipschitz_smul hΦ (-1)
    have h2 := lip034_lipschitz_smul hT (-1)
    have h3 := lip034_lipschitz_const_add (lip034_lipschitz_add hS (lip034_lipschitz_add h1 h2))
      (c - Real.log (gibbsPartition A m))
    rw [← show Wf = fun x => (c - Real.log (gibbsPartition A m)) +
      (S x + (-1 * equilibriumPotential A m x + -1 * centeredOperatorC A m h x))
      from funext hWfdef] at h3
    exact ⟨_, abs_nonneg _, lip034_lipschitz_abs h3⟩
  have hWc : Continuous Wf := torusLipschitz_continuous hWl
  obtain ⟨B, -, hB⟩ := exists_abs_bound hWc
  obtain ⟨u, hu⟩ : ∃ u : Torus d → ℝ, ∀ x, u x = 1 * Real.exp ((1 / 2) * Wf x) :=
    ⟨_, fun _ => rfl⟩
  have hucont : Continuous u := by
    rw [show u = fun x => 1 * Real.exp ((1 / 2) * Wf x) from funext hu]
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hWc))
  have hu0 : ∀ x, 0 < u x := fun x => by rw [hu]; positivity
  have hu2 : ∀ x, u x ^ 2 = Real.exp (Wf x) := fun x => by
    rw [hu, one_mul, sq, ← Real.exp_add]; congr 1; ring
  have hgu : IsWeakGradientLp ∞ u
      (fun x => ((1 : ℝ) * (1 / 2) * Real.exp ((1 / 2) * Wf x)) • smoothGrad Wf x) := by
    rw [show u = fun x => 1 * Real.exp ((1 / 2) * Wf x) from funext hu]
    exact WeightedGenerator.isWeakGradientLp_exp hLW0 hWl hB 1 (1 / 2)
  have hgu2 := lip034_isWeakGradient_of_top hgu
  -- the Gibbs density
  have hqc : Continuous (gibbsDensity A m) :=
    (Real.continuous_exp.comp (torusLipschitz_continuous hΦ).neg).div_const _
  have hq0 : ∀ x, 0 ≤ gibbsDensity A m x := fun x =>
    div_nonneg (Real.exp_pos _).le hZ.le
  have hexp : ∀ x, Real.exp (Wf x) = gibbsDensity A m x * (1 + h x) := fun x => by
    have h1 : 1 + h x = Real.exp (c + S x - centeredOperatorC A m h x) := by
      rw [← Real.exp_log (hpos x)]; congr 1
      linarith [heq x, hSdef x]
    have hq : gibbsDensity A m x =
        Real.exp (-equilibriumPotential A m x - Real.log (gibbsPartition A m)) := by
      rw [Real.exp_sub, Real.exp_log hZ]; rfl
    rw [hq, h1, ← Real.exp_add]; congr 1; rw [hWfdef]; ring
  have hgib := minimizer_eq_gibbs A μ hmin
  rw [gibbsMeasure_eq_withDensity] at hgib
  have hmeq : perturb (haar d) (gibbsDensity A m) = m := hgib.symm
  have hhI : Integrable (fun y => h y) m := integrable_of_continuous_torus h.continuous m
  have hmass : ∫ x, u x ^ 2 ∂haar d = 1 := by
    have e1 : ∀ x, u x ^ 2 = gibbsDensity A m x * (1 + h x) := fun x => by rw [hu2 x, hexp x]
    simp_rw [e1]
    rw [← integral_perturb (μ := haar d) hqc hq0 (fun x => 1 + h x), hmeq,
      integral_add (integrable_const _) hhI, h0]
    simp
  obtain ⟨ρ, hρs, hρm⟩ : ∃ ρ : AbsoluteDensity d, ρ.sqrt = u ∧
      weakGradient ρ.sqrt ρ.sqrt_mem =ᵐ[haar d]
        (fun x => ((1 : ℝ) * (1 / 2) * Real.exp ((1 / 2) * Wf x)) • smoothGrad Wf x) :=
    ⟨⟨u, ⟨_, hgu2⟩, Filter.Eventually.of_forall fun x => (hu0 x).le, hmass⟩, rfl,
      weakGradient_ae_eq hgu2⟩
  have hu1 : Continuous fun x => 1 + h x := continuous_const.add h.continuous
  have hρ : (densityMeasure ρ : Measure (Torus d)) = perturb m (fun x => 1 + h x) := by
    rw [densityMeasure_coe]
    have e : ∀ x, ENNReal.ofReal (ρ.sqrt x ^ 2) =
        ENNReal.ofReal (gibbsDensity A m x) * ENNReal.ofReal (1 + h x) := fun x => by
      rw [← ENNReal.ofReal_mul (hq0 x), hρs, hu2 x, hexp x]
    refine Eq.trans ?_ (congrArg (fun ν => perturb ν (fun x => 1 + h x)) hmeq)
    unfold perturb
    rw [← withDensity_mul _ (Measurable.ennreal_ofReal hqc.measurable)
      (Measurable.ennreal_ofReal hu1.measurable)]
    congr 1
    funext x
    exact e x
  have hPot : ∀ x, interactionPotential A ρ x =
      equilibriumPotential A m x + centeredOperatorC A m h x + s := fun x => by
    rw [lip034_interactionPotential_eq hpos h0 ρ hρ x, hs]
  have hPl : TorusLipschitzWith (abs (LΦ + |LT|)) (interactionPotential A ρ) := by
    have h3 := lip034_lipschitz_const_add (lip034_lipschitz_add hΦ hT) s
    rw [← show interactionPotential A ρ = fun x => s +
      (equilibriumPotential A m x + centeredOperatorC A m h x)
      from funext fun x => by rw [hPot x]; ring] at h3
    exact lip034_lipschitz_abs h3
  obtain ⟨hgP, -⟩ := exists_weak_gradient (abs_nonneg _) hPl
  obtain ⟨hgW, -⟩ := exists_weak_gradient hLW0 hWl
  have hSκ : TorusLipschitzWith (∑ i, |b i| * Lφ i)
      (fun x => (c - Real.log (gibbsPartition A m) + s) + S x) :=
    lip034_lipschitz_const_add hS _
  obtain ⟨hgS, hgSb⟩ := exists_weak_gradient hLc hSκ
  have hsum := isWeakGradientLp_add hgW hgP
  rw [show (fun x => Wf x + interactionPotential A ρ x) =
      fun x => (c - Real.log (gibbsPartition A m) + s) + S x from
    funext fun x => by rw [hWfdef, hPot]; ring] at hsum
  have hae := (lip034_isWeakGradient_of_top hsum).ae_eq (lip034_isWeakGradient_of_top hgS)
  refine ⟨ρ, hρ, fun drift => ?_⟩
  have hF : drift.force ρ =ᵐ[haar d] smoothGrad (interactionPotential A ρ) :=
    drift.ae_eq_of_isWeakGradient ρ (lip034_isWeakGradientLp_one_of_top hgP)
  have hfi : Integrable (fun x => u x ^ 2 * (∑ i, |b i| * Lφ i) ^ 2) (haar d) :=
    integrable_of_continuous_torus ((hucont.pow 2).mul continuous_const) (haar d)
  have hnn : 0 ≤ᵐ[haar d] fun x => u x ^ 2 * (∑ i, |b i| * Lφ i) ^ 2 :=
    Filter.Eventually.of_forall fun x => by positivity
  calc scalarDissipation A drift ρ
      ≤ ∫⁻ x, ENNReal.ofReal (u x ^ 2 * (∑ i, |b i| * Lφ i) ^ 2) ∂haar d := by
        unfold scalarDissipation
        refine lintegral_mono_ae ?_
        filter_upwards [hF, hρm, hae, hgSb] with x hx1 hx2 hx3 hx4
        apply ENNReal.ofReal_le_ofReal
        have hscore : scalarScore A drift ρ x =
            u x • smoothGrad (fun x => (c - Real.log (gibbsPartition A m) + s) + S x) x := by
          unfold scalarScore
          rw [hx1, hx2, ← hx3, hρs]
          rw [smul_add, smul_smul, hu x]
          congr 2
          ring
        rw [hscore, norm_smul, Real.norm_eq_abs, abs_of_pos (hu0 x)]
        calc (u x * ‖smoothGrad (fun x => (c - Real.log (gibbsPartition A m) + s) + S x) x‖) ^ 2
            ≤ (u x * ∑ i, |b i| * Lφ i) ^ 2 :=
              pow_le_pow_left₀ (mul_nonneg (hu0 x).le (norm_nonneg _))
                (mul_le_mul_of_nonneg_left hx4 (hu0 x).le) 2
          _ = u x ^ 2 * (∑ i, |b i| * Lφ i) ^ 2 := by ring
    _ = ENNReal.ofReal ((∑ i, |b i| * Lφ i) ^ 2) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hfi hnn, integral_mul_const, hmass, one_mul]

end Core

section Final

variable {A : InteractionData d} {μ : ProbabilityMeasure (Torus d)}

/-- The proof of S6 with the Euler data supplied explicitly, so that it can be combined with the
dissipation bound for the same graph. -/
theorem lip034_potential_gradient_of_euler {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ) {U : Set (Par k)} (hUo : IsOpen U)
    (y : Par k → Ysub A μ) (hsm : ContDiffOn ℝ ∞ y U)
    (hpos : ∀ a ∈ U, ∀ x, 0 < 1 + (phiMap φ a + (y a : C(Torus d, ℝ))) x)
    (b : Par k → Par k) (c : Par k → ℝ)
    (heq : ∀ a ∈ U, ∀ x, Real.log (1 + (phiMap φ a + (y a : C(Torus d, ℝ))) x) +
      centeredOperatorC A (μ : Measure (Torus d)) (phiMap φ a + (y a : C(Torus d, ℝ))) x =
      c a + ∑ i, b a i * φ i x) {a : Par k} (ha : a ∈ U) :
    HasGradientAt (fun a => lip034_potential (A := A) (μ : Measure (Torus d))
      (phiMap φ a + (y a : C(Torus d, ℝ)))) (b a) a := by
  set m : Measure (Torus d) := (μ : Measure (Torus d)) with hm
  have hd : DifferentiableAt ℝ y a :=
    (hsm.differentiableOn (by simp)).differentiableAt (hUo.mem_nhds ha)
  have hy := hd.hasFDerivAt
  have hsub : HasFDerivAt (fun a => ((y a : Ysub A μ) : C(Torus d, ℝ)))
      ((Ysub A μ).subtypeL.comp (fderiv ℝ y a)) a := by
    have h1 :=
      HasFDerivAt.comp (𝕜 := ℝ) (E := Par k) (F := Ysub A μ) (G := C(Torus d, ℝ))
        (g := (Ysub A μ).subtypeL) (f := y) (g' := (Ysub A μ).subtypeL)
        (f' := fderiv ℝ y a) a (Ysub A μ).subtypeL.hasFDerivAt hy
    simpa [Function.comp_def] using h1
  have hH : HasFDerivAt (fun a => phiMap φ a + ((y a : Ysub A μ) : C(Torus d, ℝ)))
      (phiMap φ + (Ysub A μ).subtypeL.comp (fderiv ℝ y a)) a :=
    (phiMap φ).hasFDerivAt.add hsub
  have hΨ := (lip034_hasFDerivAt_potential (A := A) m
    (f0 := phiMap φ a + ((y a : Ysub A μ) : C(Torus d, ℝ)))
    (fun x => hpos a ha x)).comp a hH
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hΨ.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  set u : Ysub A μ := fderiv ℝ y a v with hu
  have hg : (1 + nemLog (phiMap φ a + ((y a : Ysub A μ) : C(Torus d, ℝ))) +
      centeredOperatorC A m (phiMap φ a + ((y a : Ysub A μ) : C(Torus d, ℝ)))) =
      (1 + c a) • (1 : C(Torus d, ℝ)) + ∑ i, b a i • φ i := by
    ext x
    have := heq a ha x
    rw [← nemLog_apply (fun x => hpos a ha x)] at this
    simp only [ContinuousMap.add_apply, ContinuousMap.one_apply, ContinuousMap.smul_apply,
      ContinuousMap.sum_apply, smul_eq_mul, mul_one]
    linarith
  have hδ : ((phiMap φ + (Ysub A μ).subtypeL.comp (fderiv ℝ y a)) v) =
      phiMap φ v + (u : C(Torus d, ℝ)) := rfl
  simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply]
  rw [hg, hδ]
  have e : pairCLM m ((1 + c a) • (1 : C(Torus d, ℝ)) + ∑ i, b a i • φ i)
      (phiMap φ v + (u : C(Torus d, ℝ))) =
      (1 + c a) * intCLM m (phiMap φ v + (u : C(Torus d, ℝ))) +
        ∑ i, b a i * pairCLM m (φ i) (phiMap φ v + (u : C(Torus d, ℝ))) := by
    simp only [pairCLM_apply, intCLM_apply]
    generalize phiMap φ v + (u : C(Torus d, ℝ)) = δ
    have pt : ∀ x, ((1 + c a) • (1 : C(Torus d, ℝ)) + ∑ i, b a i • φ i) x * δ x =
        (1 + c a) * δ x + ∑ i, b a i * (φ i x * δ x) := fun x => by
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
        ContinuousMap.sum_apply, smul_eq_mul, mul_one]
      rw [add_mul, Finset.sum_mul]
      simp_rw [mul_assoc]
    simp_rw [pt]
    have iδ : Integrable (fun x => δ x) m := integrable_cts m δ
    have iφ : ∀ i, Integrable (fun x => b a i * (φ i x * δ x)) m := fun i =>
      (integrable_cts m (φ i * δ)).const_mul _
    rw [integral_add (iδ.const_mul _) (integrable_finsetSum _ fun i _ => iφ i),
      integral_const_mul, integral_finsetSum _ fun i _ => iφ i]
    simp_rw [integral_const_mul]
  rw [e, lip034_int_phi_add hφ u.2]
  rw [Finset.sum_congr rfl (fun i _ => by rw [lip034_pair_phi_add hφ u.2 v i])]
  simp [inner, mul_comm]

/-- `Ψ` is the free-energy gap of the density `ρ = q (1 + h)`. -/
theorem lip034_gap_eq_potential
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν)
    {h : C(Torus d, ℝ)} (hpos : ∀ x, 0 < 1 + h x)
    (h0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) (ρ : AbsoluteDensity d)
    (hρ : (densityMeasure ρ : Measure (Torus d)) =
      perturb (μ : Measure (Torus d)) (fun x => 1 + h x)) :
    ((scalarGap A ρ : NNReal) : ℝ) = lip034_potential (A := A) (μ : Measure (Torus d)) h := by
  set m : Measure (Torus d) := (μ : Measure (Torus d)) with hm
  have hgib := minimizer_eq_gibbs A μ hmin
  have hu : Continuous fun x => 1 + h x := continuous_const.add h.continuous
  have h1 : ∫ x, (1 + h x) ∂m = 1 := by
    rw [integral_add (integrable_const _) (integrable_of_continuous_torus h.continuous m), h0]
    simp
  obtain ⟨hk, -⟩ := klDiv_perturb (μ := m) hu hpos h1
  have hν : relativeEntropy (densityMeasure ρ : Measure (Torus d)) (haar d) ≠ ⊤ := by
    rw [Analysis.relativeEntropy_eq_klDiv,
      ← klDiv_gibbs_ne_top_iff A m (densityMeasure ρ : Measure (Torus d)), ← hgib, hρ]
    exact hk
  have hfe := free_energy_sub_eq A μ hgib (densityMeasure ρ) hν
  have hmin' : freeEnergy A μ = freeEnergyMinimum A :=
    le_antisymm (le_iInf hmin) (iInf_le (fun ν : ProbabilityMeasure (Torus d) => freeEnergy A ν) μ)
  rw [← coe_densityFreeEnergy, hmin', ← coe_freeEnergyMinimumReal,
    Analysis.relativeEntropy_eq_klDiv, hρ, ← EReal.coe_ennreal_toReal hk, ← EReal.coe_sub,
    ← EReal.coe_add, EReal.coe_eq_coe_iff] at hfe
  rw [coe_scalarGap, lip034_potential_eq_gap m (fun x => hpos x) h0]
  exact hfe

end Final

section Assemble

variable {A : InteractionData d} {μ : ProbabilityMeasure (Torus d)}

/-- **S7.** Along the Euler data of the graph, `D(q (1 + h a)) ≤ C_D ‖b a‖²` for every drift
provider, with `C_D = ∑ Lᵢ²` the squared Lipschitz constants of the basis. -/
theorem lip034_dissipation_bound (hA : LipschitzData A) {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ)
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν)
    {U : Set (Par k)} (h0U : (0 : Par k) ∈ U) (y : Par k → Ysub A μ)
    (hpos : ∀ a ∈ U, ∀ x, 0 < 1 + (phiMap φ a + (y a : C(Torus d, ℝ))) x)
    (b : Par k → Par k) (c : Par k → ℝ)
    (heq : ∀ a ∈ U, ∀ x, Real.log (1 + (phiMap φ a + (y a : C(Torus d, ℝ))) x) +
      centeredOperatorC A (μ : Measure (Torus d)) (phiMap φ a + (y a : C(Torus d, ℝ))) x =
      c a + ∑ i, b a i * φ i x) :
    ∃ C_D : ℝ, 0 ≤ C_D ∧ ∃ ρ : Par k → AbsoluteDensity d, ∀ a ∈ U,
      (densityMeasure (ρ a) : Measure (Torus d)) = perturb (μ : Measure (Torus d))
          (fun x => 1 + (phiMap φ a + (y a : C(Torus d, ℝ))) x) ∧
        ∀ drift : AbsoluteDrift A,
          scalarDissipation A drift (ρ a) ≤ ENNReal.ofReal (C_D * ‖b a‖ ^ 2) := by
  have hL : ∀ i, ∃ L, 0 ≤ L ∧ TorusLipschitzWith L fun x => φ i x := fun i => by
    obtain ⟨L, hL⟩ := lip034_phi_lipschitz hA hφ hmin i
    exact ⟨|L|, abs_nonneg _, lip034_lipschitz_abs hL⟩
  choose Lφ hLφ using hL
  have key : ∀ a, ∃ ρ : AbsoluteDensity d, a ∈ U →
      (densityMeasure ρ : Measure (Torus d)) = perturb (μ : Measure (Torus d))
          (fun x => 1 + (phiMap φ a + (y a : C(Torus d, ℝ))) x) ∧
        ∀ drift : AbsoluteDrift A,
          scalarDissipation A drift ρ ≤ ENNReal.ofReal ((∑ i, Lφ i ^ 2) * ‖b a‖ ^ 2) := by
    intro a
    by_cases ha : a ∈ U
    · have h0 : ∫ x, (phiMap φ a + (y a : C(Torus d, ℝ))) x ∂(μ : Measure (Torus d)) = 0 := by
        have := lip034_int_phi_add hφ (y a).2 a
        rwa [intCLM_apply] at this
      obtain ⟨ρ, hρ, hD⟩ := lip034_dissipation_core hA hmin (fun i => ⟨(hLφ i).1, (hLφ i).2⟩)
        (hpos a ha) h0 (b a) (c a) (heq a ha)
      refine ⟨ρ, fun _ => ⟨hρ, fun drift => (hD drift).trans ?_⟩⟩
      refine ENNReal.ofReal_le_ofReal ?_
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |b a i|) Lφ
      have hn : ‖b a‖ ^ 2 = ∑ i, |b a i| ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp only [Real.norm_eq_abs]
      rw [hn, mul_comm]
      exact hcs
    · obtain ⟨ρ0, -, -⟩ := lip034_dissipation_core hA hmin
        (fun i => ⟨(hLφ i).1, (hLφ i).2⟩) (h := phiMap φ 0 + (y 0 : C(Torus d, ℝ)))
        (hpos 0 h0U) (by
          have := lip034_int_phi_add hφ (y 0).2 0
          rwa [intCLM_apply] at this) (b 0) (c 0) (heq 0 h0U)
      exact ⟨ρ0, fun h => (ha h).elim⟩
  choose ρ hρ using key
  exact ⟨∑ i, Lφ i ^ 2, Finset.sum_nonneg fun i _ => sq_nonneg _, ρ, fun a ha => hρ a ha⟩

/-- **S8.** The Lyapunov–Schmidt graph for an equilibrium (LIP034): the implicit graph
`h(a) = ∑ aᵢ φᵢ + y(a)` of the projected Euler equation, with positivity, the Euler expression
`log (1 + h) + T h = c + ∑ bᵢ φᵢ`, the gradient `∇Ψ = b`, the identification of `Ψ` with the
free-energy gap `G(q (1 + h))`, and the dissipation bound `D ≤ C_D ‖b‖²`. -/
theorem lyapunov_schmidt_graph_for_equilibrium (hA : LipschitzData A) {k : ℕ}
    {φ : Fin k → C(Torus d, ℝ)} (hφ : IsEquilibriumBasis A μ φ)
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν) :
    ∃ U : Set (Par k), IsOpen U ∧ (0 : Par k) ∈ U ∧ ∃ y : Par k → Ysub A μ,
      y 0 = 0 ∧ fderiv ℝ y 0 = 0 ∧ ContDiffOn ℝ ∞ y U ∧
      (∀ a ∈ U, ∀ x, 0 < 1 + (phiMap φ a + (y a : C(Torus d, ℝ))) x) ∧
      ∃ (b : Par k → Par k) (c : Par k → ℝ),
        ContDiffOn ℝ ∞ b U ∧ ContDiffOn ℝ ∞ c U ∧ b 0 = 0 ∧ fderiv ℝ b 0 = 0 ∧
        (∀ a ∈ U, ∀ x, Real.log (1 + (phiMap φ a + (y a : C(Torus d, ℝ))) x) +
          centeredOperatorC A (μ : Measure (Torus d)) (phiMap φ a + (y a : C(Torus d, ℝ))) x =
          c a + ∑ i, b a i * φ i x) ∧
        (∀ a ∈ U, HasGradientAt
          (fun a => lip034_potential (A := A) (μ : Measure (Torus d))
            (phiMap φ a + (y a : C(Torus d, ℝ)))) (b a) a) ∧
        ∃ C_D : ℝ, 0 ≤ C_D ∧ ∃ ρ : Par k → AbsoluteDensity d, ∀ a ∈ U,
          (densityMeasure (ρ a) : Measure (Torus d)) = perturb (μ : Measure (Torus d))
              (fun x => 1 + (phiMap φ a + (y a : C(Torus d, ℝ))) x) ∧
          ((scalarGap A (ρ a) : NNReal) : ℝ) = lip034_potential (A := A) (μ : Measure (Torus d))
              (phiMap φ a + (y a : C(Torus d, ℝ))) ∧
          HasGradientAt (fun a => ((scalarGap A (ρ a) : NNReal) : ℝ)) (b a) a ∧
          ∀ drift : AbsoluteDrift A,
            scalarDissipation A drift (ρ a) ≤ ENNReal.ofReal (C_D * ‖b a‖ ^ 2) := by
  obtain ⟨U, hUo, h0U, y, hy0, hyd, hsm, -, hpos, b, c, hbsm, hcsm, hb0, hbd, heq⟩ :=
    lip034_euler_expansion hφ hmin
  obtain ⟨C_D, hC, ρ, hρ⟩ := lip034_dissipation_bound hA hφ hmin h0U y hpos b c heq
  have hgrad : ∀ a ∈ U, HasGradientAt
      (fun a => lip034_potential (A := A) (μ : Measure (Torus d))
        (phiMap φ a + (y a : C(Torus d, ℝ)))) (b a) a := fun a ha =>
    lip034_potential_gradient_of_euler hφ hUo y hsm hpos b c heq ha
  have hgap : ∀ a ∈ U, ((scalarGap A (ρ a) : NNReal) : ℝ) = lip034_potential (A := A)
      (μ : Measure (Torus d)) (phiMap φ a + (y a : C(Torus d, ℝ))) := fun a ha => by
    have h0 : ∫ x, (phiMap φ a + (y a : C(Torus d, ℝ))) x ∂(μ : Measure (Torus d)) = 0 := by
      have := lip034_int_phi_add hφ (y a).2 a
      rwa [intCLM_apply] at this
    exact lip034_gap_eq_potential hmin (hpos a ha) h0 (ρ a) (hρ a ha).1
  refine ⟨U, hUo, h0U, y, hy0, hyd, hsm, hpos, b, c, hbsm, hcsm, hb0, hbd, heq, hgrad, C_D, hC, ρ,
    fun a ha => ⟨(hρ a ha).1, hgap a ha, ?_, (hρ a ha).2⟩⟩
  refine (hgrad a ha).congr_of_eventuallyEq ?_
  filter_upwards [hUo.mem_nhds ha] with a' ha'
  exact hgap a' ha'

end Assemble

end DGPS.Lipschitz
