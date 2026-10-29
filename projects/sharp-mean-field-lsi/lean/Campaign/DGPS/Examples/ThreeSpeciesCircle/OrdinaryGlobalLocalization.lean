import DGPS.Examples.ThreeSpeciesCircle.OrdinaryBootstrap
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRangeEquation

/-!
# Ordinary optimizers: global localization (packet STR025b-iv)

For `h_j → 0` and global minimizers `ρ_j` of the ordinary quotient at `h_j`:

* `√ρ_j → 1` in `H¹` (from `ordinaryOptimizer_globalLocalization_H1`);
* for every `α ∈ (0,1)` (instance `HolderExponent α`), the log densities enter every
  neighbourhood of `0` in the chart `Par × Wsp α` of `OrdinaryRangeEquation` (STR026): there are
  chart points `x_j = ((a_j, b_j, h_j, 0), w_j)` with `x_j → 0` and
  `ρ_j = rho α x_j` almost everywhere (`rho` is the normalized exponential
  `exp(h cos 3t + u) / ∫ exp(h cos 3t + u)`, `u = a cos + b sin + w`).

Chart translation: with `f_j` the `C^{2,α}` log density of the bootstrap
(`ordinaryOptimizer_logDensity_C2alpha`), `u_j = f_j - h_j cos 3t - mean`, `a_j, b_j` are twice the
first Fourier coefficients of `u_j`, `w_j = u_j - (a_j cos + b_j sin)`; the parameter `γ` does not
enter the density and is set to `0`.
-/

open MeasureTheory Filter Topology Function
open DGPS DGPS.Analysis.PeriodicHolder

namespace DGPS.Examples.ThreeSpeciesCircle

section Chart
variable {α : ℝ} [HolderExponent α]

/-- The centred first-harmonic-free part of a log density: `F - h cos 3t` minus its mean. -/
noncomputable def oglU (F : PH α 2) (h : ℝ) : PH α 2 :=
  (F - h • PH.trig 2 3 1 0) - PH.integral 2 (F - h • PH.trig 2 3 1 0) • (1 : PH α 2)

/-- The chart coordinates of the log density `F` at the parameter `h`, with `γ = 0`. -/
noncomputable def oglChart (F : PH α 2) (h : ℝ) : Par × Wsp α :=
  (![2 * PH.cosCoeff 2 1 (oglU F h), 2 * PH.sinCoeff 2 1 (oglU F h), h, 0],
    ⟨oglU F h - PH.modeProj 2 {0, 1} (oglU F h), sub_modeProj01_mem _⟩)

theorem integral_one_two : PH.integral (α := α) 2 1 = 1 := by
  rw [PH.integral_apply]; simp

theorem integral_oglU (F : PH α 2) (h : ℝ) : PH.integral 2 (oglU F h) = 0 := by
  unfold oglU
  rw [map_sub, map_smul, integral_one_two]; simp

theorem continuous_oglU : Continuous (fun q : PH α 2 × ℝ => oglU q.1 q.2) := by
  unfold oglU
  have h1 : Continuous (fun q : PH α 2 × ℝ => q.1 - q.2 • PH.trig (α := α) 2 3 1 0) := by fun_prop
  exact h1.sub (((PH.integral 2).continuous.comp h1).smul continuous_const)

theorem continuous_oglChart : Continuous (fun q : PH α 2 × ℝ => oglChart q.1 q.2) := by
  have hu := continuous_oglU (α := α)
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_const.mul ((PH.cosCoeff 2 1).continuous.comp hu)
    · exact continuous_const.mul ((PH.sinCoeff 2 1).continuous.comp hu)
    · exact continuous_snd
    · exact continuous_const
  · exact Continuous.subtype_mk (hu.sub ((PH.modeProj 2 {0, 1}).continuous.comp hu)) _

theorem oglChart_zero : oglChart (0 : PH α 2) 0 = 0 := by
  unfold oglChart oglU
  refine Prod.ext ?_ ?_
  · funext i; fin_cases i <;> simp
  · apply Subtype.ext; simp

theorem uCLM_oglChart (F : PH α 2) (h : ℝ) : uCLM (oglChart F h) = oglU F h := by
  have hI := integral_oglU F h
  refine PH.ext (funext fun x => ?_)
  have := PH.modeProj01_val (oglU F h) x
  rw [hI, zero_add] at this
  simp only [uCLM, oglChart, add_apply, ContinuousLinearMap.smulRight_apply,
    pc_apply, PH.val_add, PH.val_smul, cosT, sinT, PH.val_trig, trigFun, Pi.add_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, Submodule.subtypeL_apply,
    ContinuousLinearMap.coe_snd', Pi.smul_apply, smul_eq_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_one, mul_one, zero_mul, add_zero]
  rw [PH.val_sub, Pi.sub_apply, this]
  ring

theorem phi_oglChart (F : PH α 2) (h : ℝ) (x : ℝ) :
    (phiCLM (oglChart F h)).val x =
      F.val x - PH.integral 2 (F - h • PH.trig (α := α) 2 3 1 0) := by
  have hu := uCLM_oglChart F h
  have : (phiCLM (oglChart F h)) = (h • cos3 : PH α 0) + incl2 (oglU F h) := by
    unfold phiCLM
    rw [add_apply, ContinuousLinearMap.smulRight_apply, u0CLM, ContinuousLinearMap.comp_apply, hu]
    simp [pc_apply, oglChart]
  rw [this]
  simp only [PH.val_add, PH.val_smul, Pi.add_apply, incl2_val, Pi.smul_apply, smul_eq_mul, oglU,
    cos3, PH.val_trig, trigFun, PH.val_sub, Pi.sub_apply, PH.val_one, Pi.one_apply]
  ring

theorem rho_oglChart (F : PH α 2) (h : ℝ) (s : ℝ) :
    (rho α (oglChart F h)).val s =
      (∫ x in (0:ℝ)..1, Real.exp (F.val x)) ⁻¹ * Real.exp (F.val s) := by
  set c := PH.integral 2 (F - h • PH.trig (α := α) 2 3 1 0) with hc
  have hexp : ∀ x, (PH.expMap 0 (phiCLM (oglChart F h))).val x = Real.exp (F.val x) * Real.exp (-c) := by
    intro x
    rw [PH.expMap_val, phi_oglChart, ← Real.exp_add]; congr 1
  unfold rho PH.normMap
  rw [PH.val_smul, Pi.smul_apply, smul_eq_mul, PH.integral_apply]
  simp only [hexp]
  rw [intervalIntegral.integral_mul_const, mul_inv]
  have : Real.exp (-c) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  
end Chart

section Mass

theorem ogl_mass_exp {f : ℝ → ℝ} (hc : Continuous f) (hp : Periodic f 1) (ρ : AbsoluteDensity 1)
    (hae : ∀ᵐ x ∂haar 1, ∀ s : ℝ, torusLift (fun _ => s) = x → ρ.density x = Real.exp (f s)) :
    ∫ s in (0:ℝ)..1, Real.exp (f s) = 1 := by
  have hper : Periodic (fun s => Real.exp (f s)) 1 := fun s => by simp [hp s]
  let F : UnitAddCircle → ℝ := hper.lift
  have hF : Continuous F := by
    have := (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1:ℝ))).continuous_iff (g := F)
    refine this.2 ?_
    have e : F ∘ (QuotientAddGroup.mk : ℝ → ℝ ⧸ AddSubgroup.zmultiples (1:ℝ)) = fun s => Real.exp (f s) := by
      funext s; exact hper.lift_coe s
    rw [e]; exact hc.rexp
  let G : Torus 1 → ℝ := fun x => F (x 0)
  have hG : Continuous G := hF.comp (continuous_apply 0)
  have hGp : ∀ s, G (pt s) = Real.exp (f s) := fun s => hper.lift_coe s
  have hae2 : (ρ.density) =ᵐ[haar 1] G := by
    filter_upwards [hae] with x hx
    obtain ⟨t, rfl⟩ := bs_exists_pt x
    rw [hx t rfl, hGp]
  have : ∫ x, ρ.density x ∂haar 1 = ∫ x, G x ∂haar 1 := integral_congr_ae hae2
  rw [ρ.integral_density, integral_haar_one G hG] at this
  simpa [hGp] using this.symm

end Mass

section Main

/-- **Global localization of the ordinary optimizers.**  (a) `√ρ_j → 1` in `H¹(m)`;
(b) for every Hölder exponent `α`, the optimizers' log densities, written in the chart of
`threefold_range_equation_invertible`, tend to `0` in `Par × Wsp α`, with `h`-coordinate `h_j`
and `γ`-coordinate `0`, and `ρ_j = rho α x_j` almost everywhere. -/
theorem ordinaryOptimizer_globalLocalization (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (ρ : ℕ → AbsoluteDensity 1)
    (hpos : ∀ j, 0 < ordinaryEntropy (h j) (ρ j))
    (hmin : ∀ j, ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy (h j) ρ' →
      ordinaryFisher (h j) (ρ j) / (2 * ordinaryEntropy (h j) (ρ j)) ≤
        ordinaryFisher (h j) ρ' / (2 * ordinaryEntropy (h j) ρ')) :
    (Tendsto (fun j => ∫ x, ((ρ j).sqrt x - 1) ^ 2 ∂haar 1) atTop (𝓝 0) ∧
      Tendsto (fun j => ∫ x, ‖weakGradient (ρ j).sqrt (ρ j).sqrt_mem x‖ ^ 2 ∂haar 1)
        atTop (𝓝 0)) ∧
    ∀ (α : ℝ) [HolderExponent α], ∃ x : ℕ → Par × Wsp α,
      Tendsto x atTop (𝓝 0) ∧ (∀ j, (x j).1 2 = h j ∧ (x j).1 3 = 0) ∧
      ∀ᶠ j in atTop, ∀ᵐ y ∂haar 1, ∀ s : ℝ, torusLift (fun _ => s) = y →
        (ρ j).density y = (rho α (x j)).val s := by
  refine ⟨ordinaryOptimizer_globalLocalization_H1 h hh ρ hpos hmin, ?_⟩
  intro α _
  obtain ⟨f, hf, hfn⟩ := ordinaryOptimizer_logDensity_C2alpha h hh ρ hpos hmin
    (HolderExponent.pos (α := α)) (HolderExponent.lt_one (α := α))
  classical
  let F : ℕ → PH α 2 := fun j => if hp : IsPH α 2 (f j) then PH.mk (f j) hp else 0
  have hFval : ∀ᶠ j in atTop, (F j).val = f j := by
    filter_upwards [hf] with j hj
    simp [F, hj.2.1]
  have hFt : Tendsto F atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine hfn.congr' ?_
    filter_upwards [hFval] with j hj
    rw [PH.norm_def, hj]
  have hxt : Tendsto (fun j => oglChart (F j) (h j)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => (F j, h j)) atTop (𝓝 ((0 : PH α 2), (0 : ℝ))) :=
      hFt.prodMk_nhds hh
    have := ((continuous_oglChart (α := α)).tendsto ((0 : PH α 2), (0 : ℝ))).comp h1
    rw [show oglChart (0 : PH α 2) 0 = 0 from oglChart_zero] at this
    exact this
  refine ⟨fun j => oglChart (F j) (h j), hxt, fun j => ⟨?_, ?_⟩, ?_⟩
  · simp [oglChart]
  · simp [oglChart]
  · filter_upwards [hFval, hf] with j hj hj2
    obtain ⟨hper, hph, hae⟩ := hj2
    have hmass := ogl_mass_exp hph.continuous hper (ρ j) hae
    filter_upwards [hae] with y hy s hs
    rw [hy s hs, rho_oglChart, hj, hmass]
    simp

end Main

end DGPS.Examples.ThreeSpeciesCircle
