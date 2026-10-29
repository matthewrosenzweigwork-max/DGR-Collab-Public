import FullLabeledLSI.Examples.Paper.Sec9Prop97A

/-!
# Proposition 9.7, part B: profiles of periodic functions and the dilation `F(·) ↦ F(·/k)`

Lane C of the Section 9 formalization.  For a `C¹` 1-periodic `F` write `prof F = F ∘ secT`.  We compute
`Wd`, `Hf`, `mcos`, `msin` of `prof F` as integrals over `[0,1]` (`Wd_prof`, `Hf_prof`, `mcos_prof`,
`msin_prof`), prove the dilation identity `∫₀¹ φ(s/k) = ∫₀¹ φ` for `1/k`-periodic `φ`, and deduce that
the deficit of a `1/k`-periodic profile at frequency `k` and rate `r` is `k²` times the deficit of the
dilated profile at frequency `1` and rate `r/k²` (`Lam_scaling`).
-/

open MeasureTheory InformationTheory Filter Topology Set
open scoped ENNReal Real

namespace SharpLSI.FL.Ex.P97

open SharpLSI FL.Ex.Reg FL.Ex FL.Ex.SR FL.Ex.Def

/-- The profile `F ∘ secT` of a function on `ℝ`. -/
noncomputable def prof (F : ℝ → ℝ) : Torus 1 → ℝ := fun y => F (secT y 0)

theorem isWeakGrad_prof {F F1 : ℝ → ℝ} (hd : ∀ x, HasDerivAt F (F1 x) x) (hc1 : Continuous F1)
    (hp : Function.Periodic F 1) : IsWeakGrad (prof F) (fun y _ => F1 (secT y 0)) := by
  have hC1 : ContDiff ℝ 1 (prof F ∘ liftT) := by
    have e : prof F ∘ liftT = fun z : Fin 1 → ℝ => F (z 0) := comp_secT_lift hp
    rw [e]
    have hFC : ContDiff ℝ 1 F := by
      refine contDiff_one_iff_deriv.2 ⟨fun x => (hd x).differentiableAt, ?_⟩
      have : deriv F = F1 := funext fun x => (hd x).deriv
      rw [this]; exact hc1
    exact hFC.comp (contDiff_apply ℝ ℝ 0)
  have hw0 := isWeakGrad_of_contDiff hC1
  have hgrad : (fun (y : Torus 1) (k : Fin 1) => fderiv ℝ (prof F ∘ liftT) (secT y) (Pi.single k 1)) =
      fun y _ => F1 (secT y 0) := by
    funext y k
    have e : prof F ∘ liftT = fun z : Fin 1 → ℝ => F (z 0) := comp_secT_lift hp
    rw [e]
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    have hdiff : DifferentiableAt ℝ (fun z : Fin 1 → ℝ => F (z 0)) (secT y) :=
      ((hd (secT y 0)).differentiableAt).comp (secT y) (differentiableAt_apply 0 _)
    have h1 : HasDerivAt (fun t : ℝ => secT y 0 + t) 1 0 := (hasDerivAt_id 0).const_add _
    have h2 : HasDerivAt F (F1 (secT y 0)) (secT y 0 + 0) := by simpa using hd (secT y 0)
    have h3 := h2.comp (0 : ℝ) h1
    have hd' : HasDerivAt (fun t : ℝ => (fun z : Fin 1 → ℝ => F (z 0))
        (secT y + t • (Pi.single 0 1 : Fin 1 → ℝ))) (F1 (secT y 0)) 0 := by
      convert h3 using 1
      · funext t; simp
      · simp
    rw [fderiv_apply_of_line hdiff hd']
  rw [hgrad] at hw0
  exact hw0

theorem memH1_prof {F F1 : ℝ → ℝ} (hd : ∀ x, HasDerivAt F (F1 x) x) (hc1 : Continuous F1)
    (hp : Function.Periodic F 1) :
    MemH1 (haar 1) (prof F) ∧ (fun y => weakGrad (prof F) y 0) =ᵐ[haar 1] fun y => F1 (secT y 0) := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  exact memH1_of_isWeakGrad (isWeakGrad_prof hd hc1 hp) (BM.ofF hFc).memLp (BM.ofF hc1).memLp

theorem Wd_prof {F F1 : ℝ → ℝ} (hd : ∀ x, HasDerivAt F (F1 x) x) (hc1 : Continuous F1)
    (hp : Function.Periodic F 1) : Wd (prof F) = ∫ s in (0 : ℝ)..1, F1 s ^ 2 := by
  have hF1p := periodic_deriv_of_hasDerivAt hd hp
  obtain ⟨-, hae⟩ := memH1_prof hd hc1 hp
  unfold Wd
  have : ∫ y, weakGrad (prof F) y 0 ^ 2 ∂haar 1 = ∫ y : Torus 1, F1 (secT y 0) ^ 2 ∂haar 1 :=
    integral_congr_ae (hae.mono fun y hy => by simp only at hy ⊢; rw [hy])
  rw [this]
  exact integral_torus_eq (G := fun t => F1 t ^ 2) (hc1.pow 2) (fun t => by simp [hF1p t])

theorem Hf_prof {F : ℝ → ℝ} (hFc : Continuous F) (hp : Function.Periodic F 1)
    (hm : ∫ s in (0 : ℝ)..1, F s ^ 2 = 1) :
    Hf (prof F) = ∫ s in (0 : ℝ)..1, klFun (F s ^ 2) := by
  have h1 : ∫ y : Torus 1, prof F y ^ 2 ∂haar 1 = 1 := by
    refine Eq.trans ?_ hm
    exact integral_torus_eq (G := fun t => F t ^ 2) (hFc.pow 2) (fun t => by simp [hp t])
  unfold Hf
  rw [Cmp.klDiv_toReal_eq_integral (fun x => sq_nonneg _) h1]
  exact integral_torus_eq (G := fun t => klFun (F t ^ 2))
    (continuous_klFun.comp (hFc.pow 2)) (fun t => by simp [hp t])

theorem mcos_prof {F : ℝ → ℝ} (hFc : Continuous F) (hp : Function.Periodic F 1) (j : ℤ) :
    mcos j (fun y => prof F y ^ 2) = ∫ s in (0 : ℝ)..1, Real.cos (2 * π * j * s) * F s ^ 2 := by
  unfold mcos
  have hper : Function.Periodic (fun t : ℝ => Real.cos (2 * π * j * t) * F t ^ 2) 1 := by
    intro t
    have : 2 * π * j * (t + 1) = 2 * π * j * t + (j : ℝ) * (2 * π) := by ring
    simp only [this, Real.cos_add_int_mul_two_pi, hp t]
  exact integral_torus_eq (G := fun t => Real.cos (2 * π * j * t) * F t ^ 2)
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul (hFc.pow 2)) hper

theorem msin_prof {F : ℝ → ℝ} (hFc : Continuous F) (hp : Function.Periodic F 1) (j : ℤ) :
    msin j (fun y => prof F y ^ 2) = ∫ s in (0 : ℝ)..1, Real.sin (2 * π * j * s) * F s ^ 2 := by
  unfold msin
  have hper : Function.Periodic (fun t : ℝ => Real.sin (2 * π * j * t) * F t ^ 2) 1 := by
    intro t
    have : 2 * π * j * (t + 1) = 2 * π * j * t + (j : ℝ) * (2 * π) := by ring
    simp only [this, Real.sin_add_int_mul_two_pi, hp t]
  exact integral_torus_eq (G := fun t => Real.sin (2 * π * j * t) * F t ^ 2)
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul (hFc.pow 2)) hper

/-! ### Dilation -/

theorem integral_dilate {k : ℕ} (hk : 1 ≤ k) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hp : Function.Periodic φ (1 / (k : ℝ))) :
    ∫ s in (0 : ℝ)..1, φ (s / k) = ∫ s in (0 : ℝ)..1, φ s := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hk1 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [intervalIntegral.integral_comp_div (fun s => φ s) hk0]
  have h := hp.intervalIntegral_add_zsmul_eq (k : ℤ) 0 (fun a b => hc.intervalIntegrable _ _)
  simp only [zsmul_eq_mul, zero_add, Int.cast_natCast] at h
  have e : (k : ℝ) * (1 / (k : ℝ)) = 1 := by field_simp
  rw [e] at h
  simp only [zero_div, smul_eq_mul]
  rw [h]

theorem adm_prof {F F1 : ℝ → ℝ} (hd : ∀ x, HasDerivAt F (F1 x) x) (hc1 : Continuous F1)
    (hp : Function.Periodic F 1) (hnn : ∀ x, 0 ≤ F x) (hm : ∫ s in (0 : ℝ)..1, F s ^ 2 = 1) :
    Def.Adm (prof F) := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  refine ⟨fun y => hnn _, (memH1_prof hd hc1 hp).1, ?_⟩
  show ∫ y : Torus 1, F (secT y 0) ^ 2 ∂haar 1 = 1
  refine Eq.trans ?_ hm
  exact integral_torus_eq (G := fun t => F t ^ 2) (hFc.pow 2) (fun t => by simp [hp t])

theorem periodic_deriv_T {F : ℝ → ℝ} {T : ℝ} (hp : Function.Periodic F T) :
    Function.Periodic (deriv F) T := by
  intro x
  have h := deriv_comp_add_const F T x
  have e : (fun y => F (y + T)) = F := funext hp
  rw [e] at h
  exact h.symm

theorem Psi_scaling (k : ℕ) (hk : 1 ≤ k) (a r c1 s1 c2 s2 : ℝ) :
    Def.Psi k a r c1 s1 c2 s2 = (k : ℝ) ^ 2 * Def.Psi 1 a (r / (k : ℝ) ^ 2) c1 s1 c2 s2 := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  unfold Def.Psi Def.omg
  push_cast
  field_simp

/-- The dilated profile `G(s) = F(s/k)` of a `1/k`-periodic `C¹` function. -/
theorem scaling_data {k : ℕ} (hk : 1 ≤ k) {F F1 : ℝ → ℝ} (hd : ∀ x, HasDerivAt F (F1 x) x)
    (hc1 : Continuous F1) (hp : Function.Periodic F (1 / (k : ℝ))) :
    (∀ x, HasDerivAt (fun s => F (s / k)) (F1 (x / k) / k) x) ∧
      Continuous (fun s => F1 (s / k) / k) ∧ Function.Periodic (fun s => F (s / k)) 1 := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  refine ⟨fun x => ?_, ?_, ?_⟩
  · have h := (hd (x / k)).comp x ((hasDerivAt_id x).div_const (k : ℝ))
    simpa [Function.comp_def, div_eq_mul_inv] using h
  · exact (hc1.comp (continuous_id.div_const _)).div_const _
  · intro s
    have : (s + 1) / k = s / k + 1 / k := by ring
    simp only [this]
    exact hp (s / k)

theorem Lam_scaling {k : ℕ} (hk : 1 ≤ k) (a r : ℝ) {F F1 : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt F (F1 x) x) (hc1 : Continuous F1) (hp1 : Function.Periodic F 1)
    (hpk : Function.Periodic F (1 / (k : ℝ))) (hm : ∫ s in (0 : ℝ)..1, F s ^ 2 = 1) :
    Def.Lam k a r (Def.Pt k r (prof F)) =
      (k : ℝ) ^ 2 * Def.Lam 1 a (r / (k : ℝ) ^ 2)
        (Def.Pt 1 (r / (k : ℝ) ^ 2) (prof (fun s => F (s / k)))) := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  obtain ⟨hdG, hc1G, hpG⟩ := scaling_data hk hd hc1 hpk
  set G : ℝ → ℝ := fun s => F (s / k) with hG
  have hGc : Continuous G := hFc.comp (continuous_id.div_const _)
  have hF1T : Function.Periodic F1 (1 / (k : ℝ)) := by
    have : F1 = deriv F := funext fun x => (hd x).deriv.symm
    rw [this]; exact periodic_deriv_T hpk
  -- dilation facts
  have hmG : ∫ s in (0 : ℝ)..1, G s ^ 2 = 1 := by
    have := integral_dilate hk (φ := fun s => F s ^ 2) (hFc.pow 2) (fun t => by show F (t + 1 / (k : ℝ)) ^ 2 = F t ^ 2; rw [hpk t])
    simp only [hG]
    rw [this, hm]
  have hWd : Wd (prof G) = Wd (prof F) / (k : ℝ) ^ 2 := by
    rw [Wd_prof hdG hc1G hpG, Wd_prof hd hc1 hp1]
    have e : ∀ s, (F1 (s / k) / k) ^ 2 = (1 / (k : ℝ) ^ 2) * F1 (s / k) ^ 2 := fun s => by
      field_simp
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul,
      integral_dilate hk (φ := fun s => F1 s ^ 2) (hc1.pow 2) (fun t => by show F1 (t + 1 / (k : ℝ)) ^ 2 = F1 t ^ 2; rw [hF1T t])]
    ring
  have hHf : Hf (prof G) = Hf (prof F) := by
    rw [Hf_prof hGc hpG hmG, Hf_prof hFc hp1 hm]
    exact integral_dilate hk (φ := fun s => klFun (F s ^ 2))
      (continuous_klFun.comp (hFc.pow 2))
      (fun t => by show klFun (F (t + 1 / (k : ℝ)) ^ 2) = klFun (F t ^ 2); rw [hpk t])
  have hmv : mvecF 1 (prof G) = mvecF k (prof F) := by
    have hcos : ∀ j : ℤ, mcos (j * k) (fun y => prof F y ^ 2) = mcos j (fun y => prof G y ^ 2) := by
      intro j
      rw [mcos_prof hFc hp1, mcos_prof hGc hpG]
      have := integral_dilate hk
        (φ := fun s => Real.cos (2 * π * ((j * (k : ℤ) : ℤ) : ℝ) * s) * F s ^ 2)
        ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul (hFc.pow 2))
        (fun t => by
          show Real.cos (2 * π * ((j * (k : ℤ) : ℤ) : ℝ) * (t + 1 / k)) * F (t + 1 / k) ^ 2 =
            Real.cos (2 * π * ((j * (k : ℤ) : ℤ) : ℝ) * t) * F t ^ 2
          have h1 : 2 * π * ((j * (k : ℤ) : ℤ) : ℝ) * (t + 1 / k) =
              2 * π * ((j * (k : ℤ) : ℤ) : ℝ) * t + (j : ℝ) * (2 * π) := by
            push_cast; field_simp
          rw [h1, Real.cos_add_int_mul_two_pi, hpk t])
      simp only [hG]
      rw [← this]
      refine intervalIntegral.integral_congr fun s _ => ?_
      have h2 : 2 * π * ((j * (k : ℤ) : ℤ) : ℝ) * (s / k) = 2 * π * j * s := by
        push_cast; field_simp
      rw [h2]
    have hsin : ∀ j : ℤ, msin (j * k) (fun y => prof F y ^ 2) = msin j (fun y => prof G y ^ 2) := by
      intro j
      rw [msin_prof hFc hp1, msin_prof hGc hpG]
      have := integral_dilate hk
        (φ := fun s => Real.sin (2 * π * ((j * (k : ℤ) : ℤ) : ℝ) * s) * F s ^ 2)
        ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul (hFc.pow 2))
        (fun t => by
          show Real.sin (2 * π * ((j * (k : ℤ) : ℤ) : ℝ) * (t + 1 / k)) * F (t + 1 / k) ^ 2 =
            Real.sin (2 * π * ((j * (k : ℤ) : ℤ) : ℝ) * t) * F t ^ 2
          have h1 : 2 * π * ((j * (k : ℤ) : ℤ) : ℝ) * (t + 1 / k) =
              2 * π * ((j * (k : ℤ) : ℤ) : ℝ) * t + (j : ℝ) * (2 * π) := by
            push_cast; field_simp
          rw [h1, Real.sin_add_int_mul_two_pi, hpk t])
      simp only [hG]
      rw [← this]
      refine intervalIntegral.integral_congr fun s _ => ?_
      have h2 : 2 * π * ((j * (k : ℤ) : ℤ) : ℝ) * (s / k) = 2 * π * j * s := by
        push_cast; field_simp
      rw [h2]
    funext j
    fin_cases j
    · have := hcos 1
      simpa [mvecF] using this.symm
    · have := hsin 1
      simpa [mvecF] using this.symm
    · have := hcos 2
      simpa [mvecF, mul_comm] using this.symm
    · have := hsin 2
      simpa [mvecF, mul_comm] using this.symm
  unfold Def.Lam Def.Pt Def.Jf
  simp only
  rw [hmv, hWd, hHf]
  unfold Def.PsiV
  rw [Psi_scaling k hk a r]
  field_simp

end SharpLSI.FL.Ex.P97
