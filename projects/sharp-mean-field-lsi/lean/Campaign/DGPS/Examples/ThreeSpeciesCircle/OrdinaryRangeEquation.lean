import DGPS.Examples.ThreeSpeciesCircle.Model
import DGPS.Analysis.ComplementaryElliptic
import DGPS.Analysis.ParameterImplicitFunction

/-!
# Ordinary optimizers on the three-species circle: the range equation

Lyapunov-Schmidt reduction of the threefold-symmetric ordinary-optimizer equation.
With the angular coordinate `t = 2 pi x` and `r = 1 + gamma`, the range part of the
Euler-Lagrange equation is `rangeMap = -2 Q[rho (E + kappa/2)]`, the Riesz gradient of the
constrained functional, in the parameters `p = (a, b, h, gamma)`.

* `threefold_range_equation_invertible`: `rangeMap` is real-analytic, vanishes at `0`, and its
  derivative in the range variable at `0` is `-2` times the (invertible) operator `d_t^2 + 1`
  on modes `|n| >= 2`; the implicit function theorem (`C^k` version, all `k`) gives the branch
  `w(a, b, h, gamma)`.
* `threefold_range_secondJet`: the weighted-degree-two jet of `w` and the remainder control
  (value, first and second derivatives in `(a, b, h)`, first derivative in `gamma`).
-/

open Function Filter Topology Asymptotics
open scoped ContDiff

namespace DGPS.Examples.ThreeSpeciesCircle
open DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic

section Maps

variable {α : ℝ} [HolderExponent α]

/-- Inclusion `C^{2,α} → C^{0,α}`. -/
noncomputable def incl2 : PH α 2 →L[ℝ] PH α 0 :=
  LinearMap.mkContinuous
    { toFun := fun u => PH.mk u.val (isPH_of_two u.isPH)
      map_add' := fun u v => PH.ext rfl
      map_smul' := fun c u => PH.ext rfl } 9 (fun u => by
      have hα0 := (HolderExponent.pos (α := α)).le
      have hα1 := (HolderExponent.lt_one (α := α)).le
      have h1 : IsPH α 1 u.val := IsPH.of_succ hα0 hα1 u.isPH
      have e1 : phNorm α 1 u.val ≤ 3 * phNorm α 2 u.val := phNorm_le_succ hα0 hα1 u.isPH
      have e2 : phNorm α 0 u.val ≤ 3 * phNorm α 1 u.val := phNorm_le_succ hα0 hα1 h1
      show phNorm α 0 u.val ≤ 9 * phNorm α 2 u.val
      linarith)

@[simp] theorem incl2_val (u : PH α 2) : (incl2 u).val = u.val := rfl

/-- The (x-)derivative `C^{2,α} → C^{0,α}`. -/
noncomputable def dx1 : PH α 2 →L[ℝ] PH α 0 :=
  LinearMap.mkContinuous
    { toFun := fun u => PH.mk (deriv u.val)
        (IsPH.of_succ (HolderExponent.pos (α := α)).le (HolderExponent.lt_one (α := α)).le u.isPH.2.2)
      map_add' := fun u v => PH.ext (deriv_add_fun u.isPH.2.1 v.isPH.2.1)
      map_smul' := fun c u => PH.ext (deriv_smul_fun c u.isPH.2.1) } 3 (fun u => by
      have hα0 := (HolderExponent.pos (α := α)).le
      have hα1 := (HolderExponent.lt_one (α := α)).le
      have e2 : phNorm α 0 (deriv u.val) ≤ 3 * phNorm α 1 (deriv u.val) :=
        phNorm_le_succ hα0 hα1 u.isPH.2.2
      have := supNorm_nonneg u.val
      show phNorm α 0 (deriv u.val) ≤ 3 * phNorm α 2 u.val
      have e3 : phNorm α 2 u.val = supNorm u.val + phNorm α 1 (deriv u.val) := rfl
      linarith)

@[simp] theorem dx1_val (u : PH α 2) : (dx1 u).val = deriv u.val := rfl

/-- The second x-derivative `C^{2,α} → C^{0,α}`. -/
noncomputable def dx2 : PH α 2 →L[ℝ] PH α 0 :=
  LinearMap.mkContinuous
    { toFun := fun u => PH.mk (deriv (deriv u.val)) (isPH_deriv_deriv u.isPH)
      map_add' := fun u v => by
        refine PH.ext ?_
        show deriv (deriv (u.val + v.val)) = _
        rw [deriv_add_fun u.isPH.2.1 v.isPH.2.1, deriv_add_fun u.isPH.2.2.2.1 v.isPH.2.2.2.1]
        rfl
      map_smul' := fun c u => by
        refine PH.ext ?_
        show deriv (deriv (c • u.val)) = _
        rw [deriv_smul_fun c u.isPH.2.1, deriv_smul_fun c u.isPH.2.2.2.1]
        rfl } 1 (fun u => by
      have := supNorm_nonneg u.val
      have := supNorm_nonneg (deriv u.val)
      show phNorm α 0 (deriv (deriv u.val)) ≤ 1 * phNorm α 2 u.val
      simp only [phNorm]; linarith)

@[simp] theorem dx2_val (u : PH α 2) : (dx2 u).val = deriv (deriv u.val) := rfl

/-- Multiplication in `C^{0,α}` as a bounded bilinear map. -/
noncomputable def mulCLM : PH α 0 →L[ℝ] PH α 0 →L[ℝ] PH α 0 :=
  LinearMap.mkContinuous₂ (LinearMap.mul ℝ (PH α 0)) (PH.scale α 0)
    (fun f g => by simpa [mul_assoc] using PH.norm_mul_le_scale α 0 f g)

@[simp] theorem mulCLM_apply (f g : PH α 0) : mulCLM f g = f * g := rfl

theorem ell_eq (u : PH α 2) : ell u = (kappa⁻¹ : ℝ) • dx2 u + incl2 u := rfl


/-- Parameters `(a, b, h, γ)`. -/
abbrev Par : Type := Fin 4 → ℝ

/-- Chart space `C^{2,α}` functions orthogonal to `1, cos, sin`. -/
abbrev Wsp (α : ℝ) [HolderExponent α] : Type := PH.orthSub α 2

noncomputable def cosT : PH α 2 := PH.trig 2 1 1 0
noncomputable def sinT : PH α 2 := PH.trig 2 1 0 1
noncomputable def cos3 : PH α 0 := PH.trig 0 3 1 0
noncomputable def sin3 : PH α 0 := PH.trig 0 3 0 1

theorem sub_modeProj01_mem {k : ℕ} (f : PH α k) : f - PH.modeProj k {0, 1} f ∈ PH.orthSub α k := by
  obtain ⟨a, b, c⟩ := PH.modeProj01_orth f
  refine ⟨?_, ?_, ?_⟩
  · rw [map_sub, a, sub_self]
  · rw [map_sub, b, sub_self]
  · rw [map_sub, c, sub_self]

/-- The projection removing the modes `0` and `1`. -/
noncomputable def Qproj : PH α 0 →L[ℝ] PH.orthSub α 0 :=
  (ContinuousLinearMap.id ℝ (PH α 0) - PH.modeProj 0 {0, 1}).codRestrict (PH.orthSub α 0)
    (fun f => sub_modeProj01_mem f)

theorem Qproj_val (f : PH α 0) : ((Qproj f : PH.orthSub α 0) : PH α 0) = f - PH.modeProj 0 {0, 1} f := rfl

/-- Coordinate functional of the parameter. -/
noncomputable def pc (i : Fin 4) : Par × Wsp α →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i).comp
    (ContinuousLinearMap.fst ℝ Par (Wsp α))

/-- `u = a cos + b sin + w`. -/
noncomputable def uCLM : Par × Wsp α →L[ℝ] PH α 2 :=
  (pc 0).smulRight cosT + (pc 1).smulRight sinT +
    (PH.orthSub α 2).subtypeL.comp (ContinuousLinearMap.snd ℝ Par (Wsp α))

noncomputable def u0CLM : Par × Wsp α →L[ℝ] PH α 0 := incl2.comp uCLM

/-- `Du = u_t = (2π)⁻¹ ∂ₓ u`. -/
noncomputable def DuCLM : Par × Wsp α →L[ℝ] PH α 0 := ((2 * Real.pi)⁻¹ : ℝ) • dx1.comp uCLM

/-- `D²u = u_tt`. -/
noncomputable def D2uCLM : Par × Wsp α →L[ℝ] PH α 0 := (kappa⁻¹ : ℝ) • dx2.comp uCLM

/-- Log-density `h cos 3t + u`. -/
noncomputable def phiCLM : Par × Wsp α →L[ℝ] PH α 0 := (pc 2).smulRight cos3 + u0CLM

section Defs
variable (α)
/-- Density `ρ = exp(φ)/∫exp φ`. -/
noncomputable def rho (x : Par × Wsp α) : PH α 0 := PH.normMap 0 (phiCLM x)

/-- Euler–Lagrange expression `E = u_tt + r u - 3h sin3t u_t + ½ u_t²`, `r = 1 + γ`. -/
noncomputable def eul (x : Par × Wsp α) : PH α 0 :=
  D2uCLM x + (1 + x.1 3) • u0CLM x - (3 * x.1 2) • (sin3 * DuCLM x) + (1 / 2 : ℝ) • (DuCLM x * DuCLM x)

/-- `κ = ∫ρ u_t² - 2 r ∫ ρ u`. -/
noncomputable def kap (x : Par × Wsp α) : ℝ :=
  PH.integral 0 (rho α x * (DuCLM x * DuCLM x)) - 2 * (1 + x.1 3) * PH.integral 0 (rho α x * u0CLM x)

noncomputable def resid (x : Par × Wsp α) : PH α 0 := eul α x + (kap α x / 2) • (1 : PH α 0)

/-- The range map: the Riesz gradient `-2 Q[ρ (E + κ/2)]` of the constrained functional. -/
noncomputable def rangeMap (x : Par × Wsp α) : PH.orthSub α 0 :=
  (-2 : ℝ) • Qproj (rho α x * resid α x)
end Defs


section Smooth

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem contDiff_mulB {n : WithTop ℕ∞} {f g : X → PH α 0} (hf : ContDiff ℝ n f)
    (hg : ContDiff ℝ n g) : ContDiff ℝ n (fun x => f x * g x) :=
  (mulCLM.contDiff.comp hf).clm_apply hg

theorem pc_apply (i : Fin 4) (x : Par × Wsp α) : pc i x = x.1 i := rfl

theorem contDiff_rho (n : WithTop ℕ∞) : ContDiff ℝ n (rho α) :=
  (PH.contDiff_normMap 0 n).comp phiCLM.contDiff

theorem contDiff_eul (n : WithTop ℕ∞) : ContDiff ℝ n (eul α) := by
  have h3 : ContDiff ℝ n (fun x : Par × Wsp α => x.1 3) := (pc 3).contDiff
  have h2 : ContDiff ℝ n (fun x : Par × Wsp α => x.1 2) := (pc 2).contDiff
  unfold eul
  refine ((D2uCLM.contDiff.add ((contDiff_const.add h3).smul u0CLM.contDiff)).sub
    ((contDiff_const.mul h2).smul (contDiff_mulB contDiff_const DuCLM.contDiff))).add
    ((contDiff_mulB DuCLM.contDiff DuCLM.contDiff).const_smul _)

theorem contDiff_kap (n : WithTop ℕ∞) : ContDiff ℝ n (kap α) := by
  have h3 : ContDiff ℝ n (fun x : Par × Wsp α => x.1 3) := (pc 3).contDiff
  unfold kap
  exact ((PH.integral 0).contDiff.comp (contDiff_mulB (contDiff_rho n)
      (contDiff_mulB DuCLM.contDiff DuCLM.contDiff))).sub
    ((contDiff_const.mul (contDiff_const.add h3)).mul
      ((PH.integral 0).contDiff.comp (contDiff_mulB (contDiff_rho n) u0CLM.contDiff)))

theorem contDiff_resid (n : WithTop ℕ∞) : ContDiff ℝ n (resid α) :=
  (contDiff_eul n).add (((contDiff_kap n).div_const 2).smul contDiff_const)

theorem contDiff_rangeMap (n : WithTop ℕ∞) : ContDiff ℝ n (rangeMap α) :=
  (Qproj.contDiff.comp (contDiff_mulB (contDiff_rho n) (contDiff_resid n))).const_smul _

end Smooth


section Deriv

theorem phiCLM_zero : phiCLM (0 : Par × Wsp α) = 0 := map_zero _
theorem DuCLM_zero : DuCLM (0 : Par × Wsp α) = 0 := map_zero _
theorem u0CLM_zero : u0CLM (0 : Par × Wsp α) = 0 := map_zero _

theorem expMap_zero : PH.expMap (α := α) 0 0 = 1 := by
  refine PH.ext (funext fun x => ?_)
  rw [PH.expMap_val]; simp

theorem integral_one : PH.integral (α := α) 0 1 = 1 := by
  rw [PH.integral_apply]; simp

theorem normMap_zero : PH.normMap (α := α) 0 0 = 1 := by
  unfold PH.normMap
  rw [expMap_zero, integral_one]; simp

theorem rho_zero : rho α 0 = 1 := by
  unfold rho; rw [phiCLM_zero, normMap_zero]

theorem eul_zero : eul α 0 = 0 := by
  unfold eul
  simp [DuCLM_zero, u0CLM_zero]

theorem kap_zero : kap α 0 = 0 := by
  unfold kap
  simp [DuCLM_zero, u0CLM_zero, rho_zero]

theorem resid_zero : resid α 0 = 0 := by
  unfold resid
  rw [eul_zero, kap_zero]; simp

theorem rangeMap_zero : rangeMap α 0 = 0 := by
  unfold rangeMap
  rw [resid_zero, rho_zero]; simp

theorem hasFDerivAt_eul : HasFDerivAt (eul α) (D2uCLM + u0CLM) (0 : Par × Wsp α) := by
  have h3 : HasFDerivAt (fun x : Par × Wsp α => (1 + x.1 3)) (pc 3) 0 := by
    have := (pc (α := α) 3).hasFDerivAt (x := 0)
    exact (this.const_add 1).congr_fderiv (by simp)
  have h2 : HasFDerivAt (fun x : Par × Wsp α => 3 * x.1 2) ((3 : ℝ) • pc 2) 0 := by
    have := (pc (α := α) 2).hasFDerivAt (x := 0)
    exact (this.const_mul 3).congr_fderiv (by simp)
  have hD := DuCLM.hasFDerivAt (x := (0 : Par × Wsp α))
  have hu0 := u0CLM.hasFDerivAt (x := (0 : Par × Wsp α))
  have hD2 := D2uCLM.hasFDerivAt (x := (0 : Par × Wsp α))
  have t2 := h3.smul hu0
  have t3 := h2.smul ((mulCLM sin3).hasFDerivAt.comp (0 : Par × Wsp α) hD)
  have hc : HasFDerivAt (fun x : Par × Wsp α => (mulCLM (DuCLM x) : PH α 0 →L[ℝ] PH α 0))
      (mulCLM.comp DuCLM) 0 := mulCLM.hasFDerivAt.comp (0 : Par × Wsp α) hD
  have t4 := hc.clm_apply hD
  have all := ((hD2.add t2).sub t3).add (t4.const_smul (1 / 2 : ℝ))
  refine all.congr_fderiv ?_
  ext x
  · simp [u0CLM_zero, DuCLM_zero]
  · simp [u0CLM_zero, DuCLM_zero]




end Deriv

section Deriv2

theorem Qproj_const (c : ℝ) : Qproj (c • (1 : PH α 0)) = 0 := by
  refine Subtype.ext ?_
  rw [Qproj_val]
  refine PH.ext (funext fun x => ?_)
  have hI : PH.integral (α := α) 0 (c • 1) = c := by
    rw [map_smul, integral_one]; simp
  have hC : PH.cosCoeff (α := α) 0 1 (c • 1) = 0 := by
    rw [PH.cosCoeff_apply]; simp
  have hS : PH.sinCoeff (α := α) 0 1 (c • 1) = 0 := by
    rw [PH.sinCoeff_apply]; simp
  show (c • (1 : PH α 0)).val x - (PH.modeProj 0 {0, 1} (c • 1)).val x = 0
  rw [PH.modeProj01_val, hI, hC, hS]
  simp

theorem hasFDerivAt_resid : ∃ K : Par × Wsp α →L[ℝ] ℝ,
    HasFDerivAt (resid α) (D2uCLM + u0CLM + K.smulRight (1 : PH α 0)) (0 : Par × Wsp α) := by
  have hk : HasFDerivAt (kap α) (fderiv ℝ (kap α) 0) (0 : Par × Wsp α) :=
    (((contDiff_kap (α := α) 1).differentiable (by simp)) 0).hasFDerivAt
  have hk2 : HasFDerivAt (fun x => kap α x / 2) ((1 / 2 : ℝ) • fderiv ℝ (kap α) 0) 0 := by
    have := hk.const_smul (1 / 2 : ℝ)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    rw [Pi.smul_apply, smul_eq_mul]; ring
  have := hk2.smul_const (1 : PH α 0)
  have all := hasFDerivAt_eul.add this
  exact ⟨_, all⟩


theorem uCLM_inr (v : Wsp α) : uCLM ((0 : Par), v) = (v : PH α 2) := by
  simp [uCLM, pc_apply]

theorem D2uCLM_inr (v : Wsp α) : D2uCLM ((0 : Par), v) = (kappa⁻¹ : ℝ) • dx2 (v : PH α 2) := by
  simp [D2uCLM, uCLM_inr]

theorem u0CLM_inr (v : Wsp α) : u0CLM ((0 : Par), v) = incl2 (v : PH α 2) := by
  simp [u0CLM, uCLM_inr]

theorem Qproj_orth (f : PH α 0) (hf : f ∈ PH.orthSub α 0) : (Qproj f : PH α 0) = f := by
  rw [Qproj_val, PH.modeProj01_eq_zero hf, sub_zero]

theorem fderiv_rangeMap_inr (v : Wsp α) :
    fderiv ℝ (rangeMap α) 0 ((0 : Par), v) = (-2 : ℝ) • ellOrth v := by
  obtain ⟨K, hr⟩ := hasFDerivAt_resid (α := α)
  have hρ : HasFDerivAt (rho α) (fderiv ℝ (rho α) 0) (0 : Par × Wsp α) :=
    (((contDiff_rho (α := α) 1).differentiable (by simp)) 0).hasFDerivAt
  have hprod := (mulCLM.hasFDerivAt.comp (0 : Par × Wsp α) hρ).clm_apply hr
  have hQ := Qproj.hasFDerivAt.comp (0 : Par × Wsp α) hprod
  have hfin := hQ.const_smul (-2 : ℝ)
  have hd : HasFDerivAt (rangeMap α) _ (0 : Par × Wsp α) := hfin
  rw [hd.fderiv]
  refine Subtype.ext ?_
  have key : ((((mulCLM (rho α 0)).comp (D2uCLM + u0CLM + K.smulRight 1) +
      (mulCLM.comp (fderiv ℝ (rho α) 0)).flip (resid α 0) : Par × Wsp α →L[ℝ] PH α 0))
      ((0 : Par), v) : PH α 0) =
      ell (v : PH α 2) + K ((0 : Par), v) • (1 : PH α 0) := by
    rw [resid_zero]
    simp [rho_zero, D2uCLM_inr, u0CLM_inr, ell_eq]
  have hmem : ell (v : PH α 2) ∈ PH.orthSub α 0 := ell_mem_orthSub v.2
  show ((((-2 : ℝ) • Qproj ((((mulCLM (rho α 0)).comp (D2uCLM + u0CLM + K.smulRight 1) +
      (mulCLM.comp (fderiv ℝ (rho α) 0)).flip (resid α 0) : Par × Wsp α →L[ℝ] PH α 0))
      ((0 : Par), v))) : PH.orthSub α 0) : PH α 0) = _
  rw [key, map_add, Qproj_const, add_zero]
  show (-2 : ℝ) • ((Qproj (ell (v : PH α 2)) : PH.orthSub α 0) : PH α 0) = (-2 : ℝ) • ((ellOrth v : PH.orthSub α 0) : PH α 0)
  rw [Qproj_orth _ hmem, ellOrth_apply]


theorem fderiv_rangeMap_comp_inr :
    fderiv ℝ (rangeMap α) 0 ∘L ContinuousLinearMap.inr ℝ Par (Wsp α) = (-2 : ℝ) • ellOrth := by
  ext v : 1
  exact fderiv_rangeMap_inr v

theorem rangeMap_isInvertible :
    (fderiv ℝ (rangeMap α) 0 ∘L ContinuousLinearMap.inr ℝ Par (Wsp α)).IsInvertible := by
  rw [fderiv_rangeMap_comp_inr]
  refine ⟨ContinuousLinearEquiv.equivOfInverse ((-2 : ℝ) • ellOrth) ((-1 / 2 : ℝ) • ellInv)
    (fun u => ?_) (fun f => ?_), rfl⟩
  · simp only [FunLike.coe_smul, Pi.smul_apply, map_smul, ellInv_ell, smul_smul]
    norm_num
  · have := ellOrth_ellInv (α := α) f
    simp only [FunLike.coe_smul, Pi.smul_apply, map_smul, this, smul_smul]
    norm_num

end Deriv2

end Maps

section Main
variable {α : ℝ} [HolderExponent α]

theorem threefold_range_equation_invertible :
    ContDiff ℝ ω (rangeMap α) ∧ rangeMap α 0 = 0 ∧
    fderiv ℝ (rangeMap α) 0 ∘L ContinuousLinearMap.inr ℝ Par (Wsp α) = (-2 : ℝ) • ellOrth ∧
    (fderiv ℝ (rangeMap α) 0 ∘L ContinuousLinearMap.inr ℝ Par (Wsp α)).IsInvertible ∧
    ∀ k : ℕ, 1 ≤ k → ∃ U : Set Par, IsOpen U ∧ (0 : Par) ∈ U ∧ ∃ Wn : Set (Wsp α), IsOpen Wn ∧
      (0 : Wsp α) ∈ Wn ∧ ∃ ψ : Par → Wsp α,
      ψ 0 = 0 ∧
      (∀ p ∈ U, ψ p ∈ Wn ∧ rangeMap α (p, ψ p) = 0) ∧
      (∀ p ∈ U, ∀ w ∈ Wn, rangeMap α (p, w) = 0 → w = ψ p) ∧
      ContDiffOn ℝ k ψ U ∧
      (∀ p ∈ U, (fderiv ℝ (rangeMap α) (p, ψ p) ∘L ContinuousLinearMap.inr ℝ Par (Wsp α)).IsInvertible ∧
        HasFDerivAt ψ (-(fderiv ℝ (rangeMap α) (p, ψ p) ∘L ContinuousLinearMap.inr ℝ Par (Wsp α)).inverse ∘L
          (fderiv ℝ (rangeMap α) (p, ψ p) ∘L ContinuousLinearMap.inl ℝ Par (Wsp α))) p) := by
  refine ⟨contDiff_rangeMap _, rangeMap_zero, fderiv_rangeMap_comp_inr, rangeMap_isInvertible, ?_⟩
  intro k hk
  obtain ⟨U, hU, h0, Wn, hWn, hw0, ψ, h1, h2, h3, h4, h5, -, -⟩ :=
    DGPS.Analysis.parameter_implicit_function_and_differentiated_remainders
      (F := rangeMap α) (p₀ := (0 : Par)) (w₀ := (0 : Wsp α)) hk
      ((contDiff_rangeMap (α := α) k).contDiffAt) (by have := rangeMap_zero (α := α); rwa [← Prod.mk_zero_zero] at this)
      rangeMap_isInvertible
  exact ⟨U, hU, h0, Wn, hWn, hw0, ψ, h1, h2, h3, h4, h5⟩

end Main

section Jet
variable {α : ℝ} [HolderExponent α]

theorem trig_mem_orth {k n : ℕ} (hn : 2 ≤ n) (a b : ℝ) :
    PH.trig (α := α) k n a b ∈ PH.orthSub α k := by
  refine ⟨?_, ?_, ?_⟩
  · rw [PH.integral_apply]; exact integral_trig_const (by omega) a b
  · rw [PH.cosCoeff_apply]; exact integral_trig_cos_one (by omega) a b
  · rw [PH.sinCoeff_apply]; exact integral_trig_sin_one (by omega) a b

theorem trig_lin (k n : ℕ) (a b : ℝ) :
    PH.trig (α := α) k n a b = a • PH.trig k n 1 0 + b • PH.trig k n 0 1 := by
  refine PH.ext (funext fun x => ?_)
  simp [trigFun]

theorem ell_trig (n : ℕ) (a b : ℝ) :
    ell (PH.trig (α := α) 2 n a b) = (1 - (n : ℝ) ^ 2) • PH.trig 0 n a b := by
  refine PH.ext ?_
  rw [ell_val, PH.val_trig, ellFun_trigFun]
  rfl

/-- The elements `a cos(nt) + b sin(nt)` of the range space, `n ≥ 2`. -/
noncomputable def tw (n : ℕ) (hn : 2 ≤ n) (a b : ℝ) : Wsp α :=
  ⟨PH.trig 2 n a b, trig_mem_orth hn a b⟩

theorem tw_val (n : ℕ) (hn : 2 ≤ n) (a b : ℝ) : ((tw n hn a b : Wsp α) : PH α 2) = PH.trig 2 n a b := rfl

theorem tw_lin (n : ℕ) (hn : 2 ≤ n) (a b : ℝ) :
    tw (α := α) n hn a b = a • tw n hn 1 0 + b • tw n hn 0 1 :=
  Subtype.ext (trig_lin 2 n a b)

/-- Coefficients of the weighted-degree-two jet. -/
noncomputable def jc2 (p : Par) : ℝ := p 2 * p 0 / 2 + (p 1 ^ 2 - p 0 ^ 2) / 12
noncomputable def js2 (p : Par) : ℝ := -(p 2 * p 1) / 2 - p 0 * p 1 / 6
noncomputable def jc4 (p : Par) : ℝ := -(p 2 * p 0) / 10
noncomputable def js4 (p : Par) : ℝ := -(p 2 * p 1) / 10

/-- The weighted-degree-two jet of the range solution. -/
noncomputable def jetW (p : Par) : Wsp α :=
  tw 2 le_rfl (jc2 p) (js2 p) + tw 4 (by norm_num) (jc4 p) (js4 p)

/-- Second-order part of the Euler–Lagrange expression. -/
noncomputable def E2 (p : Par) : PH α 0 :=
  (-(3 * p 2) : ℝ) • (sin3 * PH.trig 0 1 (p 1) (-(p 0))) +
    (1 / 2 : ℝ) • (PH.trig 0 1 (p 1) (-(p 0)) * PH.trig 0 1 (p 1) (-(p 0)))

theorem E2_eq (p : Par) :
    E2 (α := α) p = ((p 0 ^ 2 + p 1 ^ 2) / 4 : ℝ) • (1 : PH α 0) +
      (PH.trig 0 2 (3 * p 2 * p 0 / 2 + (p 1 ^ 2 - p 0 ^ 2) / 4) (-(3 * p 2 * p 1) / 2 - p 0 * p 1 / 2) +
       PH.trig 0 4 (-(3 * p 2 * p 0) / 2) (-(3 * p 2 * p 1) / 2)) := by
  refine PH.ext (funext fun x => ?_)
  set θ := 2 * Real.pi * x with hθ
  have e1 : 2 * Real.pi * ((1 : ℕ) : ℝ) * x = θ := by simp [hθ]
  have e2 : 2 * Real.pi * ((2 : ℕ) : ℝ) * x = 2 * θ := by simp [hθ]; ring
  have e3 : 2 * Real.pi * ((3 : ℕ) : ℝ) * x = 3 * θ := by simp [hθ]; ring
  have e4 : 2 * Real.pi * ((4 : ℕ) : ℝ) * x = 4 * θ := by simp [hθ]; ring
  have F1 : Real.sin (3 * θ) * Real.sin θ = (Real.cos (2 * θ) - Real.cos (4 * θ)) / 2 := by
    have h1 := Real.cos_sub (3 * θ) θ
    have h2 := Real.cos_add (3 * θ) θ
    rw [show 3 * θ - θ = 2 * θ by ring] at h1
    rw [show 3 * θ + θ = 4 * θ by ring] at h2
    linarith
  have F2 : Real.sin (3 * θ) * Real.cos θ = (Real.sin (4 * θ) + Real.sin (2 * θ)) / 2 := by
    have h1 := Real.sin_add (3 * θ) θ
    have h2 := Real.sin_sub (3 * θ) θ
    rw [show 3 * θ - θ = 2 * θ by ring] at h2
    rw [show 3 * θ + θ = 4 * θ by ring] at h1
    linarith
  have F3 : Real.cos θ ^ 2 = (1 + Real.cos (2 * θ)) / 2 := by
    rw [Real.cos_two_mul]; ring
  have F4 : Real.sin θ ^ 2 = (1 - Real.cos (2 * θ)) / 2 := by
    rw [Real.cos_two_mul, Real.sin_sq]; ring
  have F5 : Real.sin θ * Real.cos θ = Real.sin (2 * θ) / 2 := by
    rw [Real.sin_two_mul]; ring
  simp only [E2, sin3, PH.val_add, PH.val_smul, PH.val_mul, PH.val_trig, PH.val_one, trigFun,
    Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.one_apply, smul_eq_mul, e1, e2, e3, e4]
  linear_combination (-3 * p 2 * p 1) * F2 + (3 * p 2 * p 0) * F1 + (p 1 ^ 2 / 2) * F3 +
    (-(p 0) * p 1) * F5 + (p 0 ^ 2 / 2) * F4

end Jet

section Generic

theorem eq_zero_of_le_mul {V : Type*} [NormedAddCommGroup V] (c : V) (C r : ℝ) (hr : 0 < r)
    (h : ∀ s : ℝ, 0 < s → s < r → ‖c‖ ≤ C * s) : c = 0 := by
  rw [← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set s := min (r / 2) (ε / (|C| + 1)) with hs
  have hC : 0 < |C| + 1 := by positivity
  have hs0 : 0 < s := lt_min (by linarith) (by positivity)
  have hsr : s < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have h1 := h s hs0 hsr
  have h2 : s ≤ ε / (|C| + 1) := min_le_right _ _
  have h3 : C * s ≤ |C| * s := mul_le_mul_of_nonneg_right (le_abs_self C) hs0.le
  have h4 : |C| * s ≤ |C| * (ε / (|C| + 1)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
  have h5 : |C| * (ε / (|C| + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hC]
    nlinarith [abs_nonneg C]
  linarith

theorem eq_zero_of_le_pow {V : Type*} [NormedAddCommGroup V] (c : V) (C r : ℝ) (n : ℕ) (hr : 0 < r)
    (h : ∀ s : ℝ, 0 < s → s < r → ‖c‖ ≤ C * s ^ (n + 1)) : c = 0 := by
  refine eq_zero_of_le_mul c |C| (min r 1) (lt_min hr one_pos) fun s hs hsr => ?_
  have h1 := h s hs (lt_of_lt_of_le hsr (min_le_left _ _))
  have hs1 : s < 1 := lt_of_lt_of_le hsr (min_le_right _ _)
  have h2 : s ^ (n + 1) ≤ s := by
    calc s ^ (n + 1) = s ^ n * s := pow_succ s n
      _ ≤ 1 * s := by gcongr; exact pow_le_one₀ hs.le hs1.le
      _ = s := one_mul s
  calc ‖c‖ ≤ C * s ^ (n + 1) := h1
    _ ≤ |C| * s ^ (n + 1) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * s := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)

theorem poly2_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (c0 c1 c2 : V) (C r : ℝ)
    (hr : 0 < r)
    (h : ∀ s : ℝ, 0 < s → s < r → ‖c0 + s • c1 + s ^ 2 • c2‖ ≤ C * s ^ 3) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
  have hr3 : 0 < r / 3 := by linarith
  have key : ∀ s : ℝ, 0 < s → s < r / 3 →
      ‖c0 + s • c1 + s ^ 2 • c2‖ ≤ C * s ^ 3 ∧ ‖c0 + (2 * s) • c1 + (2 * s) ^ 2 • c2‖ ≤ C * (2 * s) ^ 3 ∧
      ‖c0 + (3 * s) • c1 + (3 * s) ^ 2 • c2‖ ≤ C * (3 * s) ^ 3 := by
    intro s hs hsr
    exact ⟨h s hs (by linarith), h (2 * s) (by linarith) (by linarith),
      h (3 * s) (by linarith) (by linarith)⟩
  have e0 : c0 = 0 := by
    refine eq_zero_of_le_pow c0 (54 * C) (r / 3) 2 hr3 fun s hs hsr => ?_
    obtain ⟨k1, k2, k3⟩ := key s hs hsr
    have : c0 = (3 : ℝ) • (c0 + s • c1 + s ^ 2 • c2) - (3 : ℝ) • (c0 + (2 * s) • c1 + (2 * s) ^ 2 • c2) +
        (c0 + (3 * s) • c1 + (3 * s) ^ 2 • c2) := by module
    rw [this]
    calc _ ≤ ‖(3 : ℝ) • (c0 + s • c1 + s ^ 2 • c2) - (3 : ℝ) • (c0 + (2 * s) • c1 + (2 * s) ^ 2 • c2)‖ +
          ‖c0 + (3 * s) • c1 + (3 * s) ^ 2 • c2‖ := norm_add_le _ _
      _ ≤ (‖(3 : ℝ) • (c0 + s • c1 + s ^ 2 • c2)‖ + ‖(3 : ℝ) • (c0 + (2 * s) • c1 + (2 * s) ^ 2 • c2)‖) +
          ‖c0 + (3 * s) • c1 + (3 * s) ^ 2 • c2‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ 3 * (C * s ^ 3) + 3 * (C * (2 * s) ^ 3) + C * (3 * s) ^ 3 := by
          rw [norm_smul, norm_smul]
          norm_num
          gcongr
      _ = 54 * C * s ^ (2 + 1) := by ring
  subst e0
  have e1 : c1 = 0 := by
    refine eq_zero_of_le_pow c1 (6 * C) (r / 3) 1 hr3 fun s hs hsr => ?_
    obtain ⟨k1, k2, -⟩ := key s hs hsr
    simp only [zero_add] at k1 k2
    have : s • c1 = (2 : ℝ) • (s • c1 + s ^ 2 • c2) - (1 / 2 : ℝ) • ((2 * s) • c1 + (2 * s) ^ 2 • c2) := by
      module
    have hn : ‖s • c1‖ ≤ 6 * C * s ^ 3 := by
      rw [this]
      calc _ ≤ ‖(2 : ℝ) • (s • c1 + s ^ 2 • c2)‖ + ‖(1 / 2 : ℝ) • ((2 * s) • c1 + (2 * s) ^ 2 • c2)‖ :=
            norm_sub_le _ _
        _ ≤ 2 * (C * s ^ 3) + 1 / 2 * (C * (2 * s) ^ 3) := by
            rw [norm_smul, norm_smul]
            norm_num
            gcongr
        _ = 6 * C * s ^ 3 := by ring
    rw [norm_smul, Real.norm_of_nonneg hs.le] at hn
    have : ‖c1‖ * s ≤ (6 * C * s ^ 2) * s := by nlinarith
    exact le_of_mul_le_mul_right this hs
  subst e1
  refine ⟨rfl, rfl, ?_⟩
  refine eq_zero_of_le_pow c2 C (r / 3) 0 hr3 fun s hs hsr => ?_
  obtain ⟨k1, -, -⟩ := key s hs hsr
  simp only [zero_add, smul_zero] at k1
  rw [norm_smul, norm_pow, Real.norm_of_nonneg hs.le] at k1
  have : ‖c2‖ * s ^ 2 ≤ (C * s) * s ^ 2 := by nlinarith
  have h2 := le_of_mul_le_mul_right this (by positivity)
  simpa using h2

end Generic

section Generic2

theorem lipschitz_inverse {P W V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : P × W → V) (hF : ContDiff ℝ 1 F)
    (hinv : (fderiv ℝ F 0 ∘L ContinuousLinearMap.inr ℝ P W).IsInvertible) :
    ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, ∀ (p : P) (w₁ w₂ : W), ‖p‖ < r → ‖w₁‖ < r → ‖w₂‖ < r →
      ‖w₁ - w₂‖ ≤ M * ‖F (p, w₁) - F (p, w₂)‖ := by
  obtain ⟨e, he⟩ := hinv
  set L : W →L[ℝ] V := fderiv ℝ F 0 ∘L ContinuousLinearMap.inr ℝ P W with hL
  set m : ℝ := ‖(e.symm : V →L[ℝ] W)‖ with hm
  have hm0 : 0 ≤ m := norm_nonneg _
  set ε : ℝ := 1 / (2 * (m + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hcont : Continuous (fun v : P × W => fderiv ℝ F v ∘L ContinuousLinearMap.inr ℝ P W) :=
    (hF.continuous_fderiv (by simp)).clm_comp continuous_const
  have hev : ∀ᶠ v in 𝓝 (0 : P × W), ‖(fderiv ℝ F v ∘L ContinuousLinearMap.inr ℝ P W) - L‖ < ε := by
    have := hcont.continuousAt (x := (0 : P × W))
    have h2 := this.eventually (Metric.ball_mem_nhds _ hε0)
    filter_upwards [h2] with v hv
    simpa [dist_eq_norm, hL] using hv
  obtain ⟨r, hr, hrball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨r, hr, 2 * m, fun p w₁ w₂ hp hw₁ hw₂ => ?_⟩
  set g : W → V := fun w => F (p, w) - L w with hg
  have hgd : ∀ w ∈ Metric.ball (0 : W) r, HasFDerivWithinAt g
      ((fderiv ℝ F (p, w) ∘L ContinuousLinearMap.inr ℝ P W) - L) (Metric.ball (0 : W) r) w := by
    intro w _
    have h1 : HasFDerivAt (fun w : W => (p, w)) (ContinuousLinearMap.inr ℝ P W) w :=
      (hasFDerivAt_const p w).prodMk (hasFDerivAt_id w)
    have h2 : HasFDerivAt F (fderiv ℝ F (p, w)) (p, w) :=
      ((hF.differentiable (by simp)) _).hasFDerivAt
    exact ((h2.comp w h1).sub L.hasFDerivAt).hasFDerivWithinAt
  have hbd : ∀ w ∈ Metric.ball (0 : W) r,
      ‖(fderiv ℝ F (p, w) ∘L ContinuousLinearMap.inr ℝ P W) - L‖ ≤ ε := by
    intro w hw
    have : dist (p, w) (0 : P × W) < r := by
      rw [dist_eq_norm, sub_zero, Prod.norm_def]
      simp only [mem_ball_zero_iff] at hw
      exact max_lt hp hw
    exact (hrball this).le
  have hmv := (convex_ball (0 : W) r).norm_image_sub_le_of_norm_hasFDerivWithin_le hgd hbd
    (mem_ball_zero_iff.mpr hw₂) (mem_ball_zero_iff.mpr hw₁)
  have hLd : L (w₁ - w₂) = (F (p, w₁) - F (p, w₂)) - (g w₁ - g w₂) := by
    simp only [hg, map_sub]; abel
  have h1 : ‖w₁ - w₂‖ ≤ m * ‖L (w₁ - w₂)‖ := by
    have : w₁ - w₂ = (e.symm : V →L[ℝ] W) (L (w₁ - w₂)) := by
      rw [← he]; simp
    calc ‖w₁ - w₂‖ = ‖(e.symm : V →L[ℝ] W) (L (w₁ - w₂))‖ := by rw [← this]
      _ ≤ m * ‖L (w₁ - w₂)‖ := (e.symm : V →L[ℝ] W).le_opNorm _
  have h2 : ‖L (w₁ - w₂)‖ ≤ ‖F (p, w₁) - F (p, w₂)‖ + ε * ‖w₁ - w₂‖ := by
    rw [hLd]
    exact (norm_sub_le _ _).trans (by gcongr)
  have h3 : m * ε ≤ 1 / 2 := by
    rw [hε]
    rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  nlinarith [norm_nonneg (w₁ - w₂), norm_nonneg (F (p, w₁) - F (p, w₂))]

theorem localTaylor {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (G : P → W) (j : ℕ) (hG : ContDiffAt ℝ (j + 1 : ℕ) G 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ q : P, ‖q‖ ≤ r →
      ‖G q - ∑ i ∈ Finset.range (j + 1), (i.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ i G 0 (fun _ => q)‖ ≤
        C * ‖q‖ ^ (j + 1) := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hG.eventually (by simp))
  have hU : ContDiffOn ℝ (j + 1 : ℕ) G (Metric.ball (0 : P) ε) := fun y hy =>
    (hball (by simpa using hy)).contDiffWithinAt
  obtain ⟨C, hC⟩ := DGPS.Analysis.taylor_remainder_bound_of_contDiffOn (j := j) Metric.isOpen_ball hU
    (K := Metric.closedBall (0 : P) (ε / 2)) (Metric.closedBall_subset_ball (by linarith))
    (isCompact_closedBall _ _) (convex_closedBall _ _)
  refine ⟨ε / 2, by linarith, C, fun q hq => ?_⟩
  have := hC 0 (by simp; linarith) q (by simpa using hq)
  simpa using this

end Generic2

section Nu

/-- The weighted order `|a| + |b| + |h| + √|γ|`. -/
noncomputable def nu (p : Par) : ℝ := |p 0| + |p 1| + |p 2| + Real.sqrt |p 3|

theorem nu_nonneg (p : Par) : 0 ≤ nu p := by unfold nu; positivity

theorem nu_zero : nu 0 = 0 := by simp [nu]

theorem continuous_nu : Continuous nu := by
  unfold nu
  fun_prop

theorem abs_le_nu_0 (p : Par) : |p 0| ≤ nu p := by
  unfold nu; have := abs_nonneg (p 1); have := abs_nonneg (p 2); have := Real.sqrt_nonneg |p 3|; linarith
theorem abs_le_nu_1 (p : Par) : |p 1| ≤ nu p := by
  unfold nu; have := abs_nonneg (p 0); have := abs_nonneg (p 2); have := Real.sqrt_nonneg |p 3|; linarith
theorem abs_le_nu_2 (p : Par) : |p 2| ≤ nu p := by
  unfold nu; have := abs_nonneg (p 1); have := abs_nonneg (p 0); have := Real.sqrt_nonneg |p 3|; linarith
theorem abs_le_nu_3 (p : Par) : |p 3| ≤ nu p ^ 2 := by
  have h1 : Real.sqrt |p 3| ≤ nu p := by
    unfold nu; have := abs_nonneg (p 1); have := abs_nonneg (p 0); have := abs_nonneg (p 2); linarith
  calc |p 3| = Real.sqrt |p 3| ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
    _ ≤ nu p ^ 2 := by gcongr

theorem norm_le_nu (p : Par) (h : nu p ≤ 1) : ‖p‖ ≤ nu p := by
  have hn := nu_nonneg p
  refine (pi_norm_le_iff_of_nonneg hn).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact abs_le_nu_0 p
  · exact abs_le_nu_1 p
  · exact abs_le_nu_2 p
  · show |p 3| ≤ nu p
    have := abs_le_nu_3 p
    nlinarith

theorem nu_le_norm_mul (p : Par) : nu p ≤ 3 * ‖p‖ + Real.sqrt ‖p‖ := by
  have h0 : |p 0| ≤ ‖p‖ := by simpa using norm_le_pi_norm p 0
  have h1 : |p 1| ≤ ‖p‖ := by simpa using norm_le_pi_norm p 1
  have h2 : |p 2| ≤ ‖p‖ := by simpa using norm_le_pi_norm p 2
  have h3 : Real.sqrt |p 3| ≤ Real.sqrt ‖p‖ := by
    apply Real.sqrt_le_sqrt; simpa using norm_le_pi_norm p 3
  unfold nu; linarith

end Nu

section Vanish

theorem taylor_sum_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (Δ : Par → V) (v : Par) (s : ℝ) :
    ∑ i ∈ Finset.range 3, (i.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ i Δ 0 (fun _ => s • v) =
      Δ 0 + s • fderiv ℝ Δ 0 v + s ^ 2 • ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ Δ) 0 v v) := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, iteratedFDeriv_two_apply, map_smul,
    smul_apply]
  simp [Nat.factorial]
  module

theorem taylor_vanish {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (Δ : Par → V) (hΔ : ContDiffAt ℝ 3 Δ 0)
    (hb : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ q : Par, ‖q‖ < r → ‖Δ q‖ ≤ C * nu q ^ 3) :
    Δ 0 = 0 ∧ (∀ v : Par, v 3 = 0 → fderiv ℝ Δ 0 v = 0) ∧
      fderiv ℝ Δ 0 (Pi.single 3 1) = 0 ∧
      (∀ v v' : Par, v 3 = 0 → v' 3 = 0 → fderiv ℝ (fderiv ℝ Δ) 0 v v' = 0) := by
  obtain ⟨r0, hr0, C0, hC0⟩ := hb
  obtain ⟨r1, hr1, C1, hC1⟩ := localTaylor (P := Par) Δ 2 (by simpa using hΔ)
  have hdiag : ∀ v : Par, v 3 = 0 →
      Δ 0 = 0 ∧ fderiv ℝ Δ 0 v = 0 ∧ fderiv ℝ (fderiv ℝ Δ) 0 v v = 0 := by
    intro v hv
    set ρ := min r0 r1 with hρ
    have hρ0 : 0 < ρ := lt_min hr0 hr1
    have hv1 : 0 < ‖v‖ + 1 := by positivity
    have hp := poly2_zero (Δ 0) (fderiv ℝ Δ 0 v) ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ Δ) 0 v v)
      (C0 * (|v 0| + |v 1| + |v 2|) ^ 3 + C1 * ‖v‖ ^ 3) (ρ / (‖v‖ + 1)) (by positivity) (by
      intro s hs hsR
      have hq : ‖s • v‖ < ρ := by
        rw [norm_smul, Real.norm_of_nonneg hs.le]
        rw [lt_div_iff₀ hv1] at hsR
        nlinarith [norm_nonneg v]
      have hqr0 : ‖s • v‖ < r0 := lt_of_lt_of_le hq (min_le_left _ _)
      have hqr1 : ‖s • v‖ ≤ r1 := (lt_of_lt_of_le hq (min_le_right _ _)).le
      have e1 := hC0 _ hqr0
      have e2 := hC1 _ hqr1
      rw [taylor_sum_smul] at e2
      have hnu : nu (s • v) = s * (|v 0| + |v 1| + |v 2|) := by
        simp only [nu, Pi.smul_apply, smul_eq_mul, hv, mul_zero, abs_zero, Real.sqrt_zero, add_zero,
          abs_mul, abs_of_pos hs]
        ring
      rw [hnu] at e1
      rw [norm_smul, Real.norm_of_nonneg hs.le] at e2
      have e3 : ‖Δ 0 + s • fderiv ℝ Δ 0 v + s ^ 2 • ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ Δ) 0 v v)‖ ≤
          ‖Δ (s • v)‖ + ‖Δ (s • v) - (Δ 0 + s • fderiv ℝ Δ 0 v + s ^ 2 • ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ Δ) 0 v v))‖ := by
        have := norm_sub_le (Δ (s • v)) (Δ (s • v) - (Δ 0 + s • fderiv ℝ Δ 0 v + s ^ 2 • ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ Δ) 0 v v)))
        simpa using this
      calc _ ≤ _ := e3
        _ ≤ C0 * (s * (|v 0| + |v 1| + |v 2|)) ^ 3 + C1 * (s * ‖v‖) ^ 3 := add_le_add e1 e2
        _ = _ := by ring)
    obtain ⟨h0, h1, h2⟩ := hp
    refine ⟨h0, h1, ?_⟩
    have := smul_eq_zero.mp h2
    rcases this with h | h
    · norm_num at h
    · exact h
  have hsymm := (hΔ.isSymmSndFDerivAt (by simp; exact_mod_cast (by norm_num : (2:ℕ) ≤ 3)))
  have h0 : Δ 0 = 0 := (hdiag 0 rfl).1
  refine ⟨h0, fun v hv => (hdiag v hv).2.1, ?_, ?_⟩
  · obtain ⟨r2, hr2, C2, hC2⟩ := localTaylor (P := Par) Δ 1 (by simpa using hΔ.of_le (by norm_num))
    set e3 : Par := Pi.single 3 1 with he3
    set ρ := min (min r0 r2) 1 with hρ
    have hρ0 : 0 < ρ := lt_min (lt_min hr0 hr2) one_pos
    refine eq_zero_of_le_mul _ (|C0| + |C2|) ρ hρ0 fun t ht htρ => ?_
    have ht1 : t < 1 := lt_of_lt_of_le htρ (min_le_right _ _)
    have htr0 : t < r0 := lt_of_lt_of_le htρ ((min_le_left _ _).trans (min_le_left _ _))
    have htr2 : t < r2 := lt_of_lt_of_le htρ ((min_le_left _ _).trans (min_le_right _ _))
    have hq3 : (t ^ 2 • e3) 3 = t ^ 2 := by simp [he3]
    have hqn : ‖t ^ 2 • e3‖ = t ^ 2 := by
      rw [norm_smul, he3, norm_pow, Real.norm_of_nonneg ht.le]
      simp [Pi.norm_single]
    have hnu : nu (t ^ 2 • e3) = t := by
      simp only [nu, Pi.smul_apply, smul_eq_mul]
      simp [he3, abs_of_pos ht, Real.sqrt_sq ht.le]
    have e1 := hC0 (t ^ 2 • e3) (by
      rw [hqn]; nlinarith)
    have e2 := hC2 (t ^ 2 • e3) (by
      rw [hqn]; nlinarith)
    rw [hnu] at e1
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, Nat.factorial, Nat.cast_one, inv_one,
      one_smul, h0, hqn, map_smul] at e2
    norm_num at e2
    have e3' : ‖t ^ 2 • fderiv ℝ Δ 0 e3‖ ≤ ‖Δ (t ^ 2 • e3)‖ + ‖Δ (t ^ 2 • e3) - t ^ 2 • fderiv ℝ Δ 0 e3‖ := by
      have := norm_sub_le (Δ (t ^ 2 • e3)) (Δ (t ^ 2 • e3) - t ^ 2 • fderiv ℝ Δ 0 e3)
      simpa using this
    rw [norm_smul, norm_pow, Real.norm_of_nonneg ht.le] at e3'
    have hA := norm_nonneg (fderiv ℝ Δ 0 e3)
    have h4 : C2 * (t ^ 2) ^ 2 ≤ |C2| * t ^ 3 := by
      have : (t ^ 2) ^ 2 ≤ t ^ 3 := by nlinarith [pow_pos ht 3]
      calc C2 * (t ^ 2) ^ 2 ≤ |C2| * (t ^ 2) ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |C2| * t ^ 3 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    have h5 : C0 * t ^ 3 ≤ |C0| * t ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have h6 : t ^ 2 * ‖fderiv ℝ Δ 0 e3‖ ≤ ((|C0| + |C2|) * t) * t ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left (by linarith) (pow_pos ht 2)
  · intro v v' hv hv'
    have a1 := (hdiag (v + v') (by simp [hv, hv'])).2.2
    have a2 := (hdiag v hv).2.2
    have a3 := (hdiag v' hv').2.2
    simp only [map_add, add_apply] at a1
    rw [a2, a3, hsymm v v'] at a1
    have : (2 : ℝ) • fderiv ℝ (fderiv ℝ Δ) 0 v' v = 0 := by
      rw [two_smul]; simpa using a1
    rcases smul_eq_zero.mp this with h | h
    · norm_num at h
    · rw [hsymm v v']; exact h

end Vanish

section DerivBounds

set_option synthInstance.maxHeartbeats 400000 in
theorem deriv_bounds {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (Δ : Par → V) (hΔ : ContDiffAt ℝ 3 Δ 0)
    (hb : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ q : Par, ‖q‖ < r → ‖Δ q‖ ≤ C * nu q ^ 3) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ q : Par, ‖q‖ < r →
      ‖Δ q‖ ≤ C * nu q ^ 3 ∧
      (∀ v : Par, v 3 = 0 → ‖fderiv ℝ Δ q v‖ ≤ C * nu q ^ 2 * ‖v‖) ∧
      ‖fderiv ℝ Δ q (Pi.single 3 1)‖ ≤ C * nu q ∧
      (∀ v v' : Par, v 3 = 0 → v' 3 = 0 →
        ‖fderiv ℝ (fderiv ℝ Δ) q v v'‖ ≤ C * nu q * ‖v‖ * ‖v'‖) := by
  obtain ⟨hD0, hD1, hD3, hD2⟩ := taylor_vanish Δ hΔ hb
  obtain ⟨r0, hr0, C0, hC0⟩ := hb
  have hA : ContDiffAt ℝ (1 + 1 : ℕ) (fderiv ℝ Δ) 0 := by
    exact_mod_cast hΔ.fderiv_right (m := 2) (by norm_cast)
  have hA0 : ContDiffAt ℝ (0 + 1 : ℕ) (fderiv ℝ Δ) 0 := hA.of_le (by norm_num)
  have hB : ContDiffAt ℝ (0 + 1 : ℕ) (fderiv ℝ (fderiv ℝ Δ)) 0 := by
    have h1 : ContDiffAt ℝ 2 (fderiv ℝ Δ) 0 := hΔ.fderiv_right (m := 2) (by norm_cast)
    exact_mod_cast h1.fderiv_right (m := 1) (by norm_cast)
  have : CompleteSpace (Par →L[ℝ] V) := inferInstance
  have : CompleteSpace (Par →L[ℝ] Par →L[ℝ] V) := inferInstance
  obtain ⟨r1, hr1, C1, hC1⟩ := localTaylor (P := Par) _ 1 hA
  obtain ⟨r2, hr2, C2, hC2⟩ := localTaylor (P := Par) _ 0 hA0
  obtain ⟨r3, hr3, C3, hC3⟩ := localTaylor (P := Par) _ 0 hB
  set B0 := fderiv ℝ (fderiv ℝ Δ) 0 with hB0
  set S : ℝ := |C0| + |C1| + |C2| + |C3| + ‖B0‖ with hM
  have hM0 : 0 ≤ S := by positivity
  set M : ℝ := 2 * S with hMdef
  set ρ := min (min (min r0 r1) (min r2 r3)) 1 with hρ
  have hρ0 : 0 < ρ := lt_min (lt_min (lt_min hr0 hr1) (lt_min hr2 hr3)) one_pos
  refine ⟨ρ, hρ0, M, fun q hq => ?_⟩
  have hq1 : ‖q‖ < 1 := lt_of_lt_of_le hq (min_le_right _ _)
  have hqr0 : ‖q‖ < r0 := lt_of_lt_of_le hq ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hqr1 : ‖q‖ ≤ r1 := (lt_of_lt_of_le hq ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))).le
  have hqr2 : ‖q‖ ≤ r2 := (lt_of_lt_of_le hq ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))).le
  have hqr3 : ‖q‖ ≤ r3 := (lt_of_lt_of_le hq ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))).le
  have hnu_nonneg := nu_nonneg q
  have hqnu : ‖q‖ ≤ nu q := by
    have h3 : |q 3| ≤ Real.sqrt |q 3| := by
      have : |q 3| ≤ 1 := by simpa using (norm_le_pi_norm q 3).trans hq1.le
      calc |q 3| = Real.sqrt (|q 3| * |q 3|) := (Real.sqrt_mul_self (abs_nonneg _)).symm
        _ ≤ Real.sqrt |q 3| := Real.sqrt_le_sqrt (by nlinarith [abs_nonneg (q 3)])
    refine (pi_norm_le_iff_of_nonneg hnu_nonneg).2 fun i => ?_
    rw [Real.norm_eq_abs]
    fin_cases i
    · exact abs_le_nu_0 q
    · exact abs_le_nu_1 q
    · exact abs_le_nu_2 q
    · exact h3.trans (by simp [nu]; positivity)
  have hq3 := abs_le_nu_3 q
  have hMC0 : C0 ≤ S := by
    have := le_abs_self C0
    have : 0 ≤ |C1| + |C2| + |C3| + ‖B0‖ := by positivity
    linarith
  have hMC1 : C1 ≤ S := by
    have := le_abs_self C1
    have : 0 ≤ |C0| + |C2| + |C3| + ‖B0‖ := by positivity
    linarith
  have hMC2 : C2 ≤ S := by
    have := le_abs_self C2
    have : 0 ≤ |C0| + |C1| + |C3| + ‖B0‖ := by positivity
    linarith
  have hMC3 : C3 ≤ S := by
    have := le_abs_self C3
    have : 0 ≤ |C0| + |C1| + |C2| + ‖B0‖ := by positivity
    linarith
  have hMB : ‖B0‖ ≤ S := by
    have : 0 ≤ |C0| + |C1| + |C2| + |C3| := by positivity
    linarith
  have hnq : 0 ≤ ‖q‖ := norm_nonneg q
  have hdec : ∀ w : Par, w = Function.update w 3 0 + w 3 • (Pi.single 3 1 : Par) := by
    intro w; ext i; fin_cases i <;> simp
  have hA00 : fderiv ℝ Δ 0 = 0 := by
    ext w
    conv_lhs => rw [hdec w]
    rw [map_add, map_smul, hD1 _ (by simp), hD3]; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc ‖Δ q‖ ≤ C0 * nu q ^ 3 := hC0 q hqr0
      _ ≤ M * nu q ^ 3 := mul_le_mul_of_nonneg_right (by rw [hMdef]; linarith [hMC0]) (by positivity)
  · intro v hv
    have t1 := hC1 q hqr1
    simp [Finset.sum_range_succ, iteratedFDeriv_one_apply] at t1
    have hB1 : ‖fderiv ℝ (fderiv ℝ Δ) 0 q v‖ ≤ |q 3| * ‖B0‖ * ‖v‖ := by
      conv_lhs => rw [hdec q]
      rw [map_add, add_apply, hD2 _ _ (by simp) hv, zero_add, map_smul,
        smul_apply, norm_smul, Real.norm_eq_abs]
      have : ‖(B0 (Pi.single 3 1)) v‖ ≤ ‖B0‖ * ‖(Pi.single 3 1 : Par)‖ * ‖v‖ :=
        (B0 (Pi.single 3 1)).le_opNorm v |>.trans
          (mul_le_mul_of_nonneg_right (B0.le_opNorm _) (norm_nonneg _))
      have h1 : ‖(Pi.single 3 1 : Par)‖ = 1 := by simp [Pi.norm_single]
      rw [h1, mul_one] at this
      calc |q 3| * ‖(B0 (Pi.single 3 1)) v‖ ≤ |q 3| * (‖B0‖ * ‖v‖) :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = |q 3| * ‖B0‖ * ‖v‖ := by ring
    rw [hA00] at t1
    have e1 : fderiv ℝ Δ q v = (fderiv ℝ Δ q - (0 + fderiv ℝ (fderiv ℝ Δ) 0 q)) v +
        fderiv ℝ (fderiv ℝ Δ) 0 q v := by simp
    have n1 : ‖(fderiv ℝ Δ q - (0 + fderiv ℝ (fderiv ℝ Δ) 0 q)) v‖ ≤ C1 * ‖q‖ ^ 2 * ‖v‖ :=
      ((fderiv ℝ Δ q - (0 + fderiv ℝ (fderiv ℝ Δ) 0 q)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right t1 (norm_nonneg _))
    have hqq : ‖q‖ ^ 2 ≤ nu q ^ 2 := pow_le_pow_left₀ hnq hqnu 2
    have hv0 := norm_nonneg v
    have k1 : C1 * ‖q‖ ^ 2 ≤ S * nu q ^ 2 := by
      calc C1 * ‖q‖ ^ 2 ≤ |C1| * ‖q‖ ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ S * ‖q‖ ^ 2 := mul_le_mul_of_nonneg_right (by
            have : 0 ≤ |C0| + |C2| + |C3| + ‖B0‖ := by positivity
            rw [hM]; linarith) (by positivity)
        _ ≤ S * nu q ^ 2 := mul_le_mul_of_nonneg_left hqq hM0
    have k2 : |q 3| * ‖B0‖ ≤ S * nu q ^ 2 := by
      calc |q 3| * ‖B0‖ ≤ nu q ^ 2 * ‖B0‖ := mul_le_mul_of_nonneg_right hq3 (by positivity)
        _ ≤ nu q ^ 2 * S := mul_le_mul_of_nonneg_left hMB (by positivity)
        _ = S * nu q ^ 2 := by ring
    rw [e1]
    calc ‖(fderiv ℝ Δ q - (0 + fderiv ℝ (fderiv ℝ Δ) 0 q)) v + fderiv ℝ (fderiv ℝ Δ) 0 q v‖
        ≤ C1 * ‖q‖ ^ 2 * ‖v‖ + |q 3| * ‖B0‖ * ‖v‖ := (norm_add_le _ _).trans (add_le_add n1 hB1)
      _ = (C1 * ‖q‖ ^ 2 + |q 3| * ‖B0‖) * ‖v‖ := by ring
      _ ≤ (S * nu q ^ 2 + S * nu q ^ 2) * ‖v‖ := mul_le_mul_of_nonneg_right (add_le_add k1 k2) hv0
      _ = M * nu q ^ 2 * ‖v‖ := by rw [hMdef]; ring
  · have t2 := hC2 q hqr2
    simp at t2
    rw [hA00] at t2
    have h1 : ‖(Pi.single 3 1 : Par)‖ = 1 := by simp [Pi.norm_single]
    have e1 : ‖fderiv ℝ Δ q (Pi.single 3 1)‖ ≤ C2 * ‖q‖ := by
      calc ‖fderiv ℝ Δ q (Pi.single 3 1)‖ ≤ ‖fderiv ℝ Δ q‖ * ‖(Pi.single 3 1 : Par)‖ :=
            (fderiv ℝ Δ q).le_opNorm _
        _ ≤ C2 * ‖q‖ := by rw [h1, mul_one]; simpa using t2
    calc ‖fderiv ℝ Δ q (Pi.single 3 1)‖ ≤ C2 * ‖q‖ := e1
      _ ≤ S * nu q := mul_le_mul (hMC2) hqnu hnq hM0
      _ ≤ M * nu q := mul_le_mul_of_nonneg_right (by rw [hMdef]; linarith) hnu_nonneg
  · intro v v' hv hv'
    have t3 := hC3 q hqr3
    simp at t3
    have e1 : fderiv ℝ (fderiv ℝ Δ) q v v' =
        (fderiv ℝ (fderiv ℝ Δ) q - fderiv ℝ (fderiv ℝ Δ) 0) v v' := by
      simp [← hB0, hD2 v v' hv hv']
    rw [e1]
    have n1 : ‖(fderiv ℝ (fderiv ℝ Δ) q - fderiv ℝ (fderiv ℝ Δ) 0) v v'‖ ≤
        ‖fderiv ℝ (fderiv ℝ Δ) q - fderiv ℝ (fderiv ℝ Δ) 0‖ * ‖v‖ * ‖v'‖ :=
      (((fderiv ℝ (fderiv ℝ Δ) q - fderiv ℝ (fderiv ℝ Δ) 0) v).le_opNorm v').trans
        (mul_le_mul_of_nonneg_right
          (((fderiv ℝ (fderiv ℝ Δ) q - fderiv ℝ (fderiv ℝ Δ) 0).le_opNorm v)) (norm_nonneg _))
    have hv0 := norm_nonneg v
    have hv0' := norm_nonneg v'
    calc _ ≤ _ := n1
      _ ≤ C3 * ‖q‖ * ‖v‖ * ‖v'‖ := by gcongr
      _ ≤ S * nu q * ‖v‖ * ‖v'‖ := by
        gcongr
      _ ≤ M * nu q * ‖v‖ * ‖v'‖ := by
        gcongr
        rw [hMdef]; linarith

end DerivBounds

section Jet2
variable {α : ℝ} [HolderExponent α]

theorem PH_mul_isBigO {ι : Type*} {l : Filter ι} {f g : ι → PH α 0} {a b : ι → ℝ}
    (hf : f =O[l] a) (hg : g =O[l] b) : (fun i => f i * g i) =O[l] (fun i => a i * b i) := by
  obtain ⟨c, hc⟩ := hf.bound
  obtain ⟨d, hd⟩ := hg.bound
  have hS : 0 ≤ PH.scale α 0 := (zero_le_one.trans (PH.one_le_scale α 0))
  refine IsBigO.of_bound (PH.scale α 0 * (c * d)) ?_
  filter_upwards [hc, hd] with i h1 h2
  have h3 := PH.norm_mul_le_scale α 0 (f i) (g i)
  rw [norm_mul (a i) (b i)]
  have h4 : 0 ≤ c * ‖a i‖ := (norm_nonneg _).trans h1
  calc ‖f i * g i‖ ≤ PH.scale α 0 * (‖f i‖ * ‖g i‖) := h3
    _ ≤ PH.scale α 0 * ((c * ‖a i‖) * (d * ‖b i‖)) := by
        gcongr
    _ = _ := by ring

theorem Du_trig1 (a b : ℝ) :
    ((2 * Real.pi)⁻¹ : ℝ) • dx1 (PH.trig (α := α) 2 1 a b) = PH.trig 0 1 b (-a) := by
  refine PH.ext (funext fun x => ?_)
  have hd := (trigFun_hasDerivAt 1 a b x).deriv
  rw [PH.val_smul, dx1_val, PH.val_trig, PH.val_trig, Pi.smul_apply, hd]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  simp only [trigFun, Nat.cast_one, mul_one, smul_eq_mul]
  field_simp


theorem eventually_nu_lt_one : ∀ᶠ p : Par in 𝓝 0, nu p < 1 := by
  have : ContinuousAt nu (0 : Par) := continuous_nu.continuousAt
  have h0 : nu 0 < 1 := by rw [nu_zero]; exact one_pos
  exact this.eventually (gt_mem_nhds h0)

theorem bigO_nu_pow {E : Type*} [NormedAddCommGroup E] {f : Par → E} {k : ℕ} (C : ℝ)
    (h : ∀ᶠ p in 𝓝 (0 : Par), ‖f p‖ ≤ C * nu p ^ k) : f =O[𝓝 0] (fun p : Par => nu p ^ k) := by
  refine IsBigO.of_bound C ?_
  filter_upwards [h] with p hp
  have := nu_nonneg p
  rwa [Real.norm_of_nonneg (by positivity)]

theorem nu_pow_isBigO {i j : ℕ} (h : i ≤ j) :
    (fun p : Par => nu p ^ j) =O[𝓝 0] (fun p : Par => nu p ^ i) := by
  refine bigO_nu_pow 1 ?_
  filter_upwards [eventually_nu_lt_one] with p hp
  have h0 := nu_nonneg p
  rw [Real.norm_of_nonneg (by positivity), one_mul]
  exact pow_le_pow_of_le_one h0 hp.le h

theorem coord_isBigO {i : Fin 4} (hi : i ≠ 3) : (fun p : Par => p i) =O[𝓝 0] (fun p : Par => nu p ^ 1) := by
  refine bigO_nu_pow 1 (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, one_mul, pow_one]
  fin_cases i
  · exact abs_le_nu_0 p
  · exact abs_le_nu_1 p
  · exact abs_le_nu_2 p
  · exact absurd rfl hi

theorem gam_isBigO : (fun p : Par => p 3) =O[𝓝 0] (fun p : Par => nu p ^ 2) := by
  refine bigO_nu_pow 1 (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, one_mul]
  exact abs_le_nu_3 p

theorem smul_const_isBigO {ι : Type*} {l : Filter ι} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ι → ℝ) (X : E) : (fun i => c i • X) =O[l] c := by
  refine IsBigO.of_bound ‖X‖ (Eventually.of_forall fun i => ?_)
  rw [norm_smul, mul_comm]

theorem sq_le_nu (p : Par) {i : Fin 4} (hi : i ≠ 3) : p i ^ 2 ≤ nu p ^ 2 := by
  have : |p i| ≤ nu p := by
    fin_cases i
    · exact abs_le_nu_0 p
    · exact abs_le_nu_1 p
    · exact abs_le_nu_2 p
    · exact absurd rfl hi
  calc p i ^ 2 = |p i| ^ 2 := (sq_abs _).symm
    _ ≤ nu p ^ 2 := by gcongr

theorem mul_le_nu (p : Par) {i j : Fin 4} (hi : i ≠ 3) (hj : j ≠ 3) : |p i * p j| ≤ nu p ^ 2 := by
  have h1 : |p i| ≤ nu p := by
    fin_cases i
    · exact abs_le_nu_0 p
    · exact abs_le_nu_1 p
    · exact abs_le_nu_2 p
    · exact absurd rfl hi
  have h2 : |p j| ≤ nu p := by
    fin_cases j
    · exact abs_le_nu_0 p
    · exact abs_le_nu_1 p
    · exact abs_le_nu_2 p
    · exact absurd rfl hj
  rw [abs_mul, sq]
  exact mul_le_mul h1 h2 (abs_nonneg _) (nu_nonneg p)

theorem jcoef_isBigO : (fun p : Par => jc2 p) =O[𝓝 0] (fun p : Par => nu p ^ 2) ∧
    (fun p : Par => js2 p) =O[𝓝 0] (fun p : Par => nu p ^ 2) ∧
    (fun p : Par => jc4 p) =O[𝓝 0] (fun p : Par => nu p ^ 2) ∧
    (fun p : Par => js4 p) =O[𝓝 0] (fun p : Par => nu p ^ 2) := by
  refine ⟨bigO_nu_pow 1 (Eventually.of_forall fun p => ?_), bigO_nu_pow 1 (Eventually.of_forall fun p => ?_),
    bigO_nu_pow 1 (Eventually.of_forall fun p => ?_), bigO_nu_pow 1 (Eventually.of_forall fun p => ?_)⟩ <;>
  rw [Real.norm_eq_abs, one_mul]
  · have a1 := abs_le.mp (mul_le_nu p (i := 2) (j := 0) (by decide) (by decide))
    have a2 := sq_le_nu p (i := 0) (by decide)
    have a3 := sq_le_nu p (i := 1) (by decide)
    have a4 := sq_nonneg (p 0)
    have a5 := sq_nonneg (p 1)
    unfold jc2
    rw [abs_le]; constructor <;> nlinarith
  · have a1 := abs_le.mp (mul_le_nu p (i := 2) (j := 1) (by decide) (by decide))
    have a2 := abs_le.mp (mul_le_nu p (i := 0) (j := 1) (by decide) (by decide))
    unfold js2
    rw [abs_le]; constructor <;> nlinarith
  · have a1 := abs_le.mp (mul_le_nu p (i := 2) (j := 0) (by decide) (by decide))
    unfold jc4
    rw [abs_le]; constructor <;> nlinarith
  · have a1 := abs_le.mp (mul_le_nu p (i := 2) (j := 1) (by decide) (by decide))
    unfold js4
    rw [abs_le]; constructor <;> nlinarith


theorem jetW_coe (p : Par) : ((jetW p : Wsp α) : PH α 2) =
    (jc2 p • PH.trig 2 2 1 0 + js2 p • PH.trig 2 2 0 1) + (jc4 p • PH.trig 2 4 1 0 + js4 p • PH.trig 2 4 0 1) := by
  unfold jetW
  rw [Submodule.coe_add, tw_val, tw_val, trig_lin 2 2, trig_lin 2 4]

theorem jetW_isBigO : (fun p : Par => (jetW p : Wsp α)) =O[𝓝 0] (fun p : Par => nu p ^ 2) := by
  obtain ⟨h1, h2, h3, h4⟩ := jcoef_isBigO
  have e : (fun p : Par => ((jetW p : Wsp α) : PH α 2)) = fun p =>
    (jc2 p • PH.trig 2 2 1 0 + js2 p • PH.trig 2 2 0 1) + (jc4 p • PH.trig 2 4 1 0 + js4 p • PH.trig 2 4 0 1) :=
    funext jetW_coe
  have : (fun p : Par => ((jetW p : Wsp α) : PH α 2)) =O[𝓝 0] (fun p : Par => nu p ^ 2) := by
    rw [e]
    exact (((smul_const_isBigO _ _).trans h1).add ((smul_const_isBigO _ _).trans h2)).add
      (((smul_const_isBigO _ _).trans h3).add ((smul_const_isBigO _ _).trans h4))
  obtain ⟨c, hc⟩ := this.bound
  exact IsBigO.of_bound c hc

/-- The point `(p, jetW p)`. -/
noncomputable def Xp (p : Par) : Par × Wsp α := (p, jetW p)

theorem Xp_isBigO : (fun p : Par => (Xp p : Par × Wsp α)) =O[𝓝 0] (fun p : Par => nu p ^ 1) := by
  obtain ⟨C, hC⟩ := (jetW_isBigO (α := α)).bound
  refine bigO_nu_pow (1 + |C|) ?_
  filter_upwards [eventually_nu_lt_one, hC] with p hp hJ
  have h0 := nu_nonneg p
  rw [Real.norm_of_nonneg (by positivity)] at hJ
  have hn : ‖p‖ ≤ nu p := norm_le_nu p hp.le
  have hsq : nu p ^ 2 ≤ nu p := by nlinarith
  have hC' : C * nu p ^ 2 ≤ |C| * nu p := by
    calc C * nu p ^ 2 ≤ |C| * nu p ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C| * nu p := mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
  simp only [Xp, Prod.norm_def, pow_one]
  refine max_le ?_ ?_
  · nlinarith [abs_nonneg C]
  · nlinarith [abs_nonneg C]

theorem Xp_tendsto : Tendsto (fun p : Par => (Xp p : Par × Wsp α)) (𝓝 0) (𝓝 0) := by
  refine Xp_isBigO.trans_tendsto ?_
  have : Tendsto nu (𝓝 (0 : Par)) (𝓝 0) := by
    have h := continuous_nu.continuousAt (x := (0 : Par))
    rwa [ContinuousAt, nu_zero] at h
  simpa using this.pow 1

theorem sigma_isBigO : (fun p : Par => rho α (Xp p) - 1) =O[𝓝 0] (fun p : Par => nu p ^ 1) := by
  have hρ : HasFDerivAt (rho α) (fderiv ℝ (rho α) 0) (0 : Par × Wsp α) :=
    (((contDiff_rho (α := α) 1).differentiable (by simp)) 0).hasFDerivAt
  have := (hρ.isBigO_sub.comp_tendsto Xp_tendsto)
  simp only [rho_zero, sub_zero] at this
  exact this.trans Xp_isBigO


/-- The jet as an element of `C^{2,α}`. -/
noncomputable abbrev jw (p : Par) : PH α 2 := ((jetW p : Wsp α) : PH α 2)

/-- `(2π)⁻¹ ∂ₓ` on the chart space. -/
noncomputable def dwCLM : Wsp α →L[ℝ] PH α 0 :=
  ((2 * Real.pi)⁻¹ : ℝ) • (dx1 (α := α)).comp (PH.orthSub α 2).subtypeL

/-- First-order part of `Du`. -/
noncomputable def t1 (p : Par) : PH α 0 := PH.trig 0 1 (p 1) (-(p 0))

theorem uCLM_Xp (p : Par) :
    uCLM (Xp p : Par × Wsp α) = PH.trig 2 1 (p 0) (p 1) + (jw (α := α) p) := by
  have := trig_lin (α := α) 2 1 (p 0) (p 1)
  simp [uCLM, pc_apply, cosT, sinT, this, Xp]

theorem DuCLM_Xp (p : Par) : DuCLM (Xp p : Par × Wsp α) = t1 p + dwCLM (jetW p) := by
  simp only [DuCLM, smul_apply, ContinuousLinearMap.comp_apply, uCLM_Xp, map_add, smul_add, Du_trig1, dwCLM, t1]
  rfl

theorem D2u_add_u0 (x : Par × Wsp α) : D2uCLM x + u0CLM x = ell (uCLM x) := by
  simp [D2uCLM, u0CLM, ell_eq]

theorem ell_uXp (p : Par) : ell (uCLM (Xp p : Par × Wsp α)) = ell (jw (α := α) p) := by
  rw [uCLM_Xp, map_add, ell_trig]; simp

/-- Third-order remainder of the Euler-Lagrange expression. -/
noncomputable def R3 (p : Par) : PH α 0 :=
  (p 3) • u0CLM (Xp p : Par × Wsp α) + (-(3 * p 2) : ℝ) • (sin3 * dwCLM (jetW p)) +
    (1 / 2 : ℝ) • (t1 p * dwCLM (jetW p) + dwCLM (jetW p) * t1 p + dwCLM (jetW p) * dwCLM (jetW p))

theorem eul_Xp (p : Par) :
    eul α (Xp p) = (ell (jw (α := α) p) + E2 p) + R3 p := by
  have h := D2u_add_u0 (Xp p : Par × Wsp α)
  rw [ell_uXp] at h
  have e : eul α (Xp p) = (D2uCLM (Xp p : Par × Wsp α) + u0CLM (Xp p)) + (p 3) • u0CLM (Xp p : Par × Wsp α) -
      (3 * p 2) • (sin3 * DuCLM (Xp p : Par × Wsp α)) + (1 / 2 : ℝ) • (DuCLM (Xp p : Par × Wsp α) * DuCLM (Xp p)) := by
    unfold eul
    simp only [Xp, add_smul, one_smul]
    abel
  rw [e, h, DuCLM_Xp]
  unfold R3 E2
  simp only [t1, Algebra.smul_def, map_mul, map_neg, mul_add, add_mul]
  ring


theorem jw_eq (p : Par) : jw (α := α) p = PH.trig 2 2 (jc2 p) (js2 p) + PH.trig 2 4 (jc4 p) (js4 p) := by
  unfold jw jetW
  rw [Submodule.coe_add, tw_val, tw_val]

theorem jet_cancel (p : Par) :
    ell (jw (α := α) p) + E2 p = ((p 0 ^ 2 + p 1 ^ 2) / 4 : ℝ) • (1 : PH α 0) := by
  rw [jw_eq, map_add, ell_trig, ell_trig, E2_eq]
  refine PH.ext (funext fun x => ?_)
  simp only [PH.val_add, PH.val_smul, PH.val_trig, PH.val_one, trigFun, Pi.add_apply, Pi.smul_apply,
    Pi.one_apply, smul_eq_mul, jc2, js2, jc4, js4]
  push_cast
  ring

theorem Qproj_eul_Xp (p : Par) : Qproj (eul α (Xp p)) = Qproj (R3 (α := α) p) := by
  rw [eul_Xp, jet_cancel, map_add, Qproj_const, zero_add]

theorem const_isBigO_pow0 (c : PH α 0) : (fun _ : Par => c) =O[𝓝 0] (fun p : Par => nu p ^ 0) := by
  refine IsBigO.of_bound ‖c‖ (Eventually.of_forall fun p => ?_)
  simp

theorem PH_mul_pow {f g : Par → PH α 0} {i j : ℕ} (hf : f =O[𝓝 0] (fun p : Par => nu p ^ i))
    (hg : g =O[𝓝 0] (fun p : Par => nu p ^ j)) :
    (fun p => f p * g p) =O[𝓝 0] (fun p : Par => nu p ^ (i + j)) := by
  have := PH_mul_isBigO hf hg
  simpa only [pow_add] using this

theorem smul_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : Par → ℝ} {f : Par → E} {i j : ℕ}
    (hc : c =O[𝓝 0] (fun p : Par => nu p ^ i)) (hf : f =O[𝓝 0] (fun p : Par => nu p ^ j)) :
    (fun p => c p • f p) =O[𝓝 0] (fun p : Par => nu p ^ (i + j)) := by
  have := hc.smul hf
  simpa only [pow_add, smul_eq_mul] using this

theorem t1_isBigO : (fun p : Par => t1 (α := α) p) =O[𝓝 0] (fun p : Par => nu p ^ 1) := by
  have e : (fun p : Par => t1 (α := α) p) = fun p => p 1 • PH.trig 0 1 1 0 + (-(p 0)) • PH.trig 0 1 0 1 :=
    funext fun p => trig_lin 0 1 (p 1) (-(p 0))
  rw [e]
  exact ((smul_const_isBigO _ _).trans (coord_isBigO (i := 1) (by decide))).add
    ((smul_const_isBigO _ _).trans (coord_isBigO (i := 0) (by decide)).neg_left)

theorem jw_isBigO : (fun p : Par => jw (α := α) p) =O[𝓝 0] (fun p : Par => nu p ^ 2) :=
  ((PH.orthSub α 2).subtypeL.isBigO_comp _ _).trans jetW_isBigO

theorem dw_isBigO : (fun p : Par => dwCLM (α := α) (jetW p)) =O[𝓝 0] (fun p : Par => nu p ^ 2) :=
  (dwCLM.isBigO_comp _ _).trans jetW_isBigO

theorem u0_isBigO : (fun p : Par => u0CLM (Xp p : Par × Wsp α)) =O[𝓝 0] (fun p : Par => nu p ^ 1) :=
  (u0CLM.isBigO_comp _ _).trans Xp_isBigO


theorem bo_mono {f : Par → PH α 0} {i j : ℕ} (h : j ≤ i) (hf : f =O[𝓝 0] (fun p : Par => nu p ^ i)) :
    f =O[𝓝 0] (fun p : Par => nu p ^ j) := hf.trans (nu_pow_isBigO h)

theorem coef_isBigO (i : Fin 4) (hi : i ≠ 3) (c : ℝ) :
    (fun p : Par => c * p i) =O[𝓝 0] (fun p : Par => nu p ^ 1) :=
  (coord_isBigO hi).const_mul_left c

theorem R3_isBigO : (fun p : Par => R3 (α := α) p) =O[𝓝 0] (fun p : Par => nu p ^ 3) := by
  have hs : (fun _ : Par => (sin3 : PH α 0)) =O[𝓝 0] (fun p : Par => nu p ^ 0) := const_isBigO_pow0 _
  have hA : (fun p : Par => p 3 • u0CLM (Xp p : Par × Wsp α)) =O[𝓝 0] (fun p : Par => nu p ^ 3) :=
    smul_pow gam_isBigO u0_isBigO
  have hc : (fun p : Par => (-(3 * p 2) : ℝ)) =O[𝓝 0] (fun p : Par => nu p ^ 1) :=
    ((coef_isBigO (2 : Fin 4) (by decide) (-3)).congr_left fun p => by ring)
  have hB : (fun p : Par => (-(3 * p 2) : ℝ) • (sin3 * dwCLM (α := α) (jetW p))) =O[𝓝 0]
      (fun p : Par => nu p ^ 3) :=
    smul_pow hc (PH_mul_pow hs dw_isBigO)
  have h1 : (fun p : Par => t1 (α := α) p * dwCLM (jetW p)) =O[𝓝 0] (fun p : Par => nu p ^ 3) :=
    PH_mul_pow t1_isBigO dw_isBigO
  have h2 : (fun p : Par => dwCLM (α := α) (jetW p) * t1 p) =O[𝓝 0] (fun p : Par => nu p ^ 3) :=
    PH_mul_pow dw_isBigO t1_isBigO
  have h3 : (fun p : Par => dwCLM (α := α) (jetW p) * dwCLM (jetW p)) =O[𝓝 0] (fun p : Par => nu p ^ 3) :=
    bo_mono (i := 2 + 2) (by norm_num) (PH_mul_pow dw_isBigO dw_isBigO)
  have hC := ((h1.add h2).add h3).const_smul_left (1 / 2 : ℝ)
  unfold R3
  exact (hA.add hB).add hC

theorem E2_isBigO : (fun p : Par => E2 (α := α) p) =O[𝓝 0] (fun p : Par => nu p ^ 2) := by
  have hs : (fun _ : Par => (sin3 : PH α 0)) =O[𝓝 0] (fun p : Par => nu p ^ 0) := const_isBigO_pow0 _
  have hc : (fun p : Par => (-(3 * p 2) : ℝ)) =O[𝓝 0] (fun p : Par => nu p ^ 1) :=
    ((coef_isBigO (2 : Fin 4) (by decide) (-3)).congr_left fun p => by ring)
  have hB : (fun p : Par => (-(3 * p 2) : ℝ) • (sin3 * t1 (α := α) p)) =O[𝓝 0] (fun p : Par => nu p ^ 2) :=
    bo_mono (i := 1 + (0 + 1)) (by norm_num) (smul_pow hc (PH_mul_pow hs t1_isBigO))
  have hC := (PH_mul_pow (t1_isBigO (α := α)) t1_isBigO).const_smul_left (1 / 2 : ℝ)
  unfold E2
  exact hB.add hC

theorem eul_isBigO : (fun p : Par => eul α (Xp p)) =O[𝓝 0] (fun p : Par => nu p ^ 2) := by
  have hc : (fun p : Par => ((p 0 ^ 2 + p 1 ^ 2) / 4 : ℝ) • (1 : PH α 0)) =O[𝓝 0] (fun p : Par => nu p ^ 2) := by
    refine (smul_const_isBigO _ _).trans (bigO_nu_pow 1 (Eventually.of_forall fun p => ?_))
    have a2 := sq_le_nu p (i := 0) (by decide)
    have a3 := sq_le_nu p (i := 1) (by decide)
    rw [Real.norm_eq_abs, one_mul, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (nu p)]
  have e : (fun p : Par => eul α (Xp p)) = fun p =>
      ((p 0 ^ 2 + p 1 ^ 2) / 4 : ℝ) • (1 : PH α 0) + R3 p := by
    funext p; rw [eul_Xp, jet_cancel]
  rw [e]
  exact hc.add (bo_mono (i := 3) (by norm_num) R3_isBigO)

theorem Du_isBigO : (fun p : Par => DuCLM (Xp p : Par × Wsp α)) =O[𝓝 0] (fun p : Par => nu p ^ 1) := by
  have e : (fun p : Par => DuCLM (Xp p : Par × Wsp α)) = fun p => t1 p + dwCLM (jetW p) := funext DuCLM_Xp
  rw [e]
  exact t1_isBigO.add (bo_mono (i := 2) (by norm_num) dw_isBigO)

theorem rho_isBigO : (fun p : Par => rho α (Xp p)) =O[𝓝 0] (fun p : Par => nu p ^ 0) := by
  have hρ : ContinuousAt (rho α) (0 : Par × Wsp α) := ((contDiff_rho (α := α) 0).continuous).continuousAt
  have hX : Tendsto (fun p : Par => (Xp p : Par × Wsp α)) (𝓝 0) (𝓝 (0 : Par × Wsp α)) := Xp_tendsto
  have : Tendsto (fun p : Par => rho α (Xp p)) (𝓝 0) (𝓝 (rho α (0 : Par × Wsp α))) :=
    hρ.tendsto.comp hX
  simpa using this.isBigO_one ℝ

theorem int_u0_Xp (p : Par) : PH.integral 0 (u0CLM (Xp p : Par × Wsp α)) = 0 := by
  have e : u0CLM (Xp p : Par × Wsp α) = incl2 (α := α) (PH.trig 2 1 (p 0) (p 1) + jw (α := α) p) := by
    simp only [u0CLM, ContinuousLinearMap.comp_apply, uCLM_Xp]
  rw [e, map_add]
  have h1 : PH.integral 0 (incl2 (PH.trig (α := α) 2 1 (p 0) (p 1))) = 0 := by
    rw [PH.integral_apply]; exact integral_trig_const (by omega) _ _
  have h2 : PH.integral 0 (incl2 (jw (α := α) p)) = 0 := by
    have := (jetW (α := α) p).2.1
    rw [PH.integral_apply]
    rw [PH.integral_apply] at this
    exact this
  rw [map_add, h1, h2, add_zero]


theorem kap_isBigO : (fun p : Par => kap α (Xp p)) =O[𝓝 0] (fun p : Par => nu p ^ 2) := by
  have h1 : (fun p : Par => PH.integral 0 (rho α (Xp p) * (DuCLM (Xp p : Par × Wsp α) * DuCLM (Xp p)))) =O[𝓝 0]
      (fun p : Par => nu p ^ 2) := by
    have := (PH.integral (α := α) 0).isBigO_comp (fun p : Par => rho α (Xp p) * (DuCLM (Xp p : Par × Wsp α) * DuCLM (Xp p)))
      (𝓝 0)
    refine this.trans ?_
    exact bo_mono (i := 0 + (1 + 1)) (by norm_num) (PH_mul_pow rho_isBigO (PH_mul_pow Du_isBigO Du_isBigO))
  have hσu : (fun p : Par => (rho α (Xp p) - 1) * u0CLM (Xp p : Par × Wsp α)) =O[𝓝 0] (fun p : Par => nu p ^ 2) :=
    bo_mono (i := 1 + 1) (by norm_num) (PH_mul_pow sigma_isBigO u0_isBigO)
  have h2 : (fun p : Par => PH.integral 0 (rho α (Xp p) * u0CLM (Xp p : Par × Wsp α))) =O[𝓝 0]
      (fun p : Par => nu p ^ 2) := by
    have e : (fun p : Par => PH.integral 0 (rho α (Xp p) * u0CLM (Xp p : Par × Wsp α))) =
        fun p => PH.integral 0 ((rho α (Xp p) - 1) * u0CLM (Xp p : Par × Wsp α)) := by
      funext p
      have : rho α (Xp p) * u0CLM (Xp p : Par × Wsp α) =
          (rho α (Xp p) - 1) * u0CLM (Xp p : Par × Wsp α) + u0CLM (Xp p : Par × Wsp α) := by ring
      rw [this, map_add, int_u0_Xp, add_zero]
    rw [e]
    exact ((PH.integral (α := α) 0).isBigO_comp _ (𝓝 0)).trans hσu
  have hcoef : (fun p : Par => 2 * (1 + p 3)) =O[𝓝 0] (fun p : Par => nu p ^ 0) := by
    have hc : Continuous (fun p : Par => 2 * (1 + p 3)) := by fun_prop
    simpa using (hc.tendsto 0).isBigO_one ℝ
  have h3 : (fun p : Par => 2 * (1 + p 3) * PH.integral 0 (rho α (Xp p) * u0CLM (Xp p : Par × Wsp α))) =O[𝓝 0]
      (fun p : Par => nu p ^ 2) := by
    have := hcoef.mul h2
    simpa only [pow_zero, one_mul] using this
  have e : (fun p : Par => kap α (Xp p)) = fun p =>
      PH.integral 0 (rho α (Xp p) * (DuCLM (Xp p : Par × Wsp α) * DuCLM (Xp p))) -
        2 * (1 + p 3) * PH.integral 0 (rho α (Xp p) * u0CLM (Xp p : Par × Wsp α)) := by
    funext p; rfl
  rw [e]
  exact h1.sub h3

theorem rangeMap_Xp_eq (p : Par) :
    rangeMap α (Xp p) = (-2 : ℝ) • (Qproj (R3 (α := α) p) + Qproj ((rho α (Xp p) - 1) * eul α (Xp p)) +
      (kap α (Xp p) / 2) • Qproj (rho α (Xp p) - 1)) := by
  unfold rangeMap
  congr 1
  have e : rho α (Xp p) * resid α (Xp p) = eul α (Xp p) + (kap α (Xp p) / 2) • (1 : PH α 0) +
      (rho α (Xp p) - 1) * eul α (Xp p) + (kap α (Xp p) / 2) • (rho α (Xp p) - 1) := by
    unfold resid
    simp only [Algebra.smul_def]
    ring
  rw [e, map_add, map_add, map_add, Qproj_eul_Xp, Qproj_const, map_smul, add_zero]

theorem rangeMap_Xp_isBigO :
    (fun p : Par => rangeMap α (Xp p)) =O[𝓝 0] (fun p : Par => nu p ^ 3) := by
  have hQ : ∀ {f : Par → PH α 0} {k : ℕ}, f =O[𝓝 0] (fun p : Par => nu p ^ k) →
      (fun p => Qproj (f p)) =O[𝓝 0] (fun p : Par => nu p ^ k) :=
    fun hf => (Qproj.isBigO_comp _ _).trans hf
  have hs := hQ (sigma_isBigO (α := α))
  have hse : (fun p : Par => Qproj ((rho α (Xp p) - 1) * eul α (Xp p))) =O[𝓝 0] (fun p : Par => nu p ^ 3) :=
    hQ (PH_mul_pow sigma_isBigO eul_isBigO)
  have hk : (fun p : Par => (kap α (Xp p) / 2) • Qproj (rho α (Xp p) - 1)) =O[𝓝 0] (fun p : Par => nu p ^ 3) :=
    smul_pow (((kap_isBigO (α := α)).const_mul_left (1 / 2 : ℝ)).congr_left fun p => by ring) hs
  have hr := hQ R3_isBigO
  have e : (fun p : Par => rangeMap α (Xp p)) = fun p => (-2 : ℝ) • (Qproj (R3 (α := α) p) +
      Qproj ((rho α (Xp p) - 1) * eul α (Xp p)) + (kap α (Xp p) / 2) • Qproj (rho α (Xp p) - 1)) :=
    funext rangeMap_Xp_eq
  rw [e]
  exact ((hr.add hse).add hk).const_smul_left (-2 : ℝ)


theorem jetW_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n (jetW (α := α)) := by
  have e : (jetW (α := α)) = fun p => (jc2 p • tw 2 le_rfl 1 0 + js2 p • tw 2 le_rfl 0 1) +
      (jc4 p • tw 4 (by norm_num) 1 0 + js4 p • tw 4 (by norm_num) 0 1) := by
    funext p
    unfold jetW
    rw [tw_lin 2, tw_lin 4]
  have c0 : ContDiff ℝ n (fun p : Par => p 0) := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).contDiff
  have c1 : ContDiff ℝ n (fun p : Par => p 1) := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1).contDiff
  have c2 : ContDiff ℝ n (fun p : Par => p 2) := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2).contDiff
  have k1 : ContDiff ℝ n (fun p : Par => jc2 p) := by unfold jc2; fun_prop
  have k2 : ContDiff ℝ n (fun p : Par => js2 p) := by unfold js2; fun_prop
  have k3 : ContDiff ℝ n (fun p : Par => jc4 p) := by unfold jc4; fun_prop
  have k4 : ContDiff ℝ n (fun p : Par => js4 p) := by unfold js4; fun_prop
  rw [e]
  exact ((k1.smul contDiff_const).add (k2.smul contDiff_const)).add
    ((k3.smul contDiff_const).add (k4.smul contDiff_const))

theorem jetW_tendsto : Tendsto (fun p : Par => (jetW p : Wsp α)) (𝓝 0) (𝓝 0) := by
  have := (continuous_snd.tendsto (0 : Par × Wsp α)).comp (Xp_tendsto (α := α))
  simpa [Function.comp_def, Xp] using this

theorem branch_bound (ψ : Par → Wsp α) (hc : ContinuousAt ψ 0) (h0 : ψ 0 = 0)
    (hψ : ∀ᶠ p in 𝓝 (0 : Par), rangeMap α (p, ψ p) = 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ q : Par, ‖q‖ < r → ‖ψ q - jetW q‖ ≤ C * nu q ^ 3 := by
  obtain ⟨r, hr, M, hM⟩ := lipschitz_inverse (P := Par) (W := Wsp α) (rangeMap α)
    (contDiff_rangeMap (α := α) 1) rangeMap_isInvertible
  obtain ⟨C, hC⟩ := (rangeMap_Xp_isBigO (α := α)).bound
  have hψt : Tendsto ψ (𝓝 0) (𝓝 0) := by simpa [h0] using hc.tendsto
  have hψs : ∀ᶠ p in 𝓝 (0 : Par), ‖ψ p‖ < r := by
    simpa using hψt.eventually (Metric.ball_mem_nhds (0 : Wsp α) hr)
  have hjs : ∀ᶠ p in 𝓝 (0 : Par), ‖(jetW p : Wsp α)‖ < r := by
    simpa using (jetW_tendsto (α := α)).eventually (Metric.ball_mem_nhds (0 : Wsp α) hr)
  have hp : ∀ᶠ p in 𝓝 (0 : Par), ‖p‖ < r := by
    filter_upwards [Metric.ball_mem_nhds (0 : Par) hr] with p hp
    simpa using hp
  have hev : ∀ᶠ p in 𝓝 (0 : Par), ‖ψ p - jetW p‖ ≤ (|M| * |C|) * nu p ^ 3 := by
    filter_upwards [hψ, hC, hψs, hjs, hp] with p h1 h2 h3 h4 h5
    have h6 := hM p (ψ p) (jetW p) h5 h3 h4
    rw [h1] at h6
    have h7 : rangeMap α (p, jetW p) = rangeMap α (Xp p) := rfl
    rw [h7, zero_sub, norm_neg] at h6
    have hn := nu_nonneg p
    rw [Real.norm_of_nonneg (by positivity)] at h2
    have h8 : C * nu p ^ 3 ≤ |C| * nu p ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have h9 : ‖rangeMap α (Xp p)‖ ≤ |C| * nu p ^ 3 := h2.trans h8
    calc ‖ψ p - jetW p‖ ≤ M * ‖rangeMap α (Xp p)‖ := h6
      _ ≤ |M| * ‖rangeMap α (Xp p)‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      _ ≤ |M| * (|C| * nu p ^ 3) := mul_le_mul_of_nonneg_left h9 (abs_nonneg _)
      _ = _ := by ring
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨ε, hε, |M| * |C|, fun q hq => hball (by simpa using hq)⟩


end Jet2

section Final
variable {α : ℝ} [HolderExponent α]

/-- Second jet of the range solution.  With `p = (a, b, h, γ)` and `t = 2π x`:
`jetW p = [h a/2 + (b²-a²)/12] cos 2t + [-h b/2 - a b/6] sin 2t - (h a/10) cos 4t - (h b/10) sin 4t`,
and every `C³` branch `ψ` of the range equation through `0` differs from it by a remainder
`R = ψ - jetW` with `‖R‖ ≲ ν³`, `∂_{a,b,h} R ≲ ν²`, `∂_γ R ≲ ν`, `∂²_{(a,b,h)} R ≲ ν`
(`ν = |a|+|b|+|h|+√|γ|`, the weighted size). -/
theorem threefold_range_secondJet :
    (∀ p : Par, ((jetW p : Wsp α) : PH α 2) =
      (((p 2 * p 0 / 2 + (p 1 ^ 2 - p 0 ^ 2) / 12) • PH.trig 2 2 1 0 +
        (-(p 2 * p 1) / 2 - p 0 * p 1 / 6) • PH.trig 2 2 0 1) +
       ((-(p 2 * p 0) / 10) • PH.trig 2 4 1 0 + (-(p 2 * p 1) / 10) • PH.trig 2 4 0 1))) ∧
    (∃ ψ : Par → Wsp α, ContDiffAt ℝ 3 ψ 0 ∧ ψ 0 = 0 ∧
      ∀ᶠ p in 𝓝 (0 : Par), rangeMap α (p, ψ p) = 0) ∧
    ∀ ψ : Par → Wsp α, ContDiffAt ℝ 3 ψ 0 → ψ 0 = 0 →
      (∀ᶠ p in 𝓝 (0 : Par), rangeMap α (p, ψ p) = 0) →
      ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ q : Par, ‖q‖ < r →
        ‖ψ q - jetW q‖ ≤ C * nu q ^ 3 ∧
        (∀ v : Par, v 3 = 0 →
          ‖fderiv ℝ (fun x => ψ x - jetW x) q v‖ ≤ C * nu q ^ 2 * ‖v‖) ∧
        ‖fderiv ℝ (fun x => ψ x - jetW x) q (Pi.single 3 1)‖ ≤ C * nu q ∧
        (∀ v v' : Par, v 3 = 0 → v' 3 = 0 →
          ‖fderiv ℝ (fderiv ℝ (fun x => ψ x - jetW x)) q v v'‖ ≤ C * nu q * ‖v‖ * ‖v'‖) := by
  refine ⟨fun p => ?_, ?_, fun ψ hψ h0 hF => ?_⟩
  · rw [jetW_coe]; rfl
  · obtain ⟨-, -, -, -, h⟩ := threefold_range_equation_invertible (α := α)
    obtain ⟨U, hU, h0, Wn, -, -, ψ, h1, h2, -, h4, -⟩ := h 3 (by norm_num)
    refine ⟨ψ, ?_, h1, ?_⟩
    · exact_mod_cast h4.contDiffAt (hU.mem_nhds h0)
    · filter_upwards [hU.mem_nhds h0] with p hp using (h2 p hp).2
  · have hΔ : ContDiffAt ℝ 3 (fun x => ψ x - jetW x) 0 :=
      hψ.sub ((jetW_contDiff (α := α) 3).contDiffAt)
    exact deriv_bounds _ hΔ (branch_bound ψ hψ.continuousAt h0 hF)

end Final

end DGPS.Examples.ThreeSpeciesCircle
