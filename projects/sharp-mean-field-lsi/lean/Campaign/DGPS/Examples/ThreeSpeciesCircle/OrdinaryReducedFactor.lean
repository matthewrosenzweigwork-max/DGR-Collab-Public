import DGPS.Examples.ThreeSpeciesCircle.OrdinaryAllOptimizersGraph

/-!
# Reduced value and Hadamard factorization along the STR026 range graph (packet STR028-b1)

Chart: `u = a cos t + b sin t + w`, `w ∈ Wsp α`, parameters `p = (a, b, h, γ) : Par = Fin 4 → ℝ`,
`r = 1 + γ`. `ψ : Par → Wsp α` is the STR026 branch, `rangeMap α (p, ψ p) = 0`.
The weighted size is `ν(p) = |a| + |b| + |h| + √|γ|` and `R0(p) = √(a² + b²)`.

## Reduced value

`Phi x = kap α x + 2 (1 + γ) (log Z(x) - log Z₀(h))`, with `Z(x) = ∫ e^{φ(x)}` the partition
function of the chart density `rho α x` and `Z₀(h) = ∫ e^{h cos 3t}` the reference partition
function (the same normalisation as in `OrdinaryAllOptimizers*`), and
`Fred ψ p = Phi (p, ψ p)`. This is the entropy-type/quotient functional of campaign §4 evaluated on
the range graph.

## Jet-strength verification (the required preliminary check)

Claim: the second jet of `threefold_range_secondJet` is strong enough.
* The remainder `Rm = ψ - jetW` satisfies `‖Rm‖ ≤ C ν³` and `‖∂_{a,b,h} Rm‖ ≤ C ν²`, and
  `Rm = 0` when `a = b = 0` (the equilibrium branch is `ψ(0,0,h,γ) = 0 = jetW(0,0,h,γ)`).
  Integrating the `ν²` bound for the `(a, b)`-derivative along `s ↦ (s a, s b, h, γ)` gives
  `‖Rm(p)‖ ≤ C R0 ν²` (lemma `Rm_bound_STR028b1`); `ν³` alone would only give `ν³`,
  which is not `O(R0)` when `R0 ≪ |h|`.
* `Phi (p, ψ p) - Phi (Xp p)` is controlled by the envelope identity: `dΦ_x (0, w) = 0` whenever
  `rangeMap x = 0` and `dΦ` is Lipschitz, so by the mean value theorem along
  `t ↦ Phi (p, ψ p + t (jetW p - ψ p))` one gets `|F - Phi (Xp p)| ≤ C ‖Rm‖² ≤ C R0² ν⁴`
  (lemma `transfer_STR028b1`). The first variation in the direction `Rm` vanishes, so no
  linear term in `Rm` appears.
* Weighted comparison: for `‖p‖ ≤ 1/3`,
  `ν⁴ ≤ 128 ((|h| + R0)³ + |γ| (|h| + R0) + γ²)` (lemma `nu4_le_STR028b1`; this is where
  `ν⁴ ~ (|h|+R0)⁴ + γ²` is compared with the target remainder; the `h`-linear piece is
  absorbed since `|h| + R0 ≤ 1`).
Hence `F = Phi (Xp p) + R0² · O((|h|+R0)³ + |γ|(|h|+R0) + γ²)` with the remainder
factor `R0²` kept explicitly. Only the second jet is needed; no third jet. The one point
where a weaker jet would fail: with only `‖Rm‖ ≲ ν³` the error would be `ν⁶ ≥ |γ|³`
without the `R0²` factor, which cannot be divided by `R0²` uniformly.

Expansion of `Phi (Xp p)` (to be proved in STR028-b2):
`-γ R0²/2 - (9/20) h² R0² - h (a³ - 3 a b²)/12 + R0⁴/48 + R0² · O(...)`.

## Outputs (all for every small parameter, not along sequences)

`reducedFactor_STR028b1` gives `r > 0` and `C, M` such that on `‖p‖ < r`:
`F` is `C³`; `F(0,0,h,γ) = 0`; `(0,0,h,γ)` is critical in `(a, b)` (`dF · v = 0` for
`v 2 = v 3 = 0`); the Hadamard form `F = a² Gaa + a b Gab + b² Gbb` with continuous
`Gaa, Gab, Gbb` (`hadamard_STR028b1`, via the Taylor integral
`Gij = ∫₀¹ (1-s) D²F(s a, s b, h, γ)[e_i, e_j] ds`); `F = R0² · Gred` with `Gred = F / R0²`
continuous off `R0 = 0` and bounded by `M` on `‖p‖ ≤ r/2`; `‖ψ - jetW‖ ≤ C R0 ν²`;
`|F - Phi (Xp p)| ≤ C R0² ν⁴`; and `|Gred - Phi (Xp p) / R0²| ≤ C ν⁴` where `R0 ≠ 0`.

## Hypotheses (R5 notes)

* `ψ : Par → Wsp α` with `ContDiffAt ℝ 3 ψ 0`, `ψ 0 = 0`, and `rangeMap α (p, ψ p) = 0`
  eventually near `0` (the STR026 branch); no other assumption.
* Route: self-contained (envelope identity, Taylor-integral Hadamard); consumes
  `threefold_range_secondJet` only through `Rm_bound_STR028b1`/`transfer_STR028b1`.
* `Gab` is the coefficient of `a b` (`Gint e0 e1 + Gint e1 e0`), so no symmetry of `D²F` is used.
* Not proved here: continuity of `Gred` at `R0 = 0` (it needs the `C3`-isotropy of the `(a, b)`
  Hessian; downstream only needs the bounded `Gred` and the `ν⁴` transfer).
-/

open Function Filter Topology Asymptotics MeasureTheory
open scoped ContDiff
open DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic

namespace DGPS.Examples.ThreeSpeciesCircle

section Calc
variable {α : ℝ} [HolderExponent α]

/-- Point evaluation on `C^{0,α}`. -/
noncomputable def evCLM_STR028b1 (s : ℝ) : PH α 0 →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => f.val s
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl } 1 (fun f => by
    rw [one_mul, Real.norm_eq_abs]
    exact (f.isPH.bdd.abs_le_supNorm s).trans (supNorm_le_phNorm (α := α) 0 _))

@[simp] theorem evCLM_STR028b1_apply (s : ℝ) (f : PH α 0) : evCLM_STR028b1 s f = f.val s := rfl

/-- The derivative of `f ↦ e^f` on `C^{0,α}` is multiplication by `e^f`. -/
theorem hasFDerivAt_expMap_STR028b1 (f : PH α 0) :
    HasFDerivAt (PH.expMap (α := α) 0) (mulCLM (PH.expMap 0 f)) f := by
  have hd : DifferentiableAt ℝ (PH.expMap (α := α) 0) f :=
    (PH.contDiff_expMap (α := α) 0 1).differentiable one_ne_zero f
  have hD := hd.hasFDerivAt
  have key : fderiv ℝ (PH.expMap (α := α) 0) f = mulCLM (PH.expMap 0 f) := by
    refine ContinuousLinearMap.ext fun h => PH.ext (funext fun s => ?_)
    have h1 := (evCLM_STR028b1 (α := α) s).hasFDerivAt.comp f hD
    have h2 := ((evCLM_STR028b1 (α := α) s).hasFDerivAt (x := f)).exp
    have e : (evCLM_STR028b1 (α := α) s ∘ PH.expMap 0) =
        fun g : PH α 0 => Real.exp (evCLM_STR028b1 s g) := by
      funext g; simp [PH.expMap_val]
    rw [e] at h1
    have h3 := congrArg (fun L => L h) (h1.unique h2)
    simpa [PH.expMap_val, mul_comm] using h3
  rw [← key]; exact hD

section Chain
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem hasFDerivAt_mulB_STR028b1 {f g : X → PH α 0} {f' g' : X →L[ℝ] PH α 0} {x : X}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun y => f y * g y) ((mulCLM (f x)).comp g' + (mulCLM.comp f').flip (g x)) x := by
  have hc : HasFDerivAt (fun y => (mulCLM (f y) : PH α 0 →L[ℝ] PH α 0)) (mulCLM.comp f') x :=
    mulCLM.hasFDerivAt.comp x hf
  exact hc.clm_apply hg

theorem hasFDerivAt_mulB_apply_STR028b1 (f g : PH α 0) (f' g' : X →L[ℝ] PH α 0) (δ : X) :
    ((mulCLM f).comp g' + (mulCLM.comp f').flip g) δ = f * g' δ + f' δ * g := by
  simp

theorem hasFDerivAt_int_STR028b1 {f : X → PH α 0} {f' : X →L[ℝ] PH α 0} {x : X}
    (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y => PH.integral 0 (f y)) ((PH.integral 0).comp f') x :=
  (PH.integral (α := α) 0).hasFDerivAt.comp x hf

end Chain

section Rho
variable {α : ℝ} [HolderExponent α]

/-- Unnormalized exponential `e^φ`. -/
noncomputable def eV_STR028b1 (x : Par × Wsp α) : PH α 0 := PH.expMap 0 (phiCLM x)

/-- The partition function `Z = ∫ e^φ`. -/
noncomputable def ZV_STR028b1 (x : Par × Wsp α) : ℝ := PH.integral 0 (eV_STR028b1 x)

theorem ZV_pos_STR028b1 (x : Par × Wsp α) : 0 < ZV_STR028b1 x := PH.integral_expMap_pos _

theorem rho_eq_STR028b1 (x : Par × Wsp α) : rho α x = (ZV_STR028b1 x)⁻¹ • eV_STR028b1 x := rfl

theorem hasFDerivAt_eV_STR028b1 (x : Par × Wsp α) :
    HasFDerivAt (eV_STR028b1 (α := α)) ((mulCLM (eV_STR028b1 x)).comp phiCLM) x :=
  (hasFDerivAt_expMap_STR028b1 (phiCLM x)).comp x phiCLM.hasFDerivAt

theorem hasFDerivAt_ZV_STR028b1 (x : Par × Wsp α) :
    HasFDerivAt (ZV_STR028b1 (α := α))
      ((PH.integral 0).comp ((mulCLM (eV_STR028b1 x)).comp phiCLM)) x :=
  hasFDerivAt_int_STR028b1 (hasFDerivAt_eV_STR028b1 x)

theorem hasFDerivAt_rho_STR028b1 (x : Par × Wsp α) :
    ∃ D : Par × Wsp α →L[ℝ] PH α 0, HasFDerivAt (rho α) D x ∧
      ∀ δ, D δ = rho α x * phiCLM δ - (PH.integral 0 (rho α x * phiCLM δ)) • rho α x := by
  have hZ := hasFDerivAt_ZV_STR028b1 x
  have hinv := (hasDerivAt_inv (ZV_pos_STR028b1 x).ne').comp_hasFDerivAt x hZ
  have hs := hinv.smul (hasFDerivAt_eV_STR028b1 x)
  refine ⟨_, hs, fun δ => ?_⟩
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, mulCLM_apply, Function.comp]
  rw [rho_eq_STR028b1]
  simp only [smul_mul_assoc, map_smul, smul_eq_mul]
  have hZ0 : ZV_STR028b1 x ≠ 0 := (ZV_pos_STR028b1 x).ne'
  module
end Rho

section Kap
variable {α : ℝ} [HolderExponent α]

theorem hasFDerivAt_kap_STR028b1 (x : Par × Wsp α) :
    ∃ L : Par × Wsp α →L[ℝ] ℝ, HasFDerivAt (kap α) L x ∧ ∀ δ, L δ =
      PH.integral 0 ((rho α x * phiCLM δ - (PH.integral 0 (rho α x * phiCLM δ)) • rho α x) *
          (DuCLM x * DuCLM x)) +
        2 * PH.integral 0 (rho α x * (DuCLM x * DuCLM δ)) -
        2 * δ.1 3 * PH.integral 0 (rho α x * u0CLM x) -
        2 * (1 + x.1 3) * (PH.integral 0 ((rho α x * phiCLM δ -
          (PH.integral 0 (rho α x * phiCLM δ)) • rho α x) * u0CLM x) +
          PH.integral 0 (rho α x * u0CLM δ)) := by
  obtain ⟨D, hD, hDδ⟩ := hasFDerivAt_rho_STR028b1 x
  have hDu : HasFDerivAt (fun y : Par × Wsp α => DuCLM y) DuCLM x := DuCLM.hasFDerivAt
  have hu0 : HasFDerivAt (fun y : Par × Wsp α => u0CLM y) u0CLM x := u0CLM.hasFDerivAt
  have h1 := hasFDerivAt_int_STR028b1
    (hasFDerivAt_mulB_STR028b1 hD (hasFDerivAt_mulB_STR028b1 hDu hDu))
  have h2 := hasFDerivAt_int_STR028b1 (hasFDerivAt_mulB_STR028b1 hD hu0)
  have h3 : HasFDerivAt (fun y : Par × Wsp α => 2 * (1 + y.1 3))
      ((2 : ℝ) • (pc 3 : Par × Wsp α →L[ℝ] ℝ)) x := by
    have := ((pc (α := α) 3).hasFDerivAt (x := x))
    exact ((hasFDerivAt_const (1:ℝ) x).add this).const_mul 2 |>.congr_fderiv (by simp)
  have h4 := h1.sub (h3.mul h2)
  refine ⟨_, h4, fun δ => ?_⟩
  simp only [sub_apply, ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.flip_apply, mulCLM_apply, smul_apply, pc_apply, smul_eq_mul]
  rw [hDδ]
  have e1 : rho α x * (DuCLM x * DuCLM δ + DuCLM δ * DuCLM x) =
      (2 : ℝ) • (rho α x * (DuCLM x * DuCLM δ)) := by
    rw [mul_comm (DuCLM δ), ← two_smul ℝ (DuCLM x * DuCLM δ), mul_smul_comm]
  rw [e1, map_add, map_smul, map_add, smul_eq_mul]
  ring

/-- Reference partition function `Z₀(h) = ∫ e^{h cos 3t}`. -/
noncomputable def Z0_STR028b1 (h : ℝ) : ℝ := ZV_STR028b1 (((Pi.single 2 h : Par), (0 : Wsp α)))

/-- The value functional `Φ = κ + 2 r (log Z - log Z₀(h))`, `r = 1+γ`. -/
noncomputable def Phi_STR028b1 (x : Par × Wsp α) : ℝ :=
  kap α x + 2 * (1 + x.1 3) * (Real.log (ZV_STR028b1 x) - Real.log (Z0_STR028b1 (α := α) (x.1 2)))

theorem contDiff_eV_STR028b1 (n : WithTop ℕ∞) : ContDiff ℝ n (eV_STR028b1 (α := α)) :=
  (PH.contDiff_expMap 0 n).comp phiCLM.contDiff

theorem contDiff_ZV_STR028b1 (n : WithTop ℕ∞) : ContDiff ℝ n (ZV_STR028b1 (α := α)) :=
  (PH.integral (α := α) 0).contDiff.comp (contDiff_eV_STR028b1 n)

theorem contDiff_Z0_STR028b1 (n : WithTop ℕ∞) : ContDiff ℝ n (Z0_STR028b1 (α := α)) := by
  have hι : ContDiff ℝ n (fun h : ℝ => (((Pi.single 2 h : Par), (0 : Wsp α)) : Par × Wsp α)) := by
    refine ContDiff.prodMk ?_ contDiff_const
    exact (LinearMap.toContinuousLinearMap (LinearMap.single ℝ (fun _ : Fin 4 => ℝ) 2)).contDiff
  exact (contDiff_ZV_STR028b1 n).comp hι

theorem Z0_pos_STR028b1 (h : ℝ) : 0 < Z0_STR028b1 (α := α) h := ZV_pos_STR028b1 _

theorem contDiff_Phi_STR028b1 (n : WithTop ℕ∞) : ContDiff ℝ n (Phi_STR028b1 (α := α)) := by
  unfold Phi_STR028b1
  refine (contDiff_kap n).add ?_
  refine (contDiff_const.mul (contDiff_const.add ((contDiff_apply ℝ ℝ 3).comp contDiff_fst))).mul ?_
  refine ((contDiff_ZV_STR028b1 n).log fun x => (ZV_pos_STR028b1 x).ne').sub ?_
  exact ((contDiff_Z0_STR028b1 n).log fun h => (Z0_pos_STR028b1 h).ne').comp
    ((contDiff_apply ℝ ℝ 2).comp contDiff_fst)

theorem hasFDerivAt_Phi_STR028b1 (x : Par × Wsp α) :
    ∃ L : Par × Wsp α →L[ℝ] ℝ, HasFDerivAt (Phi_STR028b1 (α := α)) L x ∧
      ∀ δ : Par × Wsp α, δ.1 2 = 0 → δ.1 3 = 0 → L δ =
        PH.integral 0 ((rho α x * u0CLM δ) * (DuCLM x * DuCLM x - (2 * (1 + x.1 3)) • u0CLM x -
          kap α x • (1 : PH α 0))) + 2 * PH.integral 0 (rho α x * (DuCLM x * DuCLM δ)) := by
  obtain ⟨Lk, hLk, hLkδ⟩ := hasFDerivAt_kap_STR028b1 x
  have hZ := hasFDerivAt_ZV_STR028b1 x
  have hlog := hZ.log (ZV_pos_STR028b1 x).ne'
  have hz0 : DifferentiableAt ℝ (fun h => Real.log (Z0_STR028b1 (α := α) h)) (x.1 2) :=
    (((contDiff_Z0_STR028b1 (α := α) 1).log fun h => (Z0_pos_STR028b1 h).ne').differentiable
      one_ne_zero) _
  have hlog0 := hz0.hasFDerivAt.comp x (pc (α := α) 2).hasFDerivAt
  have h3 : HasFDerivAt (fun y : Par × Wsp α => 2 * (1 + y.1 3))
      ((2 : ℝ) • (pc 3 : Par × Wsp α →L[ℝ] ℝ)) x := by
    have := ((pc (α := α) 3).hasFDerivAt (x := x))
    exact ((hasFDerivAt_const (1:ℝ) x).add this).const_mul 2 |>.congr_fderiv (by simp)
  have h5 := hLk.add (h3.mul (hlog.sub hlog0))
  refine ⟨_, h5, fun δ h2 h3' => ?_⟩
  simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply, smul_apply, pc_apply,
    hLkδ, smul_eq_mul]
  have hφ : phiCLM δ = u0CLM δ := by simp [phiCLM, pc_apply, h2]
  have hI : (ZV_STR028b1 x)⁻¹ * PH.integral 0 (mulCLM (eV_STR028b1 x) (u0CLM δ)) =
      PH.integral 0 (rho α x * u0CLM δ) := by
    rw [rho_eq_STR028b1, smul_mul_assoc, map_smul, smul_eq_mul, mulCLM_apply]
  have hk : kap α x = PH.integral 0 (rho α x * (DuCLM x * DuCLM x)) -
      2 * (1 + x.1 3) * PH.integral 0 (rho α x * u0CLM x) := rfl
  rw [hφ, h2, h3', map_zero]
  rw [hI]
  simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, map_sub, map_smul, mul_one,
    smul_eq_mul]
  rw [hk]
  ring

/-- The integrand whose integral vanishes (integration by parts). -/
noncomputable def Yv_STR028b1 (x δ : Par × Wsp α) : PH α 0 :=
  (rho α x * u0CLM δ) * (DuCLM x * DuCLM x - (2 * (1 + x.1 3)) • u0CLM x -
      kap α x • (1 : PH α 0)) + (2 : ℝ) • (rho α x * (DuCLM x * DuCLM δ)) +
    (2 : ℝ) • (rho α x * resid α x * u0CLM δ)

theorem ibp_STR028b1 (x δ : Par × Wsp α) : PH.integral 0 (Yv_STR028b1 x δ) = 0 := by
  have hpu : IsPH α 2 (uCLM x).val := (uCLM x).isPH
  have hpv : IsPH α 2 (uCLM δ).val := (uCLM δ).isPH
  set u := (uCLM x).val with hu
  set v := (uCLM δ).val with hv
  have hu1 : ∀ s, HasDerivAt u (deriv u s) s := fun s => (hpu.2.1 s).hasDerivAt
  have hu2 : ∀ s, HasDerivAt (deriv u) (deriv (deriv u) s) s :=
    fun s => (hpu.2.2.2.1 s).hasDerivAt
  have hv1 : ∀ s, HasDerivAt v (deriv v s) s := fun s => (hpv.2.1 s).hasDerivAt
  have hcρ : Continuous (rho α x).val := (rho α x).isPH.continuous
  have hρd : ∀ s, HasDerivAt (rho α x).val
      ((rho α x).val s * (sg0 (x.1 2) s + deriv u s)) s := by
    intro s
    have h1 : HasDerivAt (fun y => ellF (x.1 2) 0 y + u y) (sg0 (x.1 2) s + deriv u s) s :=
      (hasDerivAt_ellF (x.1 2) 0 s).add (hu1 s)
    have h2 := (h1.exp).const_mul (∫ y in (0 : ℝ)..1, Real.exp ((phiCLM x).val y))⁻¹
    have e : (rho α x).val = fun y => (∫ y in (0 : ℝ)..1, Real.exp ((phiCLM x).val y))⁻¹ *
        Real.exp (ellF (x.1 2) 0 y + u y) := by
      funext y; rw [sgv_rho, sgv_phi]; simp [ellF, hu]
    rw [e]
    refine h2.congr_deriv ?_
    rw [← e]
    rw [sgv_rho, sgv_phi]
    simp [ellF, hu]
    ring
  set E : ℝ → ℝ := fun s => (rho α x).val s * deriv u s * v s with hE
  set E' : ℝ → ℝ := fun s => (rho α x).val s * (sg0 (x.1 2) s + deriv u s) * deriv u s * v s +
    (rho α x).val s * deriv (deriv u) s * v s + (rho α x).val s * deriv u s * deriv v s with hE'
  have hEd : ∀ s, HasDerivAt E (E' s) s := fun s =>
    ((((hρd s).mul (hu2 s)).mul (hv1 s)).congr_deriv (by simp only [hE', Pi.mul_apply]; ring))
  have hcu1 : Continuous (deriv u) := hpu.2.2.continuous
  have hcu2 : Continuous (deriv (deriv u)) := (isPH_deriv_deriv hpu).continuous
  have hcv1 : Continuous (deriv v) := hpv.2.2.continuous
  have hcv : Continuous v := hpv.continuous
  have hσc : Continuous (sg0 (x.1 2)) := by unfold sg0; fun_prop
  have hcE' : Continuous E' := by
    simp only [hE']
    exact ((((hcρ.mul (hσc.add hcu1)).mul hcu1).mul hcv).add ((hcρ.mul hcu2).mul hcv)).add
      ((hcρ.mul hcu1).mul hcv1)
  have hper : E 1 = E 0 := by
    have h1 := (rho α x).isPH.periodic 0
    have h2 := hpu.2.2.1 0
    have h3 := hpv.periodic 0
    simp only [zero_add] at h1 h2 h3
    simp only [hE, h1, h2, h3]
  have hI0 : ∫ s in (0 : ℝ)..1, E' s = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hEd s)
      (hcE'.intervalIntegrable _ _), hper, sub_self]
  have hpt : ∀ s, (Yv_STR028b1 x δ).val s = 2 * kappa⁻¹ * E' s := by
    intro s
    simp only [Yv_STR028b1, resid, PH.val_add, PH.val_sub, PH.val_smul, PH.val_mul, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, sgv_Du, sgv_eul, sgv_u0, hE', PH.val_one, Pi.one_apply]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    simp only [kappa]
    field_simp
    ring
  rw [PH.integral_apply]
  have : ∀ s ∈ Set.uIcc (0:ℝ) 1, (Yv_STR028b1 x δ).val s = 2 * kappa⁻¹ * E' s := fun s _ => hpt s
  rw [intervalIntegral.integral_congr this, intervalIntegral.integral_const_mul, hI0, mul_zero]

/-- First variation of `Φ` in the directions fixing `h, γ`: `dΦ δ = -2 ∫ ρ (E + κ/2) uδ`. -/
theorem hasFDerivAt_Phi_resid_STR028b1 (x : Par × Wsp α) :
    ∃ L : Par × Wsp α →L[ℝ] ℝ, HasFDerivAt (Phi_STR028b1 (α := α)) L x ∧
      ∀ δ : Par × Wsp α, δ.1 2 = 0 → δ.1 3 = 0 →
        L δ = -2 * PH.integral 0 (rho α x * resid α x * u0CLM δ) := by
  obtain ⟨L, hL, hLδ⟩ := hasFDerivAt_Phi_STR028b1 x
  refine ⟨L, hL, fun δ h2 h3 => ?_⟩
  have h0 := ibp_STR028b1 x δ
  simp only [Yv_STR028b1, map_add, map_smul, smul_eq_mul] at h0
  rw [hLδ δ h2 h3]
  linarith

theorem uCLM_ab_zero_STR028b1 (p : Par) (h0 : p 0 = 0) (h1 : p 1 = 0) :
    uCLM ((p, (0 : Wsp α)) : Par × Wsp α) = 0 := by
  simp [uCLM, pc_apply, h0, h1]

theorem rangeMap_ab_zero_STR028b1 (p : Par) (h0 : p 0 = 0) (h1 : p 1 = 0) :
    resid α ((p, (0 : Wsp α)) : Par × Wsp α) = 0 ∧ rangeMap α ((p, (0 : Wsp α)) : Par × Wsp α) = 0 := by
  have hu : uCLM ((p, (0 : Wsp α)) : Par × Wsp α) = 0 := uCLM_ab_zero_STR028b1 p h0 h1
  have hu0 : u0CLM ((p, (0 : Wsp α)) : Par × Wsp α) = 0 := by simp [u0CLM, hu]
  have hDu : DuCLM ((p, (0 : Wsp α)) : Par × Wsp α) = 0 := by simp [DuCLM, hu]
  have hD2 : D2uCLM ((p, (0 : Wsp α)) : Par × Wsp α) = 0 := by simp [D2uCLM, hu]
  have he : eul α ((p, (0 : Wsp α)) : Par × Wsp α) = 0 := by
    simp [eul, hu0, hDu, hD2]
  have hk : kap α ((p, (0 : Wsp α)) : Par × Wsp α) = 0 := by
    simp [kap, hu0, hDu]
  have hr : resid α ((p, (0 : Wsp α)) : Par × Wsp α) = 0 := by
    simp [resid, he, hk]
  refine ⟨hr, ?_⟩
  simp [rangeMap, hr]

theorem Phi_ab_zero_STR028b1 (p : Par) (h0 : p 0 = 0) (h1 : p 1 = 0) :
    Phi_STR028b1 ((p, (0 : Wsp α)) : Par × Wsp α) = 0 := by
  have hu : uCLM ((p, (0 : Wsp α)) : Par × Wsp α) = 0 := uCLM_ab_zero_STR028b1 p h0 h1
  have hu0 : u0CLM ((p, (0 : Wsp α)) : Par × Wsp α) = 0 := by simp [u0CLM, hu]
  have hDu : DuCLM ((p, (0 : Wsp α)) : Par × Wsp α) = 0 := by simp [DuCLM, hu]
  have hk : kap α ((p, (0 : Wsp α)) : Par × Wsp α) = 0 := by
    simp [kap, hu0, hDu]
  have hphi : phiCLM ((p, (0 : Wsp α)) : Par × Wsp α) =
      phiCLM (((Pi.single 2 (p 2) : Par), (0 : Wsp α)) : Par × Wsp α) := by
    simp [phiCLM, pc_apply, u0CLM, uCLM, h0, h1]
  have hZ : ZV_STR028b1 ((p, (0 : Wsp α)) : Par × Wsp α) = Z0_STR028b1 (α := α) (p 2) := by
    unfold ZV_STR028b1 eV_STR028b1 Z0_STR028b1
    rw [hphi]
    rfl
  unfold Phi_STR028b1
  rw [hk, hZ]
  simp

theorem orth_STR028b1 (g : PH α 0) (hg : Qproj g = 0) (w : Wsp α) :
    PH.integral 0 (g * incl2 (w : PH α 2)) = 0 := by
  have hq : g - PH.modeProj 0 {0, 1} g = 0 := by
    rw [← Qproj_val, hg]; rfl
  have hgv : ∀ x, g.val x = PH.integral 0 g + 2 * PH.cosCoeff 0 1 g * Real.cos (2 * Real.pi * x) +
      2 * PH.sinCoeff 0 1 g * Real.sin (2 * Real.pi * x) := by
    intro x
    have h1 : g = PH.modeProj 0 {0, 1} g := sub_eq_zero.1 hq
    conv_lhs => rw [h1]
    rw [PH.modeProj01_val]
  have hw : (w : PH α 2) ∈ PH.orthSub α 2 := w.2
  obtain ⟨w0, w1, w2⟩ := hw
  rw [PH.integral_apply] at w0
  rw [PH.cosCoeff_apply] at w1
  rw [PH.sinCoeff_apply] at w2
  have hcw : Continuous (w : PH α 2).val := (w : PH α 2).isPH.continuous
  have hc1 : Continuous fun x : ℝ => (w : PH α 2).val x * Real.cos (2 * Real.pi * (1 : ℕ) * x) := by
    fun_prop
  have hc2 : Continuous fun x : ℝ => (w : PH α 2).val x * Real.sin (2 * Real.pi * (1 : ℕ) * x) := by
    fun_prop
  rw [PH.integral_apply]
  have e : ∀ x, (g * incl2 (w : PH α 2)).val x = PH.integral 0 g * (w : PH α 2).val x +
      (2 * PH.cosCoeff 0 1 g) * ((w : PH α 2).val x * Real.cos (2 * Real.pi * (1 : ℕ) * x)) +
      (2 * PH.sinCoeff 0 1 g) * ((w : PH α 2).val x * Real.sin (2 * Real.pi * (1 : ℕ) * x)) := by
    intro x
    simp only [PH.val_mul, Pi.mul_apply, incl2_val, hgv x, Nat.cast_one, mul_one]
    ring
  simp_rw [e]
  rw [int_comb3 hcw hc1 hc2, w0, w1, w2]
  ring

/-- On the range graph the `w`-gradient of `Φ` vanishes (envelope). -/
theorem fderiv_Phi_w_zero_STR028b1 (x : Par × Wsp α) (hx : rangeMap α x = 0) (w : Wsp α) :
    fderiv ℝ (Phi_STR028b1 (α := α)) x (((0 : Par), w) : Par × Wsp α) = 0 := by
  obtain ⟨L, hL, hLδ⟩ := hasFDerivAt_Phi_resid_STR028b1 x
  rw [hL.fderiv, hLδ _ (by simp) (by simp)]
  have hQ : Qproj (rho α x * resid α x) = 0 := by
    have h : (-2 : ℝ) • Qproj (rho α x * resid α x) = 0 := hx
    rcases smul_eq_zero.1 h with h | h
    · norm_num at h
    · exact h
  have hu : u0CLM (((0 : Par), w) : Par × Wsp α) = incl2 (w : PH α 2) := by
    simp [u0CLM, uCLM, pc_apply]
  rw [hu, orth_STR028b1 _ hQ w]
  simp

/-- Local regularity of a `C³` branch of the range equation. -/
theorem branch_STR028b1 (ψ : Par → Wsp α) (hψ : ContDiffAt ℝ 3 ψ 0) (h0 : ψ 0 = 0)
    (hF : ∀ᶠ p in 𝓝 (0 : Par), rangeMap α (p, ψ p) = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ p : Par, ‖p‖ < r →
      ContDiffAt ℝ 3 ψ p ∧ rangeMap α (p, ψ p) = 0 ∧ (p 0 = 0 → p 1 = 0 → ψ p = 0) := by
  obtain ⟨r1, hr1, M, hM⟩ := lipschitz_inverse (P := Par) (W := Wsp α) (rangeMap α)
    (contDiff_rangeMap (α := α) 1) rangeMap_isInvertible
  have hψt : Tendsto ψ (𝓝 0) (𝓝 0) := by simpa [h0] using hψ.continuousAt.tendsto
  have hψs : ∀ᶠ p in 𝓝 (0 : Par), ‖ψ p‖ < r1 := by
    simpa using hψt.eventually (Metric.ball_mem_nhds (0 : Wsp α) hr1)
  have hp : ∀ᶠ p in 𝓝 (0 : Par), ‖p‖ < r1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : Par) hr1] with p hp
    simpa using hp
  have hev : ∀ᶠ p in 𝓝 (0 : Par), ContDiffAt ℝ 3 ψ p ∧ rangeMap α (p, ψ p) = 0 ∧
      ‖ψ p‖ < r1 ∧ ‖p‖ < r1 := by
    filter_upwards [hψ.eventually (by simp), hF, hψs, hp] with p h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨r, hr, fun p hp => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hball (by simpa using hp)
  refine ⟨h1, h2, fun ha hb => ?_⟩
  have h5 := hM p (ψ p) 0 h4 h3 (by simpa using hr1)
  rw [h2, (rangeMap_ab_zero_STR028b1 p ha hb).2, sub_zero, sub_zero, norm_zero, mul_zero] at h5
  exact norm_le_zero_iff.1 h5


/-- The reduced value `F(p) = Φ(p, ψ p)` of the entropy-type functional along the range graph. -/
noncomputable def Fred_STR028b1 (ψ : Par → Wsp α) (p : Par) : ℝ :=
  Phi_STR028b1 ((p, ψ p) : Par × Wsp α)

theorem contDiffAt_Fred_STR028b1 (ψ : Par → Wsp α) {p : Par} (h : ContDiffAt ℝ 3 ψ p) :
    ContDiffAt ℝ 3 (Fred_STR028b1 ψ) p :=
  ((contDiff_Phi_STR028b1 (α := α) 3).contDiffAt).comp p (contDiffAt_id.prodMk h)

theorem Fred_zero_STR028b1 (ψ : Par → Wsp α) (p : Par) (hz : ψ p = 0) (h0 : p 0 = 0)
    (h1 : p 1 = 0) : Fred_STR028b1 ψ p = 0 := by
  unfold Fred_STR028b1
  rw [hz]
  exact Phi_ab_zero_STR028b1 p h0 h1

theorem fderiv_Fred_ab_STR028b1 (ψ : Par → Wsp α) (p : Par) (hψp : DifferentiableAt ℝ ψ p)
    (hz : ψ p = 0) (h0 : p 0 = 0) (h1 : p 1 = 0) (v : Par) (hv2 : v 2 = 0) (hv3 : v 3 = 0) :
    fderiv ℝ (Fred_STR028b1 ψ) p v = 0 := by
  obtain ⟨L, hL, hLδ⟩ := hasFDerivAt_Phi_resid_STR028b1 ((p, ψ p) : Par × Wsp α)
  have hg : HasFDerivAt (fun q : Par => ((q, ψ q) : Par × Wsp α))
      ((ContinuousLinearMap.id ℝ Par).prod (fderiv ℝ ψ p)) p :=
    (hasFDerivAt_id p).prodMk hψp.hasFDerivAt
  have hc : HasFDerivAt (Fred_STR028b1 ψ)
      (L.comp ((ContinuousLinearMap.id ℝ Par).prod (fderiv ℝ ψ p))) p := hL.comp p hg
  rw [hc.fderiv]
  have hr : resid α ((p, ψ p) : Par × Wsp α) = 0 := by
    rw [hz]; exact (rangeMap_ab_zero_STR028b1 p h0 h1).1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply]
  rw [hLδ _ hv2 hv3, hr]
  simp


section Hadamard

/-- The point `(s a, s b, h, γ)` on the segment from `(0,0,h,γ)` to `p`. -/
def pt_STR028b1 (p : Par) (s : ℝ) : Par := ![s * p 0, s * p 1, p 2, p 3]

/-- Clamp to `[0,1]`. -/
noncomputable def cl_STR028b1 (s : ℝ) : ℝ := max 0 (min s 1)

theorem cl_cont_STR028b1 : Continuous cl_STR028b1 :=
  continuous_const.max (continuous_id.min continuous_const)

theorem cl_eq_STR028b1 {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : cl_STR028b1 s = s := by
  unfold cl_STR028b1
  rw [min_eq_left h1, max_eq_right h0]

theorem cl_nonneg_STR028b1 (s : ℝ) : 0 ≤ cl_STR028b1 s := le_max_left _ _

theorem cl_le_one_STR028b1 (s : ℝ) : cl_STR028b1 s ≤ 1 :=
  max_le zero_le_one (min_le_right _ _)

theorem continuous_pt_STR028b1 : Continuous (fun x : Par × ℝ => pt_STR028b1 x.1 x.2) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [pt_STR028b1] <;> fun_prop

theorem pt_norm_le_STR028b1 (p : Par) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ‖pt_STR028b1 p s‖ ≤ ‖p‖ := by
  have hi : ∀ i, ‖p i‖ ≤ ‖p‖ := norm_le_pi_norm p
  have hs : ∀ i, ‖s * p i‖ ≤ ‖p‖ := fun i => by
    rw [norm_mul, Real.norm_of_nonneg h0]
    calc s * ‖p i‖ ≤ 1 * ‖p i‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ ‖p‖ := by rw [one_mul]; exact hi i
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  fin_cases i <;> simp [pt_STR028b1]
  · simpa [abs_mul] using hs 0
  · simpa [abs_mul] using hs 1
  · exact hi 2
  · exact hi 3

theorem hasDerivAt_pt_STR028b1 (p : Par) (s : ℝ) :
    HasDerivAt (pt_STR028b1 p) (![p 0, p 1, 0, 0] : Par) s := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [pt_STR028b1] using (hasDerivAt_id s).mul_const (p 0)
  · simpa [pt_STR028b1] using (hasDerivAt_id s).mul_const (p 1)
  · simpa [pt_STR028b1] using hasDerivAt_const s (p 2)
  · simpa [pt_STR028b1] using hasDerivAt_const s (p 3)

theorem pt_zero_STR028b1 (p : Par) : (pt_STR028b1 p 0) 0 = 0 ∧ (pt_STR028b1 p 0) 1 = 0 := by
  simp [pt_STR028b1]

theorem pt_one_STR028b1 (p : Par) : pt_STR028b1 p 1 = p := by
  ext i
  fin_cases i <;> simp [pt_STR028b1]


/-- Clamped Taylor-integrand `(1-s) D²F(pt p s)[u,v]`. -/
noncomputable def Kc_STR028b1 (F : Par → ℝ) (u v p : Par) (s : ℝ) : ℝ :=
  (1 - cl_STR028b1 s) * fderiv ℝ (fderiv ℝ F) (pt_STR028b1 p (cl_STR028b1 s)) u v

noncomputable def Gint_STR028b1 (F : Par → ℝ) (u v p : Par) : ℝ :=
  ∫ s in (0 : ℝ)..1, Kc_STR028b1 F u v p s

theorem contOn_D2_STR028b1 (F : Par → ℝ) (r : ℝ) (hF : ∀ p : Par, ‖p‖ < r → ContDiffAt ℝ 2 F p) :
    ContinuousOn (fderiv ℝ (fderiv ℝ F)) (Metric.ball (0 : Par) r) := by
  have hF2 : ContDiffOn ℝ 2 F (Metric.ball (0 : Par) r) := fun p hp =>
    (hF p (by simpa using hp)).contDiffWithinAt
  have h1 := hF2.fderiv_of_isOpen Metric.isOpen_ball (m := 1) (by norm_num)
  exact h1.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl

theorem continuous_Kc_STR028b1 (F : Par → ℝ) (r : ℝ)
    (hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ F)) (Metric.ball (0 : Par) r)) (u v : Par) :
    Continuous (fun x : (Metric.ball (0 : Par) r) × ℝ => Kc_STR028b1 F u v x.1.1 x.2) := by
  unfold Kc_STR028b1
  refine (continuous_const.sub (cl_cont_STR028b1.comp continuous_snd)).mul ?_
  have hpt : Continuous (fun x : (Metric.ball (0 : Par) r) × ℝ =>
      pt_STR028b1 x.1.1 (cl_STR028b1 x.2)) :=
    continuous_pt_STR028b1.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk (cl_cont_STR028b1.comp continuous_snd))
  have hmem : ∀ x : (Metric.ball (0 : Par) r) × ℝ,
      pt_STR028b1 x.1.1 (cl_STR028b1 x.2) ∈ Metric.ball (0 : Par) r := by
    intro x
    have h1 := x.1.2
    rw [mem_ball_zero_iff] at h1 ⊢
    exact lt_of_le_of_lt (pt_norm_le_STR028b1 _ (cl_nonneg_STR028b1 _) (cl_le_one_STR028b1 _)) h1
  exact ((hD2.comp_continuous hpt hmem).clm_apply continuous_const).clm_apply continuous_const

theorem continuousOn_Gint_STR028b1 (F : Par → ℝ) (r : ℝ)
    (hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ F)) (Metric.ball (0 : Par) r)) (u v : Par) :
    ContinuousOn (Gint_STR028b1 F u v) (Metric.ball (0 : Par) r) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (x : Metric.ball (0 : Par) r) (s : ℝ) => Kc_STR028b1 F u v x.1 s)
    (continuous_Kc_STR028b1 F r hD2 u v) 0 1

theorem continuous_Kc_s_STR028b1 (F : Par → ℝ) (r : ℝ)
    (hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ F)) (Metric.ball (0 : Par) r)) (u v p : Par)
    (hp : ‖p‖ < r) : Continuous (Kc_STR028b1 F u v p) := by
  have h := (continuous_Kc_STR028b1 F r hD2 u v).comp
    (continuous_const (y := (⟨p, by simpa using hp⟩ : Metric.ball (0 : Par) r)) |>.prodMk
      continuous_id)
  exact h


theorem taylor_STR028b1 (F : Par → ℝ) (r : ℝ) (hF : ∀ p : Par, ‖p‖ < r → ContDiffAt ℝ 2 F p)
    (p : Par) (hp : ‖p‖ < r) :
    F p - F (pt_STR028b1 p 0) - fderiv ℝ F (pt_STR028b1 p 0) (![p 0, p 1, 0, 0] : Par) =
      ∫ s in (0 : ℝ)..1, (1 - s) *
        fderiv ℝ (fderiv ℝ F) (pt_STR028b1 p s) (![p 0, p 1, 0, 0] : Par) (![p 0, p 1, 0, 0] : Par) := by
  set d : Par := ![p 0, p 1, 0, 0] with hd
  have hD2 := contOn_D2_STR028b1 F r hF
  have hmem : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖pt_STR028b1 p s‖ < r := fun s hs =>
    lt_of_le_of_lt (pt_norm_le_STR028b1 p hs.1 hs.2) hp
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
      (fun s => (1 - s) * fderiv ℝ F (pt_STR028b1 p s) d + F (pt_STR028b1 p s))
      ((1 - s) * fderiv ℝ (fderiv ℝ F) (pt_STR028b1 p s) d d) s := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    have hq := hF _ (hmem s hs)
    have h1 : HasDerivAt (fun s => F (pt_STR028b1 p s)) (fderiv ℝ F (pt_STR028b1 p s) d) s :=
      (hq.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_pt_STR028b1 p s)
    have hfd : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (pt_STR028b1 p s))
        (pt_STR028b1 p s) :=
      ((hq.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
    have h2 : HasDerivAt (fun s => fderiv ℝ F (pt_STR028b1 p s))
        (fderiv ℝ (fderiv ℝ F) (pt_STR028b1 p s) d) s :=
      hfd.comp_hasDerivAt s (hasDerivAt_pt_STR028b1 p s)
    have h3 : HasDerivAt (fun s => fderiv ℝ F (pt_STR028b1 p s) d)
        (fderiv ℝ (fderiv ℝ F) (pt_STR028b1 p s) d d) s := by
      have := h2.clm_apply (hasDerivAt_const s d)
      simpa using this
    have h4 := (((hasDerivAt_id s).const_sub 1).mul h3).add h1
    refine h4.congr_deriv ?_
    simp only [id]
    ring
  have hint : IntervalIntegrable (fun s => (1 - s) *
      fderiv ℝ (fderiv ℝ F) (pt_STR028b1 p s) d d) MeasureTheory.volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    refine (continuousOn_const.sub continuousOn_id).mul ?_
    have hpc : ContinuousOn (fun s => pt_STR028b1 p s) (Set.Icc (0 : ℝ) 1) :=
      (continuous_pt_STR028b1.comp (continuous_const.prodMk continuous_id)).continuousOn
    have := hD2.comp hpc (fun s hs => by simpa using hmem s hs)
    exact (this.clm_apply continuousOn_const).clm_apply continuousOn_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [pt_one_STR028b1]
  simp only [sub_self, zero_mul, one_mul, sub_zero]
  ring


/-- Hadamard factorisation in the first two variables: a `C²` function vanishing together with its
`(a,b)`-derivative on `a = b = 0` is a quadratic form in `(a,b)` with continuous coefficients. -/
theorem hadamard_STR028b1 (F : Par → ℝ) (r : ℝ)
    (hF : ∀ p : Par, ‖p‖ < r → ContDiffAt ℝ 2 F p)
    (hF0 : ∀ p : Par, ‖p‖ < r → p 0 = 0 → p 1 = 0 → F p = 0)
    (hcrit : ∀ p : Par, ‖p‖ < r → p 0 = 0 → p 1 = 0 → ∀ v : Par, v 2 = 0 → v 3 = 0 →
      fderiv ℝ F p v = 0) :
    ∃ Gaa Gab Gbb : Par → ℝ, ContinuousOn Gaa (Metric.ball (0 : Par) r) ∧
      ContinuousOn Gab (Metric.ball (0 : Par) r) ∧ ContinuousOn Gbb (Metric.ball (0 : Par) r) ∧
      ∀ p : Par, ‖p‖ < r →
        F p = p 0 ^ 2 * Gaa p + p 0 * p 1 * Gab p + p 1 ^ 2 * Gbb p := by
  have hD2 := contOn_D2_STR028b1 F r hF
  set e0 : Par := ![1, 0, 0, 0] with he0
  set e1 : Par := ![0, 1, 0, 0] with he1
  refine ⟨Gint_STR028b1 F e0 e0, fun p => Gint_STR028b1 F e0 e1 p + Gint_STR028b1 F e1 e0 p,
    Gint_STR028b1 F e1 e1, continuousOn_Gint_STR028b1 F r hD2 _ _,
    (continuousOn_Gint_STR028b1 F r hD2 _ _).add (continuousOn_Gint_STR028b1 F r hD2 _ _),
    continuousOn_Gint_STR028b1 F r hD2 _ _, fun p hp => ?_⟩
  have hT := taylor_STR028b1 F r hF p hp
  have hz := hF0 _ (lt_of_le_of_lt (pt_norm_le_STR028b1 p le_rfl zero_le_one) hp)
    (pt_zero_STR028b1 p).1 (pt_zero_STR028b1 p).2
  have hc := hcrit _ (lt_of_le_of_lt (pt_norm_le_STR028b1 p le_rfl zero_le_one) hp)
    (pt_zero_STR028b1 p).1 (pt_zero_STR028b1 p).2 (![p 0, p 1, 0, 0] : Par) (by simp) (by simp)
  rw [hz, hc, sub_zero, sub_zero] at hT
  set d : Par := ![p 0, p 1, 0, 0] with hd
  have hdd : d = p 0 • e0 + p 1 • e1 := by
    ext i
    fin_cases i <;> simp [hd, he0, he1]
  have hi : ∀ u v : Par, IntervalIntegrable (Kc_STR028b1 F u v p) MeasureTheory.volume 0 1 :=
    fun u v => (continuous_Kc_s_STR028b1 F r hD2 u v p hp).intervalIntegrable 0 1
  have hcl : ∫ s in (0 : ℝ)..1, (1 - s) *
      fderiv ℝ (fderiv ℝ F) (pt_STR028b1 p s) d d =
      ∫ s in (0 : ℝ)..1, Kc_STR028b1 F d d p s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le zero_le_one] at hs
    simp only [Kc_STR028b1, cl_eq_STR028b1 hs.1 hs.2]
  have hexp : ∀ s, Kc_STR028b1 F d d p s = p 0 ^ 2 * Kc_STR028b1 F e0 e0 p s +
      p 0 * p 1 * (Kc_STR028b1 F e0 e1 p s + Kc_STR028b1 F e1 e0 p s) +
      p 1 ^ 2 * Kc_STR028b1 F e1 e1 p s := by
    intro s
    simp only [Kc_STR028b1, hdd, map_add, map_smul, add_apply,
      smul_apply, smul_eq_mul]
    ring
  rw [hT, hcl]
  simp_rw [hexp]
  unfold Gint_STR028b1
  rw [intervalIntegral.integral_add ((hi _ _).const_mul _ |>.add ((hi _ _ |>.add (hi _ _)).const_mul _))
      ((hi _ _).const_mul _),
    intervalIntegral.integral_add ((hi _ _).const_mul _) (((hi _ _).add (hi _ _)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hi _ _) (hi _ _)]


/-- The radial size `R0 = √(a² + b²)`. -/
noncomputable def R0_STR028b1 (p : Par) : ℝ := Real.sqrt (p 0 ^ 2 + p 1 ^ 2)

theorem R0_nonneg_STR028b1 (p : Par) : 0 ≤ R0_STR028b1 p := Real.sqrt_nonneg _

theorem norm_d_le_STR028b1 (p : Par) : ‖(![p 0, p 1, 0, 0] : Par)‖ ≤ R0_STR028b1 p := by
  refine (pi_norm_le_iff_of_nonneg (R0_nonneg_STR028b1 p)).2 fun i => ?_
  have h0 : |p 0| ≤ R0_STR028b1 p := Real.abs_le_sqrt (by nlinarith [sq_nonneg (p 1)])
  have h1 : |p 1| ≤ R0_STR028b1 p := Real.abs_le_sqrt (by nlinarith [sq_nonneg (p 0)])
  have h2 := R0_nonneg_STR028b1 p
  fin_cases i <;> simp <;> assumption

theorem nu_pt_le_STR028b1 (p : Par) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    nu (pt_STR028b1 p s) ≤ nu p := by
  unfold nu
  have hs : |s| = s := abs_of_nonneg h0
  simp [pt_STR028b1, abs_mul, hs]
  nlinarith [abs_nonneg (p 0), abs_nonneg (p 1)]

theorem jetW_ab_zero_STR028b1 (q : Par) (h0 : q 0 = 0) (h1 : q 1 = 0) :
    (jetW q : Wsp α) = 0 := by
  apply Subtype.ext
  rw [(threefold_range_secondJet (α := α)).1 q, h0, h1]
  simp

/-- `‖ψ − jetW‖ ≲ R0 ν²` on a small ball. -/
theorem Rm_bound_STR028b1 (ψ : Par → Wsp α) (hψ : ContDiffAt ℝ 3 ψ 0) (h0 : ψ 0 = 0)
    (hF : ∀ᶠ p in 𝓝 (0 : Par), rangeMap α (p, ψ p) = 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ p : Par, ‖p‖ < r →
      ‖ψ p - jetW p‖ ≤ C * R0_STR028b1 p * nu p ^ 2 := by
  obtain ⟨r1, hr1, hbr⟩ := branch_STR028b1 ψ hψ h0 hF
  obtain ⟨-, -, hJ⟩ := threefold_range_secondJet (α := α)
  obtain ⟨r2, hr2, C, hC⟩ := hJ ψ hψ h0 hF
  refine ⟨min r1 r2, lt_min hr1 hr2, |C|, fun p hp => ?_⟩
  have hmem : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖pt_STR028b1 p s‖ < min r1 r2 := fun s hs =>
    lt_of_le_of_lt (pt_norm_le_STR028b1 p hs.1 hs.2) hp
  set d : Par := ![p 0, p 1, 0, 0] with hd
  have hd3 : d 3 = 0 := by simp [hd]
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt
      (fun s => ψ (pt_STR028b1 p s) - jetW (pt_STR028b1 p s))
      (fderiv ℝ (fun x => ψ x - jetW x) (pt_STR028b1 p s) d) (Set.Icc 0 1) s := by
    intro s hs
    have hq := (hbr _ (lt_of_lt_of_le (hmem s hs) (min_le_left _ _))).1
    have hΔ : DifferentiableAt ℝ (fun x => ψ x - jetW x) (pt_STR028b1 p s) :=
      (hq.sub ((jetW_contDiff (α := α) 3).contDiffAt)).differentiableAt (by norm_num)
    exact (hΔ.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_pt_STR028b1 p s)).hasDerivWithinAt
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      ‖fderiv ℝ (fun x => ψ x - jetW x) (pt_STR028b1 p s) d‖ ≤ |C| * R0_STR028b1 p * nu p ^ 2 := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hs
    obtain ⟨-, hC2, -⟩ := hC _ (lt_of_lt_of_le (hmem s hs') (min_le_right _ _))
    have h1 := hC2 d hd3
    have hnu := nu_pt_le_STR028b1 p hs.1 hs'.2
    have hn0 := nu_nonneg (pt_STR028b1 p s)
    have hdn := norm_d_le_STR028b1 p
    have hR := R0_nonneg_STR028b1 p
    calc _ ≤ C * nu (pt_STR028b1 p s) ^ 2 * ‖d‖ := h1
      _ ≤ |C| * nu (pt_STR028b1 p s) ^ 2 * ‖d‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
            (norm_nonneg _)
      _ ≤ |C| * nu p ^ 2 * R0_STR028b1 p := by
          have : nu (pt_STR028b1 p s) ^ 2 ≤ nu p ^ 2 := pow_le_pow_left₀ hn0 hnu 2
          gcongr
      _ = _ := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1
    (Set.right_mem_Icc.2 zero_le_one)
  have hq0 : ψ (pt_STR028b1 p 0) = 0 := (hbr _ (lt_of_lt_of_le (hmem 0 (Set.left_mem_Icc.2 zero_le_one))
    (min_le_left _ _))).2.2 (pt_zero_STR028b1 p).1 (pt_zero_STR028b1 p).2
  simp only [pt_one_STR028b1, hq0, jetW_ab_zero_STR028b1 _ (pt_zero_STR028b1 p).1 (pt_zero_STR028b1 p).2,
    sub_zero, sub_self, mul_one] at hmv
  exact hmv


/-- Transfer from `ψ` to the jet: `Φ(p, ψ p) - Φ(p, jetW p) = O(‖ψ - jetW‖²)`, by the envelope
identity `∂_w Φ = 0` on the range graph and the Lipschitz continuity of `dΦ`. -/
theorem transfer_STR028b1 (ψ : Par → Wsp α) (hψ : ContDiffAt ℝ 3 ψ 0) (h0 : ψ 0 = 0)
    (hF : ∀ᶠ p in 𝓝 (0 : Par), rangeMap α (p, ψ p) = 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ p : Par, ‖p‖ < r →
      |Fred_STR028b1 ψ p - Phi_STR028b1 (Xp (α := α) p)| ≤ C * R0_STR028b1 p ^ 2 * nu p ^ 4 := by
  obtain ⟨r1, hr1, hbr⟩ := branch_STR028b1 ψ hψ h0 hF
  obtain ⟨r3, hr3, C3, hC3⟩ := Rm_bound_STR028b1 ψ hψ h0 hF
  have hΦ1 : ContDiffAt ℝ 1 (fderiv ℝ (Phi_STR028b1 (α := α))) 0 :=
    ((contDiff_Phi_STR028b1 (α := α) 2).fderiv_right (m := 1) (by norm_num)).contDiffAt
  obtain ⟨K, T, hT, hK⟩ := hΦ1.exists_lipschitzOnWith
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.1 hT
  have hψt : Tendsto ψ (𝓝 0) (𝓝 0) := by simpa [h0] using hψ.continuousAt.tendsto
  have hψs : ∀ᶠ p in 𝓝 (0 : Par), ‖ψ p‖ < ε / 4 := by
    simpa using hψt.eventually (Metric.ball_mem_nhds (0 : Wsp α) (by positivity : (0 : ℝ) < ε / 4))
  have hjs : ∀ᶠ p in 𝓝 (0 : Par), ‖(jetW p : Wsp α)‖ < ε / 4 := by
    simpa using (jetW_tendsto (α := α)).eventually
      (Metric.ball_mem_nhds (0 : Wsp α) (by positivity : (0 : ℝ) < ε / 4))
  have hpε : ∀ᶠ p in 𝓝 (0 : Par), ‖p‖ < ε / 4 := by
    filter_upwards [Metric.ball_mem_nhds (0 : Par) (by positivity : (0 : ℝ) < ε / 4)] with p hp
    simpa using hp
  obtain ⟨r4, hr4, hball⟩ := Metric.eventually_nhds_iff.mp (hψs.and (hjs.and hpε))
  refine ⟨min (min r1 r3) r4, lt_min (lt_min hr1 hr3) hr4, (K : ℝ) * C3 ^ 2, fun p hp => ?_⟩
  have hp1 : ‖p‖ < r1 := lt_of_lt_of_le hp ((min_le_left _ _).trans (min_le_left _ _))
  have hp3 : ‖p‖ < r3 := lt_of_lt_of_le hp ((min_le_left _ _).trans (min_le_right _ _))
  have hp4 : ‖p‖ < r4 := lt_of_lt_of_le hp (min_le_right _ _)
  obtain ⟨hψε, hjε, hpε'⟩ := hball (by simpa using hp4)
  obtain ⟨hcd, hrm, -⟩ := hbr p hp1
  set Δ : Wsp α := jetW p - ψ p with hΔdef
  have hΔn : ‖Δ‖ ≤ |C3| * R0_STR028b1 p * nu p ^ 2 := by
    have h1 := hC3 p hp3
    rw [hΔdef, norm_sub_rev]
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C3)
      (R0_nonneg_STR028b1 p)) (sq_nonneg _)
  have hΔε : ‖Δ‖ < ε / 2 := by
    calc ‖Δ‖ ≤ ‖(jetW p : Wsp α)‖ + ‖ψ p‖ := norm_sub_le _ _
      _ < ε / 4 + ε / 4 := add_lt_add hjε hψε
      _ = ε / 2 := by ring
  set x : ℝ → Par × Wsp α := fun t => ((p, ψ p + t • Δ) : Par × Wsp α) with hx
  have hxT : ∀ t ∈ Set.Icc (0 : ℝ) 1, x t ∈ T := by
    intro t ht
    apply hεT
    rw [mem_ball_zero_iff, hx, Prod.norm_def]
    refine max_lt (by simp only; linarith) ?_
    simp only
    calc ‖ψ p + t • Δ‖ ≤ ‖ψ p‖ + ‖t • Δ‖ := norm_add_le _ _
      _ = ‖ψ p‖ + t * ‖Δ‖ := by rw [norm_smul, Real.norm_of_nonneg ht.1]
      _ ≤ ‖ψ p‖ + 1 * ‖Δ‖ := by gcongr; exact ht.2
      _ < ε := by linarith
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun t => Phi_STR028b1 (x t))
      (fderiv ℝ (Phi_STR028b1 (α := α)) (x t) (((0 : Par), Δ) : Par × Wsp α)) (Set.Icc 0 1) t := by
    intro t _
    have hpath : HasDerivAt x (((0 : Par), Δ) : Par × Wsp α) t := by
      have := (hasDerivAt_const t p).prodMk
        (((hasDerivAt_id t).smul_const Δ).const_add (ψ p))
      simpa using this
    have hdiff : DifferentiableAt ℝ (Phi_STR028b1 (α := α)) (x t) :=
      ((contDiff_Phi_STR028b1 (α := α) 1).differentiable one_ne_zero) _
    exact (hdiff.hasFDerivAt.comp_hasDerivAt t hpath).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖fderiv ℝ (Phi_STR028b1 (α := α)) (x t) (((0 : Par), Δ) : Par × Wsp α)‖ ≤
        (K : ℝ) * ‖Δ‖ ^ 2 := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self ht
    have h00 : x 0 = ((p, ψ p) : Par × Wsp α) := by simp [hx]
    have hx0T : x 0 ∈ T := hxT 0 (Set.left_mem_Icc.2 zero_le_one)
    have henv := fderiv_Phi_w_zero_STR028b1 ((p, ψ p) : Par × Wsp α) hrm Δ
    have hdist := hK.dist_le_mul (x t) (hxT t ht') (x 0) hx0T
    rw [h00, dist_eq_norm, dist_eq_norm] at hdist
    have hxn : ‖x t - ((p, ψ p) : Par × Wsp α)‖ = t * ‖Δ‖ := by
      have : x t - ((p, ψ p) : Par × Wsp α) = ((0 : Par), t • Δ) := by
        simp [hx]
      rw [this, Prod.norm_def, norm_zero, norm_smul, Real.norm_of_nonneg ht'.1]
      exact max_eq_right (mul_nonneg ht'.1 (norm_nonneg _))
    have hvn : ‖(((0 : Par), Δ) : Par × Wsp α)‖ = ‖Δ‖ := by
      rw [Prod.norm_def, norm_zero]; exact max_eq_right (norm_nonneg _)
    have h1 : ‖fderiv ℝ (Phi_STR028b1 (α := α)) (x t) (((0 : Par), Δ) : Par × Wsp α)‖ ≤
        ‖fderiv ℝ (Phi_STR028b1 (α := α)) (x t) - fderiv ℝ (Phi_STR028b1 (α := α))
          ((p, ψ p) : Par × Wsp α)‖ * ‖(((0 : Par), Δ) : Par × Wsp α)‖ := by
      have := ContinuousLinearMap.le_opNorm
        (fderiv ℝ (Phi_STR028b1 (α := α)) (x t) - fderiv ℝ (Phi_STR028b1 (α := α))
          ((p, ψ p) : Par × Wsp α)) (((0 : Par), Δ) : Par × Wsp α)
      rwa [sub_apply, henv, sub_zero] at this
    rw [hxn] at hdist
    rw [hvn] at h1
    refine h1.trans ?_
    calc _ ≤ ((K : ℝ) * (t * ‖Δ‖)) * ‖Δ‖ :=
          mul_le_mul_of_nonneg_right hdist (norm_nonneg _)
      _ ≤ ((K : ℝ) * (1 * ‖Δ‖)) * ‖Δ‖ := by
          gcongr; exact ht'.2
      _ = _ := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1
    (Set.right_mem_Icc.2 zero_le_one)
  have h1x : x 1 = Xp (α := α) p := by simp [hx, Xp, hΔdef]
  have h0x : x 0 = ((p, ψ p) : Par × Wsp α) := by simp [hx]
  simp only [h1x, h0x, sub_zero, mul_one] at hmv
  rw [Real.norm_eq_abs] at hmv
  have hfin : Fred_STR028b1 ψ p - Phi_STR028b1 (Xp (α := α) p) =
      -(Phi_STR028b1 (Xp (α := α) p) - Phi_STR028b1 ((p, ψ p) : Par × Wsp α)) := by
    unfold Fred_STR028b1; ring
  rw [hfin, abs_neg]
  refine hmv.trans ?_
  have hK0 : (0 : ℝ) ≤ K := K.2
  calc (K : ℝ) * ‖Δ‖ ^ 2 ≤ (K : ℝ) * ((|C3| * R0_STR028b1 p * nu p ^ 2) ^ 2) := by
        gcongr
    _ = (K : ℝ) * C3 ^ 2 * R0_STR028b1 p ^ 2 * nu p ^ 4 := by
        rw [mul_pow, mul_pow, sq_abs]; ring


/-- The quotient `G = F / R0²` (equal to `0` where `R0 = 0`). -/
noncomputable def Gred_STR028b1 (ψ : Par → Wsp α) (p : Par) : ℝ :=
  Fred_STR028b1 ψ p / (p 0 ^ 2 + p 1 ^ 2)

theorem R0_sq_STR028b1 (p : Par) : R0_STR028b1 p ^ 2 = p 0 ^ 2 + p 1 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem nu4_le_STR028b1 (p : Par) (hp : ‖p‖ ≤ 1 / 3) :
    nu p ^ 4 ≤ 128 * ((|p 2| + R0_STR028b1 p) ^ 3 + |p 3| * (|p 2| + R0_STR028b1 p) + p 3 ^ 2) := by
  have ha : |p 0| ≤ R0_STR028b1 p := Real.abs_le_sqrt (by nlinarith [sq_nonneg (p 1)])
  have hb : |p 1| ≤ R0_STR028b1 p := Real.abs_le_sqrt (by nlinarith [sq_nonneg (p 0)])
  have hR0 := R0_nonneg_STR028b1 p
  have hRle : R0_STR028b1 p ≤ |p 0| + |p 1| := by
    unfold R0_STR028b1
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_abs (p 0), sq_abs (p 1), abs_nonneg (p 0), abs_nonneg (p 1)]
  have hn0 : |p 0| ≤ ‖p‖ := by simpa using norm_le_pi_norm p 0
  have hn1 : |p 1| ≤ ‖p‖ := by simpa using norm_le_pi_norm p 1
  have hn2 : |p 2| ≤ ‖p‖ := by simpa using norm_le_pi_norm p 2
  set s : ℝ := |p 2| + R0_STR028b1 p with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := by rw [hs]; linarith
  set g : ℝ := Real.sqrt |p 3| with hg
  have hg0 : 0 ≤ g := Real.sqrt_nonneg _
  have hg2 : g ^ 2 = |p 3| := Real.sq_sqrt (abs_nonneg _)
  have hg4 : g ^ 4 = p 3 ^ 2 := by
    have : g ^ 4 = (g ^ 2) ^ 2 := by ring
    rw [this, hg2, sq_abs]
  have hnu : nu p ≤ 2 * s + g := by
    have e : nu p = |p 0| + |p 1| + |p 2| + g := rfl
    rw [e]; linarith [abs_nonneg (p 2)]
  have hnu0 := nu_nonneg p
  have h4 : nu p ^ 4 ≤ (2 * s + g) ^ 4 := pow_le_pow_left₀ hnu0 hnu 4
  have h5 : (2 * s + g) ^ 4 ≤ 8 * ((2 * s) ^ 4 + g ^ 4) := by
    have e1 : (2 * s + g) ^ 2 ≤ 2 * ((2 * s) ^ 2 + g ^ 2) := by nlinarith [sq_nonneg (2 * s - g)]
    have e2 : ((2 * s) ^ 2 + g ^ 2) ^ 2 ≤ 2 * ((2 * s) ^ 4 + g ^ 4) := by
      nlinarith [sq_nonneg ((2 * s) ^ 2 - g ^ 2)]
    calc (2 * s + g) ^ 4 = ((2 * s + g) ^ 2) ^ 2 := by ring
      _ ≤ (2 * ((2 * s) ^ 2 + g ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) e1 2
      _ = 4 * ((2 * s) ^ 2 + g ^ 2) ^ 2 := by ring
      _ ≤ 4 * (2 * ((2 * s) ^ 4 + g ^ 4)) := by linarith
      _ = _ := by ring
  have h6 : s ^ 4 ≤ s ^ 3 := pow_le_pow_of_le_one hs0 hs1 (by norm_num)
  have h7 : 0 ≤ |p 3| * s := by positivity
  calc nu p ^ 4 ≤ 8 * ((2 * s) ^ 4 + g ^ 4) := h4.trans h5
    _ = 128 * s ^ 4 + 8 * p 3 ^ 2 := by rw [hg4]; ring
    _ ≤ _ := by nlinarith [sq_nonneg (p 3)]

/-- Main output of the reduction (packet STR028-b1): see the file docstring. -/
theorem reducedFactor_STR028b1 (ψ : Par → Wsp α) (hψ : ContDiffAt ℝ 3 ψ 0) (h0 : ψ 0 = 0)
    (hF : ∀ᶠ p in 𝓝 (0 : Par), rangeMap α (p, ψ p) = 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ Gaa Gab Gbb : Par → ℝ, ∃ C M : ℝ,
      (∀ p : Par, ‖p‖ < r → ContDiffAt ℝ 3 (Fred_STR028b1 ψ) p) ∧
      (∀ p : Par, ‖p‖ < r → p 0 = 0 → p 1 = 0 → Fred_STR028b1 ψ p = 0) ∧
      (∀ p : Par, ‖p‖ < r → p 0 = 0 → p 1 = 0 → ∀ v : Par, v 2 = 0 → v 3 = 0 →
        fderiv ℝ (Fred_STR028b1 ψ) p v = 0) ∧
      ContinuousOn Gaa (Metric.ball (0 : Par) r) ∧ ContinuousOn Gab (Metric.ball (0 : Par) r) ∧
      ContinuousOn Gbb (Metric.ball (0 : Par) r) ∧
      (∀ p : Par, ‖p‖ < r →
        Fred_STR028b1 ψ p = p 0 ^ 2 * Gaa p + p 0 * p 1 * Gab p + p 1 ^ 2 * Gbb p) ∧
      (∀ p : Par, ‖p‖ < r → Fred_STR028b1 ψ p = (p 0 ^ 2 + p 1 ^ 2) * Gred_STR028b1 ψ p) ∧
      ContinuousOn (Gred_STR028b1 ψ)
        (Metric.ball (0 : Par) r ∩ {p : Par | p 0 ^ 2 + p 1 ^ 2 ≠ 0}) ∧
      (∀ p : Par, ‖p‖ ≤ r / 2 → |Gred_STR028b1 ψ p| ≤ M) ∧
      (∀ p : Par, ‖p‖ < r → ‖ψ p - jetW p‖ ≤ C * R0_STR028b1 p * nu p ^ 2) ∧
      (∀ p : Par, ‖p‖ < r →
        |Fred_STR028b1 ψ p - Phi_STR028b1 (Xp (α := α) p)| ≤ C * R0_STR028b1 p ^ 2 * nu p ^ 4) ∧
      (∀ p : Par, ‖p‖ < r → p 0 ^ 2 + p 1 ^ 2 ≠ 0 →
        |Gred_STR028b1 ψ p - Phi_STR028b1 (Xp (α := α) p) / (p 0 ^ 2 + p 1 ^ 2)| ≤ C * nu p ^ 4) := by
  obtain ⟨r1, hr1, hbr⟩ := branch_STR028b1 ψ hψ h0 hF
  obtain ⟨r3, hr3, C3, hC3⟩ := Rm_bound_STR028b1 ψ hψ h0 hF
  obtain ⟨r5, hr5, C5, hC5⟩ := transfer_STR028b1 ψ hψ h0 hF
  set r : ℝ := min r1 (min r3 r5) with hr
  have hr0 : 0 < r := lt_min hr1 (lt_min hr3 hr5)
  have hrr1 : ∀ p : Par, ‖p‖ < r → ‖p‖ < r1 := fun p hp => lt_of_lt_of_le hp (min_le_left _ _)
  have hrr3 : ∀ p : Par, ‖p‖ < r → ‖p‖ < r3 := fun p hp =>
    lt_of_lt_of_le hp ((min_le_right _ _).trans (min_le_left _ _))
  have hrr5 : ∀ p : Par, ‖p‖ < r → ‖p‖ < r5 := fun p hp =>
    lt_of_lt_of_le hp ((min_le_right _ _).trans (min_le_right _ _))
  have hsm : ∀ p : Par, ‖p‖ < r → ContDiffAt ℝ 3 (Fred_STR028b1 ψ) p := fun p hp =>
    contDiffAt_Fred_STR028b1 ψ (hbr p (hrr1 p hp)).1
  have hz : ∀ p : Par, ‖p‖ < r → p 0 = 0 → p 1 = 0 → Fred_STR028b1 ψ p = 0 := fun p hp ha hb =>
    Fred_zero_STR028b1 ψ p ((hbr p (hrr1 p hp)).2.2 ha hb) ha hb
  have hcr : ∀ p : Par, ‖p‖ < r → p 0 = 0 → p 1 = 0 → ∀ v : Par, v 2 = 0 → v 3 = 0 →
      fderiv ℝ (Fred_STR028b1 ψ) p v = 0 := fun p hp ha hb v hv2 hv3 =>
    fderiv_Fred_ab_STR028b1 ψ p
      ((hbr p (hrr1 p hp)).1.differentiableAt (by norm_num)) ((hbr p (hrr1 p hp)).2.2 ha hb)
      ha hb v hv2 hv3
  obtain ⟨Gaa, Gab, Gbb, hGaa, hGab, hGbb, hFG⟩ := hadamard_STR028b1 (Fred_STR028b1 ψ) r
    (fun p hp => (hsm p hp).of_le (by norm_num)) hz hcr
  have hFc : ∀ p : Par, ‖p‖ < r → Fred_STR028b1 ψ p = (p 0 ^ 2 + p 1 ^ 2) * Gred_STR028b1 ψ p := by
    intro p hp
    by_cases hpos : p 0 ^ 2 + p 1 ^ 2 = 0
    · have ha : p 0 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
      have hb : p 1 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
      rw [hz p hp ha hb, hpos, zero_mul]
    · unfold Gred_STR028b1
      field_simp
  have hcompact : IsCompact (Metric.closedBall (0 : Par) (r / 2)) := isCompact_closedBall _ _
  have hsub : Metric.closedBall (0 : Par) (r / 2) ⊆ Metric.ball (0 : Par) r :=
    Metric.closedBall_subset_ball (by linarith)
  obtain ⟨M1, hM1⟩ := hcompact.exists_bound_of_continuousOn (hGaa.mono hsub)
  obtain ⟨M2, hM2⟩ := hcompact.exists_bound_of_continuousOn (hGab.mono hsub)
  obtain ⟨M3, hM3⟩ := hcompact.exists_bound_of_continuousOn (hGbb.mono hsub)
  refine ⟨r, hr0, Gaa, Gab, Gbb, max C3 C5, |M1| + |M2| + |M3|, hsm, hz, hcr, hGaa, hGab, hGbb,
    hFG, hFc, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : ContinuousOn (Fred_STR028b1 ψ) (Metric.ball (0 : Par) r) := fun p hp =>
      (hsm p (by simpa using hp)).continuousAt.continuousWithinAt
    refine (hc.mono Set.inter_subset_left).div
      (by fun_prop : Continuous fun p : Par => p 0 ^ 2 + p 1 ^ 2).continuousOn ?_
    intro p hp
    exact hp.2
  · intro p hp
    have hpr : ‖p‖ < r := lt_of_le_of_lt hp (by linarith)
    have hpm : p ∈ Metric.closedBall (0 : Par) (r / 2) := by simpa using hp
    have e1 := hM1 p hpm
    have e2 := hM2 p hpm
    have e3 := hM3 p hpm
    rw [Real.norm_eq_abs] at e1 e2 e3
    by_cases hpos : p 0 ^ 2 + p 1 ^ 2 = 0
    · unfold Gred_STR028b1
      rw [hpos, div_zero, abs_zero]
      positivity
    · have hpos' : 0 < p 0 ^ 2 + p 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hpos)
      have hF1 := hFG p hpr
      have hab : |p 0 * p 1| ≤ p 0 ^ 2 + p 1 ^ 2 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg (p 0 + p 1), sq_nonneg (p 0 - p 1)]
      have hbound : |Fred_STR028b1 ψ p| ≤ (p 0 ^ 2 + p 1 ^ 2) * (|M1| + |M2| + |M3|) := by
        rw [hF1]
        have t1 : |p 0 ^ 2 * Gaa p| ≤ p 0 ^ 2 * |M1| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
          exact mul_le_mul_of_nonneg_left (e1.trans (le_abs_self _)) (sq_nonneg _)
        have t2 : |p 0 * p 1 * Gab p| ≤ (p 0 ^ 2 + p 1 ^ 2) * |M2| := by
          rw [abs_mul]
          exact mul_le_mul hab (e2.trans (le_abs_self _)) (abs_nonneg _) (by positivity)
        have t3 : |p 1 ^ 2 * Gbb p| ≤ p 1 ^ 2 * |M3| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
          exact mul_le_mul_of_nonneg_left (e3.trans (le_abs_self _)) (sq_nonneg _)
        have hM1' := abs_nonneg M1
        have hM3' := abs_nonneg M3
        have hM2' := abs_nonneg M2
        calc _ ≤ |p 0 ^ 2 * Gaa p| + |p 0 * p 1 * Gab p| + |p 1 ^ 2 * Gbb p| :=
              (abs_add_three _ _ _)
          _ ≤ p 0 ^ 2 * |M1| + (p 0 ^ 2 + p 1 ^ 2) * |M2| + p 1 ^ 2 * |M3| := by linarith
          _ ≤ _ := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
      unfold Gred_STR028b1
      rw [abs_div, abs_of_pos hpos', div_le_iff₀ hpos']
      linarith
  · intro p hp
    have h1 := hC3 p (hrr3 p hp)
    have h2 : 0 ≤ R0_STR028b1 p * nu p ^ 2 := mul_nonneg (R0_nonneg_STR028b1 p) (sq_nonneg _)
    calc _ ≤ C3 * R0_STR028b1 p * nu p ^ 2 := h1
      _ ≤ max C3 C5 * R0_STR028b1 p * nu p ^ 2 := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) h2
  · intro p hp
    have h1 := hC5 p (hrr5 p hp)
    have h2 : 0 ≤ R0_STR028b1 p ^ 2 * nu p ^ 4 := by positivity
    calc _ ≤ C5 * R0_STR028b1 p ^ 2 * nu p ^ 4 := h1
      _ ≤ max C3 C5 * R0_STR028b1 p ^ 2 * nu p ^ 4 := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) h2
  · intro p hp hpos
    have hpos' : 0 < p 0 ^ 2 + p 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hpos)
    have h1 := hC5 p (hrr5 p hp)
    have h2 : 0 ≤ R0_STR028b1 p ^ 2 * nu p ^ 4 := by positivity
    have h3 : |Fred_STR028b1 ψ p - Phi_STR028b1 (Xp (α := α) p)| ≤
        max C3 C5 * R0_STR028b1 p ^ 2 * nu p ^ 4 := by
      calc _ ≤ C5 * R0_STR028b1 p ^ 2 * nu p ^ 4 := h1
        _ ≤ _ := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) h2
    rw [R0_sq_STR028b1] at h3
    have e : Gred_STR028b1 ψ p - Phi_STR028b1 (Xp (α := α) p) / (p 0 ^ 2 + p 1 ^ 2) =
        (Fred_STR028b1 ψ p - Phi_STR028b1 (Xp (α := α) p)) / (p 0 ^ 2 + p 1 ^ 2) := by
      unfold Gred_STR028b1; ring
    rw [e, abs_div, abs_of_pos hpos', div_le_iff₀ hpos']
    calc _ ≤ max C3 C5 * (p 0 ^ 2 + p 1 ^ 2) * nu p ^ 4 := h3
      _ = _ := by ring

end Hadamard

end Kap

end Calc

end DGPS.Examples.ThreeSpeciesCircle
