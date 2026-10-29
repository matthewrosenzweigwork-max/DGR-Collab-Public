import DGPS.Lipschitz.EigenfunctionH2
import DGPS.Lipschitz.ResolventFourier
import DGPS.Lipschitz.ResolventSobolev
import DGPS.Lipschitz.ResolventIteration
import DGPS.Lipschitz.WeightedSpectrum

/-!
# LIP010d: `C¹` bounds for weighted eigenfunctions without differentiating the drift

Final assembly of LIP010.  Let `e` be a weak eigenfunction of the weighted Dirichlet form with
weight `w` (`WData d w b c C`, so only `b ∈ L∞`), eigenvalue `λ ≥ 0` and `‖e‖_{L²(w m)} = 1`.
Then `e ∈ H²`, `‖e‖_{H²} ≤ C(1+λ)`, and `e` has a `C¹` representative `ũ` with gradient
`∇ũ = ∇e` a.e. and `‖ũ‖_∞ + ‖∇ũ‖_∞ ≤ C (1+λ)^d`, with `C` depending only on `d, M, c`.

Route.  `F = (1+λ)e + b·∇e ∈ L²`; the weak Laplacian identity `Δe = -(λe + b·∇e)` gives the Fourier
coefficients `(1+4π²|k|²) ê(k) = F̂(k)`, so `e = R F` a.e. with `R = (1-Δ)⁻¹` (LIP010c3).  Then the
exponent ladder `p_k = 2d/(d-k)` is climbed with LIP010c2 (1): each rung
`L^{p_k} → W^{1,p_{k+1}}` costs one factor `1+λ` through the drift term.  At `p_{d-1} = 2d > d` the
`C¹` endpoint (LIP010c2 (3)) closes the argument.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace DGPS.Lipschitz.EigenfunctionC1

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent DGPS.Lipschitz DGPS.Lipschitz.WeightedGenerator
  DGPS.Lipschitz.ParabolicChainRule

variable {d : ℕ}

/-- The right-hand side `F = (1+λ) u + b · ∇u` of `(1-Δ) u = F`. -/
noncomputable def rhs (b : Torus d → Tangent d) (lam : ℝ) (u : Torus d → ℝ)
    (G : Torus d → Tangent d) : Torus d → ℝ :=
  fun x => (1 + lam) * u x + ⟪b x, G x⟫_ℝ

theorem memLp_rhs {b : Torus d → Tangent d} {lam : ℝ} {u : Torus d → ℝ} {G : Torus d → Tangent d}
    (hb : MemLp b ∞ (haar d)) (hu : IsWeakGradient u G) : MemLp (rhs b lam u G) 2 (haar d) :=
  (hu.memLp.const_mul (1 + lam)).add (memLp_inner_top hb hu.memLp_grad)

/-- Ladder exponents as extended reals. -/
noncomputable def pE (d k : ℕ) : ℝ≥0∞ := ENNReal.ofReal (ladderExponent d k)

theorem ladderExponent_ge_two {k : ℕ} (hk : k < d) : 2 ≤ ladderExponent d k := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have h1 : (0 : ℝ) < d - k := by
    have : (k : ℝ) < d := by exact_mod_cast hk
    linarith
  unfold ladderExponent
  rw [le_div_iff₀ h1]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

theorem ladderExponent_mono {k : ℕ} (hk : k + 1 < d) :
    ladderExponent d k ≤ ladderExponent d (k + 1) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have h2 : (0 : ℝ) < d - (k + 1 : ℕ) := by
    have : ((k + 1 : ℕ) : ℝ) < d := by exact_mod_cast hk
    linarith
  unfold ladderExponent
  apply div_le_div_of_nonneg_left (by positivity) h2
  push_cast at *
  linarith

theorem one_le_pE {k : ℕ} (hk : k < d) : 1 ≤ pE d k := by
  unfold pE
  have := ladderExponent_ge_two hk
  calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

theorem pE_le {k : ℕ} (hk : k + 1 < d) : pE d k ≤ pE d (k + 1) :=
  ENNReal.ofReal_le_ofReal (ladderExponent_mono hk)

theorem inv_pE_toReal {k : ℕ} (hk : k < d) : ((pE d k)⁻¹).toReal = 1 / ladderExponent d k := by
  have h := ladderExponent_ge_two hk
  unfold pE
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith), one_div]

theorem theta_pE_lt {k : ℕ} (hk : k + 1 < d) : (d : ℝ) * theta (pE d k) (pE d (k + 1)) < 1 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold theta
  rw [inv_pE_toReal (by omega), inv_pE_toReal hk]
  have := ladderExponent_gap d k hk
  calc (d : ℝ) * _ < d * (1 / d) := mul_lt_mul_of_pos_left this hd
    _ = 1 := by field_simp

theorem pE_zero (hd : 0 < d) : pE d 0 = 2 := by
  unfold pE
  rw [ladderExponent_zero d hd]
  simp

theorem pE_last (hd : 0 < d) : pE d (d - 1) = ENNReal.ofReal (2 * d) := by
  unfold pE
  rw [ladderExponent_last d hd]

theorem lt_pE_last (hd : 0 < d) : (d : ℝ≥0∞) < pE d (d - 1) := by
  rw [pE_last hd]
  have : (d : ℝ≥0∞) = ENNReal.ofReal d := by simp
  rw [this]
  have : (0 : ℝ) < d := by exact_mod_cast hd
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)

/-- Weak gradient identification: if `u = R F` a.e. and `G` is a weak gradient of `u`, then
`G = ∇R F` a.e. -/
theorem grad_ae_eq_resolventGrad {u : Torus d → ℝ} {G : Torus d → Tangent d} {F : Torus d → ℝ}
    (hF : MemLp F 2 (haar d)) (hu : IsWeakGradient u G) (hsol : u =ᵐ[haar d] resolvent F) :
    G =ᵐ[haar d] resolventGrad F :=
  (hu.congr_ae hsol (Filter.EventuallyEq.refl _ _)).ae_eq
    (lip010c3_resolvent_fourier hF).2.1

/-- Triangle inequality for the right-hand side. -/
theorem eLpNorm_rhs_le {M lam : ℝ} {b : Torus d → Tangent d} {u : Torus d → ℝ}
    {G : Torus d → Tangent d} {q : ℝ≥0∞} (hq1 : 1 ≤ q) (hM : 0 ≤ M) (hlam : 0 ≤ lam)
    (hb : MemLp b ∞ (haar d)) (hbM : ∀ᵐ x ∂haar d, ‖b x‖ ≤ M) (hu : IsWeakGradient u G) :
    eLpNorm (rhs b lam u G) q (haar d) ≤
      ENNReal.ofReal (1 + lam) * eLpNorm u q (haar d) + ENNReal.ofReal M * eLpNorm G q (haar d) := by
  have hmu : AEStronglyMeasurable (fun x => (1 + lam) * u x) (haar d) :=
    (hu.memLp.const_mul (1 + lam)).aestronglyMeasurable
  have hmb : AEStronglyMeasurable (fun x => ⟪b x, G x⟫_ℝ) (haar d) :=
    (memLp_inner_top hb hu.memLp_grad).aestronglyMeasurable
  have h1 : eLpNorm (rhs b lam u G) q (haar d) ≤
      eLpNorm (fun x => (1 + lam) * u x) q (haar d) + eLpNorm (fun x => ⟪b x, G x⟫_ℝ) q (haar d) :=
    eLpNorm_add_le (μ := haar d) (f := fun x => (1 + lam) * u x)
      (g := fun x => ⟪b x, G x⟫_ℝ) hq1
  have h2 : eLpNorm (fun x => (1 + lam) * u x) q (haar d) =
      ENNReal.ofReal (1 + lam) * eLpNorm u q (haar d) := by
    have h := eLpNorm_const_smul (μ := haar d) (p := q) (1 + lam) u
    have e : (fun x => (1 + lam) * u x) = (1 + lam) • u := by funext x; simp
    rw [e, h, Real.enorm_eq_ofReal (by linarith)]
  have h3 : eLpNorm (fun x => ⟪b x, G x⟫_ℝ) q (haar d) ≤
      ENNReal.ofReal M * eLpNorm G q (haar d) := by
    have hae : ∀ᵐ x ∂haar d, ‖⟪b x, G x⟫_ℝ‖₊ ≤ M.toNNReal * ‖G x‖₊ := by
      filter_upwards [hbM] with x hx
      rw [← NNReal.coe_le_coe]
      simp only [coe_nnnorm, NNReal.coe_mul, Real.coe_toNNReal _ hM]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (μ := haar d)
      (f := fun x => ⟪b x, G x⟫_ℝ) (g := G) (c := M.toNNReal) hmb hae
    simpa [ENNReal.smul_def, ENNReal.ofReal] using this q
  exact h1.trans (by rw [h2]; exact add_le_add le_rfl h3)

/-- One rung of the ladder: the bound on `F` in `L^{p_k}` yields one in `L^{p_{k+1}}`, losing one
factor `(1+λ)`. -/
theorem step {k : ℕ} (hk : k + 1 < d) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ (M lam B : ℝ) (b : Torus d → Tangent d) (u : Torus d → ℝ)
      (G : Torus d → Tangent d), 0 ≤ M → 0 ≤ lam → 0 ≤ B → MemLp b ∞ (haar d) →
      (∀ᵐ x ∂haar d, ‖b x‖ ≤ M) → IsWeakGradient u G →
      u =ᵐ[haar d] resolvent (rhs b lam u G) →
      eLpNorm (rhs b lam u G) (pE d k) (haar d) ≤ ENNReal.ofReal B →
      eLpNorm (rhs b lam u G) (pE d (k + 1)) (haar d) ≤
        ENNReal.ofReal ((1 + M) * (1 + lam) * (Cr * B)) := by
  obtain ⟨Cr, hCr, hbd⟩ := (lip010c2_resolvent_sobolev d).1 (pE d k) (pE d (k + 1))
    (one_le_pE (by omega)) (pE_le hk) (theta_pE_lt hk)
  refine ⟨Cr, hCr, fun M lam B b u G hM hlam hB hb hbM hu hsol hFB => ?_⟩
  set F := rhs b lam u G with hFdef
  have hF : MemLp F 2 (haar d) := memLp_rhs hb hu
  have hG := grad_ae_eq_resolventGrad hF hu hsol
  set q := pE d (k + 1) with hq
  have hq1 : 1 ≤ q := one_le_pE hk
  have hres := hbd F hF.aestronglyMeasurable
  have hX : eLpNorm u q (haar d) = eLpNorm (resolvent F) q (haar d) := eLpNorm_congr_ae hsol
  have hY : eLpNorm G q (haar d) = eLpNorm (resolventGrad F) q (haar d) := eLpNorm_congr_ae hG
  have hXY : eLpNorm u q (haar d) + eLpNorm G q (haar d) ≤ ENNReal.ofReal (Cr * B) := by
    rw [hX, hY]
    refine hres.trans ?_
    rw [ENNReal.ofReal_mul hCr]
    gcongr
  have hmain := eLpNorm_rhs_le hq1 hM hlam hb hbM hu
  have hc1 : ENNReal.ofReal (1 + lam) ≤ ENNReal.ofReal ((1 + M) * (1 + lam)) :=
    ENNReal.ofReal_le_ofReal (by nlinarith)
  have hc2 : ENNReal.ofReal M ≤ ENNReal.ofReal ((1 + M) * (1 + lam)) :=
    ENNReal.ofReal_le_ofReal (by nlinarith)
  calc eLpNorm F q (haar d) ≤ ENNReal.ofReal (1 + lam) * eLpNorm u q (haar d) +
        ENNReal.ofReal M * eLpNorm G q (haar d) := hmain
    _ ≤ ENNReal.ofReal ((1 + M) * (1 + lam)) * eLpNorm u q (haar d) +
        ENNReal.ofReal ((1 + M) * (1 + lam)) * eLpNorm G q (haar d) :=
      by gcongr
    _ = ENNReal.ofReal ((1 + M) * (1 + lam)) * (eLpNorm u q (haar d) + eLpNorm G q (haar d)) :=
      (mul_add _ _ _).symm
    _ ≤ ENNReal.ofReal ((1 + M) * (1 + lam)) * ENNReal.ofReal (Cr * B) :=
      by gcongr
    _ = ENNReal.ofReal ((1 + M) * (1 + lam) * (Cr * B)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]

/-- The ladder: after `k` rungs the right-hand side is bounded in `L^{p_k}` by `B (1+λ)^{k+1}`. -/
theorem ladder (hd : 0 < d) (M K0 : ℝ) (hM0 : 0 ≤ M) (hK0 : 0 ≤ K0) : ∀ k : ℕ, k < d →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (lam : ℝ) (b : Torus d → Tangent d) (u : Torus d → ℝ)
      (G : Torus d → Tangent d), 0 ≤ M → 0 ≤ lam → MemLp b ∞ (haar d) →
      (∀ᵐ x ∂haar d, ‖b x‖ ≤ M) → IsWeakGradient u G →
      u =ᵐ[haar d] resolvent (rhs b lam u G) →
      eLpNorm (rhs b lam u G) 2 (haar d) ≤ ENNReal.ofReal (K0 * (1 + lam)) →
      eLpNorm (rhs b lam u G) (pE d k) (haar d) ≤ ENNReal.ofReal (B * (1 + lam) ^ (k + 1)) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨K0, hK0, fun lam b u G hM hlam hb hbM hu hsol hF0 => ?_⟩
    rw [pE_zero hd]
    simpa using hF0
  | succ k ih =>
    intro hk
    obtain ⟨B, hB, hBd⟩ := ih (by omega)
    obtain ⟨Cr, hCr, hstep⟩ := step (d := d) hk
    refine ⟨(1 + M) * (Cr * B), ?_, fun lam b u G hM hlam hb hbM hu hsol hF0 => ?_⟩
    · positivity
    · have h1 := hstep M lam (B * (1 + lam) ^ (k + 1)) b u G hM hlam (by positivity) hb hbM hu hsol
        (hBd lam b u G hM hlam hb hbM hu hsol hF0)
      refine h1.trans (le_of_eq ?_)
      congr 1
      ring

/-- The core assembly (no weights): if `u ∈ H¹` solves `(1-Δ)u = F := (1+λ)u + b·∇u` and `F` has an
`L²` bound `K₀(1+λ)`, then `R F` is `C¹` with `‖R F‖_∞ + ‖∇R F‖_∞ ≤ C (1+λ)^d`. -/
theorem core (hd : 0 < d) (M K0 : ℝ) (hM0 : 0 ≤ M) (hK0 : 0 ≤ K0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : ℝ) (b : Torus d → Tangent d) (u : Torus d → ℝ)
      (G : Torus d → Tangent d), 0 ≤ M → 0 ≤ lam → MemLp b ∞ (haar d) →
      (∀ᵐ x ∂haar d, ‖b x‖ ≤ M) → IsWeakGradient u G →
      u =ᵐ[haar d] resolvent (rhs b lam u G) →
      eLpNorm (rhs b lam u G) 2 (haar d) ≤ ENNReal.ofReal (K0 * (1 + lam)) →
      IsC1Periodic (resolvent (rhs b lam u G)) ∧
      (∀ v : Tangent d, HasFDerivAt
        (fun y : Tangent d => resolvent (rhs b lam u G) (torusLift y.ofLp))
        (InnerProductSpace.toDual ℝ (Tangent d)
          (resolventGrad (rhs b lam u G) (torusLift v.ofLp))) v) ∧
      (∀ x, |resolvent (rhs b lam u G) x| + ‖resolventGrad (rhs b lam u G) x‖ ≤
        C * (1 + lam) ^ d) := by
  obtain ⟨B, hB, hBd⟩ := ladder hd M K0 hM0 hK0 (d - 1) (by omega)
  have hθ := theta_top_lt_one_of_gt (d := d) (lt_pE_last hd)
  have hCf : 0 ≤ resConst d (theta (pE d (d - 1)) ⊤) + gradConst d (theta (pE d (d - 1)) ⊤) :=
    (add_pos (resConst_pos d (by linarith)) (gradConst_pos d hθ)).le
  refine ⟨(resConst d (theta (pE d (d - 1)) ⊤) + gradConst d (theta (pE d (d - 1)) ⊤)) * B,
    mul_nonneg hCf hB, fun lam b u G hM hlam hb hbM hu hsol hF0 => ?_⟩
  have hF : MemLp (rhs b lam u G) 2 (haar d) := memLp_rhs hb hu
  have hbound := hBd lam b u G hM hlam hb hbM hu hsol hF0
  have hne : eLpNorm (rhs b lam u G) (pE d (d - 1)) (haar d) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  obtain ⟨h1, h2, h3⟩ := (lip010c2_resolvent_sobolev d).2 (pE d (d - 1)) (lt_pE_last hd)
    (one_le_pE (by omega)) (rhs b lam u G) (hF.integrable one_le_two) hne
  refine ⟨h1, h2, fun x => (h3 x).trans ?_⟩
  have hn : (eLpNorm (rhs b lam u G) (pE d (d - 1)) (haar d)).toReal ≤ B * (1 + lam) ^ d := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    rw [ENNReal.toReal_ofReal (by positivity)] at this
    rwa [Nat.sub_add_cancel hd] at this
  calc _ ≤ (resConst d (theta (pE d (d - 1)) ⊤) + gradConst d (theta (pE d (d - 1)) ⊤)) *
        (B * (1 + lam) ^ d) := mul_le_mul_of_nonneg_left hn hCf
    _ = _ := by ring

/-- `L²` norm as a square root of the integral of the squared norm. -/
theorem eLpNorm_two_eq {E : Type*} [NormedAddCommGroup E] {f : Torus d → E}
    (hf : MemLp f 2 (haar d)) :
    eLpNorm f 2 (haar d) = ENNReal.ofReal (Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂haar d)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [Real.sqrt_eq_rpow, one_div]

/-- The weak eigen-equation gives `Δ e = -(λ e + b · ∇e)` weakly. -/
theorem weak_laplacian_of_eig {w : Torus d → ℝ} {b : Torus d → Tangent d} {c C lam : ℝ}
    (hwd : WData d w b c C) {e : Hw d w} {G : Torus d → Tangent d}
    (hG : IsWeakGradient (e : Torus d → ℝ) G)
    (heig : ∀ (f : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (f : Torus d → ℝ) Y →
      weightedForm w G Y = lam * ⟪e, f⟫_ℝ) :
    IsWeakLaplacian (e : Torus d → ℝ) (fun z => -(lam * (e : Torus d → ℝ) z + ⟪b z, G z⟫_ℝ)) := by
  have hc := hwd.pos
  have hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C := Eventually.of_forall hwd.bound
  have hg : MemLp (fun x => lam * (e : Torus d → ℝ) x) 2 (haar d) := hG.memLp.const_mul lam
  refine converse_laplacian hwd hG hg ?_
  intro y Y hy
  have hyw : MemLp y 2 (wMeasure d w) := (memLp_wMeasure_iff hc hwb).mpr hy.memLp
  set f : Hw d w := hyw.toLp y with hf
  have hfy : ((f : Hw d w) : Torus d → ℝ) =ᵐ[wMeasure d w] y := MemLp.coeFn_toLp hyw
  have hfy' := ae_eq_haar hc hwb hfy
  have hfg : IsWeakGradient ((f : Hw d w) : Torus d → ℝ) Y :=
    hy.congr_ae hfy'.symm (Filter.EventuallyEq.refl _ _)
  have h := heig f Y hfg
  rw [inner_Lp_wMeasure hwd.meas hc hwb] at h
  unfold weightedForm at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hfy'] with z hz
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hz]
  ring

/-- The eigenfunction is the resolvent of its right-hand side. -/
theorem eig_eq_resolvent {w : Torus d → ℝ} {b : Torus d → Tangent d} {c C lam : ℝ}
    (hwd : WData d w b c C) {e : Hw d w} {G : Torus d → Tangent d}
    (hG : IsWeakGradient (e : Torus d → ℝ) G)
    (heig : ∀ (f : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (f : Torus d → ℝ) Y →
      weightedForm w G Y = lam * ⟪e, f⟫_ℝ) :
    (e : Torus d → ℝ) =ᵐ[haar d] resolvent (rhs b lam (e : Torus d → ℝ) G) := by
  have hlap := weak_laplacian_of_eig (lam := lam) hwd hG heig
  have hF : MemLp (rhs b lam (e : Torus d → ℝ) G) 2 (haar d) := memLp_rhs hwd.b_bdd hG
  refine (lip010c3_resolvent_fourier hF).2.2.2.2 _ hG.memLp fun k => ?_
  have h1 := hlap.fourierCoeff_eq k
  have hfun : (fun z => -(lam * (e : Torus d → ℝ) z + ⟪b z, G z⟫_ℝ)) =
      fun z => (e : Torus d → ℝ) z - rhs b lam (e : Torus d → ℝ) G z := by
    funext z; simp only [rhs]; ring
  rw [hfun, fourierCoeff_sub'' hG.memLp hF] at h1
  have hpos : (0 : ℝ) < 1 + gradWeight k := by
    have : 0 ≤ gradWeight k := by unfold gradWeight; positivity
    linarith
  have hne : ((1 + gradWeight k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have h2 : fourierCoeff (rhs b lam (e : Torus d → ℝ) G) k =
      ((1 + gradWeight k : ℝ) : ℂ) * fourierCoeff (e : Torus d → ℝ) k := by
    push_cast
    linear_combination (-1 : ℂ) * h1
  rw [h2, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne']
  simp

end DGPS.Lipschitz.EigenfunctionC1

namespace DGPS.Lipschitz

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent DGPS.Lipschitz.WeightedGenerator
  DGPS.Lipschitz.ParabolicChainRule DGPS.Lipschitz.EigenfunctionC1

/-- **LIP010.**  Let `w` be a weight with `WData d w b c C` (only `b ∈ L∞` is assumed, with
`‖b‖ ≤ M` a.e.) on `𝕋^d`, `0 < d`.  There is a constant `K`, depending only on `d`, `M`, `c`, such
that every weak eigenfunction `e` (`∫⟨∇e, ∇f⟩ w = λ⟨e, f⟩_w` for all `f ∈ H¹`, `λ ≥ 0`) with
`‖e‖_{L²(w m)} = 1` and weak gradient `G`

* is in `H²`: `IsWeakHessian e G H` with `‖e‖_{H²} ≤ K (1+λ)`;
* has a `C¹` representative `v` (`v = e` a.e.) whose classical gradient `g` equals `G` a.e. and
  satisfies `‖v‖_∞ + ‖g‖_∞ ≤ K (1+λ)^d`.

The drift is never differentiated: `e = (1-Δ)⁻¹((1+λ)e + b·∇e)` is bootstrapped along the exponents
`p_k = 2d/(d-k)`, `k = 0, …, d-1`, and closed with the `C¹` endpoint at `p_{d-1} = 2d > d`. -/
theorem eigenfunction_c1_bounds_without_differentiating_drift {d : ℕ} (hd : 0 < d)
    {w : Torus d → ℝ} {b : Torus d → Tangent d} {c C M : ℝ} (hwd : WData d w b c C)
    (hM : ∀ᵐ x ∂haar d, ‖b x‖ ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lam : ℝ, 0 ≤ lam → ∀ (e : Hw d w) (G : Torus d → Tangent d),
      ‖e‖ = 1 → IsWeakGradient (e : Torus d → ℝ) G →
      (∀ (f : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (f : Torus d → ℝ) Y →
        weightedForm w G Y = lam * ⟪e, f⟫_ℝ) →
      (∃ H : Fin d → Fin d → Torus d → ℝ, IsWeakHessian (e : Torus d → ℝ) G H ∧
        Real.sqrt (h2NormSq (e : Torus d → ℝ) G H) ≤ K * (1 + lam)) ∧
      ∃ (v : Torus d → ℝ) (g : Torus d → Tangent d), IsC1Periodic v ∧
        v =ᵐ[haar d] (e : Torus d → ℝ) ∧ g =ᵐ[haar d] G ∧
        (∀ y : Tangent d, HasFDerivAt (fun z : Tangent d => v (torusLift z.ofLp))
          (InnerProductSpace.toDual ℝ (Tangent d) (g (torusLift y.ofLp))) y) ∧
        ∀ x, |v x| + ‖g x‖ ≤ K * (1 + lam) ^ d := by
  have hc := hwd.pos
  have hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C := Eventually.of_forall hwd.bound
  have hM0 : 0 ≤ M := by
    obtain ⟨x, hx⟩ := hM.exists
    exact (norm_nonneg _).trans hx
  have hsc : 0 ≤ Real.sqrt (1 / c) := Real.sqrt_nonneg _
  set K0 : ℝ := (1 + M * Real.sqrt (2 * M ^ 2 + 3)) * Real.sqrt (1 / c) with hK0def
  have hK0 : 0 ≤ K0 := by positivity
  obtain ⟨Cc, hCc, hcore⟩ := core hd M K0 hM0 hK0
  refine ⟨max ((4 * M ^ 2 + 6) * Real.sqrt (1 / c)) Cc, le_max_of_le_right hCc, ?_⟩
  intro lam hlam e G he hG heig
  have hlam1 : 1 ≤ 1 + lam := by linarith
  obtain ⟨H, hH, hY, hh2⟩ := eigenfunction_h2_bound hwd hM hlam e G hG heig
  set u : Torus d → ℝ := (e : Torus d → ℝ) with hu
  have hUnn : 0 ≤ ∫ x, u x ^ 2 ∂haar d := integral_nonneg fun x => sq_nonneg _
  have hU : ∫ x, u x ^ 2 ∂haar d ≤ 1 / c := by
    have h1 := norm_sq_Hw hwd.meas hc hwb e
    rw [he] at h1
    have hui : Integrable (fun x => u x ^ 2) (haar d) := hG.memLp.integrable_sq
    have hui' : Integrable (fun x => u x ^ 2 * w x) (haar d) := by
      refine Integrable.mono' (hui.const_mul C) (hui.1.mul hwd.meas.aestronglyMeasurable) ?_
      filter_upwards [hwb] with x hx
      have h0 : 0 ≤ w x := hc.le.trans hx.1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg (u x), hx.2]
    have : c * ∫ x, u x ^ 2 ∂haar d ≤ 1 := by
      rw [← integral_const_mul]
      calc _ ≤ ∫ x, u x ^ 2 * w x ∂haar d := by
            refine integral_mono_ae (hui.const_mul c) hui' ?_
            filter_upwards [hwb] with x hx
            nlinarith [sq_nonneg (u x), hx.1]
        _ = 1 := by rw [← h1]; norm_num
    rw [le_div_iff₀ hc]
    linarith [mul_comm c (∫ x, u x ^ 2 ∂haar d)]
  have hsU : Real.sqrt (∫ x, u x ^ 2 ∂haar d) ≤ Real.sqrt (1 / c) := Real.sqrt_le_sqrt hU
  refine ⟨⟨H, hH, ?_⟩, ?_⟩
  · refine hh2.trans ?_
    calc (4 * M ^ 2 + 6) * (1 + lam) * Real.sqrt (∫ x, u x ^ 2 ∂haar d) ≤
        (4 * M ^ 2 + 6) * (1 + lam) * Real.sqrt (1 / c) :=
          mul_le_mul_of_nonneg_left hsU (by positivity)
      _ = (4 * M ^ 2 + 6) * Real.sqrt (1 / c) * (1 + lam) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  · have hsol := eig_eq_resolvent (lam := lam) hwd hG heig
    have hF : MemLp (rhs b lam u G) 2 (haar d) := memLp_rhs hwd.b_bdd hG
    -- the `L²` bound of the right-hand side
    have hF0 : eLpNorm (rhs b lam u G) 2 (haar d) ≤ ENNReal.ofReal (K0 * (1 + lam)) := by
      refine (eLpNorm_rhs_le (q := 2) one_le_two hM0 hlam hwd.b_bdd hM hG).trans ?_
      rw [eLpNorm_two_eq hG.memLp, eLpNorm_two_eq hG.memLp_grad]
      have hYnn : 0 ≤ ∫ x, ‖G x‖ ^ 2 ∂haar d := integral_nonneg fun x => sq_nonneg _
      have e1 : ∫ x, ‖u x‖ ^ 2 ∂haar d = ∫ x, u x ^ 2 ∂haar d := by
        simp [sq_abs]
      rw [e1, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hM0,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hsY : Real.sqrt (∫ x, ‖G x‖ ^ 2 ∂haar d) ≤
          Real.sqrt (2 * M ^ 2 + 3) * (1 + lam) * Real.sqrt (∫ x, u x ^ 2 ∂haar d) := by
        calc _ ≤ Real.sqrt ((2 * M ^ 2 + 3) * (1 + lam) ^ 2 * ∫ x, u x ^ 2 ∂haar d) := by
              apply Real.sqrt_le_sqrt
              refine hY.trans ?_
              have : (2 * M ^ 2 + 3) * (1 + lam) ≤ (2 * M ^ 2 + 3) * (1 + lam) ^ 2 :=
                mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
              exact mul_le_mul_of_nonneg_right this hUnn
          _ = _ := by
              rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
                Real.sqrt_sq (by linarith)]
      have hsq : 0 ≤ Real.sqrt (∫ x, u x ^ 2 ∂haar d) := Real.sqrt_nonneg _
      calc (1 + lam) * Real.sqrt (∫ x, u x ^ 2 ∂haar d) +
          M * Real.sqrt (∫ x, ‖G x‖ ^ 2 ∂haar d) ≤
          (1 + lam) * Real.sqrt (∫ x, u x ^ 2 ∂haar d) +
          M * (Real.sqrt (2 * M ^ 2 + 3) * (1 + lam) * Real.sqrt (∫ x, u x ^ 2 ∂haar d)) := by
            gcongr
        _ = (1 + M * Real.sqrt (2 * M ^ 2 + 3)) * (1 + lam) *
            Real.sqrt (∫ x, u x ^ 2 ∂haar d) := by ring
        _ ≤ (1 + M * Real.sqrt (2 * M ^ 2 + 3)) * (1 + lam) * Real.sqrt (1 / c) := by
            gcongr
        _ = K0 * (1 + lam) := by rw [hK0def]; ring
    obtain ⟨h1, h2, h3⟩ := hcore lam b u G hM0 hlam hwd.b_bdd hM hG hsol hF0
    refine ⟨resolvent (rhs b lam u G), resolventGrad (rhs b lam u G), h1, hsol.symm,
      (grad_ae_eq_resolventGrad hF hG hsol).symm, h2, fun x => (h3 x).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
/-- The conclusion of `eigenfunction_c1_bounds_without_differentiating_drift` for one eigenpair. -/
def EigenfunctionC1Bounds {d : ℕ} (w : Torus d → ℝ) (K lam : ℝ) (e : Hw d w)
    (G : Torus d → Tangent d) : Prop :=
  (∃ H : Fin d → Fin d → Torus d → ℝ, IsWeakHessian (e : Torus d → ℝ) G H ∧
    Real.sqrt (h2NormSq (e : Torus d → ℝ) G H) ≤ K * (1 + lam)) ∧
  ∃ (v : Torus d → ℝ) (g : Torus d → Tangent d), IsC1Periodic v ∧
    v =ᵐ[haar d] (e : Torus d → ℝ) ∧ g =ᵐ[haar d] G ∧
    (∀ y : Tangent d, HasFDerivAt (fun z : Tangent d => v (torusLift z.ofLp))
      (InnerProductSpace.toDual ℝ (Tangent d) (g (torusLift y.ofLp))) y) ∧
    ∀ x, |v x| + ‖g x‖ ≤ K * (1 + lam) ^ d

/-- LIP010 for the LIP009 eigenbasis: with the orthonormal eigenbasis `e_j` of `L²(w m)` and
eigenvalues `λ_j` of `weighted_eigenbasis_and_growth`, every `e_j` is in `H²` and has a `C¹`
representative with `‖e_j‖_∞ + ‖∇e_j‖_∞ ≤ K (1+λ_j)^d`, `K` independent of `j`. -/
theorem eigenbasis_c1_bounds {d : ℕ} (hd : 0 < d) {w : Torus d → ℝ} {b : Torus d → Tangent d}
    {c C M : ℝ} (hwd : WData d w b c C) (hM : ∀ᵐ x ∂haar d, ‖b x‖ ≤ M)
    (hint : ∫ x, w x ∂haar d = 1) :
    ∃ (K : ℝ) (e : HilbertBasis ℕ ℝ (Hw d w)) (lam : ℕ → ℝ) (G : ℕ → Torus d → Tangent d),
      0 ≤ K ∧ lam 0 = 0 ∧ Monotone lam ∧ Tendsto lam atTop atTop ∧
      (∀ j, IsWeakGradient ((e j : Hw d w) : Torus d → ℝ) (G j)) ∧
      (∀ j (f : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (f : Torus d → ℝ) Y →
        weightedForm w (G j) Y = lam j * ⟪e j, f⟫_ℝ) ∧
      (∀ j : ℕ, 1 ≤ j → 4 * Real.pi ^ 2 * c / (25 * C) * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j) ∧
      ∀ j, EigenfunctionC1Bounds w K (lam j) (e j) (G j) := by
  obtain ⟨K, hK, hmain⟩ := eigenfunction_c1_bounds_without_differentiating_drift hd hwd hM
  obtain ⟨e, lam, G, _, h0, _, hmono, htend, hgrad, heig, _, hweyl⟩ :=
    DGPS.Lipschitz.WeightedSpectrum.weighted_eigenbasis_and_growth hd hwd.meas hwd.pos (Eventually.of_forall hwd.bound) hint
  refine ⟨K, e, lam, G, hK, h0, hmono, htend, hgrad, heig, hweyl, fun j => ?_⟩
  have hl : 0 ≤ lam j := h0 ▸ hmono (Nat.zero_le j)
  exact hmain (lam j) hl (e j) (G j) (e.orthonormal.norm_eq_one j) (hgrad j) (heig j)

end DGPS.Lipschitz
