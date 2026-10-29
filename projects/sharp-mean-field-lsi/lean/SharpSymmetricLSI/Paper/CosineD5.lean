import SharpSymmetricLSI.Paper.CosineD4
import SharpSymmetricLSI.Paper.CosineExpansion

/-!
# The `d`-dimensional cosine model (5): tools for the upper bound

* `dissipation_cosWd_eq`: `D(ρ) = ∫ ∑ₖ (2∂ₖ√ρ + κ√ρ · 2π(-Aₖ sin 2πxₖ + Bₖ cos 2πxₖ))²`.
* half-period shifts `x ↦ x + ½eⱼ` (`cosDhalf`) and the vanishing of odd integrals.
* the maps `x ↦ xᵢ` (`cosDproj`) and `x ↦ xᵢ + xⱼ` (`cosDsum`, `i ≠ j`) push `m` forward to the
  Haar measure of the circle (`integral_cosDsum`, by averaging over translations in `xᵢ`).
* entropy of `1 + ε cos(2π σ(x))` for such `σ` (`klDiv_comp_mode`).
-/

open MeasureTheory Set Filter InformationTheory
open scoped ENNReal Real

namespace SharpLSI

variable {d : ℕ}

/-- **The dissipation of the `d`-dimensional cosine model.** -/
theorem dissipation_cosWd_eq (κ : ℝ) {ρ : Torus d → ℝ} (hρ1 : ∫ x, ρ x ∂haar d = 1)
    (hH1 : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) :
    dissipation (fun _ => 0) (cosWd κ) ρ =
      ∫⁻ x, ENNReal.ofReal (∑ k, (2 * weakGrad (fun y => Real.sqrt (ρ y)) x k +
        κ * Real.sqrt (ρ x) * (2 * π * (-cosDA ρ k * cosDs k x + cosDB ρ k * cosDc k x))) ^ 2)
        ∂haar d := by
  set A := cosDA ρ
  set B := cosDB ρ
  set Φ : Torus d → ℝ := fun x => (fun _ : Torus d => (0 : ℝ)) x + convDens (cosWd κ) ρ x
    with hΦ
  have hlift : Φ ∘ liftT = fun z => κ * (cosDT A B z - d) := convDens_cosWd_lift κ hρ1
  have hT1 : ContDiff ℝ 1 (cosDT A B) := (contDiff_cosDT A B).of_le le_top
  have hF : ContDiff ℝ 1 (Φ ∘ liftT) := by
    rw [hlift]; exact contDiff_const.mul (hT1.sub contDiff_const)
  have hG' : ∀ᵐ x ∂haar d, ∀ k, weakGrad Φ x k =
      κ * (2 * π * (-A k * cosDs k x + B k * cosDc k x)) := by
    filter_upwards [weakGrad_ae_eq_of_contDiff hF] with x hx
    intro k
    rw [hx]
    simp only
    rw [hlift, show (fun z => κ * (cosDT A B z - d)) = fun z => κ * ((cosDT A B) z - d) from rfl,
      fderiv_const_mul ((hT1.differentiable one_ne_zero (secT x)).sub_const _),
      fderiv_sub_const]
    simp only [smul_apply, smul_eq_mul]
    rw [fderiv_cosDT, cosDs_secT, cosDc_secT]
  unfold dissipation
  rw [if_pos ⟨hH1, ⟨_, isWeakGrad_of_contDiff hF⟩⟩]
  show ∫⁻ x, ENNReal.ofReal (∑ k, (2 * weakGrad (fun y => Real.sqrt (ρ y)) x k +
    Real.sqrt (ρ x) * weakGrad Φ x k) ^ 2) ∂haar d = _
  refine lintegral_congr_ae (hG'.mono fun x hx => ?_)
  simp_rw [hx]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### Half-period shifts -/

/-- `½ eⱼ`. -/
noncomputable def cosDhalf (j : Fin d) : Torus d := Pi.single j ((2⁻¹ : ℝ) : UnitAddCircle)

theorem fourier_add_half (t : UnitAddCircle) :
    fourier 1 (t + ((2⁻¹ : ℝ) : UnitAddCircle)) = -fourier 1 t := by
  have := fourier_add_half_inv_index (T := 1) (n := 1) one_ne_zero one_pos t
  simpa using this

theorem cosDhalf_apply_ne {j k : Fin d} (h : j ≠ k) (x : Torus d) : (x + cosDhalf j) k = x k := by
  simp [cosDhalf, h.symm]

theorem cosDhalf_apply_self (j : Fin d) (x : Torus d) :
    (x + cosDhalf j) j = x j + ((2⁻¹ : ℝ) : UnitAddCircle) := by
  simp [cosDhalf]

theorem cosDc_add_half_ne {j k : Fin d} (h : j ≠ k) (x : Torus d) :
    cosDc k (x + cosDhalf j) = cosDc k x := by
  simp only [cosDc, gCos, expT, cosDproj, cosDhalf_apply_ne h]

theorem cosDs_add_half_ne {j k : Fin d} (h : j ≠ k) (x : Torus d) :
    cosDs k (x + cosDhalf j) = cosDs k x := by
  simp only [cosDs, sCos, expT, cosDproj, cosDhalf_apply_ne h]

theorem cosDc_add_half_self (j : Fin d) (x : Torus d) :
    cosDc j (x + cosDhalf j) = -cosDc j x := by
  simp only [cosDc, gCos, expT, cosDproj, cosDhalf_apply_self, fourier_add_half, Complex.neg_re]

theorem cosDs_add_half_self (j : Fin d) (x : Torus d) :
    cosDs j (x + cosDhalf j) = -cosDs j x := by
  simp only [cosDs, sCos, expT, cosDproj, cosDhalf_apply_self, fourier_add_half, Complex.neg_im]

/-- An integrand that is odd under a half-period shift has integral `0`. -/
theorem integral_eq_zero_of_half (j : Fin d) {F : Torus d → ℝ}
    (hF : ∀ x, F (x + cosDhalf j) = -F x) : ∫ x, F x ∂haar d = 0 := by
  have h1 := integral_add_right_eq_self (μ := haar d) F (cosDhalf j)
  simp only [hF, integral_neg] at h1
  linarith

/-! ### Push-forwards to the circle -/

/-- `x ↦ xᵢ + xⱼ`, as a point of `𝕋^1`. -/
def cosDsum (i j : Fin d) (x : Torus d) : Torus 1 := fun _ => x i + x j

theorem continuous_cosDsum (i j : Fin d) : Continuous (cosDsum i j) :=
  continuous_pi fun _ => (continuous_apply i).add (continuous_apply j)

theorem integral_torus1_fun {G : Torus 1 → ℝ} :
    ∫ t : UnitAddCircle, G (fun _ => t) = ∫ y, G y ∂haar 1 := by
  have h := (volume_preserving_funUnique (Fin 1) UnitAddCircle).integral_comp'
    (g := fun t => G (fun _ => t))
  simp only [MeasurableEquiv.funUnique_apply] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show G (fun _ => y 0) = G y
  congr 1; funext i; rw [Subsingleton.elim i 0]

theorem integral_cosDsum {i j : Fin d} (hij : i ≠ j) {G : Torus 1 → ℝ} (hG : Continuous G) :
    ∫ x, G (cosDsum i j x) ∂haar d = ∫ y, G y ∂haar 1 := by
  set H : Torus d → ℝ := fun x => G (cosDsum i j x)
  set K : UnitAddCircle → Torus d → ℝ := fun t x => G (fun _ => (x i + x j) + t)
  have hK : Continuous (Function.uncurry K) :=
    hG.comp (continuous_pi fun _ => (((continuous_apply i).comp continuous_snd).add
      ((continuous_apply j).comp continuous_snd)).add continuous_fst)
  have hshift : ∀ t, ∫ x, K t x ∂haar d = ∫ x, H x ∂haar d := fun t => by
    have h1 := integral_add_right_eq_self (μ := haar d) H (Pi.single i t)
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show G _ = G _
    congr 1; funext
    simp only [cosDsum, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij.symm, add_zero]
    abel
  have hcirc : ∀ x, ∫ t : UnitAddCircle, K t x = ∫ y, G y ∂haar 1 := fun x => by
    rw [← integral_torus1_fun]
    exact integral_add_left_eq_self (μ := (volume : Measure UnitAddCircle))
      (fun t => G (fun _ => t)) (x i + x j)
  have hint : Integrable (Function.uncurry K) ((volume : Measure UnitAddCircle).prod (haar d)) :=
    (BoundedContinuousFunction.mkOfCompact ⟨_, hK⟩).integrable _
  have hswap := integral_integral_swap hint
  simp_rw [hshift, hcirc] at hswap
  simpa using hswap

/-- `x ↦ xᵢ` and `x ↦ xᵢ + xⱼ` preserve the Haar measure. -/
def CosDPres (σ : Torus d → Torus 1) : Prop :=
  Continuous σ ∧ ∀ G : Torus 1 → ℝ, Continuous G → ∫ x, G (σ x) ∂haar d = ∫ y, G y ∂haar 1

theorem cosDPres_proj (k : Fin d) : CosDPres (cosDproj k) :=
  ⟨continuous_cosDproj k, fun _ hG => integral_cosDproj_haar k hG⟩

theorem cosDPres_sum {i j : Fin d} (hij : i ≠ j) : CosDPres (cosDsum i j) :=
  ⟨continuous_cosDsum i j, fun _ hG => integral_cosDsum hij hG⟩

/-! ### The entropy of `1 + ε cos(2πσ)` -/

theorem klDiv_comp_mode {σ : Torus d → Torus 1} (hσ : CosDPres σ) {ε : ℝ} (hε : |ε| ≤ 1) :
    klDiv (densMeasure (fun x => 1 + ε * gCos (σ x))) (haar d) =
      ENNReal.ofReal (∫ y, klFun (1 + ε * gCos y) ∂haar 1) := by
  have h0 : ∀ x, 0 ≤ 1 + ε * gCos (σ x) := fun x => one_add_mul_nonneg abs_gCos_le hε (σ x)
  have hc : Continuous fun y => 1 + ε * gCos y := continuous_const.add
    (continuous_const.mul continuous_gCos)
  have h1 : ∫ x, 1 + ε * gCos (σ x) ∂haar d = 1 := by
    rw [hσ.2 _ hc]; exact integral_mode continuous_gCos integral_gCos ε
  rw [klDiv_densMeasure' h0 h1, ← ofReal_integral_eq_lintegral_ofReal
    (f := fun x => klFun (1 + ε * gCos (σ x))) (integrable_torusD
      ((continuous_klFun.comp hc).comp hσ.1))
    (Eventually.of_forall fun x => klFun_nonneg (h0 x))]
  congr 1
  exact hσ.2 (fun y => klFun (1 + ε * gCos y)) (continuous_klFun.comp hc)

theorem integral_comp_mode {σ : Torus d → Torus 1} (hσ : CosDPres σ) (ε : ℝ) :
    ∫ x, 1 + ε * gCos (σ x) ∂haar d = 1 := by
  rw [hσ.2 (fun y => 1 + ε * gCos y) (continuous_const.add (continuous_const.mul continuous_gCos))]
  exact integral_mode continuous_gCos integral_gCos ε

end SharpLSI
