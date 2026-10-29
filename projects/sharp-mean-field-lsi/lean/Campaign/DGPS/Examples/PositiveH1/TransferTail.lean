import Mathlib
import DGPS.Examples.PositiveH1.TransferRough

/-!
# Uniform force tail form bound (H1030)

With `κ = 1/100`, `α_M = κ (2 A_M + B_M) → 0`, the tail potential `T_{N,M} = U_N - U_{N,M}` has
weak gradient `∇T_{N,M} = (κ/N) ∑_{j≠i} Q_M'(xᵢ - xⱼ)` with `Q_M = R - R_M`, `Q_M' = R' - R_M'`,
and for all `N ≥ 1`, `ψ ∈ H¹(m^N)`:
`‖ψ ∇T_{N,M}‖₂ ≤ α_M ‖∇ψ‖₂ + κ B_M ‖ψ‖₂`
(force multiplier closure applied to `Q_M`, with `‖Q_M‖_∞ ≤ A_M`, `‖Q_M'‖₂ ≤ B_M`).
For `f ∈ H¹(P_N)` the ground state map `ψ = f √p_N` of H1028 gives
`∫ f² |∇T_{N,M}|² dP_N ≤ 16 α_M² (E_N(f) + ‖f‖₂²)`.
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
open DGPS
open DGPS.Examples.PositiveH1.Particle DGPS.Examples.PositiveH1.Fourier
open DGPS.Analysis.ForceMultiplierH1

namespace DGPS.Examples.PositiveH1.Transfer

/-- The tail kernel `Q_M = R - R_M`. -/
noncomputable def h1030_Q (M : ℕ) (x : Torus 1) : ℝ := R x - RM M x

/-- The weak derivative `Q_M' = R' - R_M'` of the tail kernel. -/
noncomputable def h1030_dQ (M : ℕ) (x : Torus 1) : ℝ := dR x - dRM M x

/-- The tail force `x ↦ (κ/N) ∑_{j≠i} Q_M'(xᵢ - xⱼ)`. -/
noncomputable def h1030_tailForce (κ : ℝ) (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) (i : Fin N) :
    Tangent 1 :=
  (κ / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
    (EuclideanSpace.single (0 : Fin 1) (h1030_dQ M (x i - x j)) : Tangent 1)

/-- The quantity `α_M = κ (2 A_M + B_M)` at `κ = 1/100`. -/
noncomputable def h1030_alpha (M : ℕ) : ℝ := (1 / 100) * (2 * tailA M + B M)

theorem h1030_continuous_Q (M : ℕ) : Continuous (h1030_Q M) :=
  continuous_R.sub (continuous_RM M)

theorem h1030_weak_gradient_Q (M : ℕ) :
    IsWeakGradient (h1030_Q M)
      (fun x => (EuclideanSpace.single (0 : Fin 1) (h1030_dQ M x) : Tangent 1)) := by
  have h := sub_wg weak_gradient_R (isSmoothPeriodic_RM M).isWeakGradient
  have e : (fun x => (EuclideanSpace.single (0 : Fin 1) (dR x) : Tangent 1) -
      smoothGrad (RM M) x) =
      fun x => (EuclideanSpace.single (0 : Fin 1) (h1030_dQ M x) : Tangent 1) := by
    funext x
    ext j
    fin_cases j
    simp [smoothGrad, coordPartial_RM, h1030_dQ]
  rw [e] at h
  exact h

theorem h1030_Q_bound (M : ℕ) (x : Torus 1) : |h1030_Q M x| ≤ tailA M :=
  abs_R_sub_RM_le M x

theorem h1030_Q_zero (M : ℕ) : h1030_Q M 0 = tailA M := R_sub_RM_zero M

theorem h1030_Q_neg (M : ℕ) (x : Torus 1) : h1030_Q M (-x) = h1030_Q M x := by
  unfold h1030_Q RM
  rw [R_neg]
  simp only [cosMode_neg]

theorem h1030_tailA_nonneg (M : ℕ) : 0 ≤ tailA M := by
  unfold tailA
  exact tsum_nonneg fun n => by
    split_ifs
    · exact a_nonneg n
    · exact le_rfl

theorem h1030_eLpNorm_Q_le (M : ℕ) : (eLpNorm (h1030_Q M) ⊤ (haar 1)).toReal ≤ tailA M := by
  have h : eLpNormEssSup (h1030_Q M) (haar 1) ≤ ENNReal.ofReal (tailA M) :=
    eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact h1030_Q_bound M x)
  rw [eLpNorm_exponent_top]
  · exact ENNReal.toReal_le_of_le_ofReal (h1030_tailA_nonneg M) h
  · exact (h1030_continuous_Q M).aestronglyMeasurable

theorem h1030_summable_tailSeries_zero : Summable (tailSeries (3 / 2) 0) := by
  refine Summable.of_nonneg_of_le (tailSeries_nonneg _ _) (fun n => ?_)
    (Real.summable_nat_rpow.2 (show (-(3 / 2 : ℝ)) < -1 by norm_num))
  unfold tailSeries
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem h1030_B_one_le_zero : B 1 ≤ B 0 := by
  rw [B_eq, B_eq]
  refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact (tailSeries_bound (p := 3 / 2) (by norm_num) le_rfl).1.tsum_le_tsum
    (fun n => tailSeries_anti (p := 3 / 2) (Nat.zero_le 1) n)
    h1030_summable_tailSeries_zero

theorem h1030_integral_sq_dQ_le (M : ℕ) :
    ∫ x, h1030_dQ M x ^ 2 ∂haar 1 ≤ B M ^ 2 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have e : ∀ x, h1030_dQ 0 x = dR x - dRM 1 x := fun x => by simp [h1030_dQ, dRM]
    simp_rw [e]
    rw [integral_sq_dR_sub (le_refl 1)]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1030_B_one_le_zero 2
  · simp_rw [h1030_dQ]
    rw [integral_sq_dR_sub hM]

theorem h1030_sqrt_integral_sq_dQ_le (M : ℕ) :
    Real.sqrt (∫ t, ‖(EuclideanSpace.single (0 : Fin 1) (h1030_dQ M t) : Tangent 1)‖ ^ 2
      ∂haar 1) ≤ B M := by
  have h1 : ∫ t, ‖(EuclideanSpace.single (0 : Fin 1) (h1030_dQ M t) : Tangent 1)‖ ^ 2 ∂haar 1 =
      ∫ t, h1030_dQ M t ^ 2 ∂haar 1 := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp
  rw [h1]
  exact Real.sqrt_le_iff.2 ⟨Real.sqrt_nonneg _, h1030_integral_sq_dQ_le M⟩

theorem h1030_gTorus_tail_eq (κ : ℝ) (N : ℕ+) (M : ℕ) (y : Torus (N : ℕ)) :
    gTorus N (h1030_tailForce κ N M) y = κ • forceB (h1030_dQ M) y := by
  ext j
  simp only [gTorus, h1030_tailForce, forceB_apply, PiLp.smul_apply, smul_eq_mul]
  have e : ∀ k, ((EuclideanSpace.single (0 : Fin 1) (h1030_dQ M ((EE N).symm y j - (EE N).symm y k)) :
      Tangent 1) 0) = h1030_dQ M (fun _ => y j - y k) := by
    intro k
    have : ((EE N).symm y j - (EE N).symm y k : Torus 1) = fun _ => y j - y k := by
      funext i; rfl
    rw [this]; simp
  simp only [WithLp.ofLp_sum, Finset.sum_apply, e]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem h1030_multiplier_torus (κ : ℝ) (hκ : 0 ≤ κ) (N : ℕ+) (M : ℕ) {ψ : Torus (N : ℕ) → ℝ}
    {g : Torus (N : ℕ) → Tangent (N : ℕ)} (hψ : IsWeakGradient ψ g) :
    MemLp (fun y => ψ y • gTorus N (h1030_tailForce κ N M) y) 2 (haar (N : ℕ)) ∧
    Real.sqrt (∫ y, ‖ψ y • gTorus N (h1030_tailForce κ N M) y‖ ^ 2 ∂haar (N : ℕ)) ≤
      κ * (2 * tailA M + B M) * Real.sqrt (∫ y, ‖g y‖ ^ 2 ∂haar (N : ℕ)) +
        κ * B M * Real.sqrt (∫ y, ψ y ^ 2 ∂haar (N : ℕ)) := by
  have hQ : MemH1 (h1030_Q M) := ⟨_, h1030_weak_gradient_Q M⟩
  have hψ' : MemH1 ψ := ⟨g, hψ⟩
  obtain ⟨hmem, hle, hle2⟩ := full_h1_force_multiplier_closure (N : ℕ) N.pos (h1030_Q M) hQ ψ hψ'
    (L := (eLpNorm (h1030_Q M) ⊤ (haar 1)).toReal)
    (β := Real.sqrt (∫ t, ‖weakGradient (h1030_Q M) hQ t‖ ^ 2 ∂haar 1))
    (u := Real.sqrt (∫ x, ψ x ^ 2 ∂haar (N : ℕ)))
    (v := Real.sqrt (∫ x, ‖weakGradient ψ hψ' x‖ ^ 2 ∂haar (N : ℕ))) rfl rfl rfl rfl
  have hwg : weakGradient ψ hψ' =ᵐ[haar (N : ℕ)] g := weakGradient_ae_eq hψ
  have hv : (∫ x, ‖weakGradient ψ hψ' x‖ ^ 2 ∂haar (N : ℕ)) = ∫ x, ‖g x‖ ^ 2 ∂haar (N : ℕ) :=
    integral_congr_ae (by filter_upwards [hwg] with x hx; rw [hx])
  have hwR : weakGradient (h1030_Q M) hQ =ᵐ[haar 1]
      fun x => (EuclideanSpace.single (0 : Fin 1) (h1030_dQ M x) : Tangent 1) :=
    weakGradient_ae_eq (h1030_weak_gradient_Q M)
  have hb : (∫ t, ‖weakGradient (h1030_Q M) hQ t‖ ^ 2 ∂haar 1) =
      ∫ t, ‖(EuclideanSpace.single (0 : Fin 1) (h1030_dQ M t) : Tangent 1)‖ ^ 2 ∂haar 1 :=
    integral_congr_ae (by filter_upwards [hwR] with x hx; rw [hx])
  rw [hv, hb] at hle hle2
  have hβ := h1030_sqrt_integral_sq_dQ_le M
  have hL := h1030_eLpNorm_Q_le M
  have hu0 := Real.sqrt_nonneg (∫ x, ψ x ^ 2 ∂haar (N : ℕ))
  have hv0 := Real.sqrt_nonneg (∫ x, ‖g x‖ ^ 2 ∂haar (N : ℕ))
  have hae : (fun x => ψ x • forceB (fun t => weakGradient (h1030_Q M) hQ t 0) x) =ᵐ[haar (N : ℕ)]
      fun x => ψ x • forceB (h1030_dQ M) x := by
    have hall : ∀ᵐ x ∂haar (N : ℕ), ∀ i j : Fin (N : ℕ), i ≠ j →
        weakGradient (h1030_Q M) hQ (fun _ : Fin 1 => x i - x j) 0 =
          h1030_dQ M (fun _ : Fin 1 => x i - x j) := by
      rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
      by_cases hij : i = j
      · exact Eventually.of_forall fun x h => absurd hij h
      · have h0 : (fun t => weakGradient (h1030_Q M) hQ t 0) =ᵐ[haar 1] h1030_dQ M := by
          filter_upwards [hwR] with t ht; rw [ht]; simp
        have := (DGPS.Analysis.ForceMultiplier.measurePreserving_pairDiff
          hij).quasiMeasurePreserving.ae_eq_comp h0
        filter_upwards [this] with x hx _ using hx
    filter_upwards [hall] with x hx
    congr 1
    ext i
    simp only [forceB_apply]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    exact hx i j (Finset.ne_of_mem_erase hj).symm
  have hF : MemLp (fun x => ψ x • forceB (h1030_dQ M) x) 2 (haar (N : ℕ)) := hmem.ae_eq hae
  have hG : ∀ y, ψ y • gTorus N (h1030_tailForce κ N M) y = κ • (ψ y • forceB (h1030_dQ M) y) := by
    intro y; rw [h1030_gTorus_tail_eq, smul_comm]
  simp_rw [hG]
  refine ⟨hF.const_smul κ, ?_⟩
  have hT := DGPS.Analysis.ForceMultiplierH1.toReal_eLpNorm_two (hF.const_smul κ)
  have hE := eLpNorm_const_smul (c := κ) (f := fun y => ψ y • forceB (h1030_dQ M) y) 2
    (haar (N : ℕ))
  calc √(∫ y, ‖κ • (ψ y • forceB (h1030_dQ M) y)‖ ^ 2 ∂haar (N : ℕ))
      = (eLpNorm (κ • fun y => ψ y • forceB (h1030_dQ M) y) 2 (haar (N : ℕ))).toReal := hT.symm
    _ = κ * (eLpNorm (fun x => ψ x • forceB (fun t => weakGradient (h1030_Q M) hQ t 0) x) 2
          (haar (N : ℕ))).toReal := by
        rw [hE, ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs, abs_of_nonneg hκ,
          eLpNorm_congr_ae hae]
    _ ≤ _ := ?_
  have h1 := hle.trans hle2
  have h2 : (2 * (eLpNorm (h1030_Q M) ⊤ (haar 1)).toReal +
      √(∫ t, ‖(EuclideanSpace.single (0 : Fin 1) (h1030_dQ M t) : Tangent 1)‖ ^ 2 ∂haar 1)) *
        √(∫ x, ‖g x‖ ^ 2 ∂haar (N : ℕ)) +
      √(∫ t, ‖(EuclideanSpace.single (0 : Fin 1) (h1030_dQ M t) : Tangent 1)‖ ^ 2 ∂haar 1) *
        √(∫ x, ψ x ^ 2 ∂haar (N : ℕ)) ≤
      (2 * tailA M + B M) * √(∫ x, ‖g x‖ ^ 2 ∂haar (N : ℕ)) +
        B M * √(∫ x, ψ x ^ 2 ∂haar (N : ℕ)) := by
    gcongr
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hκ]

theorem h1030_multiplier_particle (κ : ℝ) (hκ : 0 ≤ κ) (N : ℕ+) (M : ℕ)
    {ψ : ParticleSpace 1 N → ℝ} {g : ParticleSpace 1 N → Fin N → Tangent 1}
    (hg : IsParticleHaarWeakGradient N ψ g) :
    MemLp (fun x i => ψ x • h1030_tailForce κ N M x i) 2 (particleHaar 1 N) ∧
    Real.sqrt (∫ x, particleTangentNormSq (fun i => ψ x • h1030_tailForce κ N M x i)
        ∂particleHaar 1 N) ≤
      κ * (2 * tailA M + B M) *
          Real.sqrt (∫ x, particleTangentNormSq (g x) ∂particleHaar 1 N) +
        κ * B M * Real.sqrt (∫ x, ψ x ^ 2 ∂particleHaar 1 N) := by
  obtain ⟨hmem, hb⟩ := h1030_multiplier_torus κ hκ N M (transport_weak N hg)
  have hG : ∀ x i, (ψ x • h1030_tailForce κ N M x i) = (EuclideanSpace.single (0 : Fin 1)
      ((ψ ((EE N).symm (EE N x)) • gTorus N (h1030_tailForce κ N M) (EE N x)) i) : Tangent 1) := by
    intro x i
    ext j
    fin_cases j
    simp [gTorus]
  refine ⟨memLp_particle_of_torus N hmem hG, ?_⟩
  rw [integral_normSq_particle N
    (v := fun y => ψ ((EE N).symm y) • gTorus N (h1030_tailForce κ N M) y)
    (G := fun x i => ψ x • h1030_tailForce κ N M x i) hG, ← integral_gTorus N g,
    ← integral_sq_EE N ψ]
  exact hb

theorem h1030_summable_tail_cos (M : ℕ) (x : Torus 1) :
    Summable fun n : ℕ => if M < n then a n * cosMode n x else 0 :=
  Summable.of_norm_bounded a_summable (fun n => by
    split_ifs
    · exact term_abs_le n x
    · simpa using a_nonneg n)

theorem h1030_sum_Q (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) :
    ∑ i, ∑ j, h1030_Q M (x i - x j) =
      N * ∑' n : ℕ, if M < n then a n * ‖Z N n x‖ ^ 2 else 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have e1 : ∀ i, ∑ j, h1030_Q M (x i - x j) =
      ∑' n : ℕ, ∑ j, (if M < n then a n * cosMode n (x i - x j) else 0) := by
    intro i
    simp_rw [h1030_Q, R_sub_RM]
    exact (Summable.tsum_finsetSum (fun j _ => h1030_summable_tail_cos M _)).symm
  simp_rw [e1]
  rw [← Summable.tsum_finsetSum (fun i _ => summable_sum
    (fun j _ => h1030_summable_tail_cos M _))]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  by_cases hn : M < n
  · simp only [hn, ite_true]
    simp_rw [← Finset.mul_sum]
    rw [← normSq_S_cos, norm_Z_sq]
    field_simp
  · simp [hn]

theorem h1030_tailT_eq (κ : ℝ) (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) :
    tailT κ N M x = ∑ i, (fun _ : Torus 1 => κ * tailA M / 2) (x i) +
      (1 / (2 * (N : ℝ))) * ∑ i, ∑ j,
        (fun a b : Torus 1 => κ * (h1030_Q M (a - b) - h1030_Q M 0)) (x i) (x j) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hS := h1030_sum_Q N M x
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hS, h1030_Q_zero]
  unfold tailT
  field_simp
  ring

theorem h1030_weak_tail_gradient (κ : ℝ) (N : ℕ+) (M : ℕ) :
    IsParticleHaarWeakGradient N (tailT κ N M) (h1030_tailForce κ N M) := by
  set F : Torus 1 → Torus 1 → ℝ := fun x y => κ * (h1030_Q M (x - y) - h1030_Q M 0) with hFdef
  set B' : Torus 1 → Torus 1 → Tangent 1 :=
    fun x y => κ • (EuclideanSpace.single (0 : Fin 1) (h1030_dQ M (x - y)) : Tangent 1) with hBdef
  have hsymm : ∀ x y, F x y = F y x := fun x y => by
    simp only [hFdef]; rw [show y - x = -(x - y) from (neg_sub x y).symm, h1030_Q_neg]
  have hFc : Continuous (Function.uncurry F) :=
    continuous_const.mul (((h1030_continuous_Q M).comp (continuous_fst.sub continuous_snd)).sub
      continuous_const)
  have hBmem : ∀ i j : Fin N, i ≠ j →
      MemLp (fun x : ParticleSpace 1 N => B' (x i) (x j)) 2 (particleHaar 1 N) := by
    intro i j hij
    exact ((h1030_weak_gradient_Q M).memLp_grad.const_smul κ).comp_measurePreserving
      (measurePreserving_pairDiff hij)
  have hB : ∀ y, IsWeakGradient (fun x => F x y) (fun x => B' x y) := by
    intro y
    have h1 := ((isWeakGradient_translate (h1030_weak_gradient_Q M) y).add
      (Lipschitz.df_isWeakGradient_const (d := 1) (-h1030_Q M 0))).smul κ
    have e1 : (fun x => F x y) = fun x => κ * (h1030_Q M (x - y) + -h1030_Q M 0) := by
      funext x; simp [hFdef, sub_eq_add_neg]
    have e2 : (fun x => B' x y) = fun x => κ •
        ((EuclideanSpace.single (0 : Fin 1) (h1030_dQ M (x - y)) : Tangent 1) + 0) := by
      funext x; simp [hBdef]
    rw [e1, e2]
    exact h1
  have hV : IsWeakGradient (fun _ : Torus 1 => κ * tailA M / 2) (fun _ => 0) :=
    Lipschitz.df_isWeakGradient_const _
  have hδ : IsWeakGradient (fun x => F x x) (fun _ => 0) := by
    have : (fun x => F x x) = fun _ => (0 : ℝ) := by funext x; simp [hFdef]
    rw [this]; exact isWeakGradient_zero
  have hcore := core_rough (V := fun _ : Torus 1 => κ * tailA M / 2) (gV := fun _ => 0)
    (gδ := fun _ => 0) hsymm hFc N hBmem hB hV hδ
  have hfun : (fun (x : ParticleSpace 1 N) (i : Fin N) => (0 : Tangent 1) +
      (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B' (x i) (x j) +
        (2 * (N : ℝ))⁻¹ • (0 : Tangent 1)) = h1030_tailForce κ N M := by
    funext x i
    simp only [h1030_tailForce, hBdef, smul_zero, zero_add, add_zero, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_eq_mul_inv, mul_comm κ]
  rw [hfun] at hcore
  have hT : tailT κ N M = fun x : ParticleSpace 1 N =>
      ∑ i, (fun _ : Torus 1 => κ * tailA M / 2) (x i) +
        (1 / (2 * (N : ℝ))) * ∑ i, ∑ j, F (x i) (x j) := funext (h1030_tailT_eq κ N M)
  rw [hT]
  exact hcore

theorem h1030_psi_bound (N : ℕ+) (M : ℕ) {G : ParticleSpace 1 N → Fin N → Tangent 1}
    (hG : IsParticleHaarWeakGradient N (tailT (1 / 100) N M) G)
    {ψ : ParticleSpace 1 N → ℝ} {g : ParticleSpace 1 N → Fin N → Tangent 1}
    (hg : IsParticleHaarWeakGradient N ψ g) :
    MemLp (fun x i => ψ x • G x i) 2 (particleHaar 1 N) ∧
    Real.sqrt (∫ x, particleTangentNormSq (fun i => ψ x • G x i) ∂particleHaar 1 N) ≤
      h1030_alpha M * Real.sqrt (∫ x, particleTangentNormSq (g x) ∂particleHaar 1 N) +
        (1 / 100) * B M * Real.sqrt (∫ x, ψ x ^ 2 ∂particleHaar 1 N) := by
  have hae : G =ᵐ[particleHaar 1 N] h1030_tailForce (1 / 100) N M :=
    hG.ae_eq (h1030_weak_tail_gradient (1 / 100) N M)
  have hae' : (fun x i => ψ x • G x i) =ᵐ[particleHaar 1 N]
      fun x i => ψ x • h1030_tailForce (1 / 100) N M x i := by
    filter_upwards [hae] with x hx
    funext i
    rw [hx]
  obtain ⟨hm, hb⟩ := h1030_multiplier_particle (1 / 100) (by norm_num) N M hg
  refine ⟨hm.ae_eq hae'.symm, ?_⟩
  have : ∫ x, particleTangentNormSq (fun i => ψ x • G x i) ∂particleHaar 1 N =
      ∫ x, particleTangentNormSq (fun i => ψ x • h1030_tailForce (1 / 100) N M x i)
        ∂particleHaar 1 N := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  rw [this]
  unfold h1030_alpha
  exact hb

theorem uniform_force_tail_form_bound :
    Tendsto h1030_alpha atTop (𝓝 0) ∧ ∀ (N : ℕ+) (M : ℕ),
      (∃ G, IsParticleHaarWeakGradient N (tailT (1 / 100) N M) G) ∧
      ∀ G, IsParticleHaarWeakGradient N (tailT (1 / 100) N M) G →
        (∀ (ψ : ParticleSpace 1 N → ℝ) (g : ParticleSpace 1 N → Fin N → Tangent 1),
            IsParticleHaarWeakGradient N ψ g →
          MemLp (fun x i => ψ x • G x i) 2 (particleHaar 1 N) ∧
          Real.sqrt (∫ x, particleTangentNormSq (fun i => ψ x • G x i) ∂particleHaar 1 N) ≤
            h1030_alpha M * Real.sqrt (∫ x, particleTangentNormSq (g x) ∂particleHaar 1 N) +
              (1 / 100) * B M * Real.sqrt (∫ x, ψ x ^ 2 ∂particleHaar 1 N)) ∧
        (∀ f : ParticleH1 (kernelData (1 / 100)) N,
          ∫ x, f x ^ 2 * particleTangentNormSq (G x) ∂particleLaw (kernelData (1 / 100)) N ≤
            16 * h1030_alpha M ^ 2 *
              (particleEnergy (kernelData (1 / 100)) N f +
                ∫ x, f x ^ 2 ∂particleLaw (kernelData (1 / 100)) N)) := by
  refine ⟨?_, fun N M => ⟨⟨_, h1030_weak_tail_gradient (1 / 100) N M⟩, fun G hG => ⟨?_, ?_⟩⟩⟩
  · have h := ((tendsto_tailA.const_mul 2).add tendsto_B).const_mul (1 / 100 : ℝ)
    rw [show (1 / 100 : ℝ) * (2 * 0 + 0) = 0 by norm_num] at h
    exact h
  · intro ψ g hg
    exact h1030_psi_bound N M hG hg
  · intro f
    have hα0 : 0 ≤ h1030_alpha M := by
      unfold h1030_alpha
      have := h1030_tailA_nonneg M
      have : 0 ≤ B M := Real.sqrt_nonneg _
      positivity
    have hκB : (1 / 100 : ℝ) * B M ≤ h1030_alpha M := by
      unfold h1030_alpha
      have := h1030_tailA_nonneg M
      nlinarith
    obtain ⟨-, hW, -, h4⟩ := ground_state_map_on_every_rough_particle_test N f.1 f.2
      (particleWeakGradient f) (isParticleWeakGradient_particleWeakGradient f)
    set ψ : ParticleSpace 1 N → ℝ := fun x => f x * Real.sqrt (p (1 / 100) N x) with hψ
    set g' : ParticleSpace 1 N → Fin N → Tangent 1 := fun x i =>
      Real.sqrt (p (1 / 100) N x) • particleWeakGradient f x i -
        ((1 / 2 : ℝ) * (f x * Real.sqrt (p (1 / 100) N x))) • roughForce (1 / 100) N x i with hg'
    obtain ⟨-, hb⟩ := h1030_psi_bound N M hG hW
    set E := particleEnergy (kernelData (1 / 100)) N f with hE
    set u2 := ∫ x, f x ^ 2 ∂particleLaw (kernelData (1 / 100)) N with hu2
    have hE0 : 0 ≤ E := particleEnergy_nonneg f
    have hu0 : 0 ≤ u2 := integral_nonneg fun x => sq_nonneg _
    have eψ : ∫ x, ψ x ^ 2 ∂particleHaar 1 N = u2 := by
      rw [hu2, DGPS.Particle.integral_particleLaw]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [density_eq, hψ]
      rw [mul_pow, Real.sq_sqrt (p_nonneg' (1 / 100) N x)]
      ring
    have eX : ∫ x, f x ^ 2 * particleTangentNormSq (G x) ∂particleLaw (kernelData (1 / 100)) N =
        ∫ x, particleTangentNormSq (fun i => ψ x • G x i) ∂particleHaar 1 N := by
      rw [DGPS.Particle.integral_particleLaw]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show particleDensity (kernelData (1 / 100)) N x * (f x ^ 2 * particleTangentNormSq (G x)) =
        particleTangentNormSq (ψ x • G x)
      have hsm : particleTangentNormSq (ψ x • G x) = ψ x ^ 2 * particleTangentNormSq (G x) := by
        simp [particleTangentNormSq, norm_smul, mul_pow, Finset.mul_sum]
      rw [hsm]
      simp only [density_eq, hψ]
      rw [mul_pow, Real.sq_sqrt (p_nonneg' (1 / 100) N x)]
      ring
    rw [eX]
    rw [eψ] at hb
    set S := ∫ x, particleTangentNormSq (fun i => ψ x • G x i) ∂particleHaar 1 N with hS
    set a := ∫ x, particleTangentNormSq (g' x) ∂particleHaar 1 N with ha
    have ha0 : 0 ≤ a := integral_nonneg fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have ha1 : a ≤ 8 * E + 2 * u2 := h4
    have hS0 : 0 ≤ S := integral_nonneg fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hsa := Real.sq_sqrt ha0
    have ht := Real.sq_sqrt hu0
    have hsa0 := Real.sqrt_nonneg a
    have ht0 := Real.sqrt_nonneg u2
    have hb2 : Real.sqrt S ≤ h1030_alpha M * (Real.sqrt a + Real.sqrt u2) := by
      have := mul_le_mul_of_nonneg_right hκB ht0
      nlinarith
    have hS2 : S ≤ (h1030_alpha M * (Real.sqrt a + Real.sqrt u2)) ^ 2 := by
      calc S = Real.sqrt S ^ 2 := (Real.sq_sqrt hS0).symm
        _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hb2 2
    have hα2 : 0 ≤ h1030_alpha M ^ 2 := sq_nonneg _
    have h5 : (Real.sqrt a + Real.sqrt u2) ^ 2 ≤ 2 * (a + u2) := by
      nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt u2)]
    have h6 : (h1030_alpha M * (Real.sqrt a + Real.sqrt u2)) ^ 2 ≤
        h1030_alpha M ^ 2 * (2 * (a + u2)) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left h5 hα2
    have h7 : h1030_alpha M ^ 2 * (2 * (a + u2)) ≤ 16 * h1030_alpha M ^ 2 * (E + u2) := by
      have : 2 * (a + u2) ≤ 16 * (E + u2) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this hα2]
    linarith

end DGPS.Examples.PositiveH1.Transfer
