import DGPS.Particle.Rates
import DGPS.Particle.Sobolev
import DGPS.Particle.Symmetry
import SharpSymmetricLSI.Paper.FourierPoincare


/-!
# Bounded test LSI linearization (FIN003)

For a bounded `F ∈ H¹(P_N)` with `P_N(F) = 0` and `Var_{P_N}(F) > 0`:
`Ent_{P_N}((1+εF)²) = 2ε² Var(F) + O(|ε|³)` with the explicit error bound `10 M³ |ε|³`
(`|F| ≤ M`), uniformly for `|ε| M ≤ 1/2`; `E_N(1+εF) = ε² E_N(F)`; hence `r_N^all ≤ E_N(F)/Var(F)`
and `r_N^sym ≤ E_N(F)/Var(F)` for permutation invariant `F` (`bounded_test_lsi_linearization`).

The hypothesis "smooth" is generalised to "`F ∈ H¹(P_N)`" (smooth periodic functions are in
`H¹`); the only place where regularity enters is that constants and `1 + εF` are in `H¹(P_N)` with
weak gradient `ε ∇F`, which uses `∫ ∂_{ij} φ dm^N = 0` for smooth periodic `φ`
(`linearization_integral_particlePartial`, proved from the legacy torus FTC).
-/

open MeasureTheory
open scoped ENNReal ContDiff

namespace DGPS.FiniteN

theorem linearization_taylor {u : ℝ} (hu : |u| ≤ 1/2) :
    |(1+u)^2 * Real.log ((1+u)^2) - 2*u - 3*u^2| ≤ (19/2) * |u|^3 := by
  have h1 : |(-u)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have hl : Real.log ((1+u)^2) = 2 * Real.log (1+u) := by
    rw [Real.log_pow]; norm_num
  have hpos : 0 < 1 + u := by have := abs_le.mp hu; linarith
  set e := Real.log (1+u) - (u - u^2/2) with he
  have hlog : Real.log (1 - (-u)) = Real.log (1+u) := by ring_nf
  rw [hlog] at h
  have hau : |u| ≤ 1/2 := hu
  have hbd : |e| ≤ 2 * |u|^3 := by
    have : |(-u)|^(2+1) / (1 - |(-u)|) ≤ 2 * |u|^3 := by
      rw [abs_neg]
      rw [div_le_iff₀ (by linarith)]
      have h0 : 0 ≤ |u|^3 := by positivity
      have h5 : |u|^(2+1) = |u|^3 := by norm_num
      rw [h5]
      nlinarith [mul_nonneg h0 (by linarith : 0 ≤ 1 - 2*|u|)]
    refine le_trans ?_ this
    convert h using 2
    rw [he]; ring_nf
  have hR : (1+u)^2 * Real.log ((1+u)^2) - 2*u - 3*u^2 = -u^4 + 2*(1+u)^2*e := by
    rw [hl, he]; ring
  rw [hR]
  have hsq : (1+u)^2 ≤ 9/4 := by
    have := abs_le.mp hu; nlinarith
  have hu4 : u^4 ≤ |u|^3 / 2 := by
    have : u^4 = |u|^3 * |u| := by
      have : u^4 = |u|^4 := by rw [← abs_pow]; simp [abs_of_nonneg (by positivity : (0:ℝ) ≤ u^4)]
      rw [this]; ring
    rw [this]; have : 0 ≤ |u|^3 := by positivity
    nlinarith
  have h2 : |2*(1+u)^2*e| ≤ 9 * |u|^3 := by
    rw [abs_mul, abs_mul]
    have : |(1+u)^2| = (1+u)^2 := abs_of_nonneg (by positivity)
    rw [this]; norm_num
    have : 0 ≤ |e| := abs_nonneg _
    nlinarith [sq_nonneg (1+u)]
  have h3 : |-u^4| ≤ |u|^3/2 := by
    rw [abs_neg, abs_of_nonneg (by positivity)]; exact hu4
  calc _ ≤ |-u^4| + |2*(1+u)^2*e| := abs_add_le _ _
    _ ≤ _ := by linarith


theorem linearization_entropy_expansion {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] {F : α → ℝ} (hF : AEStronglyMeasurable F P) {M ε : ℝ}
    (hM : ∀ x, |F x| ≤ M) (hmean : ∫ x, F x ∂P = 0) (hε : |ε| * M ≤ 1/2) :
    homogeneousEntropy P (fun x => (1 + ε * F x)^2) ≠ ⊤ ∧
    |(homogeneousEntropy P (fun x => (1 + ε * F x)^2)).toReal - 2 * ε^2 * ∫ x, F x ^ 2 ∂P|
      ≤ 10 * M^3 * |ε|^3 := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure P
  obtain ⟨x0⟩ := this
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x0)
  set V := ∫ x, F x ^ 2 ∂P with hV
  have hFint : Integrable F P := Integrable.of_bound hF M (Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hM x)
  have hF2meas : AEStronglyMeasurable (fun x => F x ^ 2) P := hF.pow 2
  have hF2int : Integrable (fun x => F x ^ 2) P := Integrable.of_bound hF2meas (M^2)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2)
  have hV0 : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  have hVM : V ≤ M^2 := by
    have : ∫ x, F x ^ 2 ∂P ≤ ∫ _, M^2 ∂P := integral_mono hF2int (integrable_const _)
      (fun x => by
        have := hM x
        calc F x ^ 2 = |F x|^2 := (sq_abs _).symm
          _ ≤ M^2 := pow_le_pow_left₀ (abs_nonneg _) this 2)
    simpa using this
  -- the density
  set v : α → ℝ := fun x => (1 + ε * F x)^2 with hv
  have hvint : Integrable v P := by
    have : v = fun x => 1 + 2*ε * F x + ε^2 * F x ^ 2 := by funext x; simp only [hv]; ring
    rw [this]
    have i2 : Integrable (fun x => 2*ε * F x) P := hFint.const_mul _
    have i1 : Integrable (fun x => 1 + 2*ε * F x) P := (integrable_const _).add i2
    exact i1.add (hF2int.const_mul _)
  have hvmean : ∫ x, v x ∂P = 1 + ε^2 * V := by
    have : v = fun x => 1 + 2*ε * F x + ε^2 * F x ^ 2 := by funext x; simp only [hv]; ring
    have i2 : Integrable (fun x => 2*ε * F x) P := hFint.const_mul _
    have i1 : Integrable (fun x => 1 + 2*ε * F x) P := (integrable_const _).add i2
    have i3 : Integrable (fun x => ε^2 * F x ^ 2) P := hF2int.const_mul _
    rw [this, integral_add i1 i3, integral_add (integrable_const _) i2, integral_const_mul,
      integral_const_mul, hmean]
    simp [hV]
  have hv0 : 0 ≤ᵐ[P] v := Filter.Eventually.of_forall fun x => sq_nonneg _
  -- v log v = 2εF + 3ε²F² + T
  set T : α → ℝ := fun x => v x * Real.log (v x) - 2*ε*F x - 3*ε^2 * F x ^ 2 with hT
  have hTbd : ∀ x, |T x| ≤ (19/2) * (|ε|^3 * M^3) := by
    intro x
    have hu : |ε * F x| ≤ 1/2 := by
      rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _)) hε
    have := linearization_taylor hu
    have e1 : T x = (1 + ε * F x)^2 * Real.log ((1 + ε * F x)^2) - 2*(ε * F x) - 3*(ε * F x)^2 := by
      simp only [hT, hv]; ring
    rw [e1]
    refine this.trans ?_
    rw [abs_mul, mul_pow]
    have : |F x|^3 ≤ M^3 := pow_le_pow_left₀ (abs_nonneg _) (hM x) 3
    nlinarith [pow_nonneg (abs_nonneg ε) 3]
  have hvlogmeas : AEStronglyMeasurable (fun x => v x * Real.log (v x)) P := by
    have hc : Continuous (fun u : ℝ => (1 + ε * u)^2 * Real.log ((1 + ε * u)^2)) :=
      Real.continuous_mul_log.comp (by fun_prop : Continuous fun u : ℝ => (1 + ε * u)^2)
    exact hc.comp_aestronglyMeasurable hF
  have hTmeas : AEStronglyMeasurable T P := by
    have h1 : AEStronglyMeasurable (fun x => 2*ε*F x) P := hF.const_mul _
    have h2 : AEStronglyMeasurable (fun x => 3*ε^2 * F x ^ 2) P := hF2meas.const_mul _
    exact (hvlogmeas.sub h1).sub h2
  have hTint : Integrable T P := Integrable.of_bound hTmeas ((19/2) * (|ε|^3 * M^3))
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hTbd x)
  have hlogeq : (fun x => v x * Real.log (v x)) =
      fun x => (2*ε*F x + 3*ε^2 * F x ^ 2) + T x := by funext x; simp only [hT]; ring
  have hlogint : Integrable (fun x => v x * Real.log (v x)) P := by
    rw [hlogeq]
    exact ((hFint.const_mul (2*ε)).add (hF2int.const_mul (3*ε^2))).add hTint
  have hlogmean : ∫ x, v x * Real.log (v x) ∂P = 3 * ε^2 * V + ∫ x, T x ∂P := by
    have j1 : Integrable (fun x => 2*ε * F x) P := hFint.const_mul _
    have j2 : Integrable (fun x => 3*ε^2 * F x ^ 2) P := hF2int.const_mul _
    have j3 : Integrable (fun x => 2*ε * F x + 3*ε^2 * F x ^ 2) P := j1.add j2
    rw [hlogeq, integral_add j3 hTint, integral_add j1 j2, integral_const_mul,
      integral_const_mul, hmean]
    simp [hV]
  have hform := homogeneousEntropy_eq_formula hv0 hvint hlogint
  rw [hvmean, hlogmean] at hform
  have hEnt : homogeneousEntropy P v = ENNReal.ofReal (3 * ε^2 * V + ∫ x, T x ∂P
      - (1 + ε^2 * V) * Real.log (1 + ε^2 * V)) := hform
  refine ⟨by rw [hEnt]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [hEnt, ENNReal.toReal_ofReal']
  -- numerical estimates
  have hTI : |∫ x, T x ∂P| ≤ (19/2) * (|ε|^3 * M^3) := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := T) (C := (19/2) * (|ε|^3 * M^3))
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hTbd x)
    simpa using this
  set s := ε^2 * V with hs
  have hs0 : 0 ≤ s := by positivity
  have hεM : |ε| * M ≤ 1/2 := hε
  have hs_le : s ≤ (|ε| * M)^2 := by
    have : s ≤ ε^2 * M^2 := mul_le_mul_of_nonneg_left hVM (sq_nonneg _)
    calc s ≤ ε^2 * M^2 := this
      _ = (|ε| * M)^2 := by rw [mul_pow, sq_abs]
  have hq0 : 0 ≤ |ε| * M := mul_nonneg (abs_nonneg _) hM0
  have hcube : (|ε| * M)^3 = |ε|^3 * M^3 := by rw [mul_pow]
  have hs2 : s^2 ≤ (|ε|^3 * M^3) / 2 := by
    rw [← hcube]
    have h4 : s^2 ≤ ((|ε| * M)^2)^2 := pow_le_pow_left₀ hs0 hs_le 2
    have : ((|ε| * M)^2)^2 = (|ε| * M)^3 * (|ε| * M) := by ring
    rw [this] at h4
    have hc3 : 0 ≤ (|ε| * M)^3 := by positivity
    nlinarith
  have hlogle : Real.log (1 + s) ≤ s := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + s); linarith
  have hloglo : s / (1 + s) ≤ Real.log (1 + s) := by
    have := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + s)
    have e : 1 - (1 + s)⁻¹ = s / (1 + s) := by field_simp; ring
    linarith
  have hg1 : (1 + s) * Real.log (1 + s) ≤ s + s^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hlogle (by linarith : (0:ℝ) ≤ 1 + s)]
  have hg0 : s ≤ (1 + s) * Real.log (1 + s) := by
    have := mul_le_mul_of_nonneg_left hloglo (by linarith : (0:ℝ) ≤ 1 + s)
    have e : (1 + s) * (s / (1 + s)) = s := by field_simp
    linarith
  have hK0 : 0 ≤ |ε|^3 * M^3 := by positivity
  have hmain : |3 * ε^2 * V + ∫ x, T x ∂P - (1 + ε^2 * V) * Real.log (1 + ε^2 * V) - 2 * ε^2 * V|
      ≤ 10 * (|ε|^3 * M^3) := by
    rw [abs_le] at hTI ⊢
    constructor <;> nlinarith [hTI.1, hTI.2]
  have hrew : 10 * M^3 * |ε|^3 = 10 * (|ε|^3 * M^3) := by ring
  rw [hrew]
  rcases le_total 0 (3 * ε^2 * V + ∫ x, T x ∂P - (1 + ε^2 * V) * Real.log (1 + ε^2 * V)) with h | h
  · rw [max_eq_left h]; exact hmain
  · rw [max_eq_right h, zero_sub, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * ε^2 * V)]
    rw [abs_le] at hmain
    nlinarith [hmain.1, hmain.2]


/-- The currying continuous linear map on lifts. -/
noncomputable def linearizationCurry (d : ℕ) (N : ℕ+) :
    ((Fin N × Fin d) → ℝ) →L[ℝ] (Fin N → Fin d → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N × Fin d => ℝ) (i, j)

theorem linearization_integral_particlePartial {d : ℕ} {N : ℕ+} {φ : ParticleSpace d N → ℝ}
    (hφ : IsSmoothPeriodicParticle φ) (i : Fin N) (j : Fin d) :
    ∫ x, particlePartial i j φ x ∂particleHaar d N = 0 := by
  set C := linearizationCurry d N with hC
  set W : UnitAddTorus (Fin N × Fin d) → ℝ := fun y => φ ((particleUncurry d N).symm y)
    with hW
  have hWl : W ∘ SharpLSI.liftT = (φ ∘ particleLift) ∘ C := by
    funext z; rfl
  have hWc : ContDiff ℝ 1 (W ∘ SharpLSI.liftT) := by
    rw [hWl]
    exact (hφ.of_le (by simp)).comp C.contDiff
  have h0 := SharpLSI.integral_fderiv_torus_eq_zero hWc (Pi.single (i, j) (1:ℝ))
  have hvol : (volume : Measure (UnitAddTorus (Fin N × Fin d))) =
      Measure.pi fun _ : Fin N × Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    show Measure.pi _ = _
    congr 1
    funext k
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  have he := measurePreserving_particleUncurry d N
  rw [← hvol] at he
  have key := he.integral_comp' (fun y => fderiv ℝ (W ∘ SharpLSI.liftT) (SharpLSI.secT y)
    (Pi.single (i, j) (1:ℝ)))
  rw [h0] at key
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show _ = fderiv ℝ (W ∘ SharpLSI.liftT) (SharpLSI.secT (particleUncurry d N x)) _
  rw [hWl]
  have hd : DifferentiableAt ℝ (φ ∘ particleLift) (C (SharpLSI.secT (particleUncurry d N x))) :=
    (hφ.differentiable (by simp)) _
  rw [fderiv_comp _ hd C.differentiableAt, C.fderiv]
  have e1 : C (SharpLSI.secT (particleUncurry d N x)) = fun k => SharpLSI.secT (x k) := rfl
  have e2 : C (Pi.single (i, j) (1:ℝ)) = Pi.single i (Pi.single j (1:ℝ)) := by
    funext a b
    simp only [hC, linearizationCurry, ContinuousLinearMap.pi_apply]
    by_cases ha : a = i <;> by_cases hb : b = j <;> simp [ha, hb, Prod.ext_iff]
  rw [ContinuousLinearMap.comp_apply, e2]
  unfold particlePartial
  rw [e1]


theorem linearization_isParticleHaarWeakGradient_one_add_smul {d : ℕ} {N : ℕ+}
    {f : ParticleSpace d N → ℝ} {g : ParticleSpace d N → Fin N → Tangent d}
    (hg : IsParticleHaarWeakGradient N f g) (ε : ℝ) :
    IsParticleHaarWeakGradient N (fun x => 1 + ε * f x) (fun x => ε • g x) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (memLp_const (1 : ℝ)).add (hg.memLp.const_mul ε)
  · exact hg.memLp_grad.const_smul ε
  · intro φ hφ i j
    have hp : Integrable (particlePartial i j φ) (particleHaar d N) :=
      (hφ.memLp_top_particlePartial i j).integrable le_top
    have hfp := integrable_mul_of_memLp_two_particle hg.memLp (hφ.memLp_top_particlePartial i j)
    have hgp := integrable_mul_of_memLp_two_particle (memLp_particleCoord hg.memLp_grad i j)
      hφ.memLp_top
    have e1 : (fun x => (1 + ε * f x) * particlePartial i j φ x) =
        fun x => particlePartial i j φ x + ε * (f x * particlePartial i j φ x) := by
      funext x; ring
    rw [e1, integral_add hp (hfp.const_mul ε), integral_const_mul,
      linearization_integral_particlePartial hφ i j, hg.ibp φ hφ i j]
    have e2 : (fun x => (ε • g x) i j * φ x) = fun x => ε * (g x i j * φ x) := by
      funext x; simp [mul_assoc]
    rw [e2, integral_const_mul]
    ring

theorem linearization_memParticleH1_one_add_smul {d : ℕ} {A : InteractionData d} {N : ℕ+}
    (F : ParticleH1 A N) (ε : ℝ) : MemParticleH1 A N (fun x => 1 + ε * F x) := by
  have hg := (isParticleWeakGradient_iff A N _ _).1 (isParticleWeakGradient_particleWeakGradient F)
  exact ⟨_, (isParticleWeakGradient_iff A N _ _).2
    (linearization_isParticleHaarWeakGradient_one_add_smul hg ε)⟩

theorem linearization_particleEnergy_one_add_smul {d : ℕ} {A : InteractionData d} {N : ℕ+}
    (F : ParticleH1 A N) (ε : ℝ) :
    particleEnergy A N ⟨fun x => 1 + ε * F x, linearization_memParticleH1_one_add_smul F ε⟩ =
      ε ^ 2 * particleEnergy A N F := by
  have hg := (isParticleWeakGradient_iff A N _ _).1 (isParticleWeakGradient_particleWeakGradient F)
  have hw := (isParticleWeakGradient_iff A N _ _).2
    (linearization_isParticleHaarWeakGradient_one_add_smul hg ε)
  rw [particleEnergy_eq_of_isParticleWeakGradient
    (⟨fun x => 1 + ε * F x, linearization_memParticleH1_one_add_smul F ε⟩ : ParticleH1 A N) hw]
  unfold particleEnergy
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [particleTangentNormSq_eq]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [mul_pow]


/-- The core of the rate bound: for `ε` small, `1 + εF` is a competitor with quotient at most
`E(F) / (V - 5 M³ ε)`. -/
theorem linearization_competitor {d : ℕ} {A : InteractionData d} {N : ℕ+}
    (F : ParticleH1 A N) {M : ℝ} (hM : ∀ x, |F x| ≤ M)
    (hmean : ∫ x, F x ∂particleLaw A N = 0) {ε : ℝ} (hε0 : 0 < ε) (hεM : |ε| * M ≤ 1/2)
    (hεV : 10 * M^3 * ε < ∫ x, F x ^ 2 ∂particleLaw A N) :
    0 < particleEntropy A N ⟨fun x => 1 + ε * F x, linearization_memParticleH1_one_add_smul F ε⟩ ∧
    particleQuotient A N ⟨fun x => 1 + ε * F x, linearization_memParticleH1_one_add_smul F ε⟩ ≤
      ENNReal.ofReal (particleEnergy A N F /
        (∫ x, F x ^ 2 ∂particleLaw A N - 5 * M^3 * ε)) := by
  have : IsProbabilityMeasure (particleLaw A N) := DGPS.Particle.particleLaw_isProbabilityMeasure' A N
  set V := ∫ x, F x ^ 2 ∂particleLaw A N with hV
  have hFm : AEStronglyMeasurable F.1 (particleLaw A N) := (F.2.choose_spec.memLp).aestronglyMeasurable
  obtain ⟨hne, hbd⟩ := linearization_entropy_expansion hFm hM hmean hεM
  set Ent := homogeneousEntropy (particleLaw A N) (fun x => (1 + ε * F x)^2) with hEnt
  have hM0 : 0 ≤ M := by
    have := hM (fun _ => 0 : ParticleSpace d N)
    exact (abs_nonneg _).trans this
  set D := V - 5 * M^3 * ε with hD
  have hDpos : 0 < D := by
    have : 0 ≤ M^3 * ε := by positivity
    rw [hD]; nlinarith
  have hε3 : ε^3 = ε^2 * ε := by ring
  have habs : |ε|^3 = ε^2 * ε := by rw [abs_of_pos hε0]; ring
  have ht : 2 * ε^2 * D ≤ Ent.toReal := by
    have := (abs_le.mp hbd).1
    rw [habs] at this
    rw [hD]; nlinarith
  have htpos : 0 < Ent.toReal := lt_of_lt_of_le (by positivity) ht
  have hEntpos : 0 < Ent := by
    rcases (ENNReal.toReal_pos_iff.mp htpos) with ⟨h, _⟩; exact h
  have hEntEq : Ent = ENNReal.ofReal Ent.toReal := (ENNReal.ofReal_toReal hne).symm
  refine ⟨hEntpos, ?_⟩
  have hE0 := particleEnergy_nonneg F
  unfold particleQuotient
  rw [linearization_particleEnergy_one_add_smul]
  show ENNReal.ofReal (2 * (ε^2 * particleEnergy A N F)) / Ent ≤ _
  rw [hEntEq, ← ENNReal.ofReal_div_of_pos htpos]
  refine ENNReal.ofReal_le_ofReal ?_
  have h2 : 0 < 2 * ε^2 * D := by positivity
  calc 2 * (ε^2 * particleEnergy A N F) / Ent.toReal
      ≤ 2 * (ε^2 * particleEnergy A N F) / (2 * ε^2 * D) :=
        div_le_div_of_nonneg_left (by positivity) h2 ht
    _ = particleEnergy A N F / D := by field_simp

/-- Quantitative form of the rate bound with the second moment `∫ F²`. -/
theorem linearization_rate_le {d : ℕ} {A : InteractionData d} {N : ℕ+}
    (F : ParticleH1 A N) {M : ℝ} (hM : ∀ x, |F x| ≤ M)
    (hmean : ∫ x, F x ∂particleLaw A N = 0) (hV : 0 < ∫ x, F x ^ 2 ∂particleLaw A N) :
    particleRateAll A N ≤
      ENNReal.ofReal (particleEnergy A N F / ∫ x, F x ^ 2 ∂particleLaw A N) ∧
    (IsSymmetricParticleTest F → particleRateSym A N ≤
      ENNReal.ofReal (particleEnergy A N F / ∫ x, F x ^ 2 ∂particleLaw A N)) := by
  set V := ∫ x, F x ^ 2 ∂particleLaw A N with hVdef
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (fun _ => 0 : ParticleSpace d N))
  have hlim : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (particleEnergy A N F / (V - 5 * M^3 * ε)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (particleEnergy A N F / V))) := by
    have hc : ContinuousAt (fun ε : ℝ => ENNReal.ofReal (particleEnergy A N F / (V - 5 * M^3 * ε))) 0 := by
      refine ENNReal.continuous_ofReal.continuousAt.comp ?_
      refine ContinuousAt.div continuousAt_const (by fun_prop) ?_
      simp; exact hV.ne'
    have := hc.tendsto
    simpa using this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < ε ∧ |ε| * M ≤ 1/2 ∧ 10 * M^3 * ε < V := by
    have hb : (0:ℝ) < min (1 / (2 * M + 1)) (V / (10 * M^3 + 1)) :=
      lt_min (by positivity) (by positivity)
    filter_upwards [Ioo_mem_nhdsGT hb] with ε hε
    obtain ⟨h0, h1⟩ := hε
    have h1a := h1.trans_le (min_le_left _ _)
    have h1b := h1.trans_le (min_le_right _ _)
    refine ⟨h0, ?_, ?_⟩
    · rw [abs_of_pos h0]
      rw [lt_div_iff₀ (by positivity)] at h1a
      nlinarith
    · rw [lt_div_iff₀ (by positivity)] at h1b
      nlinarith [mul_pos h0 (by norm_num : (0:ℝ) < 1)]
  constructor
  · refine ge_of_tendsto hlim ?_
    filter_upwards [hev] with ε ⟨h0, h1, h2⟩
    obtain ⟨hp, hq⟩ := linearization_competitor F hM hmean h0 h1 h2
    exact (particleRateAll_le_quotient A N _ hp).trans hq
  · intro hs
    refine ge_of_tendsto hlim ?_
    filter_upwards [hev] with ε ⟨h0, h1, h2⟩
    obtain ⟨hp, hq⟩ := linearization_competitor F hM hmean h0 h1 h2
    have hs' : IsSymmetricParticleTest
        (⟨fun x => 1 + ε * F x, linearization_memParticleH1_one_add_smul F ε⟩ : ParticleH1 A N) := by
      intro σ
      filter_upwards [hs σ] with x hx
      simp only [Function.comp_apply] at hx ⊢
      show 1 + ε * F (permuteParticles σ x) = 1 + ε * F x
      rw [hx]
    exact (particleRateSym_le_quotient A N _ hs' hp).trans hq

/-- FIN003: bounded test LSI linearization.  For a bounded `F ∈ H¹(P_N)` (in particular any bounded
smooth `F`) with `P_N(F) = 0`, `Var(F) > 0` and `|F| ≤ M`:
* `Ent_{P_N}((1+εF)²) = 2ε² Var(F) + O(|ε|³)`, with explicit error `≤ 10 M³ |ε|³`, uniformly for
  `|ε| M ≤ 1/2` (and the entropy is finite);
* `1 + εF ∈ H¹(P_N)` with `E(1+εF) = ε² E(F)`;
* hence `r_N^all ≤ E(F)/Var(F)`, and `r_N^sym ≤ E(F)/Var(F)` when `F` is permutation invariant. -/
theorem bounded_test_lsi_linearization {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (F : ParticleH1 A N) (M : ℝ) (hM : ∀ x, |F x| ≤ M)
    (hmean : ∫ x, F x ∂particleLaw A N = 0)
    (hvar : 0 < ProbabilityTheory.variance F.1 (particleLaw A N)) :
    (∀ ε : ℝ, |ε| * M ≤ 1/2 →
      homogeneousEntropy (particleLaw A N) (fun x => (1 + ε * F x)^2) ≠ ⊤ ∧
      |(homogeneousEntropy (particleLaw A N) (fun x => (1 + ε * F x)^2)).toReal
          - 2 * ε^2 * ProbabilityTheory.variance F.1 (particleLaw A N)| ≤ 10 * M^3 * |ε|^3) ∧
    (∀ ε : ℝ, ∃ h : MemParticleH1 A N (fun x => 1 + ε * F x),
      particleEnergy A N ⟨fun x => 1 + ε * F x, h⟩ = ε^2 * particleEnergy A N F) ∧
    particleRateAll A N ≤
      ENNReal.ofReal (particleEnergy A N F / ProbabilityTheory.variance F.1 (particleLaw A N)) ∧
    (IsSymmetricParticleTest F → particleRateSym A N ≤
      ENNReal.ofReal (particleEnergy A N F / ProbabilityTheory.variance F.1 (particleLaw A N))) := by
  have : IsProbabilityMeasure (particleLaw A N) := DGPS.Particle.particleLaw_isProbabilityMeasure' A N
  have hFm : AEStronglyMeasurable F.1 (particleLaw A N) := (F.2.choose_spec.memLp).aestronglyMeasurable
  have hvarEq : ProbabilityTheory.variance F.1 (particleLaw A N) = ∫ x, F x ^ 2 ∂particleLaw A N :=
    ProbabilityTheory.variance_of_integral_eq_zero hFm.aemeasurable hmean
  rw [hvarEq] at hvar ⊢
  obtain ⟨h1, h2⟩ := linearization_rate_le F hM hmean hvar
  exact ⟨fun ε hε => linearization_entropy_expansion hFm hM hmean hε,
    fun ε => ⟨linearization_memParticleH1_one_add_smul F ε,
      linearization_particleEnergy_one_add_smul F ε⟩, h1, h2⟩

end DGPS.FiniteN
