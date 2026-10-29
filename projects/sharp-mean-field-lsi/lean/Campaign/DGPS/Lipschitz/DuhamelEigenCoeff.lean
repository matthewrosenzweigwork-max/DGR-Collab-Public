import DGPS.Lipschitz.DuhamelSemigroup
import DGPS.Lipschitz.WeightedSpectrum

/-!
# LIP007d2: eigen-coefficients of the Duhamel potential

For the Duhamel potential `u(t) = duhamelPotential b f v t` of the drift `b` of `μ = w dx`
(`WData`: `∇w = w b`) and a weak eigenpair `(λ, ε)` of the weighted generator (LIP009):

* `duhamel_weak_trig`: the weak Duhamel identity against trigonometric polynomials;
* `duhamel_weak_H1` (a): the identity extends to all `H¹` test functions `φ` by Fourier cutoff and
  dominated convergence in time:
  `∫ u(t) φ - ∫ f φ = -∫₀ᵗ ∫ (v(s)·∇φ - (b·v(s)) φ)`;
* `duhamel_eigen_integral` (b): with `φ = ε w` (weak product rule), the eigen relation turns this
  into `c(t) - c(0) = -λ ∫₀ᵗ c(s) ds`, where `c(t) = ∫ u(t) ε w dx = ∫ u(t) ε dμ`;
* `ode_integral_unique` and `duhamel_eigen_coeff_ode` (c): `c(t) = e^{-λ t} c(0)` on `(0,T)`;
* `lip007d2_duhamel_eigen_coeff`, `lip007d2_duhamel_eigenbasis_coeff`: the packaged statements,
  with `v` produced by `lip007b_mild_gradient`.

Design note: `heatOp 0 f` is not `f`, so the conclusion is stated for `t ∈ (0,T)` with the
initial value `c(0) := ∫ f ε dμ`; the integral identity (a) is stated as a single time integral
of `duhamelPair`.
-/
open MeasureTheory Set Filter Topology
open scoped Real RealInnerProductSpace ComplexConjugate
namespace DGPS.Lipschitz
open DGPS.Analysis.CompactResolvent
variable {d : ℕ}

theorem integral_mul_psum {F : Torus d → ℝ} (hF : Integrable F (haar d))
    {c : (Fin d → ℤ) → ℂ} (hc : ∀ k, c (-k) = conj (c k)) (N : ℕ) :
    ((∫ x, F x * SharpLSI.psum c N x ∂haar d : ℝ) : ℂ) =
      ∑ k ∈ SharpLSI.box N, c k * fourierCoeff F (-k) := by
  rw [← integral_complex_ofReal]
  have h1 : ∀ x, ((F x * SharpLSI.psum c N x : ℝ) : ℂ) =
      ∑ k ∈ SharpLSI.box N, c k * (UnitAddTorus.mFourier k x * (F x : ℂ)) := by
    intro x
    push_cast
    rw [SharpLSI.psumC_real hc N x]
    unfold SharpLSI.psumC
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [h1]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    congr 1
    unfold fourierCoeff
    rw [mFourierCoeff_ofReal_eq]
    simp
  · intro k _
    refine Integrable.const_mul ?_ _
    have := hF.ofReal (𝕜 := ℂ)
    exact this.bdd_mul (c := 1) (UnitAddTorus.mFourier k : C(UnitAddTorus (Fin d), ℂ)).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        have := ContinuousMap.norm_coe_le_norm
          (UnitAddTorus.mFourier k : C(UnitAddTorus (Fin d), ℂ)) x
        rwa [UnitAddTorus.mFourier_norm] at this)


theorem measurable_fourierCoeff_gSlice {b : Torus d → Tangent d} (hb : Measurable b)
    {v : ℝ × Torus d → Tangent d} (hv : Measurable v) (k : Fin d → ℤ) :
    Measurable (fun s : ℝ => fourierCoeff (gSlice b v s) k) := by
  have hm : Measurable (fun p : ℝ × Torus d =>
      UnitAddTorus.mFourier (-k) p.2 * (gSlice b v p.1 p.2 : ℂ)) := by
    have h1 : Measurable (fun p : ℝ × Torus d => UnitAddTorus.mFourier (-k) p.2) :=
      ((UnitAddTorus.mFourier (-k) : C(UnitAddTorus (Fin d), ℂ)).continuous.measurable).comp
        measurable_snd
    have h2 : Measurable (fun p : ℝ × Torus d => gSlice b v p.1 p.2) :=
      (hb.comp measurable_snd).inner (hv.comp (measurable_fst.prodMk measurable_snd))
    exact h1.mul (Complex.measurable_ofReal.comp h2)
  have := hm.stronglyMeasurable.integral_prod_right' (ν := haar d)
  have heq : (fun s : ℝ => fourierCoeff (gSlice b v s) k) = fun s : ℝ =>
      ∫ x, UnitAddTorus.mFourier (-k) x * (gSlice b v s x : ℂ) ∂haar d :=
    funext fun s => mFourierCoeff_ofReal_eq _ _
  rw [heq]; exact this.measurable

theorem norm_fourierCoeff_gSlice_le {B0 V : ℝ} {b : Torus d → Tangent d}
    (hbB : ∀ x, ‖b x‖ ≤ B0) {v : ℝ × Torus d → Tangent d} (hvV : ∀ p, ‖v p‖ ≤ V) (s : ℝ)
    (k : Fin d → ℤ) : ‖fourierCoeff (gSlice b v s) k‖ ≤ B0 * V := by
  unfold fourierCoeff
  rw [mFourierCoeff_ofReal_eq]
  have := norm_integral_le_of_norm_le_const (μ := haar d) (C := B0 * V)
    (f := fun x => UnitAddTorus.mFourier (-k) x * (gSlice b v s x : ℂ))
    (Filter.Eventually.of_forall fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := ContinuousMap.norm_coe_le_norm
        (UnitAddTorus.mFourier (-k) : C(UnitAddTorus (Fin d), ℂ)) x
      rw [UnitAddTorus.mFourier_norm] at h1
      calc _ ≤ 1 * (B0 * V) :=
            mul_le_mul h1 (abs_gSlice_le hbB hvV s x) (abs_nonneg _) zero_le_one
        _ = B0 * V := one_mul _)
  simpa using this

theorem measurable_expConv {w : ℝ} {g : ℝ → ℂ} (hg : Measurable g) :
    Measurable (fun τ : ℝ => ∫ s in Ioo 0 τ, (Real.exp (-(w * (τ - s))) : ℂ) * g s) := by
  let G : ℝ × ℝ → ℂ := fun p =>
    if 0 < p.2 ∧ p.2 < p.1 then (Real.exp (-(w * (p.1 - p.2))) : ℂ) * g p.2 else 0
  have hGm : Measurable G := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_fst)
    · exact (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul (measurable_fst.sub measurable_snd)).neg)).mul
        (hg.comp measurable_snd)
  have h := (hGm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  have heq : (fun τ : ℝ => ∫ s in Ioo 0 τ, (Real.exp (-(w * (τ - s))) : ℂ) * g s) =
      fun τ => ∫ s, G (τ, s) := by
    funext τ
    rw [← integral_indicator measurableSet_Ioo]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    by_cases hs : s ∈ Ioo 0 τ
    · simp [G, hs.1, hs.2]
    · have : ¬ (0 < s ∧ s < τ) := fun h => hs ⟨h.1, h.2⟩
      simp [G, this]
  rw [heq]; exact h

theorem integrableOn_fourierCoeff_gSlice {B0 V : ℝ} {b : Torus d → Tangent d} (hb : Measurable b)
    (hbB : ∀ x, ‖b x‖ ≤ B0) {v : ℝ × Torus d → Tangent d} (hv : Measurable v)
    (hvV : ∀ p, ‖v p‖ ≤ V) (k : Fin d → ℤ) (t : ℝ) :
    IntegrableOn (fun s : ℝ => fourierCoeff (gSlice b v s) k) (Ioo 0 t) := by
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) t)) := ⟨by simp⟩
  exact Integrable.of_bound (measurable_fourierCoeff_gSlice hb hv k).aestronglyMeasurable (B0 * V)
    (Eventually.of_forall fun s => norm_fourierCoeff_gSlice_le hbB hvV s k)

theorem integrableOn_fourierCoeff_duhamelPotential {B0 V : ℝ} {b : Torus d → Tangent d}
    (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0) {f : Torus d → ℝ} (hf : Integrable f (haar d))
    {v : ℝ × Torus d → Tangent d} (hv : Measurable v) (hvV : ∀ p, ‖v p‖ ≤ V) (k : Fin d → ℤ)
    (t : ℝ) :
    IntegrableOn (fun τ : ℝ => fourierCoeff (duhamelPotential b f v τ) k) (Ioo 0 t) := by
  have hw0 : 0 ≤ gradWeight k := by unfold gradWeight; positivity
  have hgm : Measurable (fun s : ℝ => fourierCoeff (gSlice b v s) k) :=
    measurable_fourierCoeff_gSlice hb hv k
  set Φ : ℝ → ℂ := fun τ => (Real.exp (-(gradWeight k * τ)) : ℂ) * fourierCoeff f k +
    ∫ s in Ioo 0 τ, (Real.exp (-(gradWeight k * (τ - s))) : ℂ) * fourierCoeff (gSlice b v s) k
    with hΦ
  have hΦm : Measurable Φ := by
    refine Measurable.add ?_ (measurable_expConv hgm)
    exact (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul measurable_id).neg)).mul measurable_const
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) t)) := ⟨by simp⟩
  have hΦi : IntegrableOn Φ (Ioo 0 t) := by
    refine Integrable.of_bound hΦm.aestronglyMeasurable (‖fourierCoeff f k‖ + |t| * (B0 * V))
      ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun τ hτ => ?_
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have : Real.exp (-(gradWeight k * τ)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [hτ.1])
      exact (mul_le_of_le_one_left (norm_nonneg _) this)
    · have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hbB 0)
      have hV0 : 0 ≤ V := (norm_nonneg _).trans (hvV 0)
      have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo 0 τ)
        (C := B0 * V)
        (f := fun s => (Real.exp (-(gradWeight k * (τ - s))) : ℂ) * fourierCoeff (gSlice b v s) k)
        (by simp) (fun s hs => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          have : Real.exp (-(gradWeight k * (τ - s))) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by nlinarith [hs.2])
          calc _ ≤ 1 * (B0 * V) := mul_le_mul this (norm_fourierCoeff_gSlice_le hbB hvV s k)
                (norm_nonneg _) zero_le_one
            _ = B0 * V := one_mul _)
      refine h1.trans ?_
      rw [Real.volume_real_Ioo_of_le hτ.1.le]
      have : τ - 0 ≤ |t| := by linarith [le_abs_self t, hτ.2]
      nlinarith [mul_nonneg hB0 hV0]
  exact hΦi.congr_fun (fun τ hτ => (fourierCoeff_duhamelPotential hb hbB hf hv hvV hτ.1 k).symm)
    measurableSet_Ioo

theorem gradWeight_neg (k : Fin d → ℤ) : gradWeight (-k) = gradWeight k := by
  unfold gradWeight; simp

theorem inner_tangent_eq_sum (a b : Tangent d) : ⟪a, b⟫ = ∑ j, a j * b j := by
  simp [PiLp.inner_apply, mul_comm]

theorem pair_grad_psum {u : Torus d → ℝ} {Y : Torus d → Tangent d} (hY : IsWeakGradient u Y)
    {c : (Fin d → ℤ) → ℂ} (hc : ∀ k, c (-k) = conj (c k)) (N : ℕ) {G : Torus d → Tangent d}
    (hG : ∀ x j, G x j = SharpLSI.psum (fun k => 2 * π * Complex.I * (k j : ℂ) * c k) N x) :
    ((∫ x, ⟪Y x, G x⟫ ∂haar d : ℝ) : ℂ) =
      ∑ k ∈ SharpLSI.box N, c k * (gradWeight k : ℂ) * fourierCoeff u (-k) := by
  have hsymm : ∀ j : Fin d, ∀ k, (fun k : Fin d → ℤ => 2 * π * Complex.I * (k j : ℂ) * c k) (-k) =
      conj ((fun k : Fin d → ℤ => 2 * π * Complex.I * (k j : ℂ) * c k) k) := by
    intro j k
    simp only [Pi.neg_apply, Int.cast_neg, hc k, map_mul, Complex.conj_I,
      Complex.conj_ofReal, map_intCast, map_ofNat]
    ring
  have hGm : ∀ j, MemLp (fun x => G x j) 2 (haar d) := fun j => by
    have : (fun x => G x j) = SharpLSI.psum (fun k => 2 * π * Complex.I * (k j : ℂ) * c k) N := by
      funext x; exact hG x j
    rw [this]; exact SharpLSI.memLp_psum _ _ 2
  have hint : ∀ j, Integrable (fun x => Y x j * G x j) (haar d) := fun j =>
    (memLp_coord hY.memLp_grad j).integrable_mul (hGm j)
  have h1 : (∫ x, ⟪Y x, G x⟫ ∂haar d) = ∑ j, ∫ x, Y x j * G x j ∂haar d := by
    simp_rw [inner_tangent_eq_sum]
    exact integral_finsetSum _ fun j _ => hint j
  rw [h1]
  push_cast
  have h2 : ∀ j : Fin d, ((∫ x, Y x j * G x j ∂haar d : ℝ) : ℂ) =
      ∑ k ∈ SharpLSI.box N, c k * ((4 * π ^ 2 * ((k j : ℤ) : ℝ) ^ 2 : ℝ) : ℂ) *
        fourierCoeff u (-k) := by
    intro j
    have hGj : (fun x => G x j) =
        SharpLSI.psum (fun k => 2 * π * Complex.I * (k j : ℂ) * c k) N := by
      funext x; exact hG x j
    have := integral_mul_psum (c := fun k : Fin d → ℤ => 2 * π * Complex.I * (k j : ℂ) * c k)
      ((memLp_coord hY.memLp_grad j).integrable one_le_two) (hsymm j) N
    simp_rw [hG]
    rw [this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fourierCoeff_weakGradient hY j (-k)]
    have hI := Complex.I_sq
    push_cast
    simp only [Pi.neg_apply, Int.cast_neg]
    linear_combination (-(4 * (π : ℂ) ^ 2 * ((k j : ℤ) : ℂ) ^ 2 * c k * fourierCoeff u (-k))) * hI
  simp_rw [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hs : ∑ j : Fin d, ((4 * π ^ 2 * ((k j : ℤ) : ℝ) ^ 2 : ℝ) : ℂ) = (gradWeight k : ℂ) := by
    unfold gradWeight
    push_cast
    rw [Finset.mul_sum]
  rw [hs]


theorem integrable_inner_bdd {Y H : Torus d → Tangent d} (hY : Measurable Y) {V : ℝ}
    (hV : ∀ x, ‖Y x‖ ≤ V) (hH : Integrable H (haar d)) :
    Integrable (fun x => ⟪Y x, H x⟫) (haar d) := by
  refine Integrable.mono' (hH.norm.const_mul V)
    (hY.aestronglyMeasurable.inner hH.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  calc ‖⟪Y x, H x⟫‖ ≤ ‖Y x‖ * ‖H x‖ := norm_inner_le_norm _ _
    _ ≤ V * ‖H x‖ := mul_le_mul_of_nonneg_right (hV x) (norm_nonneg _)

theorem duhamel_weak_trig {B0 V : ℝ} {b : Torus d → Tangent d} (hb : Measurable b)
    (hbB : ∀ x, ‖b x‖ ≤ B0) {f : Torus d → ℝ} (hf : Integrable f (haar d))
    {v : ℝ × Torus d → Tangent d} (hv : Measurable v) (hvV : ∀ p, ‖v p‖ ≤ V) {t : ℝ} (ht : 0 < t)
    (hu : Integrable (duhamelPotential b f v t) (haar d))
    (hgrad : ∀ s ∈ Ioo 0 t, IsWeakGradient (duhamelPotential b f v s) (fun x => v (s, x)))
    {c : (Fin d → ℤ) → ℂ} (hc : ∀ k, c (-k) = conj (c k)) (N : ℕ) {G : Torus d → Tangent d}
    (hG : ∀ x j, G x j = SharpLSI.psum (fun k => 2 * π * Complex.I * (k j : ℂ) * c k) N x) :
    ∫ x, duhamelPotential b f v t x * SharpLSI.psum c N x ∂haar d -
        ∫ x, f x * SharpLSI.psum c N x ∂haar d =
      -∫ s in Ioo 0 t, ∫ x, (⟪v (s, x), G x⟫ - gSlice b v s x * SharpLSI.psum c N x) ∂haar d := by
  have hg : ∀ s, Integrable (gSlice b v s) (haar d) := fun s => integrable_gSlice hb hv hbB hvV s
  have e1 := integral_mul_psum hu hc N
  have e2 := integral_mul_psum hf hc N
  have e3 : ∀ s, ((∫ x, gSlice b v s x * SharpLSI.psum c N x ∂haar d : ℝ) : ℂ) =
      ∑ k ∈ SharpLSI.box N, c k * fourierCoeff (gSlice b v s) (-k) :=
    fun s => integral_mul_psum (hg s) hc N
  have hGmem : MemLp G 2 (haar d) := memLp_piLp_iff.mpr fun j => by
    have : (fun x => G x j) =
        SharpLSI.psum (fun k => 2 * π * Complex.I * (k j : ℂ) * c k) N := funext fun x => hG x j
    rw [this]; exact SharpLSI.memLp_psum _ _ 2
  have hA : ∀ s, Integrable (fun x => ⟪v (s, x), G x⟫) (haar d) := fun s =>
    integrable_inner_bdd (hv.comp (measurable_const.prodMk measurable_id)) (fun x => hvV _)
      (hGmem.integrable one_le_two)
  have hB : ∀ s, Integrable (fun x => gSlice b v s x * SharpLSI.psum c N x) (haar d) := fun s =>
    ((SharpLSI.memLp_psum c N 2).integrable one_le_two).bdd_mul
      (measurable_gSlice hb hv s).aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_gSlice_le hbB hvV s x)
  have e4 : ∀ s ∈ Ioo 0 t, ((∫ x, ⟪v (s, x), G x⟫ ∂haar d : ℝ) : ℂ) =
      ∑ k ∈ SharpLSI.box N, c k * (gradWeight k : ℂ) *
        fourierCoeff (duhamelPotential b f v s) (-k) :=
    fun s hs => pair_grad_psum (hgrad s hs) hc N hG
  have hJ : ∀ s ∈ Ioo 0 t,
      ((∫ x, (⟪v (s, x), G x⟫ - gSlice b v s x * SharpLSI.psum c N x) ∂haar d : ℝ) : ℂ) =
        ∑ k ∈ SharpLSI.box N, (c k * (gradWeight k : ℂ) *
          fourierCoeff (duhamelPotential b f v s) (-k) - c k * fourierCoeff (gSlice b v s) (-k)) := by
    intro s hs
    rw [integral_sub (hA s) (hB s), Complex.ofReal_sub, e4 s hs, e3 s, Finset.sum_sub_distrib]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sub, Complex.ofReal_neg, e1, e2, ← integral_complex_ofReal,
    setIntegral_congr_fun measurableSet_Ioo hJ]
  have hint1 : ∀ k, IntegrableOn (fun s => c k * (gradWeight k : ℂ) *
      fourierCoeff (duhamelPotential b f v s) (-k)) (Ioo 0 t) := fun k =>
    (integrableOn_fourierCoeff_duhamelPotential hb hbB hf hv hvV (-k) t).const_mul _
  have hint2 : ∀ k, IntegrableOn (fun s => c k * fourierCoeff (gSlice b v s) (-k)) (Ioo 0 t) :=
    fun k => (integrableOn_fourierCoeff_gSlice hb hbB hv hvV (-k) t).const_mul _
  have hint3 : ∀ k ∈ SharpLSI.box N, IntegrableOn (fun s => c k * (gradWeight k : ℂ) *
      fourierCoeff (duhamelPotential b f v s) (-k) - c k * fourierCoeff (gSlice b v s) (-k))
      (Ioo 0 t) := fun k _ => (hint1 k).sub (hint2 k)
  rw [integral_finsetSum _ hint3]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_sub (hint1 k) (hint2 k), integral_const_mul, integral_const_mul]
  have := fourierCoeff_duhamelPotential_ode hb hbB hf hv hvV ht (-k)
  rw [gradWeight_neg] at this
  linear_combination (c k) * this

/-- The `s`-slice of the (negated) right-hand side of the weak Duhamel identity. -/
noncomputable def duhamelPair (b : Torus d → Tangent d) (v : ℝ × Torus d → Tangent d) (s : ℝ)
    (φ : Torus d → ℝ) (G : Torus d → Tangent d) : ℝ :=
  ∫ x, (⟪v (s, x), G x⟫ - gSlice b v s x * φ x) ∂haar d

theorem measurable_duhamelPair {b : Torus d → Tangent d} (hb : Measurable b)
    {v : ℝ × Torus d → Tangent d} (hv : Measurable v) {φ : Torus d → ℝ} (hφ : Measurable φ)
    {G : Torus d → Tangent d} (hG : Measurable G) :
    Measurable (fun s => duhamelPair b v s φ G) := by
  have hm : Measurable (fun p : ℝ × Torus d =>
      ⟪v (p.1, p.2), G p.2⟫ - gSlice b v p.1 p.2 * φ p.2) := by
    have h1 : Measurable (fun p : ℝ × Torus d => ⟪v (p.1, p.2), G p.2⟫) :=
      (hv.comp (measurable_fst.prodMk measurable_snd)).inner (hG.comp measurable_snd)
    have h2 : Measurable (fun p : ℝ × Torus d => gSlice b v p.1 p.2) :=
      (hb.comp measurable_snd).inner (hv.comp (measurable_fst.prodMk measurable_snd))
    exact h1.sub (h2.mul (hφ.comp measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := haar d)).measurable

theorem integrable_pairB {B0 V : ℝ} {b : Torus d → Tangent d} (hb : Measurable b)
    (hbB : ∀ x, ‖b x‖ ≤ B0) {v : ℝ × Torus d → Tangent d} (hv : Measurable v)
    (hvV : ∀ p, ‖v p‖ ≤ V) {φ : Torus d → ℝ} (hφ : Integrable φ (haar d)) (s : ℝ) :
    Integrable (fun x => gSlice b v s x * φ x) (haar d) :=
  hφ.bdd_mul (measurable_gSlice hb hv s).aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_gSlice_le hbB hvV s x)

theorem duhamelPair_eq {B0 V : ℝ} {b : Torus d → Tangent d} (hb : Measurable b)
    (hbB : ∀ x, ‖b x‖ ≤ B0) {v : ℝ × Torus d → Tangent d} (hv : Measurable v)
    (hvV : ∀ p, ‖v p‖ ≤ V) {φ : Torus d → ℝ} (hφ : MemLp φ 2 (haar d))
    {G : Torus d → Tangent d} (hG : MemLp G 2 (haar d)) (s : ℝ) :
    duhamelPair b v s φ G =
      ∫ x, ⟪v (s, x), G x⟫ ∂haar d - ∫ x, gSlice b v s x * φ x ∂haar d := by
  unfold duhamelPair
  exact integral_sub (integrable_inner_bdd (hv.comp (measurable_const.prodMk measurable_id))
    (fun x => hvV _) (hG.integrable one_le_two))
    (integrable_pairB hb hbB hv hvV (hφ.integrable one_le_two) s)

theorem abs_duhamelPair_le {B0 V : ℝ} {b : Torus d → Tangent d} (hb : Measurable b)
    (hbB : ∀ x, ‖b x‖ ≤ B0) {v : ℝ × Torus d → Tangent d} (hv : Measurable v)
    (hvV : ∀ p, ‖v p‖ ≤ V) {φ : Torus d → ℝ} (hφ : MemLp φ 2 (haar d))
    {G : Torus d → Tangent d} (hG : MemLp G 2 (haar d)) (s : ℝ) :
    |duhamelPair b v s φ G| ≤
      V * (1 + ∫ x, ‖G x‖ ^ 2 ∂haar d) + B0 * V * (1 + ∫ x, φ x ^ 2 ∂haar d) := by
  have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hbB 0)
  have hV0 : 0 ≤ V := (norm_nonneg _).trans (hvV (0, 0))
  have hsG : Integrable (fun x => ‖G x‖ ^ 2) (haar d) := hG.norm.integrable_sq
  have hsφ : Integrable (fun x => φ x ^ 2) (haar d) := hφ.integrable_sq
  rw [duhamelPair_eq hb hbB hv hvV hφ hG s]
  have hA : |∫ x, ⟪v (s, x), G x⟫ ∂haar d| ≤ V * (1 + ∫ x, ‖G x‖ ^ 2 ∂haar d) := by
    have hbd : Integrable (fun x => V * (1 + ‖G x‖ ^ 2)) (haar d) :=
      ((integrable_const (1 : ℝ)).add hsG).const_mul V
    have := norm_integral_le_of_norm_le hbd (Eventually.of_forall fun x => by
      calc ‖⟪v (s, x), G x⟫‖ ≤ ‖v (s, x)‖ * ‖G x‖ := norm_inner_le_norm _ _
        _ ≤ V * ‖G x‖ := mul_le_mul_of_nonneg_right (hvV _) (norm_nonneg _)
        _ ≤ V * (1 + ‖G x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (‖G x‖ - 1)]) hV0)
    rw [integral_const_mul, integral_add (integrable_const _) hsG] at this
    simpa using this
  have hB : |∫ x, gSlice b v s x * φ x ∂haar d| ≤ B0 * V * (1 + ∫ x, φ x ^ 2 ∂haar d) := by
    have hbd : Integrable (fun x => B0 * V * (1 + φ x ^ 2)) (haar d) :=
      ((integrable_const (1 : ℝ)).add hsφ).const_mul _
    have := norm_integral_le_of_norm_le hbd (Eventually.of_forall fun x => by
      rw [norm_mul (gSlice b v s x) (φ x), Real.norm_eq_abs, Real.norm_eq_abs]
      calc |gSlice b v s x| * |φ x| ≤ (B0 * V) * |φ x| :=
            mul_le_mul_of_nonneg_right (abs_gSlice_le hbB hvV s x) (abs_nonneg _)
        _ ≤ B0 * V * (1 + φ x ^ 2) :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (|φ x| - 1), sq_abs (φ x)])
            (mul_nonneg hB0 hV0))
    rw [integral_const_mul, integral_add (integrable_const _) hsφ] at this
    simpa using this
  calc _ ≤ |∫ x, ⟪v (s, x), G x⟫ ∂haar d| + |∫ x, gSlice b v s x * φ x ∂haar d| := abs_sub _ _
    _ ≤ _ := add_le_add hA hB

theorem eLpNorm_two_eq_sqrt {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {F : α → E} (hF : MemLp F 2 μ) :
    eLpNorm F 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, ‖F x‖ ^ 2 ∂μ)) := by
  rw [hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  norm_num

theorem tendsto_eLpNorm_cutoff {φ : Torus d → ℝ} (hφ : MemLp φ 2 (haar d)) :
    Tendsto (fun n : ℕ => eLpNorm (fun x => fourierCutoff φ n x - φ x) 2 (haar d)) atTop (𝓝 0) := by
  have h := (tendsto_integral_sq_fourierCutoff_sub hφ).comp tendsto_natCast_atTop_atTop
  have h2 := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at h2
  have h3 := (ENNReal.tendsto_ofReal h2)
  rw [ENNReal.ofReal_zero] at h3
  refine h3.congr fun n => ?_
  have := eLpNorm_two_eq_sqrt (F := fun x => fourierCutoff φ n x - φ x)
    ((memLp_fourierCutoff φ n).sub hφ)
  rw [this]
  simp only [Function.comp, Real.norm_eq_abs, sq_abs]

theorem integral_sq_fourierCutoff_le {u : Torus d → ℝ} (hu : MemLp u 2 (haar d)) (R : ℝ) :
    ∫ x, fourierCutoff u R x ^ 2 ∂haar d ≤ ∫ x, u x ^ 2 ∂haar d := by
  refine hasSum_le (fun k => ?_) (hasSum_sq_fourierCoeff (memLp_fourierCutoff u R))
    (hasSum_sq_fourierCoeff hu)
  rw [fourierCoeff_fourierCutoff, norm_sq_cutCoeff]
  split_ifs
  · exact le_rfl
  · positivity

theorem memLp_coord_slice {V : ℝ} {v : ℝ × Torus d → Tangent d} (hv : Measurable v)
    (hvV : ∀ p, ‖v p‖ ≤ V) (s : ℝ) (j : Fin d) :
    MemLp (fun x => v (s, x) j) 2 (haar d) := by
  refine MemLp.of_bound ?_ V (Eventually.of_forall fun x => ?_)
  · exact ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable.comp
      (hv.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le (v (s, x)) j).trans (hvV _)

theorem memLp_gSlice {B0 V : ℝ} {b : Torus d → Tangent d} (hb : Measurable b)
    (hbB : ∀ x, ‖b x‖ ≤ B0) {v : ℝ × Torus d → Tangent d} (hv : Measurable v)
    (hvV : ∀ p, ‖v p‖ ≤ V) (s : ℝ) : MemLp (gSlice b v s) 2 (haar d) :=
  MemLp.of_bound (measurable_gSlice hb hv s).aestronglyMeasurable (B0 * V)
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_gSlice_le hbB hvV s x)

theorem tendsto_duhamelPair {B0 V : ℝ} {b : Torus d → Tangent d} (hb : Measurable b)
    (hbB : ∀ x, ‖b x‖ ≤ B0) {v : ℝ × Torus d → Tangent d} (hv : Measurable v)
    (hvV : ∀ p, ‖v p‖ ≤ V) {φ : Torus d → ℝ} (hφ : MemLp φ 2 (haar d))
    {G : Torus d → Tangent d} (hG : MemLp G 2 (haar d)) (s : ℝ) :
    Tendsto (fun n : ℕ => duhamelPair b v s (fourierCutoff φ n) (fourierCutoffGrad G n))
      atTop (𝓝 (duhamelPair b v s φ G)) := by
  have hGn : ∀ n : ℕ, MemLp (fourierCutoffGrad G n) 2 (haar d) := fun n =>
    memLp_piLp_iff.mpr fun j => memLp_fourierCutoff _ _
  have hsum : ∀ (H : Torus d → Tangent d), MemLp H 2 (haar d) →
      ∫ x, ⟪v (s, x), H x⟫ ∂haar d = ∑ j, ∫ x, v (s, x) j * H x j ∂haar d := by
    intro H hH
    simp_rw [inner_tangent_eq_sum]
    refine integral_finsetSum _ fun j _ => ?_
    exact ((memLp_coord hH j).integrable one_le_two).bdd_mul
      (((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable.comp
        (hv.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
      (Eventually.of_forall fun x => (PiLp.norm_apply_le (v (s, x)) j).trans (hvV _))
  have h1 : Tendsto (fun n : ℕ => ∫ x, ⟪v (s, x), fourierCutoffGrad G n x⟫ ∂haar d) atTop
      (𝓝 (∫ x, ⟪v (s, x), G x⟫ ∂haar d)) := by
    simp_rw [hsum _ (hGn _)]
    rw [hsum G hG]
    refine tendsto_finsetSum _ fun j _ => ?_
    exact WeightedGenerator.tendsto_integral_mul_L2 (memLp_coord_slice hv hvV s j)
      (fun n => memLp_fourierCutoff _ _) (memLp_coord hG j) (tendsto_eLpNorm_cutoff (memLp_coord hG j))
  have h2 : Tendsto (fun n : ℕ => ∫ x, gSlice b v s x * fourierCutoff φ n x ∂haar d) atTop
      (𝓝 (∫ x, gSlice b v s x * φ x ∂haar d)) :=
    WeightedGenerator.tendsto_integral_mul_L2 (memLp_gSlice hb hbB hv hvV s) (fun n => memLp_fourierCutoff _ _) hφ
      (tendsto_eLpNorm_cutoff hφ)
  simp_rw [duhamelPair_eq hb hbB hv hvV (memLp_fourierCutoff _ _) (hGn _) s]
  rw [duhamelPair_eq hb hbB hv hvV hφ hG s]
  exact h1.sub h2

theorem measurable_fourierCutoff (u : Torus d → ℝ) (R : ℝ) : Measurable (fourierCutoff u R) :=
  (SharpLSI.continuous_psum _ _).measurable

theorem measurable_fourierCutoffGrad (g : Torus d → Tangent d) (R : ℝ) :
    Measurable (fourierCutoffGrad g R) :=
  ((PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
    (continuous_pi fun _ => SharpLSI.continuous_psum _ _)).measurable

theorem fourierCutoffGrad_psum {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) (n : ℕ) (x : Torus d) (j : Fin d) :
    fourierCutoffGrad g n x j = SharpLSI.psum
      (fun k => 2 * π * Complex.I * (k j : ℂ) * cutCoeff (fourierCoeff u) n k) ⌈(n : ℝ)⌉₊ x := by
  show SharpLSI.psum (cutCoeff (fourierCoeff (fun y => g y j)) n) ⌈(n : ℝ)⌉₊ x = _
  have : cutCoeff (fourierCoeff (fun y => g y j)) n =
      fun k => 2 * π * Complex.I * (k j : ℂ) * cutCoeff (fourierCoeff u) n k := by
    funext k
    rw [← cutCoeff_mul (fun k => 2 * π * Complex.I * (k j : ℂ)) (fourierCoeff u) n k]
    exact congrArg (fun c => cutCoeff c n k) (funext fun k => fourierCoeff_weakGradient h j k)
  rw [this]

theorem duhamel_weak_H1 {B0 V : ℝ} {b : Torus d → Tangent d} (hb : Measurable b)
    (hbB : ∀ x, ‖b x‖ ≤ B0) {f : Torus d → ℝ} (hf : MemLp f 2 (haar d))
    {v : ℝ × Torus d → Tangent d} (hv : Measurable v) (hvV : ∀ p, ‖v p‖ ≤ V) {t : ℝ} (ht : 0 < t)
    (hu : MemLp (duhamelPotential b f v t) 2 (haar d))
    (hgrad : ∀ s ∈ Ioo 0 t, IsWeakGradient (duhamelPotential b f v s) (fun x => v (s, x)))
    {φ : Torus d → ℝ} {Gφ : Torus d → Tangent d} (hφ : IsWeakGradient φ Gφ) :
    ∫ x, duhamelPotential b f v t x * φ x ∂haar d - ∫ x, f x * φ x ∂haar d =
      -∫ s in Ioo 0 t, duhamelPair b v s φ Gφ := by
  have hφ2 := hφ.memLp
  have hG2 := hφ.memLp_grad
  have hGn : ∀ n : ℕ, MemLp (fourierCutoffGrad Gφ n) 2 (haar d) := fun n =>
    memLp_piLp_iff.mpr fun j => memLp_fourierCutoff _ _
  have key : ∀ n : ℕ,
      ∫ x, duhamelPotential b f v t x * fourierCutoff φ n x ∂haar d -
        ∫ x, f x * fourierCutoff φ n x ∂haar d =
      -∫ s in Ioo 0 t, duhamelPair b v s (fourierCutoff φ n) (fourierCutoffGrad Gφ n) := by
    intro n
    exact duhamel_weak_trig hb hbB (hf.integrable one_le_two) hv hvV ht (hu.integrable one_le_two)
      hgrad (c := cutCoeff (fourierCoeff φ) n) (cutCoeff_symm (fourierCoeff_neg φ) n) ⌈(n : ℝ)⌉₊
      (G := fourierCutoffGrad Gφ n) (fourierCutoffGrad_psum hφ n)
  have hL1 := WeightedGenerator.tendsto_integral_mul_L2 hu (fun n => memLp_fourierCutoff φ n) hφ2
    (tendsto_eLpNorm_cutoff hφ2)
  have hL2 := WeightedGenerator.tendsto_integral_mul_L2 hf (fun n => memLp_fourierCutoff φ n) hφ2
    (tendsto_eLpNorm_cutoff hφ2)
  have hR : Tendsto (fun n : ℕ => ∫ s in Ioo 0 t,
      duhamelPair b v s (fourierCutoff φ n) (fourierCutoffGrad Gφ n)) atTop
      (𝓝 (∫ s in Ioo 0 t, duhamelPair b v s φ Gφ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun _ => V * (1 + ∫ x, ‖Gφ x‖ ^ 2 ∂haar d) + B0 * V * (1 + ∫ x, φ x ^ 2 ∂haar d))
      (fun n => (measurable_duhamelPair hb hv (measurable_fourierCutoff φ n)
        (measurable_fourierCutoffGrad Gφ n)).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun s => ?_)
      (Eventually.of_forall fun s => tendsto_duhamelPair hb hbB hv hvV hφ2 hG2 s)
    rw [Real.norm_eq_abs]
    refine (abs_duhamelPair_le hb hbB hv hvV (memLp_fourierCutoff φ n) (hGn n) s).trans ?_
    have h1 := integral_norm_sq_cutoffGrad_le hφ (n : ℝ)
    have h2 := integral_sq_fourierCutoff_le hφ2 (n : ℝ)
    have hV0 : 0 ≤ V := (norm_nonneg _).trans (hvV (0, 0))
    have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hbB 0)
    gcongr
  exact tendsto_nhds_unique (hL1.sub hL2) ((hR.neg).congr fun n => (key n).symm)

theorem ode_integral_unique {T M lam a : ℝ} {K c : ℝ → ℝ} (hKm : Measurable K)
    (hKb : ∀ s, |K s| ≤ M) (hKc : ∀ s ∈ Ioo 0 T, K s = lam * c s)
    (hc : ∀ t ∈ Ioo 0 T, c t - a = -∫ s in Ioo 0 t, K s) :
    ∀ t ∈ Ioo 0 T, c t = Real.exp (-lam * t) * a := by
  have ib : ∀ x y : ℝ, IntegrableOn K (Ioc x y) := fun x y =>
    Measure.integrableOn_of_bounded (M := M) (by simp) hKm.aestronglyMeasurable
      (Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact hKb s)
  have hKi : ∀ x y : ℝ, IntervalIntegrable K volume x y := fun x y => ⟨ib _ _, ib _ _⟩
  set g : ℝ → ℝ := fun t => a - ∫ s in (0 : ℝ)..t, K s with hgdef
  have hgc : Continuous g :=
    continuous_const.sub (intervalIntegral.continuous_primitive hKi 0)
  have hcg : ∀ t ∈ Ioo 0 T, c t = g t := by
    intro t ht
    have := hc t ht
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.1.le] at this
    simp only [hgdef]
    linarith
  have hKg : ∀ s ∈ Ioo 0 T, K s = lam * g s := fun s hs => by rw [hKc s hs, hcg s hs]
  have hder : ∀ t ∈ Ioo 0 T, HasDerivAt (fun s => Real.exp (lam * s) * g s) 0 t := by
    intro t ht
    have hKcont : ContinuousAt K t := by
      have : ContinuousAt (fun s => lam * g s) t := (continuous_const.mul hgc).continuousAt
      refine this.congr ?_
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs using (hKg s hs).symm
    have h1 : HasDerivAt g (-K t) t := by
      have := (intervalIntegral.integral_hasDerivAt_right (hKi 0 t)
        hKm.stronglyMeasurable.stronglyMeasurableAtFilter hKcont).const_sub a
      exact this
    have h2 : HasDerivAt (fun s => Real.exp (lam * s)) (Real.exp (lam * t) * lam) t := by
      have := ((hasDerivAt_id t).const_mul lam).exp
      simpa using this
    have := h2.mul h1
    convert this using 1
    rw [hKg t ht]; ring
  have hhc : Continuous (fun s => Real.exp (lam * s) * g s) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hgc
  intro t ht
  have hconst : ∀ ε ∈ Ioo 0 t, Real.exp (lam * t) * g t = Real.exp (lam * ε) * g ε := by
    intro ε hε
    have hsub : Icc ε t ⊆ Ioo 0 T := fun x hx => ⟨hε.1.trans_le hx.1, hx.2.trans_lt ht.2⟩
    have := constant_of_derivWithin_zero (f := fun s => Real.exp (lam * s) * g s) (a := ε) (b := t)
      (fun x hx => (hder x (hsub hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => (hder x (hsub ⟨hx.1, hx.2.le⟩)).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc hε.2 x ⟨hx.1, hx.2.le⟩)) t ⟨hε.2.le, le_rfl⟩
    exact this
  have h1 : Tendsto (fun s => Real.exp (lam * s) * g s) (𝓝[>] 0) (𝓝 a) := by
    have := (hhc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [hgdef] using this
  have h2 : Tendsto (fun s => Real.exp (lam * s) * g s) (𝓝[>] 0)
      (𝓝 (Real.exp (lam * t) * g t)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT ht.1] with ε hε using hconst ε hε)
  have h3 := tendsto_nhds_unique h2 h1
  rw [hcg t ht]
  have hexp : Real.exp (-lam * t) * Real.exp (lam * t) = 1 := by
    rw [← Real.exp_add]; simp
  calc g t = Real.exp (-lam * t) * (Real.exp (lam * t) * g t) := by
        rw [← mul_assoc, hexp, one_mul]
    _ = _ := by rw [h3]

theorem duhamelPair_eigen {c C : ℝ} {w : Torus d → ℝ} {b : Torus d → Tangent d}
    (hW : WeightedGenerator.WData d w b c C) {v : ℝ × Torus d → Tangent d} (s : ℝ)
    (ε : Hw d w) {G : Torus d → Tangent d} {lam : ℝ}
    (hE : ∀ (g : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (g : Torus d → ℝ) Y →
      weightedForm w G Y = lam * inner ℝ ε g)
    {U : Torus d → ℝ} (hU : IsWeakGradient U (fun x => v (s, x))) :
    duhamelPair b v s (fun x => (ε : Torus d → ℝ) x * w x)
        (fun x => w x • G x + (ε : Torus d → ℝ) x • (w x • b x)) =
      lam * ∫ x, U x * ((ε : Torus d → ℝ) x * w x) ∂haar d := by
  have hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C := Eventually.of_forall hW.bound
  have hUμ : MemLp U 2 (wMeasure d w) := (memLp_wMeasure_iff hW.pos hwb).mpr hU.memLp
  set g : Hw d w := hUμ.toLp U with hg
  have hgae : (g : Torus d → ℝ) =ᵐ[haar d] U :=
    ae_eq_haar hW.pos hwb hUμ.coeFn_toLp
  have hgG : IsWeakGradient (g : Torus d → ℝ) (fun x => v (s, x)) :=
    hU.congr_ae hgae.symm (Eventually.of_forall fun _ => rfl)
  have h1 := hE g _ hgG
  rw [inner_Lp_wMeasure hW.meas hW.pos hwb] at h1
  have e1 : duhamelPair b v s (fun x => (ε : Torus d → ℝ) x * w x)
        (fun x => w x • G x + (ε : Torus d → ℝ) x • (w x • b x)) = weightedForm w G (fun x => v (s, x)) := by
    unfold duhamelPair weightedForm gSlice
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [inner_add_right, inner_smul_right, real_inner_comm (v (s, x)) (b x),
      real_inner_comm (v (s, x)) (G x)]
    ring
  rw [e1, h1]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hgae] with x hx
  rw [hx]
  simp [mul_comm, mul_left_comm]

theorem duhamel_weak_eigen {B0 V c C : ℝ} {w : Torus d → ℝ} {b : Torus d → Tangent d}
    (hW : WeightedGenerator.WData d w b c C) (hb : Measurable b)
    (hbB : ∀ x, ‖b x‖ ≤ B0) {f : Torus d → ℝ} (hf : MemLp f 2 (haar d))
    {v : ℝ × Torus d → Tangent d} (hv : Measurable v) (hvV : ∀ p, ‖v p‖ ≤ V) {t : ℝ} (ht : 0 < t)
    (hgrad : ∀ s ∈ Ioc 0 t, IsWeakGradient (duhamelPotential b f v s) (fun x => v (s, x)))
    (ε : Hw d w) {G : Torus d → Tangent d} (hεG : IsWeakGradient (ε : Torus d → ℝ) G) :
    ∫ x, duhamelPotential b f v t x * ((ε : Torus d → ℝ) x * w x) ∂haar d -
        ∫ x, f x * ((ε : Torus d → ℝ) x * w x) ∂haar d =
      -∫ s in Ioo 0 t, duhamelPair b v s (fun x => (ε : Torus d → ℝ) x * w x)
        (fun x => w x • G x + (ε : Torus d → ℝ) x • (w x • b x)) :=
  duhamel_weak_H1 hb hbB hf hv hvV ht (hgrad t ⟨ht, le_rfl⟩).memLp
    (fun s hs => hgrad s ⟨hs.1, hs.2.le⟩) (hεG.mul_W1infty hW.grad_w)

/-- (b): the eigen-coefficient `c(t) = ∫ u(t) ε w` satisfies `c(t) - c(0) = -λ ∫₀ᵗ c`. -/
theorem duhamel_eigen_integral {B0 V c C : ℝ} {w : Torus d → ℝ} {b : Torus d → Tangent d}
    (hW : WeightedGenerator.WData d w b c C) (hb : Measurable b)
    (hbB : ∀ x, ‖b x‖ ≤ B0) {f : Torus d → ℝ} (hf : MemLp f 2 (haar d))
    {v : ℝ × Torus d → Tangent d} (hv : Measurable v) (hvV : ∀ p, ‖v p‖ ≤ V) {t : ℝ} (ht : 0 < t)
    (hgrad : ∀ s ∈ Ioc 0 t, IsWeakGradient (duhamelPotential b f v s) (fun x => v (s, x)))
    (ε : Hw d w) {G : Torus d → Tangent d} (hεG : IsWeakGradient (ε : Torus d → ℝ) G) {lam : ℝ}
    (hE : ∀ (g : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (g : Torus d → ℝ) Y →
      weightedForm w G Y = lam * inner ℝ ε g) :
    ∫ x, duhamelPotential b f v t x * ((ε : Torus d → ℝ) x * w x) ∂haar d -
        ∫ x, f x * ((ε : Torus d → ℝ) x * w x) ∂haar d =
      -(lam * ∫ s in Ioo 0 t, ∫ x, duhamelPotential b f v s x *
        ((ε : Torus d → ℝ) x * w x) ∂haar d) := by
  rw [duhamel_weak_eigen hW hb hbB hf hv hvV ht hgrad ε hεG, ← integral_const_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  exact duhamelPair_eigen hW s ε hE (hgrad s ⟨hs.1, hs.2.le⟩)

/-- (c): `c(t) = e^{-λ t} c(0)` for `t ∈ (0,T)`. -/
theorem duhamel_eigen_coeff_ode {B0 V c C T : ℝ} {w : Torus d → ℝ} {b : Torus d → Tangent d}
    (hW : WeightedGenerator.WData d w b c C) (hb : Measurable b)
    (hbB : ∀ x, ‖b x‖ ≤ B0) {f : Torus d → ℝ} (hf : MemLp f 2 (haar d))
    {v : ℝ × Torus d → Tangent d} (hv : Measurable v) (hvV : ∀ p, ‖v p‖ ≤ V)
    (hgrad : ∀ t ∈ Ioo 0 T, IsWeakGradient (duhamelPotential b f v t) (fun x => v (t, x)))
    (ε : Hw d w) {G : Torus d → Tangent d} (hεG : IsWeakGradient (ε : Torus d → ℝ) G) {lam : ℝ}
    (hE : ∀ (g : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (g : Torus d → ℝ) Y →
      weightedForm w G Y = lam * inner ℝ ε g) :
    ∀ t ∈ Ioo 0 T, ∫ x, duhamelPotential b f v t x * ((ε : Torus d → ℝ) x * w x) ∂haar d =
      Real.exp (-lam * t) * ∫ x, f x * ((ε : Torus d → ℝ) x * w x) ∂haar d := by
  -- replace `G` by a measurable representative
  have hGm0 := hεG.memLp_grad.aestronglyMeasurable
  set G' : Torus d → Tangent d := hGm0.mk G with hG'
  have hGae : G =ᵐ[haar d] G' := hGm0.ae_eq_mk
  have hGm : Measurable G' := hGm0.stronglyMeasurable_mk.measurable
  have hεG' : IsWeakGradient (ε : Torus d → ℝ) G' :=
    hεG.congr_ae (Eventually.of_forall fun _ => rfl) hGae
  have hE' : ∀ (g : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (g : Torus d → ℝ) Y →
      weightedForm w G' Y = lam * inner ℝ ε g := by
    intro g Y hY
    rw [← hE g Y hY]
    unfold weightedForm
    refine integral_congr_ae ?_
    filter_upwards [hGae] with x hx
    rw [hx]
  have hεm : Measurable (ε : Torus d → ℝ) := (Lp.stronglyMeasurable ε).measurable
  have hφm : Measurable (fun x => (ε : Torus d → ℝ) x * w x) := hεm.mul hW.meas
  have hGφm : Measurable (fun x => w x • G' x + (ε : Torus d → ℝ) x • (w x • b x)) :=
    (hW.meas.smul hGm).add (hεm.smul (hW.meas.smul hb))
  have hφG := hεG'.mul_W1infty hW.grad_w
  have hK := measurable_duhamelPair hb hv hφm hGφm
  set K : ℝ → ℝ := fun s => duhamelPair b v s (fun x => (ε : Torus d → ℝ) x * w x)
    (fun x => w x • G' x + (ε : Torus d → ℝ) x • (w x • b x)) with hKdef
  have hKb : ∀ s, |K s| ≤ V * (1 + ∫ x, ‖w x • G' x + (ε : Torus d → ℝ) x • (w x • b x)‖ ^ 2 ∂haar d) +
      B0 * V * (1 + ∫ x, ((ε : Torus d → ℝ) x * w x) ^ 2 ∂haar d) := fun s =>
    abs_duhamelPair_le hb hbB hv hvV hφG.memLp hφG.memLp_grad s
  refine ode_integral_unique (T := T) (M := _) (lam := lam)
    (a := ∫ x, f x * ((ε : Torus d → ℝ) x * w x) ∂haar d)
    (c := fun s => ∫ x, duhamelPotential b f v s x * ((ε : Torus d → ℝ) x * w x) ∂haar d)
    hK hKb (fun s hs => duhamelPair_eigen hW s ε hE' (hgrad s hs)) (fun t ht => ?_)
  have := duhamel_weak_eigen (G := G') hW hb hbB hf hv hvV ht.1
    (fun s hs => hgrad s ⟨hs.1, hs.2.trans_lt ht.2⟩) ε hεG'
  exact this

theorem lip007d2_duhamel_eigen_coeff {T B0 L c C : ℝ} (hT : 0 < T) (hL : 0 ≤ L)
    {w : Torus d → ℝ} {b : Torus d → Tangent d} (hW : WeightedGenerator.WData d w b c C)
    (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0) (hTB : 16 * B0 ^ 2 * T ≤ π)
    {f : Torus d → ℝ} (hf : TorusLipschitzWith L f) :
    ∃ v : ℝ × Torus d → Tangent d, Measurable v ∧ (∀ p, ‖v p‖ ≤ 2 * L) ∧
      (∀ t ∈ Ioo 0 T, IsWeakGradient (duhamelPotential b f v t) (fun x => v (t, x))) ∧
      ∀ (ε : Hw d w) {G : Torus d → Tangent d}, IsWeakGradient (ε : Torus d → ℝ) G →
        ∀ {lam : ℝ}, (∀ (g : Hw d w) (Y : Torus d → Tangent d),
          IsWeakGradient (g : Torus d → ℝ) Y → weightedForm w G Y = lam * inner ℝ ε g) →
        ∀ t ∈ Ioo 0 T,
          ∫ x, duhamelPotential b f v t x * (ε : Torus d → ℝ) x ∂wMeasure d w =
            Real.exp (-lam * t) * ∫ x, f x * (ε : Torus d → ℝ) x ∂wMeasure d w := by
  obtain ⟨v, hvm, hvb, -, -, hgrad⟩ := lip007b_mild_gradient hT hL hb hbB hTB hf
  have hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C := Eventually.of_forall hW.bound
  have hfm : MemLp f 2 (haar d) :=
    (continuous_of_torusLipschitz hL hf).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨v, hvm, hvb, hgrad, fun ε G hεG lam hE t ht => ?_⟩
  have h := duhamel_eigen_coeff_ode hW hb hbB hfm hvm hvb hgrad ε hεG hE t ht
  rw [integral_wMeasure hW.meas hW.pos hwb, integral_wMeasure hW.meas hW.pos hwb]
  simpa only [smul_eq_mul, mul_comm (w _), mul_assoc] using h

/-- LIP007d2 for the LIP009 eigenbasis: every eigen-coefficient of the Duhamel potential decays
exponentially at the rate of its eigenvalue. -/
theorem lip007d2_duhamel_eigenbasis_coeff {T B0 L c C : ℝ} (hd : 0 < d) (hT : 0 < T) (hL : 0 ≤ L)
    {w : Torus d → ℝ} {b : Torus d → Tangent d} (hW : WeightedGenerator.WData d w b c C)
    (hint : ∫ x, w x ∂haar d = 1) (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0)
    (hTB : 16 * B0 ^ 2 * T ≤ π) {f : Torus d → ℝ} (hf : TorusLipschitzWith L f) :
    ∃ v : ℝ × Torus d → Tangent d, Measurable v ∧ (∀ p, ‖v p‖ ≤ 2 * L) ∧
      (∀ t ∈ Ioo 0 T, IsWeakGradient (duhamelPotential b f v t) (fun x => v (t, x))) ∧
      ∃ (e : HilbertBasis ℕ ℝ (Hw d w)) (lam : ℕ → ℝ), lam 0 = 0 ∧ Monotone lam ∧
        Tendsto lam atTop atTop ∧
        ∀ (j : ℕ), ∀ t ∈ Ioo 0 T,
          ∫ x, duhamelPotential b f v t x * ((e j : Hw d w) : Torus d → ℝ) x ∂wMeasure d w =
            Real.exp (-lam j * t) *
              ∫ x, f x * ((e j : Hw d w) : Torus d → ℝ) x ∂wMeasure d w := by
  have hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C := Eventually.of_forall hW.bound
  obtain ⟨e, lam, G, -, h0, -, hmono, hlim, hG, hE, -, -⟩ :=
    WeightedSpectrum.weighted_eigenbasis_and_growth hd hW.meas hW.pos hwb hint
  obtain ⟨v, hvm, hvb, hgrad, hc⟩ := lip007d2_duhamel_eigen_coeff hT hL hW hb hbB hTB hf
  exact ⟨v, hvm, hvb, hgrad, e, lam, h0, hmono, hlim, fun j t ht => hc (e j) (hG j) (hE j) t ht⟩

end DGPS.Lipschitz
