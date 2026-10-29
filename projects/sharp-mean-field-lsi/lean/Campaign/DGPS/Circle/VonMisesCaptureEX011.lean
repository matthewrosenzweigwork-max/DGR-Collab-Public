import DGPS.Circle.VonMisesSmallField
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryBootstrap
import DGPS.Analysis.CircleMoments

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Circle.VonMisesCaptureEX011

open DGPS.Examples.ThreeSpeciesCircle DGPS.Circle.VonMisesSmallField
open DGPS.Analysis.PeriodicHolder

/-- The constant (Haar) density. -/
noncomputable def constDensity_ex011 : AbsoluteDensity 1 :=
  ⟨fun _ => 1, ⟨fun _ => 0, isWeakGradient_const 1⟩, ae_of_all _ (fun _ => zero_le_one), by simp⟩

theorem integral_sinHarm_sq_ex011 : ∫ x, sinHarm 1 x ^ 2 ∂haar 1 = 1 / 2 := by
  rw [integral_haar_one (fun x => sinHarm 1 x ^ 2) ((continuous_sinHarm 1).pow 2)]
  have : ∀ t : ℝ, sinHarm 1 (pt t) ^ 2 = Real.sin (2 * Real.pi * t) ^ 2 := by
    intro t; rw [sinHarm_pt]; simp
  simp only [this]
  exact DGPS.Analysis.CircleMoments.integral_sin_sq_two_pi

theorem ground_const_ex011 (h : ℝ) : ex010_ground h constDensity_ex011 = h ^ 2 / 2 := by
  have hF : DGPS.Analysis.circleFisherInformation constDensity_ex011 = 0 := by
    unfold DGPS.Analysis.circleFisherInformation
    have hae := weakGradient_ae_eq (isWeakGradient_const (d := 1) 1)
    have : (fun x => ‖weakGradient constDensity_ex011.sqrt constDensity_ex011.sqrt_mem x‖ ^ 2) =ᵐ[haar 1]
        fun _ => 0 := by
      filter_upwards [hae] with x hx
      have h0 : weakGradient constDensity_ex011.sqrt constDensity_ex011.sqrt_mem x = 0 := hx
      simp [h0]
    rw [integral_congr_ae this]; simp
  have hH : DGPS.Analysis.circleEntropy constDensity_ex011 = 0 := by
    rw [circleEntropy_eq]
    simp [constDensity_ex011, AbsoluteDensity.density]
  have hP : ex010_potential constDensity_ex011 = 1 / 2 := by
    unfold ex010_potential
    simpa [constDensity_ex011, AbsoluteDensity.density] using integral_sinHarm_sq_ex011
  unfold ex010_ground ex010_haarFisher
  rw [hF, hH, hP]; ring

/-- `ρ` minimizes `ex010_ground h` on the whole absolute domain. -/
def IsGroundMin_ex011 (h : ℝ) (ρ : AbsoluteDensity 1) : Prop :=
  ∀ ρ' : AbsoluteDensity 1, ex010_ground h ρ ≤ ex010_ground h ρ'

theorem quantitative_ex011 {h : ℝ} (hh : 0 ≤ h) {ρ : AbsoluteDensity 1}
    (hρ : IsGroundMin_ex011 h ρ) :
    ex010_ground h ρ ≤ h ^ 2 / 2 ∧ 0 ≤ ex010_ground h ρ ∧
    DGPS.Analysis.circleEntropy ρ ≤ Real.sqrt 3 * h ∧
    ex010_haarFisher ρ ≤ h ^ 2 / 2 + 2 * Real.sqrt 3 * h := by
  have hE : ex010_ground h ρ ≤ h ^ 2 / 2 := by
    have := hρ constDensity_ex011
    rwa [ground_const_ex011] at this
  have hr := ex010_remainder ρ
  have hP := mul_nonneg (sq_nonneg h) (ex010_potential_nonneg ρ)
  have hH0 := circleEntropy_nonneg ρ
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hEnn := ex010_ground_nonneg h ρ
  have hH : DGPS.Analysis.circleEntropy ρ ≤ Real.sqrt 3 * h := by
    by_contra hc
    replace hc := not_le.1 hc
    have h1 : (Real.sqrt 3 * h) ^ 2 < DGPS.Analysis.circleEntropy ρ ^ 2 :=
      pow_lt_pow_left₀ hc (by positivity) two_ne_zero
    have h2 : (Real.sqrt 3 * h) ^ 2 = 3 * h ^ 2 := by rw [mul_pow, hs3]
    unfold ex010_ground at hE
    nlinarith
  refine ⟨hE, hEnn, hH, ?_⟩
  unfold ex010_ground at hE
  nlinarith


theorem norm_sq_tangent_ex011 (y : Tangent 1) : ‖y‖ ^ 2 = (y 0) ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq]

theorem ground_eq_ex011 (h : ℝ) (ρ : AbsoluteDensity 1) :
    ex010_ground h ρ = (Real.pi ^ 2)⁻¹ * (∫ x, (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ∂haar 1)
      - 2 * ∫ x, eulF (ρ.sqrt x) ∂haar 1
      + h ^ 2 * ∫ x, ρ.sqrt x ^ 2 * sinHarm 1 x ^ 2 ∂haar 1 := by
  unfold ex010_ground ex010_haarFisher ex010_potential DGPS.Analysis.circleFisherInformation
  rw [circleEntropy_eq]
  simp only [AbsoluteDensity.density, norm_sq_tangent_ex011, eulF, DGPS.Circle.AngularNormalization.a0]
  have : (4 * Real.pi ^ 2) = 4 * Real.pi ^ 2 := rfl
  field_simp

theorem fisher_normAbs_ex011 {v : Torus 1 → ℝ} {G : Torus 1 → Tangent 1}
    (hG : IsWeakGradient v G) (hn : 0 < ∫ x, v x ^ 2 ∂haar 1) :
    DGPS.Analysis.circleFisherInformation (normAbs v ⟨G, hG⟩ hn) =
      4 * ((∫ x, (G x 0) ^ 2 ∂haar 1) / ∫ x, v x ^ 2 ∂haar 1) := by
  unfold DGPS.Analysis.circleFisherInformation
  congr 1
  set n := ∫ x, v x ^ 2 ∂haar 1 with hn_def
  have hGa := (hG.abs).smul (Real.sqrt n)⁻¹
  have hu : IsWeakGradient (normAbs v ⟨G, hG⟩ hn).sqrt
      (fun x => (Real.sqrt n)⁻¹ • (if 0 < v x then G x else if v x < 0 then -G x else 0)) :=
    hGa.congr_ae (Eventually.of_forall fun x => by simp [normAbs, div_eq_inv_mul, hn_def])
      (Eventually.of_forall fun x => rfl)
  have hae := weakGradient_ae_eq hu
  rw [← integral_div]
  have hsn : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn.le
  have hsp : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  refine integral_congr_ae ?_
  filter_upwards [hae, hG.ae_grad_eq_zero 0] with x hx hz
  have hx0 : weakGradient (normAbs v ⟨G, hG⟩ hn).sqrt (normAbs v ⟨G, hG⟩ hn).sqrt_mem x 0 =
      (Real.sqrt n)⁻¹ * (if 0 < v x then G x 0 else if v x < 0 then -G x 0 else 0) := by
    have := congrArg (fun y : Tangent 1 => y 0) hx
    simp only at this
    rw [this]
    split_ifs <;> simp
  simp only [norm_sq_tangent_ex011]
  rw [hx0]
  rcases lt_trichotomy (v x) 0 with h1 | h1 | h1
  · have e : (if 0 < v x then G x 0 else if v x < 0 then -G x 0 else 0) = -G x 0 := by
      simp [not_lt.2 h1.le, h1]
    rw [e]
    field_simp
    rw [hsn]; ring
  · have := hz h1
    rw [h1]; simp [this]
  · have e : (if 0 < v x then G x 0 else if v x < 0 then -G x 0 else 0) = G x 0 := by
      simp [h1]
    rw [e]
    field_simp
    rw [hsn]; ring

theorem entropy_normAbs_ex011 {v : Torus 1 → ℝ} (hv : MemH1 v) (hn : 0 < ∫ x, v x ^ 2 ∂haar 1) :
    DGPS.Analysis.circleEntropy (normAbs v hv hn) =
      (∫ x, eulF (v x) ∂haar 1) / (∫ x, v x ^ 2 ∂haar 1) - Real.log (∫ x, v x ^ 2 ∂haar 1) := by
  rw [circleEntropy_eq]
  set n := ∫ x, v x ^ 2 ∂haar 1 with hn_def
  obtain ⟨G, hG⟩ := id hv
  have i1 : Integrable (fun x => eulF (v x)) (haar 1) :=
    integrable_sq_mul_log_sq_of_memH1 1 hv
  have i2 : Integrable (fun x => v x ^ 2) (haar 1) := hG.memLp.integrable_sq
  have : (fun x => (normAbs v hv hn).density x *
      Real.log ((normAbs v hv hn).density x)) =
      fun x => eulF (v x) / n - Real.log n * (v x ^ 2 / n) := by
    funext x
    rw [normAbs_density]
    by_cases h0 : v x = 0
    · simp [h0, eulF]
    · have : v x ^ 2 ≠ 0 := pow_ne_zero 2 h0
      rw [Real.log_div this hn.ne']
      simp only [eulF]
      ring
  rw [this, integral_sub (i1.div_const _) ((i2.div_const _).const_mul _), integral_div,
    integral_const_mul, integral_div, ← hn_def]
  field_simp

theorem potential_normAbs_ex011 {v : Torus 1 → ℝ} (hv : MemH1 v) (hn : 0 < ∫ x, v x ^ 2 ∂haar 1) :
    ex010_potential (normAbs v hv hn) =
      (∫ x, v x ^ 2 * sinHarm 1 x ^ 2 ∂haar 1) / (∫ x, v x ^ 2 ∂haar 1) := by
  unfold ex010_potential
  rw [← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [normAbs_density]
  ring

theorem ground_normAbs_ex011 (h : ℝ) {v : Torus 1 → ℝ} {G : Torus 1 → Tangent 1}
    (hG : IsWeakGradient v G) (hn : 0 < ∫ x, v x ^ 2 ∂haar 1) :
    ex010_ground h (normAbs v ⟨G, hG⟩ hn) =
      (Real.pi ^ 2)⁻¹ * ((∫ x, (G x 0) ^ 2 ∂haar 1) / ∫ x, v x ^ 2 ∂haar 1)
      - 2 * ((∫ x, eulF (v x) ∂haar 1) / (∫ x, v x ^ 2 ∂haar 1) - Real.log (∫ x, v x ^ 2 ∂haar 1))
      + h ^ 2 * ((∫ x, v x ^ 2 * sinHarm 1 x ^ 2 ∂haar 1) / (∫ x, v x ^ 2 ∂haar 1)) := by
  unfold ex010_ground ex010_haarFisher
  rw [fisher_normAbs_ex011 hG hn, entropy_normAbs_ex011 ⟨G, hG⟩ hn,
    potential_normAbs_ex011 ⟨G, hG⟩ hn]
  simp only [DGPS.Circle.AngularNormalization.a0]
  field_simp

theorem euler_scalar_ex011 {A n Φ S : ℝ → ℝ} {A' n' Φ' S' c k : ℝ}
    (hA : HasDerivAt A A' 0) (hn : HasDerivAt n n' 0) (hΦ : HasDerivAt Φ Φ' 0)
    (hS : HasDerivAt S S' 0) (hn0 : n 0 = 1)
    (hmin : ∀ᶠ t in 𝓝 (0:ℝ), 0 < n t →
      c * A 0 - 2 * Φ 0 + k * S 0 ≤
        c * (A t / n t) - 2 * (Φ t / n t - Real.log (n t)) + k * (S t / n t)) :
    c * (A' - A 0 * n') - 2 * (Φ' - Φ 0 * n' - n') + k * (S' - S 0 * n') = 0 := by
  have hn1 : n 0 ≠ 0 := by rw [hn0]; exact one_ne_zero
  set F : ℝ → ℝ := fun t => c * (A t / n t) - 2 * (Φ t / n t - Real.log (n t)) +
    k * (S t / n t) with hF
  have hd : HasDerivAt F (c * ((A' * n 0 - A 0 * n') / n 0 ^ 2) -
      2 * ((Φ' * n 0 - Φ 0 * n') / n 0 ^ 2 - n' / n 0) +
      k * ((S' * n 0 - S 0 * n') / n 0 ^ 2)) 0 :=
    (((hA.div hn hn1).const_mul c).sub (((hΦ.div hn hn1).sub (hn.log hn1)).const_mul 2)).add
      ((hS.div hn hn1).const_mul k)
  have hnpos : ∀ᶠ t in 𝓝 (0:ℝ), 0 < n t :=
    hn.continuousAt.eventually (lt_mem_nhds (by rw [hn0]; exact one_pos))
  have hloc : IsLocalMin F 0 := by
    filter_upwards [hmin, hnpos] with t h1 h2
    have := h1 h2
    have e0 : F 0 = c * A 0 - 2 * Φ 0 + k * S 0 := by simp [hF, hn0]
    show F 0 ≤ F t
    rw [e0]; exact this
  have h0 := hloc.hasDerivAt_eq_zero hd
  rw [hn0] at h0
  simpa using h0

theorem weakEuler_ex011 (h : ℝ) {ρ : AbsoluteDensity 1} (hρ : IsGroundMin_ex011 h ρ)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    ∫ x, weakGradient ρ.sqrt ρ.sqrt_mem x 0 * G x 0 ∂haar 1 =
      Real.pi ^ 2 * ∫ x, ρ.sqrt x * φ x *
        (ex010_ground h ρ + 2 * Real.log (ρ.sqrt x ^ 2) - h ^ 2 * sinHarm 1 x ^ 2) ∂haar 1 := by
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  have hEq := ground_eq_ex011 h ρ
  have hw1 : ∫ x, ρ.sqrt x ^ 2 ∂haar 1 = 1 := ρ.mass_one
  obtain ⟨w, hwdef⟩ : ∃ w, w = ρ.sqrt := ⟨_, rfl⟩
  obtain ⟨Gw, hGwdef⟩ : ∃ Gw, Gw = weakGradient ρ.sqrt ρ.sqrt_mem := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E, E = ex010_ground h ρ := ⟨_, rfl⟩
  have hρ' : ∀ ρ' : AbsoluteDensity 1, E ≤ ex010_ground h ρ' := by rw [hEdef]; exact hρ
  rw [← hGwdef] at hw hEq ⊢
  rw [← hwdef] at hw hw1 hEq ⊢
  rw [← hEdef] at hEq ⊢
  set k := h ^ 2 with hk
  obtain ⟨s, hsdef⟩ : ∃ s : Torus 1 → ℝ, s = fun x => sinHarm 1 x ^ 2 := ⟨_, rfl⟩
  have hsc : AEStronglyMeasurable s (haar 1) := by
    rw [hsdef]; exact ((continuous_sinHarm 1).pow 2).aestronglyMeasurable
  have hsb : ∀ x, |s x| ≤ 1 := fun x => by
    rw [hsdef]; simp only
    rw [abs_pow]
    simpa using pow_le_one₀ (abs_nonneg _) (ex010_sin_bound x) (n := 2)
  have hone : AEStronglyMeasurable (fun _ : Torus 1 => (1:ℝ)) (haar 1) := aestronglyMeasurable_const
  have hv : ∀ t : ℝ, IsWeakGradient (fun x => w x + t * φ x) (fun x => Gw x + t • G x) :=
    fun t => hw.add (hφ.smul t)
  have hnf : HasDerivAt (fun t : ℝ => ∫ x, (w x + t * φ x) ^ 2 ∂haar 1)
      (2 * ∫ x, w x * φ x ∂haar 1) 0 := by
    have := hasDerivAt_integral_quad (c := fun _ => (1:ℝ)) (C := 1) hone
      (fun x => by simp) hw.memLp hφ.memLp
    simpa using this
  have hAf : HasDerivAt (fun t : ℝ => ∫ x, (Gw x 0 + t * G x 0) ^ 2 ∂haar 1)
      (2 * ∫ x, Gw x 0 * G x 0 ∂haar 1) 0 := by
    have := hasDerivAt_integral_quad (c := fun _ => (1:ℝ)) (C := 1) hone
      (fun x => by simp) (memLp_coord hw.memLp_grad 0) (memLp_coord hφ.memLp_grad 0)
    simpa using this
  have hSf : HasDerivAt (fun t : ℝ => ∫ x, (w x + t * φ x) ^ 2 * s x ∂haar 1)
      (2 * ∫ x, w x * φ x * s x ∂haar 1) 0 :=
    hasDerivAt_integral_quad hsc hsb hw.memLp hφ.memLp
  have hΦf := hasDerivAt_integral_eulF hw hφ
  have hn0 : (∫ x, (w x + (0:ℝ) * φ x) ^ 2 ∂haar 1) = 1 := by simpa using hw1
  have hnpos : ∀ᶠ t in 𝓝 (0:ℝ), 0 < ∫ x, (w x + t * φ x) ^ 2 ∂haar 1 :=
    hnf.continuousAt.eventually (lt_mem_nhds (by
      show (0:ℝ) < ∫ x, (w x + (0:ℝ) * φ x) ^ 2 ∂haar 1; rw [hn0]; exact one_pos))
  have hE0 : E = (Real.pi ^ 2)⁻¹ * (∫ x, (Gw x 0 + (0:ℝ) * G x 0) ^ 2 ∂haar 1) -
      2 * ∫ x, eulF (w x + (0:ℝ) * φ x) ∂haar 1 +
      k * ∫ x, (w x + (0:ℝ) * φ x) ^ 2 * s x ∂haar 1 := by
    rw [hEq, hsdef]; simp
  have hmin' : ∀ᶠ t in 𝓝 (0:ℝ), 0 < ∫ x, (w x + t * φ x) ^ 2 ∂haar 1 →
      (Real.pi ^ 2)⁻¹ * (∫ x, (Gw x 0 + (0:ℝ) * G x 0) ^ 2 ∂haar 1) -
        2 * ∫ x, eulF (w x + (0:ℝ) * φ x) ∂haar 1 +
        k * ∫ x, (w x + (0:ℝ) * φ x) ^ 2 * s x ∂haar 1 ≤
      (Real.pi ^ 2)⁻¹ * ((∫ x, (Gw x 0 + t * G x 0) ^ 2 ∂haar 1) /
          ∫ x, (w x + t * φ x) ^ 2 ∂haar 1) -
        2 * ((∫ x, eulF (w x + t * φ x) ∂haar 1) / (∫ x, (w x + t * φ x) ^ 2 ∂haar 1) -
          Real.log (∫ x, (w x + t * φ x) ^ 2 ∂haar 1)) +
        k * ((∫ x, (w x + t * φ x) ^ 2 * s x ∂haar 1) / ∫ x, (w x + t * φ x) ^ 2 ∂haar 1) := by
    filter_upwards with t hnt
    have hvm : MemH1 (fun x => w x + t * φ x) := ⟨_, hv t⟩
    have := hρ' (normAbs _ ⟨_, hv t⟩ hnt)
    rw [ground_normAbs_ex011 h (hv t) hnt] at this
    rw [← hE0]
    have e : (fun x => (Gw x + t • G x) 0 ^ 2) = fun x => (Gw x 0 + t * G x 0) ^ 2 := by
      funext x; simp
    simp only [e, hsdef, hk] at this ⊢
    exact this
  have key := euler_scalar_ex011 (c := (Real.pi ^ 2)⁻¹) (k := k) hAf hnf hΦf hSf hn0 hmin'
  have i1 := integrable_mul_mul_log hw hφ
  have i0 : Integrable (fun x => w x * φ x) (haar 1) := hw.memLp.integrable_mul hφ.memLp
  have i2 : Integrable (fun x => w x * φ x * s x) (haar 1) :=
    integrable_mul_bdd_two hsc hsb hw.memLp hφ.memLp
  have hΦ' : ∫ x, eulF' (w x) * φ x ∂haar 1 =
      2 * ∫ x, w x * φ x * Real.log (w x ^ 2) ∂haar 1 + 2 * ∫ x, w x * φ x ∂haar 1 := by
    have e : (fun x => eulF' (w x) * φ x) =
        fun x => 2 * (w x * φ x * Real.log (w x ^ 2)) + 2 * (w x * φ x) := by
      funext x; simp only [eulF']; ring
    rw [e, integral_add (i1.const_mul 2) (i0.const_mul 2), integral_const_mul,
      integral_const_mul]
  have hrhs : ∫ x, w x * φ x * (E + 2 * Real.log (w x ^ 2) - k * s x) ∂haar 1 =
      E * ∫ x, w x * φ x ∂haar 1 + 2 * ∫ x, w x * φ x * Real.log (w x ^ 2) ∂haar 1 -
        k * ∫ x, w x * φ x * s x ∂haar 1 := by
    have e : (fun x => w x * φ x * (E + 2 * Real.log (w x ^ 2) - k * s x)) =
        fun x => (E * (w x * φ x) + 2 * (w x * φ x * Real.log (w x ^ 2))) -
          k * (w x * φ x * s x) := by funext x; ring
    have j1 : Integrable (fun x => E * (w x * φ x)) (haar 1) := i0.const_mul E
    have j2 : Integrable (fun x => 2 * (w x * φ x * Real.log (w x ^ 2))) (haar 1) :=
      i1.const_mul 2
    have j3 : Integrable (fun x => k * (w x * φ x * s x)) (haar 1) := i2.const_mul k
    have j12 : Integrable (fun x => E * (w x * φ x) + 2 * (w x * φ x * Real.log (w x ^ 2)))
        (haar 1) := j1.add j2
    rw [e, integral_sub j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
      integral_const_mul]
  have hrhs' : ∫ x, w x * φ x * (E + 2 * Real.log (w x ^ 2) - k * sinHarm 1 x ^ 2) ∂haar 1 =
      ∫ x, w x * φ x * (E + 2 * Real.log (w x ^ 2) - k * s x) ∂haar 1 := by
    simp only [hsdef]
  rw [hrhs', hrhs]
  simp only [zero_mul, add_zero] at hE0 key
  rw [hΦ'] at key
  have hp : Real.pi ^ 2 ≠ 0 := by positivity
  generalize (∫ x, Gw x 0 * G x 0 ∂haar 1) = B at key ⊢
  generalize (∫ x, w x * φ x ∂haar 1) = a at key ⊢
  generalize (∫ x, w x * φ x * Real.log (w x ^ 2) ∂haar 1) = M1 at key ⊢
  generalize (∫ x, w x * φ x * s x ∂haar 1) = M2 at key ⊢
  generalize (∫ x, (Gw x 0) ^ 2 ∂haar 1) = A0 at key hE0 ⊢
  generalize (∫ x, eulF (w x) ∂haar 1) = Φ0 at key hE0 ⊢
  generalize (∫ x, w x ^ 2 * s x ∂haar 1) = S0 at key hE0 ⊢
  field_simp at key hE0
  linear_combination (1/2) * key - a * hE0

theorem fisher_eq_ex011 (ρ : AbsoluteDensity 1) :
    ex010_haarFisher ρ =
      (Real.pi ^ 2)⁻¹ * ∫ x, (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ∂haar 1 := by
  unfold ex010_haarFisher DGPS.Analysis.circleFisherInformation
  simp only [norm_sq_tangent_ex011, DGPS.Circle.AngularNormalization.a0]
  field_simp

/-- `‖∇√ρ‖₂²` in terms of the Haar Fisher information. -/
theorem gradNorm_sq_ex011 (ρ : AbsoluteDensity 1) :
    (eLpNorm (weakGradient ρ.sqrt ρ.sqrt_mem) 2 (haar 1)).toReal ^ 2 =
      Real.pi ^ 2 * ex010_haarFisher ρ := by
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  rw [toReal_eLpNorm_two_vec hw.memLp_grad, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _),
    fisher_eq_ex011]
  simp only [norm_sq_tangent_ex011]
  have : Real.pi ^ 2 ≠ 0 := by positivity
  field_simp

theorem closeness_ex011 {ρ : AbsoluteDensity 1} {Wc : Torus 1 → ℝ} (hWc : Continuous Wc)
    (hae : Wc =ᵐ[haar 1] ρ.sqrt) {γ : ℝ}
    (hm : ∀ x, |Wc x - ∫ y, ρ.sqrt y ∂haar 1| ≤ γ) (x : Torus 1) :
    |Wc x - 1| ≤ γ + γ ^ 2 := by
  set m := ∫ y, ρ.sqrt y ∂haar 1 with hmdef
  have hmW : ∫ y, Wc y ∂haar 1 = m := integral_congr_ae hae
  have hW2 : ∫ y, Wc y ^ 2 ∂haar 1 = 1 := by
    calc ∫ y, Wc y ^ 2 ∂haar 1 = ∫ y, ρ.sqrt y ^ 2 ∂haar 1 :=
          integral_congr_ae (hae.mono fun y hy => by simp [hy])
      _ = 1 := ρ.mass_one
  have iW : Integrable Wc (haar 1) := (memLp_two_of_continuous hWc).integrable one_le_two
  have iW2 : Integrable (fun y => Wc y ^ 2) (haar 1) := (memLp_two_of_continuous hWc).integrable_sq
  have hexp : ∫ y, (Wc y - m) ^ 2 ∂haar 1 = 1 - m ^ 2 := by
    have : (fun y => (Wc y - m) ^ 2) = fun y => Wc y ^ 2 - 2 * m * Wc y + m ^ 2 := by
      funext y; ring
    have j2 : Integrable (fun y => 2 * m * Wc y) (haar 1) := iW.const_mul _
    have j12 : Integrable (fun y => Wc y ^ 2 - 2 * m * Wc y) (haar 1) := iW2.sub j2
    have j3 : Integrable (fun _ : Torus 1 => m ^ 2) (haar 1) := integrable_const _
    rw [this, integral_add j12 j3, integral_sub iW2 j2, integral_const_mul, hW2, hmW]
    simp; ring
  have hlo : 0 ≤ ∫ y, (Wc y - m) ^ 2 ∂haar 1 := integral_nonneg fun y => sq_nonneg _
  have hhi : ∫ y, (Wc y - m) ^ 2 ∂haar 1 ≤ γ ^ 2 := by
    have : ∀ y, ‖(Wc y - m) ^ 2‖ ≤ γ ^ 2 := fun y => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hm y) 2
    have := norm_integral_le_of_norm_le_const (μ := haar 1) (f := fun y => (Wc y - m) ^ 2)
      (Eventually.of_forall this)
    simp at this
    exact (le_abs_self _).trans this
  have hm0 : 0 ≤ m := integral_nonneg_of_ae ρ.sqrt_nonneg
  have hm1 : m ≤ 1 := by nlinarith
  have hm2 : 1 - γ ^ 2 ≤ m := by
    by_contra hc
    replace hc := not_le.1 hc
    have h1 : 0 ≤ 1 - γ ^ 2 := by nlinarith
    nlinarith [sq_nonneg γ]
  have := hm x
  rw [abs_le] at this ⊢
  constructor <;> nlinarith [this.1, this.2]

theorem gamma_bound_ex011 {h : ℝ} (hh0 : 0 ≤ h) {ρ : AbsoluteDensity 1}
    (hρ : IsGroundMin_ex011 h ρ) :
    (eLpNorm (weakGradient ρ.sqrt ρ.sqrt_mem) 2 (haar 1)).toReal ^ 2 ≤
      Real.pi ^ 2 * (h ^ 2 / 2 + 2 * Real.sqrt 3 * h) := by
  rw [gradNorm_sq_ex011]
  exact mul_le_mul_of_nonneg_left (quantitative_ex011 hh0 hρ).2.2.2 (by positivity)

theorem gamma_small_ex011 {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 1000) :
    Real.pi ^ 2 * (h ^ 2 / 2 + 2 * Real.sqrt 3 * h) ≤ 1 / 25 := by
  have hpi : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hs : Real.sqrt 3 ≤ 7 / 4 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have h1 : h ^ 2 / 2 + 2 * Real.sqrt 3 * h ≤ 1 / 250 := by nlinarith
  have : 0 ≤ h ^ 2 / 2 + 2 * Real.sqrt 3 * h := by positivity
  nlinarith

theorem sinHarm_sq_pt_ex011 (t : ℝ) : sinHarm 1 (pt t) ^ 2 = Real.sin (2 * Real.pi * t) ^ 2 := by
  rw [sinHarm_pt]; simp

theorem weakDeriv_ex011 {h : ℝ} {ρ : AbsoluteDensity 1} (hρ : IsGroundMin_ex011 h ρ)
    {Wc : Torus 1 → ℝ} (hWc : Continuous Wc) (hae : Wc =ᵐ[haar 1] ρ.sqrt)
    (hW0 : ∀ x, 0 < Wc x) :
    IsWeakGradient (fun x => weakGradient ρ.sqrt ρ.sqrt_mem x 0)
      (vec1 fun x => -(Real.pi ^ 2 * (Wc x * (ex010_ground h ρ + 2 * Real.log (Wc x ^ 2) -
        h ^ 2 * sinHarm 1 x ^ 2)))) := by
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  obtain ⟨Gw, hGw⟩ : ∃ Gw, Gw = weakGradient ρ.sqrt ρ.sqrt_mem := ⟨_, rfl⟩
  rw [← hGw] at hw ⊢
  have hTc : Continuous (fun x => Wc x * (ex010_ground h ρ + 2 * Real.log (Wc x ^ 2) -
      h ^ 2 * sinHarm 1 x ^ 2)) := by
    have := (hWc.pow 2).log fun x => (pow_pos (hW0 x) 2).ne'
    exact hWc.mul ((continuous_const.add (continuous_const.mul this)).sub
      (continuous_const.mul ((continuous_sinHarm 1).pow 2)))
  have hg1c : Continuous (fun x => -(Real.pi ^ 2 * (Wc x * (ex010_ground h ρ +
      2 * Real.log (Wc x ^ 2) - h ^ 2 * sinHarm 1 x ^ 2)))) := (continuous_const.mul hTc).neg
  refine ⟨memLp_coord hw.memLp_grad 0, memLp_vec1 (memLp_two_of_continuous hg1c), ?_⟩
  intro φ hφ j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  have E1 := weakEuler_ex011 h hρ hφ.isWeakGradient
  rw [← hGw] at E1
  have hφc : Continuous φ := hφ.continuous_torus
  have e1 : ∫ x, Gw x 0 * smoothGrad φ x 0 ∂haar 1 =
      ∫ x, Gw x 0 * coordPartial 0 φ x ∂haar 1 := by
    simp only [smoothGrad_apply]
  have e2 : ∫ x, ρ.sqrt x * φ x * (ex010_ground h ρ + 2 * Real.log (ρ.sqrt x ^ 2) -
      h ^ 2 * sinHarm 1 x ^ 2) ∂haar 1 =
      ∫ x, (Wc x * (ex010_ground h ρ + 2 * Real.log (Wc x ^ 2) - h ^ 2 * sinHarm 1 x ^ 2)) * φ x
        ∂haar 1 :=
    integral_congr_ae (hae.mono fun x hx => by simp only [← hx]; ring)
  rw [e1, e2] at E1
  have e3 : ∫ x, vec1 (fun x => -(Real.pi ^ 2 * (Wc x * (ex010_ground h ρ +
      2 * Real.log (Wc x ^ 2) - h ^ 2 * sinHarm 1 x ^ 2)))) x 0 * φ x ∂haar 1 =
      -(Real.pi ^ 2 * ∫ x, (Wc x * (ex010_ground h ρ + 2 * Real.log (Wc x ^ 2) -
        h ^ 2 * sinHarm 1 x ^ 2)) * φ x ∂haar 1) := by
    simp only [vec1_apply]
    rw [← integral_const_mul, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only; ring
  rw [e3, E1]; ring

theorem regular_single_ex011 {h : ℝ} (hh0 : 0 ≤ h) {ρ : AbsoluteDensity 1}
    (hρ : IsGroundMin_ex011 h ρ) {Wc : Torus 1 → ℝ} (hWc : Continuous Wc)
    (hae : Wc =ᵐ[haar 1] ρ.sqrt) {δ : ℝ} (hδ0 : δ ≤ 1 / 2) (hδ : ∀ x, |Wc x - 1| ≤ δ) :
    ∃ Ac : Torus 1 → ℝ, Continuous Ac ∧
      (∀ t, HasDerivAt (fun s => Wc (pt s)) (Ac (pt t)) t) ∧
      (∀ t, HasDerivAt (fun s => Ac (pt s)) (Real.pi ^ 2 * (Wc (pt t) *
         (h ^ 2 * Real.sin (2 * Real.pi * t) ^ 2 - ex010_ground h ρ -
           2 * Real.log (Wc (pt t) ^ 2)))) t) ∧
      ∀ x, |Ac x| ≤ Real.pi ^ 2 * ((1 + δ) * (2 * h ^ 2 + 8 * δ)) := by
  have hW0 : ∀ x, 0 < Wc x := bs_Wc_pos hδ0 hδ
  have hA := weakDeriv_ex011 hρ hWc hae hW0
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  obtain ⟨Gw, hGw⟩ : ∃ Gw, Gw = weakGradient ρ.sqrt ρ.sqrt_mem := ⟨_, rfl⟩
  rw [← hGw] at hw hA
  obtain ⟨E, hEdef⟩ : ∃ E, E = ex010_ground h ρ := ⟨_, rfl⟩
  obtain ⟨hEle, hE0, -, -⟩ := quantitative_ex011 hh0 hρ
  rw [← hEdef] at hA hEle hE0 ⊢
  obtain ⟨g1, hg1⟩ : ∃ g1 : Torus 1 → ℝ, g1 = fun x => -(Real.pi ^ 2 * (Wc x * (E +
      2 * Real.log (Wc x ^ 2) - h ^ 2 * sinHarm 1 x ^ 2))) := ⟨_, rfl⟩
  have hg1c : Continuous g1 := by
    rw [hg1]
    have := (hWc.pow 2).log fun x => (pow_pos (hW0 x) 2).ne'
    exact (continuous_const.mul (hWc.mul ((continuous_const.add (continuous_const.mul this)).sub
      (continuous_const.mul ((continuous_sinHarm 1).pow 2))))).neg
  have hA' : IsWeakGradient (fun x => Gw x 0) (vec1 g1) := by rw [hg1]; exact hA
  obtain ⟨Ac, hAc, hAae, -, hmean⟩ := circle_H1_holder_half hA'
  have hAw : IsWeakGradient Ac (vec1 g1) := hA'.congr_ae hAae.symm (ae_eq_refl _)
  obtain ⟨hAd, -⟩ := circle_duBoisReymond hAc hAw (continuous_vec1 hg1c) (ae_eq_refl _)
  have hwW : IsWeakGradient Wc Gw := hw.congr_ae hae.symm (ae_eq_refl _)
  have hGae : Gw =ᵐ[haar 1] vec1 Ac := by
    filter_upwards [hAae] with x hx
    ext i
    fin_cases i
    simp [hx]
  obtain ⟨hWd, -⟩ := circle_duBoisReymond hWc hwW (continuous_vec1 hAc) hGae
  -- sup bound
  have hδp : 0 ≤ δ := (abs_nonneg _).trans (hδ 0)
  set C : ℝ := Real.pi ^ 2 * ((1 + δ) * (2 * h ^ 2 + 8 * δ)) with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hnb : ∀ᵐ x ∂haar 1, ‖vec1 g1 x‖ ≤ C := by
    refine Eventually.of_forall fun x => ?_
    rw [norm_vec1, hg1]
    simp only
    have h1 : |Wc x| ≤ 1 + δ := by
      have := abs_le.1 (hδ x)
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    have h2 : |Real.log (Wc x ^ 2)| ≤ 4 * δ := by
      have := abs_log_sq_le ((hδ x).trans hδ0)
      linarith [hδ x]
    have h3 : sinHarm 1 x ^ 2 ≤ 1 := by
      have := ex010_sin_bound x
      nlinarith [abs_nonneg (sinHarm 1 x), sq_abs (sinHarm 1 x)]
    have h3' : 0 ≤ sinHarm 1 x ^ 2 := sq_nonneg _
    have h4 : |E + 2 * Real.log (Wc x ^ 2) - h ^ 2 * sinHarm 1 x ^ 2| ≤ 2 * h ^ 2 + 8 * δ := by
      have hh2 : 0 ≤ h ^ 2 := sq_nonneg h
      have := abs_le.1 h2
      rw [abs_le]
      constructor <;> nlinarith [mul_le_mul_of_nonneg_left h3 hh2, mul_nonneg hh2 h3']
    rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.pi ^ 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul h1 h4 (abs_nonneg _) (by linarith)
  have hg1m : MemLp (vec1 g1) 2 (haar 1) := hA'.memLp_grad
  have hel : (eLpNorm (vec1 g1) 2 (haar 1)).toReal ≤ C := by
    have := eLpNorm_le_of_ae_bound (p := 2) hg1m.aestronglyMeasurable hnb
    simp only [measure_univ, ENNReal.one_rpow, one_mul] at this
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top this
    rwa [ENNReal.toReal_ofReal hC0] at h2
  have hint0 : ∫ y, Gw y 0 ∂haar 1 = 0 := bs_integral_grad hw
  refine ⟨Ac, hAc, ?_, ?_, fun x => ?_⟩
  · intro t
    have := hWd t
    simpa using this
  · intro t
    have := hAd t
    simp only [vec1_apply, hg1, sinHarm_sq_pt_ex011] at this
    convert this using 1
    ring
  · have := hmean x
    rw [hint0, sub_zero] at this
    exact this.trans hel


theorem smooth_W_ex011 {h E : ℝ} {W A : ℝ → ℝ} (hW : ∀ t, 0 < W t)
    (hWd : ∀ t, HasDerivAt W (A t) t)
    (hAd : ∀ t, HasDerivAt A (Real.pi ^ 2 * (W t *
      (h ^ 2 * Real.sin (2 * Real.pi * t) ^ 2 - E - 2 * Real.log (W t ^ 2)))) t) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W := by
  have dW : deriv W = A := funext fun t => (hWd t).deriv
  have dA : deriv A = fun t => Real.pi ^ 2 * (W t *
      (h ^ 2 * Real.sin (2 * Real.pi * t) ^ 2 - E - 2 * Real.log (W t ^ 2))) :=
    funext fun t => (hAd t).deriv
  have key : ∀ n : ℕ, ContDiff ℝ n W ∧ ContDiff ℝ n A := by
    intro n
    induction n with
    | zero =>
      exact ⟨contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (hWd t).continuousAt),
        contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (hAd t).continuousAt)⟩
    | succ n ih =>
      obtain ⟨ihW, ihA⟩ := ih
      have hlog : ContDiff ℝ n (fun t => Real.log (W t ^ 2)) :=
        (ihW.pow 2).log fun t => (pow_pos (hW t) 2).ne'
      have hsin : ContDiff ℝ n (fun t : ℝ => Real.sin (2 * Real.pi * t)) := by fun_prop
      rw [Nat.cast_succ]
      refine ⟨?_, ?_⟩
      · refine contDiff_succ_iff_deriv.2 ⟨fun t => (hWd t).differentiableAt, ?_, ?_⟩
        · intro hn; exact absurd hn (by simp)
        · rw [dW]; exact ihA
      · refine contDiff_succ_iff_deriv.2 ⟨fun t => (hAd t).differentiableAt, ?_, ?_⟩
        · intro hn; exact absurd hn (by simp)
        · rw [dA]
          exact contDiff_const.mul (ihW.mul (((contDiff_const.mul (hsin.pow 2)).sub
            contDiff_const).sub (contDiff_const.mul hlog)))
  exact contDiff_infty.2 fun n => (key n).1

theorem isSmooth_sq_ex011 {Wc : Torus 1 → ℝ} (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => Wc (pt s))) :
    IsSmoothPeriodic (fun x => Wc x ^ 2) := by
  unfold IsSmoothPeriodic
  have : ((fun x => Wc x ^ 2) ∘ torusLift) = fun y : Fin 1 → ℝ => (Wc (pt (y 0))) ^ 2 := by
    funext y
    have : torusLift y = pt (y 0) := by
      show torusLift y = torusLift (fun _ => y 0)
      congr 1; funext i; fin_cases i; rfl
    simp [this]
  rw [this]
  exact (hs.comp (contDiff_apply ℝ ℝ (0 : Fin 1))).pow 2



/-! ### Small-data analysis of the log-profile ODE -/

noncomputable def sqF_ex011 (t : ℝ) : ℝ := Real.sin (2 * Real.pi * t) ^ 2

noncomputable def dsqF_ex011 (t : ℝ) : ℝ :=
  4 * Real.pi * (Real.sin (2 * Real.pi * t) * Real.cos (2 * Real.pi * t))

theorem hasDerivAt_sqF_ex011 (t : ℝ) : HasDerivAt sqF_ex011 (dsqF_ex011 t) t := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * t) (2 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
  have h3 := (h1.sin).pow 2
  unfold sqF_ex011 dsqF_ex011
  convert h3 using 1
  simp
  ring

theorem abs_sqF_ex011 (t : ℝ) : |sqF_ex011 t| ≤ 1 := by
  unfold sqF_ex011
  rw [abs_of_nonneg (sq_nonneg _)]
  exact Real.sin_sq_le_one _

theorem abs_dsqF_ex011 (t : ℝ) : |dsqF_ex011 t| ≤ 4 * Real.pi := by
  unfold dsqF_ex011
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4), abs_of_pos Real.pi_pos]
  have h1 := Real.abs_sin_le_one (2 * Real.pi * t)
  have h2 := Real.abs_cos_le_one (2 * Real.pi * t)
  have : |Real.sin (2 * Real.pi * t)| * |Real.cos (2 * Real.pi * t)| ≤ 1 * 1 :=
    mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
  have h3 : |Real.sin (2 * Real.pi * t) * Real.cos (2 * Real.pi * t)| ≤ 1 := by
    rw [abs_mul]; simpa using this
  nlinarith [Real.pi_pos]

theorem continuous_sqF_ex011 : Continuous sqF_ex011 := by unfold sqF_ex011; fun_prop

theorem continuous_dsqF_ex011 : Continuous dsqF_ex011 := by unfold dsqF_ex011; fun_prop

noncomputable def v1E_ex011 (h E : ℝ) (A W : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.pi ^ 2 * (h ^ 2 * sqF_ex011 t - E - 2 * fF W t) - vF A W t ^ 2

noncomputable def v2E_ex011 (h E : ℝ) (A W : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.pi ^ 2 * (h ^ 2 * dsqF_ex011 t - 4 * vF A W t) - 2 * vF A W t * v1E_ex011 h E A W t

section Chain011

variable {h E : ℝ} {A W : ℝ → ℝ}

theorem hd_f_ex011 (hWd : ∀ t, HasDerivAt W (A t) t) (hW : ∀ t, 0 < W t) (t : ℝ) :
    HasDerivAt (fF W) (2 * vF A W t) t := by
  have h := ((hWd t).pow 2).log (pow_pos (hW t) 2).ne'
  unfold fF vF
  convert h using 1
  have := (hW t).ne'
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem hd_v_ex011 (hWd : ∀ t, HasDerivAt W (A t) t)
    (hAd : ∀ t, HasDerivAt A (Real.pi ^ 2 * (W t *
      (h ^ 2 * Real.sin (2 * Real.pi * t) ^ 2 - E - 2 * Real.log (W t ^ 2)))) t)
    (hW : ∀ t, 0 < W t) (t : ℝ) : HasDerivAt (vF A W) (v1E_ex011 h E A W t) t := by
  have h1 := (hAd t).div (hWd t) (hW t).ne'
  unfold vF v1E_ex011 sqF_ex011 fF vF
  convert h1 using 1
  have := (hW t).ne'
  field_simp

theorem hd_v1_ex011 (hWd : ∀ t, HasDerivAt W (A t) t)
    (hAd : ∀ t, HasDerivAt A (Real.pi ^ 2 * (W t *
      (h ^ 2 * Real.sin (2 * Real.pi * t) ^ 2 - E - 2 * Real.log (W t ^ 2)))) t)
    (hW : ∀ t, 0 < W t) (t : ℝ) : HasDerivAt (v1E_ex011 h E A W) (v2E_ex011 h E A W t) t := by
  have hv := hd_v_ex011 hWd hAd hW t
  have hf := hd_f_ex011 hWd hW t
  have hs := hasDerivAt_sqF_ex011 t
  have h1 := ((((hs.const_mul (h ^ 2)).sub_const E).sub (hf.const_mul 2)).const_mul
    (Real.pi ^ 2)).sub (hv.pow 2)
  unfold v1E_ex011 v2E_ex011
  convert h1 using 1
  simp only [Nat.cast_ofNat]
  ring

end Chain011

section Regular011

variable {α : ℝ} {h E : ℝ} {A W : ℝ → ℝ}

theorem isPH_fF_ex011 (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hWp : Function.Periodic W 1)
    (hWd : ∀ t, HasDerivAt W (A t) t)
    (hAd : ∀ t, HasDerivAt A (Real.pi ^ 2 * (W t *
      (h ^ 2 * Real.sin (2 * Real.pi * t) ^ 2 - E - 2 * Real.log (W t ^ 2)))) t)
    (hW : ∀ t, 0 < W t) :
    IsPH α 2 (fF W) ∧ deriv (fF W) = (fun t => 2 * vF A W t) ∧
      deriv (fun t => 2 * vF A W t) = (fun t => 2 * v1E_ex011 h E A W t) ∧
      deriv (fun t => 2 * v1E_ex011 h E A W t) = (fun t => 2 * v2E_ex011 h E A W t) := by
  have hper : Function.Periodic (fF W) 1 := fun t => by simp [fF, hWp t]
  have hF0 := hd_f_ex011 hWd hW
  have hF1 : ∀ t, HasDerivAt (fun t => 2 * vF A W t) (2 * v1E_ex011 h E A W t) t := fun t =>
    (hd_v_ex011 hWd hAd hW t).const_mul 2
  have hF2 : ∀ t, HasDerivAt (fun t => 2 * v1E_ex011 h E A W t) (2 * v2E_ex011 h E A W t) t :=
    fun t => (hd_v1_ex011 hWd hAd hW t).const_mul 2
  have e1 : deriv (fF W) = (fun t => 2 * vF A W t) := funext fun t => (hF0 t).deriv
  have e2 : deriv (fun t => 2 * vF A W t) = (fun t => 2 * v1E_ex011 h E A W t) :=
    funext fun t => (hF1 t).deriv
  have e3 : deriv (fun t => 2 * v1E_ex011 h E A W t) = (fun t => 2 * v2E_ex011 h E A W t) :=
    funext fun t => (hF2 t).deriv
  refine ⟨?_, e1, e2, e3⟩
  have hp1 : Function.Periodic (fun t => 2 * vF A W t) 1 := e1 ▸ periodic_deriv hper
  have hp2 : Function.Periodic (fun t => 2 * v1E_ex011 h E A W t) 1 := e2 ▸ periodic_deriv hp1
  have hp3 : Function.Periodic (fun t => 2 * v2E_ex011 h E A W t) 1 := e3 ▸ periodic_deriv hp2
  have hd2 : Differentiable ℝ (fun t => 2 * v1E_ex011 h E A W t) := fun t => (hF2 t).differentiableAt
  have hcv : Continuous (vF A W) := continuous_iff_continuousAt.2 fun t =>
    (hd_v_ex011 hWd hAd hW t).continuousAt
  have hc1 : Continuous (v1E_ex011 h E A W) := continuous_iff_continuousAt.2 fun t =>
    (hd_v1_ex011 hWd hAd hW t).continuousAt
  have hc3 : Continuous (fun t => 2 * v2E_ex011 h E A W t) := by
    have : (fun t => 2 * v2E_ex011 h E A W t) = fun t => 2 * (Real.pi ^ 2 *
        (h ^ 2 * dsqF_ex011 t - 4 * vF A W t) - 2 * vF A W t * v1E_ex011 h E A W t) := rfl
    rw [this]
    have := continuous_dsqF_ex011
    fun_prop
  have hb2 : Bdd (fun t => 2 * v1E_ex011 h E A W t) := periodic_bdd hp2 hd2.continuous
  have hb3 : Bdd (fun t => 2 * v2E_ex011 h E A W t) := periodic_bdd hp3 hc3
  refine ⟨hper, fun t => (hF0 t).differentiableAt, ?_⟩
  rw [e1]
  refine ⟨hp1, fun t => (hF1 t).differentiableAt, ?_⟩
  rw [e2]
  refine ⟨hp2, hd2.continuous, ?_⟩
  refine HolderBdd.of_le
    (C := supNorm (fun t => 2 * v2E_ex011 h E A W t) + 2 * supNorm (fun t => 2 * v1E_ex011 h E A W t))
    (add_nonneg (supNorm_nonneg _) (mul_nonneg two_pos.le (supNorm_nonneg _))) ?_
  have := holder_of_lip (supNorm_nonneg (fun t => 2 * v2E_ex011 h E A W t))
    (supNorm_nonneg (fun t => 2 * v1E_ex011 h E A W t))
    hα0 hα1 (u := fun t => 2 * v1E_ex011 h E A W t) (fun x y => by
      have := lip_bound hd2 (by rw [e3]; exact hb3) x y
      rwa [e3] at this) hb2.abs_le_supNorm
  exact this

end Regular011

theorem ode_small_ex011 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {h E : ℕ → ℝ} {A W : ℕ → ℝ → ℝ}
    (hh : Tendsto h atTop (𝓝 0)) (hE0 : ∀ j, 0 ≤ E j) (hE : ∀ j, E j ≤ h j ^ 2 / 2)
    (hWp : ∀ j, Function.Periodic (W j) 1)
    (hWd : ∀ j t, HasDerivAt (W j) (A j t) t)
    (hAd : ∀ j t, HasDerivAt (A j) (Real.pi ^ 2 * (W j t *
      (h j ^ 2 * Real.sin (2 * Real.pi * t) ^ 2 - E j - 2 * Real.log (W j t ^ 2)))) t)
    (hW1 : USmall (fun j t => W j t - 1)) (hA0 : USmall A) :
    ∀ ε > 0, ∀ᶠ j in atTop, (∀ t, 0 < W j t) ∧ IsPH α 2 (fF (W j)) ∧
      phNorm α 2 (fF (W j)) ≤ ε := by
  have hlow : ∀ᶠ j in atTop, ∀ t, |W j t - 1| ≤ 1 / 2 := hW1 (1 / 2) (by norm_num)
  have hpos : ∀ᶠ j in atTop, ∀ t, 0 < W j t := by
    filter_upwards [hlow] with j hj t
    have := (abs_le.1 (hj t)).1; linarith
  have hh2 : Tendsto (fun j => h j ^ 2) atTop (𝓝 0) := by simpa using hh.pow 2
  have hsq : USmall (fun j t => h j ^ 2 * sqF_ex011 t) :=
    USmall.of_abs_le (b := fun j => h j ^ 2) hh2 (fun j t => by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_sqF_ex011 t, sq_nonneg (h j)])
  have hdsq : USmall (fun j t => h j ^ 2 * dsqF_ex011 t) :=
    USmall.of_abs_le (b := fun j => 4 * Real.pi * h j ^ 2)
      (by simpa using hh2.const_mul (4 * Real.pi)) (fun j t => by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_dsqF_ex011 t, sq_nonneg (h j)])
  have hEs : USmall (fun j (_ : ℝ) => E j) :=
    USmall.of_abs_le (b := fun j => h j ^ 2 / 2) (by simpa using hh2.div_const 2)
      (fun j t => by rw [abs_of_nonneg (hE0 j)]; exact hE j)
  have hV : USmall (fun j t => vF (A j) (W j) t) := by
    refine hA0.of_le 2 ?_
    filter_upwards [hlow] with j hj t
    have h1 := (abs_le.1 (hj t)).1
    have hw : 1 / 2 ≤ W j t := by linarith
    unfold vF
    rw [abs_div, abs_of_pos (by linarith : 0 < W j t), div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg (A j t)]
  have hF : USmall (fun j t => fF (W j) t) := by
    refine hW1.of_le 4 ?_
    filter_upwards [hlow] with j hj t
    exact abs_log_sq_le (hj t)
  have hVb := hV.bdd
  have hv1 : USmall (fun j t => v1E_ex011 (h j) (E j) (A j) (W j) t) := by
    have e1 : USmall (fun j t => Real.pi ^ 2 * (h j ^ 2 * sqF_ex011 t - E j - 2 * fF (W j) t)) :=
      ((hsq.sub hEs).sub (hF.const_mul 2)).const_mul (Real.pi ^ 2)
    have e2 : USmall (fun j t => vF (A j) (W j) t ^ 2) :=
      USmall.congr (fun j t => by ring) (hV.mul_bdd 1 hVb)
    exact USmall.congr (fun j t => rfl) (e1.sub e2)
  have hv1b := hv1.bdd
  have hv2 : USmall (fun j t => v2E_ex011 (h j) (E j) (A j) (W j) t) := by
    have e1 : USmall (fun j t => Real.pi ^ 2 * (h j ^ 2 * dsqF_ex011 t - 4 * vF (A j) (W j) t)) :=
      (hdsq.sub (hV.const_mul 4)).const_mul (Real.pi ^ 2)
    have e2 : USmall (fun j t => 2 * vF (A j) (W j) t * v1E_ex011 (h j) (E j) (A j) (W j) t) :=
      (hV.const_mul 2).mul_bdd 1 hv1b
    exact USmall.congr (fun j t => rfl) (e1.sub e2)
  intro ε hε
  have hε6 : 0 < ε / 6 := by positivity
  filter_upwards [hpos, hF (ε / 6) hε6, (hV.const_mul 2) (ε / 6) hε6,
    (hv1.const_mul 2) (ε / 6) hε6, (hv2.const_mul 2) (ε / 6) hε6]
    with j hj hf0 hf1 hf2 hf3
  obtain ⟨hph, e1, e2, e3⟩ := isPH_fF_ex011 hα0.le hα1.le (hWp j) (hWd j) (hAd j) hj
  refine ⟨hj, hph, ?_⟩
  have hb2 : Bdd (fun t => 2 * v1E_ex011 (h j) (E j) (A j) (W j) t) := ⟨ε / 6, hf2⟩
  have hd2 : Differentiable ℝ (fun t => 2 * v1E_ex011 (h j) (E j) (A j) (W j) t) := fun t =>
    ((hd_v1_ex011 (hWd j) (hAd j) hj t).const_mul 2).differentiableAt
  have hb3 : Bdd (deriv (fun t => 2 * v1E_ex011 (h j) (E j) (A j) (W j) t)) := by
    rw [e3]; exact ⟨ε / 6, hf3⟩
  have hhold := holderSeminorm_le_succ hα0.le hα1.le hd2 hb2 hb3
  have s0 : supNorm (fF (W j)) ≤ ε / 6 := supNorm_le hf0
  have s1 : supNorm (fun t => 2 * vF (A j) (W j) t) ≤ ε / 6 := supNorm_le hf1
  have s2 : supNorm (fun t => 2 * v1E_ex011 (h j) (E j) (A j) (W j) t) ≤ ε / 6 := supNorm_le hf2
  have s3 : supNorm (deriv (fun t => 2 * v1E_ex011 (h j) (E j) (A j) (W j) t)) ≤ ε / 6 := by
    rw [e3]; exact supNorm_le hf3
  have hnorm : phNorm α 2 (fF (W j)) = supNorm (fF (W j)) + (supNorm (deriv (fF (W j))) +
      (supNorm (deriv (deriv (fF (W j)))) + holderSeminorm α (deriv (deriv (fF (W j)))))) := by
    simp [phNorm]
  rw [hnorm, e1, e2]
  linarith



/-! ### Packaging: one minimizer at small field -/

noncomputable def Qf_ex011 (h : ℝ) : ℝ := Real.pi ^ 2 * (h ^ 2 / 2 + 2 * Real.sqrt 3 * h)

noncomputable def Bf_ex011 (h : ℝ) : ℝ := Real.sqrt (Qf_ex011 h) + Qf_ex011 h

noncomputable def Cf_ex011 (h : ℝ) : ℝ :=
  Real.pi ^ 2 * ((1 + Bf_ex011 h) * (2 * h ^ 2 + 8 * Bf_ex011 h))

theorem continuous_Bf_ex011 : Continuous Bf_ex011 := by
  unfold Bf_ex011 Qf_ex011; fun_prop

theorem continuous_Cf_ex011 : Continuous Cf_ex011 := by
  have := continuous_Bf_ex011
  unfold Cf_ex011; fun_prop

theorem Bf_zero_ex011 : Bf_ex011 0 = 0 := by simp [Bf_ex011, Qf_ex011]

theorem Cf_zero_ex011 : Cf_ex011 0 = 0 := by simp [Cf_ex011, Bf_zero_ex011]

theorem Bf_nonneg_ex011 {h : ℝ} (hh : 0 ≤ h) : 0 ≤ Bf_ex011 h := by
  unfold Bf_ex011 Qf_ex011
  have : 0 ≤ Real.pi ^ 2 * (h ^ 2 / 2 + 2 * Real.sqrt 3 * h) := by positivity
  positivity

theorem package_ex011 {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 1000) {ρ : AbsoluteDensity 1}
    (hρ : IsGroundMin_ex011 h ρ) :
    ∃ Wc : Torus 1 → ℝ, Continuous Wc ∧ Wc =ᵐ[haar 1] ρ.sqrt ∧ ∃ δ : ℝ, δ ≤ Bf_ex011 h ∧
      δ ≤ 1 / 2 ∧ ∀ x, |Wc x - 1| ≤ δ := by
  obtain ⟨Wc, hc, hae, -, hm⟩ := circle_H1_holder_half (isWeakGradient_weakGradient ρ.sqrt_mem)
  set γ := (eLpNorm (weakGradient ρ.sqrt ρ.sqrt_mem) 2 (haar 1)).toReal with hγ
  have hγ0 : 0 ≤ γ := ENNReal.toReal_nonneg
  have hγ2 : γ ^ 2 ≤ Qf_ex011 h := gamma_bound_ex011 hh0 hρ
  have hQ : Qf_ex011 h ≤ 1 / 25 := gamma_small_ex011 hh0 hh1
  have hγs : γ ≤ Real.sqrt (Qf_ex011 h) := by
    have := Real.abs_le_sqrt hγ2
    rwa [abs_of_nonneg hγ0] at this
  have hγ5 : γ ≤ 1 / 5 := by nlinarith
  have hQ0 : 0 ≤ Qf_ex011 h := (sq_nonneg γ).trans hγ2
  refine ⟨Wc, hc, hae, γ + γ ^ 2, ?_, by nlinarith, fun x => closeness_ex011 hc hae hm x⟩
  unfold Bf_ex011
  linarith

theorem instance_ex011 {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 1000) {ρ : AbsoluteDensity 1}
    (hρ : IsGroundMin_ex011 h ρ) :
    ∃ Wc Ac : Torus 1 → ℝ, Continuous Wc ∧ Wc =ᵐ[haar 1] ρ.sqrt ∧
      (∀ x, 0 < Wc x) ∧ (∀ x, |Wc x - 1| ≤ Bf_ex011 h) ∧
      (∀ t, HasDerivAt (fun s => Wc (pt s)) (Ac (pt t)) t) ∧
      (∀ t, HasDerivAt (fun s => Ac (pt s)) (Real.pi ^ 2 * (Wc (pt t) *
         (h ^ 2 * Real.sin (2 * Real.pi * t) ^ 2 - ex010_ground h ρ -
           2 * Real.log (Wc (pt t) ^ 2)))) t) ∧
      (∀ x, |Ac x| ≤ Cf_ex011 h) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => Wc (pt s)) := by
  obtain ⟨Wc, hc, hae, δ, hδB, hδ0, hδ⟩ := package_ex011 hh0 hh1 hρ
  obtain ⟨Ac, hAc, hWd, hAd, hAb⟩ := regular_single_ex011 hh0 hρ hc hae hδ0 hδ
  have hδp : 0 ≤ δ := (abs_nonneg _).trans (hδ 0)
  have hW0 : ∀ x, 0 < Wc x := bs_Wc_pos hδ0 hδ
  refine ⟨Wc, Ac, hc, hae, hW0, fun x => (hδ x).trans hδB, hWd, hAd, fun x => ?_,
    smooth_W_ex011 (fun t => hW0 _) hWd hAd⟩
  refine (hAb x).trans ?_
  unfold Cf_ex011
  have := Bf_nonneg_ex011 hh0
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)

/-! ### Mean shift -/

theorem phNorm_const_ex011 (α c : ℝ) : phNorm α 2 (fun _ => c) = |c| := by
  have h0 : deriv (fun _ : ℝ => c) = (0 : ℝ → ℝ) := by funext x; simp
  show supNorm (fun _ : ℝ => c) + phNorm α 1 (deriv fun _ : ℝ => c) = |c|
  rw [h0, phNorm_zero]
  unfold supNorm
  simp

theorem profile_shift_ex011 {α : ℝ} {f : ℝ → ℝ} (hf : IsPH α 2 f) (m : ℝ) :
    IsPH α 2 (fun s => f s - m) ∧ phNorm α 2 (fun s => f s - m) ≤ phNorm α 2 f + |m| := by
  have e : (fun s => f s - m) = f + (fun _ => -m) := by
    funext s; simp [sub_eq_add_neg]
  rw [e]
  refine ⟨hf.add (isPH_const 2 _), ?_⟩
  have := phNorm_add_le hf (isPH_const 2 (-m))
  rwa [phNorm_const_ex011, abs_neg] at this

theorem abs_mean_log_ex011 {Wc : Torus 1 → ℝ} {δ : ℝ} (hδ0 : δ ≤ 1 / 2)
    (hδ : ∀ x, |Wc x - 1| ≤ δ) : |∫ x, Real.log (Wc x ^ 2) ∂haar 1| ≤ 4 * δ := by
  have := norm_integral_le_of_norm_le_const (μ := haar 1) (f := fun x => Real.log (Wc x ^ 2))
    (C := 4 * δ) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      have := abs_log_sq_le ((hδ x).trans hδ0)
      linarith [hδ x])
  simpa using this


/-! ### The uniform argument -/

/-- The data delivered by `instance_ex011`, packaged as a predicate. -/
def Inst_ex011 (h : ℝ) (ρ : AbsoluteDensity 1) (Wc Ac : Torus 1 → ℝ) : Prop :=
  Continuous Wc ∧ Wc =ᵐ[haar 1] ρ.sqrt ∧
      (∀ x, 0 < Wc x) ∧ (∀ x, |Wc x - 1| ≤ Bf_ex011 h) ∧
      (∀ t, HasDerivAt (fun s => Wc (pt s)) (Ac (pt t)) t) ∧
      (∀ t, HasDerivAt (fun s => Ac (pt s)) (Real.pi ^ 2 * (Wc (pt t) *
         (h ^ 2 * Real.sin (2 * Real.pi * t) ^ 2 - ex010_ground h ρ -
           2 * Real.log (Wc (pt t) ^ 2)))) t) ∧
      (∀ x, |Ac x| ≤ Cf_ex011 h) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => Wc (pt s))

theorem exists_inst_ex011 {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 1000) {ρ : AbsoluteDensity 1}
    (hρ : IsGroundMin_ex011 h ρ) : ∃ Wc Ac : Torus 1 → ℝ, Inst_ex011 h ρ Wc Ac :=
  instance_ex011 hh0 hh1 hρ

theorem uniform_ex011 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ h1 : ℝ, 0 < h1 ∧ h1 ≤ 1 / 1000 ∧ ∀ (h : ℝ) (ρ : AbsoluteDensity 1), 0 < h → h < h1 →
      IsGroundMin_ex011 h ρ → ∀ Wc Ac : Torus 1 → ℝ, Inst_ex011 h ρ Wc Ac →
        IsPH α 2 (fun s => Real.log (Wc (pt s) ^ 2) - ∫ x, Real.log (Wc x ^ 2) ∂haar 1) ∧
        phNorm α 2 (fun s => Real.log (Wc (pt s) ^ 2) - ∫ x, Real.log (Wc x ^ 2) ∂haar 1) ≤ ε := by
  by_contra H
  have H' : ∀ n : ℕ, ∃ (h : ℝ) (ρ : AbsoluteDensity 1), 0 < h ∧ h < min (1 / 1000) (1 / ((n : ℝ) + 1)) ∧
      IsGroundMin_ex011 h ρ ∧ ∃ Wc Ac : Torus 1 → ℝ, Inst_ex011 h ρ Wc Ac ∧
        ¬ (IsPH α 2 (fun s => Real.log (Wc (pt s) ^ 2) - ∫ x, Real.log (Wc x ^ 2) ∂haar 1) ∧
        phNorm α 2 (fun s => Real.log (Wc (pt s) ^ 2) - ∫ x, Real.log (Wc x ^ 2) ∂haar 1) ≤ ε) :=
    fun n => by
      by_contra hc
      refine H ⟨min (1 / 1000) (1 / ((n : ℝ) + 1)), lt_min (by norm_num) (by positivity),
        min_le_left _ _, fun h ρ h0 h1 hρ Wc Ac hI => ?_⟩
      by_contra hn
      exact hc ⟨h, ρ, h0, h1, hρ, Wc, Ac, hI, hn⟩
  choose h ρ hh0 hh1 hmin Wc Ac hI hnot using H'
  have hhlim : Tendsto h atTop (𝓝 0) := by
    refine squeeze_zero (fun n => (hh0 n).le) (fun n => ((hh1 n).trans_le (min_le_right _ _)).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hq := fun n => quantitative_ex011 (hh0 n).le (hmin n)
  have hBt : Tendsto (fun n => Bf_ex011 (h n)) atTop (𝓝 0) := by
    have := (continuous_Bf_ex011.tendsto 0).comp hhlim
    rwa [Bf_zero_ex011] at this
  have hCt : Tendsto (fun n => Cf_ex011 (h n)) atTop (𝓝 0) := by
    have := (continuous_Cf_ex011.tendsto 0).comp hhlim
    rwa [Cf_zero_ex011] at this
  have hW1 : USmall (fun n t => Wc n (pt t) - 1) :=
    USmall.of_abs_le hBt fun n t => (hI n).2.2.2.1 _
  have hA0 : USmall (fun n t => Ac n (pt t)) :=
    USmall.of_abs_le hCt fun n t => (hI n).2.2.2.2.2.2.1 _
  have hper : ∀ n, Function.Periodic (fun s => Wc n (pt s)) 1 := fun n s => by
    show Wc n (pt (s + 1)) = Wc n (pt s)
    show Wc n (torusLift fun _ => s + 1) = _
    rw [torusLift_one_add]
  have hode := ode_small_ex011 (α := α) hα0 hα1 (h := h) (E := fun n => ex010_ground (h n) (ρ n))
    (A := fun n t => Ac n (pt t)) (W := fun n s => Wc n (pt s)) hhlim
    (fun n => (hq n).2.1) (fun n => (hq n).1) hper
    (fun n => (hI n).2.2.2.2.1) (fun n => (hI n).2.2.2.2.2.1) hW1 hA0 (ε / 2) (by positivity)
  have hev2 : ∀ᶠ n in atTop, 4 * Bf_ex011 (h n) ≤ ε / 2 ∧ Bf_ex011 (h n) ≤ 1 / 2 := by
    have h1 := (tendsto_order.1 ((tendsto_const_nhds (x := (4:ℝ))).mul hBt)).2 (ε / 2) (by
      simpa using (by positivity : 0 < ε / 2))
    have h2 := (tendsto_order.1 hBt).2 (1 / 2) (by norm_num)
    filter_upwards [h1, h2] with n a b
    exact ⟨a.le, b.le⟩
  obtain ⟨n, hn1, hn2⟩ := (hode.and hev2).exists
  obtain ⟨-, hph, hnorm⟩ := hn1
  obtain ⟨hb4, hb2⟩ := hn2
  obtain ⟨hs1, hs2⟩ := profile_shift_ex011 hph (∫ x, Real.log (Wc n x ^ 2) ∂haar 1)
  have hm := abs_mean_log_ex011 (Wc := Wc n) hb2 (fun x => (hI n).2.2.2.1 x)
  exact hnot n ⟨hs1, le_trans hs2 (by linarith)⟩

end DGPS.Circle.VonMisesCaptureEX011

namespace DGPS.Examples

open MeasureTheory DGPS.Circle.VonMisesSmallField DGPS.Circle.VonMisesCaptureEX011
open DGPS.Analysis.PeriodicHolder

/-- EX011: uniform Haar capture of the ground minimizers of the one-site von Mises functional
`ex010_ground h` on the absolute square-root Haar Sobolev domain, in the Haar-mean-zero
log-density `C^{2,α}` norm, with the quantitative entropy and Fisher bounds. -/
theorem uniform_haar_capture_of_ground_minimizers :
    ∃ h0 : ℝ, 0 < h0 ∧
      (∀ h : ℝ, 0 < h → h < h0 → ∀ ρ : AbsoluteDensity 1,
        (∀ ρ' : AbsoluteDensity 1, ex010_ground h ρ ≤ ex010_ground h ρ') →
          DGPS.Analysis.circleEntropy ρ ≤ Real.sqrt 3 * h ∧
          ex010_haarFisher ρ ≤ h ^ 2 / 2 + 2 * Real.sqrt 3 * h ∧
          ∃ r : Torus 1 → ℝ, (∀ x, 0 < r x) ∧ IsSmoothPeriodic r ∧ ρ.density =ᵐ[haar 1] r) ∧
      (∀ α : ℝ, 0 < α → α < 1 → ∀ ε : ℝ, 0 < ε → ∃ h1 : ℝ, 0 < h1 ∧ h1 ≤ h0 ∧
        ∀ h : ℝ, 0 < h → h < h1 → ∀ ρ : AbsoluteDensity 1,
          (∀ ρ' : AbsoluteDensity 1, ex010_ground h ρ ≤ ex010_ground h ρ') →
          ∃ r : Torus 1 → ℝ, (∀ x, 0 < r x) ∧ IsSmoothPeriodic r ∧ ρ.density =ᵐ[haar 1] r ∧
            IsPH α 2 (fun s => Real.log (r (torusLift fun _ => s)) - ∫ x, Real.log (r x) ∂haar 1) ∧
            phNorm α 2 (fun s => Real.log (r (torusLift fun _ => s)) - ∫ x, Real.log (r x) ∂haar 1) ≤ ε) := by
  have key : ∀ (h : ℝ), 0 < h → h < 1 / 1000 → ∀ ρ : AbsoluteDensity 1,
      (∀ ρ' : AbsoluteDensity 1, ex010_ground h ρ ≤ ex010_ground h ρ') →
      ∃ Wc Ac : Torus 1 → ℝ, Inst_ex011 h ρ Wc Ac := fun h h0 h1 ρ hρ =>
    exists_inst_ex011 h0.le h1.le hρ
  have rep : ∀ {h : ℝ} {ρ : AbsoluteDensity 1} {Wc Ac : Torus 1 → ℝ}, Inst_ex011 h ρ Wc Ac →
      (∀ x, 0 < Wc x ^ 2) ∧ IsSmoothPeriodic (fun x => Wc x ^ 2) ∧
        ρ.density =ᵐ[haar 1] (fun x => Wc x ^ 2) := by
    intro h ρ Wc Ac hI
    obtain ⟨-, hae, hpos, -, -, -, -, hsm⟩ := hI
    refine ⟨fun x => pow_pos (hpos x) 2, isSmooth_sq_ex011 hsm, ?_⟩
    filter_upwards [hae] with x hx
    show ρ.sqrt x ^ 2 = Wc x ^ 2
    rw [hx]
  refine ⟨1 / 1000, by norm_num, ?_, ?_⟩
  · intro h hh0 hh1 ρ hρ
    obtain ⟨Wc, Ac, hI⟩ := key h hh0 hh1 ρ hρ
    obtain ⟨hp, hs, ha⟩ := rep hI
    have hq := quantitative_ex011 hh0.le hρ
    exact ⟨hq.2.2.1, hq.2.2.2, _, hp, hs, ha⟩
  · intro α hα0 hα1 ε hε
    obtain ⟨h1, hh1, hh1', hu⟩ := uniform_ex011 hα0 hα1 hε
    refine ⟨h1, hh1, hh1', fun h hh0 hh ρ hρ => ?_⟩
    obtain ⟨Wc, Ac, hI⟩ := key h hh0 (hh.trans_le hh1') ρ hρ
    obtain ⟨hp, hs, ha⟩ := rep hI
    exact ⟨_, hp, hs, ha, hu h ρ hh0 hh hρ Wc Ac hI⟩

end DGPS.Examples
