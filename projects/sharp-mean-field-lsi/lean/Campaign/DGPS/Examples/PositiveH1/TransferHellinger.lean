import Mathlib
import DGPS.Examples.PositiveH1.TransferEntropyChange

open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS
open DGPS.Examples.PositiveH1.Particle DGPS.Examples.PositiveH1.Fourier
open DGPS.Examples.PositiveH1.Model

/-!
# H1038: uniform Hellinger transfer bound

With `κ = 1/100`, `t_M = e^{κA/2} κ A_M / 2 → 0` (`A_M = tailA M = Σ_{n>M} a_n`), the tail
potential `T_{N,M}` satisfies `∫ T_{N,M} dP_{N,M} ≤ t_M` and
`‖h_{N,M} - 1‖²_{L²(P_{N,M})} ≤ t_M` for all `N`.  If `∫ f dP_N = 0` and `‖f‖²_{P_N} = 1`, then
`g = f h_{N,M}` has `‖g‖²_{P_{N,M}} = 1` and `Var_{P_{N,M}}(g) ≥ 1 - t_M`.
Main result: `uniform_hellinger_transfer_bound`.
-/

namespace DGPS.Examples.PositiveH1.Transfer

/-- The Hellinger transfer constant `t_M = e^{κA/2} κ A_M / 2` at `κ = 1/100`
(`A_M` is the tail sum `tailA M`). -/
noncomputable def tHell (M : ℕ) : ℝ :=
  Real.exp ((1 / 100) * A / 2) * ((1 / 100) * tailA M / 2)

theorem tailA_nonneg' (M : ℕ) : 0 ≤ tailA M := h1030_tailA_nonneg M

theorem tHell_nonneg (M : ℕ) : 0 ≤ tHell M :=
  mul_nonneg (Real.exp_pos _).le (by have := tailA_nonneg' M; positivity)

theorem tendsto_tHell : Tendsto tHell atTop (𝓝 0) := by
  have h := (tendsto_tailA.const_mul ((1 / 100 : ℝ) / 2)).const_mul
    (Real.exp ((1 / 100) * A / 2))
  simp only [mul_zero] at h
  refine h.congr fun M => ?_
  unfold tHell
  ring

theorem integral_tailT_haar (N : ℕ+) (M : ℕ) :
    ∫ x, tailT (1 / 100) N M x ∂particleHaar 1 N = (1 / 100) * tailA M / 2 := by
  unfold tailT
  rw [integral_const_mul]
  have hterm : ∀ n : ℕ, Integrable (fun x : ParticleSpace 1 N =>
      if M < n then a n * ‖Z N n x‖ ^ 2 else 0) (particleHaar 1 N) := fun n => by
    split_ifs
    · exact integrable_mode_term N n
    · exact integrable_const _
  have hint : ∀ n : ℕ, ∫ x, (if M < n then a n * ‖Z N n x‖ ^ 2 else 0) ∂particleHaar 1 N =
      if M < n then a n else 0 := fun n => by
    split_ifs
    · exact integral_mode_term N n
    · simp
  have hs : Summable fun n : ℕ => ∫ x, ‖if M < n then a n * ‖Z N n x‖ ^ 2 else 0‖
      ∂particleHaar 1 N := by
    have : (fun n : ℕ => ∫ x, ‖if M < n then a n * ‖Z N n x‖ ^ 2 else 0‖ ∂particleHaar 1 N) =
        fun n => if M < n then a n else 0 := by
      funext n
      split_ifs
      · have h : (fun x : ParticleSpace 1 N => ‖a n * ‖Z N n x‖ ^ 2‖)
          = fun x => a n * ‖Z N n x‖ ^ 2 :=
          funext fun x => Real.norm_of_nonneg (mul_nonneg (a_nonneg n) (sq_nonneg _))
        rw [h, integral_mode_term]
      · simp
    rw [this]
    exact a_summable.of_nonneg_of_le (fun n => by split_ifs <;> simp [a_nonneg n])
      (fun n => by split_ifs <;> simp [a_nonneg n])
  rw [← integral_tsum_of_summable_integral_norm hterm hs]
  simp_rw [hint]
  unfold tailA
  ring

theorem UM_nonneg (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) : 0 ≤ UM (1 / 100) N M x := by
  unfold UM
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun n _ => ?_)
  exact mul_nonneg (a_nonneg n) (sq_nonneg _)

theorem density_cutoff_le (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) :
    particleDensity (positiveH1Cutoff M) N x ≤ Real.exp ((1 / 100) * A / 2) := by
  rw [cutoff_density]
  have hK := K_pos (1 / 100 : ℝ) N
  have hKM := KM_pos N M
  have h1 : (KM N M)⁻¹ ≤ Real.exp ((1 / 100) * A / 2) := by
    refine le_trans (inv_anti₀ hK (K_le_KM N M)) ?_
    rw [inv_le_comm₀ hK (Real.exp_pos _), ← Real.exp_neg]
    exact exp_le_K (1 / 100) N
  have h2 : Real.exp (-UM (1 / 100) N M x) ≤ 1 := by simpa using UM_nonneg N M x
  calc (KM N M)⁻¹ * Real.exp (-UM (1 / 100) N M x) ≤ (KM N M)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hKM.le)
    _ ≤ _ := by rw [mul_one]; exact h1

theorem continuous_density (A' : InteractionData 1) (N : ℕ+) :
    Continuous (particleDensity A' N) := by
  unfold particleDensity
  exact continuous_const.mul
    (Real.continuous_exp.comp (DGPS.Particle.particleHamiltonian_continuous A' N).neg)

theorem continuous_hNM (N : ℕ+) (M : ℕ) : Continuous (hNM N M) := by
  unfold hNM
  refine Real.continuous_sqrt.comp ((continuous_density _ N).div (continuous_density _ N) fun x => ?_)
  exact (DGPS.Particle.particleDensity_pos _ N x).ne'

theorem hNM_nonneg (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) : 0 ≤ hNM N M x :=
  Real.sqrt_nonneg _

theorem hNM_sq_exp (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) :
    hNM N M x ^ 2 = KM N M / K (1 / 100) N * Real.exp (-tailT (1 / 100) N M x) := by
  rw [hNM_sq, ratio_eq]

theorem density_mul_hNM_sq (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) :
    particleDensity (positiveH1Cutoff M) N x * hNM N M x ^ 2 =
      particleDensity (kernelData (1 / 100)) N x := by
  have h := DGPS.Particle.particleDensity_pos (positiveH1Cutoff M) N x
  rw [hNM_sq]
  field_simp

theorem integral_hNM_sq (N : ℕ+) (M : ℕ) :
    ∫ x, hNM N M x ^ 2 ∂particleLaw (positiveH1Cutoff M) N = 1 := by
  rw [DGPS.Particle.integral_particleLaw]
  simp_rw [density_mul_hNM_sq]
  have h1 := DGPS.Particle.integral_particleLaw (kernelData (1 / 100)) N (fun _ => (1 : ℝ))
  simpa using h1.symm

theorem memLp_hNM (N : ℕ+) (M : ℕ) :
    MemLp (hNM N M) 2 (particleLaw (positiveH1Cutoff M) N) :=
  (continuous_hNM N M).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem continuous_tailT (N : ℕ+) (M : ℕ) : Continuous (tailT (1 / 100) N M) := by
  have : tailT (1 / 100) N M = fun x => U (1 / 100) N x - UM (1 / 100) N M x := by
    funext x; rw [U_sub_UM]
  rw [this]; exact (continuous_U _ N).sub (continuous_UM N M)

theorem integral_tailT_le (N : ℕ+) (M : ℕ) :
    ∫ x, tailT (1 / 100) N M x ∂particleLaw (positiveH1Cutoff M) N ≤ tHell M := by
  rw [DGPS.Particle.integral_particleLaw]
  have hTi : Integrable (tailT (1 / 100) N M) (particleHaar 1 N) :=
    (continuous_tailT N M).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc ∫ x, particleDensity (positiveH1Cutoff M) N x * tailT (1 / 100) N M x ∂particleHaar 1 N
      ≤ ∫ x, Real.exp ((1 / 100) * A / 2) * tailT (1 / 100) N M x ∂particleHaar 1 N := by
        refine integral_mono ?_ (hTi.const_mul _) fun x => ?_
        · exact ((continuous_density _ N).mul (continuous_tailT N M)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        · exact mul_le_mul_of_nonneg_right (density_cutoff_le N M x)
            (tailT_nonneg (by norm_num) N M x)
    _ = tHell M := by
        rw [integral_const_mul, integral_tailT_haar]; rfl

/-- `‖h_{N,M} - 1‖²_{L²(P_{N,M})} ≤ t_M`. -/
theorem hellinger_distance_bound (N : ℕ+) (M : ℕ) :
    ∫ x, (hNM N M x - 1) ^ 2 ∂particleLaw (positiveH1Cutoff M) N ≤ tHell M := by
  set Q := particleLaw (positiveH1Cutoff M) N with hQ
  set T := tailT (1 / 100) N M with hT
  have hK := K_pos (1 / 100 : ℝ) N
  have hKM := KM_pos N M
  have hTc : Continuous T := continuous_tailT N M
  have hTi : Integrable T Q :=
    hTc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hEi : ∀ c : ℝ, Integrable (fun x => Real.exp (-T x) * c) Q := fun c =>
    ((Real.continuous_exp.comp hTc.neg).mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hE1 : Integrable (fun x => Real.exp (-T x)) Q := by simpa using hEi 1
  set m := ∫ x, T x ∂Q with hm
  have hmt : m ≤ tHell M := integral_tailT_le N M
  -- the mean of e^{-T}
  set z := K (1 / 100) N / KM N M with hz
  have hzpos : 0 < z := div_pos hK hKM
  have hEz : ∫ x, Real.exp (-T x) ∂Q = z := by
    have h1 := integral_hNM_sq N M
    simp_rw [hNM_sq_exp] at h1
    rw [integral_const_mul] at h1
    rw [hz]
    field_simp
    field_simp at h1
    linarith
  -- Jensen via tangent line
  have hJ : Real.exp (-m) ≤ z := by
    have hmono : ∫ x, Real.exp (-m) * (1 + (-T x + m)) ∂Q ≤ ∫ x, Real.exp (-T x) ∂Q := by
      refine integral_mono ?_ hE1 fun x => ?_
      · exact ((integrable_const (1 : ℝ)).add (hTi.neg.add (integrable_const m))).const_mul _
      · have h := Real.add_one_le_exp (-T x + m)
        have : Real.exp (-T x) = Real.exp (-m) * Real.exp (-T x + m) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [this]
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    have h3 : ∫ x, Real.exp (-m) * (1 + (-T x + m)) ∂Q = Real.exp (-m) := by
      have hI1 : Integrable (fun x => -T x + m) Q := hTi.neg.add (integrable_const m)
      have hI2 : Integrable (fun x => -T x) Q := hTi.neg
      rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hI1,
        integral_add hI2 (integrable_const m), integral_neg]
      simp [← hm]
    rw [← hEz]; linarith
  -- lower bound for h
  set s := Real.sqrt (KM N M / K (1 / 100) N) with hs
  have hs2 : s ^ 2 = KM N M / K (1 / 100) N := Real.sq_sqrt (div_pos hKM hK).le
  have hspos : 0 < s := Real.sqrt_pos.2 (div_pos hKM hK)
  have hlow : ∀ x, s * Real.exp (-T x) ≤ hNM N M x := fun x => by
    unfold hNM
    rw [ratio_eq]
    refine Real.le_sqrt_of_sq_le ?_
    have hT0 : 0 ≤ T x := tailT_nonneg (by norm_num) N M x
    have he1 : Real.exp (-T x) ≤ 1 := by simpa using hT0
    have he0 := Real.exp_pos (-T x)
    rw [mul_pow, hs2]
    have : Real.exp (-T x) ^ 2 ≤ Real.exp (-T x) := by nlinarith
    exact mul_le_mul_of_nonneg_left this (div_pos hKM hK).le
  have hhi : Integrable (hNM N M) Q := (memLp_hNM N M).integrable (by norm_num)
  have hmean : s * z ≤ ∫ x, hNM N M x ∂Q := by
    rw [← hEz, ← integral_const_mul]
    exact integral_mono (hE1.const_mul _) hhi hlow
  have hsz : Real.exp (-m / 2) ≤ s * z := by
    have h1 : Real.exp (-m / 2) ^ 2 ≤ (s * z) ^ 2 := by
      rw [← Real.exp_nat_mul]
      have : (s * z) ^ 2 = z := by
        rw [mul_pow, hs2, hz]; field_simp
      rw [this]
      refine le_trans (le_of_eq ?_) hJ
      congr 1; push_cast; ring
    exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (mul_pos hspos hzpos).le
      (by norm_num)).1 h1
  have hexp : 1 - m / 2 ≤ Real.exp (-m / 2) := by
    have := Real.add_one_le_exp (-m / 2); linarith
  -- expand
  have hexpand : ∫ x, (hNM N M x - 1) ^ 2 ∂Q = 2 - 2 * ∫ x, hNM N M x ∂Q := by
    have hsqi : Integrable (fun x => hNM N M x ^ 2) Q := (memLp_hNM N M).integrable_sq
    have : (fun x => (hNM N M x - 1) ^ 2) =
        fun x => (hNM N M x ^ 2 - 2 * hNM N M x) + 1 := by funext x; ring
    have hI1 : Integrable (fun x => hNM N M x ^ 2 - 2 * hNM N M x) Q :=
      hsqi.sub (hhi.const_mul 2)
    rw [this, integral_add hI1 (integrable_const _),
      integral_sub hsqi (hhi.const_mul 2), integral_const_mul, integral_hNM_sq]
    simp
    ring
  rw [hexpand]
  linarith

theorem uniform_hellinger_transfer_bound :
    Tendsto tHell atTop (𝓝 0) ∧ ∀ (N : ℕ+) (M : ℕ),
      ∫ x, tailT (1 / 100) N M x ∂particleLaw (positiveH1Cutoff M) N ≤ tHell M ∧
      ∫ x, (hNM N M x - 1) ^ 2 ∂particleLaw (positiveH1Cutoff M) N ≤ tHell M ∧
      ∀ f : ParticleH1 (kernelData (1 / 100)) N,
        ∫ x, f x ∂particleLaw (kernelData (1 / 100)) N = 0 →
        ∫ x, f x ^ 2 ∂particleLaw (kernelData (1 / 100)) N = 1 →
        MemParticleH1 (positiveH1Cutoff M) N (fun x => f x * hNM N M x) ∧
          ∫ x, (f x * hNM N M x) ^ 2 ∂particleLaw (positiveH1Cutoff M) N = 1 ∧
          (∫ x, f x * hNM N M x ∂particleLaw (positiveH1Cutoff M) N) ^ 2 ≤ tHell M ∧
          1 - tHell M ≤ ProbabilityTheory.variance (fun x => f x * hNM N M x)
            (particleLaw (positiveH1Cutoff M) N) := by
  refine ⟨tendsto_tHell, fun N M => ⟨integral_tailT_le N M, hellinger_distance_bound N M,
    fun f hf0 hf1 => ?_⟩⟩
  obtain ⟨hg, hmass, -⟩ := full_domain_entropy_change_of_density N M f
  refine ⟨hg, hmass.trans hf1, ?_⟩
  set Q := particleLaw (positiveH1Cutoff M) N with hQ
  set h := hNM N M with hh
  have hg2 : MemLp (fun x => f x * h x) 2 Q := by
    obtain ⟨gg, hgg⟩ := hg
    exact hgg.memLp
  have hg1 : Integrable (fun x => f x * h x) Q := hg2.integrable (by norm_num)
  have hh2 : MemLp h 2 Q := memLp_hNM N M
  have hhi : Integrable h Q := hh2.integrable (by norm_num)
  have hgsq : ∫ x, (f x * h x) ^ 2 ∂Q = 1 := hmass.trans hf1
  have hgsqi : Integrable (fun x => (f x * h x) ^ 2) Q := hg2.integrable_sq
  have hhsqi : Integrable (fun x => h x ^ 2) Q := hh2.integrable_sq
  -- orthogonality
  have horth : ∫ x, (f x * h x) * h x ∂Q = 0 := by
    rw [hQ, DGPS.Particle.integral_particleLaw]
    have : ∀ x, particleDensity (positiveH1Cutoff M) N x * ((f x * hNM N M x) * hNM N M x) =
        particleDensity (kernelData (1 / 100)) N x * f x := fun x => by
      have := density_mul_hNM_sq N M x
      calc _ = (particleDensity (positiveH1Cutoff M) N x * hNM N M x ^ 2) * f x := by ring
        _ = _ := by rw [this]
    refine (integral_congr_ae (Filter.Eventually.of_forall this)).trans ?_
    rw [← DGPS.Particle.integral_particleLaw (kernelData (1 / 100)) N f]
    exact hf0
  have hghi : Integrable (fun x => (f x * h x) * h x) Q := hg2.integrable_mul hh2
  set u := ∫ x, f x * h x ∂Q with hu
  have hu' : u = ∫ x, (f x * h x) * (1 - h x) ∂Q := by
    have : (fun x => (f x * h x) * (1 - h x)) = fun x => f x * h x - (f x * h x) * h x := by
      funext x; ring
    rw [this, integral_sub hg1 hghi, horth, hu]; simp
  have hI : ∫ x, (h x - 1) ^ 2 ∂Q ≤ tHell M := hellinger_distance_bound N M
  have hsq : u ^ 2 ≤ ∫ x, (h x - 1) ^ 2 ∂Q := by
    have hnn : 0 ≤ ∫ x, (u * (f x * h x) - (1 - h x)) ^ 2 ∂Q :=
      integral_nonneg fun x => sq_nonneg _
    have hcross : Integrable (fun x => (f x * h x) * (1 - h x)) Q := by
      have : (fun x => (f x * h x) * (1 - h x)) = fun x => f x * h x - (f x * h x) * h x := by
        funext x; ring
      rw [this]; exact hg1.sub hghi
    have hhh : Integrable (fun x => (h x - 1) ^ 2) Q := by
      have : (fun x => (h x - 1) ^ 2) = fun x => h x ^ 2 - 2 * h x + 1 := by funext x; ring
      rw [this]; exact (hhsqi.sub (hhi.const_mul 2)).add (integrable_const _)
    have hex : (fun x => (u * (f x * h x) - (1 - h x)) ^ 2) =
        fun x => u ^ 2 * (f x * h x) ^ 2 - 2 * u * ((f x * h x) * (1 - h x)) +
          (h x - 1) ^ 2 := by funext x; ring
    have hA1 : Integrable (fun x => u ^ 2 * (f x * h x) ^ 2) Q := hgsqi.const_mul _
    have hA2 : Integrable (fun x => 2 * u * ((f x * h x) * (1 - h x))) Q := hcross.const_mul _
    have hA3 : Integrable (fun x => u ^ 2 * (f x * h x) ^ 2 - 2 * u * ((f x * h x) * (1 - h x))) Q :=
      hA1.sub hA2
    rw [hex, integral_add hA3 hhh, integral_sub hA1 hA2, integral_const_mul,
      integral_const_mul, hgsq, ← hu'] at hnn
    nlinarith
  refine ⟨hsq.trans hI, ?_⟩
  rw [ProbabilityTheory.variance_eq_sub hg2]
  show 1 - tHell M ≤ ∫ x, (f x * h x) ^ 2 ∂Q - u ^ 2
  have := hsq.trans hI
  linarith

end DGPS.Examples.PositiveH1.Transfer
