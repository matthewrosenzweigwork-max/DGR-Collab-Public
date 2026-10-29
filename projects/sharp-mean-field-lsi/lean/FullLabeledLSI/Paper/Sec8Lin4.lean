import FullLabeledLSI.Paper.Sec8Lin3
import SharpSymmetricLSI.Paper.Prop21Assembly1

/-!
# Section 8.3 (linearization), part 4: the entropy of `ρ_a` relative to `ρ̄` along the perturbation

`∑_a θ_a H(ρ_a|ρ̄)/t² → (1/2) ∑_a θ_a ∫ (h_a - h̄)² dμ`, through the pointwise estimate
`|(1 + t b) klFun((1 + t a)/(1 + t b)) - t²(a - b)²/2| ≤ 200 B³ |t|³`.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ}

theorem eventually_small' {B : ℝ} : ∀ᶠ t in 𝓝 (0 : ℝ), |t| * B ≤ 1 / 8 := by
  have : Tendsto (fun t : ℝ => |t| * B) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => |t| * B := continuous_abs.mul continuous_const
    convert hc.tendsto 0 using 2
    simp
  exact this.eventually (ge_mem_nhds (by norm_num))

theorem klpert_bound {a b t B : ℝ} (hB0 : 0 ≤ B) (ha : |a| ≤ B) (hb : |b| ≤ B)
    (ht : |t| * B ≤ 1 / 8) :
    |(1 + t * b) * klFun ((1 + t * a) / (1 + t * b)) - t ^ 2 * (a - b) ^ 2 / 2| ≤
      200 * B ^ 3 * |t| ^ 3 := by
  set s := |t| with hs
  have hs0 : 0 ≤ s := abs_nonneg t
  have hta : |t * a| ≤ 1 / 8 := by
    rw [abs_mul]; exact (mul_le_mul_of_nonneg_left ha hs0).trans ht
  have htb : |t * b| ≤ 1 / 8 := by
    rw [abs_mul]; exact (mul_le_mul_of_nonneg_left hb hs0).trans ht
  set Bt := 1 + t * b with hBt
  have hBt1 : 7 / 8 ≤ Bt := by linarith [(abs_le.mp htb).1]
  have hBt2 : Bt ≤ 9 / 8 := by linarith [(abs_le.mp htb).2]
  have hBt0 : 0 < Bt := by linarith
  set u := (1 + t * a) / Bt - 1 with hu
  have hu_eq : u = t * (a - b) / Bt := by
    rw [hu]; field_simp; ring
  have hab : |a - b| ≤ 2 * B := (abs_sub _ _).trans (by linarith)
  have hu_abs : |u| ≤ 3 * (s * B) := by
    rw [hu_eq, abs_div, abs_of_pos hBt0, div_le_iff₀ hBt0, abs_mul]
    have : s * |a - b| ≤ s * (2 * B) := mul_le_mul_of_nonneg_left hab hs0
    nlinarith [mul_nonneg hs0 hB0]
  have hsB0 : 0 ≤ s * B := mul_nonneg hs0 hB0
  have hu_half : |u| ≤ 1 / 2 := by linarith
  have hR := abs_klFun_one_add_sub_le hu_half
  have e1 : (1 + t * a) / Bt = 1 + u := by rw [hu]; ring
  rw [e1]
  set R := klFun (1 + u) - u ^ 2 / 2 with hRdef
  have hkl : Bt * klFun (1 + u) - t ^ 2 * (a - b) ^ 2 / 2 =
      Bt * R + t ^ 2 * (a - b) ^ 2 / 2 * (-(t * b) / Bt) := by
    have : Bt * (u ^ 2 / 2) = t ^ 2 * (a - b) ^ 2 / 2 * (1 / Bt) := by
      rw [hu_eq]; field_simp
    have h2 : t ^ 2 * (a - b) ^ 2 / 2 * (-(t * b) / Bt) = t ^ 2 * (a - b) ^ 2 / 2 * (1 / Bt) -
        t ^ 2 * (a - b) ^ 2 / 2 := by
      field_simp; rw [hBt]; ring
    rw [h2, hRdef]
    linarith
  rw [hkl]
  have hu3 : |u| ^ 3 ≤ 27 * (s * B) ^ 3 := by
    calc |u| ^ 3 ≤ (3 * (s * B)) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hu_abs 3
      _ = 27 * (s * B) ^ 3 := by ring
  have t1 : |Bt * R| ≤ 122 * (s * B) ^ 3 := by
    rw [abs_mul, abs_of_pos hBt0]
    calc Bt * |R| ≤ (9 / 8) * (4 * |u| ^ 3) := mul_le_mul hBt2 hR (abs_nonneg _) (by norm_num)
      _ ≤ (9 / 8) * (4 * (27 * (s * B) ^ 3)) := by gcongr
      _ ≤ 122 * (s * B) ^ 3 := by nlinarith [pow_nonneg hsB0 3]
  have t2 : |t ^ 2 * (a - b) ^ 2 / 2 * (-(t * b) / Bt)| ≤ 4 * (s * B) ^ 3 := by
    have hX0 : 0 ≤ t ^ 2 * (a - b) ^ 2 / 2 := by positivity
    have h1 : t ^ 2 = s ^ 2 := by rw [hs, sq_abs]
    have h2 : (a - b) ^ 2 ≤ 4 * B ^ 2 := by
      calc (a - b) ^ 2 = |a - b| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * B) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hab 2
        _ = 4 * B ^ 2 := by ring
    have hX : t ^ 2 * (a - b) ^ 2 / 2 ≤ 2 * (s * B) ^ 2 := by
      rw [h1]
      have := mul_le_mul_of_nonneg_left h2 (sq_nonneg s)
      nlinarith
    have h3 : |t * b| ≤ s * B := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hb hs0
    have hY : |-(t * b) / Bt| ≤ 2 * (s * B) := by
      rw [abs_div, abs_neg, abs_of_pos hBt0, div_le_iff₀ hBt0]
      nlinarith
    calc |t ^ 2 * (a - b) ^ 2 / 2 * (-(t * b) / Bt)| = t ^ 2 * (a - b) ^ 2 / 2 * |-(t * b) / Bt| := by
          rw [abs_mul, abs_of_nonneg hX0]
      _ ≤ 2 * (s * B) ^ 2 * (2 * (s * B)) := mul_le_mul hX hY (abs_nonneg _) (by positivity)
      _ = 4 * (s * B) ^ 3 := by ring
  calc _ ≤ |Bt * R| + |t ^ 2 * (a - b) ^ 2 / 2 * (-(t * b) / Bt)| := abs_add_le _ _
    _ ≤ 122 * (s * B) ^ 3 + 4 * (s * B) ^ 3 := add_le_add t1 t2
    _ ≤ 200 * B ^ 3 * s ^ 3 := by
        have : (s * B) ^ 3 = B ^ 3 * s ^ 3 := by ring
        rw [this]; nlinarith [mul_nonneg (pow_nonneg hB0 3) (pow_nonneg hs0 3)]


/-- `Φ(t) = ∫ p (1 + t b) klFun((1 + t a)/(1 + t b))`, the relative entropy along the perturbation. -/
noncomputable def klPhi (p ha hb : Torus d → ℝ) (t : ℝ) : ℝ :=
  ∫ x, p x * ((1 + t * hb x) * klFun ((1 + t * ha x) / (1 + t * hb x))) ∂haar d

theorem klKt_props {p ha hb : Torus d → ℝ} (hp0 : ∀ x, 0 < p x) (hca : Continuous ha)
    (hcb : Continuous hb) {B t : ℝ} (hB0 : 0 ≤ B) (hBa : ∀ x, |ha x| ≤ B) (hBb : ∀ x, |hb x| ≤ B)
    (ht : |t| * B ≤ 1 / 8) :
    Continuous (fun x => (1 + t * hb x) * klFun ((1 + t * ha x) / (1 + t * hb x))) ∧
      ∀ x, 0 ≤ (1 + t * hb x) * klFun ((1 + t * ha x) / (1 + t * hb x)) := by
  have hb' : ∀ x, 7 / 8 ≤ 1 + t * hb x := fun x => by
    have : |t * hb x| ≤ 1 / 8 := by
      rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hBb x) (abs_nonneg t)).trans ht
    linarith [(abs_le.mp this).1]
  have ha' : ∀ x, 7 / 8 ≤ 1 + t * ha x := fun x => by
    have : |t * ha x| ≤ 1 / 8 := by
      rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hBa x) (abs_nonneg t)).trans ht
    linarith [(abs_le.mp this).1]
  refine ⟨?_, fun x => mul_nonneg (by linarith [hb' x]) (klFun_nonneg (div_nonneg (by linarith [ha' x])
    (by linarith [hb' x])))⟩
  exact (continuous_const.add (continuous_const.mul hcb)).mul (continuous_klFun.comp
    ((continuous_const.add (continuous_const.mul hca)).div
      (continuous_const.add (continuous_const.mul hcb)) fun x => by linarith [hb' x]))

theorem tendsto_klPhi {p ha hb : Torus d → ℝ} (hp0 : ∀ x, 0 < p x) (hpc : Continuous p)
    (hp1 : ∫ x, p x ∂haar d = 1) (hca : Continuous ha) (hcb : Continuous hb) {B : ℝ}
    (hBa : ∀ x, |ha x| ≤ B) (hBb : ∀ x, |hb x| ≤ B) :
    Tendsto (fun t : ℝ => klPhi p ha hb t / t ^ 2) (𝓝[≠] 0)
      (𝓝 (∫ x, p x * ((ha x - hb x) ^ 2 / 2) ∂haar d)) := by
  have hpi : Integrable p (haar d) := integrable_of_integral_eq_one' hp1
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hBa 0)
  set L := ∫ x, p x * ((ha x - hb x) ^ 2 / 2) ∂haar d with hL
  have hI2 : Integrable (fun x => p x * ((ha x - hb x) ^ 2 / 2)) (haar d) := by
    refine Integrable.mono' (hpi.const_mul (2 * B ^ 2))
      (hpc.mul (((hca.sub hcb).pow 2).div_const 2)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hp0 x), abs_of_nonneg (by positivity)]
    have h2 : (ha x - hb x) ^ 2 ≤ 4 * B ^ 2 := by
      calc (ha x - hb x) ^ 2 = |ha x - hb x| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * B) ^ 2 := pow_le_pow_left₀ (abs_nonneg _)
            ((abs_sub _ _).trans (by linarith [hBa x, hBb x])) 2
        _ = 4 * B ^ 2 := by ring
    nlinarith [hp0 x]
  have hbd : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |klPhi p ha hb t / t ^ 2 - L| ≤ 200 * B ^ 3 * |t| := by
    filter_upwards [nhdsWithin_le_nhds (eventually_small' (B := B)), self_mem_nhdsWithin]
      with t ht ht0
    obtain ⟨hKc, hK0⟩ := klKt_props hp0 hca hcb hB0 hBa hBb ht
    set Kt : Torus d → ℝ := fun x => (1 + t * hb x) * klFun ((1 + t * ha x) / (1 + t * hb x))
      with hKt
    have hKb : ∀ x, |Kt x - t ^ 2 * ((ha x - hb x) ^ 2 / 2)| ≤ 200 * B ^ 3 * |t| ^ 3 := fun x => by
      have := klpert_bound hB0 (hBa x) (hBb x) ht
      rw [mul_div_assoc] at this
      exact this
    have hI1 : Integrable (fun x => p x * Kt x) (haar d) := by
      refine Integrable.mono' (hpi.const_mul (t ^ 2 * (2 * B ^ 2) + 200 * B ^ 3 * |t| ^ 3))
        (hpc.mul hKc).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hp0 x), abs_of_nonneg (hK0 x)]
      have h2 : (ha x - hb x) ^ 2 ≤ 4 * B ^ 2 := by
        calc (ha x - hb x) ^ 2 = |ha x - hb x| ^ 2 := (sq_abs _).symm
          _ ≤ (2 * B) ^ 2 := pow_le_pow_left₀ (abs_nonneg _)
              ((abs_sub _ _).trans (by linarith [hBa x, hBb x])) 2
          _ = 4 * B ^ 2 := by ring
      have h3 := (abs_le.mp (hKb x)).2
      have h4 : Kt x ≤ t ^ 2 * (2 * B ^ 2) + 200 * B ^ 3 * |t| ^ 3 := by
        nlinarith [sq_nonneg t]
      exact mul_le_mul_of_nonneg_left h4 (hp0 x).le |>.trans (by rw [mul_comm])
    have key : klPhi p ha hb t - t ^ 2 * L =
        ∫ x, p x * (Kt x - t ^ 2 * ((ha x - hb x) ^ 2 / 2)) ∂haar d := by
      unfold klPhi
      rw [hL, ← integral_const_mul, ← integral_sub hI1 (hI2.const_mul _)]
      congr 1; funext x; ring
    have hle : |klPhi p ha hb t - t ^ 2 * L| ≤ 200 * B ^ 3 * |t| ^ 3 := by
      rw [key]
      have hint : Integrable (fun x => p x * (Kt x - t ^ 2 * ((ha x - hb x) ^ 2 / 2))) (haar d) := by
        have := hI1.sub (hI2.const_mul (t ^ 2))
        convert this using 1
        funext x; simp only [Pi.sub_apply]; ring
      calc _ ≤ ∫ x, |p x * (Kt x - t ^ 2 * ((ha x - hb x) ^ 2 / 2))| ∂haar d :=
            abs_integral_le_integral_abs
        _ ≤ ∫ x, p x * (200 * B ^ 3 * |t| ^ 3) ∂haar d :=
            integral_mono hint.abs (hpi.mul_const _) fun x => by
              rw [abs_mul, abs_of_pos (hp0 x)]
              exact mul_le_mul_of_nonneg_left (hKb x) (hp0 x).le
        _ = 200 * B ^ 3 * |t| ^ 3 := by rw [integral_mul_const, hp1, one_mul]
    have ht0' : t ≠ 0 := ht0
    have ht2 : 0 < t ^ 2 := by positivity
    have e : klPhi p ha hb t / t ^ 2 - L = (klPhi p ha hb t - t ^ 2 * L) / t ^ 2 := by
      field_simp
    rw [e, abs_div, abs_of_pos ht2, div_le_iff₀ ht2]
    calc _ ≤ 200 * B ^ 3 * |t| ^ 3 := hle
      _ = 200 * B ^ 3 * |t| * t ^ 2 := by rw [← sq_abs t]; ring
  have h0 : Tendsto (fun t : ℝ => 200 * B ^ 3 * |t|) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => 200 * B ^ 3 * |t|) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun t : ℝ => 200 * B ^ 3 * |t| := continuous_const.mul continuous_abs
      convert hc.tendsto 0 using 2
      simp
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hbd.mono fun t h => by rwa [Real.norm_eq_abs]) h0)

end Sec8
end SharpLSI.FL
