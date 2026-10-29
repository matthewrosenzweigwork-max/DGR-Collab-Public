import DGPS.FiniteN.ScalarFoldFIN060H
import DGPS.FiniteN.Tools.EntropyDefects
import DGPS.Particle.RateEquivalences

/-!
# FIN060 (part I): rate-level assembly

* `lsi_of_poincare_defect_FIN060`: an inverse Poincare constant `P` together with an entropy defect
  `Ent(f^2) <= a E(f) + b ||f||^2` gives the unrestricted LSI rate `>= 2 / (a + (b + 2) P)`
  (Rothaus centering, FIN005).
* `all_N_FIN060`: a lower power bound for `N` large upgrades to all `N >= 1` with a smaller constant,
  once every `N` has some positive rate.
* `poincare_inverse_FIN060`: for the scalar fold model, `Var <= P0 N^(1/3) E` for `N` large.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ContDiff ENNReal

namespace DGPS.FiniteN.ScalarFoldFIN060

open DGPS DGPS.Models DGPS.Particle DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.AuxiliaryTransfer
  DGPS.FiniteN.Tools.GaussianCoupling

theorem cosData_eq_FIN060 (h κ : ℝ) :
    DGPS.FiniteN.EntropyDefects.cosData h κ = scalarCosine κ h := rfl

theorem entropy_defect_FIN060 (h : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (N : ℕ+)
    (f : ParticleH1 (scalarCosine κ h) N) :
    homogeneousEntropy (particleLaw (scalarCosine κ h) N) (fun y => f.1 y ^ 2) ≤
      ENNReal.ofReal (2 / (4 * Real.pi ^ 2) * particleEnergy (scalarCosine κ h) N f +
        (|h| + κ) * (N : ℝ) * ∫ y, f.1 y ^ 2 ∂particleLaw (scalarCosine κ h) N) :=
  DGPS.FiniteN.explicit_particle_entropy_defects.1 h κ hκ N f

theorem lsi_of_poincare_defect_FIN060 {d : ℕ} (A : InteractionData d) (N : ℕ+) {P a b : ℝ}
    (hP : 0 < P) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpoin : ∀ f : ParticleH1 A N, variance f.1 (particleLaw A N) ≤ P * particleEnergy A N f)
    (hdef : ∀ f : ParticleH1 A N, homogeneousEntropy (particleLaw A N) (fun y => f.1 y ^ 2) ≤
      ENNReal.ofReal (a * particleEnergy A N f + b * ∫ y, f.1 y ^ 2 ∂particleLaw A N)) :
    ENNReal.ofReal (2 / (a + (b + 2) * P)) ≤ particleRateAll A N := by
  have hM : 0 < a + (b + 2) * P := by positivity
  rw [← particleRate_iff_lsi A N (by positivity)]
  intro f
  have hmem : MemLp f.1 2 (particleLaw A N) :=
    (isParticleWeakGradient_particleWeakGradient f).memLp
  have hprob := particleLaw_isProbabilityMeasure' A N
  set c : ℝ := ∫ y, f.1 y ∂particleLaw A N with hc
  let g : ParticleH1 A N := ⟨fun x => 1 * f.1 x + (-c), f.2.affine 1 (-c)⟩
  have hg : g.1 = fun x => f.1 x - c := by
    funext x; simp only [g]; ring
  have hEg : particleEnergy A N g = particleEnergy A N f := by
    rw [particleEnergy_affine f g 1 (-c) rfl]; simp
  have hrot := DGPS.FiniteN.Tools.Rothaus.rothaus_centering_variance hmem
  have hint : ∫ y, g.1 y ^ 2 ∂particleLaw A N = variance f.1 (particleLaw A N) := by
    rw [hg, variance_eq_integral hmem.aemeasurable]
  have hd := hdef g
  rw [hint, hEg] at hd
  have hgent : homogeneousEntropy (particleLaw A N) (fun x => (f.1 x - c) ^ 2) ≤
      ENNReal.ofReal (a * particleEnergy A N f + b * variance f.1 (particleLaw A N)) := by
    have : (fun x => (f.1 x - c) ^ 2) = fun y => g.1 y ^ 2 := by rw [hg]
    rw [this]; exact hd
  have hV := variance_nonneg f.1 (particleLaw A N)
  have hE := particleEnergy_nonneg f
  have hP' := hpoin f
  unfold particleEntropy
  refine hrot.trans ((add_le_add hgent le_rfl).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : 2 * particleEnergy A N f / (2 / (a + (b + 2) * P)) =
      (a + (b + 2) * P) * particleEnergy A N f := by field_simp
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left hP' (show 0 ≤ b + 2 by linarith)]

theorem exists_pos_lower_FIN060 {ι : Type*} (S : Finset ι) (g : ι → ℝ) (hg : ∀ i, 0 < g i) :
    ∃ m : ℝ, 0 < m ∧ ∀ i ∈ S, m ≤ g i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨m, hm, h⟩ := ih
    refine ⟨min m (g a), lt_min hm (hg a), ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h i hi)

theorem finite_lt_FIN060 (N₀ : ℝ) : {N : ℕ+ | (N : ℝ) < N₀}.Finite := by
  refine (Set.finite_Iic (⟨⌈N₀⌉₊ + 1, Nat.succ_pos _⟩ : ℕ+)).subset fun N hN => ?_
  have h1 : ((N : ℕ) : ℝ) < N₀ := hN
  have h2 : (N : ℕ) < ⌈N₀⌉₊ := by
    have := Nat.le_ceil N₀
    exact_mod_cast h1.trans_le this
  exact (PNat.coe_le_coe N _).1 (h2.le.trans (Nat.le_succ _))

theorem all_N_FIN060 {p : ℝ} (hp : 0 ≤ p) (R : ℕ+ → ℝ≥0∞)
    (hR : ∀ N, ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ R N) {c N₀ : ℝ} (hc : 0 < c)
    (h : ∀ N : ℕ+, N₀ ≤ (N : ℝ) → ENNReal.ofReal (c * (N : ℝ) ^ (-p)) ≤ R N) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ N : ℕ+, ENNReal.ofReal (c' * (N : ℝ) ^ (-p)) ≤ R N := by
  choose g hg hgR using hR
  have hfin := finite_lt_FIN060 N₀
  obtain ⟨m, hm, hmg⟩ := exists_pos_lower_FIN060 hfin.toFinset g hg
  refine ⟨min c m, lt_min hc hm, fun N => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hpow : 0 < (N : ℝ) ^ (-p) := Real.rpow_pos_of_pos (by linarith) _
  have hpow1 : (N : ℝ) ^ (-p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  by_cases hN : N₀ ≤ (N : ℝ)
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (h N hN)
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) hpow.le
  · have hmem : N ∈ hfin.toFinset := by simpa using not_le.1 hN
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hgR N)
    calc min c m * (N : ℝ) ^ (-p) ≤ m * 1 :=
          mul_le_mul (min_le_right _ _) hpow1 hpow.le hm.le
      _ ≤ g N := by rw [mul_one]; exact hmg N hmem

theorem phiS_bound_FIN060 (x : Torus 1) : √(∑ j, phiSFIN060 x j ^ 2) ≤ 1 := by
  rw [Fin.sum_univ_one]
  simp only [phiSFIN060]
  rw [Real.sqrt_sq_eq_abs]
  exact scalarCos_bound x

/-- The inverse Poincare constant of the scalar fold particle law is `O(N^(1/3))`. -/
theorem poincare_inverse_FIN060 {κ : ℝ} (hκ : 2 < κ) :
    ∃ P0 : ℝ, 0 < P0 ∧ ∃ N₀ : ℝ, ∀ N : ℕ+, N₀ ≤ (N : ℝ) →
      ∀ f : ParticleH1 (scalarCosine κ (scalarFoldField κ)) N,
        variance f.1 (particleLaw (scalarCosine κ (scalarFoldField κ)) N) ≤
          P0 * (N : ℝ) ^ (1 / 3 : ℝ) *
            particleEnergy (scalarCosine κ (scalarFoldField κ)) N f := by
  obtain ⟨c, hc, N₀, haux⟩ := haux_FIN060 hκ
  have hκ0 : 0 < κ := by linarith
  set K0 : ℝ := 2 * Real.exp (2 * (|scalarFoldField κ| + |κ|) + 2 * κ) * (4 * Real.pi ^ 2)⁻¹
    with hK0def
  have hK0 : 0 ≤ K0 := by positivity
  refine ⟨K0 * (1 + 1 / c) + 1, by positivity, N₀, fun N hN f => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hNpos : (0 : ℝ) < N := by linarith
  have hlam : 0 < c * (N : ℝ) ^ (2 / 3 : ℝ) := mul_pos hc (Real.rpow_pos_of_pos hNpos _)
  have hmain := particle_poincare_torus_FIN060 (A := scalarCosine κ (scalarFoldField κ))
    (N := N) (D := dSFIN060 κ) (h := hSFIN060 (scalarFoldField κ)) (U := uSFIN060)
    (φ := phiSFIN060) (dSFIN060_posDef hκ0) hubbardHyp_FIN060
    (particleWeight_FIN060 κ (scalarFoldField κ) N) hlam (haux N hN)
    (C := fun w => Real.exp (2 * |w 0|) * (4 * Real.pi ^ 2)⁻¹) (by fun_prop)
    (hcond_FIN060 N) hK0
    (fun x => hK_FIN060 hκ0 (scalarFoldField κ) N x) (L := 1) (fun x => phiS_bound_FIN060 x) f
  have hE := particleEnergy_nonneg f
  refine hmain.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ hE
  have h13 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hp : (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) = N := by
    rw [← Real.rpow_add hNpos]; norm_num
  have hq : (N : ℝ) / (c * (N : ℝ) ^ (2 / 3 : ℝ)) = (N : ℝ) ^ (1 / 3 : ℝ) / c := by
    have h23 : 0 < (N : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hNpos _
    rw [div_eq_div_iff (by positivity) hc.ne']
    linear_combination (-c) * hp
  rw [one_pow, mul_one, hq]
  have : 1 + (N : ℝ) ^ (1 / 3 : ℝ) / c ≤ (1 + 1 / c) * (N : ℝ) ^ (1 / 3 : ℝ) := by
    have : 1 / c ≤ (1 / c) * (N : ℝ) ^ (1 / 3 : ℝ) :=
      le_mul_of_one_le_right (by positivity) h13
    have e : (N : ℝ) ^ (1 / 3 : ℝ) / c = 1 / c * (N : ℝ) ^ (1 / 3 : ℝ) := by ring
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left this hK0
  nlinarith

end DGPS.FiniteN.ScalarFoldFIN060
