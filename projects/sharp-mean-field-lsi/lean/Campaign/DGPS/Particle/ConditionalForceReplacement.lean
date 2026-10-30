import DGPS.Lipschitz.T01SpectralBridge
import FullLabeledLSI.Paper.Sec5ForceSum

/-!
# Bounded measurable force replacement for the actual centered kernel

The unrestricted subset-averaged replacement theorem needs only bounded measurable force
representatives. Its inherited proof has no semiconvexity, equilibrium, or symmetry premise.
The diagonal representative below is half the gradient of the actual centered diagonal.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace DGPS.Lipschitz

open KernelApproximation

/-- A crude bound handles the finitely small conditioning cutoffs where the triple-label
estimate is unavailable. It is uniform in the particle number and in the comparison law. -/
theorem conditional_force_uniform_bound {d N j : ℕ}
    {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {B : ℝ}
    (hB : SharpLSI.FL.ForceRep bF bΔ B) (hB0 : 0 ≤ B)
    (ν : Measure (SharpLSI.Config N d)) [IsProbabilityMeasure ν] (hj : j < N) :
    SharpLSI.FL.forceDelta bF bΔ ν j ≤ (d : ℝ) * (3 * B) ^ 2 := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  apply (le_abs_self _).trans
  apply SharpLSI.FL.avg1R_abs_le hj
  intro S hS i hi
  have hSc : 1 ≤ Sᶜ.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hpt : ∀ X : SharpLSI.Config N d,
      |∑ k, (SharpLSI.FL.BS bF ν S X (X i) k - SharpLSI.FL.Gpart bF bΔ N X i k) ^ 2| ≤
        (d : ℝ) * (3 * B) ^ 2 := by
    intro X
    apply SharpLSI.FL.abs_sum_sq_le'
    intro k
    have hb := SharpLSI.FL.abs_BS_le hB ν S hSc X (X i) k
    have hg := SharpLSI.FL.abs_Gpart_le hB X i k
    have hg2 : (N : ℝ)⁻¹ * ((N : ℝ) * B + B) ≤ 2 * B := by
      rw [show (N : ℝ)⁻¹ * ((N : ℝ) * B + B) = ((N : ℝ) * B + B) / N by
        rw [div_eq_mul_inv, mul_comm], div_le_iff₀ hN]
      nlinarith
    exact (abs_sub _ _).trans (by linarith)
  have hnorm : ∀ᵐ X ∂ν,
      ‖∑ k, (SharpLSI.FL.BS bF ν S X (X i) k - SharpLSI.FL.Gpart bF bΔ N X i k) ^ 2‖ ≤
        (d : ℝ) * (3 * B) ^ 2 :=
    Eventually.of_forall fun X => by simpa only [Real.norm_eq_abs] using hpt X
  simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const
    (μ := ν) (C := (d : ℝ) * (3 * B) ^ 2) hnorm

/-- The inherited force sum extends to all cutoffs: when `M < 3`, the constraint
`M/N ≥ τ` bounds `N` and a direct bounded-force estimate suffices. -/
theorem abstract_force_sum_all_cutoffs {d : ℕ}
    {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {B : ℝ}
    (hB : SharpLSI.FL.ForceRep bF bΔ B) (hB0 : 0 ≤ B) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, ∀ (N M : ℕ), M ≤ N → τ ≤ (M : ℝ) / N →
      ∀ (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
        (ν : Measure (SharpLSI.Config N d)) [IsProbabilityMeasure ν],
        InformationTheory.klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤ →
        ∑ j ∈ Finset.range (N - M), SharpLSI.FL.forceDelta bF bΔ ν j ≤
          C * (1 + Real.sqrt (InformationTheory.klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal) := by
  obtain ⟨C0, hC0⟩ := SharpLSI.FL.abstract_force_sum hB τ hτ
  let U : ℝ := (d : ℝ) * (3 * B) ^ 2
  have hU : 0 ≤ U := by positivity
  refine ⟨|C0| + 2 / τ * U, fun N M hMN hτM μ _ ν _ hH => ?_⟩
  have hroot : 0 ≤ Real.sqrt (InformationTheory.klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal :=
    Real.sqrt_nonneg _
  by_cases hM : 3 ≤ M
  · have hCc : C0 ≤ |C0| + 2 / τ * U :=
      (le_abs_self C0).trans (le_add_of_nonneg_right (by positivity))
    exact (hC0 N M hM hMN hτM μ ν hH).trans
      (mul_le_mul_of_nonneg_right hCc (by linarith))
  · have hN : 0 < (N : ℝ) := by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp only [Nat.cast_zero, div_zero] at hτM
        linarith
      · exact_mod_cast hN
    have hM2 : (M : ℝ) ≤ 2 := by exact_mod_cast (by omega : M ≤ 2)
    have hNb : (N : ℝ) ≤ 2 / τ := by
      rw [le_div_iff₀ hτ]
      have := (le_div_iff₀ hN).mp hτM
      nlinarith
    have hsum : ∑ j ∈ Finset.range (N - M), SharpLSI.FL.forceDelta bF bΔ ν j ≤
        ((N - M : ℕ) : ℝ) * U := by
      calc _ ≤ ∑ _j ∈ Finset.range (N - M), U :=
          Finset.sum_le_sum fun j hj => conditional_force_uniform_bound hB hB0 ν
            (by have := Finset.mem_range.mp hj; omega)
        _ = _ := by simp [nsmul_eq_mul]
    have hlen : ((N - M : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N M
    have hsmall : ∑ j ∈ Finset.range (N - M), SharpLSI.FL.forceDelta bF bΔ ν j ≤
        2 / τ * U := hsum.trans (mul_le_mul_of_nonneg_right (hlen.trans hNb) hU)
    have hC0pos : 0 ≤ 2 / τ * U := by positivity
    have hmul : 2 / τ * U ≤
        (|C0| + 2 / τ * U) *
          (1 + Real.sqrt (InformationTheory.klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal) := by
      nlinarith [abs_nonneg C0, mul_nonneg (abs_nonneg C0) hroot,
        mul_nonneg hC0pos hroot]
    exact hsmall.trans hmul

/-- Current bounded kernel and diagonal gradients satisfy the inherited force interface. -/
theorem kernel_force_rep {d : ℕ} (D : KData d) {g : Torus d → Tangent d}
    (hgm : Measurable g) {M : ℝ} (hgb : ∀ x, ‖g x‖ ≤ M) :
    SharpLSI.FL.ForceRep (fun x y k => D.G1 x y k) (fun x k => g x k / 2)
      (|D.B| + |M|) := by
  refine ⟨fun k => ?_, fun k => ?_, fun x y k => ?_, fun x k => ?_⟩
  · exact (EuclideanSpace.proj k : Tangent d →L[ℝ] ℝ).continuous.measurable.comp D.G1m
  · exact ((EuclideanSpace.proj k : Tangent d →L[ℝ] ℝ).continuous.measurable.comp hgm).div_const 2
  · have h := (PiLp.norm_apply_le (D.G1 x y) k).trans (D.G1b x y)
    have : |D.G1 x y k| ≤ |D.B| := by simpa [Real.norm_eq_abs] using h.trans (le_abs_self D.B)
    exact this.trans (le_add_of_nonneg_right (abs_nonneg M))
  · have h : |g x k| ≤ |M| := by
      simpa [Real.norm_eq_abs] using
        (PiLp.norm_apply_le (g x) k).trans ((hgb x).trans (le_abs_self M))
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hhalf : |g x k| / 2 ≤ |M| := by linarith [abs_nonneg M]
    exact hhalf.trans (le_add_of_nonneg_left (abs_nonneg D.B))

/-- The inherited force has exactly the current particle scaling, including `1/(2N)`
on the separately differentiated diagonal. -/
theorem kernel_Gpart_eq {d : ℕ} (D : KData d) (g : Torus d → Tangent d)
    (N : ℕ+) (X : ParticleSpace d N) (i : Fin N) (k : Fin d) :
    SharpLSI.FL.Gpart (fun x y k => D.G1 x y k) (fun x k => g x k / 2) N X i k =
      ((N : ℝ)⁻¹ • ∑ l ∈ Finset.univ.erase i, D.G1 (X i) (X l) +
        (2 * (N : ℝ))⁻¹ • g (X i)) k := by
  classical
  have hsum : (∑ l : Fin N, if l ≠ i then D.G1 (X i) (X l) k else 0) =
      ∑ l ∈ Finset.univ.erase i, D.G1 (X i) (X l) k := by
    rw [← Finset.sum_filter]
    congr 1
    ext l
    simp [and_comm]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.pos.ne'
  simp only [SharpLSI.FL.Gpart, hsum, PiLp.add_apply, PiLp.smul_apply,
    WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
  field_simp [hN]
  <;> ring

/-- The inherited force representative is a genuine current weak particle gradient. -/
theorem kernel_Gpart_isParticleHaarWeakGradient {d : ℕ} (D : KData d)
    (hsymm : ∀ x y, D.K x y = D.K y x) {g : Torus d → Tangent d}
    (hg : IsWeakGradient (fun x => D.K x x) g) (N : ℕ+) :
    IsParticleHaarWeakGradient N
      (fun X : ParticleSpace d N => (2 * (N : ℝ))⁻¹ * ∑ i, ∑ l, D.K (X i) (X l))
      (fun X i => WithLp.toLp 2 (fun k => SharpLSI.FL.Gpart
        (fun x y k => D.G1 x y k) (fun x k => g x k / 2) N X i k)) := by
  have hforce : (fun X i => WithLp.toLp 2 (fun k => SharpLSI.FL.Gpart
      (fun x y k => D.G1 x y k) (fun x k => g x k / 2) N X i k)) =
      fun X i => (N : ℝ)⁻¹ • ∑ l ∈ Finset.univ.erase i, D.G1 (X i) (X l) +
        (2 * (N : ℝ))⁻¹ • g (X i) := by
    funext X i
    apply WithLp.ofLp_injective
    funext k
    exact kernel_Gpart_eq D g N X i k
  rw [hforce]
  simpa only [Finset.sum_const_zero, zero_add, one_div] using
    df_core (V := fun _ => (0 : ℝ)) (gV := fun _ => 0)
      hsymm D.Kc D.G1m D.G1b D.g1 isWeakGradient_zero hg N

/-- The actual centered direct-Lipschitz kernel admits the unrestricted averaged
conditional force-replacement bound, including its true diagonal correction. -/
theorem averaged_conditional_force_replacement {d : ℕ} (A : InteractionData d)
    (hA : LipschitzData A) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    ∃ (D : KData d) (g : Torus d → Tangent d), D.K = centeredKernel A μ ∧
      Measurable g ∧ IsWeakGradient (fun x => centeredKernel A μ x x) g ∧
      (∀ N : ℕ+, IsParticleHaarWeakGradient N
        (fun X : ParticleSpace d N => (2 * (N : ℝ))⁻¹ * ∑ i, ∑ l, centeredKernel A μ (X i) (X l))
        (fun X i => WithLp.toLp 2 (fun k => SharpLSI.FL.Gpart
          (fun x y k => D.G1 x y k) (fun x k => g x k / 2) N X i k))) ∧
      ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, ∀ (N M : ℕ), M ≤ N → τ ≤ (M : ℝ) / N →
        ∀ (ν : Measure (SharpLSI.Config N d)) [IsProbabilityMeasure ν],
          InformationTheory.klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤ →
          ∑ j ∈ Finset.range (N - M),
            SharpLSI.FL.forceDelta (fun x y k => D.G1 x y k) (fun x k => g x k / 2) ν j ≤
              C * (1 + Real.sqrt (InformationTheory.klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal) := by
  obtain ⟨D, hD⟩ := exists_centeredKernel_data A hA μ
  obtain ⟨g, hgm, ⟨M, hgb⟩, hgw⟩ := exists_centeredKernel_diagonal_gradient A hA μ
  refine ⟨D, g, hD, hgm, hgw, ?_, fun τ hτ => ?_⟩
  · have hsymm : ∀ x y, D.K x y = D.K y x := by
      rw [hD]
      exact centeredKernel_symm A μ
    have hgwD : IsWeakGradient (fun x => D.K x x) g := by rw [hD]; exact hgw
    intro N
    have hh := kernel_Gpart_isParticleHaarWeakGradient D hsymm hgwD N
    rwa [hD] at hh
  · obtain ⟨C, hC⟩ := abstract_force_sum_all_cutoffs
      (kernel_force_rep D hgm hgb) (by positivity) τ hτ
    exact ⟨C, fun N M hMN hτM ν _ hH => hC N M hMN hτM μ ν hH⟩

end DGPS.Lipschitz
