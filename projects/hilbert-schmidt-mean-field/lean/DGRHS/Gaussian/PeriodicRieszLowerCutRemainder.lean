import DGRHS.Gaussian.PeriodicRieszLowerCutFeature
import DGRHS.Gaussian.PeriodicRieszTruncationRemainder
import DGRHS.Gaussian.PeriodicRieszTimeParticleSplit
import DGRHS.Gaussian.PeriodicPositiveMellinShortL2

/-!
Packet P9f, unit 1 (part 2): the `L²` remainder of the lower-cut family on the torus,
`‖g - g_ε‖²_{L²(Haar)} ≲ ε^{(d-2s)/2}` for ALL `0 < s < d/2` and `0 < ε ≤ 1` (the torus form of
`eq:fetaL2Rate` / `eq:centeredFetaL2Rate` at `ε = η²`, TeX Step 2 of Proposition 5.5), and the
centered `L²(μ⊗μ)` residual `‖h̃ - h̃_ε‖`.

The point: `g - g_ε` is a.e. the centered nonnegative short-time piece `F∫_0^ε t^{p} p_t dt - mean`,
so its `L²` norm is controlled by the existing short-time square-mass bound with exponent
`d/2 - s`, with no heat-shift saturation.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicRieszMellinTail_measurable (s τ ε : ℝ) :
    Measurable (periodicRieszMellinTail (ι := ι) s τ ε) := by
  unfold periodicRieszMellinTail
  have hm : Measurable (fun q : ℝ × PeriodicTorus ι => (q.1 + τ, q.2)) := by fun_prop
  have hh := (periodicGaussianHeat_joint_measurable (ι := ι)).comp hm
  have hf : Measurable (fun q : ℝ × PeriodicTorus ι =>
      q.1 ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
        ((periodicGaussianHeat (q.1 + τ) q.2).re - 1)) :=
    (by fun_prop : Measurable (fun q : ℝ × PeriodicTorus ι =>
      q.1 ^ (((Fintype.card ι : ℝ) - s) / 2 - 1))).mul
      ((Complex.continuous_re.measurable.comp hh).sub measurable_const)
  exact (hf.stronglyMeasurable.integral_prod_left'
    (μ := (volume : Measure ℝ).restrict (Set.Ioi ε))).measurable

lemma periodicRieszPhysicalTail_measurable (s τ ε : ℝ) :
    Measurable (periodicRieszPhysicalTail (ι := ι) s τ ε) :=
  (periodicRieszMellinTail_measurable s τ ε).const_mul _

lemma periodicRieszPhysicalTail_memLp (s τ ε : ℝ) (hs : 0 < s) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (p : ℝ≥0∞) : MemLp (periodicRieszPhysicalTail (ι := ι) s τ ε) p (periodicHaar ι) := by
  have h : MemLp (periodicRieszPhysicalTail (ι := ι) s τ ε) ∞ (periodicHaar ι) :=
    MemLp.of_bound (periodicRieszPhysicalTail_measurable s τ ε).aestronglyMeasurable _
      (Eventually.of_forall (periodicRieszPhysicalTail_norm_bound s τ ε hs hτ hε))
  exact h.mono_exponent le_top

/-- Real kernel of the lower-cut remainder `g - g_ε` (lower cut at heat time `τ = ε = η²`). -/
def periodicRieszLCRemainder (s τ : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    PeriodicTorus ι → ℝ := fun x => periodicRieszKernel s hs2 x - periodicRieszPhysicalTail s 0 τ x

lemma periodicRieszLCRemainder_memLp (s τ : ℝ) (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hτ : 0 < τ) : MemLp (periodicRieszLCRemainder s τ hs2) 2 (periodicHaar ι) :=
  (periodicRieszKernel_memLp s hs2).sub (periodicRieszPhysicalTail_memLp s 0 τ hs0 le_rfl hτ 2)

lemma periodicRieszLCRemainder_stronglyMeasurable (s τ : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    StronglyMeasurable (periodicRieszLCRemainder (ι := ι) s τ hs2) :=
  (periodicRieszKernel_stronglyMeasurable s hs2).sub
    (periodicRieszPhysicalTail_measurable (ι := ι) s 0 τ).stronglyMeasurable

/-- The remainder is a.e. the centered short-time piece. -/
lemma periodicRieszLCRemainder_ae_eq (s τ : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 < τ) :
    periodicRieszLCRemainder s τ hs2 =ᵐ[periodicHaar ι]
      (fun x => periodicRieszPositiveShort s 0 τ x - periodicRieszMellinFactor ι s *
        (τ ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2))) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hsd : s < (Fintype.card ι : ℝ) := by
    have : 0 ≤ s ∨ s < 0 := le_or_gt 0 s
    rcases this with h | h
    · linarith
    · linarith
  filter_upwards [periodicRieszMellinGreen_ae_kernel (ι := ι) s hs2,
    periodicRieszMellinGreen_sub_tail_ae (ι := ι) s 0 τ hsd le_rfl hτ.le] with x h1 h2
  unfold periodicRieszLCRemainder
  rw [← h1]
  exact h2

lemma sq_integral_sub_mean_le (S : PeriodicTorus ι → ℝ) (hS : MemLp S 2 (periodicHaar ι)) :
    ∫ x, (S x - ∫ y, S y ∂periodicHaar ι) ^ 2 ∂periodicHaar ι ≤ ∫ x, S x ^ 2 ∂periodicHaar ι := by
  have h1 := hS.integrable_sq
  have h2 : Integrable S (periodicHaar ι) := hS.integrable (by norm_num)
  set m : ℝ := ∫ y, S y ∂periodicHaar ι with hm
  have hA : Integrable (fun x => S x ^ 2 - 2 * m * S x) (periodicHaar ι) :=
    h1.sub (h2.const_mul _)
  have e1 : ∫ x, (S x - m) ^ 2 ∂periodicHaar ι =
      (∫ x, S x ^ 2 ∂periodicHaar ι) - 2 * m * m + m ^ 2 := by
    have : (fun x => (S x - m) ^ 2) = fun x => (S x ^ 2 - 2 * m * S x) + m ^ 2 := by
      funext x; ring
    rw [this, integral_add hA (integrable_const _), integral_sub h1 (h2.const_mul _),
      integral_const_mul, ← hm]
    simp
  rw [e1]
  nlinarith [sq_nonneg m]

/-- Lower-cut remainder in `L²(Haar)`: `‖g - g_τ‖² ≲ τ^{(d-2s)/2}` for every `0 < s < d/2`. -/
theorem periodicRieszLCRemainder_integral_sq_le (s : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∫ x, periodicRieszLCRemainder s τ hs2 x ^ 2 ∂periodicHaar ι ≤
        C * τ ^ (((Fintype.card ι : ℝ) - 2 * s) / 2) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hsd : s < (Fintype.card ι : ℝ) := by linarith
  set C : ℝ := (periodicRieszMellinFactor ι s) ^ 2 * periodicHeatDiagonalSmallConstant ι /
    (((Fintype.card ι : ℝ) / 4 - s / 2) ^ 2) with hC
  refine ⟨C, ?_, ?_⟩
  · have := periodicHeatDiagonalSmallConstant_nonneg (ι := ι)
    positivity
  intro τ hτ hτ1
  have hS := periodicRieszPositiveShort_memLp (ι := ι) s τ 0 hs2 hτ hτ1 le_rfl
  have hmass := periodicRieszPositiveShort_mass (ι := ι) s 0 τ hsd le_rfl hτ.le
  have hae := periodicRieszLCRemainder_ae_eq s τ hs2 hτ
  have hcongr : ∫ x, periodicRieszLCRemainder s τ hs2 x ^ 2 ∂periodicHaar ι =
      ∫ x, (periodicRieszPositiveShort s 0 τ x - ∫ y, periodicRieszPositiveShort s 0 τ y ∂periodicHaar ι) ^ 2
        ∂periodicHaar ι := by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx, hmass]
  rw [hcongr]
  refine (sq_integral_sub_mean_le _ hS).trans ?_
  have hb := periodicRieszPositiveShort_sq_mass_bound (ι := ι) s τ 0 hs2 hτ hτ1 le_rfl
  refine hb.trans (le_of_eq ?_)
  rw [hC]
  congr 2
  ring

/-- Hoeffding-centered lower-cut kernel (continuous Fourier representative). -/
abbrev periodicLCCentered (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] (s τ : ℝ) :
    PeriodicTorus ι × PeriodicTorus ι → ℝ :=
  hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszLCKernel s τ (q.1 - q.2))

/-- Centered `L²(μ⊗μ)` residual `‖h̃ - h̃_τ‖` from the Haar remainder bound for the lower-cut family. -/
theorem periodicRieszLCResidual_of_remainder (s : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (θ : ℝ)
    (hrem : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∫ x, periodicRieszLCRemainder s τ hs2 x ^ 2 ∂periodicHaar ι ≤ C * τ ^ θ)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∀ (hh : MemLp (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))) 2
          ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)))
        (hq : MemLp (periodicLCCentered (periodicCappedDensityMeasure ρ) s τ) 2
          ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))),
      ‖(hh.sub hq).toLp (fun p => hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2)) p -
          periodicLCCentered (periodicCappedDensityMeasure ρ) s τ p)‖ ≤ A * τ ^ (θ / 2) := by
  obtain ⟨C, hC0, hC⟩ := hrem
  refine ⟨4 * M * Real.sqrt C, by positivity, ?_⟩
  intro τ hτ hτ1 hh hq
  set μ := periodicCappedDensityMeasure ρ with hμ
  have hg := periodicRieszLCRemainder_memLp s τ hs0 hs2 hτ
  have hgm := periodicRieszLCRemainder_stronglyMeasurable (ι := ι) s τ hs2
  have hWint : Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      periodicRieszKernel s hs2 (p.1 - p.2)) (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _ (periodicRieszKernel_integrable s hs2)
  have hVint : Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      periodicRieszLCKernel s τ (p.1 - p.2)) (μ.prod μ) := by
    apply periodicDensityPair_integrable_of_haar ρ M hρ _
    exact ((periodicPositiveFourierKernel_continuous _
      (periodicRieszLCCoeff_nonneg (ι := ι) s τ hs0 hτ.le)
      (periodicRieszLCCoeff_summable (ι := ι) s τ hs0 hs2 hτ)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  have hsub := ae_hoeffdingCentered_sub μ
    (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (p.1 - p.2))
    (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszLCKernel s τ (p.1 - p.2))
    hWint hVint
  have hgreen := periodicDensity_pair_ae_of_haar ρ
    (fun x => periodicRieszPhysicalTail s 0 τ x = periodicRieszLCKernel s τ x)
    (periodicRieszPhysicalTail_ae_LCKernel s τ hs0 hs2 hτ)
  have hWV : ((fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (p.1 - p.2)) -
      (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszLCKernel s τ (p.1 - p.2)))
      =ᵐ[μ.prod μ] (fun p => periodicRieszLCRemainder s τ hs2 (p.1 - p.2)) := by
    filter_upwards [hgreen] with p hp
    simp only [Pi.sub_apply, periodicRieszLCRemainder]
    rw [hp]
  have hcong := ae_hoeffdingCentered_congr μ _ _ hWV
  have hae : (fun p => hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2)) p -
      periodicLCCentered μ s τ p) =ᵐ[μ.prod μ]
      (fun p : PeriodicTorus ι × PeriodicTorus ι =>
        DGRHS.centeredKernel μ (fun x y => periodicRieszLCRemainder s τ hs2 (x - y)) p.1 p.2) := by
    filter_upwards [hsub, hcong] with p h1 h2
    have h3 : hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
        periodicRieszLCRemainder s τ hs2 (q.1 - q.2)) p =
        DGRHS.centeredKernel μ (fun x y => periodicRieszLCRemainder s τ hs2 (x - y)) p.1 p.2 := rfl
    rw [← h3, ← h2, h1]
    rfl
  have hcM := periodicCenteredPair_memLp_of_density_cap ρ M hρ _ hgm hg
  have hnorm := periodicCenteredPair_norm_le_of_density_cap ρ M hM hρ _ hgm hg
  have key : (hh.sub hq).toLp (fun p => hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2)) p -
      periodicLCCentered μ s τ p) = hcM.toLp (fun p : PeriodicTorus ι × PeriodicTorus ι =>
        DGRHS.centeredKernel μ (fun x y => periodicRieszLCRemainder s τ hs2 (x - y)) p.1 p.2) :=
    MemLp.toLp_congr _ _ hae
  rw [key]
  refine hnorm.trans ?_
  have hn2 : ‖hg.toLp (periodicRieszLCRemainder s τ hs2)‖ ^ 2 ≤ C * τ ^ θ := by
    rw [DGRHS.Kernel.norm_toLp_sq hg]
    exact hC τ hτ hτ1
  have hb := norm_le_sqrt_mul_rpow _ C τ θ (norm_nonneg _) hC0 hτ hn2
  calc 4 * M * ‖hg.toLp (periodicRieszLCRemainder s τ hs2)‖
      ≤ 4 * M * (Real.sqrt C * τ ^ (θ / 2)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end DGRHS.Periodic
