import DGPS.Lipschitz.T01DefectiveAssembly
import DGPS.Lipschitz.T01ArbitraryForceBound
import DGPS.Lipschitz.T01ConditionalMeanFieldLevel
import DGPS.Lipschitz.T01LastIncrementReference
import DGPS.Lipschitz.T01ActualScoreData
import DGPS.Analysis.RelativeFisher

/-!
# Large-particle defective absorption on actual score data

The equilibrium and all uniform reference/force constants are derived from positive scalar
rate. The kernel, diagonal derivative and reference LSI constant are fixed before the cutoff
and particle number. The remaining inputs at each particle number are factual normalized-law
score data. Their specialization to bounded positive particle tests is a separate domain adapter.
-/

open MeasureTheory InformationTheory Filter
open scoped ENNReal

namespace DGPS.Lipschitz

open KernelApproximation

/-- Shared absorption for a genuine local-level provider, on its specified class of laws. -/
private theorem t01_large_N_score_bound_of_local_levels {d : ℕ} (A : InteractionData d)
    (hA : LipschitzData A) (hd : 0 < d) (b : AbsoluteDrift A)
    (hrate : 0 < scalarRate A b) (μ : ProbabilityMeasure (Torus d))
    (hmin : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A)
    (D : KData d) (hD : D.K = centeredKernel A (μ : Measure (Torus d)))
    (gδ : Torus d → Tangent d) (hδm : Measurable gδ) (Mδ : ℝ)
    (hδb : ∀ x, ‖gδ x‖ ≤ Mδ)
    (hδ : IsWeakGradient (fun x => D.K x x) gδ)
    (R : ℝ≥0∞) (P : (N : ℕ+) → Measure (ParticleSpace d N) → Prop)
    (hlevel : ∀ (r₀ : ℝ), 0 ≤ r₀ → ENNReal.ofReal r₀ ≤ R →
      ∀ (N : ℕ+) (ν : Measure (ParticleSpace d N)) [IsProbabilityMeasure ν], P N ν →
        ∀ (Q : ParticleSpace d N → ℝ) (c C : ℝ)
          (GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ)
          (s : Fin N → Fin d → ParticleSpace d N → ℝ),
          SharpLSI.FL.ScoreData A.V A.W (μ : Measure (Torus d)) ν Q c C GQ s
            (fun x y k => D.G1 x y k) (fun x k => gδ x k / 2) (|D.B| + |Mδ|) →
          klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≠ ⊤ →
          ∀ (ε : ℝ), 0 < ε → ∀ (j : ℕ), j < (N : ℕ) →
            2 * r₀ * ((SharpLSI.FL.hRev ν (μ : Measure (Torus d)) j).toReal +
              SharpLSI.FL.condMeanS ν 2 (SharpLSI.FL.Bk A.W (μ : Measure (Torus d))) j) ≤
              (1 + ε) * ((N : ℝ)⁻¹ * SharpLSI.FL.fisherS ν s) +
                (1 + 1 / ε) * SharpLSI.FL.forceDelta
                  (fun x y k => D.G1 x y k) (fun x k => gδ x k / 2) ν j)
    {r : ℝ} (hr : 0 < r) (hrr : ENNReal.ofReal r < R) :
    ∃ N₀ : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N : ℕ+), N₀ ≤ N →
        ∀ (ν : Measure (ParticleSpace d N)) [IsProbabilityMeasure ν], P N ν →
          ∀
          (Q : ParticleSpace d N → ℝ) (c C : ℝ)
          (GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ)
          (s : Fin N → Fin d → ParticleSpace d N → ℝ),
          SharpLSI.FL.ScoreData A.V A.W (μ : Measure (Torus d)) ν Q c C GQ s
            (fun x y k => D.G1 x y k) (fun x k => gδ x k / 2) (|D.B| + |Mδ|) →
          klDiv ν (particleLaw A N) ≠ ⊤ →
            2 * r * (klDiv ν (particleLaw A N)).toReal ≤ SharpLSI.FL.fisherS ν s + K := by
  classical
  obtain ⟨μ₀, hmin₀, huniq₀, -, hfix, c₀, Cref, p, -, -, hCref, -, -, hRef⟩ :=
    t01_positive_rate_reference_data A hA b hrate
  have hμ₀ : μ₀ = μ := (huniq₀ μ hmin).symm
  subst μ₀
  have href : ∀ (N : ℕ+) (ν : Measure (ParticleSpace d N)) [IsProbabilityMeasure ν],
      klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤
        ENNReal.ofReal Cref * (klDiv ν (particleLaw A N) + 1) := fun N ν _ => (hRef N).2.2 ν
  obtain ⟨g₀, C20, hC20, hU₀, -, -, hForce⟩ :=
    t01_arbitrary_force_bound_of_reference_entropy A hA hd μ hfix hCref.le href
  let bF := fun x y k => D.G1 x y k
  let bΔ := fun x k => gδ x k / 2
  let gG : (N : ℕ+) → ParticleSpace d N → Fin N → Tangent d :=
    fun N X i => WithLp.toLp 2 (fun k => SharpLSI.FL.Gpart bF bΔ N X i k)
  have hG : ∀ N, IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) (gG N) :=
    fun N => (actual_centered_Gpart_data A μ D hD hδ N).1
  have hForceRep := kernel_force_rep D hδm hδb
  obtain ⟨Aref, hAref0, hAref⟩ := exists_actual_refLSI A hA μ hfix
  obtain ⟨r₀, hrr₀, hr₀⟩ := SharpLSI.exists_r0 hr hrr
  have hr₀0 : 0 < r₀ := hr.trans hrr₀
  obtain ⟨τ, ε, hτ0, hτ, hε, hchoice⟩ := SharpLSI.exists_tau_eps hr hrr₀
    (a := 2 + 4 * Aref * C20) (b := 8 * r₀ * Aref) (by positivity) (by positivity)
  obtain ⟨C18, h18⟩ := t01_centered_conditional_products A μ τ hτ0
  obtain ⟨C21, h21⟩ := abstract_force_sum_all_cutoffs hForceRep (by positivity) τ hτ0
  let C18' := max C18 0
  let C21' := max C21 0
  have hC18' : 0 ≤ C18' := le_max_right _ _
  have hC21' : 0 ≤ C21' := le_max_right _ _
  let K := SharpLSI.FL.algK r r₀ τ ε Aref C18' Cref C20 C21' Cref
  refine ⟨⌈4 / τ⌉₊ + 4, K, le_max_left _ _, ?_⟩
  intro N hN ν _ hPν Q c C GQ s hscore hfin
  obtain ⟨hM3, hMN, hτM, hM2τ, hNpos⟩ := SharpLSI.ceil_tau_facts hτ0 hτ hN
  generalize ⌈τ * (N : ℝ)⌉₊ = M at hM3 hMN hτM hM2τ
  obtain ⟨hfinQ, hid⟩ := t01_particle_relative_entropy_identity A μ hfix N ν hfin
  let H := (klDiv ν (particleLaw A N)).toReal
  let H0 := (klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))).toReal
  let I := SharpLSI.FL.fisherS ν s
  let GG := ∫ X, ∑ i, ∑ k : Fin d, SharpLSI.FL.Gpart bF bΔ N X i k ^ 2 ∂ν
  have hH : 0 ≤ H := ENNReal.toReal_nonneg
  have hH0 : 0 ≤ H0 := ENNReal.toReal_nonneg
  have hI : 0 ≤ I := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ =>
    integral_nonneg fun X => sq_nonneg _
  have hGG : 0 ≤ GG := integral_nonneg fun X =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hH0le : H0 ≤ Cref * (H + 1) := by
    have hRt : ENNReal.ofReal Cref * (klDiv ν (particleLaw A N) + 1) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨hfin, ENNReal.one_ne_top⟩)
    have hh := ENNReal.toReal_mono hRt (href N ν)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCref.le,
      ENNReal.toReal_add hfin ENNReal.one_ne_top, ENNReal.toReal_one] at hh
  have hGGle : GG ≤ C20 * (H + 1) := by
    have he : GG = ∫ X, particleTangentNormSq (gG N X) ∂ν := by
      apply integral_congr_ae
      exact Eventually.of_forall fun X => by
        simpa only [particleTangentNormSq_eq, gG]
    rw [he, t01_centered_force_integral_eq A μ N (hG N) (hU₀ N) ν hfin]
    exact hForce N ν hfin
  have hmain := t01_sum_conditional_levels (M := M) N.pos hε.le hI
    (fun j => (SharpLSI.FL.hRev ν (μ : Measure (Torus d)) j).toReal)
    (fun j => SharpLSI.FL.condMeanS ν 2 (SharpLSI.FL.Bk A.W (μ : Measure (Torus d))) j)
    (SharpLSI.FL.forceDelta bF bΔ ν)
    (fun j hj => hlevel r₀ hr₀0.le hr₀ N ν hPν Q c C GQ s hscore hfinQ ε hε j hj)
  have hSf : (∑ j ∈ Finset.range ((N : ℕ) - M), SharpLSI.FL.forceDelta bF bΔ ν j) ≤
      C21' * (1 + Real.sqrt H0) :=
    (h21 N M hMN hτM (μ : Measure (Torus d)) ν hfinQ).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hSh := SharpLSI.FL.chain_lower ν (μ : Measure (Torus d)) hfinQ hMN
  have hlast := actual_last_increment_reference_bound_of_refLSI A hA μ hscore hfinQ
    hAref0 hAref ((N : ℕ) - 1) (by omega)
  have hsG := t01_score_difference_energy_le hscore
  have hP : (M : ℝ) * (SharpLSI.FL.hRev ν (μ : Measure (Torus d)) ((N : ℕ) - 1)).toReal ≤
      ((M : ℝ) / N) * Aref * (2 * I + 2 * GG) := by
    calc
      _ ≤ M * (Aref * ((N : ℝ)⁻¹ * ∑ i, ∫ X, ∑ k : Fin d,
          (s i k X - SharpLSI.FL.Gpart bF bΔ N X i k) ^ 2 ∂ν)) :=
        mul_le_mul_of_nonneg_left hlast (Nat.cast_nonneg _)
      _ ≤ M * (Aref * ((N : ℝ)⁻¹ * (2 * I + 2 * GG))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsG (by positivity)) hAref0.le) (Nat.cast_nonneg _)
      _ = _ := by rw [div_eq_mul_inv]; ring
  have hprod := h18 N M (by omega) hMN hτM ν hfinQ
  have hBk : (fun z : Fin 2 → Torus d => DGPS.centeredKernel A μ (z 0) (z 1) / 2) =
      SharpLSI.FL.Bk A.W (μ : Measure (Torus d)) := by
    funext z
    simp only [SharpLSI.FL.Bk, t01_legacy_centeredKernel_eq]
  rw [hBk] at hprod
  have hfrac : ((((N : ℕ) - M : ℕ) : ℝ) / N) = 1 - (M : ℝ) / N := by
    rw [Nat.cast_sub hMN, sub_div, div_self hNpos.ne']
  rw [hfrac] at hprod
  have hScp : (1 - (M : ℝ) / N) * (∫ X, centeredParticlePotential A μ N X ∂ν) -
      C18' * (1 + Real.sqrt H0) ≤
      ∑ j ∈ Finset.range ((N : ℕ) - M),
        SharpLSI.FL.condMeanS ν 2 (SharpLSI.FL.Bk A.W (μ : Measure (Torus d))) j := by
    have hh := (abs_le.mp hprod).1
    have hmax : C18 * (1 + Real.sqrt H0) ≤ C18' * (1 + Real.sqrt H0) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith
  have hEU : (∫ X, centeredParticlePotential A μ N X ∂ν) =
      H - H0 - Real.log (centeredParticleNormalizer A μ N) := by linarith
  have hlog : Real.log (centeredParticleNormalizer A μ N) ≤ Cref :=
    (le_abs_self _).trans (hRef N).1
  exact SharpLSI.FL.large_N_algebra hr hrr₀ hτ0 hτ hε hAref0.le hC18' hCref.le hC20 hC21'
    hCref.le hchoice hH hH0 hI hGG (by positivity) hM2τ hmain hSf hSh hP hScp hEU hlog
    hH0le hGGle

/-- The actual species subrate supplies the unrestricted large-N score inequality.
The fixed diagonal derivative and every absorption constant precede N and the comparison law. -/
theorem t01_large_N_species_score_bound {d : ℕ} (A : InteractionData d)
    (hA : LipschitzData A) (hd : 0 < d) (b : AbsoluteDrift A)
    (hrate : 0 < scalarRate A b) (μ : ProbabilityMeasure (Torus d))
    (hmin : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A)
    (D : KData d) (hD : D.K = centeredKernel A (μ : Measure (Torus d)))
    (gδ : Torus d → Tangent d) (hδm : Measurable gδ) (Mδ : ℝ)
    (hδb : ∀ x, ‖gδ x‖ ≤ Mδ) (hδ : IsWeakGradient (fun x => D.K x x) gδ)
    {r : ℝ} (hr : 0 < r) (hrr : ENNReal.ofReal r < speciesRate A b) :
    ∃ N₀ : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ+), N₀ ≤ N →
      ∀ (ν : Measure (ParticleSpace d N)) [IsProbabilityMeasure ν]
        (Q : ParticleSpace d N → ℝ) (c C : ℝ)
        (GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ)
        (s : Fin N → Fin d → ParticleSpace d N → ℝ),
        SharpLSI.FL.ScoreData A.V A.W (μ : Measure (Torus d)) ν Q c C GQ s
          (fun x y k => D.G1 x y k) (fun x k => gδ x k / 2) (|D.B| + |Mδ|) →
        klDiv ν (particleLaw A N) ≠ ⊤ →
          2 * r * (klDiv ν (particleLaw A N)).toReal ≤ SharpLSI.FL.fisherS ν s + K := by
  let v := DGPS.RelativeFisher.lipGradVec (frozenPotential A (μ : Measure (Torus d)))
  obtain ⟨L, hL, hΦ⟩ := lipschitz_equilibriumPotential A hA
  have hvm : Measurable v := DGPS.RelativeFisher.measurable_lipGradVec (hΦ (μ : Measure (Torus d)))
  have hv := actual_frozen_lipGrad_isWeakGradient A hA μ
  have hvc : ∀ x k, v x k = SharpLSI.lipGrad (SharpLSI.PhiMF A.V A.W μ) x k := fun _ _ => rfl
  obtain ⟨N₀, K, hK, hbound⟩ := t01_large_N_score_bound_of_local_levels A hA hd b hrate μ hmin
    D hD gδ hδm Mδ hδb hδ (speciesRate A b) (fun _ _ => True) (by
      intro r₀ hr₀ hR₀ N ν _ _ Q c C GQ s hscore hH ε hε j hj
      exact actual_species_level_bound A hA b μ hmin D hD hvm hv hvc hscore hH hr₀ hR₀ hε hj)
    hr hrr
  exact ⟨N₀, K, hK, fun N hN ν _ => hbound N hN ν True.intro⟩

/-- The actual scalar subrate supplies the same absorption on symmetric comparison laws.
Only the local pointwise provider changes; the entropy, force and cutoff proof is shared. -/
theorem t01_large_N_scalar_score_bound {d : ℕ} (A : InteractionData d)
    (hA : LipschitzData A) (hd : 0 < d) (b : AbsoluteDrift A)
    (hrate : 0 < scalarRate A b) (μ : ProbabilityMeasure (Torus d))
    (hmin : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A)
    (D : KData d) (hD : D.K = centeredKernel A (μ : Measure (Torus d)))
    (gδ : Torus d → Tangent d) (hδm : Measurable gδ) (Mδ : ℝ)
    (hδb : ∀ x, ‖gδ x‖ ≤ Mδ) (hδ : IsWeakGradient (fun x => D.K x x) gδ)
    {r : ℝ} (hr : 0 < r) (hrr : ENNReal.ofReal r < scalarRate A b) :
    ∃ N₀ : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ+), N₀ ≤ N →
      ∀ (ν : Measure (ParticleSpace d N)) [IsProbabilityMeasure ν],
        SharpLSI.IsSymmetricMeasure ν →
        ∀ (Q : ParticleSpace d N → ℝ) (c C : ℝ)
          (GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ)
          (s : Fin N → Fin d → ParticleSpace d N → ℝ),
          SharpLSI.FL.ScoreData A.V A.W (μ : Measure (Torus d)) ν Q c C GQ s
            (fun x y k => D.G1 x y k) (fun x k => gδ x k / 2) (|D.B| + |Mδ|) →
          klDiv ν (particleLaw A N) ≠ ⊤ →
            2 * r * (klDiv ν (particleLaw A N)).toReal ≤ SharpLSI.FL.fisherS ν s + K := by
  let v := DGPS.RelativeFisher.lipGradVec (frozenPotential A (μ : Measure (Torus d)))
  obtain ⟨L, hL, hΦ⟩ := lipschitz_equilibriumPotential A hA
  have hvm : Measurable v := DGPS.RelativeFisher.measurable_lipGradVec (hΦ (μ : Measure (Torus d)))
  have hv := actual_frozen_lipGrad_isWeakGradient A hA μ
  have hvc : ∀ x k, v x k = SharpLSI.lipGrad (SharpLSI.PhiMF A.V A.W μ) x k := fun _ _ => rfl
  exact t01_large_N_score_bound_of_local_levels A hA hd b hrate μ hmin D hD gδ hδm Mδ hδb hδ
    (scalarRate A b) (fun _ ν => SharpLSI.IsSymmetricMeasure ν) (by
      intro r₀ hr₀ hR₀ N ν _ hsym Q c C GQ s hscore hH ε hε j hj
      apply actual_level_bound_of_pointwise A hA μ D hvm hvc hscore hH ?_ hε hj
      intro S hS
      exact ae_conditional_scalar_explicit_score A b μ hmin D hD hv hr₀ hR₀ hscore.dens
        hscore.gradW hscore.gradM hscore.gradL2 ν hscore.eq hsym S (Finset.card_pos.mp hS)) hr hrr

end DGPS.Lipschitz
