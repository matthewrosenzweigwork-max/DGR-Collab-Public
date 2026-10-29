import DGRHS.CLT.SourceEquilibriumMacroscopic
import DGRHS.CLT.SourceLogSingularLogRate
import DGRHS.CLT.SourceRieszSingularRate

/-! Source569--584: genuine canonical determinant correction with the original
logarithmic power rate and Riesz logarithmic rate. Constants are chosen before
N; the spectrum is that of the actual centered interaction on mean-zero L2.
The explicit finite-V domain is still a source-alignment obligation, not an
unannounced replacement for the original thermal equilibrium hypothesis. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace DGRHS.CLT
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι]

theorem sourceLog_equilibrium_correction (β : ℝ≥0) (hβ : 0 < (β : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x => Real.exp (-4 * (β : ℝ) *
      logPhysicalPotential (gaussianRieszDensityMeasure ρ) x)) (gaussianRieszDensityMeasure ρ))
    (V : EuclideanSpace ℝ ι → ℝ) (hV : Integrable V (gaussianRieszDensityMeasure ρ))
    (hEL : (volume : Measure (EuclideanSpace ℝ ι)).tilted (fun x => -(β : ℝ) *
      (V x + DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b)) x)) =
      gaussianRieszDensityMeasure ρ) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι => logPhysicalPair (a,b)
    let h := hoeffdingCentered μ logPhysicalPair
    let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
    ∃ (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p) (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧ (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => (β : ℝ) * eig i) ∧
      HasProd (fun i => (1 + (β : ℝ) * eig i) * Real.exp (-((β : ℝ) * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => (β : ℝ) * eig i)) ∧
      Integrable (llr μ volume) μ ∧
      Tendsto (fun N => Real.log (canonicalSingularPartition volume W V (β : ℝ) N).toReal +
        (β : ℝ) * (N : ℝ) * macroscopicFreeEnergy volume μ W V (β : ℝ)) atTop
        (𝓝 ((β : ℝ) * DGRHS.interactionEnergy μ W -
          (1/2 : ℝ) * Real.log (DGRHS.Kernel.regularizedDet (fun i => (β : ℝ) * eig i)))) ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
        (0 < canonicalSingularPartition volume W V (β : ℝ) N ∧
          canonicalSingularPartition volume W V (β : ℝ) N < ∞) ∧
        |Real.log (canonicalSingularPartition volume W V (β : ℝ) N).toReal -
          (-(β : ℝ) * (N : ℝ) * macroscopicFreeEnergy volume μ W V (β : ℝ) +
            (β : ℝ) * DGRHS.interactionEnergy μ W -
              (1/2 : ℝ) * Real.log (DGRHS.Kernel.regularizedDet (fun i => (β : ℝ) * eig i)))| ≤
            C * (Real.exp 1 + (N : ℝ))^(-c) := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι => logPhysicalPair (a,b)
  obtain ⟨hs,hc,κ,eig,e,hκ,he,hD,hProd,hT,c,C,hc0,hc1,hC,hRate⟩ :=
    sourceLogSingularPartition_original_log_rate β hβ hd ρ M hM hρ hpair htail
  have hdet := log_inv_sqrt_regularizedDet eig (β : ℝ) hD
  rw [hdet] at hT
  simp only [neg_mul, ← sub_eq_add_neg] at hT
  have hcanon N (hN : 1 ≤ N) :=
    sourceLog_equilibrium_macroscopic β hβ hd ρ M hM hρ hpair V hV hEL N hN
  refine ⟨hs,hc,κ,eig,e,hκ,he,hD,hProd,(hcanon 1 (by norm_num)).2.1,
    hT.congr' ((eventually_ge_atTop 1).mono fun N hN => ?_),c,C,hc0,hc1,hC,?_⟩
  · dsimp only
    rw [(hcanon N hN).2.2.2]
    ring
  · intro N hN
    refine ⟨(hcanon N hN).1,?_⟩
    have hr := (hRate N hN).2.2.2
    rw [hdet] at hr
    convert hr using 1
    rw [(hcanon N hN).2.2.2]
    congr 1
    ring

theorem sourceRiesz_equilibrium_correction (s β : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (V : EuclideanSpace ℝ ι → ℝ) (hV : Integrable V (gaussianRieszDensityMeasure ρ))
    (hEL : (volume : Measure (EuclideanSpace ℝ ι)).tilted (fun x => -β *
      (V x + DGRHS.potential (gaussianRieszDensityMeasure ρ)
        (fun a b => gaussianRieszPhysicalPair s (a,b)) x)) = gaussianRieszDensityMeasure ρ) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    ∃ (hh : MemLp h 2 (μ.prod μ)) (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧ (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      HasProd (fun i => (1 + β * eig i) * Real.exp (-(β * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) ∧
      Integrable (llr μ volume) μ ∧
      Tendsto (fun N => Real.log (canonicalSingularPartition volume W V β N).toReal +
        β * (N : ℝ) * macroscopicFreeEnergy volume μ W V β) atTop
        (𝓝 (β * DGRHS.interactionEnergy μ W -
          (1/2 : ℝ) * Real.log (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
        (0 < canonicalSingularPartition volume W V β N ∧
          canonicalSingularPartition volume W V β N < ∞) ∧
        |Real.log (canonicalSingularPartition volume W V β N).toReal -
          (-β * (N : ℝ) * macroscopicFreeEnergy volume μ W V β +
            β * DGRHS.interactionEnergy μ W -
              (1/2 : ℝ) * Real.log (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))| ≤
            C * (Real.log (Real.exp 1 + (N : ℝ)))^(-(((Fintype.card ι : ℝ)-2*s)/(2*s))) := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
  obtain ⟨hh,hSym,hCan,κ,eig,e,hκ,he,hD,hProd,hT,hLog,C,hC,hRate⟩ :=
    sourceRieszSingularPartition_original_rate s β hs hβ.le ha ρ M hM hρ
  have hdet := log_inv_sqrt_regularizedDet eig β hD
  rw [hdet] at hLog
  simp only [neg_mul, ← sub_eq_add_neg] at hLog
  have hcanon N (hN : 1 ≤ N) :=
    sourceRiesz_equilibrium_macroscopic s β hs hβ ha ρ M hM hρ V hV hEL N hN
  refine ⟨hh,hSym,hCan,κ,eig,e,hκ,he,hD,hProd,(hcanon 1 (by norm_num)).2.1,
    hLog.congr' ((eventually_ge_atTop 1).mono fun N hN => ?_),C,hC,?_⟩
  · dsimp only
    rw [(hcanon N hN).2.2.2]
    ring
  · intro N hN
    refine ⟨(hcanon N hN).1,?_⟩
    have hr := (hRate N hN).2.2.2
    rw [hdet] at hr
    convert hr using 1
    rw [(hcanon N hN).2.2.2]
    congr 1
    ring

end DGRHS.CLT
#check @DGRHS.CLT.sourceLog_equilibrium_correction
#print axioms DGRHS.CLT.sourceLog_equilibrium_correction
#check @DGRHS.CLT.sourceRiesz_equilibrium_correction
#print axioms DGRHS.CLT.sourceRiesz_equilibrium_correction
