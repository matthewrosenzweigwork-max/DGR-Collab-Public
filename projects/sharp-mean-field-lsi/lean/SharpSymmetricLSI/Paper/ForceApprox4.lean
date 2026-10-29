import SharpSymmetricLSI.Paper.ForceApprox3
import SharpSymmetricLSI.Paper.GroundT3
import SharpSymmetricLSI.Statements.R23_Reference_Spectrum

/-!
# R31 groundwork: the eigenbasis kernels `K_R` through `C¹` representatives (R23)
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem haar_ac_minimizer (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) : haar d ≪ (μ : Measure (Torus d)) := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨hpm, hppos, -⟩ := elDensity_props hyp μm
  have hμp : μm = densMeasure (elDens V W μm) := minimizer_eq_elDensity hyp hμ
  rw [hμp]
  exact withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp hpm).aemeasurable
    (Eventually.of_forall fun x => by simp [hppos x])

/-- `C¹` representatives of the reference eigenfunctions (R23). -/
theorem exists_c1_reps (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    ∃ eC : ℕ → Torus d → ℝ, ∀ j, ContDiff ℝ 1 (eC j ∘ liftT) ∧ eC j =ᵐ[haar d] e j ∧
      eC j =ᵐ[(μ : Measure (Torus d))] e j := by
  obtain ⟨-, -, -, C, q, hC⟩ := (ref_spectrum hd hyp hr hμ).2 e lam he
  choose eC hc using hC
  exact ⟨eC, fun j => ⟨(hc j).1, (haar_ac_minimizer hyp hμ).ae_le (hc j).2.1, (hc j).2.1⟩⟩

section
variable {e eC : ℕ → Torus d → ℝ} (heC : ∀ j, eC j =ᵐ[haar d] e j)
  (s : Finset ℕ) (a : ℕ → ℕ → ℝ) {KR : Torus d → Torus d → ℝ}
  (hK : ∀ x y, KR x y = ∑ i ∈ s, ∑ j ∈ s, a i j * e (i + 1) x * e (j + 1) y)
include heC hK

theorem Ukernel_ae_finKer (N : ℕ) :
    (fun y : UnitAddTorus (Fin N × Fin d) => UkernelF KR N (unflat y)) =ᵐ[volume]
      fun y => UkernelF (finKer (fun i => eC (i + 1)) s a) N (unflat y) := by
  have hb : ∀ (b : Fin N) (j : ℕ), (fun y : UnitAddTorus (Fin N × Fin d) => e j (projBlock b y))
      =ᵐ[volume] fun y => eC j (projBlock b y) := fun b j =>
    (measurePreserving_projBlock b).quasiMeasurePreserving.ae_eq_comp (heC j).symm
  have hall : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin N × Fin d))), ∀ (b : Fin N) (j : ℕ),
      e j (projBlock b y) = eC j (projBlock b y) := by
    rw [ae_all_iff]; intro b; rw [ae_all_iff]; intro j; exact hb b j
  filter_upwards [hall] with y hy
  simp only [UkernelF, finKer, hK]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show unflat y b = projBlock b y from rfl, show unflat y c = projBlock c y from rfl,
    hy b (i + 1), hy c (j + 1)]

theorem pair_ae_finKer :
    (fun y : UnitAddTorus (Fin 2 × Fin d) => KR (projBlock 0 y) (projBlock 1 y)) =ᵐ[volume]
      fun y => finKer (fun i => eC (i + 1)) s a (projBlock 0 y) (projBlock 1 y) := by
  have hb : ∀ (b : Fin 2) (j : ℕ), (fun y : UnitAddTorus (Fin 2 × Fin d) => e j (projBlock b y))
      =ᵐ[volume] fun y => eC j (projBlock b y) := fun b j =>
    (measurePreserving_projBlock b).quasiMeasurePreserving.ae_eq_comp (heC j).symm
  have hall : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin 2 × Fin d))), ∀ (b : Fin 2) (j : ℕ),
      e j (projBlock b y) = eC j (projBlock b y) := by
    rw [ae_all_iff]; intro b; rw [ae_all_iff]; intro j; exact hb b j
  filter_upwards [hall] with y hy
  simp only [finKer, hK, hy]

theorem diag_ae_finKer :
    (fun z : Torus d => KR z z / 2) =ᵐ[haar d]
      fun z => finKer (fun i => eC (i + 1)) s a z z / 2 := by
  have hall : ∀ᵐ z ∂haar d, ∀ j, e j z = eC j z := by
    rw [ae_all_iff]; intro j; exact (heC j).mono fun z h => h.symm
  filter_upwards [hall] with z hz
  simp only [finKer, hK, hz]

end

end SharpLSI
