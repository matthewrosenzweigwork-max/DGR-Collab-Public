import DGRHS.Gaussian.PeriodicD1CircleKernel
import DGRHS.Gaussian.PeriodicD1GoodHaar
import DGRHS.Gaussian.PeriodicTrialParticleMean

/-! UNCOMPILED COPY (Claude complete physical d1 return, 2026-10-03): audited against
pinned Mathlib, no defect found; bytes after this header unchanged. It now imports
the repaired CircleKernel in this return. Original header follows.
 RECORDS-ONLY UNCOMPILED DRAFT. Transfer the actual one-dimensional source
particle law to circle coordinates, and pull the actual AE Green-kernel identity
through every off-diagonal pair. CircleKernel is an uncompiled predecessor.
No partition identity or integrability premise is supplied. The pointwise
Vandermonde exponential algebra and proper integral formula remain separate. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical
namespace DGRHS.Periodic

def periodicD1ParticleCoordinates (N : ℕ)
    (x : Fin N → PeriodicTorus (Fin 1)) : Fin N → UnitAddCircle := fun i => x i 0

lemma periodicD1ParticleCoordinates_measurePreserving (N : ℕ) :
    MeasurePreserving (periodicD1ParticleCoordinates N)
      (Measure.pi (fun _ : Fin N => periodicHaar (Fin 1))) (periodicHaar (Fin N)) := by
  exact measurePreserving_pi
    (fun _ : Fin N => periodicHaar (Fin 1))
    (fun _ : Fin N => (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (f := fun _ x => x 0)
    (fun _ => measurePreserving_eval
      (fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle)) 0)

lemma periodicD1ParticleCoordinates_distinct_ae (N : ℕ) :
    ∀ᵐ x : Fin N → PeriodicTorus (Fin 1)
      ∂Measure.pi (fun _ : Fin N => periodicHaar (Fin 1)),
      Function.Injective (periodicD1GoodNodes (periodicD1ParticleCoordinates N x)) := by
  exact (periodicD1ParticleCoordinates_measurePreserving N).quasiMeasurePreserving.ae
    periodicD1GoodNodes_injective_ae

lemma periodicD1_particle_pair_kernel_ae (N : ℕ) (i j : Fin N) (hij : i≠j) :
    ∀ᵐ x : Fin N → PeriodicTorus (Fin 1)
      ∂Measure.pi (fun _ : Fin N => periodicHaar (Fin 1)),
      periodicD1CircleKernel (x i-x j)=periodicLogKernel (x i-x j) := by
  have hp := periodicHaar_preserving_difference.comp
    (DGRHS.Decoupling.pair_eval_measurePreserving (periodicHaar (Fin 1)) i j hij)
  exact hp.quasiMeasurePreserving.ae periodicD1CircleKernel_eq_kernel_ae

lemma periodicD1_particle_all_pairs_kernel_ae (N : ℕ) :
    ∀ᵐ x : Fin N → PeriodicTorus (Fin 1)
      ∂Measure.pi (fun _ : Fin N => periodicHaar (Fin 1)),
      ∀i j,i≠j → periodicD1CircleKernel (x i-x j)=periodicLogKernel (x i-x j) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i=j
  · exact Eventually.of_forall (fun _ h => False.elim (h hij))
  · exact (periodicD1_particle_pair_kernel_ae N i j hij).mono (fun _ h _ => h)

/-- Exact ordered-pair source coefficient, before exponential/Vandermonde algebra. -/
lemma periodicD1_particle_exponent_circle_ae (β : ℝ) (N : ℕ) :
    (periodicParticleExponent (ι := Fin 1) β N)=ᵐ[
      Measure.pi (fun _ : Fin N => periodicHaar (Fin 1))]
      fun x => β/(2*(N:ℝ))*∑i,∑j,if i=j then 0 else periodicD1CircleKernel (x i-x j) := by
  filter_upwards [periodicD1_particle_all_pairs_kernel_ae N] with x hx
  unfold periodicParticleExponent
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i=j
  · simp only [hij,if_true]
  · simp only [hij,if_false]
    exact (hx i j hij).symm

end DGRHS.Periodic
