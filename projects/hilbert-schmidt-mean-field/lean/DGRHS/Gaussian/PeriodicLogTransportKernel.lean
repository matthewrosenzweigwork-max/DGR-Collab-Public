import DGRHS.Gaussian.PeriodicLogSmoothKernel
import DGRHS.Gaussian.PeriodicRieszTransportKernel
import DGRHS.Gaussian.PeriodicRieszSmoothSymmetry
import DGRHS.Gaussian.PeriodicRieszPairProperties

/-!
Packet P9h, unit 3 (LOG, part 6): the torus LOG transport kernel of Theorem 2.8,
`κ_n(x,y) = D^n g(x-y)[v x - v y]` with `g = periodicLogSmooth` the canonical smooth lift of the periodic
LOG kernel at the fixed scale `τ₀ = 1/2`; `0` on the diagonal.  Lattice periodicity, evenness,
symmetry and measurability.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma periodicLogProfileSum_add_lattice (η : ℝ) (z : E) (m : PeriodicFrequency ι) :
    periodicLogProfileSum η (z + periodicFrequencyVector m) = periodicLogProfileSum η z := by
  unfold periodicLogProfileSum
  have h := (Equiv.addRight m).tsum_eq
    (fun k : PeriodicFrequency ι => gaussianLogShortRange η (z + periodicFrequencyVector k))
  rw [← h]
  refine tsum_congr fun k => ?_
  simp only [Equiv.coe_addRight]
  congr 1
  have : periodicFrequencyVector (k + m) = periodicFrequencyVector k + periodicFrequencyVector m := by
    ext i; simp
  rw [this]; abel

lemma gaussianLogShortRange_neg (η : ℝ) (y : E) : gaussianLogShortRange η (-y) = gaussianLogShortRange η y := by
  unfold gaussianLogShortRange
  simp [norm_neg]

lemma periodicLogProfileSum_neg (η : ℝ) (z : E) :
    periodicLogProfileSum η (-z) = periodicLogProfileSum η z := by
  unfold periodicLogProfileSum
  have h := (Equiv.neg (PeriodicFrequency ι)).tsum_eq
    (fun k : PeriodicFrequency ι => gaussianLogShortRange η (z + periodicFrequencyVector k))
  rw [← h]
  refine tsum_congr fun k => ?_
  simp only [Equiv.neg_apply]
  rw [← gaussianLogShortRange_neg η (z + periodicFrequencyVector (-k))]
  congr 1
  have : periodicFrequencyVector (-k) = -periodicFrequencyVector k := by ext i; simp
  rw [this]; abel

lemma periodicLogLongKernel_add_lattice (ε : ℝ) (z : E) (m : PeriodicFrequency ι) :
    periodicLogLongKernel ε (z + periodicFrequencyVector m) = periodicLogLongKernel ε z := by
  unfold periodicLogLongKernel
  refine tsum_congr fun k => ?_
  rw [periodicPhase_add_lattice]
  have h : (∑ i, (k i : ℝ) * (m i : ℝ)) = (((∑ i, k i * m i : ℤ)) : ℝ) := by push_cast; rfl
  rw [h, cos_two_pi_add_int]

lemma periodicLogSmoothLift_add_lattice (τ : ℝ) (z : E) (m : PeriodicFrequency ι) :
    periodicLogSmoothLift τ (z + periodicFrequencyVector m) = periodicLogSmoothLift τ z := by
  simp only [periodicLogSmoothLift, periodicLogProfileSum_add_lattice, periodicLogLongKernel_add_lattice]

lemma periodicLogSmoothLift_neg (τ : ℝ) (z : E) :
    periodicLogSmoothLift τ (-z) = periodicLogSmoothLift τ z := by
  simp only [periodicLogSmoothLift, periodicLogProfileSum_neg, periodicLogLongKernel_neg]

/-- The canonical smooth lift of the periodic LOG kernel at the fixed scale `τ₀ = 1/2`. -/
def periodicLogSmooth : E → ℝ := periodicLogSmoothLift periodicRieszTau

/-- The torus LOG transport kernel of Theorem 2.8. -/
def periodicLogTransportKernel (n : ℕ) (v : PeriodicTorus ι → E)
    (p : PeriodicTorus ι × PeriodicTorus ι) : ℝ :=
  if p.1 = p.2 then 0 else
    iteratedFDeriv ℝ n (periodicLogSmooth (ι := ι)) (periodicCenteredLift (p.1 - p.2))
      (fun _ => v p.1 - v p.2)

lemma periodicLogSmooth_neg (z : E) : periodicLogSmooth (-z) = periodicLogSmooth z :=
  periodicLogSmoothLift_neg _ z

lemma periodicLogSmooth_add_lattice (z : E) (m : PeriodicFrequency ι) :
    periodicLogSmooth (z + periodicFrequencyVector m) = periodicLogSmooth z :=
  periodicLogSmoothLift_add_lattice _ z m

lemma periodicLogTransportKernel_symm (n : ℕ) (v : PeriodicTorus ι → E)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicLogTransportKernel n v p.swap = periodicLogTransportKernel n v p := by
  by_cases hp : p.1 = p.2
  · simp [periodicLogTransportKernel, hp]
  have hp' : p.2 ≠ p.1 := Ne.symm hp
  simp only [periodicLogTransportKernel, Prod.fst_swap, Prod.snd_swap, ite_eq_right hp, ite_eq_right hp']
  obtain ⟨m, hm⟩ := exists_centeredLift_neg (p.1 - p.2)
  have hsub : p.2 - p.1 = -(p.1 - p.2) := by abel
  rw [hsub, hm]
  have hper : ∀ z (m : PeriodicFrequency ι),
      periodicLogSmooth (z + periodicFrequencyVector m) = periodicLogSmooth z :=
    fun z m => periodicLogSmooth_add_lattice z m
  rw [iteratedFDeriv_add_lattice hper]
  have h := iteratedFDeriv_neg_apply_neg (periodicLogSmooth_neg (ι := ι)) n
    (periodicCenteredLift (p.1 - p.2)) (fun _ => v p.1 - v p.2)
  have hneg : (fun _ : Fin n => v p.2 - v p.1) = fun _ => -(v p.1 - v p.2) := by
    funext i; abel
  rw [hneg]
  exact h

lemma periodicLogSmooth_contDiffAt (N : ℕ) {z : E} (hz : z ∈ (periodicOffLattice : Set E)) :
    ContDiffAt ℝ N (periodicLogSmooth (ι := ι)) z := by
  have hτ := periodicRieszTau_pos
  have hP := periodicLogProfileSum_contDiffAt (ι := ι) periodicRieszTau hτ N hz
  have hL : ContDiffAt ℝ N (periodicLogLongKernel (ι := ι) (periodicHeatCut periodicRieszTau)) z :=
    (contDiff_periodicLogLongKernel (periodicHeatCut periodicRieszTau) (periodicHeatCut_pos hτ) N).contDiffAt
  unfold periodicLogSmooth periodicLogSmoothLift
  exact ((contDiffAt_const.mul hP).add hL).sub contDiffAt_const

lemma periodicCenteredLift_zero : periodicCenteredLift (0 : PeriodicTorus ι) = 0 := by
  ext i
  simp only [periodicCenteredLift_apply, PiLp.zero_apply]
  have h := norm_circleCentered (0 : UnitAddCircle)
  rw [norm_zero] at h
  exact abs_eq_zero.mp h.symm

lemma continuousOn_periodicLogSmooth_iteratedFDeriv (n : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ n (periodicLogSmooth (ι := ι))) (periodicOffLattice : Set E) := by
  have hco : ContDiffOn ℝ n (periodicLogSmooth (ι := ι)) (periodicOffLattice : Set E) :=
    fun z hz => (periodicLogSmooth_contDiffAt n hz).contDiffWithinAt
  have h := hco.continuousOn_iteratedFDerivWithin (m := n) le_rfl isOpen_periodicOffLattice.uniqueDiffOn
  exact h.congr (fun z hz => (iteratedFDerivWithin_of_isOpen n isOpen_periodicOffLattice hz).symm)

lemma periodicLogTransportKernel_measurable (n : ℕ) {K : ℝ≥0} {v : PeriodicTorus ι → E}
    (hv : LipschitzWith K v) : Measurable (periodicLogTransportKernel (ι := ι) n v) := by
  let U : Set (E × E) := (periodicOffLattice : Set E) ×ˢ (univ : Set E)
  let H : E × E → ℝ := fun q => iteratedFDeriv ℝ n (periodicLogSmooth (ι := ι)) q.1 (fun _ => q.2)
  have heval : Continuous (fun q : (E [×n]→L[ℝ] ℝ) × (Fin n → E) => q.1 q.2) :=
    (ContinuousLinearMap.id ℝ (E [×n]→L[ℝ] ℝ)).continuous_uncurry_of_multilinear
  have hH : ContinuousOn H U := by
    have h1 : ContinuousOn (fun q : E × E => (iteratedFDeriv ℝ n (periodicLogSmooth (ι := ι)) q.1,
        (fun _ : Fin n => q.2))) U :=
      ((continuousOn_periodicLogSmooth_iteratedFDeriv (ι := ι) n).comp continuousOn_fst
        (fun q hq => hq.1)).prodMk (continuous_pi (fun _ => continuous_snd)).continuousOn
    exact heval.comp_continuousOn h1
  have hU : MeasurableSet U := isOpen_periodicOffLattice.measurableSet.prod MeasurableSet.univ
  have hmeas : Measurable (U.piecewise H (fun _ => (0 : ℝ))) :=
    hH.measurable_piecewise continuousOn_const hU
  have hq : Measurable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      (periodicCenteredLift (p.1 - p.2), v p.1 - v p.2)) :=
    (measurable_periodicCenteredLift.comp (measurable_fst.sub measurable_snd)).prodMk
      ((hv.continuous.measurable.comp measurable_fst).sub (hv.continuous.measurable.comp measurable_snd))
  have heq : periodicLogTransportKernel (ι := ι) n v = fun p =>
      U.piecewise H (fun _ => (0 : ℝ)) (periodicCenteredLift (p.1 - p.2), v p.1 - v p.2) := by
    funext p
    by_cases hp : p.1 = p.2
    · have h0 : (periodicCenteredLift (p.1 - p.2), v p.1 - v p.2) ∉ U := by
        intro h
        have := h.1 0
        simp [hp, periodicCenteredLift_zero] at this
      rw [Set.piecewise_eq_of_notMem _ _ _ h0]
      simp only [periodicLogTransportKernel, ite_eq_left hp]
    · have h1 : (periodicCenteredLift (p.1 - p.2), v p.1 - v p.2) ∈ U :=
        ⟨periodicCenteredLift_mem_offLattice (sub_ne_zero.mpr hp), mem_univ _⟩
      rw [Set.piecewise_eq_of_mem _ _ _ h1]
      simp only [periodicLogTransportKernel, ite_eq_right hp, H]
  rw [heq]
  exact hmeas.comp hq

end DGRHS.Periodic
