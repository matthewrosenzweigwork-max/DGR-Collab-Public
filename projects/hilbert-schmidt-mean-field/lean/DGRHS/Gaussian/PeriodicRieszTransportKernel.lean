import DGRHS.Gaussian.PeriodicRieszSmoothSymmetry

/-!
Packet P9h, unit 2 (part 11): the transport kernel `∇^n g(x - y) : (v(x) - v(y))^{⊗n}` of Theorem 2.8
for the periodic Riesz kernel on the torus `𝕋^d` (Remark 2.1), with `g` the canonical smooth
representative `periodicRieszSmoothLift s (1/2)` (almost everywhere equal to the spectral kernel,
`periodicRieszSmoothLift_ae`) and `v : 𝕋^d → ℝ^d` a transport field.  The derivative is the actual
`iteratedFDeriv` of the smooth lift at the centered lift of `x - y` (the lift is lattice periodic, so
the choice of lift is immaterial); collisions are totalized to `0`.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The fixed short scale (heat cut `2π²/4`) of the smooth representative of the Riesz kernel. -/
def periodicRieszTau : ℝ := 1 / 2

lemma periodicRieszTau_pos : 0 < periodicRieszTau := by unfold periodicRieszTau; norm_num

/-- The canonical smooth lift of the periodic Riesz kernel to `ℝ^d`. -/
def periodicRieszSmooth (s : ℝ) : E → ℝ := periodicRieszSmoothLift s periodicRieszTau

/-- The transport kernel of Theorem 2.8 on the torus. -/
def periodicRieszTransportKernel (n : ℕ) (s : ℝ) (v : PeriodicTorus ι → E)
    (p : PeriodicTorus ι × PeriodicTorus ι) : ℝ :=
  if p.1 = p.2 then 0 else
    iteratedFDeriv ℝ n (periodicRieszSmooth s) (periodicCenteredLift (p.1 - p.2))
      (fun _ => v p.1 - v p.2)

lemma periodicRieszSmooth_neg (s : ℝ) (z : E) : periodicRieszSmooth s (-z) = periodicRieszSmooth s z :=
  periodicRieszSmoothLift_neg s _ z

lemma periodicRieszSmooth_add_lattice (s : ℝ) (z : E) (m : PeriodicFrequency ι) :
    periodicRieszSmooth s (z + periodicFrequencyVector m) = periodicRieszSmooth s z :=
  periodicRieszSmoothLift_add_lattice s _ z m

lemma periodicCenteredLift_mem_offLattice {x : PeriodicTorus ι} (hx : x ≠ 0) :
    periodicCenteredLift x ∈ (periodicOffLattice : Set E) := by
  intro m hm
  apply hx
  have := congrArg periodicLift hm
  rwa [periodicLift_add_lattice, periodicLift_centeredLift, periodicLift_zero] at this

lemma exists_centeredLift_neg (z : PeriodicTorus ι) :
    ∃ m : PeriodicFrequency ι, periodicCenteredLift (-z) = -periodicCenteredLift z + periodicFrequencyVector m := by
  have h : ∀ i, ∃ n : ℤ, periodicCenteredLift (-z) i + periodicCenteredLift z i = (n : ℝ) := by
    intro i
    have h1 : (((periodicCenteredLift (-z) i + periodicCenteredLift z i : ℝ)) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_add]
      simp only [periodicCenteredLift_apply, circleCentered_coe, Pi.neg_apply]
      abel
    rw [AddCircle.coe_eq_zero_iff] at h1
    obtain ⟨n, hn⟩ := h1
    exact ⟨n, by simpa using hn.symm⟩
  choose m hm using h
  refine ⟨m, ?_⟩
  ext i
  simp only [PiLp.add_apply, PiLp.neg_apply, periodicFrequencyVector_apply]
  linarith [hm i]

lemma periodicRieszTransportKernel_symm (n : ℕ) (s : ℝ) (v : PeriodicTorus ι → E)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicRieszTransportKernel n s v p.swap = periodicRieszTransportKernel n s v p := by
  by_cases hp : p.1 = p.2
  · simp [periodicRieszTransportKernel, hp]
  have hp' : p.2 ≠ p.1 := Ne.symm hp
  simp only [periodicRieszTransportKernel, Prod.fst_swap, Prod.snd_swap, ite_eq_right hp, ite_eq_right hp']
  obtain ⟨m, hm⟩ := exists_centeredLift_neg (p.1 - p.2)
  have hsub : p.2 - p.1 = -(p.1 - p.2) := by abel
  rw [hsub, hm]
  have hper : ∀ z (m : PeriodicFrequency ι),
      periodicRieszSmooth s (z + periodicFrequencyVector m) = periodicRieszSmooth s z :=
    fun z m => periodicRieszSmooth_add_lattice s z m
  rw [iteratedFDeriv_add_lattice hper]
  have h := iteratedFDeriv_neg_apply_neg (periodicRieszSmooth_neg s) n (periodicCenteredLift (p.1 - p.2))
    (fun _ => v p.1 - v p.2)
  have hneg : (fun _ : Fin n => v p.2 - v p.1) = fun _ => -(v p.1 - v p.2) := by
    funext i; abel
  rw [hneg]
  exact h

end DGRHS.Periodic
