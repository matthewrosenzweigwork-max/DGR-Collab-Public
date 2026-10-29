import DGRHS.Gaussian.PeriodicRieszNearField

/-!
Packet P9h, unit 2 (part 18): measurability and symmetry of the torus Riesz pair kernels
(full, short, long) and transport kernels (short, long).
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma measurable_periodicCenteredLift : Measurable (periodicCenteredLift : PeriodicTorus ι → E) := by
  unfold periodicCenteredLift
  have h : Measurable (fun z : PeriodicTorus ι => (fun i => circleCentered (z i) : ι → ℝ)) :=
    measurable_pi_iff.2 (fun i => measurable_circleCentered.comp (measurable_pi_apply i))
  exact (WithLp.measurable_toLp 2 (ι → ℝ)).comp h

lemma measurable_periodicProfile (c s : ℝ) (S : Set ℝ) : Measurable (periodicProfile c s S : E → ℝ) := by
  unfold periodicProfile
  refine Measurable.const_mul ?_ c
  have hm : Measurable (fun q : E × ℝ => q.2 ^ (-s - 1) * sourceRieszGaussianScale q.2 q.1) := by
    unfold sourceRieszGaussianScale
    fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict S)).measurable

lemma measurable_periodicProfileSum (c s : ℝ) (S : Set ℝ) :
    Measurable (periodicProfileSum c s S : E → ℝ) := by
  unfold periodicProfileSum
  exact Measurable.tsum fun m => (measurable_periodicProfile c s S).comp (measurable_id.add_const _)

lemma measurable_periodicRieszShortFun (s η : ℝ) :
    Measurable (periodicRieszShortFun (ι := ι) s η) := by
  unfold periodicRieszShortFun periodicRieszShortSum
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  exact (measurable_periodicProfileSum _ s _).comp measurable_periodicCenteredLift

lemma measurable_periodicRieszShortPair (s η : ℝ) :
    Measurable (periodicRieszShortPair (ι := ι) s η) := by
  have : periodicRieszShortPair (ι := ι) s η = fun p => periodicRieszShortFun s η (p.1 - p.2) :=
    funext (periodicRieszShortPair_eq s η)
  rw [this]
  exact (measurable_periodicRieszShortFun s η).comp (measurable_fst.sub measurable_snd)

lemma periodicRieszShortSum_add_lattice (s η : ℝ) (z : E) (m : PeriodicFrequency ι) :
    periodicRieszShortSum s η (z + periodicFrequencyVector m) = periodicRieszShortSum s η z :=
  periodicProfileSum_add_lattice _ s _ z m

lemma periodicRieszShortSum_neg (s η : ℝ) (z : E) :
    periodicRieszShortSum s η (-z) = periodicRieszShortSum s η z := periodicProfileSum_neg _ s _ z

/-- A pair kernel built from an even lattice-periodic function is symmetric. -/
lemma pair_symm_of_even_periodic (f : E → ℝ) (hev : ∀ z, f (-z) = f z)
    (hper : ∀ (z : E) (m : PeriodicFrequency ι), f (z + periodicFrequencyVector m) = f z)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    (if p.swap.1 = p.swap.2 then 0 else f (periodicCenteredLift (p.swap.1 - p.swap.2))) =
      (if p.1 = p.2 then 0 else f (periodicCenteredLift (p.1 - p.2))) := by
  by_cases hp : p.1 = p.2
  · simp [hp]
  have hp' : p.2 ≠ p.1 := Ne.symm hp
  simp only [Prod.fst_swap, Prod.snd_swap, ite_eq_right hp, ite_eq_right hp']
  obtain ⟨m, hm⟩ := exists_centeredLift_neg (p.1 - p.2)
  have hsub : p.2 - p.1 = -(p.1 - p.2) := by abel
  rw [hsub, hm, hper, hev]

lemma periodicRieszPair_symm (s : ℝ) (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicRieszPair s p.swap = periodicRieszPair s p :=
  pair_symm_of_even_periodic (periodicRieszSmooth s) (periodicRieszSmooth_neg s)
    (periodicRieszSmooth_add_lattice s) p

lemma periodicRieszShortPair_symm (s η : ℝ) (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicRieszShortPair s η p.swap = periodicRieszShortPair s η p :=
  pair_symm_of_even_periodic (periodicRieszShortSum s η) (periodicRieszShortSum_neg s η)
    (periodicRieszShortSum_add_lattice s η) p


lemma periodicFrequencyVector_add' (a b : PeriodicFrequency ι) :
    periodicFrequencyVector (a + b) = periodicFrequencyVector a + periodicFrequencyVector b := by
  ext i; simp

lemma periodicFrequencyVector_neg' (a : PeriodicFrequency ι) :
    periodicFrequencyVector (-a) = -periodicFrequencyVector a := by
  ext i; simp

lemma periodicFrequencyVector_sub' (a b : PeriodicFrequency ι) :
    periodicFrequencyVector (a - b) = periodicFrequencyVector a - periodicFrequencyVector b := by
  ext i; simp

/-- The evaluated derivative `(a, w) ↦ D^n f(a)(w, …, w)` of a profile is measurable. -/
lemma measurable_periodicProfileDerivEval (n : ℕ) (c s : ℝ) (S : Set ℝ) (hSm : MeasurableSet S)
    (hS : S ⊆ Ioi 0) (hs : 0 < s) :
    Measurable (fun q : E × E => iteratedFDeriv ℝ n (periodicProfile c s S) q.1 (fun _ => q.2)) := by
  let f : E × E → ℝ := fun q => iteratedFDeriv ℝ n (periodicProfile c s S) q.1 (fun _ => q.2)
  have heval : Continuous (fun q : (E [×n]→L[ℝ] ℝ) × (Fin n → E) => q.1 q.2) :=
    (ContinuousLinearMap.id ℝ (E [×n]→L[ℝ] ℝ)).continuous_uncurry_of_multilinear
  let U : Set (E × E) := {q | q.1 ≠ 0}
  have hUm : MeasurableSet U := (isClosed_singleton.measurableSet.preimage measurable_fst).compl
  have hf1 : ContinuousOn f U := by
    intro q hq
    have hq' : q.1 ≠ 0 := hq
    have hd : ContinuousAt (iteratedFDeriv ℝ n (periodicProfile c s S)) q.1 :=
      (periodicProfile_differentiableAt_iteratedFDeriv c s S hSm hS hs n hq').continuousAt
    have hw : ContinuousAt (fun q : E × E => fun _ : Fin n => q.2) q :=
      (continuous_pi (fun _ => continuous_snd)).continuousAt
    exact ((heval.continuousAt.comp ((hd.comp continuous_fst.continuousAt).prodMk hw)).continuousWithinAt)
  have hf2 : ContinuousOn f Uᶜ := by
    have hc : Continuous (fun q : E × E => iteratedFDeriv ℝ n (periodicProfile c s S) 0 (fun _ => q.2)) :=
      heval.comp (continuous_const.prodMk (continuous_pi (fun _ => continuous_snd)))
    refine hc.continuousOn.congr (fun q hq => ?_)
    have : q.1 = 0 := by simpa [U] using hq
    simp [f, this]
  have := hf1.measurable_piecewise hf2 hUm
  simpa using this

/-- Measurability of the short transport kernel. -/
lemma measurable_periodicRieszShortTransport (n : ℕ) (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) :
    Measurable (periodicRieszShortTransport (ι := ι) n s η v) := by
  unfold periodicRieszShortTransport
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  refine Measurable.tsum fun m => ?_
  have hF := measurable_periodicProfileDerivEval (ι := ι) n (periodicRieszSmoothCoeff ι s) s (Ioc 0 η)
    measurableSet_Ioc (fun t ht => ht.1) hs
  exact hF.comp (((measurable_periodicCenteredLift.comp (measurable_fst.sub measurable_snd)).add_const _).prodMk
    ((hv.continuous.measurable.comp measurable_fst).sub (hv.continuous.measurable.comp measurable_snd)))


lemma measurable_periodicLongDerivEval (n : ℕ) (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    Measurable (fun q : E × E => iteratedFDeriv ℝ n
      (periodicRieszLongKernel (ι := ι) s (periodicHeatCut periodicRieszTau)) q.1 (fun _ => q.2)) := by
  have heval : Continuous (fun q : (E [×n]→L[ℝ] ℝ) × (Fin n → E) => q.1 q.2) :=
    (ContinuousLinearMap.id ℝ (E [×n]→L[ℝ] ℝ)).continuous_uncurry_of_multilinear
  have hd : Continuous (iteratedFDeriv ℝ n
      (periodicRieszLongKernel (ι := ι) s (periodicHeatCut periodicRieszTau))) :=
    (contDiff_periodicRieszLongKernel s _ hs hs2 (periodicHeatCut_pos periodicRieszTau_pos) n).continuous_iteratedFDeriv
      le_rfl
  exact (heval.comp ((hd.comp continuous_fst).prodMk (continuous_pi (fun _ => continuous_snd)))).measurable

lemma measurable_periodicRieszLongTransport (n : ℕ) (s η : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η)
    {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) :
    Measurable (periodicRieszLongTransport (ι := ι) n s η v) := by
  unfold periodicRieszLongTransport
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  have hmaps : ∀ m : PeriodicFrequency ι, Measurable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      (periodicCenteredLift (p.1 - p.2) + periodicFrequencyVector m, v p.1 - v p.2)) := fun m =>
    ((measurable_periodicCenteredLift.comp (measurable_fst.sub measurable_snd)).add_const _).prodMk
      ((hv.continuous.measurable.comp measurable_fst).sub (hv.continuous.measurable.comp measurable_snd))
  refine Measurable.add (Measurable.tsum fun m => ?_) ?_
  · have hF := measurable_periodicProfileDerivEval (ι := ι) n (periodicRieszSmoothCoeff ι s) s
      (Ioc η periodicRieszTau) measurableSet_Ioc (fun t ht => lt_of_lt_of_le hη ht.1.le) hs
    exact hF.comp (hmaps m)
  · have hL := measurable_periodicLongDerivEval (ι := ι) n s hs hs2
    exact hL.comp (((measurable_periodicCenteredLift.comp (measurable_fst.sub measurable_snd))).prodMk
      ((hv.continuous.measurable.comp measurable_fst).sub (hv.continuous.measurable.comp measurable_snd)))

lemma measurable_periodicRieszLongPair (s η : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) :
    Measurable (periodicRieszLongPair (ι := ι) s η) := by
  unfold periodicRieszLongPair
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  have hc := measurable_periodicCenteredLift.comp (measurable_fst.sub measurable_snd :
    Measurable fun p : PeriodicTorus ι × PeriodicTorus ι => p.1 - p.2)
  refine Measurable.sub (Measurable.add ((measurable_periodicProfileSum _ s _).comp hc) ?_) measurable_const
  exact (contDiff_periodicRieszLongKernel (ι := ι) s _ hs hs2 (periodicHeatCut_pos periodicRieszTau_pos)
    0).continuous.measurable.comp hc


lemma periodicRieszShortTransport_symm (n : ℕ) (s η : ℝ) (v : PeriodicTorus ι → E)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicRieszShortTransport n s η v p.swap = periodicRieszShortTransport n s η v p := by
  by_cases hp : p.1 = p.2
  · simp [periodicRieszShortTransport, hp]
  have hp' : p.2 ≠ p.1 := Ne.symm hp
  simp only [periodicRieszShortTransport, Prod.fst_swap, Prod.snd_swap, ite_eq_right hp, ite_eq_right hp']
  obtain ⟨m0, hm0⟩ := exists_centeredLift_neg (p.1 - p.2)
  have hsub : p.2 - p.1 = -(p.1 - p.2) := by abel
  set z := periodicCenteredLift (p.1 - p.2) with hz
  set w := v p.1 - v p.2 with hw
  have hP : ∀ u : E, periodicProfile (periodicRieszSmoothCoeff ι s) s (Ioc 0 η) (-u) =
      periodicProfile (periodicRieszSmoothCoeff ι s) s (Ioc 0 η) u := fun u => periodicProfile_neg _ s _ u
  have hneg : (fun _ : Fin n => v p.2 - v p.1) = fun _ => -w := by funext i; simp [hw]
  have h1 : ∀ m : PeriodicFrequency ι,
      iteratedFDeriv ℝ n (periodicProfile (periodicRieszSmoothCoeff ι s) s (Ioc 0 η))
        (periodicCenteredLift (-(p.1 - p.2)) + periodicFrequencyVector m) (fun _ => -w) =
      iteratedFDeriv ℝ n (periodicProfile (periodicRieszSmoothCoeff ι s) s (Ioc 0 η))
        (z + periodicFrequencyVector ((Equiv.subLeft (-m0)) m)) (fun _ => w) := by
    intro m
    have e1 : periodicCenteredLift (-(p.1 - p.2)) + periodicFrequencyVector m =
        -(z + periodicFrequencyVector ((Equiv.subLeft (-m0)) m)) := by
      rw [hm0]
      simp only [Equiv.subLeft_apply, periodicFrequencyVector_sub', periodicFrequencyVector_neg']
      abel
    rw [e1]
    exact iteratedFDeriv_neg_apply_neg (f := periodicProfile (periodicRieszSmoothCoeff ι s) s (Ioc 0 η)) hP n _
      (fun _ => w)
  rw [hsub, hneg]
  rw [tsum_congr h1]
  exact (Equiv.subLeft (-m0)).tsum_eq (fun m => iteratedFDeriv ℝ n
    (periodicProfile (periodicRieszSmoothCoeff ι s) s (Ioc 0 η)) (z + periodicFrequencyVector m) (fun _ => w))

lemma periodicRieszLongTransport_eq_sub (n : ℕ) (hn : 1 ≤ n) (s η : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hητ : η ≤ periodicRieszTau)
    (v : PeriodicTorus ι → E) (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicRieszLongTransport n s η v p =
      periodicRieszTransportKernel n s v p - periodicRieszShortTransport n s η v p := by
  rw [periodicRieszTransportKernel_split n hn s η hs hs2 hη hητ v p]
  ring

lemma periodicRieszTransportKernel_measurable (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) :
    Measurable (periodicRieszTransportKernel (ι := ι) n s v) := by
  have h : periodicRieszTransportKernel (ι := ι) n s v = fun p => periodicRieszShortTransport n s periodicRieszTau v p +
      periodicRieszLongTransport n s periodicRieszTau v p :=
    funext (periodicRieszTransportKernel_split n hn s periodicRieszTau hs hs2 periodicRieszTau_pos le_rfl v)
  rw [h]
  exact (measurable_periodicRieszShortTransport n s _ hs periodicRieszTau_pos hv).add
    (measurable_periodicRieszLongTransport n s _ hs hs2 periodicRieszTau_pos hv)

lemma periodicRieszLongTransport_symm (n : ℕ) (hn : 1 ≤ n) (s η : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hητ : η ≤ periodicRieszTau)
    (v : PeriodicTorus ι → E) (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicRieszLongTransport n s η v p.swap = periodicRieszLongTransport n s η v p := by
  rw [periodicRieszLongTransport_eq_sub n hn s η hs hs2 hη hητ, periodicRieszLongTransport_eq_sub n hn s η hs hs2 hη hητ,
    periodicRieszTransportKernel_symm, periodicRieszShortTransport_symm]


lemma periodicRieszLongPair_symm (s η : ℝ) (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicRieszLongPair s η p.swap = periodicRieszLongPair s η p := by
  have h := pair_symm_of_even_periodic (ι := ι)
    (fun z => periodicProfileSum (periodicRieszSmoothCoeff ι s) s (Ioc η periodicRieszTau) z +
      periodicRieszLongKernel s (periodicHeatCut periodicRieszTau) z -
      periodicRieszMellinFactor ι s * (periodicHeatCut periodicRieszTau) ^ (((Fintype.card ι : ℝ) - s) / 2) /
        (((Fintype.card ι : ℝ) - s) / 2))
    (fun z => by simp only [periodicProfileSum_neg, periodicRieszLongKernel_neg])
    (fun z m => by simp only [periodicProfileSum_add_lattice, periodicRieszLongKernel_add_lattice]) p
  exact h

lemma measurable_periodicRieszPair (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    Measurable (periodicRieszPair (ι := ι) s) := by
  have h : periodicRieszPair (ι := ι) s = fun p => periodicRieszShortPair s periodicRieszTau p +
      periodicRieszLongPair s periodicRieszTau p :=
    funext (periodicRieszPair_split s periodicRieszTau hs periodicRieszTau_pos le_rfl)
  rw [h]
  exact (measurable_periodicRieszShortPair s _).add
    (measurable_periodicRieszLongPair s _ hs hs2 periodicRieszTau_pos)

end DGRHS.Periodic
