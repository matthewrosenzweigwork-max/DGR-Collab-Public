import SharpSymmetricLSI.Defs.D08_Gibbs
import DGPS.SingularCounterexample.BarrierKernel
import DGPS.SingularCounterexample.Cutoff
import DGPS.SingularCounterexample.BarrierGeometry
import DGPS.SingularCounterexample.Interfaces
import DGPS.SingularCounterexample.Particle.WellPosed
import DGPS.SingularCounterexample.Particle.TestFunction
import Mathlib.Probability.Independence.InfinitePi

/-! Pairwise lower bounds for the frozen ordered-pair Hamiltonian. -/

namespace DGPS.SingularCounterexample

open MeasureTheory
open ProbabilityTheory

private theorem pairDifference_measurePreserving {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    MeasurePreserving (fun X : SharpLSI.Config N 1 => X i - X j) volume (haar 1) := by
  have hpair : MeasurePreserving (fun X : SharpLSI.Config N 1 => (X i, X j)) volume
      ((haar 1).prod (haar 1)) := by
    refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
    change (Measure.pi (fun _ : Fin N => haar 1)).map (fun X => (X i, X j)) = _
    have hind := iIndepFun_pi (μ := fun _ : Fin N => haar 1)
      (X := fun _ => id) (fun _ => aemeasurable_id)
    have hm := (indepFun_iff_map_prod_eq_prod_map_map
      (μ := Measure.pi (fun _ : Fin N => haar 1))
      (f := fun X => X i) (g := fun X => X j)
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable).mp
      (hind.indepFun hij)
    rw [hm, (measurePreserving_eval (fun _ : Fin N => haar 1) i).map_eq,
      (measurePreserving_eval (fun _ : Fin N => haar 1) j).map_eq]
  exact MeasureTheory.measurePreserving_fst.comp
    ((MeasureTheory.measurePreserving_sub_prod (haar 1) (haar 1)).comp hpair)

private theorem cutoffLine_deriv_periodic_local (n : ℕ) (t : ℝ) :
    deriv (cutoffLine n) (t + 1) = deriv (cutoffLine n) t := by
  have hfun : (fun s : ℝ => cutoffLine n (s + 1)) = cutoffLine n := by
    funext s
    exact cutoffLine_periodic n s
  have hEq := congrArg (fun f : ℝ → ℝ => deriv f t) hfun
  have hlineDiff : DifferentiableAt ℝ (cutoffLine n) (t + 1) :=
    (cutoffLine_contDiff n).contDiffAt.differentiableAt (by norm_num)
  have hargDiff : DifferentiableAt ℝ (fun s : ℝ => s + 1) t := by fun_prop
  have hcomp : deriv (fun s : ℝ => cutoffLine n (s + 1)) t =
      deriv (cutoffLine n) (t + 1) := by
    change deriv ((cutoffLine n) ∘ (fun s : ℝ => s + 1)) t = _
    rw [deriv_comp t hlineDiff hargDiff, deriv_add_const 1]
    have hId : deriv (fun s : ℝ => s) t = 1 := by
      change deriv id t = 1
      exact deriv_id t
    rw [hId]
    ring
  exact hcomp.symm.trans hEq

private theorem cutoffLine_deriv_periodic_function (n : ℕ) :
    Function.Periodic (deriv (cutoffLine n)) 1 :=
  cutoffLine_deriv_periodic_local n

private theorem cutoffLine_deriv_section_sub (n : ℕ) (x y : Circle) :
    deriv (cutoffLine n) (SharpLSI.secT x 0 - SharpLSI.secT y 0) =
      deriv (cutoffLine n) (SharpLSI.secT (x - y) 0) := by
  let t := SharpLSI.secT x 0 - SharpLSI.secT y 0
  let s := SharpLSI.secT (x - y) 0
  have ht : ((t : ℝ) : AddCircle (1 : ℝ)) = (x - y) 0 := by
    have hpoint : torusPoint t = x - y := by
      ext k
      fin_cases k
      change ((SharpLSI.secT x 0 - SharpLSI.secT y 0 : ℝ) : AddCircle (1 : ℝ)) = _
      rw [AddCircle.coe_sub]
      have hx := congrFun (SharpLSI.liftT_secT x) 0
      have hy := congrFun (SharpLSI.liftT_secT y) 0
      change ((SharpLSI.secT x 0 : ℝ) : AddCircle (1 : ℝ)) = x 0 at hx
      change ((SharpLSI.secT y 0 : ℝ) : AddCircle (1 : ℝ)) = y 0 at hy
      rw [hx, hy]
      simp
    exact congrFun hpoint 0
  have hs : ((s : ℝ) : AddCircle (1 : ℝ)) = (x - y) 0 := by
    have h := congrFun (SharpLSI.liftT_secT (x - y)) 0
    change ((SharpLSI.secT (x - y) 0 : ℝ) : AddCircle (1 : ℝ)) = (x - y) 0 at h
    exact h
  have hts : ((t - s : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, ht, hs, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 hts
  have hrel : t = s + (k : ℝ) := by
    simp at hk
    dsimp [t, s]
    linarith
  have hperiod := (cutoffLine_deriv_periodic_function n).int_mul k
  have hperiod' : deriv (cutoffLine n) (s + (k : ℝ)) = deriv (cutoffLine n) s := by
    simpa using hperiod s
  change deriv (cutoffLine n) t = deriv (cutoffLine n) s
  rw [hrel, hperiod']

private theorem cutoffLine_deriv_sq_haar_bound (n : ℕ) (C : ℝ)
    (hI : (∫ t in Set.Ioc (0 : ℝ) 1, |deriv (cutoffLine n) t| ^ 2 ∂volume) ≤
      96 * C ^ 2 / width n) :
    (∫ x : Circle, (deriv (cutoffLine n) (SharpLSI.secT x 0)) ^ 2 ∂haar 1) ≤
      96 * C ^ 2 / width n := by
  let f : Circle → ℝ := fun x => (deriv (cutoffLine n) (SharpLSI.secT x 0)) ^ 2
  have hderivCont : Continuous (deriv (cutoffLine n)) :=
    (cutoffLine_contDiff n).continuous_deriv (by norm_num)
  have hf : Measurable f := by
    dsimp [f]
    exact (hderivCont.measurable.comp
      ((measurable_pi_apply 0).comp SharpLSI.measurable_secT)).pow_const 2
  have hUnit : MeasurableSet (SharpLSI.unitBox (Fin 1)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  have hI' : (∫ t in Set.Ioc (0 : ℝ) 1, (deriv (cutoffLine n) t) ^ 2 ∂volume) ≤
      96 * C ^ 2 / width n := by
    simpa using hI
  calc
    (∫ x : Circle, f x ∂haar 1) =
        ∫ y, f (SharpLSI.liftT y)
          ∂(volume : Measure (Fin 1 → ℝ)).restrict (SharpLSI.unitBox (Fin 1)) := by
      rw [DGPS.haar_eq_map_unitBox 1]
      exact integral_map SharpLSI.measurable_liftT.aemeasurable hf.aestronglyMeasurable
    _ = ∫ y, (deriv (cutoffLine n) (y 0)) ^ 2
        ∂(volume : Measure (Fin 1 → ℝ)).restrict (SharpLSI.unitBox (Fin 1)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hUnit] with y hy
      have hsec := congrFun (SharpLSI.secT_liftT hy) 0
      simp [f, hsec]
    _ = ∫ t in Set.Ioc (0 : ℝ) 1, (deriv (cutoffLine n) t) ^ 2 ∂volume := by
      rw [SharpLSI.volume_restrict_unitBox]
      simpa using (integral_fintype_prod_eq_prod
        (μ := fun _ : Fin 1 => (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))
        (f := fun _ : Fin 1 => fun t : ℝ => (deriv (cutoffLine n) t) ^ 2))
    _ ≤ 96 * C ^ 2 / width n := hI'

private theorem pair_deriv_sq_integral_bound {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    (n : ℕ) (C : ℝ)
    (hI : (∫ t in Set.Ioc (0 : ℝ) 1, |deriv (cutoffLine n) t| ^ 2 ∂volume) ≤
      96 * C ^ 2 / width n) :
    (∫ X : SharpLSI.Config N 1,
      (deriv (cutoffLine n) (SharpLSI.secT (X i - X j) 0)) ^ 2 ∂volume) ≤
      96 * C ^ 2 / width n := by
  let f : Circle → ℝ := fun x => (deriv (cutoffLine n) (SharpLSI.secT x 0)) ^ 2
  let d : SharpLSI.Config N 1 → Circle := fun X => X i - X j
  have hderivCont : Continuous (deriv (cutoffLine n)) :=
    (cutoffLine_contDiff n).continuous_deriv (by norm_num)
  have hf : Measurable f := by
    dsimp [f]
    exact (hderivCont.measurable.comp
      ((measurable_pi_apply 0).comp SharpLSI.measurable_secT)).pow_const 2
  have hmp := pairDifference_measurePreserving hij
  have hfae : AEStronglyMeasurable f (volume.map d) := by
    rw [hmp.map_eq]
    exact hf.aestronglyMeasurable
  have hmap : (∫ X, f (d X) ∂volume) = ∫ x, f x ∂haar 1 := by
    calc
      (∫ X, f (d X) ∂volume) = ∫ x, f x ∂(volume.map d) :=
        (integral_map hmp.measurable.aemeasurable hfae).symm
      _ = ∫ x, f x ∂haar 1 := by rw [hmp.map_eq]
  simpa [f, d] using hmap.trans_le (cutoffLine_deriv_sq_haar_bound n C hI)

private noncomputable def pairDerivativeSqOnConfig {N : ℕ} (n : ℕ)
    (X : SharpLSI.Config N 1) (i j : Fin N) : ℝ :=
  if i = j then 0 else (deriv (cutoffLine n) (SharpLSI.secT (X i - X j) 0)) ^ 2

private noncomputable def particleTestPairDerivativeSqOnConfig {N : ℕ} (n : ℕ)
    (X : SharpLSI.Config N 1) : ℝ :=
  ∑ i, ∑ j, pairDerivativeSqOnConfig n X i j

private theorem particleTestPairDerivativeSq_flat_eq {N : ℕ} (n : ℕ)
    (X : SharpLSI.Config N 1) :
    particleTestPairDerivativeSq n (SharpLSI.flat X) =
      particleTestPairDerivativeSqOnConfig n X := by
  unfold particleTestPairDerivativeSq particleTestPairDerivativeSqOnConfig
    pairDerivativeSqOnConfig
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · simp only [if_neg hij]
    have hi : SharpLSI.secT (SharpLSI.flat X) (i, 0) = SharpLSI.secT (X i) 0 := rfl
    have hj : SharpLSI.secT (SharpLSI.flat X) (j, 0) = SharpLSI.secT (X j) 0 := rfl
    rw [hi, hj, cutoffLine_deriv_section_sub]

private theorem pairDerivativeSqOnConfig_integrable {N : ℕ} (n : ℕ)
    (i j : Fin N) :
    Integrable (fun X : SharpLSI.Config N 1 => pairDerivativeSqOnConfig n X i j) volume := by
  obtain ⟨D, hD0, hD⟩ := cutoffLine_deriv_bounded_global n
  by_cases hij : i = j
  · simp [pairDerivativeSqOnConfig, hij]
  · have hmeas : Measurable (fun X : SharpLSI.Config N 1 =>
        (deriv (cutoffLine n) (SharpLSI.secT (X i - X j) 0)) ^ 2) := by
      have hdiff : Measurable (fun X : SharpLSI.Config N 1 => X i - X j) :=
        (measurable_pi_apply i).sub (measurable_pi_apply j)
      have hsec : Measurable (fun X : SharpLSI.Config N 1 =>
          SharpLSI.secT (X i - X j) 0) :=
        (measurable_pi_apply 0).comp (SharpLSI.measurable_secT.comp hdiff)
      have hderivCont : Continuous (deriv (cutoffLine n)) :=
        (cutoffLine_contDiff n).continuous_deriv (by norm_num)
      exact (hderivCont.measurable.comp hsec).pow_const 2
    simp only [pairDerivativeSqOnConfig, if_neg hij]
    refine Integrable.of_bound hmeas.aestronglyMeasurable (D ^ 2)
      (Filter.Eventually.of_forall fun X => ?_)
    calc
      ‖(deriv (cutoffLine n) (SharpLSI.secT (X i - X j) 0)) ^ 2‖ =
          (deriv (cutoffLine n) (SharpLSI.secT (X i - X j) 0)) ^ 2 := by
            rw [Real.norm_eq_abs]
            exact abs_of_nonneg (sq_nonneg _)
      _ = |deriv (cutoffLine n) (SharpLSI.secT (X i - X j) 0)| ^ 2 := by
            rw [sq_abs]
      _ ≤ D ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hD _) 2

private theorem particleTestPairDerivativeSqOnConfig_integrable {N : ℕ} (n : ℕ) :
    Integrable (particleTestPairDerivativeSqOnConfig n : SharpLSI.Config N 1 → ℝ) volume := by
  unfold particleTestPairDerivativeSqOnConfig
  exact integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => pairDerivativeSqOnConfig_integrable n i j

private theorem particleTestPairDerivativeSqOnConfig_integral_bound {N : ℕ} (n : ℕ)
    (C : ℝ)
    (hI : ∀ n, (∫ t in Set.Ioc (0 : ℝ) 1, |deriv (cutoffLine n) t| ^ 2 ∂volume) ≤
      96 * C ^ 2 / width n) :
    (∫ X : SharpLSI.Config N 1, particleTestPairDerivativeSqOnConfig n X ∂volume) ≤
      (N : ℝ) ^ 2 * (96 * C ^ 2 / width n) := by
  let Bnd : ℝ := 96 * C ^ 2 / width n
  have hBnd : 0 ≤ Bnd := by
    dsimp [Bnd]
    exact div_nonneg (by positivity) (width_pos n).le
  have htermInt (i j : Fin N) :
      Integrable (fun X : SharpLSI.Config N 1 => pairDerivativeSqOnConfig n X i j) volume :=
    pairDerivativeSqOnConfig_integrable n i j
  have htermBound (i j : Fin N) :
      (∫ X : SharpLSI.Config N 1, pairDerivativeSqOnConfig n X i j ∂volume) ≤ Bnd := by
    by_cases hij : i = j
    · simp [pairDerivativeSqOnConfig, hij, Bnd, hBnd]
    · simpa [pairDerivativeSqOnConfig, hij, Bnd] using
        (pair_deriv_sq_integral_bound hij n C (hI n))
  have hsum :
      (∫ X : SharpLSI.Config N 1, particleTestPairDerivativeSqOnConfig n X ∂volume) =
        ∑ i : Fin N, ∑ j : Fin N,
          ∫ X : SharpLSI.Config N 1, pairDerivativeSqOnConfig n X i j ∂volume := by
    simp_rw [particleTestPairDerivativeSqOnConfig]
    rw [integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => htermInt i j]
    simp_rw [integral_finsetSum _ fun j _ => htermInt _ j]
  calc
    (∫ X : SharpLSI.Config N 1, particleTestPairDerivativeSqOnConfig n X ∂volume) =
        ∑ i : Fin N, ∑ j : Fin N,
          ∫ X : SharpLSI.Config N 1, pairDerivativeSqOnConfig n X i j ∂volume := hsum
    _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, Bnd :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => htermBound i j
    _ = (N : ℝ) ^ 2 * Bnd := by
      simp [Bnd, Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
      ring

private theorem particleTestPairDerivativeSqOnConfig_nonneg {N : ℕ} (n : ℕ)
    (X : SharpLSI.Config N 1) : 0 ≤ particleTestPairDerivativeSqOnConfig n X := by
  unfold particleTestPairDerivativeSqOnConfig pairDerivativeSqOnConfig
  positivity

private theorem pairDerivative_measurable {N : ℕ} (n : ℕ) (i j : Fin N) :
    Measurable (fun X : SharpLSI.Config N 1 =>
      deriv (cutoffLine n) (SharpLSI.secT (X i - X j) 0)) := by
  have hdiff : Measurable (fun X : SharpLSI.Config N 1 => X i - X j) :=
    (measurable_pi_apply i).sub (measurable_pi_apply j)
  have hsec : Measurable (fun X : SharpLSI.Config N 1 => SharpLSI.secT (X i - X j) 0) :=
    (measurable_pi_apply 0).comp (SharpLSI.measurable_secT.comp hdiff)
  exact ((cutoffLine_contDiff n).continuous_deriv (by norm_num)).measurable.comp hsec

private def cutoffDerivativeEvent {N : ℕ} (n : ℕ) : Set (SharpLSI.Config N 1) :=
  {X | ∃ i j : Fin N, i ≠ j ∧
    deriv (cutoffLine n) (SharpLSI.secT (X i - X j) 0) ≠ 0}

private theorem cutoffDerivativeEvent_measurable {N : ℕ} (n : ℕ) :
    MeasurableSet (cutoffDerivativeEvent n : Set (SharpLSI.Config N 1)) := by
  classical
  rw [show cutoffDerivativeEvent n = ⋃ i : Fin N, ⋃ j : Fin N,
      {X : SharpLSI.Config N 1 | i ≠ j ∧
        deriv (cutoffLine n) (SharpLSI.secT (X i - X j) 0) ≠ 0} by
    ext X
    simp [cutoffDerivativeEvent]]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j => by
    by_cases hij : i = j
    · simp [hij]
    · have hzero : MeasurableSet
          {X : SharpLSI.Config N 1 | deriv (cutoffLine n)
            (SharpLSI.secT (X i - X j) 0) = 0} :=
        (measurableSet_singleton (0 : ℝ)).preimage (pairDerivative_measurable n i j)
      have hneq : MeasurableSet
          {X : SharpLSI.Config N 1 | deriv (cutoffLine n)
            (SharpLSI.secT (X i - X j) 0) ≠ 0} := by
        change MeasurableSet ({X : SharpLSI.Config N 1 | deriv (cutoffLine n)
          (SharpLSI.secT (X i - X j) 0) = 0}ᶜ)
        exact hzero.compl
      simpa [hij] using hneq

private theorem particleTestPairDerivativeSqOnConfig_zero_of_not_event {N : ℕ}
    (n : ℕ) (X : SharpLSI.Config N 1)
    (hX : X ∉ cutoffDerivativeEvent n) : particleTestPairDerivativeSqOnConfig n X = 0 := by
  have hderiv (i j : Fin N) (hij : i ≠ j) :
      deriv (cutoffLine n) (SharpLSI.secT (X i - X j) 0) = 0 := by
    by_contra hnonzero
    exact hX ⟨i, j, hij, hnonzero⟩
  have hterm (i j : Fin N) : pairDerivativeSqOnConfig n X i j = 0 := by
    by_cases hij : i = j
    · simp [pairDerivativeSqOnConfig, hij]
    · simp [pairDerivativeSqOnConfig, hij, hderiv i j hij]
  simp [particleTestPairDerivativeSqOnConfig, hterm]

/-- If a nonnegative integrand vanishes off `A`, a density bound only on `A` suffices
to dominate its Gibbs integral by its reference-measure integral. -/
theorem lintegral_withDensity_le_of_bound_on_support
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (ρ g : Ω → ENNReal) (A : Set Ω) (M : ENNReal) (hM : M ≠ ⊤)
    (hρ : AEMeasurable ρ μ) (hg : AEMeasurable g μ)
    (hzero : ∀ᵐ x ∂μ, x ∉ A → g x = 0)
    (hbound : ∀ᵐ x ∂μ, x ∈ A → ρ x ≤ M) :
    (∫⁻ x, g x ∂μ.withDensity ρ) ≤ M * ∫⁻ x, g x ∂μ := by
  rw [lintegral_withDensity_eq_lintegral_mul₀ (f := ρ) (g := g) hρ hg]
  calc
    (∫⁻ x, ρ x * g x ∂μ) ≤ ∫⁻ x, M * g x ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hzero, hbound] with x hxzero hxbound
      by_cases hx : x ∈ A
      · exact mul_le_mul_of_nonneg_right (hxbound hx) (by positivity)
      · simp [hxzero hx]
    _ = M * ∫⁻ x, g x ∂μ := lintegral_const_mul' M g hM

/-- On the barrier level set, the perturbation dominates its fixed bounded baseline.
This is the interaction estimate used to turn derivative support into a high-energy pair. -/
theorem pairPotential_lower_bound_of_barrier_lower_bound
    (B : BaselineKernel) {β η c₀ A C : ℝ}
    (hβ : 0 < β) (hη : 0 < η)
    (hB : ∀ x, |B.g x| ≤ C) (x y : Circle)
    (hbar : c₀ * A ≤ barrier (x - y)) :
    β * η * c₀ * A - β * C ≤
      β * (B.g (x - y) + η * barrier (x - y)) := by
  let z := x - y
  have hg : -C ≤ B.g z := (abs_le.mp (hB z)).1
  have hbase : β * (-C) ≤ β * B.g z :=
    mul_le_mul_of_nonneg_left hg hβ.le
  have hbarrier : β * (η * (c₀ * A)) ≤ β * (η * barrier z) := by
    apply mul_le_mul_of_nonneg_left _ hβ.le
    exact mul_le_mul_of_nonneg_left hbar hη.le
  calc
    β * η * c₀ * A - β * C = β * (-C) + β * (η * (c₀ * A)) := by ring
    _ ≤ β * B.g z + β * (η * barrier z) := add_le_add hbase hbarrier
    _ = β * (B.g z + η * barrier z) := by ring

/-- The combinatorial core of SLC-N014: a high symmetric pair contributes twice to the
ordered sum, hence once with coefficient `1/N` after the frozen `1/(2N)` normalization.
Every other ordered pair uses the global floor. -/
theorem hamiltonian_lower_bound_of_pair
    {N : ℕ} (hN : 2 ≤ N)
    (W : SharpLSI.Torus 1 → SharpLSI.Torus 1 → ℝ)
    (X : SharpLSI.Config N 1) (i j : Fin N) (hij : i ≠ j)
    (D Q : ℝ)
    (hWlower : ∀ x y, -D ≤ W x y)
    (hWsymm : ∀ x y, W x y = W y x)
    (hWhigh : Q - D ≤ W (X i) (X j)) :
    Q / (N : ℝ) - (N : ℝ) * D / 2 ≤
      SharpLSI.hamiltonian (fun _ : SharpLSI.Torus 1 => 0) W N X := by
  let pairs : Finset (Fin N × Fin N) := {(i, j), (j, i)}
  let shifted : Fin N × Fin N → ℝ := fun p => W (X p.1) (X p.2) + D
  have hji : Q - D ≤ W (X j) (X i) := by
    rw [hWsymm]
    exact hWhigh
  have hfirst : Q ≤ shifted (i, j) := by
    dsimp [shifted]
    linarith
  have hsecond : Q ≤ shifted (j, i) := by
    dsimp [shifted]
    linarith
  have hpairs : (i, j) ≠ (j, i) := by
    intro h
    exact hij (congrArg Prod.fst h)
  have hpairSum : 2 * Q ≤ ∑ p ∈ pairs, shifted p := by
    dsimp [pairs]
    rw [Finset.sum_pair hpairs]
    linarith
  have hshiftNonneg : ∀ p, 0 ≤ shifted p := by
    intro p
    dsimp [shifted]
    linarith [hWlower (X p.1) (X p.2)]
  have hpairSubset : pairs ⊆ (Finset.univ : Finset (Fin N × Fin N)) :=
    Finset.subset_univ _
  have hpairLeAll : ∑ p ∈ pairs, shifted p ≤
      ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)), shifted p :=
    Finset.sum_le_sum_of_subset_of_nonneg hpairSubset
      (fun p _ _ => hshiftNonneg p)
  have hsumProduct :
      (∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)), shifted p) =
        ∑ a : Fin N, ∑ b : Fin N, shifted (a, b) := by
    calc
      (∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)), shifted p) =
          ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ
            (Finset.univ : Finset (Fin N)), shifted p := by simp
      _ = ∑ a : Fin N, ∑ b : Fin N, shifted (a, b) := by
          exact Finset.sum_product _ _ _
  have hshiftSum : 2 * Q ≤ ∑ a : Fin N, ∑ b : Fin N, shifted (a, b) :=
    hpairSum.trans (hpairLeAll.trans_eq hsumProduct)
  have hshiftEq :
      (∑ a : Fin N, ∑ b : Fin N, shifted (a, b)) =
        (∑ a : Fin N, ∑ b : Fin N, W (X a) (X b)) + (N : ℝ) ^ 2 * D := by
    simp [shifted, Finset.sum_add_distrib, Finset.sum_const, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have hsumW : 2 * Q - (N : ℝ) ^ 2 * D ≤
      ∑ a : Fin N, ∑ b : Fin N, W (X a) (X b) := by
    rw [hshiftEq] at hshiftSum
    linarith
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hden : 0 < 2 * (N : ℝ) := by positivity
  calc
    Q / (N : ℝ) - (N : ℝ) * D / 2 ≤
        (∑ a : Fin N, ∑ b : Fin N, W (X a) (X b)) / (2 * (N : ℝ)) := by
          apply (le_div_iff₀ hden).2
          field_simp [ne_of_gt hNpos]
          nlinarith [hsumW]
    _ = SharpLSI.hamiltonian (fun _ : SharpLSI.Torus 1 => 0) W N X := by
          unfold SharpLSI.hamiltonian
          simp only [Finset.sum_const_zero, zero_add]
          field_simp [ne_of_gt hNpos]

/-- SLC-N014: once the barrier is high at one unordered pair, its two ordered contributions
give the claimed fixed-`N` Hamiltonian lower bound with the `1/(2N)` normalization. -/
theorem singular_hamiltonian_lower_on_barrier_pair
    (B : BaselineKernel) {β η c₀ : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (G : ℝ) (hG : ∀ x, |B.g x| ≤ G)
    {N : ℕ} (hN : 2 ≤ N) (n : ℕ) (X : SharpLSI.Config N 1)
    (i j : Fin N) (hij : i ≠ j)
    (hbar : c₀ * height n ≤ barrier (X i - X j)) :
    β * η * c₀ / (N : ℝ) * height n - (N : ℝ) * β * G / 2 ≤
      SharpLSI.hamiltonian (fun _ => 0) (perturbedInteraction B β η) N X := by
  have hpair : β * η * c₀ * height n - β * G ≤
      perturbedInteraction B β η (X i) (X j) := by
    simpa [perturbedInteraction, perturbedKernel] using
      pairPotential_lower_bound_of_barrier_lower_bound B hβ hη hG (X i) (X j) hbar
  have hfloor : ∀ x y, -(β * G) ≤ perturbedInteraction B β η x y := by
    intro x y
    rw [perturbedInteraction, perturbedKernel]
    have hg : -G ≤ B.g (x - y) := (abs_le.mp (hG (x - y))).1
    have hb0 : 0 ≤ barrier (x - y) := barrier_nonneg _
    have hbar₀ : 0 ≤ β * (η * barrier (x - y)) :=
      mul_nonneg hβ.le (mul_nonneg hη.le hb0)
    nlinarith
  have hpairHamiltonian :=
    hamiltonian_lower_bound_of_pair hN (perturbedInteraction B β η) X i j hij
      (β * G) (β * η * c₀ * height n) hfloor
      (perturbedInteraction_even B β η) hpair
  have hcoeff : β * η * c₀ / (N : ℝ) * height n =
      (β * η * c₀ * height n) / (N : ℝ) := by ring
  rw [hcoeff]
  convert hpairHamiltonian using 1
  ring

/-- SLC-N013: a nonzero cutoff derivative at the canonical lift of a pair difference
forces the pair interaction to have energy of order the corresponding barrier height. -/
theorem singular_interaction_lower_on_cutoff_derivative
    (B : BaselineKernel) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (G : ℝ) (hG : ∀ z, |B.g z| ≤ G)
    (n : ℕ) (x y : Circle)
    (hderiv : deriv (cutoffLine n) (SharpLSI.secT (x - y) 0) ≠ 0) :
    β * η * (1 / 65 : ℝ) * height n - β * G ≤
      perturbedInteraction B β η x y := by
  have hpoint : torusPoint (SharpLSI.secT (x - y) 0) = x - y :=
    (Examples.PositiveH1.Nonlinear.lift1_coord (SharpLSI.secT (x - y))).symm.trans
      (SharpLSI.liftT_secT (x - y))
  have hbar' := barrier_lower_on_cutoff_derivative n
    (SharpLSI.secT (x - y) 0) hderiv
  have hbar : (1 / 65 : ℝ) * height n ≤ barrier (x - y) := by
    rw [← hpoint]
    nlinarith [hbar']
  have h := pairPotential_lower_bound_of_barrier_lower_bound B hβ hη hG x y hbar
  simpa [perturbedInteraction, perturbedKernel] using h

/-- SLC-N014 specialized to an actual cutoff derivative event on one unordered pair. -/
theorem singular_hamiltonian_lower_on_cutoff_derivative_lift_pair
    (B : BaselineKernel) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (G : ℝ) (hG : ∀ z, |B.g z| ≤ G)
    {N : ℕ} (hN : 2 ≤ N) (n : ℕ) (X : SharpLSI.Config N 1)
    (i j : Fin N) (hij : i ≠ j)
    (t : ℝ) (ht : torusPoint t = X i - X j)
    (hderiv : deriv (cutoffLine n) t ≠ 0) :
    β * η * (1 / 65 : ℝ) / (N : ℝ) * height n - (N : ℝ) * β * G / 2 ≤
      SharpLSI.hamiltonian (fun _ => 0) (perturbedInteraction B β η) N X := by
  have hbar' := barrier_lower_on_cutoff_derivative n t hderiv
  have hbar : (1 / 65 : ℝ) * height n ≤ barrier (X i - X j) := by
    rw [← ht]
    nlinarith [hbar']
  have hC := singular_hamiltonian_lower_on_barrier_pair
    B hβ hη G hG hN n X i j hij hbar
  exact hC

/-- SLC-N014 specialized to the canonical representative of one unordered pair. -/
theorem singular_hamiltonian_lower_on_cutoff_derivative_pair
    (B : BaselineKernel) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (G : ℝ) (hG : ∀ z, |B.g z| ≤ G)
    {N : ℕ} (hN : 2 ≤ N) (n : ℕ) (X : SharpLSI.Config N 1)
    (i j : Fin N) (hij : i ≠ j)
    (hderiv : deriv (cutoffLine n) (SharpLSI.secT (X i - X j) 0) ≠ 0) :
    β * η * (1 / 65 : ℝ) / (N : ℝ) * height n - (N : ℝ) * β * G / 2 ≤
      SharpLSI.hamiltonian (fun _ => 0) (perturbedInteraction B β η) N X := by
  have hpoint : torusPoint (SharpLSI.secT (X i - X j) 0) = X i - X j :=
    (Examples.PositiveH1.Nonlinear.lift1_coord (SharpLSI.secT (X i - X j))).symm.trans
      (SharpLSI.liftT_secT (X i - X j))
  exact singular_hamiltonian_lower_on_cutoff_derivative_lift_pair B hβ hη G hG
    hN n X i j hij (SharpLSI.secT (X i - X j) 0) hpoint hderiv

private theorem particleTest_gradSq_config_aemeasurable {N : ℕ} (n : ℕ) :
    AEMeasurable (fun X : SharpLSI.Config N 1 =>
      SharpLSI.gradSqC (particleTest n) X) volume := by
  let u : UnitAddTorus (Fin N × Fin 1) → ℝ :=
    particleTest n ∘ SharpLSI.unflat
  have hlift : u ∘ SharpLSI.liftT = particleTestLift n := by
    funext v
    exact particleTest_eq_particleTestLift n v
  have hsmooth : ContDiff ℝ 1 (u ∘ SharpLSI.liftT) := by
    rw [hlift]
    exact (particleTestLift_contDiff n).of_le (by simp)
  have hweak : SharpLSI.HasWeakGrad u :=
    ⟨_, SharpLSI.isWeakGrad_of_contDiff hsmooth⟩
  have hmp : MeasurePreserving (SharpLSI.flat : SharpLSI.Config N 1 →
      UnitAddTorus (Fin N × Fin 1)) volume volume :=
    ⟨SharpLSI.measurable_flat, SharpLSI.map_flat_volume N⟩
  have heq : (fun X : SharpLSI.Config N 1 =>
      SharpLSI.gradSqC (particleTest n) X) =
      fun X => SharpLSI.sqNorm (SharpLSI.weakGrad u (SharpLSI.flat X)) := by
    funext X
    change (∑ i : Fin N, ∑ k : Fin 1,
      SharpLSI.weakGrad u (SharpLSI.flat X) (i, k) ^ 2) = _
    simp only [SharpLSI.sqNorm]
    rw [← Fintype.sum_prod_type']
  rw [heq]
  exact (SharpLSI.isWeakGrad_weakGrad hweak).aestronglyMeasurable_sqNorm
    |>.comp_measurePreserving hmp |>.aemeasurable

/-- The fixed-sequence cutoff test has exponentially small Gibbs Dirichlet energy.
The constants may depend on the fixed parameters and particle number, but not on `n`. -/
theorem particleTest_energy_upper_bound
    (B : BaselineKernel) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (G : ℝ) (hG : ∀ z, |B.g z| ≤ G)
    {N : ℕ} (hN : 2 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      SharpLSI.energy (fun _ : SharpLSI.Torus 1 => 0)
        (perturbedInteraction B β η) N (particleTest n) ≤
          ENNReal.ofReal (C / width n *
            Real.exp (-((β * η / (65 * (N : ℝ))) * height n))) := by
  obtain ⟨Cχ, hCχ0, hCχ⟩ := cutoffLine_deriv_sq_integral_bound_uniform
  let Z : ℝ := SharpLSI.partitionFn (fun _ : SharpLSI.Torus 1 => 0)
    (perturbedInteraction B β η) N
  have hNpos : 0 < N := by omega
  have hZ : 0 < Z := by
    dsimp [Z]
    exact singular_partition_pos B hβ hη (by omega)
  let rate : ℝ := β * η / (65 * (N : ℝ))
  let offset : ℝ := (N : ℝ) * β * G / 2
  let K : ℝ := (N : ℝ) ^ 3 / 4
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hG0 : 0 ≤ G := (abs_nonneg (B.g 0)).trans (hG 0)
  let Aconst : ℝ := K * (N : ℝ) ^ 2 * 96 * Cχ ^ 2 * Real.exp offset / Z
  let Cenergy : ℝ := 1 + Aconst
  have hAconst : 0 ≤ Aconst := by
    dsimp [Aconst]
    positivity
  have hCenergy : 0 < Cenergy := by dsimp [Cenergy]; linarith
  refine ⟨Cenergy, hCenergy, ?_⟩
  intro n
  let ρ : SharpLSI.Config N 1 → ENNReal := fun X =>
    ENNReal.ofReal (Real.exp (-SharpLSI.hamiltonian (fun _ => 0)
      (perturbedInteraction B β η) N X) / Z)
  let g : SharpLSI.Config N 1 → ENNReal := fun X =>
    ENNReal.ofReal (SharpLSI.gradSqC (particleTest n) X)
  let A : Set (SharpLSI.Config N 1) := cutoffDerivativeEvent n
  let M : ENNReal := ENNReal.ofReal (Real.exp (-(rate * height n - offset)) / Z)
  have hM : M ≠ ⊤ := by simp [M]
  have hHmeas := singular_hamiltonian_measurable B hβ hη N
  have hρm : Measurable ρ := by
    dsimp [ρ]
    exact ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp (hHmeas.neg)).div_const Z)
  have hgm : AEMeasurable g volume := by
    dsimp [g]
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (particleTest_gradSq_config_aemeasurable n)
  have hgrad := particleTest_gradSq_config_ae_bound (N := N) n
  have hgrad' : ∀ᵐ X ∂(volume : Measure (SharpLSI.Config N 1)),
      SharpLSI.gradSqC (particleTest n) X ≤
        K * particleTestPairDerivativeSqOnConfig n X := by
    filter_upwards [hgrad] with X hX
    rw [particleTestPairDerivativeSq_flat_eq n X] at hX
    exact hX
  have hRint : Integrable
      (particleTestPairDerivativeSqOnConfig n : SharpLSI.Config N 1 → ℝ) volume :=
    particleTestPairDerivativeSqOnConfig_integrable n
  have hRnonneg : ∀ X : SharpLSI.Config N 1,
      0 ≤ particleTestPairDerivativeSqOnConfig n X :=
    fun X => particleTestPairDerivativeSqOnConfig_nonneg n X
  have hRbound := particleTestPairDerivativeSqOnConfig_integral_bound
    (N := N) n Cχ hCχ
  have hscaledInt : Integrable
      (fun X : SharpLSI.Config N 1 => K * particleTestPairDerivativeSqOnConfig n X) volume :=
    hRint.const_mul K
  have hscaledNonneg : ∀ X : SharpLSI.Config N 1,
      0 ≤ K * particleTestPairDerivativeSqOnConfig n X :=
    fun X => mul_nonneg hK (hRnonneg X)
  have hscaledLin : (∫⁻ X : SharpLSI.Config N 1,
      ENNReal.ofReal (K * particleTestPairDerivativeSqOnConfig n X) ∂volume) ≤
      ENNReal.ofReal (K * (N : ℝ) ^ 2 * (96 * Cχ ^ 2 / width n)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hscaledInt
      (Filter.Eventually.of_forall hscaledNonneg)]
    apply ENNReal.ofReal_le_ofReal
    calc
      (∫ X : SharpLSI.Config N 1,
        K * particleTestPairDerivativeSqOnConfig n X ∂volume) =
          K * ∫ X : SharpLSI.Config N 1,
            particleTestPairDerivativeSqOnConfig n X ∂volume := by
              exact integral_const_mul K _
      _ ≤ K * ((N : ℝ) ^ 2 * (96 * Cχ ^ 2 / width n)) := by
        exact mul_le_mul_of_nonneg_left hRbound hK
      _ = K * (N : ℝ) ^ 2 * (96 * Cχ ^ 2 / width n) := by ring
  have hlinGrad : (∫⁻ X : SharpLSI.Config N 1, g X ∂volume) ≤
      ENNReal.ofReal (K * (N : ℝ) ^ 2 * (96 * Cχ ^ 2 / width n)) := by
    apply (lintegral_mono_ae ?_).trans hscaledLin
    filter_upwards [hgrad'] with X hX
    dsimp [g]
    exact ENNReal.ofReal_le_ofReal hX
  have hzero : ∀ᵐ X ∂(volume : Measure (SharpLSI.Config N 1)),
      X ∉ A → g X = 0 := by
    filter_upwards [hgrad'] with X hX hnot
    have hRzero : particleTestPairDerivativeSqOnConfig n X = 0 :=
      particleTestPairDerivativeSqOnConfig_zero_of_not_event n X hnot
    have hgradle : SharpLSI.gradSqC (particleTest n) X ≤ 0 := by
      simpa [hRzero] using hX
    have hgrad0 : SharpLSI.gradSqC (particleTest n) X = 0 :=
      le_antisymm hgradle (SharpLSI.gradSqC_nonneg _ _)
    simp [g, hgrad0]
  have hbound : ∀ᵐ X ∂(volume : Measure (SharpLSI.Config N 1)),
      X ∈ A → ρ X ≤ M := by
    filter_upwards [] with X hXA
    rcases hXA with ⟨i, j, hij, hderiv⟩
    have hH := singular_hamiltonian_lower_on_cutoff_derivative_pair
      B hβ hη G hG hN n X i j hij hderiv
    have hrate : β * η * (1 / 65 : ℝ) / (N : ℝ) = rate := by
      dsimp [rate]
      ring
    have hlower : rate * height n - offset ≤
        SharpLSI.hamiltonian (fun _ : SharpLSI.Torus 1 => 0)
          (perturbedInteraction B β η) N X := by
      dsimp [offset]
      rw [← hrate]
      exact hH
    have hreal : Real.exp (-SharpLSI.hamiltonian (fun _ => 0)
        (perturbedInteraction B β η) N X) / Z ≤
        Real.exp (-(rate * height n - offset)) / Z :=
      div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr (neg_le_neg hlower)) hZ.le
    exact ENNReal.ofReal_le_ofReal (by simpa [ρ, M] using hreal)
  have henergy : SharpLSI.energy (fun _ : SharpLSI.Torus 1 => 0)
      (perturbedInteraction B β η) N (particleTest n) ≤
      M *
        ENNReal.ofReal (K * (N : ℝ) ^ 2 * (96 * Cχ ^ 2 / width n)) := by
    unfold SharpLSI.energy
    change (∫⁻ X : SharpLSI.Config N 1, g X ∂volume.withDensity ρ) ≤ _
    exact (lintegral_withDensity_le_of_bound_on_support volume ρ g A M hM
      hρm.aemeasurable hgm hzero hbound).trans
      (mul_le_mul_of_nonneg_left hlinGrad (by positivity))
  have hexp : Real.exp (-(rate * height n - offset)) =
      Real.exp offset * Real.exp (-(rate * height n)) := by
    rw [show -(rate * height n - offset) = offset + -(rate * height n) by ring,
      Real.exp_add]
  have hprod : (Real.exp (-(rate * height n - offset)) / Z) *
      (K * (N : ℝ) ^ 2 * (96 * Cχ ^ 2 / width n)) =
      (Aconst / width n) * Real.exp (-(rate * height n)) := by
    dsimp [Aconst]
    rw [hexp]
    field_simp [ne_of_gt hZ, ne_of_gt (width_pos n)]
  have hproduct :
      ENNReal.ofReal (Real.exp (-(rate * height n - offset)) / Z) *
        ENNReal.ofReal (K * (N : ℝ) ^ 2 * (96 * Cχ ^ 2 / width n)) =
      ENNReal.ofReal ((Aconst / width n) * Real.exp (-(rate * height n))) := by
    calc
      _ = ENNReal.ofReal ((Real.exp (-(rate * height n - offset)) / Z) *
          (K * (N : ℝ) ^ 2 * (96 * Cχ ^ 2 / width n))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
      _ = _ := congrArg ENNReal.ofReal hprod
  have hcoef : (Aconst / width n) * Real.exp (-(rate * height n)) ≤
      (Cenergy / width n) * Real.exp (-(rate * height n)) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply div_le_div_of_nonneg_right
    · dsimp [Cenergy]
      linarith
    · exact (width_pos n).le
  exact henergy.trans (hproduct ▸ ENNReal.ofReal_le_ofReal hcoef)

end DGPS.SingularCounterexample
