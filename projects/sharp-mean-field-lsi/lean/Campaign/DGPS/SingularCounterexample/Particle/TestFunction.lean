import DGPS.SingularCounterexample.Cutoff
import DGPS.SingularCounterexample.Particle.WellPosed
import SharpSymmetricLSI.Infra.SmoothWeakGrad
import SharpSymmetricLSI.Infra.WeakGrad
import SharpSymmetricLSI.Paper.Gibbs

open MeasureTheory
open scoped ContDiff

namespace DGPS.SingularCounterexample

private noncomputable def orderedPairTerm {N : ℕ} (n : ℕ)
    (X : SharpLSI.Config N 1) (i j : Fin N) : ℝ :=
  if i = j then 0 else pairCutoff n (X i - X j)

/-- The pair test, written as half the ordered sum over distinct pairs to preserve the usual
unordered-pair normalization. -/
noncomputable def particleTest (n : ℕ) {N : ℕ} (X : SharpLSI.Config N 1) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, orderedPairTerm n X i j

theorem particleTest_isSymmetric (n : ℕ) {N : ℕ} :
    SharpLSI.IsSymmetric (particleTest n : SharpLSI.Config N 1 → ℝ) := by
  intro σ X
  unfold particleTest
  congr 1
  have hterm (i j : Fin N) :
      orderedPairTerm n (X ∘ ⇑σ) i j = orderedPairTerm n X (σ i) (σ j) := by
    simp [orderedPairTerm, Function.comp_apply]
  simp_rw [hterm]
  calc
    ∑ i, ∑ j, orderedPairTerm n X (σ i) (σ j) =
        ∑ i, ∑ j, orderedPairTerm n X (σ i) j := by
      apply congrArg (fun f : Fin N → ℝ => ∑ i, f i)
      funext i
      exact Equiv.sum_comp σ (fun j => orderedPairTerm n X (σ i) j)
    _ = ∑ i, ∑ j, orderedPairTerm n X i j :=
      Equiv.sum_comp σ (fun i => ∑ j, orderedPairTerm n X i j)

/-- Lifted form of the pair test, where every term is an ordinary smooth real-line cutoff. -/
noncomputable def particleTestLift (n : ℕ) {N : ℕ} (v : Fin N × Fin 1 → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j,
    if i = j then 0 else cutoffLine n (v (i, 0) - v (j, 0))

theorem particleTestLift_contDiff (n : ℕ) {N : ℕ} :
    ContDiff ℝ ∞ (particleTestLift n : (Fin N × Fin 1 → ℝ) → ℝ) := by
  unfold particleTestLift
  refine contDiff_const.mul (ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_)
  by_cases hij : i = j
  · simp [hij]
    exact contDiff_const
  · simp [hij]
    exact (cutoffLine_contDiff n).comp (by fun_prop)

private noncomputable def pairLiftDeriv {N : ℕ} (n : ℕ)
    (v : Fin N × Fin 1 → ℝ) (i j : Fin N) :
    (Fin N × Fin 1 → ℝ) →L[ℝ] ℝ :=
  if i = j then 0 else
    (ContinuousLinearMap.toSpanSingleton ℝ
      (deriv (cutoffLine n) (v (i, 0) - v (j, 0)))) ∘L
        ((ContinuousLinearMap.proj (i, (0 : Fin 1)) :
          (Fin N × Fin 1 → ℝ) →L[ℝ] ℝ) -
          (ContinuousLinearMap.proj (j, (0 : Fin 1)) :
          (Fin N × Fin 1 → ℝ) →L[ℝ] ℝ))

private theorem pairLiftTerm_hasFDerivAt {N : ℕ} (n : ℕ)
    (v : Fin N × Fin 1 → ℝ) (i j : Fin N) :
    HasFDerivAt (fun w : Fin N × Fin 1 → ℝ =>
      if i = j then 0 else cutoffLine n (w (i, 0) - w (j, 0)))
      (pairLiftDeriv n v i j) v := by
  by_cases hij : i = j
  · subst j
    simpa [pairLiftDeriv] using hasFDerivAt_const (0 : ℝ) v
  · simp only [if_neg hij, pairLiftDeriv]
    have harg : HasFDerivAt (fun w : Fin N × Fin 1 → ℝ => w (i, 0) - w (j, 0))
        ((ContinuousLinearMap.proj (i, (0 : Fin 1)) :
          (Fin N × Fin 1 → ℝ) →L[ℝ] ℝ) -
          (ContinuousLinearMap.proj (j, (0 : Fin 1)) :
          (Fin N × Fin 1 → ℝ) →L[ℝ] ℝ)) v := by
      exact ((ContinuousLinearMap.proj (i, (0 : Fin 1)) :
        (Fin N × Fin 1 → ℝ) →L[ℝ] ℝ).hasFDerivAt).sub
        (ContinuousLinearMap.proj (j, (0 : Fin 1)) :
          (Fin N × Fin 1 → ℝ) →L[ℝ] ℝ).hasFDerivAt
    have hline : HasDerivAt (cutoffLine n)
        (deriv (cutoffLine n) (v (i, 0) - v (j, 0))) (v (i, 0) - v (j, 0)) := by
      exact ((cutoffLine_contDiff n).contDiffAt.differentiableAt (by norm_num)).hasDerivAt
    change HasFDerivAt (cutoffLine n ∘ fun w : Fin N × Fin 1 → ℝ =>
      w (i, 0) - w (j, 0))
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (deriv (cutoffLine n) (v (i, 0) - v (j, 0)))) ∘L
        ((ContinuousLinearMap.proj (i, (0 : Fin 1)) :
          (Fin N × Fin 1 → ℝ) →L[ℝ] ℝ) -
          (ContinuousLinearMap.proj (j, (0 : Fin 1)) :
          (Fin N × Fin 1 → ℝ) →L[ℝ] ℝ))) v
    exact hline.hasFDerivAt.comp v harg

theorem particleTestLift_hasFDerivAt (n : ℕ) {N : ℕ}
    (v : Fin N × Fin 1 → ℝ) :
    HasFDerivAt (particleTestLift n : (Fin N × Fin 1 → ℝ) → ℝ)
      ((1 / 2 : ℝ) • ∑ i, ∑ j, pairLiftDeriv n v i j) v := by
  unfold particleTestLift
  refine (HasFDerivAt.fun_sum (fun i _ => ?_)).const_mul (1 / 2 : ℝ)
  exact HasFDerivAt.fun_sum (fun j _ => pairLiftTerm_hasFDerivAt n v i j)

private theorem pairLiftDeriv_apply {N : ℕ} (n : ℕ) (v : Fin N × Fin 1 → ℝ)
    (a b i : Fin N) :
    pairLiftDeriv n v a b (Pi.single (i, (0 : Fin 1)) 1) =
      if a = b then 0 else
        deriv (cutoffLine n) (v (a, 0) - v (b, 0)) *
          ((if a = i then (1 : ℝ) else 0) - (if b = i then 1 else 0)) := by
  by_cases hab : a = b
  · subst b
    simp [pairLiftDeriv]
  · simp [pairLiftDeriv, hab, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.proj_apply, Pi.single_apply, Prod.mk.injEq]
    by_cases hai : a = i <;> by_cases hbi : b = i <;> simp_all <;> ring

/-- The classical coordinate derivative of the lifted test.  The ordered-pair form is retained
here so no orientation convention is hidden in the formula. -/
theorem particleTestLift_coordinate_deriv (n : ℕ) {N : ℕ}
    (v : Fin N × Fin 1 → ℝ) (i : Fin N) :
    (fderiv ℝ (particleTestLift n) v) (Pi.single (i, (0 : Fin 1)) 1) =
      (1 / 2 : ℝ) * ∑ a, ∑ b,
        if a = b then 0 else
          deriv (cutoffLine n) (v (a, 0) - v (b, 0)) *
            ((if a = i then (1 : ℝ) else 0) - (if b = i then 1 else 0)) := by
  rw [(particleTestLift_hasFDerivAt n v).fderiv]
  simp_rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    pairLiftDeriv_apply]
  rw [smul_eq_mul]

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

theorem cutoffLine_deriv_bounded_global (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv (cutoffLine n) t| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := chi_deriv_bounded
  refine ⟨4 * C / width n, div_nonneg (by positivity) (width_pos n).le, fun t => ?_⟩
  let s : ℝ := if Int.fract t = 0 then 1 else Int.fract t
  let k : ℤ := if Int.fract t = 0 then Int.floor t - 1 else Int.floor t
  have hts : t = s + (k : ℝ) := by
    by_cases hz : Int.fract t = 0
    · have hf : (Int.floor t : ℝ) = t := by
        have h := Int.fract_add_floor t
        rw [hz] at h
        simpa using h
      simp [s, k, hz]
      push_cast
      linarith
    · simp [s, k, hz]
  have hs : s ∈ Set.Ioc (0 : ℝ) 1 := by
    dsimp [s]
    split_ifs with hz
    · norm_num
    · refine ⟨lt_of_le_of_ne (Int.fract_nonneg t) (Ne.symm hz),
        le_of_lt (Int.fract_lt_one t)⟩
  have hperiod := (cutoffLine_deriv_periodic_function n).int_mul k
  have hperiod' : deriv (cutoffLine n) (s + (k : ℝ)) = deriv (cutoffLine n) s := by
    simpa using hperiod s
  rw [hts, hperiod']
  exact cutoffLine_deriv_bound_on_Ioc n hs C hC

private theorem chosen_weakGrad_isWeakGrad {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : UnitAddTorus ι → ℝ} (h : SharpLSI.HasWeakGrad f) :
    SharpLSI.IsWeakGrad f (SharpLSI.weakGrad f) := by
  have heq : SharpLSI.weakGrad f = h.choose := by
    simp [SharpLSI.weakGrad, h]
  rw [heq]
  exact h.choose_spec

private theorem gibbs_map_flat_ac_lowerBound {N : ℕ}
    (W : SharpLSI.Torus 1 → SharpLSI.Torus 1 → ℝ) :
    (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N).map SharpLSI.flat ≪
      (volume : Measure (UnitAddTorus (Fin N × Fin 1))) := by
  rw [← SharpLSI.map_flat_volume N]
  have hac : SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N ≪
      (volume : Measure (SharpLSI.Config N 1)) := by
    change ((volume : Measure (SharpLSI.Config N 1)).withDensity
      (SharpLSI.gibbsDensity volume
        (SharpLSI.hamiltonian (fun _ => 0) W N))) ≪ _
    exact SharpLSI.withDensity_gibbs_absolutelyContinuous volume
  exact hac.map SharpLSI.measurable_flat

/-- Smooth bounded tests with bounded classical gradient belong to `MemH1C` for every
lower-bounded measurable Gibbs Hamiltonian.  Only absolute continuity and the finite probability
bound are used; no lower density comparison is involved. -/
theorem smooth_test_memH1C_of_bounded {N : ℕ}
    (W : SharpLSI.Torus 1 → SharpLSI.Torus 1 → ℝ)
    (hWmeas : Measurable (Function.uncurry W))
    (hWlower : ∃ a : ℝ, ∀ x y, a ≤ W x y)
    (f : SharpLSI.Config N 1 → ℝ)
    (hfm : Measurable f)
    (hfb : ∃ C : ℝ, 0 ≤ C ∧ ∀ X, |f X| ≤ C)
    (hsmooth : ContDiff ℝ 1 ((f ∘ SharpLSI.unflat) ∘ SharpLSI.liftT))
    (hgrad : ∃ C : ℝ, 0 ≤ C ∧ ∀ y p,
      |(fderiv ℝ ((f ∘ SharpLSI.unflat) ∘ SharpLSI.liftT)
        (SharpLSI.secT y) (Pi.single p 1))| ≤ C) :
    SharpLSI.MemH1C
      (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N) f := by
  obtain ⟨a, ha⟩ := hWlower
  have hHmeas := zero_hamiltonian_measurable (N := N) W hWmeas
  have hHlower : ∃ b : ℝ, ∀ X,
      b ≤ SharpLSI.hamiltonian (fun _ : SharpLSI.Torus 1 => 0) W N X := by
    refine ⟨1 / (2 * (N : ℝ)) * (∑ _i : Fin N, ∑ _j : Fin N, a), ?_⟩
    intro X
    exact zero_hamiltonian_lower_bound (N := N) W ha X
  obtain ⟨b, hb⟩ := hHlower
  haveI hprob : IsProbabilityMeasure
      (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N) :=
    gibbs_probability_of_hamiltonian_lower_bound (d := 1) (N := N)
      (fun _ : SharpLSI.Torus 1 => 0) W hHmeas hb
  let P := (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N).map SharpLSI.flat
  haveI hprobFlat : IsProbabilityMeasure P :=
    (Measure.isProbabilityMeasure_map_iff SharpLSI.measurable_flat.aemeasurable).mpr hprob
  have hac : P ≪ (volume : Measure (UnitAddTorus (Fin N × Fin 1))) := by
    change (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N).map SharpLSI.flat ≪ _
    exact gibbs_map_flat_ac_lowerBound W
  let u : UnitAddTorus (Fin N × Fin 1) → ℝ := f ∘ SharpLSI.unflat
  have hsmoothU : ContDiff ℝ 1 (u ∘ SharpLSI.liftT) := by
    simpa only [u, Function.comp_apply] using hsmooth
  have hweak : SharpLSI.HasWeakGrad u :=
    ⟨_, SharpLSI.isWeakGrad_of_contDiff hsmoothU⟩
  obtain ⟨Cv, hCv, hfb⟩ := hfb
  have hvalMeas : AEStronglyMeasurable u P := by
    exact (hfm.comp SharpLSI.measurable_unflat).aestronglyMeasurable
  have hvalLp : MemLp u 2 P := by
    refine MemLp.of_bound hvalMeas Cv ?_
    filter_upwards [] with y
    rw [Real.norm_eq_abs]
    exact hfb (SharpLSI.unflat y)
  obtain ⟨Cg, hCg, hgrad⟩ := hgrad
  have haeClassical : SharpLSI.weakGrad u =ᵐ[(volume : Measure _)]
      (fun y p => fderiv ℝ (u ∘ SharpLSI.liftT) (SharpLSI.secT y) (Pi.single p 1)) :=
    SharpLSI.weakGrad_ae_eq_of_contDiff hsmoothU
  have hgradMeas : AEStronglyMeasurable
      (fun y => Real.sqrt (SharpLSI.sqNorm (SharpLSI.weakGrad u y))) P := by
    have hw := chosen_weakGrad_isWeakGrad hweak
    exact (Real.continuous_sqrt.comp_aestronglyMeasurable
      hw.aestronglyMeasurable_sqNorm).mono_ac hac
  have hboundGrad : ∀ᵐ y ∂P,
      ‖Real.sqrt (SharpLSI.sqNorm (SharpLSI.weakGrad u y))‖ ≤
        Real.sqrt (Fintype.card (Fin N × Fin 1) : ℝ) * Cg := by
    apply hac.ae_le
    filter_upwards [haeClassical] with y hy
    have hsq : SharpLSI.sqNorm (SharpLSI.weakGrad u y) ≤
        (Fintype.card (Fin N × Fin 1) : ℝ) * Cg ^ 2 := by
      rw [hy]
      unfold SharpLSI.sqNorm
      calc
        ∑ p, (fderiv ℝ (u ∘ SharpLSI.liftT) (SharpLSI.secT y) (Pi.single p 1)) ^ 2
            ≤ ∑ _p : Fin N × Fin 1, Cg ^ 2 :=
              Finset.sum_le_sum fun p _ => by
                have hp := abs_le.mp (hgrad y p)
                nlinarith
        _ = (Fintype.card (Fin N × Fin 1) : ℝ) * Cg ^ 2 := by simp
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      Real.sqrt (SharpLSI.sqNorm (SharpLSI.weakGrad u y)) ≤
          Real.sqrt ((Fintype.card (Fin N × Fin 1) : ℝ) * Cg ^ 2) :=
        Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (Fintype.card (Fin N × Fin 1) : ℝ) * Cg := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hCg]
  have hgradLp : MemLp
      (fun y => Real.sqrt (SharpLSI.sqNorm (SharpLSI.weakGrad u y))) 2 P := by
    refine MemLp.of_bound hgradMeas _ hboundGrad
  change SharpLSI.MemH1 P u
  exact ⟨hweak, hvalLp, hgradLp⟩

private theorem particleTestLift_coordinate_bound {N : ℕ} (n : ℕ)
    (v : Fin N × Fin 1 → ℝ) (i : Fin N) (C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ t, |deriv (cutoffLine n) t| ≤ C) :
    |(fderiv ℝ (particleTestLift n) v)
      (Pi.single (i, (0 : Fin 1)) (1 : ℝ) : (Fin N × Fin 1 → ℝ))| ≤
      ((N : ℝ) ^ 2 * C) / 2 := by
  rw [particleTestLift_coordinate_deriv]
  have hdelta (a b : Fin N) :
      |if a = b then 0 else
        deriv (cutoffLine n) (v (a, 0) - v (b, 0)) *
          ((if a = i then (1 : ℝ) else 0) - (if b = i then 1 else 0))| ≤ C := by
    by_cases hab : a = b
    · simp [hab, hC0]
    · simp only [if_neg hab]
      rw [abs_mul]
      have hcoef : |(if a = i then (1 : ℝ) else 0) -
          (if b = i then (1 : ℝ) else 0)| ≤ 1 := by
        by_cases hai : a = i <;> by_cases hbi : b = i <;>
          simp [hai, hbi, hab]
      calc
        |deriv (cutoffLine n) (v (a, 0) - v (b, 0))| *
            |(if a = i then (1 : ℝ) else 0) - (if b = i then 1 else 0)|
            ≤ C * 1 := mul_le_mul (hC _) hcoef (abs_nonneg _) hC0
        _ = C := by ring
  let T (a b : Fin N) : ℝ := if a = b then 0 else
    deriv (cutoffLine n) (v (a, 0) - v (b, 0)) *
      ((if a = i then (1 : ℝ) else 0) - (if b = i then 1 else 0))
  have hsum : |∑ a, ∑ b, T a b| ≤ (N : ℝ) ^ 2 * C := by
    calc
      |∑ a, ∑ b, T a b| ≤ ∑ a, ∑ b, |T a b| := by
        calc
          |∑ a, ∑ b, T a b| ≤ ∑ a, |∑ b, T a b| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ a, ∑ b, |T a b| :=
            Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Fin N, ∑ _b : Fin N, C :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => by
          simpa [T] using hdelta a b
      _ = (N : ℝ) ^ 2 * C := by simp; ring
  change |(1 / 2 : ℝ) * ∑ a, ∑ b, T a b| ≤ ((N : ℝ) ^ 2 * C) / 2
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    (1 / 2 : ℝ) * |∑ a, ∑ b, T a b| ≤
        (1 / 2 : ℝ) * ((N : ℝ) ^ 2 * C) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = ((N : ℝ) ^ 2 * C) / 2 := by ring

/-- The directed-pair square energy, equal to the unordered sum of both orientations. -/
noncomputable def particleTestPairDerivativeSq {N : ℕ} (n : ℕ)
    (y : UnitAddTorus (Fin N × Fin 1)) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else
    (deriv (cutoffLine n) (SharpLSI.secT y (i, 0) - SharpLSI.secT y (j, 0))) ^ 2

/-- A finite-dimensional Cauchy--Schwarz bound for the classical lifted gradient.  The constant
is intentionally coarse; the right-hand side remains the oriented version of the unordered pair
energy, with no change to the test's half-ordered-sum normalization. -/
theorem particleTestLift_gradSq_bound {N : ℕ} (n : ℕ)
    (v : Fin N × Fin 1 → ℝ) :
    (∑ i : Fin N,
      ((fderiv ℝ (particleTestLift n) v)
        (Pi.single (i, (0 : Fin 1)) (1 : ℝ) : (Fin N × Fin 1 → ℝ))) ^ 2) ≤
      ((N : ℝ) ^ 3 / 4) *
        (∑ a : Fin N, ∑ b : Fin N,
          if a = b then 0 else
            (deriv (cutoffLine n) (v (a, 0) - v (b, 0))) ^ 2) := by
  let D (a b : Fin N) : ℝ := if a = b then 0 else
    deriv (cutoffLine n) (v (a, 0) - v (b, 0))
  let c (a b i : Fin N) : ℝ :=
    (if a = i then (1 : ℝ) else 0) - (if b = i then 1 else 0)
  have hc (a b i : Fin N) : |c a b i| ≤ 1 := by
    by_cases hai : a = i <;> by_cases hbi : b = i <;>
      simp [c, hai, hbi]
  have hcoeff (i a : Fin N) :
      (∑ b : Fin N, (c a b i) ^ 2) ≤ (N : ℝ) := by
    calc
      (∑ b : Fin N, (c a b i) ^ 2) ≤ ∑ _b : Fin N, (1 : ℝ) :=
        Finset.sum_le_sum fun b _ => by
          have h := hc a b i
          have h' := abs_le.mp h
          nlinarith [h'.1, h'.2]
      _ = (N : ℝ) := by simp
  have hDnonneg : 0 ≤ ∑ a : Fin N, ∑ b : Fin N, (D a b) ^ 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hcoord (i : Fin N) :
      ((fderiv ℝ (particleTestLift n) v)
        (Pi.single (i, (0 : Fin 1)) (1 : ℝ) : (Fin N × Fin 1 → ℝ))) ^ 2 ≤
        ((N : ℝ) ^ 2 / 4) * (∑ a : Fin N, ∑ b : Fin N, (D a b) ^ 2) := by
    rw [particleTestLift_coordinate_deriv]
    have hdiag : (∑ a : Fin N, ∑ b : Fin N,
        if a = b then 0 else
          deriv (cutoffLine n) (v (a, 0) - v (b, 0)) *
            ((if a = i then (1 : ℝ) else 0) - (if b = i then 1 else 0))) =
        ∑ a : Fin N, ∑ b : Fin N, D a b * c a b i := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : a = b
      · simp [hab, D, c]
      · simp [hab, D, c]
    let A (a : Fin N) : ℝ := ∑ b : Fin N, D a b * c a b i
    have hrow (a : Fin N) : A a ^ 2 ≤
        (∑ b : Fin N, (D a b) ^ 2) * (∑ b : Fin N, (c a b i) ^ 2) := by
      simpa only [A] using Finset.sum_mul_sq_le_sq_mul_sq
        (s := (Finset.univ : Finset (Fin N)))
        (fun b : Fin N => D a b) (fun b : Fin N => c a b i)
    have hrows : (∑ a : Fin N, A a ^ 2) ≤
        (N : ℝ) * (∑ a : Fin N, ∑ b : Fin N, (D a b) ^ 2) := by
      calc
        (∑ a : Fin N, A a ^ 2) ≤
            ∑ a : Fin N, (∑ b : Fin N, (D a b) ^ 2) * (N : ℝ) :=
          Finset.sum_le_sum fun a _ => by
            calc
              A a ^ 2 ≤ (∑ b : Fin N, (D a b) ^ 2) * (∑ b : Fin N, (c a b i) ^ 2) := hrow a
              _ ≤ (∑ b : Fin N, (D a b) ^ 2) * (N : ℝ) :=
                mul_le_mul_of_nonneg_left (hcoeff i a) (Finset.sum_nonneg fun b _ => sq_nonneg _)
        _ = (N : ℝ) * (∑ a : Fin N, ∑ b : Fin N, (D a b) ^ 2) := by
          calc
            _ = (∑ a : Fin N, (∑ b : Fin N, (D a b) ^ 2) * (N : ℝ)) := rfl
            _ = (∑ a : Fin N, ∑ b : Fin N, (D a b) ^ 2) * (N : ℝ) := by
              rw [Finset.sum_mul]
            _ = _ := by ring
    have houter : (∑ a : Fin N, A a) ^ 2 ≤
        (∑ a : Fin N, A a ^ 2) * (N : ℝ) := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq
        (s := (Finset.univ : Finset (Fin N))) A (fun _ => (1 : ℝ))
    rw [hdiag]
    change ((1 / 2 : ℝ) * ∑ a : Fin N, A a) ^ 2 ≤
      ((N : ℝ) ^ 2 / 4) * (∑ a : Fin N, ∑ b : Fin N, (D a b) ^ 2)
    calc
      ((1 / 2 : ℝ) * ∑ a : Fin N, A a) ^ 2 =
          (1 / 4 : ℝ) * (∑ a : Fin N, A a) ^ 2 := by ring
      _ ≤ (1 / 4 : ℝ) * ((∑ a : Fin N, A a ^ 2) * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left houter (by norm_num)
      _ ≤ (1 / 4 : ℝ) * ((N : ℝ) *
            (∑ a : Fin N, ∑ b : Fin N, (D a b) ^ 2) * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrows (by positivity)) (by norm_num)
      _ = ((N : ℝ) ^ 2 / 4) *
            (∑ a : Fin N, ∑ b : Fin N, (D a b) ^ 2) := by ring
  calc
    (∑ i : Fin N,
      ((fderiv ℝ (particleTestLift n) v)
        (Pi.single (i, (0 : Fin 1)) (1 : ℝ) : (Fin N × Fin 1 → ℝ))) ^ 2) ≤
        ∑ i : Fin N, ((N : ℝ) ^ 2 / 4) *
          (∑ a : Fin N, ∑ b : Fin N, (D a b) ^ 2) :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ = ((N : ℝ) ^ 3 / 4) *
        (∑ a : Fin N, ∑ b : Fin N, (D a b) ^ 2) := by simp; ring
    _ = ((N : ℝ) ^ 3 / 4) *
        (∑ a : Fin N, ∑ b : Fin N,
          if a = b then 0 else
            (deriv (cutoffLine n) (v (a, 0) - v (b, 0))) ^ 2) := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : a = b <;> simp [D, hab]

theorem particleTestLift_gradient_bounded (n : ℕ) {N : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v i,
    |(fderiv ℝ (particleTestLift n) v)
      (Pi.single (i, (0 : Fin 1)) (1 : ℝ) : (Fin N × Fin 1 → ℝ))| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := cutoffLine_deriv_bounded_global n
  refine ⟨((N : ℝ) ^ 2 * C) / 2, ?_, fun v i => ?_⟩
  · positivity
  · exact particleTestLift_coordinate_bound n v i C hC0 hC

private theorem unflat_lift_apply {N : ℕ} (v : Fin N × Fin 1 → ℝ) (i : Fin N) :
    SharpLSI.unflat (SharpLSI.liftT v) i =
      DGPS.torusLift (fun k : Fin 1 => v (i, k)) := by
  ext k
  simp [SharpLSI.unflat, DGPS.torusLift, SharpLSI.liftT]

private theorem pairCutoff_unflat_lift {N : ℕ} (n : ℕ)
    (v : Fin N × Fin 1 → ℝ) (i j : Fin N) :
    pairCutoff n (SharpLSI.unflat (SharpLSI.liftT v) i -
      SharpLSI.unflat (SharpLSI.liftT v) j) = cutoffLine n (v (i, 0) - v (j, 0)) := by
  rw [unflat_lift_apply, unflat_lift_apply]
  have hdiff : ((fun k : Fin 1 => v (i, k)) - (fun k => v (j, k))) =
      (fun _ : Fin 1 => v (i, 0) - v (j, 0)) := by
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    rw [hk]
    simp
  rw [← SharpLSI.liftT_sub, hdiff]
  exact pairCutoff_lift n _

theorem particleTest_eq_particleTestLift {N : ℕ} (n : ℕ)
    (v : Fin N × Fin 1 → ℝ) :
    particleTest n (SharpLSI.unflat (SharpLSI.liftT v)) = particleTestLift n v := by
  unfold particleTest particleTestLift orderedPairTerm
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp [pairCutoff_unflat_lift]

/-- Haar-a.e. the chosen weak-gradient square agrees with the classical smooth gradient and obeys
the finite-pair Cauchy--Schwarz estimate.  The a.e. qualification is essential because
`weakGrad` is a chosen representative, unique only almost everywhere. -/
theorem particleTest_gradSq_ae_bound {N : ℕ} (n : ℕ) :
    ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin N × Fin 1))),
      SharpLSI.gradSqC (particleTest n) (SharpLSI.unflat y) ≤
        ((N : ℝ) ^ 3 / 4) * particleTestPairDerivativeSq n y := by
  let u : UnitAddTorus (Fin N × Fin 1) → ℝ := particleTest n ∘ SharpLSI.unflat
  have hlift : (u ∘ SharpLSI.liftT) = particleTestLift n := by
    funext v
    exact particleTest_eq_particleTestLift n v
  have hsmooth : ContDiff ℝ 1 (u ∘ SharpLSI.liftT) := by
    rw [hlift]
    exact (particleTestLift_contDiff n).of_le (by simp)
  have hae := SharpLSI.weakGrad_ae_eq_of_contDiff hsmooth
  filter_upwards [hae] with y hy
  have hsq : SharpLSI.gradSqC (particleTest n) (SharpLSI.unflat y) =
      ∑ i : Fin N,
        (fderiv ℝ (particleTestLift n) (SharpLSI.secT y)
          (Pi.single (i, (0 : Fin 1)) (1 : ℝ))) ^ 2 := by
    change (∑ i : Fin N, ∑ k : Fin 1,
        SharpLSI.weakGrad u y (i, k) ^ 2) = _
    simp_rw [hy]
    simp [hlift]
  rw [hsq]
  simpa [particleTestPairDerivativeSq] using
    particleTestLift_gradSq_bound n (SharpLSI.secT y)

/-- The same corrected a.e. estimate on configuration Haar measure. -/
theorem particleTest_gradSq_config_ae_bound {N : ℕ} (n : ℕ) :
    ∀ᵐ X ∂(volume : Measure (SharpLSI.Config N 1)),
      SharpLSI.gradSqC (particleTest n) X ≤
        ((N : ℝ) ^ 3 / 4) * particleTestPairDerivativeSq n (SharpLSI.flat X) := by
  have hmap : ∀ᵐ y ∂((volume : Measure (SharpLSI.Config N 1)).map SharpLSI.flat),
      SharpLSI.gradSqC (particleTest n) (SharpLSI.unflat y) ≤
        ((N : ℝ) ^ 3 / 4) * particleTestPairDerivativeSq n y := by
    simpa only [SharpLSI.map_flat_volume N] using particleTest_gradSq_ae_bound n
  have h := ae_of_ae_map SharpLSI.measurable_flat.aemeasurable hmap
  filter_upwards [h] with X hX
  have hflat : SharpLSI.unflat (SharpLSI.flat X) = X := by rfl
  rw [hflat] at hX
  exact hX

theorem particleTest_nonneg {N : ℕ} (n : ℕ) (X : SharpLSI.Config N 1) :
    0 ≤ particleTest n X := by
  unfold particleTest
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    by_cases hij : i = j
    · simp [orderedPairTerm, hij]
    · simp [orderedPairTerm, hij, pairCutoff_nonneg]

theorem particleTest_le {N : ℕ} (n : ℕ) (X : SharpLSI.Config N 1) :
    particleTest n X ≤ (N : ℝ) ^ 2 / 2 := by
  unfold particleTest
  have hterm (i j : Fin N) : orderedPairTerm n X i j ≤ 1 := by
    by_cases hij : i = j
    · simp [orderedPairTerm, hij]
    · simpa [orderedPairTerm, hij] using pairCutoff_le_one n (X i - X j)
  have hsum : (∑ i, ∑ j, orderedPairTerm n X i j) ≤
      ∑ i : Fin N, ∑ _j : Fin N, (1 : ℝ) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  calc
    (1 / 2 : ℝ) * ∑ i, ∑ j, orderedPairTerm n X i j ≤
        (1 / 2 : ℝ) * (∑ i : Fin N, ∑ _j : Fin N, (1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (N : ℝ) ^ 2 / 2 := by simp; ring

/-- Measurability of the finite pair test on configuration space. -/
theorem particleTest_measurable {N : ℕ} (n : ℕ) :
    Measurable (particleTest n : SharpLSI.Config N 1 → ℝ) := by
  have hterm (i j : Fin N) :
      Measurable (fun X : SharpLSI.Config N 1 => orderedPairTerm n X i j) := by
    by_cases hij : i = j
    · simp [orderedPairTerm, hij]
    · simp only [orderedPairTerm, if_neg hij]
      exact (pairCutoff_measurable n).comp
        ((measurable_pi_apply i).sub (measurable_pi_apply j))
  unfold particleTest
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun j _ => hterm i j)

/-- The pair test is in `H¹` for every lower-bounded measurable singular Gibbs law. -/
theorem particleTest_memH1C {N : ℕ} (n : ℕ)
    (W : SharpLSI.Torus 1 → SharpLSI.Torus 1 → ℝ)
    (hWmeas : Measurable (Function.uncurry W))
    (hWlower : ∃ a : ℝ, ∀ x y, a ≤ W x y) :
    SharpLSI.MemH1C
      (SharpLSI.gibbs (fun _ : SharpLSI.Torus 1 => 0) W N) (particleTest n) := by
  have hfb : ∃ C : ℝ, 0 ≤ C ∧ ∀ X : SharpLSI.Config N 1,
      |particleTest n X| ≤ C := by
    refine ⟨(N : ℝ) ^ 2 / 2, by positivity, ?_⟩
    intro X
    rw [abs_of_nonneg (particleTest_nonneg n X)]
    exact particleTest_le n X
  have hlift : (fun v : (Fin N × Fin 1 → ℝ) =>
      particleTest n (SharpLSI.unflat (SharpLSI.liftT v))) =
      (particleTestLift n : (Fin N × Fin 1 → ℝ) → ℝ) := by
    funext v
    exact particleTest_eq_particleTestLift n v
  have hsmooth : ContDiff ℝ 1
      (fun v : (Fin N × Fin 1 → ℝ) =>
        particleTest n (SharpLSI.unflat (SharpLSI.liftT v))) := by
    rw [hlift]
    exact (particleTestLift_contDiff n).of_le (by simp)
  obtain ⟨C, hC0, hC⟩ := particleTestLift_gradient_bounded (N := N) n
  have hgrad : ∃ C : ℝ, 0 ≤ C ∧ ∀ y p,
      |(fderiv ℝ (fun v : (Fin N × Fin 1 → ℝ) =>
        particleTest n (SharpLSI.unflat (SharpLSI.liftT v)))
        (SharpLSI.secT y) (Pi.single p 1))| ≤ C := by
    refine ⟨C, hC0, fun y p => ?_⟩
    have hp : p = (p.1, 0) := by
      cases p with
      | mk i k => congr 1; exact Subsingleton.elim _ _
    have hsingle : (Pi.single p (1 : ℝ) : (Fin N × Fin 1 → ℝ)) =
        Pi.single (p.1, (0 : Fin 1)) (1 : ℝ) := by rw [hp]
    rw [hlift, hsingle]
    exact hC (SharpLSI.secT y) p.1
  exact smooth_test_memH1C_of_bounded W hWmeas hWlower (particleTest n)
    (particleTest_measurable n) hfb hsmooth hgrad

end DGPS.SingularCounterexample
