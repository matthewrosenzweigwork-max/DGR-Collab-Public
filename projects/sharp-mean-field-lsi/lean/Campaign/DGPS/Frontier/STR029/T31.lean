import DGPS.Frontier.STR029.T17
import DGPS.Frontier.STR029.T27
import DGPS.Frontier.STR029.T30

/-!
# STR029.31: The logarithmic-density expansion

## R5 notes

The graph and branches are preserved throughout. The one common interval is restricted as
in FD-006, independently of spatial order. After the restriction already made in STR029.67,
we intersect the regularity radius with the STR029.27 symmetry radius and a common
parameter-membership radius. All earlier clauses are restricted to this final interval. The parameter jet comparison below is for the
actual variable branch, using evenness of its coordinates. The normalizer is the normalized
Haar integral of exp(h cos(3t) + u(h,t)). The cubic estimate is two-sided; its constant absorbs
the harmless numerical factor in the normed-space Taylor estimate of STR029.71.
-/

open scoped ContDiff
open Topology
open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

noncomputable def harmonic_STR02931 (k n : ℕ) (a b : ℝ) : PerCm_STR02966 k :=
  PerCm_STR02966.mk (trig_STR02971 n a b) ⟨by
    intro t
    unfold trig_STR02971
    have he : (n : ℝ) * (t + 2 * Real.pi) = n * t + n * (2 * Real.pi) := by ring
    rw [he, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi], by
    unfold trig_STR02971
    exact (contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))).add
      (contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)))⟩

theorem harmonic_val_STR02931 (k n : ℕ) (a b t : ℝ) :
    (harmonic_STR02931 k n a b).val t = a * Real.cos (n * t) + b * Real.sin (n * t) := rfl

noncomputable def linearJet_STR02931 (k : ℕ) : PerCm_STR02966 k := harmonic_STR02931 k 1 2 0
noncomputable def quadraticJet_STR02931 (k : ℕ) : PerCm_STR02966 k :=
  harmonic_STR02931 k 2 (2 / 3) 0 + harmonic_STR02931 k 4 (-1 / 5) 0

theorem linearJet_val_STR02931 (k : ℕ) (t : ℝ) :
    (linearJet_STR02931 k).val t = 2 * Real.cos t := by
  simp only [linearJet_STR02931, harmonic_val_STR02931, Nat.cast_one, one_mul, zero_mul, add_zero]

theorem quadraticJet_val_STR02931 (k : ℕ) (t : ℝ) :
    (quadraticJet_STR02931 k).val t = (2 / 3) * Real.cos (2 * t) - (1 / 5) * Real.cos (4 * t) := by
  change ((2 / 3 : ℝ) * Real.cos (2 * t) + 0 * Real.sin (2 * t)) +
    ((-1 / 5 : ℝ) * Real.cos (4 * t) + 0 * Real.sin (4 * t)) = _
  ring

noncomputable def rangeIncl_STR02931 : E_STR02969 →L[ℝ] PerCm_STR02966 0 :=
  inclα0_STR02967.comp E_STR02969.subtypeL

theorem rangeIncl_val_STR02931 (w : E_STR02969) :
    (rangeIncl_STR02931 w).val = (w : PeriodicC2_STR02969).val := rfl

noncomputable def chartMap_STR02931 (ψ : Par_STR02916 → E_STR02969) (p : Par_STR02916) :
    PerCm_STR02966 0 :=
  p.1 • harmonic_STR02931 0 1 1 0 + p.2.1 • harmonic_STR02931 0 1 0 1 +
    rangeIncl_STR02931 (ψ p)

noncomputable def branchParam_STR02931 (Z : ℝ → Fin 3 → ℝ) (h : ℝ) : Par_STR02916 :=
  (h * Z h 0, h * Z h 1, h, h ^ 2 * Z h 2)

noncomputable def branchParamD_STR02931 (Z : ℝ → Fin 3 → ℝ) (h : ℝ) : Par_STR02916 :=
  (Z h 0 + h * deriv (fun x => Z x 0) h,
   Z h 1 + h * deriv (fun x => Z x 1) h, 1,
   2 * h * Z h 2 + h ^ 2 * deriv (fun x => Z x 2) h)

theorem chartMap_contDiffOn_STR02931 {ψ : Par_STR02916 → E_STR02969} {U : Set Par_STR02916}
    (hψ : ContDiffOn ℝ ∞ ψ U) : ContDiffOn ℝ ∞ (chartMap_STR02931 ψ) U :=
  ((contDiff_fst.contDiffOn.smul contDiffOn_const).add
    ((contDiff_fst.comp contDiff_snd).contDiffOn.smul contDiffOn_const)).add
    (rangeIncl_STR02931.contDiff.comp_contDiffOn hψ)

theorem chartMap_val_STR02931 (ψ : Par_STR02916 → E_STR02969) (Z : ℝ → Fin 3 → ℝ)
    (h : ℝ) : (chartMap_STR02931 ψ (branchParam_STR02931 Z h)).val =
      chartU_STR02924 ψ h (Z h) := by
  funext t
  simp only [chartMap_STR02931, branchParam_STR02931, chartU_STR02924, uT_STR02901,
    PerCm_STR02966.val_add, PerCm_STR02966.val_smul, rangeIncl_val_STR02931,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, harmonic_val_STR02931]
  simp

theorem even_deriv_zero_STR02931 {f : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (he : ∀ h ∈ Set.Ioo (-δ) δ, f (-h) = f h) : deriv f 0 = 0 := by
  have hev : (fun h => f (-h)) =ᶠ[𝓝 0] f :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨by linarith, hδ⟩) he
  have h1 := hev.deriv_eq
  rw [deriv_comp_neg, neg_zero] at h1
  linarith

theorem branchParam_hasDerivAt_STR02931 {Z : ℝ → Fin 3 → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hZ : ContDiffOn ℝ ∞ Z I) {h : ℝ} (hh : h ∈ I) :
    HasDerivAt (branchParam_STR02931 Z) (branchParamD_STR02931 Z h) h := by
  have hd : ∀ i, HasDerivAt (fun x => Z x i) (deriv (fun x => Z x i) h) h := fun i =>
    (((contDiffOn_pi.1 hZ i).differentiableOn (by simp)).differentiableAt
      (hI.mem_nhds hh)).hasDerivAt
  unfold branchParam_STR02931 branchParamD_STR02931
  convert (((hasDerivAt_id h).mul (hd 0)).prodMk
    (((hasDerivAt_id h).mul (hd 1)).prodMk
      ((hasDerivAt_id h).prodMk ((hasDerivAt_pow 2 h).mul (hd 2))))) using 1 <;>
    simp [mul_comm]

theorem branchParamD_hasDerivAt_zero_STR02931 {Z : ℝ → Fin 3 → ℝ} {η δ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hZ : ContDiffOn ℝ ∞ Z (Set.Ioo (-η) η))
    (he : ∀ h ∈ Set.Ioo (-δ) δ, Z (-h) = Z h) :
    HasDerivAt (branchParamD_STR02931 Z) (0, 0, 0, 2 * Z 0 2) 0 := by
  have h0 : (0 : ℝ) ∈ Set.Ioo (-η) η := ⟨by linarith, hη⟩
  have hZi : ∀ i, ContDiffOn ℝ ∞ (fun x => Z x i) (Set.Ioo (-η) η) := contDiffOn_pi.1 hZ
  have hd : ∀ i, HasDerivAt (fun x => Z x i) (deriv (fun x => Z x i) 0) 0 := fun i =>
    (((hZi i).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds h0)).hasDerivAt
  have hd2 : ∀ i, HasDerivAt (deriv (fun x => Z x i))
      (deriv (deriv (fun x => Z x i)) 0) 0 := fun i =>
    ((((hZi i).deriv_of_isOpen isOpen_Ioo (m := 1) (by simp)).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds h0)).hasDerivAt
  have hz : ∀ i, deriv (fun x => Z x i) 0 = 0 := fun i =>
    even_deriv_zero_STR02931 hδ (fun h hh => congrFun (he h hh) i)
  unfold branchParamD_STR02931
  convert ((hd 0).add ((hasDerivAt_id 0).mul (hd2 0))).prodMk
    (((hd 1).add ((hasDerivAt_id 0).mul (hd2 1))).prodMk
      ((hasDerivAt_const 0 (1 : ℝ)).prodMk
        ((((hasDerivAt_id 0).const_mul 2).mul (hd 2)).add
          ((hasDerivAt_pow 2 0).mul (hd2 2))))) using 1 <;>
    simp [hz]

theorem second_chain_STR02931 {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : F → G} {U : Set F} {I : Set ℝ}
    {P P1 : ℝ → F} {P2 : F} (hU : IsOpen U) (hI : IsOpen I) (h0 : (0 : ℝ) ∈ I)
    (hf : ContDiffOn ℝ ∞ f U) (hmem : ∀ x ∈ I, P x ∈ U)
    (hP : ∀ x ∈ I, HasDerivAt P (P1 x) x) (hP1 : HasDerivAt P1 P2 0) :
    deriv (deriv (fun x => f (P x))) 0 =
      (fderiv ℝ (fderiv ℝ f) (P 0) (P1 0)) (P1 0) + fderiv ℝ f (P 0) P2 := by
  have hf0 := hf.contDiffAt (hU.mem_nhds (hmem 0 h0))
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) (P 0) :=
    (hf0.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num)
  have heq : deriv (fun x => f (P x)) =ᶠ[𝓝 0]
      (fun x => fderiv ℝ f (P x) (P1 x)) := by
    filter_upwards [hI.mem_nhds h0] with x hx
    exact ((hf.contDiffAt (hU.mem_nhds (hmem x hx))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt x (hP x hx) |>.deriv
  rw [heq.deriv_eq]
  exact ((hfd.hasFDerivAt.comp_hasDerivAt 0 (hP 0 h0)).clm_apply hP1).deriv


theorem range_quadratic_STR02931 :
    rangeIncl_STR02931 (qstar_STR02971 2 0) = quadraticJet_STR02931 0 := by
  apply PerCm_STR02966.ext
  funext t
  rw [quadraticJet_val_STR02931]
  change qstarFun_STR02971 2 0 t = _
  simp [qstarFun_STR02971]
  ring

/-- The first two jets of the actual variable branch, in the common C0 carrier. -/
theorem variable_branch_jets_STR02931 {ψ : Par_STR02916 → E_STR02969}
    {U : Set Par_STR02916} {Z : ℝ → Fin 3 → ℝ} {η δ : ℝ}
    (hU : IsOpen U) (hU0 : (0 : Par_STR02916) ∈ U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0)
    (hroot : ∀ p ∈ U, Rpar_STR02916 p (ψ p) = 0)
    (hη : 0 < η) (hδ : 0 < δ) (hδη : δ ≤ η)
    (hZ : ContDiffOn ℝ ∞ Z (Set.Ioo (-η) η))
    (he : ∀ h ∈ Set.Ioo (-δ) δ, Z (-h) = Z h)
    (hZ0 : Z 0 = ![2, 0, -16 / 15])
    (hmem : ∀ h ∈ Set.Ioo (-δ) δ, branchParam_STR02931 Z h ∈ U) :
    chartMap_STR02931 ψ (branchParam_STR02931 Z 0) = 0 ∧
    deriv (fun h => chartMap_STR02931 ψ (branchParam_STR02931 Z h)) 0 = linearJet_STR02931 0 ∧
    iteratedDeriv 2 (fun h => chartMap_STR02931 ψ (branchParam_STR02931 Z h)) 0 =
      (2 : ℝ) • quadraticJet_STR02931 0 := by
  obtain ⟨ε, hε, M, hM, hall⟩ :=
    str029_71_scaled_implicit_derivatives_uniform_range_remainder hU hU0 hψ hψ0 hroot
      (K := {((2 : ℝ), (0 : ℝ), (-16 / 15 : ℝ))}) isCompact_singleton
  obtain ⟨hdom, hCC, hC0, hC1, hC2, -, -⟩ := hall 2 0 (-16 / 15) (by simp)
  let Zc : ℝ → Fin 3 → ℝ := fun _ => ![2, 0, -16 / 15]
  have hε0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hδ0 : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hη0 : (0 : ℝ) ∈ Set.Ioo (-η) η := ⟨by linarith, hη⟩
  have hsub : Set.Ioo (-δ) δ ⊆ Set.Ioo (-η) η :=
    Set.Ioo_subset_Ioo (neg_le_neg hδη) hδη
  have hZc : ContDiffOn ℝ ∞ Zc (Set.Ioo (-ε) ε) := contDiffOn_const
  have hdomc : ∀ h ∈ Set.Ioo (-ε) ε, branchParam_STR02931 Zc h ∈ U := by
    intro h hh
    exact hdom h (abs_le.2 ⟨hh.1.le, hh.2.le⟩)
  have hF := chartMap_contDiffOn_STR02931 hψ
  have hsec := second_chain_STR02931 hU isOpen_Ioo hδ0 hF hmem
    (fun h hh => branchParam_hasDerivAt_STR02931 isOpen_Ioo hZ (hsub hh))
    (branchParamD_hasDerivAt_zero_STR02931 hη hδ hZ he)
  have hsecc := second_chain_STR02931 hU isOpen_Ioo hε0 hF hdomc
    (fun h hh => branchParam_hasDerivAt_STR02931 isOpen_Ioo hZc hh)
    (branchParamD_hasDerivAt_zero_STR02931 hε hε hZc (fun _ _ => rfl))
  have hsecond : iteratedDeriv 2 (fun h => chartMap_STR02931 ψ (branchParam_STR02931 Z h)) 0 =
      iteratedDeriv 2 (fun h => chartMap_STR02931 ψ (branchParam_STR02931 Zc h)) 0 := by
    rw [iteratedDeriv_two_STR02971, iteratedDeriv_two_STR02971, hsec, hsecc]
    simp [branchParam_STR02931, branchParamD_STR02931, hZ0, Zc]
  have hfirst : deriv (fun h => chartMap_STR02931 ψ (branchParam_STR02931 Z h)) 0 =
      deriv (fun h => chartMap_STR02931 ψ (branchParam_STR02931 Zc h)) 0 := by
    have hfp := (hF.contDiffAt (hU.mem_nhds (hmem 0 hδ0))).differentiableAt (by simp)
    have hfc := (hF.contDiffAt (hU.mem_nhds (hdomc 0 hε0))).differentiableAt (by simp)
    have h1 := hfp.hasFDerivAt.comp_hasDerivAt 0
      (branchParam_hasDerivAt_STR02931 isOpen_Ioo hZ hη0)
    have h2 := hfc.hasFDerivAt.comp_hasDerivAt 0
      (branchParam_hasDerivAt_STR02931 isOpen_Ioo hZc hε0)
    have e1 : deriv (fun h => chartMap_STR02931 ψ (branchParam_STR02931 Z h)) 0 =
        fderiv ℝ (chartMap_STR02931 ψ) ((0, 0, 0, 0) : Par_STR02916) (2, 0, 1, 0) := by
      simpa [Function.comp_def, branchParam_STR02931, branchParamD_STR02931, hZ0] using h1.deriv
    have e2 : deriv (fun h => chartMap_STR02931 ψ (branchParam_STR02931 Zc h)) 0 =
        fderiv ℝ (chartMap_STR02931 ψ) ((0, 0, 0, 0) : Par_STR02916) (2, 0, 1, 0) := by
      simpa [Function.comp_def, branchParam_STR02931, branchParamD_STR02931, Zc] using h2.deriv
    exact e1.trans e2.symm
  have hfixed : (fun h => chartMap_STR02931 ψ (branchParam_STR02931 Zc h)) =
      (fun h => h • linearJet_STR02931 0 +
        rangeIncl_STR02931 (scaledCurve_STR02971 ψ 2 0 (-16 / 15) h)) := by
    funext h
    apply PerCm_STR02966.ext
    funext t
    simp only [chartMap_STR02931, branchParam_STR02931, Zc,
      scaledCurve_STR02971, PerCm_STR02966.val_add, PerCm_STR02966.val_smul,
      rangeIncl_val_STR02931, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      harmonic_val_STR02931, linearJet_val_STR02931]
    simp
    ring

  have hCO : ContDiffOn ℝ ∞ (scaledCurve_STR02971 ψ 2 0 (-16 / 15)) (Set.Ioo (-ε) ε) :=
    hCC.mono Set.Ioo_subset_Icc_self
  have hCA := hCO.contDiffAt (isOpen_Ioo.mem_nhds hε0)
  have hLC : ContDiffAt ℝ 2 (fun h : ℝ => h • linearJet_STR02931 0) 0 := by fun_prop
  have hRC : ContDiffAt ℝ 2
      (fun h => rangeIncl_STR02931 (scaledCurve_STR02971 ψ 2 0 (-16 / 15) h)) 0 :=
    (rangeIncl_STR02931.contDiff.contDiffAt.comp 0 hCA).of_le (by simp)
  have hrange2 := iteratedDeriv_clm_STR02967 rangeIncl_STR02931 isOpen_Ioo hCO
    (i := 2) (by simp) hε0
  refine ⟨?_, ?_, ?_⟩
  · have hp : branchParam_STR02931 Z 0 = (0 : Par_STR02916) := by
      simp [branchParam_STR02931]
    rw [hp]
    unfold chartMap_STR02931
    rw [hψ0]
    simp
  · rw [hfirst, hfixed]
    have hl : HasDerivAt (fun h : ℝ => h • linearJet_STR02931 0) (linearJet_STR02931 0) 0 :=
      by simpa using (hasDerivAt_id (0 : ℝ)).smul_const (linearJet_STR02931 0)
    have hr := rangeIncl_STR02931.hasFDerivAt.comp_hasDerivAt 0
      (hCA.differentiableAt (by simp)).hasDerivAt
    simpa [hC1, Function.comp_def, Pi.add_apply] using (hl.fun_add hr).deriv
  · rw [hsecond, hfixed, iteratedDeriv_fun_add hLC hRC,
      iteratedDeriv_smul_const (by fun_prop) (linearJet_STR02931 0), hrange2, hC2]
    simp [range_quadratic_STR02931, iteratedDeriv_fun_id]


theorem inclusion_injective_STR02931 (k : ℕ) : Function.Injective (incl0_STR02967 k) := by
  intro f g h
  apply PerCm_STR02966.ext
  have hv := congrArg (fun x : PerCm_STR02966 0 => x.val) h
  exact hv

theorem linearJet_incl_STR02931 (k : ℕ) :
    incl0_STR02967 k (linearJet_STR02931 k) = linearJet_STR02931 0 := by
  apply PerCm_STR02966.ext
  rfl

theorem quadraticJet_incl_STR02931 (k : ℕ) :
    incl0_STR02967 k (quadraticJet_STR02931 k) = quadraticJet_STR02931 0 := by
  apply PerCm_STR02966.ext
  rfl

/-- Equality of the underlying functions transports the jets without identifying independently
chosen lifts. -/
theorem lift_jets_STR02931 {ψ : Par_STR02916 → E_STR02969} {Z : ℝ → Fin 3 → ℝ}
    {δ : ℝ} {k : ℕ} {W : ℝ → PerCm_STR02966 k} (hδ : 0 < δ)
    (hW : ContDiffOn ℝ 3 W (Set.Ioo (-δ) δ))
    (hv : ∀ h ∈ Set.Ioo (-δ) δ, (W h).val = chartU_STR02924 ψ h (Z h))
    (h0 : chartMap_STR02931 ψ (branchParam_STR02931 Z 0) = 0)
    (h1 : deriv (fun h => chartMap_STR02931 ψ (branchParam_STR02931 Z h)) 0 = linearJet_STR02931 0)
    (h2 : iteratedDeriv 2 (fun h => chartMap_STR02931 ψ (branchParam_STR02931 Z h)) 0 =
      (2 : ℝ) • quadraticJet_STR02931 0) :
    W 0 = 0 ∧ deriv W 0 = linearJet_STR02931 k ∧
      iteratedDeriv 2 W 0 = (2 : ℝ) • quadraticJet_STR02931 k := by
  have hz : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have heq : Set.EqOn (fun h => incl0_STR02967 k (W h))
      (fun h => chartMap_STR02931 ψ (branchParam_STR02931 Z h)) (Set.Ioo (-δ) δ) := by
    intro h hh
    apply PerCm_STR02966.ext
    exact (hv h hh).trans (chartMap_val_STR02931 ψ Z h).symm
  have hj : ∀ i : ℕ, i ≤ 2 → incl0_STR02967 k (iteratedDeriv i W 0) =
      iteratedDeriv i (fun h => chartMap_STR02931 ψ (branchParam_STR02931 Z h)) 0 := by
    intro i hi
    rw [← iteratedDeriv_clm_STR02967 (incl0_STR02967 k) isOpen_Ioo hW
      (by exact_mod_cast (show i ≤ 3 by omega)) hz]
    exact heq.iteratedDeriv_of_isOpen isOpen_Ioo i hz
  refine ⟨inclusion_injective_STR02931 k ?_, inclusion_injective_STR02931 k ?_,
    inclusion_injective_STR02931 k ?_⟩
  · simpa using (hj 0 (by omega)).trans h0
  · rw [linearJet_incl_STR02931]
    have e := hj 1 (by omega)
    simp only [iteratedDeriv_one] at e
    exact e.trans h1
  · simpa [quadraticJet_incl_STR02931] using (hj 2 (by omega)).trans h2

/-- A normed-space cubic Taylor bound on any smaller symmetric compact interval. -/
theorem cubic_taylor_STR02931 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W : ℝ → F} {δ : ℝ} {v q : F} (hδ : 0 < δ)
    (hW : ContDiffOn ℝ 3 W (Set.Ioo (-δ) δ)) (hW0 : W 0 = 0)
    (hW1 : deriv W 0 = v) (hW2 : iteratedDeriv 2 W 0 = (2 : ℝ) • q)
    {d : ℝ} (hd : 0 ≤ d) (hdδ : d < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, |h| ≤ d →
      ‖W h - h • v - h ^ 2 • q‖ ≤ C * |h| ^ 3 := by
  let f : ℝ → F := fun h => W h - h • v
  have hf : ContDiffOn ℝ 3 f (Set.Ioo (-δ) δ) := hW.sub (contDiffOn_id.smul contDiffOn_const)
  have hsub : Set.Icc (-d) d ⊆ Set.Ioo (-δ) δ :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h0 : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hd1 := hf.deriv_of_isOpen isOpen_Ioo (m := 2) (by norm_num)
  have hd2 := hd1.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hD : ∀ x ∈ Set.Ioo (-δ) δ, HasDerivAt f (deriv f x) x := fun x hx =>
    ((hf.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hD1 : ∀ x ∈ Set.Ioo (-δ) δ, HasDerivAt (deriv f) (deriv (deriv f) x) x := fun x hx =>
    ((hd1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hD2 : ∀ x ∈ Set.Ioo (-δ) δ,
      HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) x) x := fun x hx =>
    ((hd2.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  obtain ⟨M, hM⟩ := third_bdd_STR02967 isOpen_Ioo hf hsub
  have hMpos : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨by linarith, hd⟩)
  have hf0 : f 0 = 0 := by simp [f, hW0]
  have hf1 : deriv f 0 = 0 := by
    have hl : HasDerivAt (fun h : ℝ => h • v) v 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    have hw := ((hW.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds h0)).hasDerivAt
    simpa [f, hW1, Pi.sub_apply] using (hw.fun_sub hl).deriv
  have hf2 : deriv (deriv f) 0 = (2 : ℝ) • q := by
    rw [← iteratedDeriv_two_STR02971]
    have hWA : ContDiffAt ℝ 2 W 0 := (hW.contDiffAt (isOpen_Ioo.mem_nhds h0)).of_le (by norm_num)
    have hLA : ContDiffAt ℝ 2 (fun h : ℝ => h • v) 0 := by fun_prop
    rw [show f = fun h => W h - h • v from rfl, iteratedDeriv_fun_sub hWA hLA,
      iteratedDeriv_smul_const (by fun_prop) v, hW2]
    simp [iteratedDeriv_fun_id]
  refine ⟨M, hMpos, fun h hh => ?_⟩
  have he := taylor_remainder_STR02971 hMpos hf0 hf1
    (fun y hy => hD y (hsub (abs_le.1 hy)))
    (fun y hy => hD1 y (hsub (abs_le.1 hy)))
    (fun y hy => hD2 y (hsub (abs_le.1 hy)))
    (fun y hy => by simpa [iteratedDeriv_three_STR02971] using hM y (abs_le.1 hy)) hh
  simpa [f, hf2, smul_smul] using he

noncomputable def normalizer_STR02931 (ψ : Par_STR02916 → E_STR02969)
    (Z : ℝ → Fin 3 → ℝ) (h : ℝ) : ℝ :=
  meanT_STR02901 (fun t => Real.exp (h * Real.cos (3 * t) + chartU_STR02924 ψ h (Z h) t))

theorem log_density_identity_STR02931 (ψ : Par_STR02916 → E_STR02969)
    (Z : ℝ → Fin 3 → ℝ) (h t : ℝ) :
    Real.log (rhoT_STR02901 h (chartU_STR02924 ψ h (Z h)) t) +
      Real.log (normalizer_STR02931 ψ Z h) = h * Real.cos (3 * t) + chartU_STR02924 ψ h (Z h) t := by
  have hlog := (gate_str029_01_bind_common_optimizer_witness_absolute_variational_positive_log h
    (chartU_isC2_STR02924 ψ h (Z h)).2.1.continuous t).2
  rw [hlog]
  simp [normalizer_STR02931]

noncomputable def logRemainder_STR02931 (ψ : Par_STR02916 → E_STR02969)
    (Z : ℝ → Fin 3 → ℝ) (h : ℝ) : ℝ → ℝ := fun t =>
  Real.log (rhoT_STR02901 h (chartU_STR02924 ψ h (Z h)) t) +
    Real.log (normalizer_STR02931 ψ Z h) - h * (Real.cos (3 * t) + 2 * Real.cos t) -
    h ^ 2 * ((2 / 3) * Real.cos (2 * t) - (1 / 5) * Real.cos (4 * t))

theorem expansion_from_jets_STR02931 {ψ : Par_STR02916 → E_STR02969}
    {Z : ℝ → Fin 3 → ℝ} {δ : ℝ} {k : ℕ} {W : ℝ → PerCm_STR02966 k}
    (hδ : 0 < δ) (hW : ContDiffOn ℝ 3 W (Set.Ioo (-δ) δ))
    (hv : ∀ h ∈ Set.Ioo (-δ) δ, (W h).val = chartU_STR02924 ψ h (Z h))
    (hW0 : W 0 = 0) (hW1 : deriv W 0 = linearJet_STR02931 k)
    (hW2 : iteratedDeriv 2 W 0 = (2 : ℝ) • quadraticJet_STR02931 k)
    {d : ℝ} (hd : 0 ≤ d) (hdδ : d < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, |h| ≤ d →
      cmN_STR02966 k (logRemainder_STR02931 ψ Z h) ≤ C * |h| ^ 3 := by
  obtain ⟨C, hC, hest⟩ := cubic_taylor_STR02931 hδ hW hW0 hW1 hW2 hd hdδ
  refine ⟨C, hC, fun h hh => ?_⟩
  have hhI : h ∈ Set.Ioo (-δ) δ := ⟨by linarith [(abs_le.1 hh).1], by linarith [(abs_le.1 hh).2]⟩
  have heq : (W h - h • linearJet_STR02931 k - h ^ 2 • quadraticJet_STR02931 k).val =
      logRemainder_STR02931 ψ Z h := by
    funext t
    rw [PerCm_STR02966.val_sub, PerCm_STR02966.val_sub,
      PerCm_STR02966.val_smul, PerCm_STR02966.val_smul, hv h hhI]
    change chartU_STR02924 ψ h (Z h) t - h * (linearJet_STR02931 k).val t -
      h ^ 2 * (quadraticJet_STR02931 k).val t = _
    rw [linearJet_val_STR02931, quadraticJet_val_STR02931]
    simp only [logRemainder_STR02931, log_density_identity_STR02931]
    ring

  rw [← heq, ← PerCm_STR02966.norm_def]
  exact hest h hh

/-- A reusable same-data interface: the regularity lift is for these very graph and branch
witnesses. The conclusion chooses a common interval independently of k. -/
theorem str029_31_required_logarithmic_density_expansion_of_data
    {U : Set Par_STR02916} {V : Set E_STR02969} {ψ : Par_STR02916 → E_STR02969}
    {O : Set (ℝ × (Fin 3 → ℝ))} {E : ℝ × (Fin 3 → ℝ) → ℝ} {η δ : ℝ}
    {N : Fin 3 → Set (Fin 3 → ℝ)} {Z : Fin 3 → ℝ → (Fin 3 → ℝ)}
    (hUo : IsOpen U) (hU0 : (0 : Par_STR02916) ∈ U) (hVo : IsOpen V)
    (hV0 : (0 : E_STR02969) ∈ V) (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0)
    (hψV : ∀ p ∈ U, ψ p ∈ V)
    (hR : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p)
    (hOo : IsOpen O) (hOmem : ∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O) (hEC : ContDiffOn ℝ ∞ E O)
    (hval : ∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
      E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4)
    (hzero : ∀ z : Fin 3 → ℝ, E ((0 : ℝ), z) =
      Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2))
    (hη : 0 < η) (hn0 : N 0 ∈ 𝓝 (![2, 0, -16 / 15] : Fin 3 → ℝ))
    (hsym : ∀ z : Fin 3 → ℝ, z ∈ N 0 ↔ (![z 0, -z 1, z 2] : Fin 3 → ℝ) ∈ N 0)
    (hZC : ∀ j : Fin 3, ContDiffOn ℝ ∞ (Z j) (Set.Ioo (-η) η))
    (hZN : ∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, Z j h ∈ N j)
    (hKuniq : ∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, ∀ z ∈ N j,
      Kfun_STR02923 E (h, z) = 0 ↔ z = Z j h)
    (hδ : 0 < δ) (hδη : δ ≤ η)
    (hreg : ∀ k : ℕ, ∃ W : ℝ → PerCm_STR02966 k,
      ContDiffOn ℝ 3 W (Set.Ioo (-δ) δ) ∧
      ∀ h ∈ Set.Ioo (-δ) δ, (W h).val = chartU_STR02924 ψ h (Z 0 h)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ ∧ ∀ k : ℕ, ∀ d : ℝ, 0 ≤ d → d < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, |h| ≤ d →
        cmN_STR02966 k (logRemainder_STR02931 ψ (Z 0) h) ≤ C * |h| ^ 3 := by
  obtain ⟨σ, hσ, hση, hsymmetry⟩ := str029_27_reflection_sign_symmetry_branches_of_data
    hUo hU0 hVo hV0 hR hOo hOmem hEC hval hzero hη hn0 hsym hZC hZN hKuniq
  obtain ⟨τ, hτ, hτmem⟩ := eventually_param_mem_STR02967 hUo hU0 hη hZC
  let ε := min δ (min σ τ)
  have hε : 0 < ε := lt_min hδ (lt_min hσ hτ)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεσ : ε ≤ σ := (min_le_right _ _).trans (min_le_left _ _)
  have hετ : ε ≤ τ := (min_le_right _ _).trans (min_le_right _ _)
  have hεη : ε ≤ η := hεδ.trans hδη
  have hsubδ : Set.Ioo (-ε) ε ⊆ Set.Ioo (-δ) δ := Set.Ioo_subset_Ioo (neg_le_neg hεδ) hεδ
  have hsubσ : Set.Ioo (-ε) ε ⊆ Set.Ioo (-σ) σ := Set.Ioo_subset_Ioo (neg_le_neg hεσ) hεσ
  have hsubτ : Set.Ioo (-ε) ε ⊆ Set.Ioo (-τ) τ := Set.Ioo_subset_Ioo (neg_le_neg hετ) hετ
  have hη0 : (0 : ℝ) ∈ Set.Ioo (-η) η := ⟨by linarith, hη⟩
  have hZ0 : Z 0 0 = ![2, 0, -16 / 15] := by
    have hK := (str029_22_invertible_finite_dimensional_jacobian_of_slice E hzero).1
    exact ((hKuniq 0 0 hη0 _ (mem_of_mem_nhds hn0)).mp hK).symm
  obtain ⟨hj0, hj1, hj2⟩ := variable_branch_jets_STR02931 hUo hU0 hψ hψ0
    (fun p hp => (hR p hp _ (hψV p hp)).mpr rfl)
    hη hε hεη (hZC 0) (fun h hh => (hsymmetry h (hsubσ hh)).2.1 0) hZ0
    (fun h hh => hτmem 0 h (hsubτ hh))
  refine ⟨ε, hε, hεδ, fun k d hd hdε => ?_⟩
  obtain ⟨W, hW, hv⟩ := hreg k
  have hWε := hW.mono hsubδ
  have hvε : ∀ h ∈ Set.Ioo (-ε) ε, (W h).val = chartU_STR02924 ψ h (Z 0 h) :=
    fun h hh => hv h (hsubδ hh)
  obtain ⟨hW0, hW1, hW2⟩ := lift_jets_STR02931 hε hWε hvε hj0 hj1 hj2
  exact expansion_from_jets_STR02931 hε hWε hvε hW0 hW1 hW2 hd hdε


theorem str029_31_required_logarithmic_density_expansion :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      ∃ (O : Set (ℝ × (Fin 3 → ℝ))) (E : ℝ × (Fin 3 → ℝ) → ℝ),
        IsOpen O ∧ (∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O) ∧ ContDiffOn ℝ ∞ E O ∧
        (∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
          E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4) ∧
        (∀ z : Fin 3 → ℝ, E ((0 : ℝ), z) =
          Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2)) ∧
        ∃ η : ℝ, 0 < η ∧
          ∃ (N : Fin 3 → Set (Fin 3 → ℝ)) (Z : Fin 3 → ℝ → (Fin 3 → ℝ)),
            IsOpen (N 0) ∧ IsOpen (N 1) ∧ IsOpen (N 2) ∧
            N 0 ∈ 𝓝 (![2, 0, -16 / 15] : Fin 3 → ℝ) ∧
            N 1 ∈ 𝓝 (![-1, Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) ∧
            N 2 ∈ 𝓝 (![-1, -Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) ∧
            (∀ i j : Fin 3, i ≠ j → Disjoint (N i) (N j)) ∧
            (∀ z : Fin 3 → ℝ, z ∈ N 0 ↔ (![z 0, -z 1, z 2] : Fin 3 → ℝ) ∈ N 0) ∧
            N 1 = rot_STR02923 '' N 0 ∧ N 2 = rot_STR02923 '' N 1 ∧
            (∀ j : Fin 3, ContDiffOn ℝ ∞ (Z j) (Set.Ioo (-η) η)) ∧
            (∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, Z j h ∈ N j) ∧
            (∀ h ∈ Set.Ioo (-η) η, Z 1 h = rot_STR02923 (Z 0 h) ∧ Z 2 h = rot_STR02923 (Z 1 h)) ∧
            (∀ h ∈ Set.Ioo (-η) η, ∀ j : Fin 3, Z j h 2 = Z 0 h 2) ∧
            (∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, ∀ z ∈ N j,
              Kfun_STR02923 E (h, z) = 0 ↔ z = Z j h) ∧
            ∃ δ : ℝ, 0 < δ ∧ δ ≤ η ∧
              (∀ h ∈ Set.Ioo (-δ) δ, ∀ j : Fin 3,
                (∀ t, 0 < rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)) t) ∧
                (∀ t, gradG_STR02950 h (h ^ 2 * Z j h 2) (chartU_STR02924 ψ h (Z j h)) t = 0) ∧
                (h ≠ 0 →
                  0 < entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) ∧
                  fisherChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) /
                    (2 * entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h))) =
                    1 + h ^ 2 * Z j h 2)) ∧
              (∀ h ∈ Set.Ioo (-δ) δ, h ≠ 0 → ∀ i j : Fin 3, i ≠ j →
                rhoT_STR02901 h (chartU_STR02924 ψ h (Z i h)) ≠
                  rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h))) ∧
              (∀ j : Fin 3, rhoT_STR02901 0 (chartU_STR02924 ψ 0 (Z j 0)) = qT_STR02901 0 ∧
                ∀ t, gradG_STR02950 0 0 (chartU_STR02924 ψ 0 (Z j 0)) t = 0) ∧
              (∀ h ∈ Set.Ioo (-δ) δ, ∀ t,
                deriv (deriv (chartU_STR02924 ψ h (Z 0 h))) t =
                  P0_STR02964
                    (eulerF_STR02964 h (1 + h ^ 2 * Z 0 h 2) (chartU_STR02924 ψ h (Z 0 h))) t) ∧
              (∀ j : Fin 3, ∃ Uα : ℝ → PeriodicC2_STR02969,
                ContDiffOn ℝ ∞ Uα (Set.Ioo (-δ) δ) ∧
                (∀ h ∈ Set.Ioo (-δ) δ, (Uα h).val = chartU_STR02924 ψ h (Z j h)) ∧
                ∀ k : ℕ, ∃ W : ℝ → PerCm_STR02966 k, ContDiffOn ℝ 3 W (Set.Ioo (-δ) δ) ∧
                  (∀ h ∈ Set.Ioo (-δ) δ, (W h).val = chartU_STR02924 ψ h (Z j h)) ∧
                  (∀ h ∈ Set.Ioo (-δ) δ, ∀ i : ℕ, i ≤ 2 →
                    incl0_STR02967 k (iteratedDeriv i W h) =
                      inclα0_STR02967 (iteratedDeriv i Uα h)) ∧
                  (∀ a b : ℝ, Set.Icc a b ⊆ Set.Ioo (-δ) δ →
                    ∃ M : ℝ, ∀ h ∈ Set.Icc a b, ‖iteratedDeriv 3 W h‖ ≤ M)) ∧
              (∀ k : ℕ, ∀ d : ℝ, 0 ≤ d → d < δ →
                ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, |h| ≤ d →
                  cmN_STR02966 k (logRemainder_STR02931 ψ (Z 0) h) ≤ C * |h| ^ 3) := by
  obtain ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo, hOmem, hEC,
    hval, hzero, η, hη, N, Z, hN0, hN1, hN2, hn0, hn1, hn2, hdisj, hsym, hrot1, hrot2,
    hZC, hZN, hZrot, hZs, hKuniq, δ, hδ, hδη, hA, hB, hC, hD, hreg⟩ :=
    str029_30_higher_norm_parameter_regularity_same_interval
  have hreg0 : ∀ k : ℕ, ∃ W : ℝ → PerCm_STR02966 k,
      ContDiffOn ℝ 3 W (Set.Ioo (-δ) δ) ∧
      ∀ h ∈ Set.Ioo (-δ) δ, (W h).val = chartU_STR02924 ψ h (Z 0 h) := by
    intro k
    obtain ⟨Uα, hUα, hvα, hks⟩ := hreg 0
    obtain ⟨W, hW, hv, hj, hb⟩ := hks k
    exact ⟨W, hW, hv⟩
  obtain ⟨ε, hε, hεδ, hexp⟩ := str029_31_required_logarithmic_density_expansion_of_data
    hUo hU0 hVo hV0 hψC hψ0 hψV hR hOo hOmem hEC hval hzero hη hn0 hsym
    hZC hZN hKuniq hδ hδη hreg0
  have hsub : Set.Ioo (-ε) ε ⊆ Set.Ioo (-δ) δ :=
    Set.Ioo_subset_Ioo (neg_le_neg hεδ) hεδ
  refine ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo, hOmem, hEC,
    hval, hzero, η, hη, N, Z, hN0, hN1, hN2, hn0, hn1, hn2, hdisj, hsym, hrot1, hrot2,
    hZC, hZN, hZrot, hZs, hKuniq, ε, hε, hεδ.trans hδη,
    (fun h hh => hA h (hsub hh)), (fun h hh => hB h (hsub hh)), hC,
    (fun h hh => hD h (hsub hh)), ?_, hexp⟩
  intro j
  obtain ⟨Uα, hUα, hvα, hks⟩ := hreg j
  refine ⟨Uα, hUα.mono hsub, (fun h hh => hvα h (hsub hh)), fun k => ?_⟩
  obtain ⟨W, hW, hv, hj, hb⟩ := hks k
  exact ⟨W, hW.mono hsub, (fun h hh => hv h (hsub hh)),
    (fun h hh => hj h (hsub hh)), fun a b hab => hb a b (hab.trans hsub)⟩

end DGPS.Frontier.STR029
