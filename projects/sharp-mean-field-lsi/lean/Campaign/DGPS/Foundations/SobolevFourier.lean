import DGPS.Foundations.PeriodicSmoothing
import SharpSymmetricLSI.Paper.FourierSynth

/-!
# FOU004: Periodic Sobolev Fourier identity

On the unit torus: `u ∈ H¹` iff `∑ 4π²|k|²|û(k)|² < ∞`, with `‖∇u‖² = ∑ 4π²|k|²|û(k)|²` and
`\widehat{∂ⱼu}(k) = 2πi kⱼ û(k)`; conversely an `L²` function with finite weighted sum has exactly
those weak `L²` derivatives; Euclidean-ball Fourier cutoffs converge in `H¹` and their gradient
norm is exactly the partial sum over `|k| ≤ R`.
-/

open MeasureTheory Filter Topology
open scoped Real ComplexConjugate ENNReal

namespace DGPS

variable {d : ℕ}

/-- The Fourier coefficient `û(k) = ∫ e^{-2πi k·x} u(x) dm` of a real function on `𝕋^d`. -/
noncomputable abbrev fourierCoeff (u : Torus d → ℝ) (k : Fin d → ℤ) : ℂ :=
  UnitAddTorus.mFourierCoeff (fun y => (u y : ℂ)) k

/-- The Fourier weight `4π²|k|² = 4π² ∑ⱼ kⱼ²` of the Euclidean gradient energy. -/
noncomputable def gradWeight (k : Fin d → ℤ) : ℝ := 4 * π ^ 2 * ∑ j, ((k j : ℤ) : ℝ) ^ 2

/-- `u` has finite Fourier gradient energy: `∑ₖ 4π²|k|²|û(k)|² < ∞`. -/
def FiniteFourierEnergy (u : Torus d → ℝ) : Prop :=
  Summable fun k : Fin d → ℤ => gradWeight k * ‖fourierCoeff u k‖ ^ 2

/-- The frequency `k` lies in the Euclidean ball `|k| ≤ R`. -/
def InFreqBall (R : ℝ) (k : Fin d → ℤ) : Prop := Real.sqrt (∑ j, ((k j : ℤ) : ℝ) ^ 2) ≤ R

noncomputable instance (R : ℝ) (k : Fin d → ℤ) : Decidable (InFreqBall R k) :=
  Real.decidableLE _ _

/-- Keep the coefficients with `|k| ≤ R`. -/
noncomputable def cutCoeff (c : (Fin d → ℤ) → ℂ) (R : ℝ) (k : Fin d → ℤ) : ℂ :=
  if InFreqBall R k then c k else 0

/-- The Fourier cutoff `S_R u = Re ∑_{|k| ≤ R} û(k) e_k`. -/
noncomputable def fourierCutoff (u : Torus d → ℝ) (R : ℝ) : Torus d → ℝ :=
  SharpLSI.psum (cutCoeff (fourierCoeff u) R) ⌈R⌉₊

/-- The componentwise Fourier cutoff of a vector field. -/
noncomputable def fourierCutoffGrad (g : Torus d → Tangent d) (R : ℝ) : Torus d → Tangent d :=
  fun x => WithLp.toLp 2 fun j => fourierCutoff (fun y => g y j) R x

/-! ### Cutoff coefficients -/

theorem InFreqBall.neg {R : ℝ} {k : Fin d → ℤ} (h : InFreqBall R k) : InFreqBall R (-k) := by
  simpa [InFreqBall] using h

theorem inFreqBall_neg_iff {R : ℝ} {k : Fin d → ℤ} : InFreqBall R (-k) ↔ InFreqBall R k := by
  simp [InFreqBall]

theorem InFreqBall.mem_box {R : ℝ} {k : Fin d → ℤ} (h : InFreqBall R k) :
    k ∈ SharpLSI.box (ι := Fin d) ⌈R⌉₊ := by
  simp only [SharpLSI.box, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h1 : |((k i : ℤ) : ℝ)| ≤ R := by
    refine le_trans ?_ h
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => ((k j : ℤ) : ℝ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  have h2 : |((k i : ℤ) : ℝ)| ≤ ((⌈R⌉₊ : ℤ) : ℝ) := by
    refine h1.trans ?_
    have := Nat.le_ceil R
    exact_mod_cast this
  have h3 := abs_le.mp h2
  constructor
  · exact_mod_cast h3.1
  · exact_mod_cast h3.2

theorem norm_sq_cutCoeff (c : (Fin d → ℤ) → ℂ) (R : ℝ) (k : Fin d → ℤ) :
    ‖cutCoeff c R k‖ ^ 2 = if InFreqBall R k then ‖c k‖ ^ 2 else 0 := by
  unfold cutCoeff; split_ifs <;> simp

theorem cutCoeff_mul (a c : (Fin d → ℤ) → ℂ) (R : ℝ) (k : Fin d → ℤ) :
    cutCoeff (fun k => a k * c k) R k = a k * cutCoeff c R k := by
  unfold cutCoeff; split_ifs <;> simp

theorem cutCoeff_symm {c : (Fin d → ℤ) → ℂ} (hc : ∀ k, c (-k) = conj (c k)) (R : ℝ)
    (k : Fin d → ℤ) : cutCoeff c R (-k) = conj (cutCoeff c R k) := by
  unfold cutCoeff
  by_cases h : InFreqBall R k
  · simp [h, inFreqBall_neg_iff.mpr h, hc]
  · have : ¬ InFreqBall R (-k) := fun h' => h (inFreqBall_neg_iff.mp h')
    simp [h, this]

theorem fourierCoeff_neg (u : Torus d → ℝ) (k : Fin d → ℤ) :
    fourierCoeff u (-k) = conj (fourierCoeff u k) :=
  SharpLSI.cf_neg u k

theorem fourierCoeff_fourierCutoff (u : Torus d → ℝ) (R : ℝ) (k : Fin d → ℤ) :
    fourierCoeff (fourierCutoff u R) k = cutCoeff (fourierCoeff u) R k := by
  have h := SharpLSI.cf_psum (ι := Fin d) (cutCoeff_symm (fourierCoeff_neg u) R) ⌈R⌉₊ k
  change SharpLSI.cf _ k = _ at *
  unfold fourierCutoff
  refine h.trans ?_
  by_cases hk : k ∈ SharpLSI.box (ι := Fin d) ⌈R⌉₊
  · simp [hk]
  · have : ¬ InFreqBall R k := fun h' => hk h'.mem_box
    simp [hk, cutCoeff, this]

/-! ### Trigonometric polynomials -/

theorem isSmoothPeriodic_psum (c : (Fin d → ℤ) → ℂ) (N : ℕ) :
    IsSmoothPeriodic (SharpLSI.psum c N) :=
  SharpLSI.contDiff_psum c N

theorem coordPartial_psum (c : (Fin d → ℤ) → ℂ) (N : ℕ) (j : Fin d) (x : Torus d) :
    coordPartial j (SharpLSI.psum c N) x =
      SharpLSI.psum (fun k => 2 * π * Complex.I * (k j : ℂ) * c k) N x := by
  unfold coordPartial
  rw [SharpLSI.fderiv_psum, SharpLSI.liftT_secT]

/-! ### Convergence of pairings with bounded tests -/

theorem exists_abs_le_of_continuous {ψ : Torus d → ℝ} (hψ : Continuous ψ) :
    ∃ C, ∀ x, |ψ x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hψ.continuousOn
  exact ⟨C, fun x => by simpa using hC x (Set.mem_univ x)⟩

theorem tendsto_integral_mul_of_lintegral {ι : Type*} {l : Filter ι} {F : ι → Torus d → ℝ}
    {f ψ : Torus d → ℝ} {C : ℝ} (hF : ∀ i, Integrable (F i) (haar d))
    (hf : Integrable f (haar d)) (hψm : Continuous ψ) (hψ : ∀ x, |ψ x| ≤ C)
    (hT : Tendsto (fun i => ∫⁻ y, ‖F i y - f y‖ₑ ∂haar d) l (𝓝 0)) :
    Tendsto (fun i => ∫ y, F i y * ψ y ∂haar d) l (𝓝 (∫ y, f y * ψ y ∂haar d)) := by
  have hbdd : ∀ {G : Torus d → ℝ}, Integrable G (haar d) → Integrable (fun y => G y * ψ y) (haar d) :=
    fun {G} hG => hG.mul_bdd (c := C) hψm.aestronglyMeasurable
      (Eventually.of_forall fun y => by simpa using hψ y)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hC : 0 ≤ C := (abs_nonneg _).trans (hψ (Classical.arbitrary _))
  have hlim := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT).const_mul C
  simp only [ENNReal.toReal_zero, mul_zero] at hlim
  refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hlim
  have e : ∫ y, F i y * ψ y ∂haar d - ∫ y, f y * ψ y ∂haar d
      = ∫ y, (F i y - f y) * ψ y ∂haar d := by
    simp_rw [sub_mul]; rw [integral_sub (hbdd (hF i)) (hbdd hf)]
  have hsub : Integrable (fun y => F i y - f y) (haar d) := (hF i).sub hf
  rw [e]
  refine (norm_integral_le_of_norm_le (g := fun y => C * ‖F i y - f y‖)
    (hsub.norm.const_mul C) (Eventually.of_forall fun y => ?_)).trans ?_
  · show ‖(F i y - f y) * ψ y‖ ≤ C * ‖F i y - f y‖
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hψ y) (norm_nonneg _)
  · rw [integral_const_mul, integral_norm_eq_lintegral_enorm hsub.aestronglyMeasurable]
    simp only [Function.comp_def]
    exact le_rfl

/-! ### The converse: the weak derivative identity from Fourier coefficients -/

theorem ibp_of_fourierCoeff {f h : Torus d → ℝ} (hf : MemLp f 2 (haar d)) (hh : MemLp h 2 (haar d))
    (j : Fin d)
    (hcoef : ∀ k, fourierCoeff h k = 2 * π * Complex.I * (k j : ℂ) * fourierCoeff f k)
    {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) :
    ∫ x, f x * coordPartial j φ x ∂haar d = -∫ x, h x * φ x ∂haar d := by
  obtain ⟨C₁, hC₁⟩ := exists_abs_le_of_continuous (hφ.continuous_coordPartial j)
  obtain ⟨C₂, hC₂⟩ := exists_abs_le_of_continuous hφ.continuous_torus
  have hfi : Integrable f (haar d) := hf.integrable one_le_two
  have hhi : Integrable h (haar d) := hh.integrable one_le_two
  have hpsf : ∀ n : ℕ, Integrable (SharpLSI.psum (fourierCoeff f) n) (haar d) :=
    fun n => (SharpLSI.memLp_psum _ n 1).integrable le_rfl
  have hpsh : ∀ n : ℕ, Integrable (SharpLSI.psum (fourierCoeff h) n) (haar d) :=
    fun n => (SharpLSI.memLp_psum _ n 1).integrable le_rfl
  have T1 := tendsto_integral_mul_of_lintegral (l := atTop) (ψ := coordPartial j φ) hpsf hfi
    (hφ.continuous_coordPartial j) hC₁ (SharpLSI.tendsto_lintegral_psum hf)
  have T2 := tendsto_integral_mul_of_lintegral (l := atTop) (ψ := φ) hpsh hhi
    hφ.continuous_torus hC₂ (SharpLSI.tendsto_lintegral_psum hh)
  have hpoint : ∀ n : ℕ, ∫ x, SharpLSI.psum (fourierCoeff f) n x * coordPartial j φ x ∂haar d
      = -∫ x, SharpLSI.psum (fourierCoeff h) n x * φ x ∂haar d := by
    intro n
    rw [integral_mul_coordPartial_of_smooth (isSmoothPeriodic_psum _ n) hφ j]
    congr 2
    funext x
    rw [coordPartial_psum]
    exact congrArg (fun c => SharpLSI.psum c n x * φ x) (funext fun k => (hcoef k).symm)
  have T3 : Tendsto (fun n : ℕ => ∫ x, SharpLSI.psum (fourierCoeff f) n x * coordPartial j φ x ∂haar d)
      atTop (𝓝 (-∫ x, h x * φ x ∂haar d)) := by
    simp_rw [hpoint]; exact T2.neg
  exact tendsto_nhds_unique T1 T3

theorem isWeakGradient_of_fourierCoeff {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hu : MemLp u 2 (haar d)) (hg : MemLp g 2 (haar d))
    (hcoef : ∀ j k, fourierCoeff (fun y => g y j) k = 2 * π * Complex.I * (k j : ℂ) * fourierCoeff u k) :
    IsWeakGradient u g where
  memLp := hu
  memLp_grad := hg
  ibp _ hφ j := ibp_of_fourierCoeff hu (memLp_coord hg j) j (hcoef j) hφ

/-! ### The forward direction -/

theorem fourierCoeff_weakGradient {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) (j : Fin d) (k : Fin d → ℤ) :
    fourierCoeff (fun y => g y j) k = 2 * π * Complex.I * (k j : ℂ) * fourierCoeff u k :=
  mFourierCoeff_of_ibp (h.memLp.integrable one_le_two)
    ((memLp_coord h.memLp_grad j).integrable one_le_two) j (fun φ hφ => h.ibp φ hφ j) k

theorem gradWeight_mul_eq_sum (k : Fin d → ℤ) (c : ℂ) :
    gradWeight k * ‖c‖ ^ 2 = ∑ j, ‖2 * π * Complex.I * (k j : ℂ) * c‖ ^ 2 := by
  simp_rw [SharpLSI.norm_grad_coeff_sq]
  unfold gradWeight
  rw [Finset.mul_sum, Finset.sum_mul]

theorem hasSum_gradWeight_of_coeff {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hg : MemLp g 2 (haar d))
    (hcoef : ∀ j k, fourierCoeff (fun y => g y j) k = 2 * π * Complex.I * (k j : ℂ) * fourierCoeff u k) :
    HasSum (fun k => gradWeight k * ‖fourierCoeff u k‖ ^ 2) (∫ x, ‖g x‖ ^ 2 ∂haar d) := by
  have hG : ∀ j : Fin d, HasSum (fun k => ‖fourierCoeff (fun y => g y j) k‖ ^ 2)
      (∫ x, g x j ^ 2 ∂haar d) := fun j =>
    SharpLSI.hasSum_sq_mFourierCoeff_real (memLp_coord hg j)
  have hsum := hasSum_sum (s := Finset.univ) (fun j _ => hG j)
  have hint : ∫ x, ‖g x‖ ^ 2 ∂haar d = ∑ j, ∫ x, g x j ^ 2 ∂haar d := by
    simp_rw [tangent_norm_sq]
    exact integral_finsetSum _ fun j _ => (memLp_coord hg j).integrable_sq
  rw [hint]
  convert hsum using 1
  funext k
  rw [gradWeight_mul_eq_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [hcoef j k]

theorem hasSum_gradWeight_weakGradient {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) :
    HasSum (fun k => gradWeight k * ‖fourierCoeff u k‖ ^ 2) (∫ x, ‖g x‖ ^ 2 ∂haar d) :=
  hasSum_gradWeight_of_coeff h.memLp_grad (fourierCoeff_weakGradient h)

theorem IsWeakGradient.finiteFourierEnergy {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) : FiniteFourierEnergy u :=
  (hasSum_gradWeight_weakGradient h).summable

/-- The Fourier gradient energy of `u ∈ H¹`, in terms of the chosen weak gradient. -/
theorem hasSum_gradWeight_weakGradient' {u : Torus d → ℝ} (hu : MemH1 u) :
    HasSum (fun k => gradWeight k * ‖fourierCoeff u k‖ ^ 2)
      (∫ x, ‖weakGradient u hu x‖ ^ 2 ∂haar d) :=
  hasSum_gradWeight_weakGradient (isWeakGradient_weakGradient hu)

/-! ### Synthesis of the weak gradient from finite Fourier energy -/

theorem norm_sq_gradCoeff_le (k : Fin d → ℤ) (j : Fin d) (c : ℂ) :
    ‖2 * π * Complex.I * (k j : ℂ) * c‖ ^ 2 ≤ gradWeight k * ‖c‖ ^ 2 := by
  rw [gradWeight_mul_eq_sum]
  exact Finset.single_le_sum (f := fun i => ‖2 * π * Complex.I * (k i : ℂ) * c‖ ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ j)

theorem exists_weakGradient_of_finiteFourierEnergy {u : Torus d → ℝ} (hu : MemLp u 2 (haar d))
    (hE : FiniteFourierEnergy u) : ∃ g : Torus d → Tangent d, IsWeakGradient u g := by
  have hex : ∀ j : Fin d, ∃ f : Torus d → ℝ, MemLp f 2 (haar d) ∧ ∀ k,
      fourierCoeff f k = 2 * π * Complex.I * (k j : ℂ) * fourierCoeff u k := by
    intro j
    refine SharpLSI.exists_of_cf (c := fun k => 2 * π * Complex.I * (k j : ℂ) * fourierCoeff u k)
      ?_ ?_
    · exact Summable.of_nonneg_of_le (fun k => sq_nonneg _)
        (fun k => norm_sq_gradCoeff_le k j _) hE
    · intro k
      have : fourierCoeff u (-k) = conj (fourierCoeff u k) := fourierCoeff_neg u k
      simp only [this, Pi.neg_apply, Int.cast_neg, map_mul, Complex.conj_ofReal,
        Complex.conj_I, Complex.conj_ofNat, map_intCast]
      ring
  choose f hf hcf using hex
  let g : Torus d → Tangent d := fun x => WithLp.toLp 2 fun j => f j x
  have hg : MemLp g 2 (haar d) := memLp_piLp_iff.mpr fun j => hf j
  exact ⟨g, isWeakGradient_of_fourierCoeff hu hg fun j k => hcf j k⟩

/-! ### Parseval and the tails of the cutoff -/

theorem hasSum_sq_fourierCoeff {u : Torus d → ℝ} (hu : MemLp u 2 (haar d)) :
    HasSum (fun k => ‖fourierCoeff u k‖ ^ 2) (∫ x, u x ^ 2 ∂haar d) :=
  SharpLSI.hasSum_sq_mFourierCoeff_real hu

theorem memLp_fourierCutoff (u : Torus d → ℝ) (R : ℝ) : MemLp (fourierCutoff u R) 2 (haar d) :=
  SharpLSI.memLp_psum _ _ 2

theorem integral_sq_fourierCutoff_sub {u : Torus d → ℝ} (hu : MemLp u 2 (haar d)) (R : ℝ) :
    ∫ y, (fourierCutoff u R y - u y) ^ 2 ∂haar d =
      ∑' k, (if InFreqBall R k then 0 else ‖fourierCoeff u k‖ ^ 2) := by
  have hP := hasSum_sq_fourierCoeff ((memLp_fourierCutoff u R).sub hu)
  simp only [Pi.sub_apply] at hP
  rw [← hP.tsum_eq]
  congr 1; funext k
  show ‖fourierCoeff (fun y => fourierCutoff u R y - u y) k‖ ^ 2 = _
  have e := SharpLSI.cf_sub ((memLp_fourierCutoff u R).integrable one_le_two)
    (hu.integrable one_le_two) k
  refine (congrArg (fun z : ℂ => ‖z‖ ^ 2) e).trans ?_
  show ‖fourierCoeff (fourierCutoff u R) k - fourierCoeff u k‖ ^ 2 = _
  rw [fourierCoeff_fourierCutoff]
  unfold cutCoeff
  split_ifs <;> simp

theorem tendsto_integral_sq_fourierCutoff_sub {u : Torus d → ℝ} (hu : MemLp u 2 (haar d)) :
    Tendsto (fun R : ℝ => ∫ y, (fourierCutoff u R y - u y) ^ 2 ∂haar d) atTop (𝓝 0) := by
  simp_rw [integral_sq_fourierCutoff_sub hu]
  have hsum : Summable fun k => ‖fourierCoeff u k‖ ^ 2 := (hasSum_sq_fourierCoeff hu).summable
  have h0 : (0 : ℝ) = ∑' k : Fin d → ℤ, (0 : ℝ) := by simp
  rw [h0]
  refine tendsto_tsum_of_dominated_convergence hsum (fun k => ?_)
    (Eventually.of_forall fun R k => ?_)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (Real.sqrt (∑ j, ((k j : ℤ) : ℝ) ^ 2))] with R hR
    simp [InFreqBall, hR]
  · split_ifs <;> simp

/-! ### The cutoff of a weak gradient -/

theorem fourierCoeff_cutoffGrad {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) (R : ℝ) (j : Fin d) (k : Fin d → ℤ) :
    fourierCoeff (fun y => fourierCutoffGrad g R y j) k =
      2 * π * Complex.I * (k j : ℂ) * fourierCoeff (fourierCutoff u R) k := by
  change fourierCoeff (fourierCutoff (fun y => g y j) R) k = _
  rw [fourierCoeff_fourierCutoff, fourierCoeff_fourierCutoff]
  have : cutCoeff (fourierCoeff (fun y => g y j)) R =
      cutCoeff (fun k => 2 * π * Complex.I * (k j : ℂ) * fourierCoeff u k) R :=
    congrArg (fun c => cutCoeff c R) (funext fun k => fourierCoeff_weakGradient h j k)
  rw [this, cutCoeff_mul]

theorem isWeakGradient_fourierCutoff {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) (R : ℝ) :
    IsWeakGradient (fourierCutoff u R) (fourierCutoffGrad g R) :=
  isWeakGradient_of_fourierCoeff (memLp_fourierCutoff u R)
    (memLp_piLp_iff.mpr fun _ => memLp_fourierCutoff _ R) (fourierCoeff_cutoffGrad h R)

/-- The cutoff gradient is the classical gradient of the smooth function `S_R u`. -/
theorem fourierCutoffGrad_apply {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) (R : ℝ) (x : Torus d) (j : Fin d) :
    fourierCutoffGrad g R x j = coordPartial j (fourierCutoff u R) x := by
  unfold fourierCutoff
  rw [coordPartial_psum]
  show SharpLSI.psum (cutCoeff (fourierCoeff (fun y => g y j)) R) ⌈R⌉₊ x = _
  have : cutCoeff (fourierCoeff (fun y => g y j)) R =
      fun k => 2 * π * Complex.I * (k j : ℂ) * cutCoeff (fourierCoeff u) R k := by
    funext k
    rw [← cutCoeff_mul (fun k => 2 * π * Complex.I * (k j : ℂ)) (fourierCoeff u) R k]
    exact congrArg (fun c => cutCoeff c R k) (funext fun k => fourierCoeff_weakGradient h j k)
  rw [this]

theorem hasSum_gradWeight_cutoff {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) (R : ℝ) :
    HasSum (fun k => if InFreqBall R k then gradWeight k * ‖fourierCoeff u k‖ ^ 2 else 0)
      (∫ x, ‖fourierCutoffGrad g R x‖ ^ 2 ∂haar d) := by
  have := hasSum_gradWeight_weakGradient (isWeakGradient_fourierCutoff h R)
  convert this using 1
  funext k
  rw [fourierCoeff_fourierCutoff]
  unfold cutCoeff
  split_ifs <;> simp

theorem integral_norm_sq_cutoffGrad_le {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) (R : ℝ) :
    ∫ x, ‖fourierCutoffGrad g R x‖ ^ 2 ∂haar d ≤ ∫ x, ‖g x‖ ^ 2 ∂haar d := by
  refine hasSum_le (fun k => ?_) (hasSum_gradWeight_cutoff h R) (hasSum_gradWeight_weakGradient h)
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (by unfold gradWeight; positivity) (sq_nonneg _)

theorem tendsto_integral_norm_sq_cutoffGrad_sub {g : Torus d → Tangent d}
    (hg : MemLp g 2 (haar d)) :
    Tendsto (fun R : ℝ => ∫ x, ‖fourierCutoffGrad g R x - g x‖ ^ 2 ∂haar d) atTop (𝓝 0) := by
  have hj : ∀ R : ℝ, ∫ x, ‖fourierCutoffGrad g R x - g x‖ ^ 2 ∂haar d =
      ∑ j, ∫ y, (fourierCutoff (fun y => g y j) R y - g y j) ^ 2 ∂haar d := by
    intro R
    simp_rw [tangent_norm_sq]
    refine integral_finsetSum _ fun j _ => ?_
    exact ((memLp_fourierCutoff _ R).sub (memLp_coord hg j)).integrable_sq
  simp_rw [hj]
  have := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun j _ =>
    tendsto_integral_sq_fourierCutoff_sub (memLp_coord hg j)
  simpa using this

end DGPS

namespace DGPS.Analysis

open DGPS

/-- FOU004: periodic Sobolev spaces via Fourier series on the unit torus. -/
theorem periodic_sobolev_fourier_identity (d : ℕ) :
    -- `H¹` is exactly `L²` with finite Fourier gradient energy
    (∀ u : Torus d → ℝ, MemH1 u ↔ MemLp u 2 (haar d) ∧ FiniteFourierEnergy u) ∧
    -- Parseval for `L²`
    (∀ u : Torus d → ℝ, MemLp u 2 (haar d) →
      HasSum (fun k => ‖fourierCoeff u k‖ ^ 2) (∫ x, u x ^ 2 ∂haar d)) ∧
    -- `‖∇u‖² = ∑ 4π²|k|²|û(k)|²` and `\widehat{∂ⱼu}(k) = 2πi kⱼ û(k)`
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g →
      HasSum (fun k => gradWeight k * ‖fourierCoeff u k‖ ^ 2) (∫ x, ‖g x‖ ^ 2 ∂haar d) ∧
      ∀ j k, fourierCoeff (fun y => g y j) k = 2 * π * Complex.I * (k j : ℂ) * fourierCoeff u k) ∧
    -- converse: the prescribed Fourier coefficients are those of the weak derivatives
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), MemLp u 2 (haar d) → MemLp g 2 (haar d) →
      (∀ j k, fourierCoeff (fun y => g y j) k = 2 * π * Complex.I * (k j : ℂ) * fourierCoeff u k) →
      IsWeakGradient u g) ∧
    -- finite Fourier cutoffs: smooth, weak gradient, exact Euclidean gradient norm, `H¹` convergence
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g →
      (∀ R : ℝ, IsSmoothPeriodic (fourierCutoff u R) ∧
        IsWeakGradient (fourierCutoff u R) (fourierCutoffGrad g R) ∧
        (∀ x j, fourierCutoffGrad g R x j = coordPartial j (fourierCutoff u R) x) ∧
        HasSum (fun k => if InFreqBall R k then gradWeight k * ‖fourierCoeff u k‖ ^ 2 else 0)
          (∫ x, ‖fourierCutoffGrad g R x‖ ^ 2 ∂haar d) ∧
        ∫ x, ‖fourierCutoffGrad g R x‖ ^ 2 ∂haar d ≤ ∫ x, ‖g x‖ ^ 2 ∂haar d) ∧
      Tendsto (fun R : ℝ => ∫ x, (fourierCutoff u R x - u x) ^ 2 ∂haar d +
        ∫ x, ‖fourierCutoffGrad g R x - g x‖ ^ 2 ∂haar d) atTop (𝓝 0)) := by
  refine ⟨fun u => ⟨fun ⟨g, hg⟩ => ⟨hg.memLp, hg.finiteFourierEnergy⟩,
      fun ⟨hu, hE⟩ => exists_weakGradient_of_finiteFourierEnergy hu hE⟩,
    fun u hu => hasSum_sq_fourierCoeff hu,
    fun u g h => ⟨hasSum_gradWeight_weakGradient h, fourierCoeff_weakGradient h⟩,
    fun u g hu hg hc => isWeakGradient_of_fourierCoeff hu hg hc,
    fun u g h => ⟨fun R => ⟨isSmoothPeriodic_psum _ _, isWeakGradient_fourierCutoff h R,
      fourierCutoffGrad_apply h R, hasSum_gradWeight_cutoff h R,
      integral_norm_sq_cutoffGrad_le h R⟩, ?_⟩⟩
  have := (tendsto_integral_sq_fourierCutoff_sub h.memLp).add
    (tendsto_integral_norm_sq_cutoffGrad_sub h.memLp_grad)
  simpa using this

end DGPS.Analysis
