import SharpSymmetricLSI.Paper.ULimit5

/-!
# The finite-dimensional central limit theorem (Phase 3, lane D; R26)

For an orthonormal family `f_0, …, f_{R-1}` of centered functions in `L²(ν)` and i.i.d. samples
`ω_k ~ ν`, the vector `(N^{-1/2} ∑_{k<N} f_a(ω_k))_a` converges in distribution to the first
`R` coordinates of `γ` (Cramér–Wold through characteristic functions, the one-dimensional CLT and
Lévy's continuity theorem).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal

namespace SharpLSI

/-- The first `R` coordinates of an infinite product of a fixed probability measure. -/
theorem infinitePi_map_fin {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (R : ℕ) : (Measure.infinitePi fun _ : ℕ => ν).map (fun ω (a : Fin R) => ω a) =
      Measure.pi fun _ : Fin R => ν := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hm : Measurable fun (ω : ℕ → α) (a : Fin R) => ω a := by fun_prop
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  set t : ℕ → Set α := fun i => if h : i < R then s ⟨i, h⟩ else Set.univ
  have hpre : (fun (ω : ℕ → α) (a : Fin R) => ω a) ⁻¹' Set.univ.pi s =
      Set.pi ((Finset.range R : Finset ℕ) : Set ℕ) t := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_pi, Finset.coe_range, Set.mem_Iio, t]
    constructor
    · intro h i hi; rw [dif_pos hi]; exact h ⟨i, hi⟩ (Set.mem_univ _)
    · intro h a _; have := h a a.2; rwa [dif_pos a.2] at this
  have ht : ∀ i ∈ Finset.range R, MeasurableSet (t i) := fun i _ => by
    simp only [t]; split_ifs with h
    · exact hs _
    · exact MeasurableSet.univ
  rw [hpre]
  refine (Measure.infinitePi_pi (μ := fun _ : ℕ => ν) ht).trans ?_
  rw [← Fin.prod_univ_eq_prod_range (fun i => ν (t i))]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [t, dif_pos a.2]

theorem gammaRef_map_fin (R : ℕ) :
    gammaRef.map (fun z (a : Fin R) => z a) = Measure.pi fun _ : Fin R => gaussianReal 0 1 :=
  infinitePi_map_fin _ R

section clt
variable {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν] {R : ℕ}
  {f : Fin R → α → ℝ}

/-- The normalized sums. -/
def cltVec (f : Fin R → α → ℝ) (N : ℕ) (ω : ℕ → α) : EuclideanSpace ℝ (Fin R) :=
  WithLp.toLp 2 fun a => (√(N : ℝ))⁻¹ * ∑ k ∈ Finset.range N, f a (ω k)

/-- The Gaussian limit. -/
def gaussVec (R : ℕ) (z : ℕ → ℝ) : EuclideanSpace ℝ (Fin R) := WithLp.toLp 2 fun a : Fin R => z a

theorem gammaRef_map_gaussVec : gammaRef.map (gaussVec R) = stdGaussian (EuclideanSpace ℝ (Fin R)) := by
  have h1 : gaussVec R = (WithLp.toLp 2) ∘ fun z (a : Fin R) => z a := rfl
  rw [h1, ← Measure.map_map (WithLp.measurable_toLp 2 _) (by fun_prop), gammaRef_map_fin,
    map_pi_eq_stdGaussian]

/-- **The finite-dimensional CLT.** -/
theorem tendstoInDistribution_cltVec (hf : ∀ a, Measurable (f a)) (hL : ∀ a, MemLp (f a) 2 ν)
    (h0 : ∀ a, ∫ x, f a x ∂ν = 0)
    (h1 : ∀ a b, ∫ x, f a x * f b x ∂ν = if a = b then 1 else 0) :
    TendstoInDistribution (cltVec f) atTop (gaussVec R)
      (fun _ => Measure.infinitePi fun _ : ℕ => ν) gammaRef := by
  set P := Measure.infinitePi fun _ : ℕ => ν
  have hmeas : ∀ N, Measurable (cltVec f N) := fun N => by
    unfold cltVec
    exact (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr fun a =>
      (Finset.measurable_sum _ fun k _ => (hf a).comp (measurable_pi_apply k)).const_mul _)
  refine TendstoInDistribution.of_tendsto_charFun (fun N => (hmeas N).aemeasurable)
    ((WithLp.measurable_toLp 2 _).comp (by fun_prop)).aemeasurable fun t => ?_
  rw [gammaRef_map_gaussVec, charFun_stdGaussian]
  -- the one-dimensional projection
  set g : α → ℝ := fun x => ∑ a, f a x * t a
  have hg : Measurable g := Finset.measurable_sum _ fun a _ => (hf a).mul_const _
  have hgL : MemLp g 2 ν := memLp_finsetSum _ fun a _ => (hL a).mul_const _
  have hg0 : ∫ x, g x ∂ν = 0 := by
    rw [integral_finsetSum _ fun a _ => ((hL a).integrable one_le_two).mul_const _]
    simp [integral_mul_const, h0]
  have hg2 : ∫ x, g x ^ 2 ∂ν = ‖t‖ ^ 2 := by
    have e : ∀ x, g x ^ 2 = ∑ a, ∑ b, t a * t b * (f a x * f b x) := fun x => by
      simp only [g, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    simp_rw [e]
    have hab : ∀ a, ∫ x, ∑ b, t a * t b * (f a x * f b x) ∂ν = t a ^ 2 := fun a => by
      rw [integral_finsetSum (f := fun b x => t a * t b * (f a x * f b x)) _
        fun b _ => ((hL a).integrable_mul (hL b)).const_mul _]
      simp_rw [integral_const_mul, h1]
      simp [sq]
    rw [integral_finsetSum (f := fun a x => ∑ b, t a * t b * (f a x * f b x)) _
      fun a _ => integrable_finsetSum _ fun b _ => ((hL a).integrable_mul (hL b)).const_mul _,
      Finset.sum_congr rfl fun a _ => hab a, EuclideanSpace.real_norm_sq_eq]
  set X : ℕ → (ℕ → α) → ℝ := fun k ω => g (ω k)
  have hXmap : ∀ k, P.map (X k) = ν.map g := fun k => by
    rw [show X k = g ∘ fun ω => ω k from rfl, ← Measure.map_map hg (measurable_pi_apply k),
      Measure.infinitePi_map_eval]
  have hindep : iIndepFun X P := iIndepFun_infinitePi (X := fun _ => g) fun _ => hg
  have hident : ∀ k, IdentDistrib (X k) (X 0) P P := fun k =>
    ⟨(hg.comp (measurable_pi_apply k)).aemeasurable, (hg.comp (measurable_pi_apply 0)).aemeasurable,
      by rw [hXmap, hXmap]⟩
  have hX0L : MemLp (X 0) 2 P := by
    have : MemLp g 2 (P.map fun ω : ℕ → α => ω 0) := by
      rw [Measure.infinitePi_map_eval]; exact hgL
    exact this.comp_of_map (measurable_pi_apply 0).aemeasurable
  have hXint : ∀ φ : ℝ → ℝ, Measurable φ → ∫ ω, φ (X 0 ω) ∂P = ∫ x, φ (g x) ∂ν := fun φ hφ => by
    have h := integral_map (μ := P) (measurable_pi_apply 0).aemeasurable
      (hφ.comp hg).aestronglyMeasurable
    rw [Measure.infinitePi_map_eval] at h
    exact h.symm
  have hP0 : ∫ ω, X 0 ω ∂P = 0 := (hXint id measurable_id).trans hg0
  have hvar : Var[X 0; P] = ‖t‖ ^ 2 := by
    rw [variance_of_integral_eq_zero (X := X 0) (hg.comp (measurable_pi_apply 0)).aemeasurable hP0,
      hXint (fun x => x ^ 2) (by fun_prop), hg2]
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (P' := gaussianReal 0 (Var[X 0; P]).toNNReal) (Y := id) HasLaw.id hX0L hindep hident
  have hc := hclt.tendsto_charFun 1
  rw [Measure.map_id, charFun_gaussianReal, hvar, Real.coe_toNNReal _ (sq_nonneg _)] at hc
  have hlim : cexp (((1 : ℝ) : ℂ) * ((0 : ℝ) : ℂ) * I - ((‖t‖ ^ 2 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) ^ 2 / 2) =
      cexp (-((‖t‖ : ℂ)) ^ 2 / 2) := by
    congr 1; push_cast; ring
  rw [hlim] at hc
  refine hc.congr fun N => ?_
  have hin : ∀ ω, (√(N : ℝ))⁻¹ * (∑ k ∈ Finset.range N, X k ω - N * ∫ ω, X 0 ω ∂P) =
      inner ℝ (cltVec f N ω) t := fun ω => by
    rw [hP0, mul_zero, sub_zero, cltVec, PiLp.inner_apply]
    simp only [X, g, PiLp.toLp_apply, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial,
      RCLike.re_to_real]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => by ring
  have hsm : Measurable fun ω : ℕ → α =>
      (√(N : ℝ))⁻¹ * (∑ k ∈ Finset.range N, X k ω - N * ∫ ω, X 0 ω ∂P) :=
    ((Finset.measurable_sum _ fun k _ => hg.comp (measurable_pi_apply k)).sub_const _).const_mul _
  rw [charFun_apply, charFun_apply, integral_map hsm.aemeasurable (by fun_prop),
    integral_map (hmeas N).aemeasurable (by fun_prop)]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  have h1' : ∀ r : ℝ, inner ℝ r (1 : ℝ) = r := fun r => by simp
  simp only [h1']
  rw [hin ω]

end clt

end SharpLSI
