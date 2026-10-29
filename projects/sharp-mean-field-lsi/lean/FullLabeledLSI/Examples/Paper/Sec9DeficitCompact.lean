import SharpSymmetricLSI.Paper.FourierSynth
import SharpSymmetricLSI.Paper.CircleNear
import SharpSymmetricLSI.Paper.CircleLSIExt
import SharpSymmetricLSI.Paper.AppAEvol2
import SharpSymmetricLSI.Paper.DensMeasure

/-!
# Section 9, generic `H¹(𝕋)` compactness (`h1_compact`)

Lane C of the Section 9 formalization (Lemma 9.5 step L3 and Lemma 9.6 step (a)).

`h1_compact`: a sequence of nonnegative `f_n ∈ H¹(𝕋)` with `∫ f_n² = 1` and bounded Dirichlet energy
has a subsequence converging in `L²` and a.e. to a nonnegative `u ∈ H¹`, `∫ u² = 1`, with
`∫ u'² ≤ L = lim ∫ f_n'²`, convergence of every moment `∫ F f_n²` (`F` continuous) and of the
entropy `H(f_n²|m) = (klDiv (densMeasure f_n²) m).toReal`.

The generic parts are COPIED (namespace changed to `SharpLSI.FL.Ex.Cmp`, otherwise unmodified except
that statements were specialized to our objects) from branch `claude/prop82-lane-B` (Prop 8.2 lane B),
commit `e672d2b`: `exists_ae_subseq_of_L2`, `DensConv` and its lemmas (`B1Convergence.lean`),
`integrable_mul_of_memLp_two`, `sq_integral_le_of_weak_tendsto` (`B2Fisher.lean`), `limit_memH1`
(`B4Attainment.lean`).
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL.Ex.Cmp

open SharpLSI

/-! ### Copies from lane B -/

/-- A.e. convergent subsequence from `L²` convergence (copy of `B1Convergence.exists_ae_subseq_of_L2`). -/
theorem exists_ae_subseq_of_L2 {f : ℕ → Torus 1 → Real} {u : Torus 1 → Real}
    (hf : ∀ n, MemLp (f n) 2 (haar 1)) (hu : MemLp u 2 (haar 1))
    (h : Tendsto (fun n => ∫ x, (f n x - u x) ^ 2 ∂haar 1) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ x ∂haar 1, Tendsto (fun n => f (φ n) x) atTop (𝓝 (u x)) := by
  have he : Tendsto (fun n => eLpNorm (f n - u) 2 (haar 1)) atTop (𝓝 0) := by
    have key : ∀ n, eLpNorm (f n - u) 2 (haar 1) =
        ENNReal.ofReal (Real.sqrt (∫ x, (f n x - u x) ^ 2 ∂haar 1)) := by
      intro n
      have hm := (hf n).sub hu
      rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      congr 1
      rw [Real.sqrt_eq_rpow]
      simp only [ENNReal.toReal_ofNat, Pi.sub_apply, Real.norm_eq_abs]
      norm_num
    simp_rw [key]
    have := ((Real.continuous_sqrt.tendsto 0).comp h)
    rw [Real.sqrt_zero] at this
    simpa using ENNReal.tendsto_ofReal this
  exact (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero he).exists_seq_tendsto_ae

theorem integrable_mul_of_memLp_two {f g : Torus 1 → Real} (hf : MemLp f 2 (haar 1))
    (hg : MemLp g 2 (haar 1)) : Integrable (fun x => f x * g x) (haar 1) := by
  refine Integrable.mono' (hf.integrable_sq.add hg.integrable_sq)
    (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_le, Pi.add_apply]
  constructor <;> nlinarith [sq_nonneg (f x + g x), sq_nonneg (f x - g x)]

/-- Weak lower semicontinuity of the `L²` norm along a sequence whose squared norms converge. -/
theorem sq_integral_le_of_weak_tendsto {w : ℕ → Torus 1 → Real} {g : Torus 1 → Real}
    (hw : ∀ n, MemLp (w n) 2 (haar 1)) (hg : MemLp g 2 (haar 1))
    (hweak : ∀ h : Torus 1 → Real, MemLp h 2 (haar 1) →
      Tendsto (fun n => ∫ x, w n x * h x ∂haar 1) atTop (𝓝 (∫ x, g x * h x ∂haar 1)))
    {L : Real} (hL : Tendsto (fun n => ∫ x, w n x ^ 2 ∂haar 1) atTop (𝓝 L)) :
    ∫ x, g x ^ 2 ∂haar 1 ≤ L := by
  have hlim : Tendsto (fun n => 2 * ∫ x, w n x * g x ∂haar 1 - ∫ x, g x ^ 2 ∂haar 1)
      atTop (𝓝 (2 * ∫ x, g x * g x ∂haar 1 - ∫ x, g x ^ 2 ∂haar 1)) :=
    ((hweak g hg).const_mul 2).sub_const _
  have hgg : ∫ x, g x * g x ∂haar 1 = ∫ x, g x ^ 2 ∂haar 1 := by
    congr 1; funext x; ring
  rw [hgg] at hlim
  have hle : ∀ n, 2 * ∫ x, w n x * g x ∂haar 1 - ∫ x, g x ^ 2 ∂haar 1 ≤
      ∫ x, w n x ^ 2 ∂haar 1 := by
    intro n
    have i1 := (hw n).integrable_sq
    have i2 := hg.integrable_sq
    have i3 := integrable_mul_of_memLp_two (hw n) hg
    have h0 : 0 ≤ ∫ x, (w n x - g x) ^ 2 ∂haar 1 := integral_nonneg fun x => sq_nonneg _
    have e : ∫ x, (w n x - g x) ^ 2 ∂haar 1 =
        ∫ x, w n x ^ 2 ∂haar 1 - 2 * ∫ x, w n x * g x ∂haar 1 + ∫ x, g x ^ 2 ∂haar 1 := by
      have : ∀ x, (w n x - g x) ^ 2 = (w n x ^ 2 - 2 * (w n x * g x)) + g x ^ 2 :=
        fun x => by ring
      simp_rw [this]
      rw [integral_add (f := fun x => w n x ^ 2 - 2 * (w n x * g x))
        (g := fun x => g x ^ 2) (i1.sub (i3.const_mul 2)) i2,
        integral_sub (f := fun x => w n x ^ 2) (g := fun x => 2 * (w n x * g x)) i1
          (i3.const_mul 2), integral_const_mul]
    linarith
  have := le_of_tendsto_of_tendsto' hlim hL hle
  linarith

/-- The weak limit is an `H¹` square root (copy of `B4Attainment.limit_memH1`). -/
theorem limit_memH1 {u : Torus 1 → Real} {g : Torus 1 → Fin 1 → Real}
    (hu : MemLp u 2 (haar 1)) (hg : ∀ j, MemLp (fun x => g x j) 2 (haar 1))
    (hw : IsWeakGrad u g) (hu0 : ∀ᵐ x ∂haar 1, 0 ≤ u x) :
    MemH1 (haar 1) (fun x => Real.sqrt (u x ^ 2)) ∧
      (∀ᵐ x ∂haar 1, weakGrad (fun y => Real.sqrt (u y ^ 2)) x 0 = g x 0) := by
  have hae : (fun x => Real.sqrt (u x ^ 2)) =ᵐ[haar 1] u := by
    filter_upwards [hu0] with x hx
    exact Real.sqrt_sq hx
  have hgu : weakGrad u =ᵐ[haar 1] g :=
    weakGrad_ae_unique (isWeakGrad_weakGrad ⟨g, hw⟩) hw
  have hU : MemH1 (haar 1) u := by
    refine ⟨⟨g, hw⟩, hu, ?_⟩
    have h1 : MemLp (fun x => Real.sqrt (sqNorm (g x))) 2 (haar 1) := by
      have : (fun x => Real.sqrt (sqNorm (g x))) = fun x => |g x 0| := by
        funext x
        simp [sqNorm, Real.sqrt_sq_eq_abs]
      rw [this]
      exact (hg 0).abs
    refine h1.ae_eq ?_
    filter_upwards [hgu] with x hx
    rw [hx]
  have hV : MemH1 (haar 1) (fun x => Real.sqrt (u x ^ 2)) := appA_memH1_congr_ae hae.symm hU
  refine ⟨hV, ?_⟩
  have h2 := appA_weakGrad_congr_ae hae hV.1
  filter_upwards [h2, hgu] with x hx1 hx2
  rw [hx1, hx2]

/-! ### Dominated convergence for density sequences (adapted from `B1Convergence`) -/

/-- `H(ρ|m)` as an integral of `klFun`. -/
theorem klDiv_toReal_eq_integral {ρ : Torus 1 → ℝ} (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) :
    (klDiv (densMeasure ρ) (haar 1)).toReal = ∫ x, klFun (ρ x) ∂haar 1 := by
  have hi := integrable_of_integral_eq_one' h1
  have hmeas : AEStronglyMeasurable (fun x => klFun (ρ x)) (haar 1) :=
    continuous_klFun.comp_aestronglyMeasurable hi.aestronglyMeasurable
  rw [klDiv_densMeasure' h0 h1, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => klFun_nonneg (h0 x)) hmeas]

theorem klFun_le_bound' {x B : ℝ} (hx : 0 ≤ x) (hB : x ≤ B) : klFun x ≤ B ^ 2 + 1 := by
  have h1 : klFun x ≤ (x - 1) ^ 2 := by
    rw [klFun_apply]
    rcases hx.eq_or_lt with h | h
    · rw [← h]; simp
    · have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h) hx
      nlinarith
  nlinarith

/-- A uniformly bounded sequence of probability densities converging a.e. -/
structure DensConv (rho : ℕ → Torus 1 → Real) (rhoInf : Torus 1 → Real) (B : Real) : Prop where
  nonneg : ∀ n x, 0 ≤ rho n x
  mass : ∀ n, ∫ x, rho n x ∂haar 1 = 1
  bound : ∀ n, ∀ᵐ x ∂haar 1, rho n x ≤ B
  tendsto : ∀ᵐ x ∂haar 1, Tendsto (fun n => rho n x) atTop (𝓝 (rhoInf x))

namespace DensConv

variable {rho : ℕ → Torus 1 → Real} {rhoInf : Torus 1 → Real} {B : Real}

theorem bound' (h : DensConv rho rhoInf B) : ∀ᵐ x ∂haar 1, ∀ n, rho n x ≤ B :=
  ae_all_iff.mpr h.bound

theorem inf_nonneg (h : DensConv rho rhoInf B) : ∀ᵐ x ∂haar 1, 0 ≤ rhoInf x := by
  filter_upwards [h.tendsto] with x hx
  exact ge_of_tendsto' hx fun n => h.nonneg n x

theorem tendsto_mom (h : DensConv rho rhoInf B) {F : Torus 1 → Real} (hF : Continuous F)
    {M : Real} (hb : ∀ x, |F x| ≤ M) :
    Tendsto (fun n => ∫ x, F x * rho n x ∂haar 1) atTop (𝓝 (∫ x, F x * rhoInf x ∂haar 1)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => M * B) (fun n => ?_)
    (integrable_const _) (fun n => ?_) ?_
  · exact (hF.aestronglyMeasurable.mul
      (integrable_of_integral_eq_one (h.mass n)).aestronglyMeasurable)
  · filter_upwards [h.bound n] with x hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (h.nonneg n x)]
    exact mul_le_mul (hb x) hx (h.nonneg n x) ((abs_nonneg _).trans (hb x))
  · filter_upwards [h.tendsto] with x hx
    exact hx.const_mul _

theorem mass_inf (h : DensConv rho rhoInf B) : ∫ x, rhoInf x ∂haar 1 = 1 := by
  have := h.tendsto_mom (F := fun _ => 1) continuous_const (M := 1) (fun x => by simp)
  simp only [one_mul, h.mass] at this
  exact tendsto_nhds_unique this tendsto_const_nhds

theorem tendsto_entropy (h : DensConv rho rhoInf B) (h0 : ∀ x, 0 ≤ rhoInf x) :
    Tendsto (fun n => (klDiv (densMeasure (rho n)) (haar 1)).toReal) atTop
      (𝓝 (klDiv (densMeasure rhoInf) (haar 1)).toReal) := by
  rw [klDiv_toReal_eq_integral h0 h.mass_inf]
  have : (fun n => (klDiv (densMeasure (rho n)) (haar 1)).toReal) =
      fun n => ∫ x, klFun (rho n x) ∂haar 1 := by
    funext n; exact klDiv_toReal_eq_integral (h.nonneg n) (h.mass n)
  rw [this]
  refine tendsto_integral_of_dominated_convergence (fun _ => B ^ 2 + 1) (fun n => ?_)
    (integrable_const _) (fun n => ?_) ?_
  · exact continuous_klFun.comp_aestronglyMeasurable
      (integrable_of_integral_eq_one (h.mass n)).aestronglyMeasurable
  · filter_upwards [h.bound n] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg (h.nonneg n x))]
    exact klFun_le_bound' (h.nonneg n x) hx
  · filter_upwards [h.tendsto] with x hx
    exact (continuous_klFun.tendsto _).comp hx

end DensConv

/-! ### `h1_compact` -/

/-- **Generic `H¹(𝕋)` compactness.** -/
theorem h1_compact {f : ℕ → Torus 1 → ℝ} {D : ℝ} (hf0 : ∀ n x, 0 ≤ f n x)
    (hH : ∀ n, MemH1 (haar 1) (f n)) (h1 : ∀ n, ∫ x, f n x ^ 2 ∂haar 1 = 1)
    (hD : ∀ n, ∫ x, weakGrad (f n) x 0 ^ 2 ∂haar 1 ≤ D) :
    ∃ (φ : ℕ → ℕ) (u : Torus 1 → ℝ) (L : ℝ), StrictMono φ ∧ (∀ x, 0 ≤ u x) ∧
      MemH1 (haar 1) u ∧ ∫ x, u x ^ 2 ∂haar 1 = 1 ∧
      (∀ᵐ x ∂haar 1, Tendsto (fun n => f (φ n) x) atTop (𝓝 (u x))) ∧
      Tendsto (fun n => ∫ x, (f (φ n) x - u x) ^ 2 ∂haar 1) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x, weakGrad (f (φ n)) x 0 ^ 2 ∂haar 1) atTop (𝓝 L) ∧
      ∫ x, weakGrad u x 0 ^ 2 ∂haar 1 ≤ L ∧
      (∀ F : Torus 1 → ℝ, Continuous F →
        Tendsto (fun n => ∫ x, F x * f (φ n) x ^ 2 ∂haar 1) atTop
          (𝓝 (∫ x, F x * u x ^ 2 ∂haar 1))) ∧
      Tendsto (fun n => (klDiv (densMeasure fun x => f (φ n) x ^ 2) (haar 1)).toReal) atTop
        (𝓝 (klDiv (densMeasure fun x => u x ^ 2) (haar 1)).toReal) := by
  have hD0 : 0 ≤ D := (integral_nonneg fun x => sq_nonneg _).trans (hD 0)
  have hw : ∀ n, IsWeakGrad (f n) (weakGrad (f n)) := fun n => isWeakGrad_weakGrad (hH n).1
  have hg : ∀ n j, MemLp (fun x => weakGrad (f n) x j) 2 (haar 1) := by
    intro n j
    have : j = 0 := Subsingleton.elim _ _
    subst this
    exact memLp_weakGrad_zero (hH n)
  have hB : ∀ n, (∫ y, f n y ^ 2) + ∑ j : Fin 1, ∫ y, weakGrad (f n) y j ^ 2 ≤ 1 + D := by
    intro n
    simp only [Fin.sum_univ_one, h1 n]
    linarith [hD n]
  obtain ⟨φ0, hφ0, fI, G, hfI, hG, hwf, hL2, hwlim⟩ :=
    rellich_torus hw (fun n => (hH n).2.1) hg hB
  obtain ⟨ψ, hψ, hae0⟩ := exists_ae_subseq_of_L2 (f := fun n x => f (φ0 n) x)
    (fun n => (hH _).2.1) hfI hL2
  -- convergent subsequence of the Dirichlet energies
  obtain ⟨L, -, χ, hχ, hLχ⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (0 : ℝ) D)
    (x := fun k => ∫ x, weakGrad (f (φ0 (ψ k))) x 0 ^ 2 ∂haar 1)
    (fun k => ⟨integral_nonneg fun x => sq_nonneg _, hD _⟩)
  set φ : ℕ → ℕ := fun k => φ0 (ψ (χ k)) with hφdef
  have hφ : StrictMono φ := hφ0.comp (hψ.comp hχ)
  have hψχ : StrictMono (ψ ∘ χ) := hψ.comp hχ
  have hu0' : ∀ᵐ x ∂haar 1, 0 ≤ fI x := by
    filter_upwards [hae0] with x hx
    exact ge_of_tendsto' hx fun n => hf0 _ x
  obtain ⟨hMu, hgrad⟩ := limit_memH1 hfI hG hwf hu0'
  set u : Torus 1 → ℝ := fun x => Real.sqrt (fI x ^ 2) with hudef
  have hu0 : ∀ x, 0 ≤ u x := fun x => Real.sqrt_nonneg _
  have huae : u =ᵐ[haar 1] fI := by
    filter_upwards [hu0'] with x hx
    exact Real.sqrt_sq hx
  have hae : ∀ᵐ x ∂haar 1, Tendsto (fun n => f (φ n) x) atTop (𝓝 (u x)) := by
    filter_upwards [hae0, huae] with x hx hx2
    rw [hx2]
    exact hx.comp hχ.tendsto_atTop
  -- sup bound
  have hsup : ∀ n, ∀ᵐ x ∂haar 1, f n x ^ 2 ≤ (1 + (Real.sqrt D + D)) ^ 2 := by
    intro n
    have hs : (fun x => Real.sqrt (f n x ^ 2)) = f n := funext fun x => Real.sqrt_sq (hf0 n x)
    have hMem : MemH1 (haar 1) (fun x => Real.sqrt (f n x ^ 2)) := by rw [hs]; exact hH n
    have key := ae_abs_sqrt_sub_one_le (ρ := fun x => f n x ^ 2) (fun x => sq_nonneg _) (h1 n) hMem
    filter_upwards [key] with x hx
    rw [hs] at hx
    have hW0 : 0 ≤ ∫ y, weakGrad (f n) y 0 ^ 2 ∂haar 1 := integral_nonneg fun y => sq_nonneg _
    have hle : f n x ≤ 1 + (Real.sqrt D + D) := by
      have := (abs_le.mp hx).2
      rw [Real.sqrt_sq (hf0 n x)] at this
      have h2 : Real.sqrt (∫ y, weakGrad (f n) y 0 ^ 2 ∂haar 1) ≤ Real.sqrt D :=
        Real.sqrt_le_sqrt (hD n)
      linarith [hD n]
    exact pow_le_pow_left₀ (hf0 n x) hle 2
  have hdc : DensConv (fun n x => f (φ n) x ^ 2) (fun x => u x ^ 2)
      ((1 + (Real.sqrt D + D)) ^ 2) :=
    { nonneg := fun n x => sq_nonneg _
      mass := fun n => h1 _
      bound := fun n => hsup _
      tendsto := by
        filter_upwards [hae] with x hx
        exact hx.pow 2 }
  have hmass : ∫ x, u x ^ 2 ∂haar 1 = 1 := hdc.mass_inf
  refine ⟨φ, u, L, hφ, hu0, hMu, hmass, hae, ?_, hLχ, ?_, ?_, ?_⟩
  · refine (hL2.comp hψχ.tendsto_atTop).congr fun n => ?_
    refine integral_congr_ae ?_
    filter_upwards [huae] with x hx
    simp only [Function.comp, hφdef, hx]
  · have hw' : ∀ n, MemLp (fun x => weakGrad (f (φ n)) x 0) 2 (haar 1) :=
      fun n => memLp_weakGrad_zero (hH _)
    have hlsc := sq_integral_le_of_weak_tendsto (w := fun n x => weakGrad (f (φ n)) x 0)
      (g := fun x => G x 0) hw' (hG 0)
      (fun h hh => (hwlim 0 h hh).comp hψχ.tendsto_atTop) hLχ
    have : ∫ x, weakGrad u x 0 ^ 2 ∂haar 1 = ∫ x, G x 0 ^ 2 ∂haar 1 :=
      integral_congr_ae (hgrad.mono fun x hx => by simp only; rw [hx])
    rw [this]
    exact hlsc
  · intro F hF
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
    exact hdc.tendsto_mom hF (M := M) (fun x => by simpa using hM x (Set.mem_univ x))
  · exact hdc.tendsto_entropy (fun x => sq_nonneg _)

end SharpLSI.FL.Ex.Cmp
