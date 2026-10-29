import DGPS.Lipschitz.MeanFieldFlowRegularity
import DGPS.Lipschitz.ResolventFourier

/-!
# Positivity and stationarity of the mean-field flow (LIP027, attempt 2)

For a mild flow `u` of the modified mean-field equation with `0 ≤ ρ0`, `∫ ρ0 = 1`:
* the Fourier cutoffs of `u` and of the flux `𝒩(u)` have space-time `L²` limits `A`, `K`
  (representatives of `∇u` and `𝒩(u)`), and `∂ₜ u = div (A + K)` weakly (`IsWeakTimeDivergence`);
* the negative-part chain rule of LIP026 and Gronwall's lemma give `u_t ≥ 0`;
* hence `P(u_t) = u_t`, the mass is one, and `u` solves the original mean-field PDE.
-/

open MeasureTheory Set Filter Topology
open scoped Real RealInnerProductSpace ComplexConjugate

namespace DGPS.Lipschitz

section PartA

variable {d : ℕ}


noncomputable abbrev tmeas (d : ℕ) (T : ℝ) : Measure (ℝ × Torus d) :=
  (volume.restrict (Icc (0 : ℝ) T)).prod (haar d)

theorem Lp_norm_sq_eq' {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (F : Lp E 2 μ) : ‖F‖ ^ 2 = ∫ x, ‖(F : α → E) x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

theorem memLp_two_tmeas_of_slices {T : ℝ} {F : ℝ × Torus d → Tangent d}
    (hF : AEStronglyMeasurable F (tmeas d T))
    (hs : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), MemLp (fun x => F (r, x)) 2 (haar d))
    (hi : Integrable (fun r => ∫ x, ‖F (r, x)‖ ^ 2 ∂haar d) (volume.restrict (Icc (0 : ℝ) T))) :
    MemLp F 2 (tmeas d T) := by
  rw [memLp_two_iff_integrable_sq_norm hF]
  have hF2 : AEStronglyMeasurable (fun p => ‖F p‖ ^ 2) (tmeas d T) := hF.norm.pow 2
  rw [integrable_prod_iff hF2]
  refine ⟨?_, ?_⟩
  · filter_upwards [hs] with r hr
    exact (memLp_two_iff_integrable_sq_norm hr.aestronglyMeasurable).1 hr
  · refine hi.congr (Eventually.of_forall fun r => ?_)
    simp only [norm_pow, norm_norm]

theorem integral_tmeas_eq {T : ℝ} {F : ℝ × Torus d → ℝ}
    (hF : Integrable F (tmeas d T)) :
    ∫ p, F p ∂tmeas d T = ∫ r in Icc (0 : ℝ) T, ∫ x, F (r, x) ∂haar d :=
  integral_prod _ hF

theorem exists_spacetime_limit (T : ℝ) (F : ℕ → ℝ × Torus d → Tangent d)
    (hm : ∀ n, Measurable (F n))
    (hs : ∀ n r, MemLp (fun x => F n (r, x)) 2 (haar d))
    (hE : ∀ n, Continuous (fun r => ∫ x, ‖F n (r, x)‖ ^ 2 ∂haar d))
    (horth : ∀ n m, n ≤ m → ∀ r ∈ Icc (0 : ℝ) T,
      ∫ x, ‖F m (r, x) - F n (r, x)‖ ^ 2 ∂haar d =
        ∫ x, ‖F m (r, x)‖ ^ 2 ∂haar d - ∫ x, ‖F n (r, x)‖ ^ 2 ∂haar d)
    (C : ℝ) (hC : ∀ n, ∫ r in Icc (0 : ℝ) T, ∫ x, ‖F n (r, x)‖ ^ 2 ∂haar d ≤ C) :
    ∃ A : ℝ × Torus d → Tangent d, Measurable A ∧ MemLp A 2 (tmeas d T) ∧
      (∀ W : ℝ × Torus d → Tangent d, MemLp W 2 (tmeas d T) →
        Tendsto (fun n => ∫ p, ⟪F n p, W p⟫ ∂tmeas d T) atTop
          (𝓝 (∫ p, ⟪A p, W p⟫ ∂tmeas d T))) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
        MemLp (fun x => A (r, x)) 2 (haar d) ∧
        Tendsto (fun n => ∫ x, ‖F (φ n) (r, x) - A (r, x)‖ ^ 2 ∂haar d) atTop (𝓝 0) := by
  have hF2 : ∀ n, MemLp (F n) 2 (tmeas d T) := fun n =>
    memLp_two_tmeas_of_slices (hm n).aestronglyMeasurable (Eventually.of_forall (hs n))
      ((hE n).integrableOn_Icc)
  set I : ℕ → ℝ := fun n => ∫ r in Icc (0 : ℝ) T, ∫ x, ‖F n (r, x)‖ ^ 2 ∂haar d with hI
  have hEi : ∀ n, Integrable (fun r => ∫ x, ‖F n (r, x)‖ ^ 2 ∂haar d)
      (volume.restrict (Icc (0 : ℝ) T)) := fun n => (hE n).integrableOn_Icc
  have hdiff : ∀ n m, n ≤ m → ∫ p, ‖F m p - F n p‖ ^ 2 ∂tmeas d T = I m - I n := by
    intro n m hnm
    have hi : Integrable (fun p => ‖F m p - F n p‖ ^ 2) (tmeas d T) :=
      (memLp_two_iff_integrable_sq_norm ((hF2 m).sub (hF2 n)).aestronglyMeasurable).1
        ((hF2 m).sub (hF2 n))
    rw [integral_tmeas_eq hi]
    rw [hI]
    simp only
    rw [← integral_sub (hEi m) (hEi n)]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    exact horth n m hnm r hr
  have hmono : Monotone I := by
    intro n m hnm
    have := hdiff n m hnm
    have h0 : 0 ≤ ∫ p, ‖F m p - F n p‖ ^ 2 ∂tmeas d T := integral_nonneg fun _ => by positivity
    linarith
  have hbdd : BddAbove (range I) := ⟨C, by rintro _ ⟨n, rfl⟩; exact hC n⟩
  have hconv : Tendsto I atTop (𝓝 (⨆ n, I n)) := tendsto_atTop_ciSup hmono hbdd
  have hcI : CauchySeq I := hconv.cauchySeq
  set f : ℕ → Lp (Tangent d) 2 (tmeas d T) := fun n => (hF2 n).toLp (F n) with hf
  have hdist : ∀ n m, n ≤ m → dist (f m) (f n) ^ 2 = I m - I n := by
    intro n m hnm
    rw [dist_eq_norm, Lp_norm_sq_eq']
    rw [← hdiff n m hnm]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (f m) (f n), (hF2 m).coeFn_toLp, (hF2 n).coeFn_toLp] with p h1 h2 h3
    have h2' : (⇑(f m)) p = F m p := h2
    have h3' : (⇑(f n)) p = F n p := h3
    rw [h1, Pi.sub_apply, h2', h3']
  have hcf : CauchySeq f := by
    rw [Metric.cauchySeq_iff] at hcI ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcI (ε ^ 2) (by positivity)
    refine ⟨N, fun m hm' n hn => ?_⟩
    have key : ∀ a b, N ≤ a → N ≤ b → a ≤ b → dist (f b) (f a) < ε := by
      intro a b ha hb hab
      have h1 := hN b hb a ha
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hmono hab])] at h1
      have h2 := hdist a b hab
      have : dist (f b) (f a) ^ 2 < ε ^ 2 := by rw [h2]; exact h1
      exact lt_of_pow_lt_pow_left₀ 2 hε.le this
    rcases le_total n m with h | h
    · exact key n m hn hm' h
    · rw [dist_comm]; exact key m n hm' hn h
  obtain ⟨finf, hfinf⟩ := cauchySeq_tendsto_of_complete hcf
  set A : ℝ × Torus d → Tangent d := ⇑finf with hA
  have hAm : Measurable A := (Lp.stronglyMeasurable finf).measurable
  have hAL : MemLp A 2 (tmeas d T) := Lp.memLp finf
  have hD : Tendsto (fun n => ∫ p, ‖F n p - A p‖ ^ 2 ∂tmeas d T) atTop (𝓝 0) := by
    have h1 := (hfinf.sub_const finf).norm.pow 2
    simp only [sub_self, norm_zero] at h1
    have h2 : Tendsto (fun n => ‖f n - finf‖ ^ 2) atTop (𝓝 0) := by
      have := ((tendsto_iff_dist_tendsto_zero.1 hfinf).pow 2)
      simpa [dist_eq_norm] using this
    refine h2.congr fun n => ?_
    rw [Lp_norm_sq_eq']
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (f n) finf, (hF2 n).coeFn_toLp] with p h1 h2
    have h2' : (⇑(f n)) p = F n p := h2
    rw [h1, Pi.sub_apply, h2']
  have hDi : ∀ n, Integrable (fun p => ‖F n p - A p‖ ^ 2) (tmeas d T) := fun n =>
    (memLp_two_iff_integrable_sq_norm ((hF2 n).sub hAL).aestronglyMeasurable).1 ((hF2 n).sub hAL)
  set Dn : ℕ → ℝ → ℝ := fun n r => ∫ x, ‖F n (r, x) - A (r, x)‖ ^ 2 ∂haar d with hDn
  have hDn_int : ∀ n, Integrable (Dn n) (volume.restrict (Icc (0 : ℝ) T)) := fun n =>
    (hDi n).integral_prod_left
  have hDn_nonneg : ∀ n r, 0 ≤ Dn n r := fun n r => integral_nonneg fun _ => by positivity
  have hDlim : Tendsto (fun n => ∫ r, Dn n r ∂(volume.restrict (Icc (0 : ℝ) T))) atTop (𝓝 0) := by
    refine hD.congr fun n => ?_
    exact integral_tmeas_eq (hDi n)
  have hL1 : Tendsto (fun n => eLpNorm (Dn n - 0) 1 (volume.restrict (Icc (0 : ℝ) T))) atTop (𝓝 0) := by
    have : ∀ n, eLpNorm (Dn n - 0) 1 (volume.restrict (Icc (0 : ℝ) T)) =
        ENNReal.ofReal (∫ r, Dn n r ∂(volume.restrict (Icc (0 : ℝ) T))) := by
      intro n
      rw [sub_zero, eLpNorm_one_eq_lintegral_enorm (hDn_int n).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm (hDn_int n)]
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun r => by
        simp only [Real.norm_eq_abs]; exact abs_of_nonneg (hDn_nonneg n r))
    simp_rw [this]
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal hDlim
  have hmeas : TendstoInMeasure (volume.restrict (Icc (0 : ℝ) T)) Dn atTop (fun _ => (0 : ℝ)) :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hL1
  obtain ⟨φ, hφ, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hweak : ∀ W : ℝ × Torus d → Tangent d, MemLp W 2 (tmeas d T) →
      Tendsto (fun n => ∫ p, ⟪F n p, W p⟫ ∂tmeas d T) atTop
        (𝓝 (∫ p, ⟪A p, W p⟫ ∂tmeas d T)) := by
    intro W hW
    have h1 := Filter.Tendsto.inner (𝕜 := ℝ) hfinf (tendsto_const_nhds (x := hW.toLp W))
    have e : ∀ G : Lp (Tangent d) 2 (tmeas d T), inner ℝ G (hW.toLp W) =
        ∫ p, ⟪(G : ℝ × Torus d → Tangent d) p, W p⟫ ∂tmeas d T := by
      intro G
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hW.coeFn_toLp] with p hp
      rw [hp]
    simp_rw [e] at h1
    have e2 : ∀ n, ∫ p, ⟪(f n : ℝ × Torus d → Tangent d) p, W p⟫ ∂tmeas d T =
        ∫ p, ⟪F n p, W p⟫ ∂tmeas d T := by
      intro n
      refine integral_congr_ae ?_
      filter_upwards [(hF2 n).coeFn_toLp] with p hp
      have hp' : (⇑(f n)) p = F n p := hp
      rw [hp']
    have e3 : ∫ p, ⟪(finf : ℝ × Torus d → Tangent d) p, W p⟫ ∂tmeas d T =
        ∫ p, ⟪A p, W p⟫ ∂tmeas d T := rfl
    simpa only [e2, e3] using h1
  have hAs : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), MemLp (fun x => A (r, x)) 2 (haar d) := by
    have hA2 : AEStronglyMeasurable (fun p => ‖A p‖ ^ 2) (tmeas d T) := (hAm.norm.pow_const 2).aestronglyMeasurable
    have := ((integrable_prod_iff hA2).1
      ((memLp_two_iff_integrable_sq_norm hAm.aestronglyMeasurable).1 hAL)).1
    filter_upwards [this] with r hr
    have hmr : Measurable (fun x => A (r, x)) := hAm.comp measurable_prodMk_left
    exact (memLp_two_iff_integrable_sq_norm hmr.aestronglyMeasurable).2 hr
  exact ⟨A, hAm, hAL, hweak, φ, hφ, by filter_upwards [hAs, hae] with r h1 h2 using ⟨h1, h2⟩⟩



theorem inFreqBall_mono {R R' : ℝ} (h : R ≤ R') {k : Fin d → ℤ} (hk : InFreqBall R k) :
    InFreqBall R' k := le_trans hk h

theorem orth_gen {H : ℝ → Torus d → ℝ} {e : (Fin d → ℤ) → ℂ}
    (hm : ∀ R, MemLp (H R) 2 (haar d))
    (hc : ∀ R k, fourierCoeff (H R) k = if InFreqBall R k then e k else 0)
    {R R' : ℝ} (hR : R ≤ R') :
    ∫ x, (H R' x - H R x) ^ 2 ∂haar d = ∫ x, (H R' x) ^ 2 ∂haar d - ∫ x, (H R x) ^ 2 ∂haar d := by
  have h1 := hasSum_sq_fourierCoeff ((hm R').sub (hm R))
  have h2 := (hasSum_sq_fourierCoeff (hm R')).sub (hasSum_sq_fourierCoeff (hm R))
  refine h1.unique ?_
  convert h2 using 1
  funext k
  have e : fourierCoeff (H R' - H R) k = fourierCoeff (H R') k - fourierCoeff (H R) k :=
    fourierCoeff_sub'' (hm R') (hm R) k
  rw [e, hc R' k, hc R k]
  by_cases h : InFreqBall R k
  · simp [h, inFreqBall_mono hR h]
  · by_cases h' : InFreqBall R' k <;> simp [h, h']

theorem integral_sub_sq_cutGrad {f : Torus d → ℝ} {R R' : ℝ} (hR : R ≤ R') :
    ∫ x, ‖cutGrad f R' x - cutGrad f R x‖ ^ 2 ∂haar d =
      ∫ x, ‖cutGrad f R' x‖ ^ 2 ∂haar d - ∫ x, ‖cutGrad f R x‖ ^ 2 ∂haar d := by
  have hj : ∀ (S : ℝ) x, ‖cutGrad f S x‖ ^ 2 = ∑ j, (coordPartial j (fourierCutoff f S) x) ^ 2 := by
    intro S x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [cutGrad]
  have hd : ∀ x, ‖cutGrad f R' x - cutGrad f R x‖ ^ 2 =
      ∑ j, (coordPartial j (fourierCutoff f R') x - coordPartial j (fourierCutoff f R) x) ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [cutGrad]
  simp_rw [hd, hj]
  have hmj : ∀ j, ∀ S, MemLp (coordPartial j (fourierCutoff f S)) 2 (haar d) :=
    fun j S => memLp_coordPartial_cutoff f S j
  have i1 : ∫ x, ∑ j, (coordPartial j (fourierCutoff f R') x - coordPartial j (fourierCutoff f R) x) ^ 2 ∂haar d =
      ∑ j, ∫ x, (coordPartial j (fourierCutoff f R') x - coordPartial j (fourierCutoff f R) x) ^ 2 ∂haar d :=
    integral_finsetSum _ (fun j _ => ((hmj j R').sub (hmj j R)).integrable_sq)
  have i2 : ∀ S, ∫ x, ∑ j, (coordPartial j (fourierCutoff f S) x) ^ 2 ∂haar d =
      ∑ j, ∫ x, (coordPartial j (fourierCutoff f S) x) ^ 2 ∂haar d := fun S =>
    integral_finsetSum _ (fun j _ => (hmj j S).integrable_sq)
  rw [i1, i2, i2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact orth_gen (H := fun S => coordPartial j (fourierCutoff f S))
    (e := fun k => 2 * π * Complex.I * (k j : ℂ) * fourierCoeff f k) (hmj j)
    (fun S k => by
      rw [fourierCoeff_coordPartial_cutoff, fourierCoeff_fourierCutoff]
      unfold cutCoeff; split_ifs <;> simp) hR

theorem integral_sub_sq_fourierCutoffGrad {F : Torus d → Tangent d}
    {R R' : ℝ} (hR : R ≤ R') :
    ∫ x, ‖fourierCutoffGrad F R' x - fourierCutoffGrad F R x‖ ^ 2 ∂haar d =
      ∫ x, ‖fourierCutoffGrad F R' x‖ ^ 2 ∂haar d - ∫ x, ‖fourierCutoffGrad F R x‖ ^ 2 ∂haar d := by
  have hj : ∀ (S : ℝ) x, ‖fourierCutoffGrad F S x‖ ^ 2 = ∑ j, (fourierCutoff (fun y => F y j) S x) ^ 2 := by
    intro S x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [fourierCutoffGrad]
  have hd : ∀ x, ‖fourierCutoffGrad F R' x - fourierCutoffGrad F R x‖ ^ 2 =
      ∑ j, (fourierCutoff (fun y => F y j) R' x - fourierCutoff (fun y => F y j) R x) ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [fourierCutoffGrad]
  simp_rw [hd, hj]
  have hmj : ∀ j, ∀ S, MemLp (fourierCutoff (fun y => F y j) S) 2 (haar d) :=
    fun j S => memLp_fourierCutoff _ S
  have i1 : ∫ x, ∑ j, (fourierCutoff (fun y => F y j) R' x - fourierCutoff (fun y => F y j) R x) ^ 2 ∂haar d =
      ∑ j, ∫ x, (fourierCutoff (fun y => F y j) R' x - fourierCutoff (fun y => F y j) R x) ^ 2 ∂haar d :=
    integral_finsetSum _ (fun j _ => ((hmj j R').sub (hmj j R)).integrable_sq)
  have i2 : ∀ S, ∫ x, ∑ j, (fourierCutoff (fun y => F y j) S x) ^ 2 ∂haar d =
      ∑ j, ∫ x, (fourierCutoff (fun y => F y j) S x) ^ 2 ∂haar d := fun S =>
    integral_finsetSum _ (fun j _ => (hmj j S).integrable_sq)
  rw [i1, i2, i2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact orth_gen (H := fun S => fourierCutoff (fun y => F y j) S)
    (e := fun k => fourierCoeff (fun y => F y j) k) (hmj j)
    (fun S k => by
      rw [fourierCoeff_fourierCutoff]
      unfold cutCoeff; rfl) hR



theorem measurable_psum_fam {c : ℝ → (Fin d → ℤ) → ℂ} (hc : ∀ k, Measurable (fun r => c r k))
    (N : ℕ) : Measurable (fun p : ℝ × Torus d => SharpLSI.psum (c p.1) N p.2) := by
  unfold SharpLSI.psum SharpLSI.psumC
  refine Complex.measurable_re.comp (Finset.measurable_sum _ fun k _ => ?_)
  exact ((hc k).comp measurable_fst).mul
    (((UnitAddTorus.mFourier k : C(UnitAddTorus (Fin d), ℂ)).continuous.measurable).comp measurable_snd)

theorem measurable_cutCoeff_fam {c : ℝ → (Fin d → ℤ) → ℂ} (hc : ∀ k, Measurable (fun r => c r k))
    (R : ℝ) (k : Fin d → ℤ) : Measurable (fun r => cutCoeff (c r) R k) := by
  unfold cutCoeff
  by_cases h : InFreqBall R k
  · simp only [h, ite_true]; exact hc k
  · simp only [h, ite_false]; exact measurable_const

theorem measurable_toLp_tangent {α : Type*} [MeasurableSpace α] {f : α → Tangent d}
    (hf : ∀ j, Measurable (fun a => f a j)) : Measurable f := by
  have : Measurable (fun a => (WithLp.ofLp (f a) : Fin d → ℝ)) := Measurable.of_eval hf
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp this

theorem measurable_cutGrad_fam {v : ℝ → Torus d → ℝ}
    (hv : ∀ k, Measurable (fun r => fourierCoeff (v r) k)) (R : ℝ) :
    Measurable (fun p : ℝ × Torus d => cutGrad (v p.1) R p.2) := by
  refine measurable_toLp_tangent fun j => ?_
  have : (fun p : ℝ × Torus d => (cutGrad (v p.1) R p.2) j) =
      fun p => SharpLSI.psum (fun k => 2 * π * Complex.I * (k j : ℂ) *
        cutCoeff (fourierCoeff (v p.1)) R k) ⌈R⌉₊ p.2 := by
    funext p
    simp only [cutGrad]
    exact coordPartial_psum _ _ j p.2
  rw [this]
  refine measurable_psum_fam (c := fun r k => 2 * π * Complex.I * (k j : ℂ) *
        cutCoeff (fourierCoeff (v r)) R k) (fun k => ?_) _
  exact measurable_const.mul (measurable_cutCoeff_fam (c := fun r => fourierCoeff (v r)) hv R k)

theorem measurable_fourierCutoffGrad_fam {F : ℝ → Torus d → Tangent d}
    (hv : ∀ j k, Measurable (fun r => fourierCoeff (fun y => F r y j) k)) (R : ℝ) :
    Measurable (fun p : ℝ × Torus d => fourierCutoffGrad (F p.1) R p.2) := by
  refine measurable_toLp_tangent fun j => ?_
  have : (fun p : ℝ × Torus d => (fourierCutoffGrad (F p.1) R p.2) j) =
      fun p => SharpLSI.psum (cutCoeff (fourierCoeff (fun y => F p.1 y j)) R) ⌈R⌉₊ p.2 := by
    funext p; rfl
  rw [this]
  exact measurable_psum_fam (c := fun r => cutCoeff (fourierCoeff (fun y => F r y j)) R)
    (fun k => measurable_cutCoeff_fam (c := fun r => fourierCoeff (fun y => F r y j)) (hv j) R k) _



theorem abs_integral_mul_le_sqrt {f g : Torus d → ℝ} (hf : MemLp f 2 (haar d))
    (hg : MemLp g 2 (haar d)) :
    |∫ x, f x * g x ∂haar d| ≤ Real.sqrt (∫ x, f x ^ 2 ∂haar d) * Real.sqrt (∫ x, g x ^ 2 ∂haar d) := by
  have e : ∫ x, f x * g x ∂haar d = inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  have n1 : ‖hf.toLp f‖ = Real.sqrt (∫ x, f x ^ 2 ∂haar d) := by
    rw [← Real.sqrt_sq (norm_nonneg _), Lp_norm_sq_eq']
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x h1
    rw [h1]; simp
  have n2 : ‖hg.toLp g‖ = Real.sqrt (∫ x, g x ^ 2 ∂haar d) := by
    rw [← Real.sqrt_sq (norm_nonneg _), Lp_norm_sq_eq']
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with x h1
    rw [h1]; simp
  rw [e, ← n1, ← n2]
  exact abs_real_inner_le_norm _ _

theorem tendsto_integral_mul_of_sq {a : ℕ → Torus d → ℝ} {a0 ψ : Torus d → ℝ}
    (ha : ∀ n, MemLp (a n) 2 (haar d)) (ha0 : MemLp a0 2 (haar d)) (hψ : MemLp ψ 2 (haar d))
    (h : Tendsto (fun n => ∫ x, (a n x - a0 x) ^ 2 ∂haar d) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, a n x * ψ x ∂haar d) atTop (𝓝 (∫ x, a0 x * ψ x ∂haar d)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun n => Real.sqrt (∫ x, (a n x - a0 x) ^ 2 ∂haar d) *
      Real.sqrt (∫ x, ψ x ^ 2 ∂haar d)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto _).comp h
    simpa using this.mul_const (Real.sqrt (∫ x, ψ x ^ 2 ∂haar d))
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb
  have hdiff : MemLp (fun x => a n x - a0 x) 2 (haar d) := (ha n).sub ha0
  have := abs_integral_mul_le_sqrt hdiff hψ
  have e : ∫ x, a n x * ψ x ∂haar d - ∫ x, a0 x * ψ x ∂haar d
      = ∫ x, (a n x - a0 x) * ψ x ∂haar d := by
    have i1 : Integrable (fun x => a n x * ψ x) (haar d) := (ha n).integrable_mul hψ
    have i2 : Integrable (fun x => a0 x * ψ x) (haar d) := ha0.integrable_mul hψ
    rw [← integral_sub i1 i2]
    simp only [sub_mul]
  rw [Real.norm_eq_abs, e]
  exact this

theorem isWeakGradient_of_limit {u : Torus d → ℝ} {A : Torus d → Tangent d}
    {P : ℕ → Torus d → ℝ} {Q : ℕ → Torus d → Tangent d}
    (hu : MemLp u 2 (haar d)) (hA : MemLp A 2 (haar d))
    (hP : ∀ n, IsWeakGradient (P n) (Q n))
    (hPu : Tendsto (fun n => ∫ x, (P n x - u x) ^ 2 ∂haar d) atTop (𝓝 0))
    (hQA : Tendsto (fun n => ∫ x, ‖Q n x - A x‖ ^ 2 ∂haar d) atTop (𝓝 0)) :
    IsWeakGradient u A := by
  refine ⟨hu, hA, fun φ hφ j => ?_⟩
  have hφ2 : MemLp φ 2 (haar d) := hφ.memLp_top.mono_exponent le_top
  have hφ2' : MemLp (coordPartial j φ) 2 (haar d) :=
    (hφ.memLp_top_coordPartial j).mono_exponent le_top
  have h1 := tendsto_integral_mul_of_sq (fun n => (hP n).memLp) hu hφ2' hPu
  have hQj : ∀ n, MemLp (fun x => Q n x j) 2 (haar d) := fun n =>
    memLp_coord_of_memLp (hP n).memLp_grad j
  have hAj : MemLp (fun x => A x j) 2 (haar d) := memLp_coord_of_memLp hA j
  have hQj2 : Tendsto (fun n => ∫ x, (Q n x j - A x j) ^ 2 ∂haar d) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => integral_nonneg fun x => sq_nonneg _) (fun n => ?_) hQA
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
      ((memLp_two_iff_integrable_sq_norm ((hP n).memLp_grad.sub hA).aestronglyMeasurable).1
        ((hP n).memLp_grad.sub hA)) (Eventually.of_forall fun x => ?_)
    have : (Q n x - A x) j = Q n x j - A x j := rfl
    have h3 := EuclideanSpace.norm_eq (Q n x - A x)
    simp only [Real.norm_eq_abs, sq_abs] at h3
    have h4 : (Q n x j - A x j) ^ 2 ≤ ∑ i, (Q n x i - A x i) ^ 2 := by
      exact Finset.single_le_sum (f := fun i => (Q n x i - A x i) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have h5 : ‖Q n x - A x‖ ^ 2 = ∑ i, (Q n x i - A x i) ^ 2 := by
      rw [h3, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      rfl
    simpa [h5] using h4
  have h2 := tendsto_integral_mul_of_sq (fun n => hQj n) hAj hφ2 hQj2
  have h2' := h2.neg
  have : ∀ n, ∫ x, P n x * coordPartial j φ x ∂haar d = -∫ x, Q n x j * φ x ∂haar d :=
    fun n => (hP n).ibp φ hφ j
  simp_rw [this] at h1
  exact tendsto_nhds_unique h1 h2'

end PartA

section PartB

variable {d : ℕ}

theorem pair_cutoff {f h : Torus d → ℝ} (hh : MemLp h 2 (haar d))
    (R : ℝ) :
    ∫ x, fourierCutoff f R x * h x ∂haar d =
      ∑ k ∈ ballSet R, (fourierCoeff f k * (starRingEnd ℂ) (fourierCoeff h k)).re := by
  have h1 := hasSum_pairing (memLp_fourierCutoff f R) hh
  have h2 := hasSum_ball (R := R) (fun k => (fourierCoeff f k * (starRingEnd ℂ) (fourierCoeff h k)).re)
  refine h1.unique ?_
  convert h2 using 1
  funext k
  rw [fourierCoeff_fourierCutoff]
  unfold cutCoeff
  split_ifs <;> simp

/-- The gradient vector field of a function, as a map into `Tangent d`. -/
noncomputable def gradT (φ : Torus d → ℝ) (x : Torus d) : Tangent d :=
  WithLp.toLp 2 fun j => coordPartial j φ x

theorem inner_gradT (F : Tangent d) (φ : Torus d → ℝ) (x : Torus d) :
    ⟪F, gradT φ x⟫ = ∑ j, F j * coordPartial j φ x := by
  simp only [gradT, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun j _ => by simp [mul_comm]

theorem fourierCoeff_coordPartial_smooth {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) (j : Fin d)
    (k : Fin d → ℤ) :
    fourierCoeff (coordPartial j φ) k = 2 * π * Complex.I * (k j : ℂ) * fourierCoeff φ k :=
  mFourierCoeff_of_ibp (integrable_of_continuous_torus hφ.continuous_torus)
    (integrable_of_continuous_torus (hφ.continuous_coordPartial j)) j
    (fun _ hψ => integral_mul_coordPartial_of_smooth hφ hψ j) k

theorem weight_eq_sum (k : Fin d → ℤ) :
    ∑ j, (2 * π * ((k j : ℤ) : ℝ)) ^ 2 = gradWeight k := by
  unfold gradWeight
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem re_gradient_term (a b : ℂ) (c : ℝ) :
    (((2 * π * Complex.I * (c : ℂ)) * a) * (starRingEnd ℂ) ((2 * π * Complex.I * (c : ℂ)) * b)).re
      = (2 * π * c) ^ 2 * (a * (starRingEnd ℂ) b).re := by
  have : ((2 * π * Complex.I * (c : ℂ)) * a) * (starRingEnd ℂ) ((2 * π * Complex.I * (c : ℂ)) * b)
      = (((2 * π * c) ^ 2 : ℝ) : ℂ) * (a * (starRingEnd ℂ) b) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [this, Complex.re_ofReal_mul]

theorem pair_cutGrad {f : Torus d → ℝ} {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) (R : ℝ) :
    ∫ x, ⟪cutGrad f R x, gradT φ x⟫ ∂haar d =
      ∑ k ∈ ballSet R, gradWeight k * (fourierCoeff f k * (starRingEnd ℂ) (fourierCoeff φ k)).re := by
  have hj : ∀ j : Fin d, ∫ x, (cutGrad f R x) j * coordPartial j φ x ∂haar d =
      ∑ k ∈ ballSet R, (2 * π * ((k j : ℤ) : ℝ)) ^ 2 *
        (fourierCoeff f k * (starRingEnd ℂ) (fourierCoeff φ k)).re := by
    intro j
    have h1 := hasSum_pairing (memLp_coordPartial_cutoff f R j)
      (hφ.memLp_top_coordPartial j |>.mono_exponent le_top)
    have h2 := hasSum_ball (R := R) (fun k => (2 * π * ((k j : ℤ) : ℝ)) ^ 2 *
        (fourierCoeff f k * (starRingEnd ℂ) (fourierCoeff φ k)).re)
    have e : ∫ x, (cutGrad f R x) j * coordPartial j φ x ∂haar d =
        ∫ x, coordPartial j (fourierCutoff f R) x * coordPartial j φ x ∂haar d := rfl
    rw [e]
    refine h1.unique ?_
    convert h2 using 1
    funext k
    rw [fourierCoeff_coordPartial_cutoff, fourierCoeff_fourierCutoff,
      fourierCoeff_coordPartial_smooth hφ]
    unfold cutCoeff
    split_ifs
    · exact re_gradient_term _ _ _
    · simp
  simp_rw [inner_gradT]
  rw [integral_finsetSum]
  · simp_rw [hj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← weight_eq_sum, Finset.sum_mul]
  · intro j _
    exact integrable_mul_of_memLp_two' (memLp_coordPartial_cutoff f R j)
      ((hφ.memLp_top_coordPartial j).mono_exponent le_top)

theorem re_div_term (a b : ℂ) (c : ℝ) :
    (a * (starRingEnd ℂ) ((2 * π * Complex.I * (c : ℂ)) * b)).re =
      -(((2 * π * Complex.I * (c : ℂ)) * a) * (starRingEnd ℂ) b).re := by
  have : a * (starRingEnd ℂ) ((2 * π * Complex.I * (c : ℂ)) * b) =
      -(((2 * π * Complex.I * (c : ℂ)) * a) * (starRingEnd ℂ) b) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  rw [this, Complex.neg_re]

theorem pair_cutVec {F : Torus d → Tangent d} {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) (R : ℝ) :
    ∫ x, ⟪fourierCutoffGrad F R x, gradT φ x⟫ ∂haar d =
      -∑ k ∈ ballSet R, ((∑ j, 2 * π * Complex.I * (k j : ℂ) *
        fourierCoeff (fun y => F y j) k) * (starRingEnd ℂ) (fourierCoeff φ k)).re := by
  have hj : ∀ j : Fin d, ∫ x, (fourierCutoffGrad F R x) j * coordPartial j φ x ∂haar d =
      ∑ k ∈ ballSet R, (fourierCoeff (fun y => F y j) k *
        (starRingEnd ℂ) ((2 * π * Complex.I * (k j : ℂ)) * fourierCoeff φ k)).re := by
    intro j
    have e : ∫ x, (fourierCutoffGrad F R x) j * coordPartial j φ x ∂haar d =
        ∫ x, fourierCutoff (fun y => F y j) R x * coordPartial j φ x ∂haar d := rfl
    rw [e, pair_cutoff ((hφ.memLp_top_coordPartial j).mono_exponent le_top)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fourierCoeff_coordPartial_smooth hφ]
  simp_rw [inner_gradT]
  rw [integral_finsetSum]
  · simp_rw [hj]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ∀ j : Fin d, (fourierCoeff (fun y => F y j) k *
        (starRingEnd ℂ) ((2 * π * Complex.I * (k j : ℂ)) * fourierCoeff φ k)).re =
        -((2 * π * Complex.I * (k j : ℂ) * fourierCoeff (fun y => F y j) k) *
          (starRingEnd ℂ) (fourierCoeff φ k)).re := fun j => re_div_term _ _ _
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_neg_distrib, ← Complex.re_sum,
      ← Finset.sum_mul]
  · intro j _
    exact integrable_mul_of_memLp_two' (memLp_fourierCutoff _ R)
      ((hφ.memLp_top_coordPartial j).mono_exponent le_top)

section Flow
variable {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}
variable {h : MeanFieldData G B g b} {ρ0 : L2s d} {T M : ℝ} {u : ℝ → L2s d}

theorem pair_flux_cut (h : MeanFieldData G B g b) (w : L2s d) {φ : Torus d → ℝ}
    (hφ : IsSmoothPeriodic φ) (R : ℝ) :
    ∫ x, ⟪cutGrad ⇑w R x, gradT φ x⟫ ∂haar d +
      ∫ x, ⟪fourierCutoffGrad ⇑(Nvec h w) R x, gradT φ x⟫ ∂haar d =
    -∑ k ∈ ballSet R, ((-(gradWeight k : ℂ) * cfL k w + divCoef k (Nvec h w)) *
        (starRingEnd ℂ) (fourierCoeff φ k)).re := by
  rw [pair_cutGrad hφ, pair_cutVec hφ, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [divCoef_apply, cfL_apply]
  have e : ((-(gradWeight k : ℂ) * fourierCoeff (fun x => (w : Torus d → ℝ) x) k +
      ∑ j, 2 * π * Complex.I * (k j : ℂ) * fourierCoeff (fun x => (Nvec h w : Torus d → Tangent d) x j) k) *
      (starRingEnd ℂ) (fourierCoeff φ k)).re =
      -(gradWeight k * (fourierCoeff (fun x => (w : Torus d → ℝ) x) k *
        (starRingEnd ℂ) (fourierCoeff φ k)).re) +
      ((∑ j, 2 * π * Complex.I * (k j : ℂ) *
        fourierCoeff (fun x => (Nvec h w : Torus d → Tangent d) x j) k) *
        (starRingEnd ℂ) (fourierCoeff φ k)).re := by
    rw [add_mul, Complex.add_re, neg_mul, neg_mul, Complex.neg_re, mul_assoc,
      ← Complex.re_ofReal_mul]
  rw [e]
  ring

end Flow

end PartB

section PartC

variable {d : ℕ} {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}

section Time
variable {h : MeanFieldData G B g b} {ρ0 : L2s d} {T M : ℝ} {u : ℝ → L2s d}

theorem MildFlow.time_identity_cut (S : MildFlow h ρ0 T M u) {φ : Torus d → ℝ}
    (hφ : IsSmoothPeriodic φ) (R : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    ∫ x, fourierCutoff (⇑(u t)) R x * φ x ∂haar d - ∫ x, fourierCutoff (⇑(u s)) R x * φ x ∂haar d =
      -∫ r in s..t, (∫ x, ⟪cutGrad (⇑(uX T u r)) R x, gradT φ x⟫ ∂haar d +
        ∫ x, ⟪fourierCutoffGrad (⇑(Nvec h (uX T u r))) R x, gradT φ x⟫ ∂haar d) := by
  have hφ2 : MemLp φ 2 (haar d) := hφ.memLp_top.mono_exponent le_top
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs, hst.trans ht⟩
  have htT : t ∈ Icc (0 : ℝ) T := ⟨hs.trans hst, ht⟩
  have hII : ∀ k (a c : ℝ), a ∈ Icc (0 : ℝ) T → c ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (MildFlow.modeDeriv h u k) volume a c := by
    intro k a c ha hc
    exact ((S.continuousOn_modeDeriv k).mono (Set.uIcc_subset_Icc ha hc)).intervalIntegrable
  have key : ∀ k : Fin d → ℤ,
      (fourierCoeff (⇑(u t)) k * (starRingEnd ℂ) (fourierCoeff φ k)).re -
        (fourierCoeff (⇑(u s)) k * (starRingEnd ℂ) (fourierCoeff φ k)).re =
      ∫ r in s..t, (MildFlow.modeDeriv h u k r * (starRingEnd ℂ) (fourierCoeff φ k)).re := by
    intro k
    have e1 := S.modeDeriv_integral k htT
    have e2 := S.modeDeriv_integral k hsT
    rw [cfL_apply] at e1 e2
    have e3 : fourierCoeff (⇑(u t)) k - fourierCoeff (⇑(u s)) k =
        ∫ r in s..t, MildFlow.modeDeriv h u k r := by
      rw [e1, e2, add_sub_add_left_eq_sub]
      exact intervalIntegral.integral_interval_sub_left
        (hII k 0 t ⟨le_rfl, S.hT⟩ htT) (hII k 0 s ⟨le_rfl, S.hT⟩ hsT)
    rw [← Complex.sub_re, ← sub_mul, e3, ← intervalIntegral.integral_mul_const]
    exact (Complex.reCLM.intervalIntegral_comp_comm
      (((hII k s t hsT htT).mul_const _))).symm
  rw [pair_cutoff hφ2, pair_cutoff hφ2, ← Finset.sum_sub_distrib]
  simp_rw [key]
  rw [← intervalIntegral.integral_finsetSum]
  · rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le hst] at hr
    have hr' : r ∈ Icc (0 : ℝ) T := ⟨hs.trans hr.1, hr.2.trans ht⟩
    rw [pair_flux_cut h (uX T u r) hφ R]
    simp only [neg_neg]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [MildFlow.modeDeriv, S.uX_of_mem hr']
  · intro k _
    have hI := (hII k s t hsT htT).mul_const ((starRingEnd ℂ) (fourierCoeff φ k))
    exact ⟨hI.1.re, hI.2.re⟩

end Time

theorem ae_eq_of_two_limits {A B : Torus d → Tangent d} {F : ℕ → Torus d → Tangent d}
    (hA : MemLp A 2 (haar d)) (hB : MemLp B 2 (haar d)) (hF : ∀ n, MemLp (F n) 2 (haar d))
    (hA' : Tendsto (fun n => ∫ x, ‖F n x - A x‖ ^ 2 ∂haar d) atTop (𝓝 0))
    (hB' : Tendsto (fun n => ∫ x, ‖F n x - B x‖ ^ 2 ∂haar d) atTop (𝓝 0)) :
    A =ᵐ[haar d] B := by
  have hint : ∀ n, Integrable (fun x => ‖F n x - A x‖ ^ 2) (haar d) := fun n =>
    (memLp_two_iff_integrable_sq_norm ((hF n).sub hA).aestronglyMeasurable).1 ((hF n).sub hA)
  have hint' : ∀ n, Integrable (fun x => ‖F n x - B x‖ ^ 2) (haar d) := fun n =>
    (memLp_two_iff_integrable_sq_norm ((hF n).sub hB).aestronglyMeasurable).1 ((hF n).sub hB)
  have hAB : Integrable (fun x => ‖A x - B x‖ ^ 2) (haar d) :=
    (memLp_two_iff_integrable_sq_norm (hA.sub hB).aestronglyMeasurable).1 (hA.sub hB)
  have hle : ∀ n, ∫ x, ‖A x - B x‖ ^ 2 ∂haar d ≤
      2 * ∫ x, ‖F n x - A x‖ ^ 2 ∂haar d + 2 * ∫ x, ‖F n x - B x‖ ^ 2 ∂haar d := by
    intro n
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hint n).const_mul _)
      ((hint' n).const_mul _)]
    refine integral_mono hAB (((hint n).const_mul _).add ((hint' n).const_mul _)) fun x => ?_
    have h1 : A x - B x = (F n x - B x) - (F n x - A x) := by abel
    have h2 : ‖A x - B x‖ ≤ ‖F n x - B x‖ + ‖F n x - A x‖ := by
      rw [h1]; exact norm_sub_le _ _
    nlinarith [norm_nonneg (F n x - B x), norm_nonneg (F n x - A x), norm_nonneg (A x - B x),
      sq_nonneg (‖F n x - B x‖ - ‖F n x - A x‖)]
  have hlim : Tendsto (fun n => 2 * ∫ x, ‖F n x - A x‖ ^ 2 ∂haar d +
      2 * ∫ x, ‖F n x - B x‖ ^ 2 ∂haar d) atTop (𝓝 0) := by
    simpa using (hA'.const_mul 2).add (hB'.const_mul 2)
  have h0 : ∫ x, ‖A x - B x‖ ^ 2 ∂haar d ≤ 0 := ge_of_tendsto' hlim hle
  have h0' : ∫ x, ‖A x - B x‖ ^ 2 ∂haar d = 0 :=
    le_antisymm h0 (integral_nonneg fun x => sq_nonneg _)
  rw [integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hAB] at h0'
  filter_upwards [h0'] with x hx
  have : ‖A x - B x‖ ^ 2 = 0 := hx
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero)|>.mp this))


/-- Space-time gradient cutoffs of the flow. -/
noncomputable def FgS (T : ℝ) (u : ℝ → L2s d) (n : ℕ) (p : ℝ × Torus d) : Tangent d :=
  cutGrad (⇑(uX T u p.1)) (n : ℝ) p.2

/-- Space-time flux cutoffs of the flow. -/
noncomputable def FkS (h : MeanFieldData G B g b) (T : ℝ) (u : ℝ → L2s d) (n : ℕ)
    (p : ℝ × Torus d) : Tangent d :=
  fourierCutoffGrad (⇑(Nvec h (uX T u p.1))) (n : ℝ) p.2

section Limits
variable {h : MeanFieldData G B g b} {ρ0 : L2s d} {T M : ℝ} {u : ℝ → L2s d}

theorem MildFlow.exists_gradient_limit (S : MildFlow h ρ0 T M u) :
    ∃ A : ℝ × Torus d → Tangent d, Measurable A ∧ MemLp A 2 (tmeas d T) ∧
      (∀ W : ℝ × Torus d → Tangent d, MemLp W 2 (tmeas d T) →
        Tendsto (fun n : ℕ => ∫ p, ⟪FgS T u n p, W p⟫ ∂tmeas d T) atTop
          (𝓝 (∫ p, ⟪A p, W p⟫ ∂tmeas d T))) ∧
      (∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), IsWeakGradient (⇑(uX T u r)) (fun x => A (r, x))) := by
  have hv : ∀ k, Measurable (fun r => fourierCoeff (⇑(uX T u r)) k) := fun k => by
    have := (cfL k).continuous.comp S.continuous_uX
    simp_rw [← cfL_apply]
    exact this.measurable
  obtain ⟨A, hAm, hA2, hw, φ, hφ, hae⟩ := exists_spacetime_limit T (FgS T u)
    (fun n => measurable_cutGrad_fam hv (n : ℝ))
    (fun n r => by
      have h1 : MemLp (cutGrad (⇑(uX T u r)) (n : ℝ)) 2 (haar d) :=
        memLp_piLp_iff.mpr fun j => memLp_coordPartial_cutoff _ _ j
      exact h1)
    (fun n => S.continuous_cutGrad (n : ℝ))
    (fun n m hnm r _ => by
      have h1 := integral_sub_sq_cutGrad (f := ⇑(uX T u r)) (R := (n : ℝ)) (R' := (m : ℝ))
        (by exact_mod_cast hnm)
      exact h1)
    (‖ρ0‖ ^ 2 + T * ((g + b) * (2 * M)) ^ 2)
    (fun n => by
      have := S.H1_bound_uX (n : ℝ)
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le S.hT]
      exact this)
  refine ⟨A, hAm, hA2, hw, ?_⟩
  filter_upwards [hae] with r hr
  obtain ⟨hr1, hr2⟩ := hr
  refine isWeakGradient_of_limit (P := fun n x => fourierCutoff (⇑(uX T u r)) ((φ n : ℕ) : ℝ) x)
    (Q := fun n x => cutGrad (⇑(uX T u r)) ((φ n : ℕ) : ℝ) x) (Lp.memLp _) hr1
    (fun n => isWeakGradient_cutoff_cutGrad _) ?_ hr2
  exact (tendsto_integral_sq_fourierCutoff_sub (Lp.memLp (uX T u r))).comp
    (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)

theorem MildFlow.exists_flux_limit (S : MildFlow h ρ0 T M u) :
    ∃ K : ℝ × Torus d → Tangent d, Measurable K ∧ MemLp K 2 (tmeas d T) ∧
      (∀ W : ℝ × Torus d → Tangent d, MemLp W 2 (tmeas d T) →
        Tendsto (fun n : ℕ => ∫ p, ⟪FkS h T u n p, W p⟫ ∂tmeas d T) atTop
          (𝓝 (∫ p, ⟪K p, W p⟫ ∂tmeas d T))) ∧
      (∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), (fun x => K (r, x)) =ᵐ[haar d] ⇑(Nvec h (uX T u r))) := by
  have hv : ∀ j k, Measurable (fun r => fourierCoeff (fun y => (⇑(Nvec h (uX T u r))) y j) k) := by
    intro j k
    have := ((cfL k).comp (coordL j)).continuous.comp S.continuous_NvecX
    have e : (fun r => fourierCoeff (fun y => (⇑(Nvec h (uX T u r))) y j) k) =
        fun r => ((cfL k).comp (coordL j)) (Nvec h (uX T u r)) := by
      funext r
      simp only [ContinuousLinearMap.comp_apply, cfL_apply]
      exact (fourierCoeff_congr_ae (coeFn_coordL j _).symm k)
    rw [e]
    exact this.measurable
  obtain ⟨K, hKm, hK2, hw, φ, hφ, hae⟩ := exists_spacetime_limit T (FkS h T u)
    (fun n => measurable_fourierCutoffGrad_fam hv (n : ℝ))
    (fun n r => by
      have h1 : MemLp (fourierCutoffGrad (⇑(Nvec h (uX T u r))) (n : ℝ)) 2 (haar d) :=
        memLp_piLp_iff.mpr fun j => memLp_fourierCutoff _ _
      exact h1)
    (fun n => S.continuous_cutN (n : ℝ))
    (fun n m hnm r _ => by
      have h1 := integral_sub_sq_fourierCutoffGrad (F := ⇑(Nvec h (uX T u r))) (R := (n : ℝ))
        (R' := (m : ℝ)) (by exact_mod_cast hnm)
      exact h1)
    (T * ((g + b) * (2 * M)) ^ 2)
    (fun n => by
      have hN : ∫ s in (0 : ℝ)..T, ∫ x, ‖fourierCutoffGrad (⇑(Nvec h (uX T u s))) (n : ℝ) x‖ ^ 2 ∂haar d ≤
          T * ((g + b) * (2 * M)) ^ 2 := by
        have : ∫ s in (0 : ℝ)..T, ((g + b) * (2 * M)) ^ 2 = T * ((g + b) * (2 * M)) ^ 2 := by
          simp
        rw [← this]
        refine intervalIntegral.integral_mono_on S.hT ((S.continuous_cutN _).intervalIntegrable _ _)
          (by simp) fun s _ => ?_
        refine (integral_norm_sq_fourierCutoffGrad_le (Lp.memLp _) _).trans ?_
        rw [← Lp_norm_sq_eq]
        exact pow_le_pow_left₀ (norm_nonneg _) (S.norm_N_le s) 2
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le S.hT]
      exact hN)
  refine ⟨K, hKm, hK2, hw, ?_⟩
  filter_upwards [hae] with r hr
  obtain ⟨hr1, hr2⟩ := hr
  refine ae_eq_of_two_limits hr1 (Lp.memLp _) (F := fun n x => FkS h T u (φ n) (r, x)) 
    (fun n => by
      have h1 : MemLp (fourierCutoffGrad (⇑(Nvec h (uX T u r))) ((φ n : ℕ) : ℝ)) 2 (haar d) :=
        memLp_piLp_iff.mpr fun j => memLp_fourierCutoff _ _
      exact h1) hr2 ?_
  exact (tendsto_integral_norm_sq_cutoffGrad_sub (Lp.memLp (Nvec h (uX T u r)))).comp
    (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)

end Limits

end PartC

section PartE

variable {d : ℕ}

theorem integrable_inner_of_memLp_two {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F W : α → Tangent d} (hF : MemLp F 2 μ) (hW : MemLp W 2 μ) :
    Integrable (fun p => ⟪F p, W p⟫) μ := by
  have h1 := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hF
  have h2 := (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).1 hW
  refine Integrable.mono' ((h1.add h2).const_mul (1/2 : ℝ))
    (hF.aestronglyMeasurable.inner hW.aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  have := abs_real_inner_le_norm (F p) (W p)
  simp only [Pi.add_apply]
  nlinarith [norm_nonneg (F p), norm_nonneg (W p), sq_nonneg (‖F p‖ - ‖W p‖)]

theorem continuous_gradT {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) :
    Continuous (gradT φ) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => hφ.continuous_coordPartial j)

theorem exists_bound_gradT {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) :
    ∃ C : ℝ, ∀ x, ‖gradT φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (continuous_gradT hφ).continuousOn
  exact ⟨C, fun x => hC x (mem_univ x)⟩

/-- The space-time test field `1_{[s,t]}(r) ∇φ(x)`. -/
noncomputable def Wst (s t : ℝ) (φ : Torus d → ℝ) (p : ℝ × Torus d) : Tangent d :=
  (Icc s t).indicator (fun _ => (1 : ℝ)) p.1 • gradT φ p.2

theorem memLp_Wst {T : ℝ} {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) (s t : ℝ) :
    MemLp (Wst s t φ) 2 (tmeas d T) := by
  obtain ⟨C, hC⟩ := exists_bound_gradT hφ
  have hm : Measurable (Wst s t φ) := by
    unfold Wst
    exact Measurable.smul (((measurable_const.indicator measurableSet_Icc).comp measurable_fst :
      Measurable fun p : ℝ × Torus d => (Icc s t).indicator (fun _ => (1 : ℝ)) p.1))
      ((continuous_gradT hφ).measurable.comp measurable_snd)
  have : IsFiniteMeasure (tmeas d T) := inferInstance
  have hb : MemLp (Wst s t φ) ⊤ (tmeas d T) := MemLp.of_bound hm.aestronglyMeasurable C
    (Eventually.of_forall fun p => ?_)
  · exact hb.mono_exponent le_top
  unfold Wst
  rw [norm_smul]
  have h1 : ‖(Icc s t).indicator (fun _ => (1 : ℝ)) p.1‖ ≤ 1 := by
    by_cases hp : p.1 ∈ Icc s t <;> simp [hp]
  calc _ ≤ 1 * C := mul_le_mul h1 (hC _) (norm_nonneg _) zero_le_one
    _ = C := one_mul C

theorem memLp_Wphi {T : ℝ} {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) :
    MemLp (fun p : ℝ × Torus d => gradT φ p.2) 2 (tmeas d T) := by
  obtain ⟨C, hC⟩ := exists_bound_gradT hφ
  have hm : Measurable (fun p : ℝ × Torus d => gradT φ p.2) :=
    (continuous_gradT hφ).measurable.comp measurable_snd
  have : IsFiniteMeasure (tmeas d T) := inferInstance
  have hb : MemLp (fun p : ℝ × Torus d => gradT φ p.2) ⊤ (tmeas d T) :=
    MemLp.of_bound hm.aestronglyMeasurable C (Eventually.of_forall fun p => hC _)
  exact hb.mono_exponent le_top

theorem integral_inner_Wst {T : ℝ} {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ)
    {F : ℝ × Torus d → Tangent d} (hF : MemLp F 2 (tmeas d T)) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t ≤ T) :
    IntervalIntegrable (fun r => ∫ x, ⟪F (r, x), gradT φ x⟫ ∂haar d) volume s t ∧
    ∫ p, ⟪F p, Wst s t φ p⟫ ∂tmeas d T =
      ∫ r in s..t, ∫ x, ⟪F (r, x), gradT φ x⟫ ∂haar d := by
  have hG : Integrable (fun p : ℝ × Torus d => ⟪F p, gradT φ p.2⟫) (tmeas d T) :=
    integrable_inner_of_memLp_two hF (memLp_Wphi hφ)
  have hI : Integrable (fun r => ∫ x, ⟪F (r, x), gradT φ x⟫ ∂haar d)
      (volume.restrict (Icc (0 : ℝ) T)) := hG.integral_prod_left
  have hsub : Icc s t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc hs ht
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hst]
    exact hI.mono_measure (Measure.restrict_mono hsub le_rfl)
  · have e : ∀ p : ℝ × Torus d, ⟪F p, Wst s t φ p⟫ =
        (Icc s t).indicator (fun _ => (1 : ℝ)) p.1 * ⟪F p, gradT φ p.2⟫ := by
      intro p
      unfold Wst
      rw [real_inner_smul_right]
    simp_rw [e]
    have hint : Integrable (fun p : ℝ × Torus d =>
        (Icc s t).indicator (fun _ => (1 : ℝ)) p.1 * ⟪F p, gradT φ p.2⟫) (tmeas d T) :=
      hG.bdd_mul (c := 1) ((measurable_const.indicator measurableSet_Icc).comp
        measurable_fst).aestronglyMeasurable (Eventually.of_forall fun p => by
          by_cases hp : p.1 ∈ Icc s t <;> simp [hp])
    rw [integral_tmeas_eq hint]
    have e2 : ∀ r : ℝ, ∫ x, (Icc s t).indicator (fun _ => (1 : ℝ)) r * ⟪F (r, x), gradT φ x⟫ ∂haar d =
        (Icc s t).indicator (fun r => ∫ x, ⟪F (r, x), gradT φ x⟫ ∂haar d) r := by
      intro r
      by_cases hr : r ∈ Icc s t
      · simp [hr]
      · simp [hr]
    simp_rw [e2]
    rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.mpr hsub, intervalIntegral.integral_of_le hst, integral_Icc_eq_integral_Ioc]

end PartE

section PartF

variable {d : ℕ} {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}
variable {h : MeanFieldData G B g b} {ρ0 : L2s d} {T M : ℝ} {u : ℝ → L2s d}

theorem MildFlow.memLp_FgS (S : MildFlow h ρ0 T M u) (n : ℕ) : MemLp (FgS T u n) 2 (tmeas d T) := by
  have hv : ∀ k, Measurable (fun r => fourierCoeff (⇑(uX T u r)) k) := fun k => by
    have := (cfL k).continuous.comp S.continuous_uX
    simp_rw [← cfL_apply]
    exact this.measurable
  have hm : Measurable (FgS T u n) := measurable_cutGrad_fam hv (n : ℝ)
  refine memLp_two_tmeas_of_slices hm.aestronglyMeasurable (Eventually.of_forall fun r => ?_) ?_
  · have h1 : MemLp (cutGrad (⇑(uX T u r)) (n : ℝ)) 2 (haar d) :=
      memLp_piLp_iff.mpr fun j => memLp_coordPartial_cutoff _ _ j
    exact h1
  · exact (S.continuous_cutGrad (n : ℝ)).continuousOn.integrableOn_Icc

theorem MildFlow.memLp_FkS (S : MildFlow h ρ0 T M u) (n : ℕ) : MemLp (FkS h T u n) 2 (tmeas d T) := by
  have hv : ∀ j k, Measurable (fun r => fourierCoeff (fun y => (⇑(Nvec h (uX T u r))) y j) k) := by
    intro j k
    have := ((cfL k).comp (coordL j)).continuous.comp S.continuous_NvecX
    have e : (fun r => fourierCoeff (fun y => (⇑(Nvec h (uX T u r))) y j) k) =
        fun r => ((cfL k).comp (coordL j)) (Nvec h (uX T u r)) := by
      funext r
      simp only [ContinuousLinearMap.comp_apply, cfL_apply]
      exact (fourierCoeff_congr_ae (coeFn_coordL j _).symm k)
    rw [e]
    exact this.measurable
  have hm : Measurable (FkS h T u n) := measurable_fourierCutoffGrad_fam hv (n : ℝ)
  refine memLp_two_tmeas_of_slices hm.aestronglyMeasurable (Eventually.of_forall fun r => ?_) ?_
  · have h1 : MemLp (fourierCutoffGrad (⇑(Nvec h (uX T u r))) (n : ℝ)) 2 (haar d) :=
      memLp_piLp_iff.mpr fun j => memLp_fourierCutoff _ _
    exact h1
  · exact (S.continuous_cutN (n : ℝ)).continuousOn.integrableOn_Icc

theorem MildFlow.exists_flux_fields (S : MildFlow h ρ0 T M u) :
    ∃ A K : ℝ × Torus d → Tangent d, Measurable A ∧ MemLp A 2 (tmeas d T) ∧
      Measurable K ∧ MemLp K 2 (tmeas d T) ∧
      (∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), IsWeakGradient (⇑(uX T u r)) (fun x => A (r, x))) ∧
      (∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
        (fun x => K (r, x)) =ᵐ[haar d] ⇑(Nvec h (uX T u r))) ∧
      ∀ φ : Torus d → ℝ, IsSmoothPeriodic φ → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        ∫ x, u t x * φ x ∂haar d - ∫ x, u s x * φ x ∂haar d =
          -∫ r in s..t, ∫ w, ∑ j, (A (r, w) + K (r, w)) j * coordPartial j φ w ∂haar d := by
  obtain ⟨A, hAm, hA2, hAw, hAg⟩ := S.exists_gradient_limit
  obtain ⟨K, hKm, hK2, hKw, hKe⟩ := S.exists_flux_limit
  refine ⟨A, K, hAm, hA2, hKm, hK2, hAg, hKe, fun φ hφ s t hs hst ht => ?_⟩
  have hφ2 : MemLp φ 2 (haar d) := hφ.memLp_top.mono_exponent le_top
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs, hst.trans ht⟩
  have htT : t ∈ Icc (0 : ℝ) T := ⟨hs.trans hst, ht⟩
  -- the limit of the left-hand side
  have hL : ∀ τ ∈ Icc (0 : ℝ) T, Tendsto
      (fun n : ℕ => ∫ x, fourierCutoff (⇑(u τ)) (n : ℝ) x * φ x ∂haar d) atTop
      (𝓝 (∫ x, u τ x * φ x ∂haar d)) := fun τ _ =>
    tendsto_integral_mul_of_sq (fun n => memLp_fourierCutoff _ _) (Lp.memLp _) hφ2
      ((tendsto_integral_sq_fourierCutoff_sub (Lp.memLp (u τ))).comp tendsto_natCast_atTop_atTop)
  -- the right-hand side
  have e1 : ∀ n : ℕ, ∫ p, ⟪FgS T u n p, Wst s t φ p⟫ ∂tmeas d T =
      ∫ r in s..t, ∫ x, ⟪cutGrad (⇑(uX T u r)) (n : ℝ) x, gradT φ x⟫ ∂haar d := fun n =>
    (integral_inner_Wst hφ (S.memLp_FgS n) hs hst ht).2
  have e2 : ∀ n : ℕ, ∫ p, ⟪FkS h T u n p, Wst s t φ p⟫ ∂tmeas d T =
      ∫ r in s..t, ∫ x, ⟪fourierCutoffGrad (⇑(Nvec h (uX T u r))) (n : ℝ) x, gradT φ x⟫ ∂haar d :=
    fun n => (integral_inner_Wst hφ (S.memLp_FkS n) hs hst ht).2
  have i1 : ∀ n : ℕ, IntervalIntegrable
      (fun r => ∫ x, ⟪cutGrad (⇑(uX T u r)) (n : ℝ) x, gradT φ x⟫ ∂haar d) volume s t :=
    fun n => (integral_inner_Wst hφ (S.memLp_FgS n) hs hst ht).1
  have i2 : ∀ n : ℕ, IntervalIntegrable
      (fun r => ∫ x, ⟪fourierCutoffGrad (⇑(Nvec h (uX T u r))) (n : ℝ) x, gradT φ x⟫ ∂haar d)
      volume s t := fun n => (integral_inner_Wst hφ (S.memLp_FkS n) hs hst ht).1
  have hR : Tendsto (fun n : ℕ => -∫ r in s..t, (∫ x, ⟪cutGrad (⇑(uX T u r)) (n : ℝ) x,
        gradT φ x⟫ ∂haar d + ∫ x, ⟪fourierCutoffGrad (⇑(Nvec h (uX T u r))) (n : ℝ) x,
        gradT φ x⟫ ∂haar d)) atTop
      (𝓝 (-(∫ p, ⟪A p, Wst s t φ p⟫ ∂tmeas d T + ∫ p, ⟪K p, Wst s t φ p⟫ ∂tmeas d T))) := by
    have := ((hAw _ (memLp_Wst hφ s t)).add (hKw _ (memLp_Wst hφ s t))).neg
    refine this.congr fun n => ?_
    rw [intervalIntegral.integral_add (i1 n) (i2 n), e1, e2]
  have hlim := (hL t htT).sub (hL s hsT)
  have hlim2 : Tendsto (fun n : ℕ => ∫ x, fourierCutoff (⇑(u t)) (n : ℝ) x * φ x ∂haar d -
      ∫ x, fourierCutoff (⇑(u s)) (n : ℝ) x * φ x ∂haar d) atTop
      (𝓝 (-(∫ p, ⟪A p, Wst s t φ p⟫ ∂tmeas d T + ∫ p, ⟪K p, Wst s t φ p⟫ ∂tmeas d T))) :=
    hR.congr fun n => (S.time_identity_cut hφ (n : ℝ) hs hst ht).symm
  rw [tendsto_nhds_unique hlim hlim2]
  -- identify the limit
  obtain ⟨hiA, eA⟩ := integral_inner_Wst hφ hA2 hs hst ht
  obtain ⟨hiK, eK⟩ := integral_inner_Wst hφ hK2 hs hst ht
  rw [eA, eK, ← intervalIntegral.integral_add hiA hiK]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  have hGA : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
      Integrable (fun x => ⟪A (r, x), gradT φ x⟫) (haar d) :=
    (integrable_inner_of_memLp_two hA2 (memLp_Wphi hφ)).prod_right_ae
  have hGK : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
      Integrable (fun x => ⟪K (r, x), gradT φ x⟫) (haar d) :=
    (integrable_inner_of_memLp_two hK2 (memLp_Wphi hφ)).prod_right_ae
  have hall := (ae_restrict_iff' measurableSet_Icc).1 (hGA.and hGK)
  filter_upwards [hall] with r hr hrI
  rw [uIoc_of_le hst] at hrI
  obtain ⟨h1, h2⟩ := hr ⟨hs.trans hrI.1.le, hrI.2.trans ht⟩
  rw [← integral_add h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [inner_gradT]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp [add_mul]

end PartF

section PartG

variable {d : ℕ} {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}
variable {h : MeanFieldData G B g b} {ρ0 : L2s d} {T M : ℝ} {u : ℝ → L2s d}

theorem MildFlow.exists_setting (S : MildFlow h ρ0 T M u) :
    ∃ A K : ℝ × Torus d → Tangent d, Measurable A ∧ MemLp A 2 (tmeas d T) ∧
      Measurable K ∧ MemLp K 2 (tmeas d T) ∧
      (∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
        (fun x => K (r, x)) =ᵐ[haar d] ⇑(Nvec h (uX T u r))) ∧
      lip026c_Setting T (fun t => ⇑(u t)) (fun r x => A (r, x)) (fun r x => A (r, x) + K (r, x)) := by
  obtain ⟨A, K, hAm, hA2, hKm, hK2, hAg, hKe, hweak⟩ := S.exists_flux_fields
  refine ⟨A, K, hAm, hA2, hKm, hK2, hKe, ?_⟩
  have hJ2 : MemLp (A + K) 2 (tmeas d T) := hA2.add hK2
  refine ⟨⟨fun t _ => (Lp.memLp (u t)).integrable one_le_two, ?_, ?_, hweak⟩,
    ⟨2 * M, fun t ht => S.bound t ht⟩, ?_, ?_, ?_, ?_⟩
  · have : Measurable (A + K) := hAm.add hKm
    exact this
  · exact hJ2.integrable one_le_two
  · have h1 := (ae_restrict_iff' measurableSet_Icc).1 hAg
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [h1] with r hr hrI
    have := hr hrI
    rwa [S.uX_of_mem hrI] at this
  · exact hAm
  · exact (memLp_two_iff_integrable_sq_norm hA2.aestronglyMeasurable).1 hA2
  · exact (memLp_two_iff_integrable_sq_norm hJ2.aestronglyMeasurable).1 hJ2

theorem inner_lower_bound {a k : Tangent d} {v B0 : ℝ} (hv : v < 0) (hk : ‖k‖ ≤ B0 * |v|) :
    -(B0 ^ 2 / 4) * (min v 0) ^ 2 ≤ ⟪a, a + k⟫ := by
  have e : ⟪a, a + k⟫ = ‖a‖ ^ 2 + ⟪a, k⟫ := by
    rw [inner_add_right, real_inner_self_eq_norm_sq]
  have h1 := abs_real_inner_le_norm a k
  have h2 := (abs_le.1 h1).1
  rw [min_eq_left hv.le, e]
  have h3 : ‖k‖ ^ 2 ≤ B0 ^ 2 * v ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hk 2
    rw [mul_pow, sq_abs] at this
    exact this
  nlinarith [sq_nonneg (‖a‖ - ‖k‖ / 2), norm_nonneg a, norm_nonneg k]

theorem slice_neg_bound (h : MeanFieldData G B g b) (v : L2s d) {a k : Torus d → Tangent d}
    (ha : MemLp a 2 (haar d)) (hk : MemLp k 2 (haar d)) (hke : k =ᵐ[haar d] ⇑(Nvec h v)) :
    -((g + b) ^ 2 / 4) * ∫ x, (min (v x) 0) ^ 2 ∂haar d ≤
      ∫ x, (if v x < 0 then ⟪a x, a x + k x⟫ else 0) ∂haar d := by
  have hint : Integrable (fun x => ⟪a x, (a + k) x⟫) (haar d) :=
    integrable_inner_of_memLp_two ha (ha.add hk)
  have hms : MeasurableSet {x | v x < 0} :=
    measurableSet_lt (Lp.stronglyMeasurable v).measurable measurable_const
  have hI1 : Integrable (fun x => if v x < 0 then ⟪a x, a x + k x⟫ else 0) (haar d) := by
    have := hint.indicator hms
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp [Set.indicator_apply]
  have hv2 : Integrable (fun x => v x ^ 2) (haar d) := (Lp.memLp v).integrable_sq
  have hI2 : Integrable (fun x => (min (v x) 0) ^ 2) (haar d) := by
    refine Integrable.mono' hv2 (((Lp.stronglyMeasurable v).measurable.min
      measurable_const).pow_const 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rcases le_total (v x) 0 with h0 | h0
    · rw [min_eq_left h0]
    · rw [min_eq_right h0]; nlinarith [sq_nonneg (v x)]
  rw [← integral_const_mul]
  refine integral_mono_ae (hI2.const_mul _) hI1 ?_
  filter_upwards [hke, coeFn_Nvec h v] with x hx1 hx2
  by_cases hx : v x < 0
  · simp only [hx, ite_true]
    refine inner_lower_bound hx ?_
    rw [hx1, hx2]
    exact norm_meanFieldN_le h ((Lp.memLp v).integrable one_le_two) x
  · simp only [hx, ite_false]
    have : min (v x) 0 = 0 := min_eq_right (not_lt.1 hx)
    rw [this]; simp

end PartG

section PartH

variable {d : ℕ} {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}
variable {h : MeanFieldData G B g b} {ρ0 : L2s d} {T M : ℝ} {u : ℝ → L2s d}

/-- The squared `L²` norm of the negative part. -/
noncomputable def negSq (v : L2s d) : ℝ := ∫ x, (min (v x) 0) ^ 2 ∂haar d

theorem negSq_eq (v : L2s d) : negSq v = ‖Lp.negPart v‖ ^ 2 := by
  rw [Lp_norm_sq_eq']
  unfold negSq
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_negPart v] with x hx
  rw [hx]; simp

theorem continuous_negSq : Continuous (negSq : L2s d → ℝ) := by
  have : (negSq : L2s d → ℝ) = fun v => ‖Lp.negPart v‖ ^ 2 := funext negSq_eq
  rw [this]
  exact (continuous_norm.comp Lp.continuous_negPart).pow 2

theorem negSq_nonneg (v : L2s d) : 0 ≤ negSq v := integral_nonneg fun _ => sq_nonneg _

theorem MildFlow.negSq_uX_continuous (S : MildFlow h ρ0 T M u) :
    Continuous fun r => negSq (uX T u r) := continuous_negSq.comp S.continuous_uX

theorem MildFlow.negSq_bound (S : MildFlow h ρ0 T M u) (h0 : 0 ≤ᵐ[haar d] ⇑ρ0) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    negSq (uX T u t) ≤ ((g + b) ^ 2 / 2) * ∫ r in (0 : ℝ)..t, negSq (uX T u r) := by
  obtain ⟨A, K, -, -, -, -, hKe, hS⟩ := S.exists_setting
  have hch := lip026c_chain_rule_neg hS le_rfl ht.1 ht.2
  have hu0 : negSq (u 0) = 0 := by
    unfold negSq
    rw [S.u_zero]
    have : ∀ᵐ x ∂haar d, (min (ρ0 x) 0) ^ 2 = 0 := by
      filter_upwards [h0] with x hx
      rw [min_eq_right (by simpa using hx)]; simp
    rw [integral_congr_ae this]; simp
  have e1 : ∀ τ, ∫ x, (min (u τ x) 0) ^ 2 / 2 ∂haar d = negSq (u τ) / 2 := fun τ => by
    unfold negSq; rw [integral_div]
  rw [e1, e1, hu0] at hch
  rw [S.uX_of_mem ht]
  set F : ℝ → ℝ := fun r => ∫ x, (if u r x < 0 then ⟪A (r, x), A (r, x) + K (r, x)⟫ else 0) ∂haar d
    with hF
  have hcont : Continuous fun r => negSq (uX T u r) := S.negSq_uX_continuous
  have hψI : IntervalIntegrable (fun r => negSq (uX T u r)) volume 0 t := hcont.intervalIntegrable _ _
  have hae : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
      -((g + b) ^ 2 / 4) * negSq (uX T u r) ≤ F r := by
    have h1 := hS.grad
    filter_upwards [h1, hKe, ae_restrict_mem measurableSet_Icc] with r hr hk hrI
    have hkm : MemLp (fun x => K (r, x)) 2 (haar d) := (Lp.memLp (Nvec h (uX T u r))).ae_eq hk.symm
    rw [S.uX_of_mem hrI] at hk ⊢
    exact slice_neg_bound h (u r) (a := fun x => A (r, x)) (k := fun x => K (r, x))
      hr.memLp_grad hkm hk
  have hae' : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) t)),
      -((g + b) ^ 2 / 4) * negSq (uX T u r) ≤ F r :=
    ae_mono (Measure.restrict_mono (Icc_subset_Icc_right ht.2) le_rfl) hae
  by_cases hI : IntervalIntegrable F volume 0 t
  · have hm := intervalIntegral.integral_mono_ae_restrict ht.1 (hψI.const_mul (-((g + b) ^ 2 / 4)))
      hI hae'
    rw [intervalIntegral.integral_const_mul] at hm
    nlinarith
  · rw [intervalIntegral.integral_undef hI] at hch
    have h0 : 0 ≤ ∫ r in (0 : ℝ)..t, negSq (uX T u r) :=
      intervalIntegral.integral_nonneg ht.1 fun r _ => negSq_nonneg _
    have : 0 ≤ (g + b) ^ 2 / 2 * ∫ r in (0 : ℝ)..t, negSq (uX T u r) := by positivity
    linarith


theorem MildFlow.negSq_eq_zero (S : MildFlow h ρ0 T M u) (h0 : 0 ≤ᵐ[haar d] ⇑ρ0) :
    ∀ t ∈ Icc (0 : ℝ) T, negSq (u t) = 0 := by
  have hcont : Continuous fun r => negSq (uX T u r) := S.negSq_uX_continuous
  have hd : ∀ t, HasDerivAt (fun x => ∫ r in (0 : ℝ)..x, negSq (uX T u r))
      (negSq (uX T u t)) t := fun t => (hcont.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hz : ∀ x ∈ Icc (0 : ℝ) T, ∫ r in (0 : ℝ)..x, negSq (uX T u r) = 0 := by
    refine eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := (g + b) ^ 2 / 2)
      (f' := fun r => negSq (uX T u r)) ?_ (fun x _ => (hd x).hasDerivWithinAt) (by simp) ?_
    · exact (continuous_iff_continuousAt.2 fun t => (hd t).continuousAt).continuousOn
    · intro x hx
      have hx' : x ∈ Icc (0 : ℝ) T := ⟨hx.1, hx.2.le⟩
      have h1 := S.negSq_bound h0 hx'
      have h2 : 0 ≤ ∫ r in (0 : ℝ)..x, negSq (uX T u r) :=
        intervalIntegral.integral_nonneg hx.1 fun r _ => negSq_nonneg _
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (negSq_nonneg _), abs_of_nonneg h2]
      exact h1
  intro t ht
  have h1 := S.negSq_bound h0 ht
  rw [hz t ht, mul_zero] at h1
  rw [S.uX_of_mem ht] at h1
  exact le_antisymm h1 (negSq_nonneg _)

theorem MildFlow.nonneg_ae (S : MildFlow h ρ0 T M u) (h0 : 0 ≤ᵐ[haar d] ⇑ρ0) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ᵐ[haar d] ⇑(u t) := by
  have h1 := S.negSq_eq_zero h0 t ht
  rw [negSq_eq] at h1
  have h2 : Lp.negPart (u t) = 0 := by
    rw [← norm_eq_zero]
    exact pow_eq_zero_iff (two_ne_zero) |>.1 h1
  have h3 : ∀ᵐ x ∂haar d, Lp.negPart (u t) x = 0 := by
    rw [h2]; exact Lp.coeFn_zero _ _ _
  filter_upwards [Lp.coeFn_negPart (u t), h3] with x hx hx0
  rw [hx] at hx0
  have : min (u t x) 0 = 0 := by linarith
  exact min_eq_right_iff.1 this

end PartH

section PartI

variable {d : ℕ} {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}

theorem normPos_ae_eq_self {v : Torus d → ℝ}
    (h0 : 0 ≤ᵐ[haar d] v) (hm : ∫ x, v x ∂haar d = 1) : normPos v =ᵐ[haar d] v := by
  have hI : ∫ y, max (v y) 0 ∂haar d = 1 := by
    refine Eq.trans (integral_congr_ae ?_) hm
    filter_upwards [h0] with y hy
    exact max_eq_left hy
  filter_upwards [h0] with y hy
  unfold normPos
  rw [hI, max_self, div_one]
  exact max_eq_left hy

theorem nonlinearity_eq_original (h : MeanFieldData G B g b) (v : L2s d)
    (h0 : 0 ≤ᵐ[haar d] ⇑v) (hm : ∫ x, v x ∂haar d = 1) :
    ⇑(Nvec h v) =ᵐ[haar d] fun x => v x • (G x + ∫ y, v y • B x y ∂haar d) := by
  have hn := normPos_ae_eq_self h0 hm
  filter_upwards [coeFn_Nvec h v] with x hx
  rw [hx, meanFieldN_eq]
  unfold meanFieldConv
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [hn] with y hy
  rw [hy]

/-- **LIP027.** The local fixed point `ρ` of the modified mean-field equation, started from a
probability density `ρ0 ≥ 0`, enjoys the regularity, energy and mass statements of
`mildFlow_regularity_energy_mass`, is nonnegative with mass one at every time in `[0,T]`, satisfies
`P ρ_t = ρ_t` (so that the modified nonlinearity coincides with the original one
`ρ (∇V + B ∗ ρ)`). -/
theorem flow_energy_regularity_positivity_and_mass {h : MeanFieldData G B g b} {ρ0 : L2s d}
    {T M : ℝ} {u : ℝ → L2s d} (S : MildFlow h ρ0 T M u) (h0 : 0 ≤ᵐ[haar d] ⇑ρ0)
    (hm : ∫ x, ρ0 x ∂haar d = 1) :
    (ContinuousOn u (Icc 0 T) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂haar d, |u t x| ≤ 2 * M) ∧
      (∀ R : ℝ, ∫ s in (0 : ℝ)..T, ∫ x, ‖cutGrad (⇑(u s)) R x‖ ^ 2 ∂haar d ≤
        ‖ρ0‖ ^ 2 + T * ((g + b) * (2 * M)) ^ 2) ∧
      (∀ k : Fin d → ℤ, ContinuousOn (MildFlow.modeDeriv h u k) (Icc 0 T) ∧
        ∀ t ∈ Icc (0 : ℝ) T,
          cfL k (u t) = cfL k ρ0 + ∫ s in (0 : ℝ)..t, MildFlow.modeDeriv h u k s) ∧
      (∀ R : ℝ, ∫ s in (0 : ℝ)..T,
          ∑ k ∈ ballSet R, ‖MildFlow.modeDeriv h u k s‖ ^ 2 / (1 + gradWeight k) ≤
        2 * (‖ρ0‖ ^ 2 + T * ((g + b) * (2 * M)) ^ 2) + 2 * (T * ((g + b) * (2 * M)) ^ 2)) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∫ x, (u t : Torus d → ℝ) x ∂haar d = ∫ x, (ρ0 : Torus d → ℝ) x ∂haar d) ∧
      (∀ R : ℝ, ∀ t ∈ Icc (0 : ℝ) T,
        ∫ x, (fourierCutoff (⇑(u t)) R x) ^ 2 ∂haar d +
            ∫ s in (0 : ℝ)..t, ∫ x, ‖cutGrad (⇑(u s)) R x‖ ^ 2 ∂haar d ≤
          ∫ x, (fourierCutoff (⇑ρ0) R x) ^ 2 ∂haar d +
            ∫ s in (0 : ℝ)..t, ∫ x, ‖fourierCutoffGrad (⇑(Nvec h (u s))) R x‖ ^ 2 ∂haar d)) ∧
    (∀ t ∈ Icc (0 : ℝ) T, 0 ≤ᵐ[haar d] ⇑(u t)) ∧
    (∀ t ∈ Icc (0 : ℝ) T, ∫ x, u t x ∂haar d = 1) ∧
    (∀ t ∈ Icc (0 : ℝ) T, normPos (⇑(u t)) =ᵐ[haar d] ⇑(u t)) ∧
    (∀ t ∈ Icc (0 : ℝ) T, meanFieldConv B (normPos (⇑(u t))) = meanFieldConv B (⇑(u t))) ∧
    (∀ t ∈ Icc (0 : ℝ) T, ⇑(Nvec h (u t)) =ᵐ[haar d]
      fun x => u t x • (G x + ∫ y, u t y • B x y ∂haar d)) := by
  have hmass : ∀ t ∈ Icc (0 : ℝ) T, ∫ x, u t x ∂haar d = 1 := fun t ht => by
    rw [S.mass_const ht]; exact hm
  have hn : ∀ t ∈ Icc (0 : ℝ) T, normPos (⇑(u t)) =ᵐ[haar d] ⇑(u t) := fun t ht =>
    normPos_ae_eq_self (S.nonneg_ae h0 ht) (hmass t ht)
  exact ⟨mildFlow_regularity_energy_mass S, fun t ht => S.nonneg_ae h0 ht, hmass, hn,
    fun t ht => meanFieldConv_congr_ae (hn t ht),
    fun t ht => nonlinearity_eq_original h (u t) (S.nonneg_ae h0 ht) (hmass t ht)⟩

end PartI

end DGPS.Lipschitz

