import FullLabeledLSI.Examples.Paper.Sec9Regularity
import FullLabeledLSI.Examples.Paper.Sec9DeficitCompact

/-!
# Lemma 9.6, part A: a priori bounds and existence of minimizers of `S_{r,A}`

Lane C of the Section 9 formalization.  For continuous `A` with `|A| ≤ R` and `0 ≤ r ≤ 1`:

* `Sfun_one`: `S_{r,A}(1) = ∫ A`;
* coercivity `Sfun_lower` (from the logarithmic Sobolev inequality `circle_quantitative_lsi_aux`);
* `sMin_bounds`: a minimizer has `-R ≤ S ≤ R`, Dirichlet energy `≤ R` and `f ≤ 1 + √R + R` a.e.;
* `exists_sMin`: the direct method, using `h1_compact`.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL.Ex.SR

open SharpLSI FL.Ex.Reg FL.Ex.Cmp

theorem weakGrad_one_ae : (fun x => weakGrad (fun _ : Torus 1 => (1 : ℝ)) x 0) =ᵐ[haar 1]
    fun _ => (0 : ℝ) := by
  filter_upwards [weakGrad_ae_eq (isWeakGrad_const (ι := Fin 1) (1 : ℝ))] with x hx
  rw [hx]; rfl

theorem memH1_one : MemH1 (haar 1) (fun _ : Torus 1 => (1 : ℝ)) := by
  refine ⟨⟨0, isWeakGrad_const (ι := Fin 1) (1 : ℝ)⟩, memLp_const 1, ?_⟩
  have h : (fun x => Real.sqrt (sqNorm (weakGrad (fun _ : Torus 1 => (1 : ℝ)) x))) =ᵐ[haar 1]
      fun _ => (0 : ℝ) := by
    filter_upwards [weakGrad_ae_eq (isWeakGrad_const (ι := Fin 1) (1 : ℝ))] with x hx
    rw [hx]; simp [sqNorm]
  exact (memLp_const (0 : ℝ)).ae_eq h.symm

theorem Sfun_one (r : ℝ) (A : Torus 1 → ℝ) : Sfun r A (fun _ => 1) = ∫ x, A x ∂haar 1 := by
  have h1 : ∫ x, weakGrad (fun _ : Torus 1 => (1 : ℝ)) x 0 ^ 2 ∂haar 1 = 0 := by
    have : ∫ x, weakGrad (fun _ : Torus 1 => (1 : ℝ)) x 0 ^ 2 ∂haar 1 = ∫ _x : Torus 1, (0 : ℝ) ∂haar 1 :=
      integral_congr_ae (weakGrad_one_ae.mono fun x hx => by simp only at hx ⊢; rw [hx]; norm_num)
    simpa using this
  have hk : (klDiv (densMeasure (fun _ : Torus 1 => (1 : ℝ) ^ 2)) (haar 1)).toReal = 0 := by
    rw [klDiv_toReal_eq_integral (fun x => by positivity) (by simp)]
    simp [klFun_one]
  unfold Sfun
  simp only [one_pow, mul_one] at hk ⊢
  rw [h1, hk]
  ring

/-- Coercivity: the entropy is controlled by the Dirichlet energy. -/
theorem entropy_le_energy {f : Torus 1 → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hH : MemH1 (haar 1) f)
    (h1 : ∫ x, f x ^ 2 ∂haar 1 = 1) :
    0 ≤ (klDiv (densMeasure fun x => f x ^ 2) (haar 1)).toReal ∧
      aCos * (klDiv (densMeasure fun x => f x ^ 2) (haar 1)).toReal ≤
        2 * ∫ x, weakGrad f x 0 ^ 2 ∂haar 1 := by
  have hs : (fun x => Real.sqrt (f x ^ 2)) = f := funext fun x => Real.sqrt_sq (hf0 x)
  have hMem : MemH1 (haar 1) (fun x => Real.sqrt (f x ^ 2)) := by rw [hs]; exact hH
  obtain ⟨-, -, -, h4⟩ := circle_quantitative_lsi_aux (ρ := fun x => f x ^ 2) (fun x => sq_nonneg _) h1 hMem
  rw [fisherInfo_densMeasure_eq (fun x => sq_nonneg _) h1 hMem, hs,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (integral_nonneg fun x => sq_nonneg _))] at h4
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have : 0 ≤ aCos / 6 * (klDiv (densMeasure fun x => f x ^ 2) (haar 1)).toReal ^ 2 := by
    have : 0 < aCos := by unfold aCos; positivity
    positivity
  linarith

theorem aCos_ge : (36 : ℝ) ≤ aCos := by
  unfold aCos
  nlinarith [Real.pi_gt_three]

theorem abs_integral_A_le {A f : Torus 1 → ℝ} (hA : Continuous A) {R : ℝ} (hR : ∀ x, |A x| ≤ R)
    (hH : MemH1 (haar 1) f) (h1 : ∫ x, f x ^ 2 ∂haar 1 = 1) :
    |∫ x, A x * f x ^ 2 ∂haar 1| ≤ R := by
  have hf2 : Integrable (fun x => f x ^ 2) (haar 1) := hH.2.1.integrable_sq
  have hi : Integrable (fun x => A x * f x ^ 2) (haar 1) := by
    have := hf2.mul_bdd hA.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hR x)
    simpa [mul_comm] using this
  rw [abs_le]
  constructor
  · have : ∫ x, (-R) * f x ^ 2 ∂haar 1 ≤ ∫ x, A x * f x ^ 2 ∂haar 1 :=
      integral_mono (hf2.const_mul _) hi fun x =>
        mul_le_mul_of_nonneg_right (neg_le_of_abs_le (hR x)) (sq_nonneg _)
    rw [integral_const_mul, h1] at this
    linarith
  · have : ∫ x, A x * f x ^ 2 ∂haar 1 ≤ ∫ x, R * f x ^ 2 ∂haar 1 :=
      integral_mono hi (hf2.const_mul _) fun x =>
        mul_le_mul_of_nonneg_right (le_of_abs_le (hR x)) (sq_nonneg _)
    rw [integral_const_mul, h1] at this
    linarith

/-- Lower bound for the functional. -/
theorem Sfun_lower {r : ℝ} (hr1 : r ≤ 1) {A f : Torus 1 → ℝ} (hA : Continuous A)
    {R : ℝ} (hR : ∀ x, |A x| ≤ R) (hf0 : ∀ x, 0 ≤ f x) (hH : MemH1 (haar 1) f)
    (h1 : ∫ x, f x ^ 2 ∂haar 1 = 1) :
    2 * ∫ x, weakGrad f x 0 ^ 2 ∂haar 1 - R ≤ Sfun r A f := by
  obtain ⟨hH0, hHle⟩ := entropy_le_energy hf0 hH h1
  have hW0 : 0 ≤ ∫ x, weakGrad f x 0 ^ 2 ∂haar 1 := integral_nonneg fun x => sq_nonneg _
  have hAi := (abs_le.1 (abs_integral_A_le hA hR hH h1)).1
  have hc := aCos_ge
  unfold Sfun
  -- 2 r H ≤ r aCos H / 18 ... : H ≤ 2W/aCos ≤ W/18, and 2 r H ≤ 2 H ≤ W/9
  have hHW : (klDiv (densMeasure fun x => f x ^ 2) (haar 1)).toReal ≤
      (2 * ∫ x, weakGrad f x 0 ^ 2 ∂haar 1) / aCos := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have h2 : (2 * ∫ x, weakGrad f x 0 ^ 2 ∂haar 1) / aCos ≤ (∫ x, weakGrad f x 0 ^ 2 ∂haar 1) / 18 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hr1 hH0]

theorem Sfun_upper {r : ℝ} (hr0 : 0 ≤ r) {A f : Torus 1 → ℝ} (hA : Continuous A)
    {R : ℝ} (hR : ∀ x, |A x| ≤ R) (hf0 : ∀ x, 0 ≤ f x) (hH : MemH1 (haar 1) f)
    (h1 : ∫ x, f x ^ 2 ∂haar 1 = 1) :
    Sfun r A f ≤ 4 * ∫ x, weakGrad f x 0 ^ 2 ∂haar 1 + R := by
  obtain ⟨hH0, -⟩ := entropy_le_energy hf0 hH h1
  have hAi := (abs_le.1 (abs_integral_A_le hA hR hH h1)).2
  unfold Sfun
  nlinarith [mul_nonneg hr0 hH0]

/-- Sup bound from the Dirichlet energy. -/
theorem ae_le_one_add {f : Torus 1 → ℝ} {D : ℝ} (hf0 : ∀ x, 0 ≤ f x) (hH : MemH1 (haar 1) f)
    (h1 : ∫ x, f x ^ 2 ∂haar 1 = 1) (hD : ∫ x, weakGrad f x 0 ^ 2 ∂haar 1 ≤ D) :
    ∀ᵐ x ∂haar 1, f x ≤ 1 + (Real.sqrt D + D) := by
  have hs : (fun x => Real.sqrt (f x ^ 2)) = f := funext fun x => Real.sqrt_sq (hf0 x)
  have hMem : MemH1 (haar 1) (fun x => Real.sqrt (f x ^ 2)) := by rw [hs]; exact hH
  have key := ae_abs_sqrt_sub_one_le (ρ := fun x => f x ^ 2) (fun x => sq_nonneg _) h1 hMem
  filter_upwards [key] with x hx
  rw [hs] at hx
  have := (abs_le.mp hx).2
  rw [Real.sqrt_sq (hf0 x)] at this
  have h2 : Real.sqrt (∫ y, weakGrad f y 0 ^ 2 ∂haar 1) ≤ Real.sqrt D := Real.sqrt_le_sqrt hD
  linarith

theorem sMin_bounds {r : ℝ} (_hr0 : 0 ≤ r) (hr1 : r ≤ 1) {A f : Torus 1 → ℝ} (hA : Continuous A)
    {R : ℝ} (hR : ∀ x, |A x| ≤ R) (hf : IsSMin r A f) :
    -R ≤ sFunctional r A f ∧ sFunctional r A f ≤ R ∧ ∫ x, weakGrad f x 0 ^ 2 ∂haar 1 ≤ R ∧
      ∀ᵐ x ∂haar 1, f x ≤ 1 + (Real.sqrt R + R) := by
  obtain ⟨hf0, hH, h1, hmin⟩ := hf
  have hone : sFunctional r A f ≤ ∫ x, A x ∂haar 1 := by
    have := hmin (fun _ => 1) (fun _ => zero_le_one) memH1_one (by simp)
    rw [show sFunctional r A (fun _ => 1) = Sfun r A (fun _ => 1) from rfl, Sfun_one] at this
    exact this
  have hAle : ∫ x, A x ∂haar 1 ≤ R := by
    have := abs_integral_A_le hA hR memH1_one (by simp)
    simp only [one_pow, mul_one] at this
    exact (le_abs_self _).trans this
  have hlow := Sfun_lower hr1 hA hR hf0 hH h1
  have hW : ∫ x, weakGrad f x 0 ^ 2 ∂haar 1 ≤ R := by
    have : sFunctional r A f = Sfun r A f := rfl
    linarith
  have hW0 : 0 ≤ ∫ x, weakGrad f x 0 ^ 2 ∂haar 1 := integral_nonneg fun x => sq_nonneg _
  refine ⟨?_, hone.trans hAle, hW, ae_le_one_add hf0 hH h1 hW⟩
  have : sFunctional r A f = Sfun r A f := rfl
  linarith

/-! ### Existence by the direct method -/

theorem exists_sMin {r : ℝ} (_hr0 : 0 ≤ r) (hr1 : r ≤ 1) {A : Torus 1 → ℝ} (hA : Continuous A) :
    ∃ f : Torus 1 → ℝ, IsSMin r A f := by
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hA.continuousOn
  have hR' : ∀ x, |A x| ≤ R := fun x => by simpa using hR x (Set.mem_univ x)
  set 𝓕 : Set (Torus 1 → ℝ) :=
    {f | (∀ x, 0 ≤ f x) ∧ MemH1 (haar 1) f ∧ ∫ x, f x ^ 2 ∂haar 1 = 1} with h𝓕
  set Sset : Set ℝ := Sfun r A '' 𝓕 with hSset
  have hne : Sset.Nonempty :=
    ⟨_, ⟨fun _ => 1, ⟨fun _ => zero_le_one, memH1_one, by simp⟩, rfl⟩⟩
  have hbdd : BddBelow Sset := by
    refine ⟨-R, ?_⟩
    rintro _ ⟨f, ⟨hf0, hfH, hf1⟩, rfl⟩
    have := Sfun_lower hr1 hA hR' hf0 hfH hf1
    have hW0 : 0 ≤ ∫ x, weakGrad f x 0 ^ 2 ∂haar 1 := integral_nonneg fun x => sq_nonneg _
    linarith
  obtain ⟨s, hsanti, hslim, hsmem⟩ := exists_seq_tendsto_sInf hne hbdd
  choose f hf hfs using hsmem
  have hD : ∀ n, ∫ x, weakGrad (f n) x 0 ^ 2 ∂haar 1 ≤ (s 0 + R) / 2 := by
    intro n
    have := Sfun_lower hr1 hA hR' (hf n).1 (hf n).2.1 (hf n).2.2
    have h2 : s n ≤ s 0 := hsanti (Nat.zero_le n)
    rw [hfs n] at this
    linarith
  obtain ⟨φ, u, L, hφ, hu0, hMu, hmass, -, -, hLim, hlsc, hmom, hent⟩ :=
    h1_compact (fun n x => (hf n).1 x) (fun n => (hf n).2.1) (fun n => (hf n).2.2) hD
  have hlim1 : Tendsto (fun n => Sfun r A (f (φ n))) atTop
      (𝓝 (4 * L + ∫ x, A x * u x ^ 2 ∂haar 1 -
        2 * r * (klDiv (densMeasure fun x => u x ^ 2) (haar 1)).toReal)) := by
    unfold Sfun
    exact ((hLim.const_mul 4).add (hmom A hA)).sub ((hent).const_mul (2 * r))
  have hlim2 : Tendsto (fun n => Sfun r A (f (φ n))) atTop (𝓝 (sInf Sset)) := by
    refine (hslim.comp hφ.tendsto_atTop).congr fun n => ?_
    simp only [Function.comp, hfs]
  have heq := tendsto_nhds_unique hlim1 hlim2
  have hSu : Sfun r A u ≤ sInf Sset := by
    unfold Sfun
    linarith
  refine ⟨u, hu0, hMu, hmass, fun g hg0 hgH hg1 => ?_⟩
  exact hSu.trans (csInf_le hbdd ⟨g, ⟨hg0, hgH, hg1⟩, rfl⟩)

end SharpLSI.FL.Ex.SR
