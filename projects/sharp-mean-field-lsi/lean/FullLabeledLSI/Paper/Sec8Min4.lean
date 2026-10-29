import FullLabeledLSI.Paper.Sec8Min3

/-!
# Section 8.3 (linearization), part 11: the lower bound in (8.11)

Every admissible family has `D/G ≥ min{λ_G, λ₁}`: the mean field part by `D1_ge` (the finite
blocks of `λ_G`), the label part by the Poincaré inequality `poincare_spec`.
-/

open MeasureTheory InformationTheory Set Filter Topology Finset
open scoped ENNReal NNReal

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The admissibility of a family in (8.11). -/
def LinFam (μ : Measure (Torus d)) (q : ℕ) (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ) : Prop :=
  (∀ a, 0 < θ a) ∧ ∑ a, θ a = 1 ∧
    ∀ a, (∃ L : ℝ≥0, LipschitzWith L (h a)) ∧ (∃ B, ∀ x, |h a x| ≤ B) ∧ ∫ x, h a x ∂μ = 0

/-- The quadratic form of (8.9). -/
noncomputable def linG (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) {q : ℕ}
    (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ) : ℝ :=
  secondVar W μ (hb θ h) + ∑ a, θ a * ∫ x, (h a x - hb θ h x) ^ 2 ∂μ

/-- The quadratic form of (8.10). -/
noncomputable def linD (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) {q : ℕ}
    (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ) : ℝ :=
  (dirichlet μ (fun x => hb θ h x + Top W μ (hb θ h) x)).toReal +
    ∑ a, θ a * (dirichlet μ (fun x => h a x - hb θ h x)).toReal

/-- The infimum of the quadratic quotients (8.11). -/
noncomputable def linInf (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) : ℝ≥0∞ :=
  ⨅ (q : ℕ) (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ)
    (_ : LinFam μ q θ h ∧ 0 < linG W μ θ h), ENNReal.ofReal (linD W μ θ h / linG W μ θ h)

theorem lip_sub {u v : Torus d → ℝ} (hu : ∃ L : ℝ≥0, LipschitzWith L u)
    (hv : ∃ L : ℝ≥0, LipschitzWith L v) : ∃ L : ℝ≥0, LipschitzWith L (fun x => u x - v x) := by
  obtain ⟨L, hL⟩ := hu
  obtain ⟨L', hL'⟩ := hv
  exact ⟨L + L', hL.sub hL'⟩

theorem lamG_le_trunc {lam' : ℕ → ℝ} {C : ℕ → ℕ → ℝ} (n : ℕ) (v : ℕ → ℝ)
    (hQ : 0 < ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j) :
    lamG lam' C ≤ ENNReal.ofReal (∑ i ∈ range n, lam' i * v i ^ 2) /
      ENNReal.ofReal (∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j) := by
  have hQe := Qv_vtr_eq (C := C) v n
  have hv : vtr v n ∈ {w : ℕ → ℝ | Summable (fun i => w i ^ 2) ∧
      Summable (fun i => lam' i * w i ^ 2) ∧ w ≠ 0} := by
    refine ⟨summable_sq_vtr n, ?_, ?_⟩
    · exact summable_of_ne_finset_zero (s := range n) fun i hi => by
        rw [vtr_eq_zero hi]; ring
    · intro h0
      rw [h0] at hQe
      simp [Cvec] at hQe
      linarith
  unfold lamG
  refine (iInf₂_le (vtr v n) hv).trans (le_of_eq ?_)
  congr 1
  · congr 1
    rw [tsum_eq_sum (s := range n) fun i hi => by rw [vtr_eq_zero hi]; ring]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [vtr, Finset.mem_range.mp hi]
  · congr 1

theorem lower_bound (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C) :
    min (lamG (lamShift lam) C) (ENNReal.ofReal (lam 1)) ≤ linInf W (μ : Measure (Torus d)) := by
  have hac := minimizer_ac hyp hμ
  obtain ⟨Chl, hlow⟩ := haar_le_smul_minimizer hyp hμ
  have hlam1 : 0 < lam 1 := ((ref_spectrum hd hyp hr hμ).2 e lam he).1 1 le_rfl
  set m : ℝ≥0∞ := min (lamG (lamShift lam) C) (ENNReal.ofReal (lam 1)) with hm
  have hmG : m ≤ lamG (lamShift lam) C := min_le_left _ _
  have hm1 : m ≤ ENNReal.ofReal (lam 1) := min_le_right _ _
  have hmtop : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm1
  set mr : ℝ := m.toReal with hmr_def
  have hmr0 : 0 ≤ mr := ENNReal.toReal_nonneg
  have hmr_m : ENNReal.ofReal mr = m := ENNReal.ofReal_toReal hmtop
  have hmr1 : mr ≤ lam 1 := by
    have : ENNReal.ofReal mr ≤ ENNReal.ofReal (lam 1) := hmr_m ▸ hm1
    exact (ENNReal.ofReal_le_ofReal_iff hlam1.le).1 this
  have hlam : ∀ i, 0 < lamShift lam i := fun i =>
    hlam1.trans_le (he.mono (by simp [lamShift] : 1 ≤ i + 1))
  -- finite blocks
  have hblk : ∀ (n : ℕ) (v : ℕ → ℝ), mr * ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j ≤
      ∑ i ∈ range n, lamShift lam i * v i ^ 2 := by
    intro n v
    set Q := ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j with hQ
    set N := ∑ i ∈ range n, lamShift lam i * v i ^ 2 with hN
    rcases le_or_gt Q 0 with hQ0 | hQ0
    · have : 0 ≤ N := Finset.sum_nonneg fun i _ => mul_nonneg (hlam i).le (sq_nonneg _)
      nlinarith
    · have h1 := hmG.trans (lamG_le_trunc (lam' := lamShift lam) (C := C) n v hQ0)
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hQ0)) (Or.inl ENNReal.ofReal_ne_top),
        ← hmr_m, ← ENNReal.ofReal_mul hmr0] at h1
      exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun i _ =>
        mul_nonneg (hlam i).le (sq_nonneg _))).1 h1
  unfold linInf
  refine le_iInf fun q => le_iInf fun θ => le_iInf fun h => le_iInf fun hfam => ?_
  obtain ⟨⟨hθ, hθ1, hrest⟩, hG⟩ := hfam
  have hLip : ∀ a, ∃ L : ℝ≥0, LipschitzWith L (h a) := fun a => (hrest a).1
  have hbd : ∀ a, ∃ B, ∀ x, |h a x| ≤ B := fun a => (hrest a).2.1
  have hmean : ∀ a, ∫ x, h a x ∂(μ : Measure (Torus d)) = 0 := fun a => (hrest a).2.2
  have hbL := lip_hb θ h hLip
  have hb0 := hb_integral θ h hLip hbd hmean
  -- the mean field part
  have hD1 := D1_ge hd hyp hr hμ he hC hblk hbL hb0
  -- the label part
  have hD2 : ∀ a, lam 1 * ∫ x, (h a x - hb θ h x) ^ 2 ∂(μ : Measure (Torus d)) ≤
      (dirichlet (μ : Measure (Torus d)) (fun x => h a x - hb θ h x)).toReal := fun a => by
    have hηL := lip_sub (hLip a) hbL
    obtain ⟨hηc, hηw, ⟨Kη, hKη⟩, hηm⟩ := lip_data hηL
    have hηB : BM (fun x => h a x - hb θ h x) := BM.of_lip hηL
    have hη0 : ∫ x, (h a x - hb θ h x) ∂(μ : Measure (Torus d)) = 0 := by
      rw [integral_sub (BM.of_lip (hLip a)).integrable (BM.of_lip hbL).integrable, hmean a, hb0,
        sub_zero]
    have hH1 := memH1_of_wg hac hηw hηB.1 hηB.2.choose_spec hKη
    have := poincare_spec hac hlow he hH1 hη0
    rw [dirPair_eq hac hηw] at this
    rwa [dirichlet_toReal_of_wg hac hηw hKη hηm]
  have hint0 : ∀ a, 0 ≤ ∫ x, (h a x - hb θ h x) ^ 2 ∂(μ : Measure (Torus d)) :=
    fun a => integral_nonneg fun x => sq_nonneg _
  have hDge : mr * linG W (μ : Measure (Torus d)) θ h ≤ linD W (μ : Measure (Torus d)) θ h := by
    unfold linG linD
    rw [mul_add, Finset.mul_sum]
    refine add_le_add hD1 (Finset.sum_le_sum fun a _ => ?_)
    calc mr * (θ a * ∫ x, (h a x - hb θ h x) ^ 2 ∂(μ : Measure (Torus d)))
        = θ a * (mr * ∫ x, (h a x - hb θ h x) ^ 2 ∂(μ : Measure (Torus d))) := by ring
      _ ≤ θ a * (lam 1 * ∫ x, (h a x - hb θ h x) ^ 2 ∂(μ : Measure (Torus d))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmr1 (hint0 a)) (hθ a).le
      _ ≤ _ := mul_le_mul_of_nonneg_left (hD2 a) (hθ a).le
  rw [← hmr_m]
  exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ hG).2 hDge)

end Sec8
end SharpLSI.FL
