import DGPS.Foundations.Torus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Spike grid of the rough counterexample and its exact integrals (RUF001)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 1.1.  On `T = ℝ/ℤ = Torus 1` with Haar
probability measure `haar 1`, for an integer `n ≥ 2`:

* `A n = e^n`, `M n = ⌈e^(n³)⌉`, `ell n = (n M_n e^(2n))⁻¹`;
* `spikeInterval n j = [j/M_n, j/M_n + ℓ_n)` (periodically), `E n = ⋃_{j<M_n} spikeInterval n j`;
* `h n = A_n 1_{E_n}`.

`spike_grid_definition_and_exact_integrals` states `M_n ≥ 1`, `0 < ℓ_n < 1/M_n`, that each interval
lies in its cell `[j/M_n,(j+1)/M_n)` and the cells are pairwise disjoint, `m(E_n) = e^(-2n)/n`,
`∫ h_n^p = e^(-(2-p)n)/n` for every real `p ≥ 1`, `∫ h_n = e^(-n)/n`, `∫ h_n² = 1/n`.
-/

open MeasureTheory Set

namespace DGPS.Examples.RoughBoundary.Spikes

/-- Amplitude `A_n = e^n`. -/
noncomputable def A (n : ℕ) : ℝ := Real.exp n

/-- Number of cells `M_n = ⌈e^(n³)⌉`. -/
noncomputable def M (n : ℕ) : ℕ := ⌈Real.exp ((n : ℝ) ^ 3)⌉₊

/-- Spike length `ℓ_n = (n M_n e^(2n))⁻¹`. -/
noncomputable def ell (n : ℕ) : ℝ := ((n : ℝ) * (M n : ℝ) * Real.exp (2 * n))⁻¹

/-- The point of `T = Torus 1` represented by a real number. -/
def pt (x : ℝ) : Torus 1 := DGPS.torusLift (fun _ => x)

/-- The `j`-th spike interval `[j/M_n, j/M_n + ℓ_n)` viewed on `T`. -/
noncomputable def spikeInterval (n j : ℕ) : Set (Torus 1) :=
  pt '' Ico ((j : ℝ) / M n) ((j : ℝ) / M n + ell n)

/-- The `j`-th cell `[j/M_n, (j+1)/M_n)` viewed on `T`. -/
noncomputable def cell (n j : ℕ) : Set (Torus 1) :=
  pt '' Ico ((j : ℝ) / M n) (((j : ℝ) + 1) / M n)

/-- The spike set `E_n = ⋃_{0 ≤ j < M_n} [j/M_n, j/M_n + ℓ_n)`. -/
noncomputable def E (n : ℕ) : Set (Torus 1) := ⋃ j ∈ Finset.range (M n), spikeInterval n j

/-- The spike function `h_n = e^n 1_{E_n}`. -/
noncomputable def h (n : ℕ) : Torus 1 → ℝ := (E n).indicator (fun _ => A n)

/-! ### Arithmetic of the grid -/

section Arith
variable {n : ℕ}

lemma M_pos : 0 < M n := Nat.ceil_pos.2 (Real.exp_pos _)

lemma M_real_pos : (0 : ℝ) < M n := by exact_mod_cast (M_pos (n := n))

lemma ell_pos (hn : 2 ≤ n) : 0 < ell n := by
  have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have := M_real_pos (n := n)
  unfold ell; positivity

lemma two_ell_M_le (hn : 2 ≤ n) : 2 * ell n * M n ≤ 1 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hM := M_real_pos (n := n)
  have he : (1 : ℝ) ≤ Real.exp (2 * n) := Real.one_le_exp (by positivity)
  have : 2 * ell n * M n = 2 / ((n : ℝ) * Real.exp (2 * n)) := by
    unfold ell; field_simp
  rw [this, div_le_one (by positivity)]
  nlinarith

lemma ell_lt (hn : 2 ≤ n) : ell n < 1 / (M n : ℝ) := by
  have hM := M_real_pos (n := n)
  have := ell_pos hn
  have := two_ell_M_le hn
  rw [lt_div_iff₀ hM]; nlinarith

lemma ell_mul_M (hn : 2 ≤ n) : (M n : ℝ) * ell n = Real.exp (-2 * n) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hM := M_real_pos (n := n)
  unfold ell
  rw [show -2 * (n : ℝ) = -(2 * n) by ring, Real.exp_neg]
  field_simp

end Arith

/-! ### Measure of images of real sets -/

lemma pt_eq (x : ℝ) : pt x = (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle).symm (x : UnitAddCircle) :=
  rfl

lemma pt_injOn : InjOn pt (Ico (0 : ℝ) 1) := by
  intro a ha b hb hab
  have := congrFun hab 0
  have h2 : ((a : ℝ) : UnitAddCircle) = (b : ℝ) := this
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
    (by simpa using ha) (by simpa using hb)).1 h2

lemma pt_image_eq (S : Set ℝ) :
    pt '' S = (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle) ⁻¹'
      (((↑) : ℝ → UnitAddCircle) '' S) := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    funext i
    have : i = 0 := Subsingleton.elim _ _
    subst this
    exact hx

/-- Images of measurable subsets of a window `(t, t+1)` are measurable and keep Lebesgue measure. -/
lemma haar_pt_image {t : ℝ} {S : Set ℝ} (hS : S ⊆ Ioo t (t + 1)) (hm : MeasurableSet S) :
    MeasurableSet (pt '' S) ∧ haar 1 (pt '' S) = volume S := by
  set g : UnitAddCircle → ℝ := fun y => (AddCircle.measurableEquivIoc (1 : ℝ) t y : ℝ) with hg
  have hgm : Measurable g :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (1 : ℝ) t).measurable
  have hgmk : ∀ x ∈ Ioc t (t + 1), g (x : UnitAddCircle) = x := fun x hx =>
    AddCircle.equivIoc_coe_of_mem (p := (1 : ℝ)) (a := t) hx
  have himg : (((↑) : ℝ → UnitAddCircle) '' S) = g ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      show g s ∈ S
      rw [hgmk s ⟨(hS hs).1, (hS hs).2.le⟩]; exact hs
    · intro hy
      refine ⟨g y, hy, ?_⟩
      exact AddCircle.coe_equivIoc (p := (1 : ℝ)) (a := t)
  have hmeas : MeasurableSet (((↑) : ℝ → UnitAddCircle) '' S) := by
    rw [himg]; exact hgm hm
  have hvol : volume (((↑) : ℝ → UnitAddCircle) '' S) = volume S := by
    have h1 := (UnitAddCircle.measurePreserving_mk t).measure_preimage hmeas.nullMeasurableSet
    rw [← h1, Measure.restrict_apply (AddCircle.measurable_mk' (hmeas))]
    congr 1
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      have : g (x : UnitAddCircle) ∈ S := by
        have h3 : (x : UnitAddCircle) ∈ g ⁻¹' S := himg ▸ hx1
        exact h3
      rwa [hgmk x hx2] at this
    · intro hx
      have hx2 : x ∈ Ioc t (t + 1) := ⟨(hS hx).1, (hS hx).2.le⟩
      exact ⟨⟨x, hx, rfl⟩, hx2⟩
  have hmeas' : MeasurableSet (pt '' S) := by
    rw [pt_image_eq]; exact (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle).measurable hmeas
  refine ⟨hmeas', ?_⟩
  rw [pt_image_eq]
  exact Eq.trans ((volume_preserving_funUnique (Fin 1) UnitAddCircle).measure_preimage_equiv _) hvol

/-! ### The spike set -/

/-- The real-line model of `E_n`. -/
def Ereal (n : ℕ) : Set ℝ :=
  ⋃ j ∈ Finset.range (M n), Ico ((j : ℝ) / M n) ((j : ℝ) / M n + ell n)

lemma E_eq_image (n : ℕ) : E n = pt '' Ereal n := by
  unfold E Ereal spikeInterval
  rw [Set.image_iUnion₂]

lemma Ereal_measurable (n : ℕ) : MeasurableSet (Ereal n) :=
  Finset.measurableSet_biUnion _ fun _ _ => measurableSet_Ico

lemma interval_disjoint {n : ℕ} (hn : 2 ≤ n) {j k : ℕ} (hjk : j < k) :
    Disjoint (Ico ((j : ℝ) / M n) ((j : ℝ) / M n + ell n))
      (Ico ((k : ℝ) / M n) ((k : ℝ) / M n + ell n)) := by
  have hM := M_real_pos (n := n)
  have hl := ell_lt hn
  rw [Set.disjoint_left]
  rintro x ⟨_, hx2⟩ ⟨hy1, _⟩
  have hjk' : ((j : ℝ) + 1) ≤ k := by exact_mod_cast hjk
  have : ((j : ℝ) + 1) / M n ≤ k / M n := by gcongr
  have h2 : (j : ℝ) / M n + ell n < ((j : ℝ) + 1) / M n := by
    rw [add_div]; linarith
  linarith

lemma Ereal_subset {n : ℕ} (hn : 2 ≤ n) : Ereal n ⊆ Ioo (-ell n) (-ell n + 1) := by
  intro x hx
  simp only [Ereal, mem_iUnion, Finset.mem_range] at hx
  obtain ⟨j, hj, hx1, hx2⟩ := hx
  have hM := M_real_pos (n := n)
  have hl := ell_pos hn
  have h2 := two_ell_M_le hn
  have hj' : (j : ℝ) + 1 ≤ M n := by exact_mod_cast hj
  refine ⟨?_, ?_⟩
  · have : 0 ≤ (j : ℝ) / M n := by positivity
    linarith
  · have h3 : ((j : ℝ) + 1) / M n ≤ 1 := by
      rw [div_le_one hM]; exact hj'
    have h4 : (j : ℝ) / M n + ell n ≤ ((j : ℝ) + 1) / M n - ell n := by
      have : ((j : ℝ) + 1) / M n = (j : ℝ) / M n + 1 / M n := by rw [add_div]
      have h5 : 2 * ell n ≤ 1 / M n := by
        rw [le_div_iff₀ hM]; exact h2
      linarith
    linarith

lemma E_measurable {n : ℕ} (hn : 2 ≤ n) : MeasurableSet (E n) := by
  rw [E_eq_image]; exact (haar_pt_image (Ereal_subset hn) (Ereal_measurable n)).1

lemma volume_Ereal {n : ℕ} (hn : 2 ≤ n) :
    volume (Ereal n) = ENNReal.ofReal (Real.exp (-2 * n) / n) := by
  have hl := ell_pos hn
  have : volume (Ereal n) = ∑ j ∈ Finset.range (M n), ENNReal.ofReal (ell n) := by
    unfold Ereal
    rw [measure_biUnion_finset]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Real.volume_Ico]; congr 1; ring
    · intro j _ k _ hjk
      rcases lt_or_gt_of_ne hjk with h | h
      · exact interval_disjoint hn h
      · exact (interval_disjoint hn h).symm
    · exact fun _ _ => measurableSet_Ico
  rw [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ell_mul_M hn]

lemma haar_E {n : ℕ} (hn : 2 ≤ n) : haar 1 (E n) = ENNReal.ofReal (Real.exp (-2 * n) / n) := by
  rw [E_eq_image, (haar_pt_image (Ereal_subset hn) (Ereal_measurable n)).2, volume_Ereal hn]

lemma haar_real_E {n : ℕ} (hn : 2 ≤ n) : (haar 1).real (E n) = Real.exp (-2 * n) / n := by
  rw [measureReal_def, haar_E hn, ENNReal.toReal_ofReal (by positivity)]

/-! ### Integrals of `h_n^p` -/

lemma integral_h_rpow {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 < p) :
    ∫ x, h n x ^ p ∂haar 1 = Real.exp (-(2 - p) * n) / n := by
  have hpt : (fun x => h n x ^ p) = (E n).indicator (fun _ => A n ^ p) := by
    funext x
    by_cases hx : x ∈ E n
    · simp [h, hx]
    · simp [h, hx, Real.zero_rpow hp.ne']
  rw [hpt, integral_indicator_const _ (E_measurable hn), haar_real_E hn, smul_eq_mul, A,
    ← Real.exp_mul, mul_comm, mul_div_assoc', ← Real.exp_add]
  congr 2
  ring

/-- **RUF001.** Spike grid definition and exact integrals. -/
theorem spike_grid_definition_and_exact_integrals (n : ℕ) (hn : 2 ≤ n) :
    (0 < M n ∧ 0 < ell n ∧ ell n < 1 / (M n : ℝ)) ∧
    (∀ j < M n, spikeInterval n j ⊆ cell n j) ∧
    (∀ j < M n, ∀ k < M n, j ≠ k → Disjoint (cell n j) (cell n k)) ∧
    (MeasurableSet (E n) ∧ Measurable (h n) ∧ Integrable (h n) (haar 1)) ∧
    haar 1 (E n) = ENNReal.ofReal (Real.exp (-2 * n) / n) ∧
    (haar 1).real (E n) = Real.exp (-2 * n) / n ∧
    (∀ p : ℝ, 1 ≤ p → ∫ x, h n x ^ p ∂haar 1 = Real.exp (-(2 - p) * n) / n) ∧
    ∫ x, h n x ∂haar 1 = Real.exp (-n) / n ∧
    ∫ x, h n x ^ 2 ∂haar 1 = 1 / n := by
  have hM := M_real_pos (n := n)
  have hl := ell_pos hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine ⟨⟨M_pos, hl, ell_lt hn⟩, ?_, ?_, ⟨E_measurable hn, ?_, ?_⟩, haar_E hn, haar_real_E hn,
    fun p hp => integral_h_rpow hn (by linarith), ?_, ?_⟩
  · intro j _
    refine Set.image_mono (Set.Ico_subset_Ico le_rfl ?_)
    rw [add_div]
    have := ell_lt hn
    linarith
  · intro j hj k hk hjk
    rw [Set.disjoint_left]
    rintro x ⟨a, ⟨ha1, ha2⟩, rfl⟩ ⟨b, ⟨hb1, hb2⟩, hab⟩
    have hj' : (j : ℝ) + 1 ≤ M n := by exact_mod_cast hj
    have hk' : (k : ℝ) + 1 ≤ M n := by exact_mod_cast hk
    have ha0 : 0 ≤ a := le_trans (by positivity) ha1
    have hb0 : 0 ≤ b := le_trans (by positivity) hb1
    have ha3 : a < 1 := ha2.trans_le ((div_le_one hM).2 hj')
    have hb3 : b < 1 := hb2.trans_le ((div_le_one hM).2 hk')
    have hba : b = a := pt_injOn ⟨hb0, hb3⟩ ⟨ha0, ha3⟩ hab
    subst hba
    rcases lt_or_gt_of_ne hjk with h | h
    · have : ((j : ℝ) + 1) ≤ k := by exact_mod_cast h
      have : ((j : ℝ) + 1) / M n ≤ k / M n := by gcongr
      linarith
    · have : ((k : ℝ) + 1) ≤ j := by exact_mod_cast h
      have : ((k : ℝ) + 1) / M n ≤ j / M n := by gcongr
      linarith
  · exact (measurable_const.indicator (E_measurable hn))
  · exact (integrable_const (A n)).indicator (E_measurable hn)
  · have := integral_h_rpow hn (p := 1) one_pos
    simp only [Real.rpow_one] at this
    rw [this]; congr 2; ring
  · have := integral_h_rpow hn (p := 2) two_pos
    have e : ∀ x, h n x ^ (2 : ℝ) = h n x ^ 2 := fun x => by norm_cast
    simp only [e] at this
    rw [this]
    have : Real.exp (-(2 - 2) * n) = 1 := by simp
    rw [this]


/-! # RUF002: common spike sum and absolutely continuous primitive -/

section RUF002

open Filter Topology

lemma pt_add_one (x : ℝ) : pt (x + 1) = pt x := by
  funext i
  exact AddCircle.coe_add_period (1 : ℝ) x

lemma measurePreserving_pt :
    MeasurePreserving pt (volume.restrict (Ioc (0 : ℝ) 1)) (haar 1) := by
  have h1 := UnitAddCircle.measurePreserving_mk 0
  simp only [zero_add] at h1
  exact ((volume_preserving_funUnique (Fin 1) UnitAddCircle).symm).comp h1

lemma measurable_pt : Measurable pt := measurePreserving_pt.measurable

lemma integral_haar_eq {F : Torus 1 → ℝ} (hF : AEStronglyMeasurable F (haar 1)) :
    ∫ x, F x ∂haar 1 = ∫ t in Ioc (0 : ℝ) 1, F (pt t) := by
  rw [← measurePreserving_pt.map_eq] at hF ⊢
  rw [integral_map measurable_pt.aemeasurable hF]


/-! ### The common spike sum -/

/-- The common spike sum `h = ∑_{n ≥ 2} h_n` (real-valued; the junk value `0` is taken only on
the null set where the series diverges). -/
noncomputable def hSum (x : Torus 1) : ℝ := ∑' n : ℕ, h (n + 2) x

/-- The mean `c = ∑_{n ≥ 2} e^(-n)/n`. -/
noncomputable def hMean : ℝ := ∑' n : ℕ, Real.exp (-((n + 2 : ℕ) : ℝ)) / ((n + 2 : ℕ) : ℝ)

lemma h_nonneg (n : ℕ) (x : Torus 1) : 0 ≤ h n x :=
  Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x

lemma h_meas (n : ℕ) : Measurable (h (n + 2)) :=
  measurable_const.indicator (E_measurable (by omega))

lemma hSum_nonneg (x : Torus 1) : 0 ≤ hSum x := tsum_nonneg fun _ => h_nonneg _ x

/-- the terms of the mean series -/
noncomputable def meanTerm (n : ℕ) : ℝ := Real.exp (-((n + 2 : ℕ) : ℝ)) / ((n + 2 : ℕ) : ℝ)

lemma meanTerm_nonneg (n : ℕ) : 0 ≤ meanTerm n := by unfold meanTerm; positivity

lemma meanTerm_le (n : ℕ) : meanTerm n ≤ (1 / 2 : ℝ) ^ (n + 2) := by
  have h1 : Real.exp (-1) ≤ 1 / 2 := by
    have := Real.exp_one_gt_d9
    rw [Real.exp_neg]
    rw [inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have h2 : Real.exp (-((n + 2 : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) ^ (n + 2) := by
    have : Real.exp (-((n + 2 : ℕ) : ℝ)) = Real.exp (-1) ^ (n + 2) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [this]
    exact pow_le_pow_left₀ (Real.exp_pos _).le h1 _
  have h3 : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ n + 2 := by omega
    exact_mod_cast this
  unfold meanTerm
  calc Real.exp (-((n + 2 : ℕ) : ℝ)) / ((n + 2 : ℕ) : ℝ)
      ≤ Real.exp (-((n + 2 : ℕ) : ℝ)) := div_le_self (Real.exp_pos _).le h3
    _ ≤ _ := h2

lemma summable_meanTerm : Summable meanTerm :=
  Summable.of_nonneg_of_le meanTerm_nonneg meanTerm_le
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 2))

lemma hMean_eq : hMean = ∑' n, meanTerm n := rfl

lemma hMean_pos : 0 < hMean :=
  summable_meanTerm.tsum_pos meanTerm_nonneg 0 (by unfold meanTerm; positivity)

lemma hMean_lt_one : hMean < 1 := by
  have h1 : hMean ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 2) :=
    Summable.tsum_le_tsum meanTerm_le summable_meanTerm
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
        (add_left_injective 2))
  have h2 : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 2) = 1 / 2 := by
    simp_rw [pow_add]
    rw [tsum_mul_right, tsum_geometric_two]
    norm_num
  linarith

lemma lintegral_ofReal_h (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (h (n + 2) x) ∂haar 1 = ENNReal.ofReal (meanTerm n) := by
  have hn : 2 ≤ n + 2 := by omega
  have hI : Integrable (h (n + 2)) (haar 1) :=
    (spike_grid_definition_and_exact_integrals (n + 2) hn).2.2.2.1.2.2
  have hv := (spike_grid_definition_and_exact_integrals (n + 2) hn).2.2.2.2.2.2.2.1
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall (h_nonneg _)), hv]
  rfl

/-- The `[0,∞]`-valued sum. -/
noncomputable def hSumE (x : Torus 1) : ENNReal := ∑' n : ℕ, ENNReal.ofReal (h (n + 2) x)

lemma hSumE_meas : Measurable hSumE :=
  Measurable.tsum fun n => (h_meas n).ennreal_ofReal

lemma lintegral_hSumE : ∫⁻ x, hSumE x ∂haar 1 = ENNReal.ofReal hMean := by
  unfold hSumE
  rw [lintegral_tsum fun n => (h_meas n).ennreal_ofReal.aemeasurable]
  simp_rw [lintegral_ofReal_h]
  rw [hMean_eq, ENNReal.ofReal_tsum_of_nonneg meanTerm_nonneg summable_meanTerm]

lemma hSum_eq_toReal (x : Torus 1) : hSum x = (hSumE x).toReal := by
  unfold hSum hSumE
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  refine tsum_congr fun n => ?_
  rw [ENNReal.toReal_ofReal (h_nonneg _ _)]

lemma hSum_meas : Measurable hSum := by
  have : hSum = fun x => (hSumE x).toReal := funext hSum_eq_toReal
  rw [this]; exact hSumE_meas.ennreal_toReal

lemma ae_summable_h : ∀ᵐ x ∂haar 1, Summable fun n : ℕ => h (n + 2) x := by
  have : ∀ᵐ x ∂haar 1, hSumE x < ⊤ :=
    ae_lt_top hSumE_meas (by rw [lintegral_hSumE]; exact ENNReal.ofReal_ne_top)
  filter_upwards [this] with x hx
  have := ENNReal.summable_toReal hx.ne
  simpa [ENNReal.toReal_ofReal (h_nonneg _ _)] using this

lemma integrable_hSum : Integrable hSum (haar 1) := by
  have : hSum = fun x => (hSumE x).toReal := funext hSum_eq_toReal
  rw [this]
  exact integrable_toReal_of_lintegral_ne_top hSumE_meas.aemeasurable
    (by rw [lintegral_hSumE]; exact ENNReal.ofReal_ne_top)

lemma integral_hSum : ∫ x, hSum x ∂haar 1 = hMean := by
  have : hSum = fun x => (hSumE x).toReal := funext hSum_eq_toReal
  rw [this, integral_toReal hSumE_meas.aemeasurable
    (ae_lt_top hSumE_meas (by rw [lintegral_hSumE]; exact ENNReal.ofReal_ne_top)),
    lintegral_hSumE, ENNReal.toReal_ofReal hMean_pos.le]


/-! ### Simultaneous `L^p` membership -/

/-- `‖h_n‖_p = n^(-1/p) e^(-(2-p)n/p)` (with `n` replaced by `n+2`). -/
noncomputable def normTerm (p : ℝ) (n : ℕ) : ℝ :=
  ((n + 2 : ℕ) : ℝ) ^ (-1 / p) * Real.exp (-(2 - p) * ((n + 2 : ℕ) : ℝ) / p)

lemma normTerm_nonneg (p : ℝ) (n : ℕ) : 0 ≤ normTerm p n := by
  unfold normTerm; positivity

lemma eLpNorm_h {p : ℝ} (hp : 1 ≤ p) (n : ℕ) :
    eLpNorm (h (n + 2)) (ENNReal.ofReal p) (haar 1) = ENNReal.ofReal (normTerm p n) := by
  have hn : 2 ≤ n + 2 := by omega
  have hp0 : 0 < p := by linarith
  have hq : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  unfold h
  rw [eLpNorm_indicator_const (E_measurable hn).nullMeasurableSet
    (by simpa using hp0) ENNReal.ofReal_ne_top, hq, haar_E hn, A,
    Real.enorm_eq_ofReal (Real.exp_pos _).le,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← ENNReal.ofReal_mul
      (Real.exp_pos _).le]
  congr 1
  unfold normTerm
  set m : ℝ := ((n + 2 : ℕ) : ℝ) with hm
  have hm0 : 0 < m := by rw [hm]; positivity
  rw [Real.div_rpow (Real.exp_pos _).le hm0.le, ← Real.exp_mul, show -1 / p = -(1 / p) by ring,
    Real.rpow_neg hm0.le, div_eq_mul_inv, mul_comm (Real.exp (-2 * m * (1 / p))), ← mul_assoc,
    mul_comm (Real.exp m), mul_assoc, ← Real.exp_add]
  congr 3
  field_simp
  ring


lemma normTerm_le {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) (n : ℕ) :
    normTerm p n ≤ Real.exp (-(2 - p) / p) ^ n := by
  have hp0 : 0 < p := by linarith
  unfold normTerm
  have hm : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 2)
  have h1 : ((n + 2 : ℕ) : ℝ) ^ (-1 / p) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hm (div_nonpos_of_nonpos_of_nonneg (by norm_num) hp0.le)
  have h2 : Real.exp (-(2 - p) * ((n + 2 : ℕ) : ℝ) / p) ≤ Real.exp (-(2 - p) / p) ^ n := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have : -(2 - p) * ((n + 2 : ℕ) : ℝ) / p = n * (-(2 - p) / p) + (-(2 - p) * 2 / p) := by
      push_cast; field_simp; ring
    rw [this]
    have : -(2 - p) * 2 / p ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith) hp0.le
    linarith
  calc ((n + 2 : ℕ) : ℝ) ^ (-1 / p) * Real.exp (-(2 - p) * ((n + 2 : ℕ) : ℝ) / p)
      ≤ 1 * Real.exp (-(2 - p) / p) ^ n :=
        mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
    _ = _ := one_mul _

lemma summable_normTerm {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) : Summable (normTerm p) := by
  have hp0 : 0 < p := by linarith
  refine Summable.of_nonneg_of_le (normTerm_nonneg p) (normTerm_le hp hp2)
    (summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.2 ?_))
  exact div_neg_of_neg_of_pos (by linarith) hp0

lemma eLpNorm_tail_le {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) (N : ℕ) :
    eLpNorm (fun x => ∑' n : ℕ, h (n + N + 2) x) (ENNReal.ofReal p) (haar 1) ≤
      ENNReal.ofReal (∑' n : ℕ, normTerm p (n + N)) := by
  have hq1 : 1 ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hsum : Summable fun n : ℕ => normTerm p (n + N) :=
    (summable_nat_add_iff N).2 (summable_normTerm hp hp2)
  let f : ℕ → Torus 1 → ℝ := fun k x => ∑ n ∈ Finset.range k, h (n + N + 2) x
  have hfm : ∀ k, AEStronglyMeasurable (f k) (haar 1) := fun k =>
    (Finset.measurable_sum _ (fun n _ => h_meas (n + N))).aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun x => ∑' n : ℕ, h (n + N + 2) x) (haar 1) := by
    refine (Measurable.tsum (fun n => h_meas (n + N))).aestronglyMeasurable
  refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := f) (Filter.Eventually.of_forall fun k => ?_)
    hfm hgm ?_
  · have : f k = ∑ n ∈ Finset.range k, h (n + N + 2) := by
      funext x; simp [f, Finset.sum_apply]
    rw [this]
    refine (eLpNorm_sum_le hq1).trans ?_
    simp_rw [eLpNorm_h hp]
    rw [← ENNReal.ofReal_sum_of_nonneg fun n _ => normTerm_nonneg p (n + N)]
    exact ENNReal.ofReal_le_ofReal (hsum.sum_le_tsum _ fun n _ => normTerm_nonneg p (n + N))
  · filter_upwards [ae_summable_h] with x hx
    exact (((summable_nat_add_iff N).2 hx).hasSum).tendsto_sum_nat


lemma eLpNorm_hSum_le {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) :
    eLpNorm hSum (ENNReal.ofReal p) (haar 1) ≤ ENNReal.ofReal (∑' n : ℕ, normTerm p n) :=
  eLpNorm_tail_le hp hp2 0

lemma memLp_hSum {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) :
    MemLp hSum (ENNReal.ofReal p) (haar 1) :=
  (eLpNorm_hSum_le hp hp2).trans_lt ENNReal.ofReal_lt_top

lemma tendsto_eLpNorm_partial {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) :
    Tendsto (fun N : ℕ => eLpNorm (fun x => hSum x - ∑ n ∈ Finset.range N, h (n + 2) x)
      (ENNReal.ofReal p) (haar 1)) atTop (𝓝 0) := by
  have hb : Tendsto (fun N : ℕ => ENNReal.ofReal (∑' n : ℕ, normTerm p (n + N))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_sum_nat_add (normTerm p))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => bot_le) (fun N => ?_)
  refine le_trans (le_of_eq ?_) (eLpNorm_tail_le hp hp2 N)
  refine eLpNorm_congr_ae ?_
  filter_upwards [ae_summable_h] with x hx
  have := hx.sum_add_tsum_nat_add N
  show hSum x - _ = _
  unfold hSum
  linarith

lemma memLp_hSum_sub_mean {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) :
    MemLp (fun x => hSum x - hMean) (ENNReal.ofReal p) (haar 1) :=
  (memLp_hSum hp hp2).sub (memLp_const _)

/-! ### The primitive on the line -/

/-- The derivative profile `h - c` along the lift `ℝ → T`. -/
noncomputable def fLine (t : ℝ) : ℝ := hSum (pt t) - hMean

/-- The primitive `g(x) = ∫₀ˣ (h - c)` on the real line. -/
noncomputable def gLine (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, fLine t

lemma fLine_periodic : Function.Periodic fLine 1 := fun x => by simp [fLine, pt_add_one]

lemma integrableOn_hSum_pt : IntegrableOn (fun t => hSum (pt t)) (Ioc (0 : ℝ) 1) := by
  have h1 := integrable_hSum
  rw [← measurePreserving_pt.map_eq] at h1
  have h2 : AEStronglyMeasurable hSum (Measure.map pt (volume.restrict (Ioc (0 : ℝ) 1))) := by
    rw [measurePreserving_pt.map_eq]; exact hSum_meas.aestronglyMeasurable
  exact (integrable_map_measure h2 measurable_pt.aemeasurable).1 h1

lemma fLine_ii01 : IntervalIntegrable fLine volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact integrableOn_hSum_pt.sub (integrableOn_const (by simp))

lemma fLine_ii (a b : ℝ) : IntervalIntegrable fLine volume a b :=
  fLine_periodic.intervalIntegrable₀ one_ne_zero fLine_ii01 a b

lemma hSumPt_ii (a b : ℝ) : IntervalIntegrable (fun t => hSum (pt t)) volume a b := by
  have := (fLine_ii a b).add (intervalIntegrable_const (c := hMean))
  simpa [fLine] using this

lemma integral_hSumPt_01 : ∫ t in (0 : ℝ)..1, hSum (pt t) = hMean := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_haar_eq hSum_meas.aestronglyMeasurable,
    integral_hSum]

lemma integral_fLine_01 : ∫ t in (0 : ℝ)..1, fLine t = 0 := by
  have : ∫ t in (0 : ℝ)..1, fLine t = (∫ t in (0 : ℝ)..1, hSum (pt t)) - ∫ t in (0 : ℝ)..1, hMean :=
    intervalIntegral.integral_sub (hSumPt_ii 0 1) intervalIntegrable_const
  rw [this, integral_hSumPt_01]; simp

lemma gLine_zero : gLine 0 = 0 := by simp [gLine]

lemma gLine_one : gLine 1 = 0 := integral_fLine_01

lemma gLine_periodic : Function.Periodic gLine 1 := by
  intro x
  unfold gLine
  have h1 := intervalIntegral.integral_add_adjacent_intervals (fLine_ii 0 x) (fLine_ii x (x + 1))
  have h2 := fLine_periodic.intervalIntegral_add_eq x 0
  rw [zero_add, integral_fLine_01] at h2
  linarith

lemma abs_gLine_le_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : |gLine x| ≤ hMean := by
  have hc := hMean_pos
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..x, hSum (pt t) :=
    intervalIntegral.integral_nonneg hx.1 fun t _ => hSum_nonneg _
  have h1 : 0 ≤ ∫ t in x..1, hSum (pt t) :=
    intervalIntegral.integral_nonneg hx.2 fun t _ => hSum_nonneg _
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hSumPt_ii 0 x) (hSumPt_ii x 1)
  rw [integral_hSumPt_01] at h2
  have h3 : gLine x = (∫ t in (0 : ℝ)..x, hSum (pt t)) - hMean * x := by
    unfold gLine
    have : ∫ t in (0 : ℝ)..x, fLine t = (∫ t in (0 : ℝ)..x, hSum (pt t)) -
        ∫ t in (0 : ℝ)..x, hMean := intervalIntegral.integral_sub (hSumPt_ii 0 x) intervalIntegrable_const
    rw [this]; simp; ring
  rw [abs_le]
  constructor <;> nlinarith [hx.1, hx.2]

lemma abs_gLine_le (x : ℝ) : |gLine x| ≤ hMean := by
  obtain ⟨y, hy, hxy⟩ := gLine_periodic.exists_mem_Ico₀ one_pos x
  rw [hxy]
  exact abs_gLine_le_Icc ⟨hy.1, hy.2.le⟩


/-! ### Derivative and absolute continuity of the primitive -/

lemma locallyIntegrable_fLine : LocallyIntegrable fLine volume := by
  intro x
  exact ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith),
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1 (fLine_ii (x - 1) (x + 1))⟩

lemma ae_hasDerivAt_gLine : ∀ᵐ t : ℝ, HasDerivAt gLine (fLine t) t := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral locallyIntegrable_fLine] with t ht
  exact ht 0

lemma ac_gLine : AbsolutelyContinuousOnInterval gLine 0 1 :=
  (fLine_ii 0 1).absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)

lemma continuous_gLine : Continuous gLine :=
  intervalIntegral.continuous_primitive (fun a b => fLine_ii a b) 0

/-! ### Transfer to the torus -/

/-- The periodic primitive on the torus, `g = gLine ∘ secT`. -/
noncomputable def gT (y : Torus 1) : ℝ := gLine (SharpLSI.secT y 0)

lemma secT_pt_exists (x : ℝ) : ∃ n : ℤ, x = SharpLSI.secT (pt x) 0 + n := by
  have h : ((SharpLSI.secT (pt x) 0 : ℝ) : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ)) :=
    congrFun (SharpLSI.liftT_secT (pt x)) 0
  have h0 : ((x - SharpLSI.secT (pt x) 0 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, ← h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h0
  exact ⟨n, by simp at hn; linarith⟩

lemma periodic_secT {F : ℝ → ℝ} (hF : Function.Periodic F 1) (x : ℝ) :
    F (SharpLSI.secT (pt x) 0) = F x := by
  obtain ⟨n, hn⟩ := secT_pt_exists x
  have := (hF.int_mul n) (SharpLSI.secT (pt x) 0)
  rw [mul_one] at this
  rw [← this, ← hn]

lemma gT_pt (x : ℝ) : gT (pt x) = gLine x := periodic_secT gLine_periodic x

lemma measurable_comp_secT {F : ℝ → ℝ} (hF : Continuous F) :
    Measurable fun y : Torus 1 => F (SharpLSI.secT y 0) :=
  hF.measurable.comp ((measurable_pi_apply 0).comp SharpLSI.measurable_secT)

lemma abs_gT_le (y : Torus 1) : |gT y| ≤ hMean := abs_gLine_le _

/-! ### Weak integration by parts -/

section IBP

variable {φ : Torus 1 → ℝ}

lemma contDiff_psi (hφ : DGPS.IsSmoothPeriodic φ) : ContDiff ℝ 1 (fun t : ℝ => φ (pt t)) := by
  have h1 : ContDiff ℝ 1 (φ ∘ DGPS.torusLift) := hφ.of_le (by simp)
  have h2 : ContDiff ℝ 1 (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    contDiff_pi.2 fun _ => contDiff_id
  exact h1.comp h2

lemma hasDerivAt_psi (hφ : DGPS.IsSmoothPeriodic φ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (pt s))
      (fderiv ℝ (φ ∘ DGPS.torusLift) (fun _ => t) (fun _ => 1)) t := by
  have h1 : HasFDerivAt (φ ∘ DGPS.torusLift) (fderiv ℝ (φ ∘ DGPS.torusLift) (fun _ => t))
      (fun _ => t) :=
    ((hφ.differentiable (by simp)).differentiableAt).hasFDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (fun _ : Fin 1 => s)) (fun _ => (1 : ℝ)) t :=
    hasDerivAt_pi.2 fun _ => hasDerivAt_id t
  exact h1.comp_hasDerivAt t h2

lemma coordPartial_eq (hφ : DGPS.IsSmoothPeriodic φ) (y : Torus 1) :
    DGPS.coordPartial 0 φ y = deriv (fun s : ℝ => φ (pt s)) (SharpLSI.secT y 0) := by
  have e1 : SharpLSI.secT y = fun _ => SharpLSI.secT y 0 :=
    funext fun i => by rw [Subsingleton.elim i 0]
  have e2 : (Pi.single 0 1 : Fin 1 → ℝ) = fun _ => 1 :=
    funext fun i => by rw [Subsingleton.elim i 0]; simp
  unfold DGPS.coordPartial
  rw [e2, (hasDerivAt_psi hφ (SharpLSI.secT y 0)).deriv, ← e1]

lemma deriv_psi_periodic :
    Function.Periodic (deriv fun s : ℝ => φ (pt s)) 1 := by
  intro t
  have h := deriv_comp_add_const (f := fun s : ℝ => φ (pt s)) (a := (1 : ℝ)) (x := t)
  have e : (fun x : ℝ => φ (pt (x + 1))) = fun s => φ (pt s) := funext fun x => by
    rw [pt_add_one]
  rw [e] at h
  exact h.symm

lemma measurable_phi (hφ : DGPS.IsSmoothPeriodic φ) : Measurable φ := by
  have h : φ = fun y => (φ ∘ DGPS.torusLift) (SharpLSI.secT y) := funext fun y => by
    simp [DGPS.torusLift, SharpLSI.liftT_secT]
  rw [h]
  exact hφ.continuous.measurable.comp SharpLSI.measurable_secT

lemma measurable_coordPartial (hφ : DGPS.IsSmoothPeriodic φ) :
    Measurable (DGPS.coordPartial 0 φ) := by
  have h : DGPS.coordPartial 0 φ = fun y => deriv (fun s : ℝ => φ (pt s)) (SharpLSI.secT y 0) :=
    funext (coordPartial_eq hφ)
  rw [h]
  exact measurable_comp_secT ((contDiff_psi hφ).continuous_deriv le_rfl)

lemma weak_ibp (hφ : DGPS.IsSmoothPeriodic φ) :
    ∫ y, gT y * DGPS.coordPartial 0 φ y ∂haar 1 =
      -∫ y, (hSum y - hMean) * φ y ∂haar 1 := by
  set ψ : ℝ → ℝ := fun s => φ (pt s) with hψdef
  have hψ := contDiff_psi hφ
  have hgm : AEStronglyMeasurable gT (haar 1) :=
    (measurable_comp_secT continuous_gLine).aestronglyMeasurable
  have hL : AEStronglyMeasurable (fun y => gT y * DGPS.coordPartial 0 φ y) (haar 1) :=
    hgm.mul (measurable_coordPartial hφ).aestronglyMeasurable
  have hR : AEStronglyMeasurable (fun y => (hSum y - hMean) * φ y) (haar 1) :=
    (hSum_meas.sub measurable_const).aestronglyMeasurable.mul (measurable_phi hφ).aestronglyMeasurable
  rw [integral_haar_eq hL, integral_haar_eq hR, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_of_le zero_le_one]
  have hcp : ∀ t : ℝ, DGPS.coordPartial 0 φ (pt t) = deriv ψ t := fun t => by
    rw [coordPartial_eq hφ]
    exact periodic_secT (deriv_psi_periodic) t
  have e1 : ∫ t in (0 : ℝ)..1, gT (pt t) * DGPS.coordPartial 0 φ (pt t) =
      ∫ t in (0 : ℝ)..1, gLine t * deriv ψ t :=
    intervalIntegral.integral_congr fun t _ => by simp only [gT_pt, hcp]
  rw [e1]
  have hψac : AbsolutelyContinuousOnInterval ψ 0 1 :=
    (hψ.contDiffOn (s := uIcc 0 1)).absolutelyContinuousOnInterval
  have key := ac_gLine.integral_mul_deriv_eq_deriv_mul hψac
  have hae : ∫ x in (0 : ℝ)..1, deriv gLine x * ψ x = ∫ x in (0 : ℝ)..1, fLine x * ψ x :=
    intervalIntegral.integral_congr_ae (by
      filter_upwards [ae_hasDerivAt_gLine] with t ht _
      rw [ht.deriv])
  rw [key, hae, gLine_one, gLine_zero]
  simp [fLine]
  rfl

end IBP

/-! ### The packet theorem -/

/-- RUF002.  With `h_n` the spike functions of RUF001 and `T = Torus 1`, `m = haar 1`:

1. `∑_{n ≥ 2} h_n(x)` is finite for a.e. `x`; the sum `hSum` lies in `L^p(T)` for every real
   `1 ≤ p < 2` simultaneously, since `‖h_n‖_p = n^(-1/p) e^(-(2-p)n/p)` is summable; moreover
   the `L^p` norm of the tail of the series tends to `0`.
2. The mean is `c = hMean = ∑_{n ≥ 2} e^(-n)/n ∈ (0,1)` and `∫ hSum = c`.
3. The single periodic primitive `g(x) = ∫₀ˣ (h - c)` (read through the lift `pt : ℝ → T`) is
   absolutely continuous on `[0,1]`, with `g(0) = g(1) = 0`, `‖g‖_∞ ≤ c`, a.e. derivative
   `h - c ∈ L^p` for all `1 ≤ p < 2`, and it satisfies the weak-derivative identity
   `∫ g ∂₀φ dm = -∫ (h - c) φ dm` for every smooth periodic test function `φ` (the
   `H¹`-type definition `DGPS.IsWeakGradient` is not usable since `h - c ∉ L²`). -/
theorem common_spike_sum_and_absolutely_continuous_primitive :
    (∀ᵐ x ∂haar 1, Summable fun n : ℕ => h (n + 2) x) ∧
    (∀ p : ℝ, 1 ≤ p → p < 2 →
      (∀ n : ℕ, eLpNorm (h (n + 2)) (ENNReal.ofReal p) (haar 1) =
        ENNReal.ofReal (((n + 2 : ℕ) : ℝ) ^ (-1 / p) *
          Real.exp (-(2 - p) * ((n + 2 : ℕ) : ℝ) / p))) ∧
      Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-1 / p) *
          Real.exp (-(2 - p) * ((n + 2 : ℕ) : ℝ) / p)) ∧
      MemLp hSum (ENNReal.ofReal p) (haar 1) ∧
      Tendsto (fun N : ℕ => eLpNorm (fun x => hSum x - ∑ n ∈ Finset.range N, h (n + 2) x)
        (ENNReal.ofReal p) (haar 1)) atTop (𝓝 0)) ∧
    (HasSum (fun n : ℕ => Real.exp (-((n + 2 : ℕ) : ℝ)) / ((n + 2 : ℕ) : ℝ)) hMean ∧
      0 < hMean ∧ hMean < 1 ∧ ∫ x, hSum x ∂haar 1 = hMean) ∧
    ∃ g : Torus 1 → ℝ,
      AbsolutelyContinuousOnInterval (fun t : ℝ => g (pt t)) 0 1 ∧
      g (pt 0) = 0 ∧ g (pt 1) = 0 ∧ (∀ y, |g y| ≤ hMean) ∧
      (∀ t : ℝ, g (pt t) = ∫ s in (0 : ℝ)..t, (hSum (pt s) - hMean)) ∧
      (∀ᵐ t : ℝ, HasDerivAt (fun s : ℝ => g (pt s)) (hSum (pt t) - hMean) t) ∧
      (∀ p : ℝ, 1 ≤ p → p < 2 →
        MemLp (fun x => hSum x - hMean) (ENNReal.ofReal p) (haar 1)) ∧
      (∀ φ : Torus 1 → ℝ, DGPS.IsSmoothPeriodic φ →
        ∫ y, g y * DGPS.coordPartial 0 φ y ∂haar 1 =
          -∫ y, (hSum y - hMean) * φ y ∂haar 1) := by
  refine ⟨ae_summable_h, fun p hp hp2 => ⟨fun n => eLpNorm_h hp n, summable_normTerm hp hp2,
    memLp_hSum hp hp2, tendsto_eLpNorm_partial hp hp2⟩,
    ⟨summable_meanTerm.hasSum, hMean_pos, hMean_lt_one, integral_hSum⟩, gT, ?_, ?_, ?_,
    abs_gT_le, ?_, ?_, fun p hp hp2 => memLp_hSum_sub_mean hp hp2, fun φ hφ => weak_ibp hφ⟩
  · have e : (fun t : ℝ => gT (pt t)) = gLine := funext gT_pt
    rw [e]; exact ac_gLine
  · rw [gT_pt]; exact gLine_zero
  · rw [gT_pt]; exact gLine_one
  · intro t; rw [gT_pt]; rfl
  · have e : (fun t : ℝ => gT (pt t)) = gLine := funext gT_pt
    rw [e]; exact ae_hasDerivAt_gLine

end RUF002

end DGPS.Examples.RoughBoundary.Spikes
