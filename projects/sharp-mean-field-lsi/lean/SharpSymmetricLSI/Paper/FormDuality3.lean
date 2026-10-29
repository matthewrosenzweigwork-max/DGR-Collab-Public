import SharpSymmetricLSI.Paper.FormDuality2
import SharpSymmetricLSI.Paper.GaussForm11

/-!
# R32 (8.8), part 3: cylinder approximation of pairs `(F, LF)`

`CylApprox lam' Y γ F G`: there are cylinders `c_n` with `c_n → F` and `L c_n → G` in `L²(γ)`.
* `CylApprox.of_tendsto`: the class is closed under `L²` limits of pairs (diagonal argument);
* `cylApprox_of_bdd`: smooth `G` of finitely many coordinates with bounded derivatives up to
  order two (the cutoff lemma of GaussForm10/11);
* generic `L²` convergence lemmas: a.e. domination, products with bounded factors.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI

variable {γ : Measure (ℕ → ℝ)}

/-- `(F, G)` is approximated by cylinders: `c_n → F` and `L c_n → G` in `L²(γ)`. -/
def CylApprox (lam' : ℕ → ℝ) (Y : ℕ → (ℕ → ℝ) → ℝ) (γ : Measure (ℕ → ℝ))
    (F G : (ℕ → ℝ) → ℝ) : Prop :=
  ∃ c : ℕ → Cyl, Tendsto (fun n => eLpNorm (fun z => (c n).eval z - F z) 2 γ) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun z => (c n).gen lam' Y z - G z) 2 γ) atTop (𝓝 0)

theorem aestronglyMeasurable_genG {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, AEStronglyMeasurable (Y i) γ)
    (lam' : ℕ → ℝ) {N : ℕ} {G : (Fin N → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) :
    AEStronglyMeasurable (genG lam' Y N G) γ := by
  unfold genG
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact aestronglyMeasurable_const.mul (((continuous_d2 hG i).measurable.comp
    (measurable_zBlock N)).aestronglyMeasurable.sub
    ((((measurable_pi_apply (i : ℕ)).aestronglyMeasurable).add (hY i)).mul
    ((continuous_pd hG i).measurable.comp (measurable_zBlock N)).aestronglyMeasurable))

theorem Cyl.aestronglyMeasurable_gen {Y : ℕ → (ℕ → ℝ) → ℝ}
    (hY : ∀ i, AEStronglyMeasurable (Y i) γ) (lam' : ℕ → ℝ) (c : Cyl) :
    AEStronglyMeasurable (c.gen lam' Y) γ :=
  aestronglyMeasurable_genG hY lam' c.smooth

/-- Triangle inequality for `L²` distances. -/
theorem eLpNorm_sub_le_add (f g h : (ℕ → ℝ) → ℝ) :
    eLpNorm (fun z => f z - h z) 2 γ ≤
      eLpNorm (fun z => f z - g z) 2 γ + eLpNorm (fun z => g z - h z) 2 γ := by
  have e : (fun z => f z - h z) = (fun z => f z - g z) + (fun z => g z - h z) := by
    funext z; simp
  rw [e]
  exact eLpNorm_add_le (by norm_num)

/-- Choosing, for every `k`, an index where two null sequences are below `1/k`. -/
theorem exists_index_le (a b : ℕ → ℝ≥0∞) (ha : Tendsto a atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) (k : ℕ) : ∃ n, a n < (k : ℝ≥0∞)⁻¹ ∧ b n < (k : ℝ≥0∞)⁻¹ := by
  have hk : (0 : ℝ≥0∞) < (k : ℝ≥0∞)⁻¹ := ENNReal.inv_pos.2 (ENNReal.natCast_ne_top k)
  exact (((tendsto_order.1 ha).2 _ hk).and ((tendsto_order.1 hb).2 _ hk)).exists

/-- **Closure under `L²` limits** (diagonal argument). -/
theorem CylApprox.of_tendsto {lam' : ℕ → ℝ} {Y : ℕ → (ℕ → ℝ) → ℝ}
    (hY : ∀ i, AEStronglyMeasurable (Y i) γ) {F G : (ℕ → ℝ) → ℝ} {Fk Gk : ℕ → (ℕ → ℝ) → ℝ}
    (hk : ∀ k, CylApprox lam' Y γ (Fk k) (Gk k))
    (hFk : ∀ k, AEStronglyMeasurable (Fk k) γ) (hGk : ∀ k, AEStronglyMeasurable (Gk k) γ)
    (hFm : AEStronglyMeasurable F γ) (hGm : AEStronglyMeasurable G γ)
    (hF : Tendsto (fun k => eLpNorm (fun z => Fk k z - F z) 2 γ) atTop (𝓝 0))
    (hG : Tendsto (fun k => eLpNorm (fun z => Gk k z - G z) 2 γ) atTop (𝓝 0)) :
    CylApprox lam' Y γ F G := by
  choose c hc1 hc2 using hk
  choose n hn1 hn2 using fun k => exists_index_le _ _ (hc1 k) (hc2 k) k
  have hinv : Tendsto (fun k : ℕ => (k : ℝ≥0∞)⁻¹) atTop (𝓝 0) := ENNReal.tendsto_inv_nat_nhds_zero
  refine ⟨fun k => c k (n k), ?_, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hinv.add hF) (fun _ => bot_le) fun k => ?_
    refine (eLpNorm_sub_le_add _ (Fk k) _).trans ?_
    exact add_le_add (hn1 k).le le_rfl
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hinv.add hG) (fun _ => bot_le) fun k => ?_
    refine (eLpNorm_sub_le_add _ (Gk k) _).trans ?_
    exact add_le_add (hn2 k).le le_rfl

/-- **Dominated convergence in `L²`**, a.e. version. -/
theorem tendsto_eLpNorm_two_of_dom_ae {F : ℕ → (ℕ → ℝ) → ℝ}
    (hm : ∀ n, AEStronglyMeasurable (F n) γ) {g : (ℕ → ℝ) → ℝ} (hg : MemLp g 2 γ)
    (hB : ∀ n, ∀ᵐ z ∂γ, |F n z| ≤ g z) (hlim : ∀ᵐ z ∂γ, Tendsto (fun n => F n z) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 2 γ) atTop (𝓝 0) := by
  have e : ∀ n, eLpNorm (F n) 2 γ = (∫⁻ z, ‖F n z‖ₑ ^ (2 : ℝ≥0∞).toReal ∂γ) ^ (1 / (2 : ℝ≥0∞).toReal) :=
    fun n => eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top (hm n)
  simp_rw [e]
  have hfin : ∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ≥0∞).toReal ∂γ ≠ ⊤ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hg.eLpNorm_lt_top).ne
  have hint : Tendsto (fun n => ∫⁻ z, ‖F n z‖ₑ ^ (2 : ℝ≥0∞).toReal ∂γ) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := γ)
      (F := fun n z => ‖F n z‖ₑ ^ (2 : ℝ≥0∞).toReal) (f := fun _ => 0)
      (fun z => ‖g z‖ₑ ^ (2 : ℝ≥0∞).toReal)
      (fun n => ((hm n).enorm).pow_const _)
      (fun n => (hB n).mono fun z hz => by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [← ofReal_norm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (by
          rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact hz.trans (le_abs_self _)))
      hfin
      (hlim.mono fun z hz => by
        have h1 : Tendsto (fun n => ‖F n z‖ₑ) atTop (𝓝 0) := by
          have := (continuous_enorm.tendsto (0 : ℝ)).comp hz
          simpa [Function.comp_def] using this
        have := (ENNReal.continuous_rpow_const (y := (2 : ℝ≥0∞).toReal)).tendsto 0 |>.comp h1
        simpa [Function.comp_def, ENNReal.zero_rpow_of_pos] using this)
    simpa using this
  have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0 |>.comp hint
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos] using this

/-- **Products with a bounded convergent factor**: `a_N b → a b` in `L²` if `a_N → a` in `L²`,
`|a_N|, |a| ≤ K` and `b ∈ L²`. -/
theorem tendsto_eLpNorm_mul_bdd {a : ℕ → (ℕ → ℝ) → ℝ} {a₀ b : (ℕ → ℝ) → ℝ}
    (ham : ∀ N, AEStronglyMeasurable (a N) γ) (ha₀ : AEStronglyMeasurable a₀ γ) {K : ℝ}
    (haK : ∀ N z, |a N z| ≤ K) (ha₀K : ∀ z, |a₀ z| ≤ K)
    (ha : Tendsto (fun N => eLpNorm (fun z => a N z - a₀ z) 2 γ) atTop (𝓝 0)) (hb : MemLp b 2 γ) :
    Tendsto (fun N => eLpNorm (fun z => a N z * b z - a₀ z * b z) 2 γ) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have h1 : Tendsto (fun n => eLpNorm (a (ns n) - a₀) 2 γ) atTop (𝓝 0) := ha.comp hns
  obtain ⟨ms, -, hms⟩ := (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero h1).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hgL : MemLp (fun z => (2 * K) * |b z|) 2 γ := hb.abs.const_mul _
  refine tendsto_eLpNorm_two_of_dom_ae (fun n => ((ham _).mul hb.aestronglyMeasurable).sub (ha₀.mul hb.aestronglyMeasurable)) hgL
    (fun n => Eventually.of_forall fun z => ?_) (hms.mono fun z hz => ?_)
  · rw [← sub_mul, abs_mul]
    refine mul_le_mul_of_nonneg_right ((abs_sub _ _).trans ?_) (abs_nonneg _)
    linarith [haK (ns (ms n)) z, ha₀K z]
  · have := (hz.sub_const (a₀ z)).mul_const (b z)
    simpa [sub_mul] using this

/-- **Products**: `a_N b_N → a b` in `L²` if moreover `b_N → b` in `L²`. -/
theorem tendsto_eLpNorm_mul_bdd' {a : ℕ → (ℕ → ℝ) → ℝ} {a₀ b₀ : (ℕ → ℝ) → ℝ}
    {b : ℕ → (ℕ → ℝ) → ℝ}
    (ham : ∀ N, AEStronglyMeasurable (a N) γ) (ha₀ : AEStronglyMeasurable a₀ γ)
    (hbm : ∀ N, AEStronglyMeasurable (b N) γ) {K : ℝ}
    (haK : ∀ N z, |a N z| ≤ K) (ha₀K : ∀ z, |a₀ z| ≤ K)
    (ha : Tendsto (fun N => eLpNorm (fun z => a N z - a₀ z) 2 γ) atTop (𝓝 0)) (hb₀ : MemLp b₀ 2 γ)
    (hb : Tendsto (fun N => eLpNorm (fun z => b N z - b₀ z) 2 γ) atTop (𝓝 0)) :
    Tendsto (fun N => eLpNorm (fun z => a N z * b N z - a₀ z * b₀ z) 2 γ) atTop (𝓝 0) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (ha₀K 0)
  have h2 := tendsto_eLpNorm_mul_bdd ham ha₀ haK ha₀K ha hb₀
  have h3 : Tendsto (fun N => ENNReal.ofReal K * eLpNorm (fun z => b N z - b₀ z) 2 γ) atTop
      (𝓝 0) := by simpa using ENNReal.Tendsto.const_mul hb (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using h3.add h2)
    (fun _ => bot_le) fun N => ?_
  refine (eLpNorm_sub_le_add (fun z => a N z * b N z) (fun z => a N z * b₀ z)
    (fun z => a₀ z * b₀ z)).trans (add_le_add ?_ le_rfl)
  have e : (fun z => a N z * b N z - a N z * b₀ z) = fun z => a N z * (b N z - b₀ z) := by
    funext z; ring
  rw [e]
  calc eLpNorm (fun z => a N z * (b N z - b₀ z)) 2 γ
      ≤ eLpNorm (fun z => K * (b N z - b₀ z)) 2 γ := by
        refine eLpNorm_mono ((ham N).mul ((hbm N).sub hb₀.aestronglyMeasurable)) fun z => ?_
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hK]
        exact mul_le_mul_of_nonneg_right (haK N z) (abs_nonneg _)
    _ = ENNReal.ofReal K * eLpNorm (fun z => b N z - b₀ z) 2 γ := by
        rw [show (fun z => K * (b N z - b₀ z)) = K • (fun z => b N z - b₀ z) from rfl,
          eLpNorm_const_smul, Real.enorm_eq_ofReal hK]

/-- **Level 1**: smooth functions of finitely many coordinates with bounded derivatives up to
order two (GaussForm10/11 cutoffs). -/
theorem cylApprox_of_bdd [IsProbabilityMeasure γ] {N : ℕ} {G : (Fin N → ℝ) → ℝ}
    (hG : ContDiff ℝ ∞ G) {B : ℝ} (hGB : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k G x‖ ≤ B)
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hz : ∀ i, MemLp (fun z : ℕ → ℝ => z i) 2 γ)
    (hY : ∀ i, MemLp (Y i) 2 γ) (lam' : ℕ → ℝ) :
    CylApprox lam' Y γ (fun z => G (zBlock N z)) (genG lam' Y N G) :=
  ⟨cutCyl N hG, tendsto_cutCyl_L2 hG (fun x => by
      have := hGB 0 (by norm_num) x
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this),
    tendsto_cutCyl_gen hG hGB hz hY lam'⟩

end SharpLSI
