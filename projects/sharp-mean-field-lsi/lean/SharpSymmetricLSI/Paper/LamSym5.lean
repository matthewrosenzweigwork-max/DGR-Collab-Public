import SharpSymmetricLSI.Paper.LamSym3
import SharpSymmetricLSI.Paper.LamSym4
import SharpSymmetricLSI.Paper.GaussForm16

/-!
# (2.8) (lane s42): `λ_N^sym → λ_G` from finite linear tests

* Gaussian side: for a centered Gaussian `γ` with covariance `C`, the linear statistic
  `ℓ_v(z) = ∑_{i<n} v_i z_i` has mean zero and variance `⟨v, C v⟩` (`var_linSum_gamma`); the
  diagonal limiting mobility gives energy `∑ λ'_i v_i²` (`sum_diag_mob`).
* `limsup_lamSym_le_of_tests`: if for every finite `v` with `⟨v,Cv⟩ > 0` there are symmetric
  `H¹` tests whose variances tend to `⟨v,Cv⟩` and energies to `∑ λ'_i v_i²` (Section 8.5, the
  linear statistics `∑ v_j Z_{N,j}` minus their means), then `limsup λ_N^sym ≤ λ_G`
  (with LamSym3).
* `lamSym_tendsto_of`: with the lower bound (LamSym4), (2.8).
-/

open MeasureTheory Filter Topology ProbabilityTheory Finset
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The linear statistic is centered under `γ`. -/
theorem integral_linSum_gamma {γ : Measure (ℕ → ℝ)} {C : ℕ → ℕ → ℝ}
    (hγ : IsCenteredGaussianCov γ C) (s : Finset ℕ) (v : ℕ → ℝ) :
    ∫ z, ∑ i ∈ s, v i * z i ∂γ = 0 := by
  have := hγ.1
  rw [show (∫ z, ∑ i ∈ s, v i * z i ∂γ) = ∫ z, id (∑ i ∈ s, v i * z i) ∂γ from rfl,
    ← integral_map (measurable_linSum s v).aemeasurable aestronglyMeasurable_id, hγ.2 s v]
  exact integral_id_gaussianReal

/-- **Variance of the linear statistic under `γ` is `⟨v, Cv⟩`.** -/
theorem var_linSum_gamma {γ : Measure (ℕ → ℝ)} {C : ℕ → ℕ → ℝ}
    (hγ : IsCenteredGaussianCov γ C) (s : Finset ℕ) (v : ℕ → ℝ)
    (h0 : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j) :
    var γ (fun z => ∑ i ∈ s, v i * z i) =
      ENNReal.ofReal (∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j) := by
  have := hγ.1
  have hL := memLp_linSum_gamma hγ s v
  show evariance _ γ = _
  rw [← hL.ofReal_variance_eq, variance_of_integral_eq_zero (measurable_linSum s v).aemeasurable
    (integral_linSum_gamma hγ s v), integral_linSum_sq_gamma hγ s v h0]

/-- The diagonal limiting mobility: `∑_{i,j} v_i v_j λ'_i δ_{ij} = ∑_i λ'_i v_i²`. -/
theorem sum_diag_mob (s : Finset ℕ) (v lam' : ℕ → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, v i * v j * (if i = j then lam' i else 0) = ∑ i ∈ s, lam' i * v i ^ 2 := by
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
    (fun h => absurd hi h), if_pos rfl]
  ring

/-- **`limsup λ_N^sym ≤ ∑ λ'_i v_i² / ⟨v,Cv⟩`** from tests with converging variance and energy. -/
theorem limsup_lamSym_le_of_test {Q L : ℝ} (hQ : 0 < Q) (hL : 0 ≤ L)
    {f : (N : ℕ) → Config N d → ℝ}
    (hf : ∀ᶠ N in atTop, MemH1C (gibbs V W N) (f N) ∧ IsSymmetric (f N))
    (hvar : Tendsto (fun N => var (gibbs V W N) (f N)) atTop (𝓝 (ENNReal.ofReal Q)))
    (hen : Tendsto (fun N => energy V W N (f N)) atTop (𝓝 (ENNReal.ofReal L))) :
    limsup (fun N => lamSym V W N) atTop ≤ ENNReal.ofReal L / ENNReal.ofReal Q := by
  have hQ0 : ENNReal.ofReal Q ≠ 0 := by simpa using hQ
  have hratio : Tendsto (fun N => energy V W N (f N) / var (gibbs V W N) (f N)) atTop
      (𝓝 (ENNReal.ofReal L / ENNReal.ofReal Q)) :=
    ENNReal.Tendsto.div hen (Or.inr hQ0) hvar (Or.inr ENNReal.ofReal_ne_top)
  have hpos : ∀ᶠ N in atTop, 0 < var (gibbs V W N) (f N) :=
    hvar.eventually (lt_mem_nhds (pos_iff_ne_zero.mpr hQ0))
  refine (limsup_le_limsup (f := atTop) (v := fun N => energy V W N (f N) /
    var (gibbs V W N) (f N)) ?_ (by isBoundedDefault) (by isBoundedDefault)).trans
    (le_of_eq hratio.limsup_eq)
  filter_upwards [hf, hpos] with N ⟨hmem, hsym⟩ hp
  unfold lamSym
  exact iInf₂_le (f N) ⟨hmem, hsym, hp⟩

/-- **`limsup λ_N^sym ≤ λ_G`** from finite linear tests (Section 8.5). -/
theorem limsup_lamSym_le_of_tests {C : ℕ → ℕ → ℝ} {σ : ℝ} (hσ0 : 0 < σ)
    (hCs : ∀ i j, C i j = C j i)
    (hnn : ∀ (s : Finset ℕ) (v : ℕ → ℝ), 0 ≤ ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j)
    (hup : ∀ (s : Finset ℕ) (v : ℕ → ℝ),
      ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j ≤ (∑ i ∈ s, v i ^ 2) / σ)
    (hcol : ∀ j, Summable fun k => C k j ^ 2) {lam' : ℕ → ℝ} (hlam : ∀ i, 0 < lam' i)
    (htests : ∀ (n : ℕ) (v : ℕ → ℝ), 0 < ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j →
      ∃ f : (N : ℕ) → Config N d → ℝ,
        (∀ᶠ N in atTop, MemH1C (gibbs V W N) (f N) ∧ IsSymmetric (f N)) ∧
        Tendsto (fun N => var (gibbs V W N) (f N)) atTop
          (𝓝 (ENNReal.ofReal (∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j))) ∧
        Tendsto (fun N => energy V W N (f N)) atTop
          (𝓝 (ENNReal.ofReal (∑ i ∈ range n, lam' i * v i ^ 2)))) :
    limsup (fun N => lamSym V W N) atTop ≤ lamG lam' C := by
  refine le_lamG_of_trunc hσ0 hCs hnn hup hcol hlam fun n v hQ => ?_
  obtain ⟨f, hf, hvar, hen⟩ := htests n v hQ
  exact limsup_lamSym_le_of_test hQ (sum_nonneg fun i _ => mul_nonneg (hlam i).le (sq_nonneg _))
    hf hvar hen

/-- **(2.8): `λ_N^sym → λ_G`**, from compactness (2.5)–(2.7), the Gaussian Poincaré inequality
(8.10), and finite linear tests. -/
theorem lamSym_tendsto_of (hyp : Hyp V W KV KW) {γ : Measure (ℕ → ℝ)} [IsProbabilityMeasure γ]
    {EInf : ((ℕ → ℝ) → ℝ) → ℝ≥0∞} {C : ℕ → ℕ → ℝ} {σ : ℝ} (hσ0 : 0 < σ)
    (hCs : ∀ i j, C i j = C j i)
    (hnn : ∀ (s : Finset ℕ) (v : ℕ → ℝ), 0 ≤ ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j)
    (hup : ∀ (s : Finset ℕ) (v : ℕ → ℝ),
      ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j ≤ (∑ i ∈ s, v i ^ 2) / σ)
    (hcol : ∀ j, Summable fun k => C k j ^ 2) {lam' : ℕ → ℝ} (hlam : ∀ i, 0 < lam' i)
    (hcomp : CompactnessProperty' V W γ EInf)
    (hP : ∀ f : (ℕ → ℝ) → ℝ, MemLp f 2 γ → var γ f ≤ EInf f / lamG lam' C)
    (htests : ∀ (n : ℕ) (v : ℕ → ℝ), 0 < ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j →
      ∃ f : (N : ℕ) → Config N d → ℝ,
        (∀ᶠ N in atTop, MemH1C (gibbs V W N) (f N) ∧ IsSymmetric (f N)) ∧
        Tendsto (fun N => var (gibbs V W N) (f N)) atTop
          (𝓝 (ENNReal.ofReal (∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j))) ∧
        Tendsto (fun N => energy V W N (f N)) atTop
          (𝓝 (ENNReal.ofReal (∑ i ∈ range n, lam' i * v i ^ 2)))) :
    lamG lam' C ≤ liminf (fun N => lamSym V W N) atTop ∧
    limsup (fun N => lamSym V W N) atTop ≤ lamG lam' C ∧
    Tendsto (fun N => lamSym V W N) atTop (𝓝 (lamG lam' C)) := by
  have h1 := le_liminf_lamSym hyp hcomp hP
  have h2 := limsup_lamSym_le_of_tests hσ0 hCs hnn hup hcol hlam htests
  exact ⟨h1, h2, tendsto_of_le_liminf_of_limsup_le h1 h2⟩

end SharpLSI
