import SharpSymmetricLSI.Paper.FormDuality6
import SharpSymmetricLSI.Paper.GaussFormClause1
import SharpSymmetricLSI.Paper.GaussFormClause2

/-!
# R32 (8.8), part 7: the hard direction `ℰ_∞(f) ≤ sup_c (2∫f(-Lc) - ℰ(c))`

With `f_α = ∫ H_α f dγ` and `Q(f) = ∑_α κ_α f_α²`:
* `gaussForm_le_Q`: `ℰ_∞(f) ≤ Q(f)` (Hermite truncations of `f`, lower semicontinuity);
* `Q_le_sup`: `Q(f) ≤ sup_c (2∫f(-Lc) - ℰ(c))` (cylinder approximants of finite Hermite sums);
* `form_duality_generic` and `form_duality_of_prop21`: the duality (8.8).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace SharpLSI

variable {γ : Measure (ℕ → ℝ)}

/-- Products of `L²`-convergent sequences: `∫ a_n b_n → ∫ a b`. -/
theorem tendsto_integral_mul_of_eLpNorm {a b : ℕ → (ℕ → ℝ) → ℝ} {a₀ b₀ : (ℕ → ℝ) → ℝ}
    (ha : ∀ n, MemLp (a n) 2 γ) (hb : ∀ n, MemLp (b n) 2 γ) (ha₀ : MemLp a₀ 2 γ)
    (hb₀ : MemLp b₀ 2 γ)
    (hA : Tendsto (fun n => eLpNorm (fun z => a n z - a₀ z) 2 γ) atTop (𝓝 0))
    (hB : Tendsto (fun n => eLpNorm (fun z => b n z - b₀ z) 2 γ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, a n z * b n z ∂γ) atTop (𝓝 (∫ z, a₀ z * b₀ z ∂γ)) := by
  set na : ℕ → ℝ := fun n => (eLpNorm (fun z => a n z - a₀ z) 2 γ).toReal
  set nb : ℕ → ℝ := fun n => (eLpNorm (fun z => b n z - b₀ z) 2 γ).toReal
  have hna : Tendsto na atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hA
    rw [ENNReal.toReal_zero] at this; exact this
  have hnb : Tendsto nb atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hB
    rw [ENNReal.toReal_zero] at this; exact this
  set A := (eLpNorm a₀ 2 γ).toReal
  set B := (eLpNorm b₀ 2 γ).toReal
  have hbound : ∀ n, |∫ z, a n z * b n z ∂γ - ∫ z, a₀ z * b₀ z ∂γ| ≤ na n * (nb n + B) + A * nb n :=
    fun n => by
    have hda : MemLp (fun z => a n z - a₀ z) 2 γ := (ha n).sub ha₀
    have hdb : MemLp (fun z => b n z - b₀ z) 2 γ := (hb n).sub hb₀
    have e : ∫ z, a n z * b n z ∂γ - ∫ z, a₀ z * b₀ z ∂γ =
        ∫ z, (a n z - a₀ z) * b n z ∂γ + ∫ z, a₀ z * (b n z - b₀ z) ∂γ := by
      have i1 : Integrable (fun z => (a n z - a₀ z) * b n z) γ := hda.integrable_mul (hb n)
      have i2 : Integrable (fun z => a₀ z * (b n z - b₀ z)) γ := ha₀.integrable_mul hdb
      have i3 : Integrable (fun z => a n z * b n z) γ := (ha n).integrable_mul (hb n)
      have i4 : Integrable (fun z => a₀ z * b₀ z) γ := ha₀.integrable_mul hb₀
      rw [← integral_add i1 i2, ← integral_sub i3 i4]
      congr 1; funext z; ring
    have h1 := abs_integral_mul_le_L2 hda (hb n)
    have h2 := abs_integral_mul_le_L2 ha₀ hdb
    have hbn : (eLpNorm (b n) 2 γ).toReal ≤ nb n + B := by
      have hle : eLpNorm (b n) 2 γ ≤ eLpNorm (fun z => b n z - b₀ z) 2 γ + eLpNorm b₀ 2 γ := by
        have := eLpNorm_sub_le_add (γ := γ) (b n) b₀ (fun _ => 0)
        simpa using this
      rw [← ENNReal.toReal_add hdb.eLpNorm_ne_top hb₀.eLpNorm_ne_top]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hdb.eLpNorm_ne_top, hb₀.eLpNorm_ne_top⟩) hle
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add (h1.trans ?_) h2)
    exact mul_le_mul_of_nonneg_left hbn ENNReal.toReal_nonneg
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => (Real.norm_eq_abs _).le.trans (hbound n)) ?_
  have := (hna.mul (hnb.add_const B)).add (hnb.const_mul A)
  simpa using this

/-- `L²` convergence of negatives. -/
theorem tendsto_eLpNorm_neg {a : ℕ → (ℕ → ℝ) → ℝ} {a₀ : (ℕ → ℝ) → ℝ}
    (h : Tendsto (fun n => eLpNorm (fun z => a n z - a₀ z) 2 γ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun z => -a n z - -a₀ z) 2 γ) atTop (𝓝 0) := by
  refine h.congr fun n => ?_
  rw [← eLpNorm_neg]; congr 1; funext z; simp; ring

theorem kappa_nonneg {ν : ℕ → ℝ} (hν : ∀ j, 0 ≤ ν j) (α : ℕ →₀ ℕ) : 0 ≤ kappa ν α :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hν j) (Nat.cast_nonneg _)

section hermite
variable [IsProbabilityMeasure γ] {ξ : ℕ → (ℕ → ℝ) → ℝ}
  (hΞ : AEMeasurable (fun z j => ξ j z) γ) (hmap : γ.map (fun z j => ξ j z) = gammaRef)
include hΞ hmap

theorem memLp_hermSum (F : Finset (ℕ →₀ ℕ)) (c : (ℕ →₀ ℕ) → ℝ) :
    MemLp (fun z => ∑ α ∈ F, c α * Hxi ξ α z) 2 γ :=
  memLp_finsetSum _ fun α _ => (memLp_Hxi hΞ hmap α).const_mul (c α)

/-- `∫ (∑ t_α H_α)(∑ s_β H_β) = ∑ t_α s_α`. -/
theorem integral_hermSum_mul (F : Finset (ℕ →₀ ℕ)) (t s : (ℕ →₀ ℕ) → ℝ) :
    ∫ z, (∑ α ∈ F, t α * Hxi ξ α z) * (∑ β ∈ F, s β * Hxi ξ β z) ∂γ = ∑ α ∈ F, t α * s α := by
  have hi : ∀ α β, Integrable (fun z => t α * Hxi ξ α z * (s β * Hxi ξ β z)) γ := fun α β =>
    ((memLp_Hxi hΞ hmap α).const_mul (t α)).integrable_mul ((memLp_Hxi hΞ hmap β).const_mul (s β))
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finset_sum _ fun α _ => integrable_finset_sum _ fun β _ => hi α β]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [integral_finset_sum _ fun β _ => hi α β]
  have e : ∀ β, ∫ z, t α * Hxi ξ α z * (s β * Hxi ξ β z) ∂γ =
      t α * s β * (if α = β then 1 else 0) := fun β => by
    rw [← integral_Hxi_mul hΞ hmap α β, ← integral_const_mul]
    congr 1; funext z; ring
  simp_rw [e]
  simp [hα]

/-- `∫ g (∑ c_β H_β) = ∑ c_β ∫ g H_β`. -/
theorem integral_mul_hermSum {g : (ℕ → ℝ) → ℝ} (hg : MemLp g 2 γ) (F : Finset (ℕ →₀ ℕ))
    (c : (ℕ →₀ ℕ) → ℝ) :
    ∫ z, g z * (∑ β ∈ F, c β * Hxi ξ β z) ∂γ = ∑ β ∈ F, c β * ∫ z, g z * Hxi ξ β z ∂γ := by
  have hi : ∀ β, Integrable (fun z => g z * (c β * Hxi ξ β z)) γ := fun β =>
    hg.integrable_mul ((memLp_Hxi hΞ hmap β).const_mul (c β))
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum _ fun β _ => hi β]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← integral_const_mul]; congr 1; funext z; ring

end hermite

/-! ### The core sequence -/

section core
variable {C T : ℕ → ℕ → ℝ} (hγ : IsCenteredGaussianCov γ C) (hPSD : ∀ N, (blockMat C N).PosSemidef)
  (hC : IsInverseOfIPlus T C) {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable T γ i (Y i))
  {lam' : ℕ → ℝ} {v : ℕ → ℕ → ℝ} {ν : ℕ → ℝ} {ξ : ℕ → (ℕ → ℝ) → ℝ}
  (hξ : ∀ j, IsRowVariable v γ j (ξ j))
  (hW : ∀ j k, Tendsto (fun N => ∑ i ∈ Finset.range N, lam' i * v j i * v k i) atTop
    (𝓝 (if j = k then ν j else 0)))
  (hLξ : ∀ j, Tendsto (fun N => eLpNorm (fun z => ∑ i ∈ Finset.range N,
    lam' i * v j i * (z i + Y i z) - ν j * ξ j z) 2 γ) atTop (𝓝 0))
  (hΞ : AEMeasurable (fun z j => ξ j z) γ) (hmap : γ.map (fun z j => ξ j z) = gammaRef)
include hγ hPSD hC hY hξ hW hLξ hΞ hmap

/-- Cylinders approximating `P = ∑_F t_α H_α`, with forms converging to `∑ κ_α t_α²` and
`∫ g (-Lc_n) → ∑ t_α κ_α ∫ g H_α`. -/
theorem exists_core_seq (F : Finset (ℕ →₀ ℕ)) (t : (ℕ →₀ ℕ) → ℝ) :
    ∃ c : ℕ → Cyl,
      Tendsto (fun n => eLpNorm (fun z => (c n).eval z - ∑ α ∈ F, t α * Hxi ξ α z) 2 γ) atTop
        (𝓝 0) ∧
      Tendsto (fun n => (c n).formR lam' γ) atTop (𝓝 (∑ α ∈ F, kappa ν α * t α ^ 2)) ∧
      ∀ g : (ℕ → ℝ) → ℝ, MemLp g 2 γ → Tendsto (fun n => ∫ z, g z * (-(c n).gen lam' Y z) ∂γ)
        atTop (𝓝 (∑ α ∈ F, t α * kappa ν α * ∫ z, g z * Hxi ξ α z ∂γ)) := by
  haveI := hγ.1
  obtain ⟨c, h1, h2⟩ := cylApprox_hermite (fun i => memLp_coord_gamma hγ i) (fun i => (hY i).1)
    hξ hW hLξ hΞ hmap F t
  have h2' := tendsto_eLpNorm_neg h2
  simp only [neg_neg] at h2'
  have hP := memLp_hermSum hΞ hmap F t
  have hG := memLp_hermSum hΞ hmap F (fun α => t α * kappa ν α)
  refine ⟨c, h1, ?_, fun g hg => ?_⟩
  · have e : ∀ n, (c n).formR lam' γ = ∫ z, (c n).eval z * (-(c n).gen lam' Y z) ∂γ := fun n =>
      (cyl_ibp_self hγ hPSD hC hY lam' (c n)).symm
    simp_rw [e]
    have := tendsto_integral_mul_of_eLpNorm (fun n => (c n).memLp_eval)
      (fun n => (memLp_gen hγ hY lam' (c n)).neg) hP hG h1 h2'
    rw [integral_hermSum_mul hΞ hmap] at this
    refine this.congr' (Eventually.of_forall fun n => rfl) |>.trans ?_
    · exact le_of_eq (by congr 1; exact Finset.sum_congr rfl fun α _ => by ring)
  · have := tendsto_integral_mul_of_eLpNorm (a := fun _ => g) (fun _ => hg)
      (fun n => (memLp_gen hγ hY lam' (c n)).neg) hg hG (by simp) h2'
    rw [integral_mul_hermSum hΞ hmap hg] at this
    exact this

end core

/-! ### `ℰ_∞ ≤ Q ≤ sup` -/

/-- The Hermite coefficients `f_α = ∫ H_α f dγ`. -/
noncomputable def hcoef (ξ : ℕ → (ℕ → ℝ) → ℝ) (γ : Measure (ℕ → ℝ)) (f : (ℕ → ℝ) → ℝ)
    (α : ℕ →₀ ℕ) : ℝ :=
  ∫ z, Hxi ξ α z * f z ∂γ

/-- `Q(f) = ∑_α κ_α f_α²`. -/
noncomputable def formQ (ν : ℕ → ℝ) (ξ : ℕ → (ℕ → ℝ) → ℝ) (γ : Measure (ℕ → ℝ))
    (f : (ℕ → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑' α, ENNReal.ofReal (kappa ν α * hcoef ξ γ f α ^ 2)

theorem coeFn_finset_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℝ) (g : ι → Lp ℝ 2 γ) :
    ⇑(∑ i ∈ s, c i • g i) =ᵐ[γ] fun z => ∑ i ∈ s, c i * g i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Lp.coeFn_zero ℝ 2 γ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (c a • g a) (∑ i ∈ s, c i • g i), Lp.coeFn_smul (c a) (g a), ih]
      with z h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Finset.sum_insert ha]
    rfl

theorem formR_nonneg' {lam' : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam' i) (c : Cyl) : 0 ≤ c.formR lam' γ :=
  integral_nonneg fun z => Finset.sum_nonneg fun i _ => mul_nonneg (hlam _) (sq_nonneg _)

section main
variable {C T : ℕ → ℕ → ℝ} (hγ : IsCenteredGaussianCov γ C) (hPSD : ∀ N, (blockMat C N).PosSemidef)
  (hC : IsInverseOfIPlus T C) {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable T γ i (Y i))
  {lam' : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam' i) {v : ℕ → ℕ → ℝ} {ν : ℕ → ℝ} (hν : ∀ j, 0 ≤ ν j)
  {ξ : ℕ → (ℕ → ℝ) → ℝ}
  (hξ : ∀ j, IsRowVariable v γ j (ξ j))
  (hW : ∀ j k, Tendsto (fun N => ∑ i ∈ Finset.range N, lam' i * v j i * v k i) atTop
    (𝓝 (if j = k then ν j else 0)))
  (hLξ : ∀ j, Tendsto (fun N => eLpNorm (fun z => ∑ i ∈ Finset.range N,
    lam' i * v j i * (z i + Y i z) - ν j * ξ j z) 2 γ) atTop (𝓝 0))
  (hΞ : AEMeasurable (fun z j => ξ j z) γ) (hmap : γ.map (fun z j => ξ j z) = gammaRef)
include hγ hPSD hC hY hlam hξ hW hLξ hΞ hmap

/-- `Q_F(f) ≤ sup_c (2∫f(-Lc) - ℰ(c))` for every finite `F`. -/
theorem formQ_finset_le_sup {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ) (F : Finset (ℕ →₀ ℕ)) :
    ((∑ α ∈ F, kappa ν α * hcoef ξ γ f α ^ 2 : ℝ) : EReal) ≤
      ⨆ c : Cyl, ((2 * ∫ z, f z * (-(c.gen lam' Y z)) ∂γ : ℝ) : EReal) -
        (c.form lam' γ : EReal) := by
  haveI := hγ.1
  obtain ⟨c, -, hform, hint⟩ :=
    exists_core_seq hγ hPSD hC hY hξ hW hLξ hΞ hmap F (hcoef ξ γ f)
  have h1 := hint f hf
  have e : ∑ α ∈ F, hcoef ξ γ f α * kappa ν α * ∫ z, f z * Hxi ξ α z ∂γ =
      ∑ α ∈ F, kappa ν α * hcoef ξ γ f α ^ 2 := Finset.sum_congr rfl fun α _ => by
    have : ∫ z, f z * Hxi ξ α z ∂γ = hcoef ξ γ f α := by
      unfold hcoef; congr 1; funext z; ring
    rw [this]; ring
  rw [e] at h1
  have hlim : Tendsto (fun n => 2 * ∫ z, f z * (-(c n).gen lam' Y z) ∂γ - (c n).formR lam' γ)
      atTop (𝓝 (∑ α ∈ F, kappa ν α * hcoef ξ γ f α ^ 2)) := by
    have := (h1.const_mul 2).sub hform
    simpa [two_mul] using this
  refine le_of_tendsto' (EReal.tendsto_coe.2 hlim) fun n => ?_
  have hterm : (((2 * ∫ z, f z * (-((c n).gen lam' Y z)) ∂γ : ℝ)) : EReal) -
      ((c n).form lam' γ : EReal) =
      ((2 * ∫ z, f z * (-((c n).gen lam' Y z)) ∂γ - (c n).formR lam' γ : ℝ) : EReal) := by
    rw [Cyl.form_eq_ofReal hlam, EReal.coe_ennreal_ofReal,
      max_eq_left (formR_nonneg' hlam (c n)), EReal.coe_sub]
  rw [← hterm]
  exact le_iSup (fun c : Cyl => ((2 * ∫ z, f z * (-(c.gen lam' Y z)) ∂γ : ℝ) : EReal) -
    (c.form lam' γ : EReal)) (c n)

include hν in
/-- `Q(f) ≤ sup_c (2∫f(-Lc) - ℰ(c))`. -/
theorem formQ_le_sup {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ) :
    (formQ ν ξ γ f : EReal) ≤
      ⨆ c : Cyl, ((2 * ∫ z, f z * (-(c.gen lam' Y z)) ∂γ : ℝ) : EReal) -
        (c.form lam' γ : EReal) := by
  set S := ⨆ c : Cyl, ((2 * ∫ z, f z * (-(c.gen lam' Y z)) ∂γ : ℝ) : EReal) -
    (c.form lam' γ : EReal)
  have h0 : (0 : EReal) ≤ S := by
    have := formQ_finset_le_sup hγ hPSD hC hY hlam hξ hW hLξ hΞ hmap hf ∅
    rwa [Finset.sum_empty, EReal.coe_zero] at this
  rw [← EReal.coe_toENNReal h0, EReal.coe_ennreal_le_coe_ennreal_iff]
  unfold formQ
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  have hnn : ∀ α ∈ F, 0 ≤ kappa ν α * hcoef ξ γ f α ^ 2 := fun α _ =>
    mul_nonneg (kappa_nonneg hν α) (sq_nonneg _)
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  have h := formQ_finset_le_sup hγ hPSD hC hY hlam hξ hW hLξ hΞ hmap hf F
  have hr := Finset.sum_nonneg hnn
  calc ENNReal.ofReal (∑ α ∈ F, kappa ν α * hcoef ξ γ f α ^ 2)
      = ((ENNReal.ofReal (∑ α ∈ F, kappa ν α * hcoef ξ γ f α ^ 2) : EReal)).toENNReal :=
        EReal.toENNReal_coe.symm
    _ ≤ S.toENNReal := by
        refine EReal.toENNReal_le_toENNReal ?_
        rw [EReal.coe_ennreal_ofReal, max_eq_left hr]
        exact h

include hν in
/-- `ℰ_∞(f) ≤ Q(f)`. -/
theorem gaussForm_le_formQ
    (hcomp : ∀ F : (ℕ → ℝ) → ℝ, MemLp F 2 γ →
      (∀ α : ℕ →₀ ℕ, ∫ z, F z * hermiteBasis α (fun j => ξ j z) ∂γ = 0) → F =ᵐ[γ] 0)
    {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ) :
    gaussForm lam' γ f ≤ formQ ν ξ γ f := by
  haveI := hγ.1
  set b := hxiBasis hΞ hmap hcomp
  set x := hf.toLp f
  obtain ⟨e, he⟩ := exists_surjective_nat (ℕ →₀ ℕ)
  set FM : ℕ → Finset (ℕ →₀ ℕ) := fun M => (Finset.range M).image e with hFM
  have hmono : Monotone FM := fun M M' h => Finset.image_subset_image (Finset.range_mono h)
  have hcov : ∀ α, ∃ M, α ∈ FM M := fun α => by
    obtain ⟨k, hk⟩ := he α
    exact ⟨k + 1, Finset.mem_image.2 ⟨k, by simp, hk⟩⟩
  have hrepr : ∀ α, b.repr x α = hcoef ξ γ f α := fun α => by
    rw [b.repr_apply_apply, hxiBasis_apply, inner_toLp_Hxi hΞ hmap hf α]; rfl
  have hsum : Tendsto (fun M => ∑ α ∈ FM M, hcoef ξ γ f α • b α) atTop (𝓝 x) := by
    have h : Tendsto (fun s : Finset (ℕ →₀ ℕ) => ∑ α ∈ s, b.repr x α • b α) atTop (𝓝 x) :=
      b.hasSum_repr x
    simp_rw [hrepr] at h
    exact h.comp (tendsto_atTop_finset_of_monotone hmono hcov)
  set P : ℕ → (ℕ → ℝ) → ℝ := fun M z => ∑ α ∈ FM M, hcoef ξ γ f α * Hxi ξ α z with hPdef
  have hb : ∀ α, ⇑(b α) =ᵐ[γ] Hxi ξ α := fun α => by
    rw [hxiBasis_apply]; exact (memLp_Hxi hΞ hmap α).coeFn_toLp
  have hP : Tendsto (fun M => eLpNorm (fun z => P M z - f z) 2 γ) atTop (𝓝 0) := by
    have e1 : ∀ M, eLpNorm (fun z => P M z - f z) 2 γ =
        ENNReal.ofReal ‖∑ α ∈ FM M, hcoef ξ γ f α • b α - x‖ := fun M => by
      have hae : (fun z => P M z - f z) =ᵐ[γ] ⇑(∑ α ∈ FM M, hcoef ξ γ f α • b α - x) := by
        filter_upwards [Lp.coeFn_sub (∑ α ∈ FM M, hcoef ξ γ f α • b α) x,
          coeFn_finset_sum_smul (FM M) (hcoef ξ γ f) b,
          (eventually_all_finset (FM M)).2 fun α _ => hb α, hf.coeFn_toLp] with z h1 h2 h3 h4
        rw [h1, Pi.sub_apply, h2, h4]
        exact congrArg (· - f z) (Finset.sum_congr rfl fun α hα => by rw [h3 α hα])
      rw [eLpNorm_congr_ae hae, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    simp_rw [e1]
    have := ENNReal.tendsto_ofReal ((tendsto_iff_norm_sub_tendsto_zero).1 hsum)
    simpa using this
  have hPM : ∀ M, gaussForm lam' γ (P M) ≤ formQ ν ξ γ f := fun M => by
    obtain ⟨c, h1, hform, -⟩ :=
      exists_core_seq hγ hPSD hC hY hξ hW hLξ hΞ hmap (FM M) (hcoef ξ γ f)
    have hlim : Tendsto (fun n => (c n).form lam' γ) atTop
        (𝓝 (ENNReal.ofReal (∑ α ∈ FM M, kappa ν α * hcoef ξ γ f α ^ 2))) := by
      simp_rw [Cyl.form_eq_ofReal hlam]
      exact ENNReal.tendsto_ofReal hform
    refine (gaussForm_le_liminf c h1).trans ?_
    rw [hlim.liminf_eq, ENNReal.ofReal_sum_of_nonneg fun α _ =>
      mul_nonneg (kappa_nonneg hν α) (sq_nonneg _)]
    exact ENNReal.sum_le_tsum _
  calc gaussForm lam' γ f ≤ liminf (fun M => gaussForm lam' γ (P M)) atTop :=
        gaussForm_le_liminf_of_L2 hP
    _ ≤ formQ ν ξ γ f := liminf_le_of_frequently_le' (Frequently.of_forall hPM)

include hν in
/-- **The hard direction of (8.8)**, generic form. -/
theorem gaussForm_le_sup_generic
    (hcomp : ∀ F : (ℕ → ℝ) → ℝ, MemLp F 2 γ →
      (∀ α : ℕ →₀ ℕ, ∫ z, F z * hermiteBasis α (fun j => ξ j z) ∂γ = 0) → F =ᵐ[γ] 0)
    {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ) :
    (gaussForm lam' γ f : EReal) ≤
      ⨆ c : Cyl, ((2 * ∫ z, f z * (-(c.gen lam' Y z)) ∂γ : ℝ) : EReal) -
        (c.form lam' γ : EReal) :=
  (EReal.coe_ennreal_le_coe_ennreal_iff.2
    (gaussForm_le_formQ hγ hPSD hC hY hlam hν hξ hW hLξ hΞ hmap hcomp hf)).trans
    (formQ_le_sup hγ hPSD hC hY hlam hν hξ hW hLξ hΞ hmap hf)

include hν in
/-- **(8.8), generic form.** -/
theorem form_duality_generic
    (hcomp : ∀ F : (ℕ → ℝ) → ℝ, MemLp F 2 γ →
      (∀ α : ℕ →₀ ℕ, ∫ z, F z * hermiteBasis α (fun j => ξ j z) ∂γ = 0) → F =ᵐ[γ] 0)
    {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ) :
    (gaussForm lam' γ f : EReal) =
      ⨆ c : Cyl, ((2 * ∫ z, f z * (-(c.gen lam' Y z)) ∂γ : ℝ) : EReal) -
        (c.form lam' γ : EReal) :=
  le_antisymm (gaussForm_le_sup_generic hγ hPSD hC hY hlam hν hξ hW hLξ hΞ hmap hcomp hf)
    (sup_le_gaussForm hγ hPSD hC hY hlam hf)

end main

/-! ### The paper version -/

/-- Partial sums of `∑_i λ'_i v_{ji} v_{ki}` from square-summability. -/
theorem tendsto_partial_lam_vv {lam' : ℕ → ℝ} {v : ℕ → ℕ → ℝ} {j k : ℕ}
    (hj : Summable fun i => (lam' i * v j i) ^ 2) (hk : Summable fun i => v k i ^ 2) :
    Tendsto (fun N => ∑ i ∈ Finset.range N, lam' i * v j i * v k i) atTop
      (𝓝 (∑' i, lam' i * v j i * v k i)) := by
  have hs : Summable fun i => lam' i * v j i * v k i := by
    refine Summable.of_norm_bounded ((hj.add hk).div_const 2) fun i => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have := two_mul_le_add_sq |lam' i * v j i| |v k i|
    rw [sq_abs, sq_abs] at this
    show _ ≤ ((lam' i * v j i) ^ 2 + v k i ^ 2) / 2
    linarith
  exact hs.hasSum.tendsto_sum_nat

section paper
variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **(8.8) form duality, conditional on Prop. 2.1.** -/
theorem form_duality_of_prop21 (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) (h21 : Prop21Conclusion V W μ)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable (Tmat W μ e) γ i (Y i))
    {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ) :
    (gaussForm (lamShift lam) γ f : EReal) =
      ⨆ c : Cyl, ((2 * ∫ z, f z * (-(c.gen (lamShift lam) Y z)) ∂γ : ℝ) : EReal) -
        (c.form (lamShift lam) γ : EReal) := by
  obtain ⟨v, ν, ξ, hv, hvC, hvΛ, hν0, hmono, -, hξ, -, -, hP⟩ :=
    genXi_of_prop21 hyp hμ he h21 hC hγ
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  have hT := Tmat_symm hyp hμ he
  have hS := (hasSum_Tmat_sq hyp hμ he).summable
  have hCs := C_symm_of_secOp hT hS hσ0 hσ hC
  have hΞ : AEMeasurable (fun z j => ξ j z) γ :=
    aemeasurable_pi_iff.2 fun j => (hξ j).1.aestronglyMeasurable.aemeasurable
  have hmap := map_xi_eq_gammaRef hT hS hσ0 hσ hC hCs hγ (fun j => (hv j).1) hvC hξ
  have hcomp : ∀ F : (ℕ → ℝ) → ℝ, MemLp F 2 γ →
      (∀ α : ℕ →₀ ℕ, ∫ z, F z * hermiteBasis α (fun j => ξ j z) ∂γ = 0) → F =ᵐ[γ] 0 :=
    fun F hF horth => hermite_complete_xi hT hS hσ0 hσ hC hCs hγ (fun j => (hv j).1) hvC hξ hP hF
      horth
  have hW : ∀ j k, Tendsto (fun N => ∑ i ∈ Finset.range N, lamShift lam i * v j i * v k i) atTop
      (𝓝 (if j = k then ν j else 0)) := fun j k => by
    rw [← hvΛ j k]; exact tendsto_partial_lam_vv (hv j).2 (hv k).1
  have hLξ := gen_xi_of_prop21 hyp hμ he h21 hC hγ hv hvC hvΛ hξ hP hY
  have hν : ∀ j, 0 ≤ ν j := fun j => hν0.le.trans (hmono (Nat.zero_le j))
  exact form_duality_generic hγ (blockMat_posSemidef_of_prop21 hyp hμ he h21 hC) hC hY
    (fun i => he.lam_nonneg' (i + 1)) hν hξ hW hLξ hΞ hmap hcomp hf

end paper

end SharpLSI
