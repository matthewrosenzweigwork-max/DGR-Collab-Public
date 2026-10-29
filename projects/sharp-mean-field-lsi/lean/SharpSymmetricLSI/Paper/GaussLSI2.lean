import SharpSymmetricLSI.Paper.GaussLSI1

/-!
# (8.10), LSI half (lane s42): `Ent_γ(f²) ≤ (2/λ_G) ℰ_∞(f)` on `L²(γ)`

* `ent_sq_le_liminf`: `f ↦ Ent_γ(f²)` is lower semicontinuous under `L²(γ)` convergence. `ent` is
  the lintegral `∫ c klFun(f²/c)` with `c = ∫ f²` (Infra/Entropy), so Fatou applies along an
  a.e.-convergent subsequence; `c = 0` gives `Ent = 0`.
* `gaussian_lsi_relax`: the LSI for `γ_∞` on `L²(γ)` (relaxation of `gaussForm`).
* `gaussian_lsi_poincare_of_prop21`: the conjunction `0 < λ_G ∧ λ_G < ∞ ∧ (LSI ∧ Poincaré)` for the
  concrete objects of Sections 6 and 8.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset InformationTheory
open scoped ENNReal ContDiff MatrixOrder

namespace SharpLSI

section lsc
variable {γ : Measure (ℕ → ℝ)} [IsProbabilityMeasure γ]

theorem ent_sq_eq {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ) :
    ent γ (fun x => f x ^ 2) = ∫⁻ x, ENNReal.ofReal ((∫ y, f y ^ 2 ∂γ) *
      klFun (f x ^ 2 / ∫ y, f y ^ 2 ∂γ)) ∂γ := by
  unfold ent; rw [if_pos hf.integrable_sq]

/-- Fatou for the entropy along an a.e.-convergent sequence with converging second moments. -/
theorem ent_sq_le_liminf_of_ae {u : ℕ → (ℕ → ℝ) → ℝ} {f : (ℕ → ℝ) → ℝ}
    (hu : ∀ n, MemLp (u n) 2 γ) (hf : MemLp f 2 γ)
    (hc : Tendsto (fun n => ∫ x, u n x ^ 2 ∂γ) atTop (𝓝 (∫ x, f x ^ 2 ∂γ)))
    (hae : ∀ᵐ x ∂γ, Tendsto (fun n => u n x) atTop (𝓝 (f x))) :
    ent γ (fun x => f x ^ 2) ≤ liminf (fun n => ent γ (fun x => u n x ^ 2)) atTop := by
  set c := ∫ x, f x ^ 2 ∂γ
  rcases (integral_nonneg (fun x => sq_nonneg (f x)) : 0 ≤ c).eq_or_lt with h0 | hpos
  · rw [ent_sq_eq hf, ← h0]; simp
  rw [ent_sq_eq hf]
  simp_rw [ent_sq_eq (hu _)]
  have hmeas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal ((∫ y, u n y ^ 2 ∂γ) *
      klFun (u n x ^ 2 / ∫ y, u n y ^ 2 ∂γ))) γ := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuous_const.mul (continuous_klFun.comp ((continuous_pow 2).div_const _))).comp_aestronglyMeasurable
        (hu n).aestronglyMeasurable).aemeasurable
  refine le_trans ?_ (lintegral_liminf_le' hmeas)
  refine lintegral_mono_ae ?_
  filter_upwards [hae] with x hx
  have hlim : Tendsto (fun n => ENNReal.ofReal ((∫ y, u n y ^ 2 ∂γ) *
      klFun (u n x ^ 2 / ∫ y, u n y ^ 2 ∂γ))) atTop (𝓝 (ENNReal.ofReal (c * klFun (f x ^ 2 / c)))) :=
    ENNReal.tendsto_ofReal (hc.mul ((continuous_klFun.tendsto _).comp ((hx.pow 2).div hc hpos.ne')))
  rw [hlim.liminf_eq]

/-- **Lower semicontinuity of `f ↦ Ent_γ(f²)` in `L²(γ)`.** -/
theorem ent_sq_le_liminf {u : ℕ → (ℕ → ℝ) → ℝ} {f : (ℕ → ℝ) → ℝ}
    (hu : ∀ n, MemLp (u n) 2 γ) (hf : MemLp f 2 γ)
    (hconv : Tendsto (fun n => eLpNorm (fun x => u n x - f x) 2 γ) atTop (𝓝 0)) :
    ent γ (fun x => f x ^ 2) ≤ liminf (fun n => ent γ (fun x => u n x ^ 2)) atTop := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨a, hLa, haE⟩ := exists_between hcon
  have hfreq : ∃ᶠ n in atTop, ent γ (fun x => u n x ^ 2) < a :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hLa
  obtain ⟨φ, hφ, hφa⟩ := extraction_of_frequently_atTop hfreq
  have hconvφ : Tendsto (fun n => eLpNorm (fun x => u (φ n) x - f x) 2 γ) atTop (𝓝 0) :=
    hconv.comp hφ.tendsto_atTop
  obtain ⟨ψ, hψ, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (f := fun n => u (φ n)) (g := f) (by norm_num)
      hconvφ).exists_seq_tendsto_ae
  -- second moments converge
  have hL : Tendsto (fun n => (hu (φ (ψ n))).toLp (u (φ (ψ n)))) atTop (𝓝 (hf.toLp f)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => u (φ (ψ n))) (fun n => hu (φ (ψ n))) f hf).2
      (hconvφ.comp hψ.tendsto_atTop)
  have hsq : ∀ {g : (ℕ → ℝ) → ℝ} (hg : MemLp g 2 γ),
      ∫ x, g x ^ 2 ∂γ = @inner ℝ _ _ (hg.toLp g) (hg.toLp g) := fun {g} hg => by
    rw [L2_inner_eq_integral_gen]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx, sq]
  have hc : Tendsto (fun n => ∫ x, u (φ (ψ n)) x ^ 2 ∂γ) atTop (𝓝 (∫ x, f x ^ 2 ∂γ)) := by
    rw [hsq hf]
    refine (((continuous_id.inner continuous_id).tendsto _).comp hL).congr fun n => ?_
    exact (hsq (hu (φ (ψ n)))).symm
  have h1 := ent_sq_le_liminf_of_ae (fun n => hu (φ (ψ n))) hf hc hae
  have h2 : liminf (fun n => ent γ (fun x => u (φ (ψ n)) x ^ 2)) atTop ≤ a :=
    liminf_le_of_frequently_le' (Frequently.of_forall fun n => (hφa (ψ n)).le)
  exact absurd (h1.trans h2) (not_le.mpr haE)

end lsc

section relax
variable {γ : Measure (ℕ → ℝ)} {C : ℕ → ℕ → ℝ} (hγ : IsCenteredGaussianCov γ C)
  (hS : ∀ N, (blockMat C N).PosSemidef)
  (hnn : ∀ (s : Finset ℕ) (v : ℕ → ℝ), 0 ≤ ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j)
  {lam' : ℕ → ℝ}
include hγ hS hnn

/-- **The Gaussian LSI for `γ_∞`** on `L²(γ)`. -/
theorem gaussian_lsi_relax (hpos : 0 < lamG lam' C) (htop : lamG lam' C < ⊤) :
    ∀ f : (ℕ → ℝ) → ℝ, MemLp f 2 γ →
      ent γ (fun z => f z ^ 2) ≤ 2 / lamG lam' C * gaussForm lam' γ f := by
  have := hγ.1
  intro f hf
  set k := lamG lam' C * 2⁻¹
  have hk : k ≠ ⊤ := ENNReal.mul_ne_top htop.ne (by simp)
  have h2 : ent γ (fun z => f z ^ 2) * k ≤ gaussForm lam' γ f := by
    unfold gaussForm
    refine le_iInf₂ fun u hu => ?_
    have hlsc := ent_sq_le_liminf (fun n => memLp_cyl hγ (u n)) hf hu
    have hmono : Monotone fun x : ℝ≥0∞ => x * k := fun a b h => by dsimp only; gcongr
    calc ent γ (fun z => f z ^ 2) * k
        ≤ liminf (fun n => ent γ (fun z => (u n).eval z ^ 2)) atTop * k := by gcongr
      _ = liminf (fun n => ent γ (fun z => (u n).eval z ^ 2) * k) atTop :=
          hmono.map_liminf_of_continuousAt _ (ENNReal.continuous_mul_const hk).continuousAt
      _ ≤ liminf (fun n => (u n).form lam' γ) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
          have h := ent_mul_lamG_le_form hγ hS hnn (lam' := lam') (u n)
          calc ent γ (fun z => (u n).eval z ^ 2) * k
              = ent γ (fun z => (u n).eval z ^ 2) * lamG lam' C * 2⁻¹ := (mul_assoc _ _ _).symm
            _ ≤ 2 * (u n).form lam' γ * 2⁻¹ := by gcongr
            _ = (u n).form lam' γ := by
                rw [mul_comm 2, mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by simp), mul_one]
  have key : ent γ (fun z => f z ^ 2) * lamG lam' C ≤ 2 * gaussForm lam' γ f := by
    calc ent γ (fun z => f z ^ 2) * lamG lam' C
        = ent γ (fun z => f z ^ 2) * k * 2 := by
          rw [mul_assoc, mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by simp), mul_one]
      _ ≤ gaussForm lam' γ f * 2 := by gcongr
      _ = 2 * gaussForm lam' γ f := mul_comm _ _
  rw [show 2 / lamG lam' C * gaussForm lam' γ f = 2 * gaussForm lam' γ f / lamG lam' C by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl htop.ne)).2 key

end relax

section main
variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **(8.9)–(8.10)** for the concrete `γ_∞`, `ℰ_∞`, `λ_G`: `0 < λ_G < ∞`, the Gaussian LSI and
the Gaussian Poincaré inequality. -/
theorem gaussian_lsi_poincare_of_prop21 (hd : 1 ≤ d) (hyp : Hyp V W KV KW)
    (hr : 0 < rStar V W) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C) :
    0 < lamG (lamShift lam) C ∧ lamG (lamShift lam) C < ⊤ ∧
    (∀ f : (ℕ → ℝ) → ℝ, MemLp f 2 γ →
      ent γ (fun z => f z ^ 2) ≤ 2 / lamG (lamShift lam) C * gaussForm (lamShift lam) γ f ∧
      var γ f ≤ gaussForm (lamShift lam) γ f / lamG (lamShift lam) C) := by
  have h21 := prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  have hT := Tmat_symm hyp hμ he
  have hS' := (hasSum_Tmat_sq hyp hμ he).summable
  have hCs : ∀ i j, C i j = C j i := fun i j => C_symm_of_secOp hT hS' hσ0 hσ hC i j
  have hnn := quadC_nonneg hT hS' hσ0 hσ hC
  have hup := quadC_le hT hS' hσ0 hσ hC
  have hcol : ∀ j, Summable fun k => C k j ^ 2 := fun j => (hC j).1
  have hlam0 : 0 < lamShift lam 0 := ((ref_spectrum hd hyp hr hμ).2 e lam he).1 1 le_rfl
  have hmono : ∀ i, lamShift lam 0 ≤ lamShift lam i := fun i =>
    he.mono (by simp [lamShift] : 0 + 1 ≤ i + 1)
  have hS : ∀ N, (blockMat C N).PosSemidef := fun N =>
    blockMat_posSemidef_of_prop21 hyp hμ he h21 hC N
  have hpos := lamG_pos hσ0 hCs hnn hup hcol hlam0 hmono
  have htop := lamG_lt_top hCs hnn hC (lamShift lam)
  exact ⟨hpos, htop, fun f hf => ⟨gaussian_lsi_relax hγ hS hnn hpos htop f hf,
    gaussian_poincare hγ hS hnn hpos htop f hf⟩⟩

end main

end SharpLSI
