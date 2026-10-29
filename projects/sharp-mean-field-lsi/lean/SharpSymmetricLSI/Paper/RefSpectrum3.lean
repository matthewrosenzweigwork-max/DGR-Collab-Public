import SharpSymmetricLSI.Paper.EnergyParseval3
import SharpSymmetricLSI.Paper.Moser4
import SharpSymmetricLSI.Paper.FourierSynth
import SharpSymmetricLSI.Paper.R37Particle
import SharpSymmetricLSI.Paper.ELEquation
import SharpSymmetricLSI.Paper.EnergyParseval2

/-!
# R23 (6.1), part 3: constrained Rayleigh minimizers (existence of the eigenbasis)

`P = ρ m` with `c ≤ ρ ≤ C`. For a family `e` and `n`, `Adm P e n` is the set of `u ∈ H¹(P)` with
`∫u² dP = 1` and `u ⊥ e₀, …, eₙ`. If it is nonempty, the Dirichlet energy `D(u) = ∫|∇u|² dP` attains
its infimum on it (`exists_min`): a minimizing sequence is bounded in `H¹(m)`, `rellich_torus`
gives `L²(m)`-convergence and weak convergence of the gradients, the constraints pass to the limit
in `L²(P)`, and `D` is weakly lower semicontinuous.
-/

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace SharpLSI

variable {d : ℕ}

/-- The Dirichlet energy `∫ |∇u|² dP` (real-valued). -/
noncomputable def dirE (P : Measure (Torus d)) (u : Torus d → ℝ) : ℝ :=
  ∫ x, ∑ k, weakGrad u x k ^ 2 ∂P

/-- The admissible set of the `(n+1)`-st Rayleigh problem. -/
def Adm (P : Measure (Torus d)) (e : ℕ → Torus d → ℝ) (n : ℕ) : Set (Torus d → ℝ) :=
  {u | MemH1 P u ∧ ∫ x, u x ^ 2 ∂P = 1 ∧ ∀ i ≤ n, ∫ x, u x * e i x ∂P = 0}

/-- The standing assumptions on the reference measure. -/
structure GoodDens (ρ : Torus d → ℝ) (c C : ℝ) : Prop where
  meas : Measurable ρ
  pos : 0 < c
  lower : ∀ x, c ≤ ρ x
  upper : ∀ x, ρ x ≤ C
  one : ∫ x, ρ x ∂haar d = 1

namespace GoodDens

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C)
include hρ

theorem nonneg (x : Torus d) : 0 ≤ ρ x := hρ.pos.le.trans (hρ.lower x)

theorem C_pos : 0 < C := hρ.pos.trans_le ((hρ.lower 0).trans (hρ.upper 0))

theorem isProb : IsProbabilityMeasure (densMeasure ρ) :=
  isProbabilityMeasure_densMeasure' hρ.nonneg hρ.one

theorem integral_eq (F : Torus d → ℝ) : ∫ x, F x ∂densMeasure ρ = ∫ x, ρ x * F x ∂haar d :=
  integral_densMeasure' hρ.nonneg hρ.one F

theorem le_smul : densMeasure ρ ≤ ENNReal.ofReal C • haar d := by
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul, densMeasure, withDensity_apply _ hs, ← setLIntegral_const]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hρ.upper x)

theorem haar_le_smul : haar d ≤ ENNReal.ofReal (1 / c) • densMeasure ρ := by
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul, densMeasure, withDensity_apply _ hs]
  calc haar d s = ENNReal.ofReal (1 / c) * (ENNReal.ofReal c * haar d s) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by have := hρ.pos; positivity),
          one_div_mul_cancel hρ.pos.ne', ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (1 / c) * ∫⁻ x in s, ENNReal.ofReal (ρ x) ∂haar d := by
        gcongr
        rw [← setLIntegral_const]
        exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hρ.lower x)

theorem ac : densMeasure ρ ≪ haar d := Measure.absolutelyContinuous_of_le_smul hρ.le_smul

theorem ac' : haar d ≪ densMeasure ρ := Measure.absolutelyContinuous_of_le_smul hρ.haar_le_smul

end GoodDens

section minimizer

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C)
include hρ

theorem dirE_nonneg (u : Torus d → ℝ) : 0 ≤ dirE (densMeasure ρ) u :=
  integral_nonneg fun x => Finset.sum_nonneg fun k _ => sq_nonneg _

theorem memLp_sqrt_sqNorm_of {G : Torus d → Fin d → ℝ} {P : Measure (Torus d)}
    (hG : ∀ j, MemLp (fun x => G x j) 2 P) :
    MemLp (fun x => Real.sqrt (sqNorm (G x))) 2 P := by
  have hs : MemLp (fun x => ∑ j, |G x j|) 2 P := memLp_finset_sum _ fun j _ => (hG j).abs
  refine hs.of_le ?_ (Eventually.of_forall fun x => ?_)
  · unfold sqNorm
    exact Real.continuous_sqrt.comp_aestronglyMeasurable
      (Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hG j).aestronglyMeasurable.pow 2)
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
    refine Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
    unfold sqNorm
    calc ∑ j, G x j ^ 2 = ∑ j, |G x j| ^ 2 := by simp_rw [sq_abs]
      _ ≤ (∑ j, |G x j|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => abs_nonneg _

/-- **Existence of a constrained minimizer.** -/
theorem exists_min {e : ℕ → Torus d → ℝ} {n : ℕ}
    (he : ∀ i ≤ n, MemLp (e i) 2 (densMeasure ρ)) (hne : (Adm (densMeasure ρ) e n).Nonempty) :
    ∃ f ∈ Adm (densMeasure ρ) e n, ∀ u ∈ Adm (densMeasure ρ) e n,
      dirE (densMeasure ρ) f ≤ dirE (densMeasure ρ) u := by
  set P := densMeasure ρ with hP
  haveI := hρ.isProb
  have ha := hρ.haar_le_smul
  have hb := hρ.le_smul
  set S := dirE P '' Adm P e n
  have hSne : S.Nonempty := hne.image _
  have hSbdd : BddBelow S := ⟨0, by rintro _ ⟨u, -, rfl⟩; exact dirE_nonneg hρ u⟩
  set L := sInf S
  have hmin : ∀ m : ℕ, ∃ u ∈ Adm P e n, dirE P u < L + 1 / (m + 1) := by
    intro m
    obtain ⟨_, ⟨u, hu, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hSne
      (lt_add_of_pos_right L (by positivity : (0 : ℝ) < 1 / (m + 1)))
    exact ⟨u, hu, hlt⟩
  choose u hu hlt using hmin
  have hLe : ∀ m, L ≤ dirE P (u m) := fun m => csInf_le hSbdd ⟨u m, hu m, rfl⟩
  have hL0 : 0 ≤ L := le_csInf hSne (by rintro _ ⟨v, -, rfl⟩; exact dirE_nonneg hρ v)
  have hH1 : ∀ m, MemH1 P (u m) := fun m => (hu m).1
  have hw : ∀ m, IsWeakGrad (u m) (weakGrad (u m)) := fun m => isWeakGrad_weakGrad (hH1 m).1
  have huv : ∀ m, MemLp (u m) 2 volume := fun m => memLp_vol ha (hH1 m)
  have hgv : ∀ m j, MemLp (fun y => weakGrad (u m) y j) 2 volume :=
    fun m j => memLp_grad_vol ha hb (hH1 m) j
  have hgP : ∀ m j, MemLp (fun y => weakGrad (u m) y j) 2 P := fun m j => memLp_grad_P hb (hH1 m) j
  -- uniform `H¹(m)` bound
  have hc0 : 0 ≤ 1 / c := by have := hρ.pos; positivity
  have hB : ∀ m, (∫ y, u m y ^ 2) + ∑ j, ∫ y, weakGrad (u m) y j ^ 2 ≤
      1 / c + 1 / c * (L + 1) := by
    intro m
    have h1 : ∫ y, u m y ^ 2 ≤ 1 / c * ∫ y, u m y ^ 2 ∂P :=
      integral_le_smul_of_le hc0 ha (fun _ => sq_nonneg _) (hH1 m).2.1.integrable_sq
    have h2 : ∑ j, ∫ y, weakGrad (u m) y j ^ 2 ≤ 1 / c * dirE P (u m) := by
      rw [dirE, integral_finsetSum _ fun j _ => (hgP m j).integrable_sq, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ =>
        integral_le_smul_of_le hc0 ha (fun _ => sq_nonneg _) (hgP m j).integrable_sq
    have h3 : dirE P (u m) ≤ L + 1 := (hlt m).le.trans (by
      have : (1 : ℝ) / (m + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      linarith)
    rw [(hu m).2.1] at h1
    nlinarith [mul_le_mul_of_nonneg_left h3 hc0]
  obtain ⟨φ, hφ, f, G, hf2, hG2, hfG, hconv, hweak⟩ :=
    rellich_torus hw huv hgv hB
  have hC0 : 0 ≤ C := hρ.C_pos.le
  have hfP : MemLp f 2 P := hf2.of_measure_le_smul ENNReal.ofReal_ne_top hb
  have huP : ∀ m, MemLp (u m) 2 P := fun m => (hH1 m).2.1
  have hconvP : Tendsto (fun m => ∫ y, (u (φ m) y - f y) ^ 2 ∂P) atTop (𝓝 0) := by
    refine squeeze_zero (fun m => integral_nonneg fun _ => sq_nonneg _) (fun m =>
      integral_le_smul_of_le hC0 hb (fun _ => sq_nonneg _)
        ((huv (φ m)).sub hf2).integrable_sq) ?_
    simpa using hconv.const_mul C
  set X : ℕ → Lp ℝ 2 P := fun m => (huP (φ m)).toLp
  set Y : Lp ℝ 2 P := hfP.toLp
  have hXY : Tendsto X atTop (𝓝 Y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have e : ∀ m, ‖X m - Y‖ = Real.sqrt (∫ y, (u (φ m) y - f y) ^ 2 ∂P) := fun m => by
      rw [← norm_toLp_sub_sq (huP (φ m)) hfP, Real.sqrt_sq (norm_nonneg _)]
    simp_rw [e]
    have := (Real.continuous_sqrt.tendsto 0).comp hconvP
    rw [Real.sqrt_zero] at this
    exact this
  -- the constraints pass to the limit
  have hnorm : ∫ y, f y ^ 2 ∂P = 1 := by
    have hc := Filter.Tendsto.inner (𝕜 := ℝ) hXY hXY
    have e1 : ∀ m, ⟪X m, X m⟫ = 1 := fun m => by
      rw [inner_toLp]
      have := (hu (φ m)).2.1
      simp_rw [sq] at this
      exact this
    have e2 : ⟪Y, Y⟫ = ∫ y, f y ^ 2 ∂P := by
      rw [inner_toLp]; congr 1; funext y; ring
    simp_rw [e1] at hc
    rw [← e2]; exact tendsto_nhds_unique tendsto_const_nhds hc |>.symm
  have horth : ∀ i ≤ n, ∫ y, f y * e i y ∂P = 0 := by
    intro i hi
    have hc := Filter.Tendsto.inner (𝕜 := ℝ) hXY (tendsto_const_nhds (x := (he i hi).toLp))
    have e1 : ∀ m, ⟪X m, (he i hi).toLp⟫ = 0 := fun m => by
      rw [inner_toLp]; exact (hu (φ m)).2.2 i hi
    simp_rw [e1] at hc
    rw [← inner_toLp hfP (he i hi)]
    exact (tendsto_nhds_unique tendsto_const_nhds hc).symm
  -- `f ∈ H¹(P)`
  have hGP : ∀ j, MemLp (fun y => G y j) 2 P := fun j =>
    (hG2 j).of_measure_le_smul ENNReal.ofReal_ne_top hb
  have hwf : HasWeakGrad f := ⟨G, hfG⟩
  have hgae : weakGrad f =ᵐ[volume] G := weakGrad_ae_unique (isWeakGrad_weakGrad hwf) hfG
  have hgaeP : weakGrad f =ᵐ[P] G := hρ.ac.ae_le hgae
  have hwfP : ∀ j, MemLp (fun y => weakGrad f y j) 2 P := fun j =>
    (hGP j).ae_eq (hgaeP.mono fun y hy => by show G y j = weakGrad f y j; rw [hy])
  have hH1f : MemH1 P f := ⟨hwf, hfP, memLp_sqrt_sqNorm_of hρ hwfP⟩
  -- weak lower semicontinuity
  set Df := ∑ j, ∫ y, G y j ^ 2 ∂P
  have hDf : dirE P f = Df := by
    show _ = ∑ j, ∫ y, G y j ^ 2 ∂P
    rw [dirE, ← integral_finsetSum _ fun j _ => (hGP j).integrable_sq]
    refine integral_congr_ae (hgaeP.mono fun y hy => ?_)
    simp only [hy]
  have hA : Tendsto (fun m => ∑ j, ∫ y, weakGrad (u (φ m)) y j * G y j ∂P) atTop (𝓝 Df) := by
    refine tendsto_finset_sum _ fun j _ => ?_
    have hρG : MemLp (fun y => ρ y * G y j) 2 volume :=
      (hG2 j).const_mul C |>.of_le ((hρ.meas.aestronglyMeasurable).mul (hG2 j).aestronglyMeasurable)
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hρ.nonneg y),
            abs_of_nonneg hC0]
          exact mul_le_mul_of_nonneg_right (hρ.upper y) (abs_nonneg _))
    have h := hweak j _ hρG
    have e : ∀ v : Torus d → ℝ, ∫ y, v y * (ρ y * G y j) = ∫ y, v y * G y j ∂P := fun v => by
      rw [hρ.integral_eq]; congr 1; funext y; ring
    simp_rw [e] at h
    convert h using 2
    congr 1; funext y; ring
  have hDu : Tendsto (fun m => dirE P (u (φ m))) atTop (𝓝 L) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun m => hLe _)
      (fun m => (hlt (φ m)).le)
    have h0 : Tendsto (fun m : ℕ => (1 : ℝ) / ((φ m : ℝ) + 1)) atTop (𝓝 0) := by
      exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    simpa using tendsto_const_nhds.add h0
  have hbound : ∀ m, ∑ j, ∫ y, weakGrad (u (φ m)) y j * G y j ∂P ≤
      (dirE P (u (φ m)) + Df) / 2 := by
    intro m
    have hj : ∀ j, ∫ y, weakGrad (u (φ m)) y j * G y j ∂P ≤
        (∫ y, weakGrad (u (φ m)) y j ^ 2 ∂P + ∫ y, G y j ^ 2 ∂P) / 2 := by
      intro j
      rw [← integral_add (hgP (φ m) j).integrable_sq (hGP j).integrable_sq, ← integral_div]
      refine integral_mono (by exact (hgP (φ m) j).integrable_mul (hGP j))
        (((hgP (φ m) j).integrable_sq.add (hGP j).integrable_sq).div_const 2) fun y => ?_
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (weakGrad (u (φ m)) y j - G y j)]
    calc ∑ j, ∫ y, weakGrad (u (φ m)) y j * G y j ∂P
        ≤ ∑ j, (∫ y, weakGrad (u (φ m)) y j ^ 2 ∂P + ∫ y, G y j ^ 2 ∂P) / 2 :=
          Finset.sum_le_sum fun j _ => hj j
      _ = (dirE P (u (φ m)) + Df) / 2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, dirE,
            integral_finsetSum _ fun j _ => (hgP (φ m) j).integrable_sq]
  have hDfL : Df ≤ L := by
    have := le_of_tendsto_of_tendsto' hA ((hDu.add tendsto_const_nhds).div_const 2) hbound
    linarith
  refine ⟨f, ⟨hH1f, hnorm, horth⟩, fun v hv => ?_⟩
  rw [hDf]
  exact hDfL.trans (csInf_le hSbdd ⟨v, hv, rfl⟩)

/-- The Dirichlet pairing `∫ ∇u·∇v dP`. -/
noncomputable def dirB (P : Measure (Torus d)) (u v : Torus d → ℝ) : ℝ :=
  ∫ x, ∑ k, weakGrad u x k * weakGrad v x k ∂P

theorem gradP {u : Torus d → ℝ} (hu : MemH1 (densMeasure ρ) u) (k : Fin d) :
    MemLp (fun x => weakGrad u x k) 2 (densMeasure ρ) := by
  haveI := hρ.isProb
  exact memLp_grad_comp hρ.ac hu k

theorem integrable_dirB_integrand {u v : Torus d → ℝ} (hu : MemH1 (densMeasure ρ) u)
    (hv : MemH1 (densMeasure ρ) v) :
    Integrable (fun x => ∑ k, weakGrad u x k * weakGrad v x k) (densMeasure ρ) := by
  haveI := hρ.isProb
  exact integrable_finset_sum _ fun k _ => (gradP hρ hu k).integrable_mul (gradP hρ hv k)

theorem dirE_eq_dirB (u : Torus d → ℝ) : dirE (densMeasure ρ) u = dirB (densMeasure ρ) u u := by
  unfold dirE dirB; congr 1; funext x; exact Finset.sum_congr rfl fun k _ => sq _

theorem dirB_comm (u v : Torus d → ℝ) : dirB (densMeasure ρ) u v = dirB (densMeasure ρ) v u := by
  unfold dirB; congr 1; funext x; exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- Linear combinations in `H¹(P)` and their weak gradients. -/
theorem memH1_lin {u v : Torus d → ℝ} (hu : MemH1 (densMeasure ρ) u)
    (hv : MemH1 (densMeasure ρ) v) (a b : ℝ) :
    MemH1 (densMeasure ρ) (fun x => a * u x + b * v x) ∧
      weakGrad (fun x => a * u x + b * v x) =ᵐ[densMeasure ρ]
        fun x k => a * weakGrad u x k + b * weakGrad v x k := by
  have hw : IsWeakGrad (fun x => a * u x + b * v x)
      (fun x k => a * weakGrad u x k + b * weakGrad v x k) :=
    ((isWeakGrad_weakGrad hu.1).cmul a).add ((isWeakGrad_weakGrad hv.1).cmul b)
  have hae : weakGrad (fun x => a * u x + b * v x) =ᵐ[densMeasure ρ]
      fun x k => a * weakGrad u x k + b * weakGrad v x k :=
    hρ.ac.ae_le (weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hw⟩) hw)
  refine ⟨⟨⟨_, hw⟩, (hu.2.1.const_mul a).add (hv.2.1.const_mul b), ?_⟩, hae⟩
  refine memLp_sqrt_sqNorm_of hρ fun k => ?_
  refine (((gradP hρ hu k).const_mul a).add ((gradP hρ hv k).const_mul b)).ae_eq ?_
  filter_upwards [hae] with x hx
  simp only [hx, Pi.add_apply]

theorem dirB_lin_left {u v w : Torus d → ℝ} (hu : MemH1 (densMeasure ρ) u)
    (hv : MemH1 (densMeasure ρ) v) (hw : MemH1 (densMeasure ρ) w) (a b : ℝ) :
    dirB (densMeasure ρ) (fun x => a * u x + b * v x) w =
      a * dirB (densMeasure ρ) u w + b * dirB (densMeasure ρ) v w := by
  have hae := (memH1_lin hρ hu hv a b).2
  unfold dirB
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((integrable_dirB_integrand hρ hu hw).const_mul a)
    ((integrable_dirB_integrand hρ hv hw).const_mul b)]
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  simp only [hx, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem integral_lin_mul {u v w : Torus d → ℝ} (hu : MemLp u 2 (densMeasure ρ))
    (hv : MemLp v 2 (densMeasure ρ)) (hw : MemLp w 2 (densMeasure ρ)) (a b : ℝ) :
    ∫ x, (a * u x + b * v x) * w x ∂densMeasure ρ =
      a * ∫ x, u x * w x ∂densMeasure ρ + b * ∫ x, v x * w x ∂densMeasure ρ := by
  haveI := hρ.isProb
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    (f := fun x => a * (u x * w x)) (g := fun x => b * (v x * w x))
    (by exact (hu.integrable_mul hw).const_mul a) (by exact (hv.integrable_mul hw).const_mul b)]
  congr 1; funext x; ring

/-- Quadratic expansion of the energy. -/
theorem dirE_lin {u v : Torus d → ℝ} (hu : MemH1 (densMeasure ρ) u)
    (hv : MemH1 (densMeasure ρ) v) (a b : ℝ) :
    dirE (densMeasure ρ) (fun x => a * u x + b * v x) =
      a ^ 2 * dirE (densMeasure ρ) u + 2 * a * b * dirB (densMeasure ρ) u v +
        b ^ 2 * dirE (densMeasure ρ) v := by
  have hl := memH1_lin hρ hu hv a b
  rw [dirE_eq_dirB hρ, dirB_lin_left hρ hu hv hl.1, dirB_comm hρ u, dirB_comm hρ v,
    dirB_lin_left hρ hu hv hu, dirB_lin_left hρ hu hv hv, dirE_eq_dirB hρ u, dirE_eq_dirB hρ v,
    dirB_comm hρ v u]
  ring

/-- Subtracting finitely many `H¹` functions. -/
theorem memH1_sub_sum {φ : Torus d → ℝ} (hφ : MemH1 (densMeasure ρ) φ) {e : ℕ → Torus d → ℝ}
    (s : Finset ℕ) (he : ∀ i ∈ s, MemH1 (densMeasure ρ) (e i)) (c : ℕ → ℝ) :
    MemH1 (densMeasure ρ) (fun x => φ x - ∑ i ∈ s, c i * e i x) ∧
      (∀ w, MemH1 (densMeasure ρ) w → dirB (densMeasure ρ) (fun x => φ x - ∑ i ∈ s, c i * e i x) w =
        dirB (densMeasure ρ) φ w - ∑ i ∈ s, c i * dirB (densMeasure ρ) (e i) w) ∧
      (∀ w, MemLp w 2 (densMeasure ρ) → ∫ x, (φ x - ∑ i ∈ s, c i * e i x) * w x ∂densMeasure ρ =
        ∫ x, φ x * w x ∂densMeasure ρ - ∑ i ∈ s, c i * ∫ x, e i x * w x ∂densMeasure ρ) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, sub_zero]
    exact ⟨hφ, fun _ _ => trivial, fun _ _ => trivial⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2, h3⟩ := ih fun i hi => he i (Finset.mem_insert_of_mem hi)
    have hea := he a (Finset.mem_insert_self a s)
    have hsplit : (fun x => φ x - ∑ i ∈ insert a s, c i * e i x) =
        fun x => 1 * (φ x - ∑ i ∈ s, c i * e i x) + (-c a) * e a x := by
      funext x; rw [Finset.sum_insert ha]; ring
    refine ⟨?_, fun w hw => ?_, fun w hw => ?_⟩
    · rw [hsplit]; exact (memH1_lin hρ h1 hea 1 (-c a)).1
    · rw [hsplit, dirB_lin_left hρ h1 hea hw, h2 w hw, Finset.sum_insert ha]; ring
    · have hI : ∫ x, (φ x - ∑ i ∈ insert a s, c i * e i x) * w x ∂densMeasure ρ =
          ∫ x, (1 * (φ x - ∑ i ∈ s, c i * e i x) + (-c a) * e a x) * w x ∂densMeasure ρ := by
        congr 1; funext x; rw [Finset.sum_insert ha]; ring
      rw [hI, integral_lin_mul hρ h1.2.1 hea.2.1 hw, h3 w hw, Finset.sum_insert ha]; ring

/-- **Euler–Lagrange equation** for a constrained minimizer. -/
theorem euler_lagrange {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} {n : ℕ} {f : Torus d → ℝ}
    (heH : ∀ i ≤ n, MemH1 (densMeasure ρ) (e i))
    (hon : ∀ i ≤ n, ∀ j ≤ n, ∫ x, e i x * e j x ∂densMeasure ρ = if i = j then 1 else 0)
    (heig : ∀ i ≤ n, ∀ φ, MemH1 (densMeasure ρ) φ →
      dirB (densMeasure ρ) (e i) φ = lam i * ∫ x, e i x * φ x ∂densMeasure ρ)
    (hf : f ∈ Adm (densMeasure ρ) e n)
    (hmin : ∀ u ∈ Adm (densMeasure ρ) e n, dirE (densMeasure ρ) f ≤ dirE (densMeasure ρ) u) :
    ∀ φ, MemH1 (densMeasure ρ) φ →
      dirB (densMeasure ρ) f φ = dirE (densMeasure ρ) f * ∫ x, f x * φ x ∂densMeasure ρ := by
  set P := densMeasure ρ
  haveI := hρ.isProb
  set L := dirE P f
  have hfH := hf.1
  -- step A: directions orthogonal to the constraints
  have stepA : ∀ φ, MemH1 P φ → (∀ i ≤ n, ∫ x, φ x * e i x ∂P = 0) →
      dirB P f φ = L * ∫ x, f x * φ x ∂P := by
    intro φ hφ hφo
    set B := dirB P f φ
    set p := ∫ x, f x * φ x ∂P
    set q := ∫ x, φ x * φ x ∂P
    set D := dirE P φ
    have hq0 : 0 ≤ q := integral_nonneg fun x => mul_self_nonneg _
    have key : ∀ t : ℝ, L * (1 + 2 * t * p + t ^ 2 * q) ≤ L + 2 * t * B + t ^ 2 * D := by
      intro t
      obtain ⟨hvH, -⟩ := memH1_lin hρ hfH hφ 1 t
      set v := fun x => 1 * f x + t * φ x
      have hN : ∫ x, v x ^ 2 ∂P = 1 + 2 * t * p + t ^ 2 * q := by
        have e1 : ∫ x, v x ^ 2 ∂P = ∫ x, (1 * f x + t * φ x) * v x ∂P := by
          congr 1; funext x; ring
        rw [e1, integral_lin_mul hρ hfH.2.1 hφ.2.1 hvH.2.1]
        have e2 : ∫ x, f x * v x ∂P = ∫ x, (1 * f x + t * φ x) * f x ∂P := by
          congr 1; funext x; ring
        have e3 : ∫ x, φ x * v x ∂P = ∫ x, (1 * f x + t * φ x) * φ x ∂P := by
          congr 1; funext x; ring
        rw [e2, e3, integral_lin_mul hρ hfH.2.1 hφ.2.1 hfH.2.1,
          integral_lin_mul hρ hfH.2.1 hφ.2.1 hφ.2.1]
        have e4 : ∫ x, f x * f x ∂P = 1 := by
          have := hf.2.1; simp_rw [sq] at this; exact this
        have e5 : ∫ x, φ x * f x ∂P = p := by simp only [p]; congr 1; funext x; ring
        rw [e4, e5]; ring
      have hE : dirE P v = L + 2 * t * B + t ^ 2 * D := by
        rw [dirE_lin hρ hfH hφ 1 t]; ring
      rw [← hN, ← hE]
      set N := ∫ x, v x ^ 2 ∂P
      have hN0 : 0 ≤ N := integral_nonneg fun x => sq_nonneg _
      rcases hN0.eq_or_lt with h0 | hpos
      · rw [← h0, mul_zero]; exact dirE_nonneg hρ v
      set sc := 1 / Real.sqrt N
      obtain ⟨hwH, -⟩ := memH1_lin hρ hvH hvH sc 0
      have hwAdm : (fun x => sc * v x + 0 * v x) ∈ Adm P e n := by
        refine ⟨hwH, ?_, fun i hi => ?_⟩
        · have : ∫ x, (sc * v x + 0 * v x) ^ 2 ∂P = sc ^ 2 * N := by
            rw [← integral_const_mul]; congr 1; funext x; ring
          rw [this, div_pow, Real.sq_sqrt hpos.le, one_pow, one_div_mul_cancel hpos.ne']
        · have : ∫ x, v x * e i x ∂P = 0 := by
            rw [integral_lin_mul hρ hfH.2.1 hφ.2.1 (heH i hi).2.1, hf.2.2 i hi, hφo i hi]; ring
          rw [integral_lin_mul hρ hvH.2.1 hvH.2.1 (heH i hi).2.1, this]; ring
      have h := hmin _ hwAdm
      rw [dirE_lin hρ hvH hvH sc 0] at h
      have hsc : sc ^ 2 * N = 1 := by
        rw [div_pow, Real.sq_sqrt hpos.le, one_pow, one_div_mul_cancel hpos.ne']
      have : L * N ≤ sc ^ 2 * dirE P v * N := by
        nlinarith [dirE_nonneg hρ v, dirB P v v]
      calc L * N ≤ sc ^ 2 * dirE P v * N := this
        _ = dirE P v := by
            rw [show sc ^ 2 * dirE P v * N = dirE P v * (sc ^ 2 * N) by ring, hsc, mul_one]
    have h1 : 0 ≤ B - L * p := by
      have := nonneg_of_forall_small (X := 2 * (B - L * p)) (Y := D - L * q) fun t ht _ => by
        have := key t; nlinarith
      linarith
    have h2 : 0 ≤ -(B - L * p) := by
      have := nonneg_of_forall_small (X := 2 * (-(B - L * p))) (Y := D - L * q) fun t ht _ => by
        have := key (-t); nlinarith
      linarith
    linarith
  -- step B: general directions
  intro φ hφ
  set cφ : ℕ → ℝ := fun i => ∫ x, φ x * e i x ∂P
  have heH' : ∀ i ∈ Finset.range (n + 1), MemH1 P (e i) := fun i hi =>
    heH i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  obtain ⟨h1, h2, h3⟩ := memH1_sub_sum hρ hφ (Finset.range (n + 1)) heH' cφ
  set φ' := fun x => φ x - ∑ i ∈ Finset.range (n + 1), cφ i * e i x
  have hφ'o : ∀ j ≤ n, ∫ x, φ' x * e j x ∂P = 0 := by
    intro j hj
    rw [h3 _ (heH j hj).2.1]
    rw [Finset.sum_eq_single j]
    · rw [hon j hj j hj, if_pos rfl, mul_one]; simp only [cφ]; ring
    · intro i hi hij
      rw [hon i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) j hj, if_neg hij, mul_zero]
    · intro hj'; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) hj'
  have hA := stepA φ' h1 hφ'o
  have hfe : ∀ i ∈ Finset.range (n + 1), ∫ x, e i x * f x ∂P = 0 := fun i hi => by
    rw [← hf.2.2 i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]; congr 1; funext x; ring
  have hB : dirB P f φ' = dirB P f φ := by
    rw [dirB_comm hρ, h2 f hfH, dirB_comm hρ φ]
    rw [Finset.sum_eq_zero fun i hi => by
      rw [heig i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) f hfH, hfe i hi]; ring]
    ring
  have hI : ∫ x, f x * φ' x ∂P = ∫ x, f x * φ x ∂P := by
    have e1 : ∫ x, f x * φ' x ∂P = ∫ x, φ' x * f x ∂P := by congr 1; funext x; ring
    rw [e1, h3 f hfH.2.1, Finset.sum_eq_zero fun i hi => by rw [hfe i hi]; ring, sub_zero]
    congr 1; funext x; ring
  rw [← hB, hA, hI]

end minimizer

end SharpLSI
