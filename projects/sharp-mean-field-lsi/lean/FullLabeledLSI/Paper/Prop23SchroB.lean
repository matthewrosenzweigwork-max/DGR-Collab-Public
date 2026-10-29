import FullLabeledLSI.Paper.Prop23SchroA
import SharpSymmetricLSI.Paper.FormLiminf4
import SharpSymmetricLSI.Paper.NBody3
import SharpSymmetricLSI.Paper.NBody4
import SharpSymmetricLSI.Paper.Occ8
import SharpSymmetricLSI.Paper.AppAFisher
import SharpSymmetricLSI.Paper.GroundT1
import SharpSymmetricLSI.Paper.GroundT11
import SharpSymmetricLSI.Paper.GroundT5
import SharpSymmetricLSI.Paper.ForceApprox2
import SharpSymmetricLSI.Paper.Moser3

/-! # Prop 2.3 WP-E1: the Schrödinger identity -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}


/-! ### Bounded functions and block sums (auxiliary) -/

section Aux

/-- Boundedness predicate. -/
def BddF {α : Type*} (f : α → ℝ) : Prop := ∃ B, ∀ x, |f x| ≤ B

theorem BddF.mul {α : Type*} {f g : α → ℝ} (hf : BddF f) (hg : BddF g) :
    BddF (fun x => f x * g x) := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨C, hC⟩ := hg
  refine ⟨B * C, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hB x) (hC x) (abs_nonneg _) ((abs_nonneg _).trans (hB x))

theorem BddF.const_mul {α : Type*} {f : α → ℝ} (c : ℝ) (hf : BddF f) :
    BddF (fun x => c * f x) := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨|c| * B, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _)

theorem BddF.comp {α β : Type*} {f : β → ℝ} (hf : BddF f) (g : α → β) : BddF (fun x => f (g x)) := by
  obtain ⟨B, hB⟩ := hf
  exact ⟨B, fun x => hB (g x)⟩

theorem BddF.sum {α ι : Type*} (s : Finset ι) {f : ι → α → ℝ} (hf : ∀ j ∈ s, BddF (f j)) :
    BddF (fun x => ∑ j ∈ s, f j x) := by
  choose! C hC using hf
  refine ⟨∑ j ∈ s, C j, fun x => ?_⟩
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => hC j hj x)

theorem BddF.of_bound {α : Type*} {f : α → ℝ} {B : ℝ} (h : ∀ x, |f x| ≤ B) : BddF f := ⟨B, h⟩

/-- Data for a block sum `y ↦ ∑_{j∈s} c_j ∑_b φ_j(y_b)` on `𝕋^{N×d}`: weak gradient
`p ↦ ∑_j c_j ∇φ_j(y_{p.1})_{p.2}`, both measurable and bounded. -/
theorem blockSum_data {d : ℕ} {φ : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (φ j ∘ liftT))
    (s : Finset ℕ) (c : ℕ → ℝ) (N : ℕ) :
    IsWeakGrad (fun y : UnitAddTorus (Fin N × Fin d) => ∑ j ∈ s, c j * ∑ b : Fin N, φ j (projBlock b y))
      (fun y p => ∑ j ∈ s, c j * cgrad (φ j) (projBlock p.1 y) p.2) ∧
    Measurable (fun y : UnitAddTorus (Fin N × Fin d) =>
      ∑ j ∈ s, c j * ∑ b : Fin N, φ j (projBlock b y)) ∧
    (∃ B, ∀ y : UnitAddTorus (Fin N × Fin d), |∑ j ∈ s, c j * ∑ b : Fin N, φ j (projBlock b y)| ≤ B) ∧
    (∀ p : Fin N × Fin d, Measurable fun y : UnitAddTorus (Fin N × Fin d) =>
      ∑ j ∈ s, c j * cgrad (φ j) (projBlock p.1 y) p.2) ∧
    (∃ L, ∀ (y : UnitAddTorus (Fin N × Fin d)) (p : Fin N × Fin d),
      |∑ j ∈ s, c j * cgrad (φ j) (projBlock p.1 y) p.2| ≤ L) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hj : ∀ j ∈ s, IsWeakGrad (fun y : UnitAddTorus (Fin N × Fin d) =>
        c j * ∑ b : Fin N, φ j (projBlock b y))
        (fun y p => c j * cgrad (φ j) (projBlock p.1 y) p.2) := by
      intro j _
      have h1 := isWeakGrad_finsetSum (Finset.univ : Finset (Fin N))
        (f := fun b y => φ j (projBlock b y))
        (g := fun b y p => if p.1 = b then cgrad (φ j) (projBlock b y) p.2 else 0)
        (fun b _ => isWeakGrad_phi_block hφ j b)
      have h2 := h1.cmul (c j)
      have e : (fun (y : UnitAddTorus (Fin N × Fin d)) (p : Fin N × Fin d) =>
          c j * ∑ b : Fin N, if p.1 = b then cgrad (φ j) (projBlock b y) p.2 else 0) =
          fun y p => c j * cgrad (φ j) (projBlock p.1 y) p.2 := by
        funext y p
        rw [Finset.sum_ite_eq]; simp
      rw [e] at h2
      exact h2
    exact isWeakGrad_finsetSum s hj
  · exact Finset.measurable_sum _ fun j _ => (Finset.measurable_sum _ fun b _ =>
      (measurable_of_contDiff (hφ j)).comp (measurable_projBlock b)).const_mul _
  · have : BddF (fun y : UnitAddTorus (Fin N × Fin d) => ∑ j ∈ s, c j * ∑ b : Fin N, φ j (projBlock b y)) :=
      BddF.sum s fun j _ => BddF.const_mul _ (BddF.sum _ fun b _ =>
        (BddF.of_bound (exists_bound_of_contDiff (hφ j)).choose_spec).comp _)
    exact this
  · intro p
    exact Finset.measurable_sum _ fun j _ =>
      ((measurable_cgrad (hφ j) p.2).comp (measurable_projBlock p.1)).const_mul _
  · choose! C hC using fun j => exists_bound_cgrad (hφ j)
    refine ⟨∑ j ∈ s, |c j| * C j, fun y p => ?_⟩
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC j _ _) (abs_nonneg _)

/-- `T_R Z_N` is bounded and measurable in `X`. -/
theorem TR_fluct_bdd_meas {d : ℕ} {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)}
    {e eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT))
    (A : FiniteRankApprox W μ e) (R : ℕ) {N : ℕ} (i : ℕ) :
    BddF (fun X : Config N d => TR A R (fun n => fluct eC N n X) i) ∧
      Measurable (fun X : Config N d => TR A R (fun n => fluct eC N n X) i) := by
  have hb : ∀ j, BddF (eC j) := fun j => ⟨_, (exists_bound_of_contDiff (hφ j)).choose_spec⟩
  unfold TR fluct
  refine ⟨BddF.sum _ fun j _ => BddF.const_mul _ (BddF.const_mul _
    (BddF.sum Finset.univ fun l _ => (hb (j + 1)).comp (fun X : Config N d => X l))), ?_⟩
  exact Finset.measurable_sum _ fun j _ => ((Finset.measurable_sum _ fun l _ =>
    (measurable_of_contDiff (hφ (j + 1))).comp (measurable_pi_apply l)).const_mul _).const_mul _

/-- Bounded and measurable. -/
def BM {α : Type*} [MeasurableSpace α] (f : α → ℝ) : Prop := BddF f ∧ Measurable f

theorem BM.mul {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : BM f) (hg : BM g) :
    BM (fun x => f x * g x) := ⟨hf.1.mul hg.1, hf.2.mul hg.2⟩

theorem BM.const_mul {α : Type*} [MeasurableSpace α] {f : α → ℝ} (c : ℝ) (hf : BM f) :
    BM (fun x => c * f x) := ⟨hf.1.const_mul c, hf.2.const_mul c⟩

theorem BM.sum {α ι : Type*} [MeasurableSpace α] (s : Finset ι) {f : ι → α → ℝ}
    (hf : ∀ j ∈ s, BM (f j)) : BM (fun x => ∑ j ∈ s, f j x) :=
  ⟨BddF.sum s fun j hj => (hf j hj).1, Finset.measurable_sum _ fun j hj => (hf j hj).2⟩

theorem BM.sub {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : BM f) (hg : BM g) :
    BM (fun x => f x - g x) := by
  obtain ⟨⟨B, hB⟩, hfm⟩ := hf
  obtain ⟨⟨C, hC⟩, hgm⟩ := hg
  exact ⟨⟨B + C, fun x => (abs_sub _ _).trans (add_le_add (hB x) (hC x))⟩, hfm.sub hgm⟩

theorem BM.comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : β → ℝ} (hf : BM f)
    {g : α → β} (hg : Measurable g) : BM (fun x => f (g x)) := ⟨hf.1.comp g, hf.2.comp hg⟩

theorem BM_fluct {d : ℕ} {eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (N n : ℕ) :
    BM (fun X : Config N d => fluct eC N n X) := by
  unfold fluct
  refine BM.const_mul _ (BM.sum Finset.univ fun l _ => ?_)
  exact (show BM (eC (n + 1)) from ⟨⟨_, (exists_bound_of_contDiff (hφ (n + 1))).choose_spec⟩,
    measurable_of_contDiff (hφ (n + 1))⟩).comp (measurable_pi_apply l)

theorem BM_ANmat {d : ℕ} {eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (N i j : ℕ) :
    BM (fun X : Config N d => ANmat eC N X i j) := by
  unfold ANmat
  have hcg : ∀ m (k : Fin d), BM (fun x : Torus d => cgrad (eC m) x k) := fun m k =>
    ⟨⟨(exists_bound_cgrad (hφ m)).choose, fun x => (exists_bound_cgrad (hφ m)).choose_spec x k⟩,
      measurable_cgrad (hφ m) k⟩
  refine BM.const_mul _ (BM.sum Finset.univ fun l _ => BM.sum Finset.univ fun k _ => ?_)
  exact ((hcg (i + 1) k).comp (measurable_pi_apply l)).mul ((hcg (j + 1) k).comp (measurable_pi_apply l))

theorem BM_TR {d : ℕ} {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)}
    {e eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT))
    (A : FiniteRankApprox W μ e) (R : ℕ) {N : ℕ} (i : ℕ) :
    BM (fun X : Config N d => TR A R (fun n => fluct eC N n X) i) :=
  TR_fluct_bdd_meas hφ A R i

/-- `∇U_{N,R}` is uniformly bounded. -/
theorem gradURN_bdd {d : ℕ} {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)}
    {e eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT))
    (A : FiniteRankApprox W μ e) (R N : ℕ) :
    ∃ L, ∀ (X : Config N d) (l : Fin N) (k : Fin d), |gradURN A eC R N X l k| ≤ L := by
  choose! Bt hBt using fun i => (TR_fluct_bdd_meas hφ A R (N := N) i).1
  choose! Cg hCg using fun i => exists_bound_cgrad (hφ (i + 1))
  refine ⟨|(N : ℝ) ^ (-(1 / 2 : ℝ))| * ∑ i ∈ A.s R, Bt i * Cg i, fun X l k => ?_⟩
  unfold gradURN
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => ?_)) (abs_nonneg _)
  rw [abs_mul]
  exact mul_le_mul (hBt i X) (hCg i (X l) k) (abs_nonneg _) ((abs_nonneg _).trans (hBt i X))

end Aux

section Schro

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} (hyp : Hyp V W KV KW)
  {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
  (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
include hyp hμ he hφ heC

/-- **One-particle Dirichlet matrix for the `C¹` representatives**:
`∑_k ∫ ∂_k eC a · ∂_k eC b dμ = λ_a δ_{ab}`.

Proof (about 30 lines): `sum_integral_grad_e` (Occ8:29, in terms of `weakGrad (e a)`), and
`weakGrad (e a) =ᵐ[μ] cgrad (eC a)` (`weakGrad_ae_eq_of_contDiff`, SmoothWeakGrad:60 for `eC a`,
`appA_isWeakGrad_congr_ae`/`IsWeakGrad.congr_ae` to pass from `eC a` to `e a`, then `minimizer_ac`
to go from `volume`-a.e. to `μ`-a.e.; model: `GaussLSI6:48`). -/
theorem sum_integral_cgrad_eC (a b : ℕ) :
    ∑ k : Fin d, ∫ x, cgrad (eC a) x k * cgrad (eC b) x k ∂(μ : Measure (Torus d)) =
      lam a * (if a = b then 1 else 0) := by
  rw [← SharpLSI.sum_integral_grad_e hyp hμ he a b]
  have hac : (μ : Measure (Torus d)) ≪ haar d := minimizer_ac hyp hμ
  have hwg : ∀ j, weakGrad (e j) =ᵐ[haar d] cgrad (eC j) := fun j =>
    weakGrad_ae_eq (appA_isWeakGrad_congr_ae (isWeakGrad_of_contDiff (hφ j)) (heC j))
  have hall : ∀ᵐ x ∂(μ : Measure (Torus d)), ∀ j, weakGrad (e j) x = cgrad (eC j) x :=
    hac.ae_le (ae_all_iff.2 hwg)
  refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
  filter_upwards [hall] with x hx
  rw [hx a, hx b]

/-- **The eigen-slice identity for `Φ = Ψ² (T_R Z_N)_i`** (E1, the integration by parts; one label `l`,
one mode `i`).  For `Ψ ∈ H¹(Q_N)`:
`∫ ∑_k (2Ψ ∂_{lk}Ψ) (TZ)_i ∂_k eC(i+1)(X_l) + ∫ Ψ² ∑_j a_ij N^{-1/2} ∑_k ∂_k eC(j+1)(X_l) ∂_k eC(i+1)(X_l)
   = λ_{i+1} ∫ Ψ² (TZ)_i eC(i+1)(X_l)`.
(`2Ψ ∂Ψ` is the weak gradient of `Ψ²`, the second integral is `∫ Ψ² ∇_l (TZ)_i · ∇_l e_{i+1}(X_l)`, the
product rule for `Φ = Ψ² (TZ)_i`.)

Proof (about 100-130 lines):
1. `u := Ψ ∘ unflat ∈ L²(volume)`, `∇u ∈ L²(volume)` (see the header, `minimizer_pi_comparison`);
   `isWeakGrad_sq` (AppAFisher:137) gives `IsWeakGrad (u²) (2 u ∇u)` with `L¹(volume)` data.
2. `h := (TZ)_i ∘ flat = N^{-1/2} ∑_j a_ij ∑_b eC(j+1)(proj_b y)` is bounded, measurable, with
   bounded measurable weak gradient `N^{-1/2} ∑_j a_ij · [p.1 = b ↦ cgrad (eC (j+1)) …]`:
   `isWeakGrad_phi_block` (ForceApprox2:43) and `isWeakGrad_finsetSum`; `IsWeakGrad.mul_lip`
   (GroundT1:46) gives `IsWeakGrad (u² h) (2u∇u h + u² ∇h)`, with `L¹` data.
3. `eigen_slice` (FormLiminf4:21) for `Φ = u² h`, `G = 2u∇u h + u²∇h`, `l`, `i+1`; rewrite the
   `volume`-a.e. identification `weakGrad (Ψ∘unflat) (flat X) (l,k) = weakGradC Ψ X l k` and
   `∑_k` bookkeeping; `integral_add`. -/
theorem eigen_slice_sq_mul (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (R : ℕ) {N : ℕ}
    (hN : 1 ≤ N) {Ψ : Config N d → ℝ} (hΨ : MemH1C (QN (μ : Measure (Torus d)) N) Ψ)
    (l : Fin N) (i : ℕ) :
    ∫ X, ∑ k : Fin d, (2 * Ψ X * weakGradC Ψ X l k) * TR A R (fun n => fluct eC N n X) i *
        cgrad (eC (i + 1)) (X l) k ∂QN (μ : Measure (Torus d)) N +
      ∫ X, Ψ X ^ 2 * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ j ∈ A.s R, A.a R i j *
        ∑ k : Fin d, cgrad (eC (j + 1)) (X l) k * cgrad (eC (i + 1)) (X l) k)
          ∂QN (μ : Measure (Torus d)) N =
      lam (i + 1) * ∫ X, Ψ X ^ 2 * TR A R (fun n => fluct eC N n X) i * eC (i + 1) (X l)
        ∂QN (μ : Measure (Torus d)) N := by
  classical
  simp only [QN] at hΨ ⊢
  set P : Measure (Config N d) := Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) with hP
  have : IsProbabilityMeasure (P.map flat) :=
    (Measure.isProbabilityMeasure_map_iff measurable_flat.aemeasurable).mpr inferInstance
  obtain ⟨a, b, ha0, hb0, ha, hb⟩ := SharpLSI.minimizer_pi_comparison hyp hμ (N := N)
  have huH : MemH1 (P.map flat) (Ψ ∘ unflat) := hΨ
  have huV : MemLp (Ψ ∘ unflat) 2 volume := memLp_vol ha huH
  have hw := isWeakGrad_weakGrad huH.1
  have hgV : ∀ p, MemLp (fun y => weakGrad (Ψ ∘ unflat) y p) 2 volume :=
    memLp_grad_vol ha hb huH
  have hsq := isWeakGrad_sq hw huV hgV
  set c : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ)) with hc
  obtain ⟨hhw, hhm, ⟨B, hB⟩, hghm, ⟨L, hL⟩⟩ :=
    blockSum_data (φ := fun j => eC (j + 1)) (fun j => hφ (j + 1)) (A.s R)
      (fun j => c * A.a R i j) N
  have hug : ∀ p, Integrable (fun y => 2 * (Ψ ∘ unflat) y * weakGrad (Ψ ∘ unflat) y p) volume :=
    fun p => ((huV.integrable_mul (hgV p)).const_mul 2).congr
      (Eventually.of_forall fun y => by simp only [Pi.mul_apply]; ring)
  have hprod := hsq.mul_lip huV.integrable_sq hug hhw hhm hB hghm hL
  have hbB : ∀ᵐ y : UnitAddTorus (Fin N × Fin d) ∂volume,
      ‖∑ j ∈ A.s R, c * A.a R i j * ∑ b : Fin N, eC (j + 1) (projBlock b y)‖ ≤ B :=
    Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y
  have hΦi := huV.integrable_sq.mul_bdd hhm.aestronglyMeasurable hbB
  have hGi : ∀ p, Integrable (fun y =>
      2 * (Ψ ∘ unflat) y * weakGrad (Ψ ∘ unflat) y p *
          (∑ j ∈ A.s R, c * A.a R i j * ∑ b : Fin N, eC (j + 1) (projBlock b y)) +
        (Ψ ∘ unflat) y ^ 2 * ∑ j ∈ A.s R, c * A.a R i j * cgrad (eC (j + 1)) (projBlock p.1 y) p.2)
      volume := fun p =>
    ((hug p).mul_bdd hhm.aestronglyMeasurable hbB).add
      (huV.integrable_sq.mul_bdd (hghm p).aestronglyMeasurable
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hL y p))
  have key := SharpLSI.eigen_slice hyp hμ he hφ heC l (i + 1) hprod hΦi hGi
  -- `X`-level functions
  set hf : Config N d → ℝ := fun X => ∑ j ∈ A.s R, c * A.a R i j * ∑ b : Fin N, eC (j + 1) (X b) with hhf
  set ghf : Config N d → Fin d → ℝ := fun X k =>
    ∑ j ∈ A.s R, c * A.a R i j * cgrad (eC (j + 1)) (X l) k with hghf
  have key' : ∫ X, ∑ k : Fin d, ((2 * Ψ X * weakGradC Ψ X l k) * hf X + Ψ X ^ 2 * ghf X k) *
        cgrad (eC (i + 1)) (X l) k ∂P =
      lam (i + 1) * ∫ X, Ψ X ^ 2 * hf X * eC (i + 1) (X l) ∂P := key
  have hTR : ∀ X : Config N d, TR A R (fun n => fluct eC N n X) i = hf X := fun X => by
    simp only [TR, fluct, hhf, hc]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [hTR]
  have hcgb : ∀ j k, BddF (fun x : Torus d => cgrad (eC j) x k) := fun j k =>
    ⟨(exists_bound_cgrad (hφ j)).choose, fun x => (exists_bound_cgrad (hφ j)).choose_spec x k⟩
  have hcgm : ∀ j k, Measurable (fun X : Config N d => cgrad (eC j) (X l) k) := fun j k =>
    (measurable_cgrad (hφ j) k).comp (measurable_pi_apply l)
  have hPsi : MemLp Ψ 2 P := memLp_of_memH1C_pi hΨ
  have hhfm : Measurable hf := hhm.comp measurable_flat
  have hhfb : BddF hf := ⟨B, fun X => hB (flat X)⟩
  have hA : ∀ k, Integrable (fun X => (2 * Ψ X * weakGradC Ψ X l k) * hf X *
      cgrad (eC (i + 1)) (X l) k) P := by
    intro k
    obtain ⟨C, hC⟩ := (hhfb.const_mul 2).mul ((hcgb (i + 1) k).comp (fun X : Config N d => X l))
    have h1 := (hPsi.integrable_mul (memLp_weakGradC hyp hμ hΨ l k)).mul_bdd
      ((hhfm.const_mul 2).mul (hcgm (i + 1) k)).aestronglyMeasurable
      (c := C) (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hC X)
    refine h1.congr (Eventually.of_forall fun X => ?_)
    simp only [Pi.mul_apply]
    ring
  have hT1 : Integrable (fun X => ∑ k : Fin d, (2 * Ψ X * weakGradC Ψ X l k) * hf X *
      cgrad (eC (i + 1)) (X l) k) P := integrable_finsetSum _ fun k _ => hA k
  have hT2 : Integrable (fun X => Ψ X ^ 2 * (c * ∑ j ∈ A.s R, A.a R i j *
      ∑ k : Fin d, cgrad (eC (j + 1)) (X l) k * cgrad (eC (i + 1)) (X l) k)) P := by
    obtain ⟨C, hC⟩ := (BddF.const_mul c (BddF.sum (A.s R) fun j _ => BddF.const_mul (A.a R i j)
      (BddF.sum (Finset.univ : Finset (Fin d)) fun k _ => BddF.mul
        ((hcgb (j + 1) k).comp (fun X : Config N d => X l))
        ((hcgb (i + 1) k).comp (fun X : Config N d => X l)))))
    exact hPsi.integrable_sq.mul_bdd
      (((Finset.measurable_sum _ fun j _ => (Finset.measurable_sum _ fun k _ =>
        (hcgm (j + 1) k).mul (hcgm (i + 1) k)).const_mul _).const_mul c).aestronglyMeasurable)
      (c := C) (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hC X)
  have hsplit : ∀ X : Config N d, ∑ k : Fin d, ((2 * Ψ X * weakGradC Ψ X l k) * hf X +
        Ψ X ^ 2 * ghf X k) * cgrad (eC (i + 1)) (X l) k =
      ∑ k : Fin d, (2 * Ψ X * weakGradC Ψ X l k) * hf X * cgrad (eC (i + 1)) (X l) k +
        Ψ X ^ 2 * (c * ∑ j ∈ A.s R, A.a R i j *
          ∑ k : Fin d, cgrad (eC (j + 1)) (X l) k * cgrad (eC (i + 1)) (X l) k) := by
    intro X
    have e2 : ∑ k : Fin d, Ψ X ^ 2 * ghf X k * cgrad (eC (i + 1)) (X l) k =
        Ψ X ^ 2 * (c * ∑ j ∈ A.s R, A.a R i j *
          ∑ k : Fin d, cgrad (eC (j + 1)) (X l) k * cgrad (eC (i + 1)) (X l) k) := by
      simp only [hghf, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    rw [← e2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [← integral_add hT1 hT2]
  calc _ = ∫ X, ∑ k : Fin d, ((2 * Ψ X * weakGradC Ψ X l k) * hf X + Ψ X ^ 2 * ghf X k) *
        cgrad (eC (i + 1)) (X l) k ∂P := by
        refine integral_congr_ae (Eventually.of_forall fun X => ?_)
        exact (hsplit X).symm
    _ = _ := key'

omit he heC in
/-- Integrability of the three families of terms in `eigen_slice_sq_mul`. -/
theorem slice_integrable (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (R : ℕ) {N : ℕ}
    {Ψ : Config N d → ℝ} (hΨ : MemH1C (QN (μ : Measure (Torus d)) N) Ψ) (l : Fin N) (i : ℕ) :
    Integrable (fun X : Config N d => ∑ k : Fin d, (2 * Ψ X * weakGradC Ψ X l k) *
        TR A R (fun n => fluct eC N n X) i * cgrad (eC (i + 1)) (X l) k)
      (QN (μ : Measure (Torus d)) N) ∧
    Integrable (fun X : Config N d => Ψ X ^ 2 * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ j ∈ A.s R, A.a R i j *
        ∑ k : Fin d, cgrad (eC (j + 1)) (X l) k * cgrad (eC (i + 1)) (X l) k))
      (QN (μ : Measure (Torus d)) N) ∧
    Integrable (fun X : Config N d => Ψ X ^ 2 * TR A R (fun n => fluct eC N n X) i * eC (i + 1) (X l))
      (QN (μ : Measure (Torus d)) N) := by
  classical
  obtain ⟨hTb, hTm⟩ := TR_fluct_bdd_meas hφ A R (N := N) i
  have hcgb : ∀ j k, BddF (fun x : Torus d => cgrad (eC j) x k) := fun j k =>
    ⟨(exists_bound_cgrad (hφ j)).choose, fun x => (exists_bound_cgrad (hφ j)).choose_spec x k⟩
  have hcgm : ∀ j k, Measurable (fun X : Config N d => cgrad (eC j) (X l) k) := fun j k =>
    (measurable_cgrad (hφ j) k).comp (measurable_pi_apply l)
  have hPsi : MemLp Ψ 2 (QN (μ : Measure (Torus d)) N) := memLp_of_memH1C_pi hΨ
  refine ⟨?_, ?_, ?_⟩
  · refine integrable_finsetSum _ fun k _ => ?_
    obtain ⟨C, hC⟩ := (hTb.const_mul 2).mul ((hcgb (i + 1) k).comp (fun X : Config N d => X l))
    have h1 := (hPsi.integrable_mul (memLp_weakGradC hyp hμ hΨ l k)).mul_bdd
      ((hTm.const_mul 2).mul (hcgm (i + 1) k)).aestronglyMeasurable
      (c := C) (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hC X)
    refine h1.congr (Eventually.of_forall fun X => ?_)
    simp only [Pi.mul_apply]
    ring
  · obtain ⟨C, hC⟩ := (BddF.const_mul ((N : ℝ) ^ (-(1 / 2 : ℝ))) (BddF.sum (A.s R) fun j _ =>
      BddF.const_mul (A.a R i j)
      (BddF.sum (Finset.univ : Finset (Fin d)) fun k _ => BddF.mul
        ((hcgb (j + 1) k).comp (fun X : Config N d => X l))
        ((hcgb (i + 1) k).comp (fun X : Config N d => X l)))))
    exact hPsi.integrable_sq.mul_bdd
      (((Finset.measurable_sum _ fun j _ => (Finset.measurable_sum _ fun k _ =>
        (hcgm (j + 1) k).mul (hcgm (i + 1) k)).const_mul _).const_mul _).aestronglyMeasurable)
      (c := C) (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hC X)
  · have heb : BddF (eC (i + 1)) := ⟨_, (exists_bound_of_contDiff (hφ (i + 1))).choose_spec⟩
    obtain ⟨C, hC⟩ := hTb.mul (heb.comp (fun X : Config N d => X l))
    refine (hPsi.integrable_sq.mul_bdd (hTm.mul ((measurable_of_contDiff (hφ (i + 1))).comp
      (measurable_pi_apply l))).aestronglyMeasurable
      (c := C) (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hC X)).congr
      (Eventually.of_forall fun X => ?_)
    simp only [Pi.mul_apply, Function.comp_apply]
    ring

/-- **The cross term** (E1, step 2): `∫ Ψ ∇Ψ·∇U_{N,R} dQ = ½ ∫ Ψ² (Z_NᵀΛ_R T_R Z_N - tr(T_R A_N)) dQ`.

Proof (about 60-80 lines): multiply `eigen_slice_sq_mul` by `N^{-1/2}`, sum over `l : Fin N` and
`i ∈ s_R` (`integral_finsetSum`; all integrands are integrable by boundedness of the `eC`, their
gradients, and `Ψ² ∈ L¹`, `Ψ ∂Ψ ∈ L¹`).  The first sum is `∫ ∑_{l,k} 2Ψ ∂Ψ gradURN` (definition of
`gradURN`), the second is `∫ Ψ² ∑_{ij} a_ij A_{N,ij}` (definition of `ANmat`; `N^{-1/2} N^{-1/2} = N⁻¹`),
the right side is `∑_i λ_{i+1} ∫ Ψ² (TZ)_i Z_i` (definition of `fluct eC`).  Divide by 2. -/
theorem cross_term_URN (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (R : ℕ) {N : ℕ}
    (hN : 1 ≤ N) {Ψ : Config N d → ℝ} (hΨ : MemH1C (QN (μ : Measure (Torus d)) N) Ψ) :
    ∫ X, Ψ X * ∑ l, ∑ k, weakGradC Ψ X l k * gradURN A eC R N X l k
        ∂QN (μ : Measure (Torus d)) N =
      (1 / 2) * ∫ X, Ψ X ^ 2 *
        (∑ i ∈ A.s R, lam (i + 1) * fluct eC N i X * TR A R (fun n => fluct eC N n X) i
          - ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * ANmat eC N X i j)
        ∂QN (μ : Measure (Torus d)) N := by
  classical
  set c : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ)) with hc
  set P := QN (μ : Measure (Torus d)) N with hP
  have hcc : c * c = (N : ℝ)⁻¹ := prop23_rpow_half_mul_self N
  let T1 : Fin N → ℕ → Config N d → ℝ := fun l i X => ∑ k : Fin d, (2 * Ψ X * weakGradC Ψ X l k) *
    TR A R (fun n => fluct eC N n X) i * cgrad (eC (i + 1)) (X l) k
  let T2 : Fin N → ℕ → Config N d → ℝ := fun l i X => Ψ X ^ 2 * (c * ∑ j ∈ A.s R, A.a R i j *
    ∑ k : Fin d, cgrad (eC (j + 1)) (X l) k * cgrad (eC (i + 1)) (X l) k)
  let T3 : Fin N → ℕ → Config N d → ℝ := fun l i X =>
    Ψ X ^ 2 * TR A R (fun n => fluct eC N n X) i * eC (i + 1) (X l)
  have hI : ∀ l i, Integrable (T1 l i) P ∧ Integrable (T2 l i) P ∧ Integrable (T3 l i) P :=
    fun l i => slice_integrable hyp hμ hφ A R hΨ l i
  have hrel : ∀ (l : Fin N) (i : ℕ), c * ∫ X, T1 l i X ∂P =
      c * (lam (i + 1) * ∫ X, T3 l i X ∂P) - c * ∫ X, T2 l i X ∂P := fun l i => by
    have h : (∫ X, T1 l i X ∂P) + ∫ X, T2 l i X ∂P = lam (i + 1) * ∫ X, T3 l i X ∂P :=
      eigen_slice_sq_mul hyp hμ he hφ heC A R hN hΨ l i
    linear_combination c * h
  -- pointwise identities
  have E1 : ∀ X : Config N d, Ψ X * ∑ l, ∑ k, weakGradC Ψ X l k * gradURN A eC R N X l k =
      (1 / 2) * ∑ l : Fin N, ∑ i ∈ A.s R, c * T1 l i X := by
    intro X
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [gradURN, T1, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have E2 : ∀ X : Config N d, Ψ X ^ 2 *
      (∑ i ∈ A.s R, lam (i + 1) * fluct eC N i X * TR A R (fun n => fluct eC N n X) i
        - ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * ANmat eC N X i j) =
      ∑ l : Fin N, ∑ i ∈ A.s R, c * (lam (i + 1) * T3 l i X) -
        ∑ l : Fin N, ∑ i ∈ A.s R, c * T2 l i X := by
    intro X
    rw [mul_sub]
    congr 1
    · simp only [fluct, T3, ← hc]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring
    · simp only [ANmat, T2, Finset.mul_sum, Finset.sum_mul]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hcc]
      ring
  have hsum : ∀ F : Fin N → ℕ → Config N d → ℝ, (∀ l i, Integrable (F l i) P) →
      ∫ X, ∑ l, ∑ i ∈ A.s R, F l i X ∂P = ∑ l, ∑ i ∈ A.s R, ∫ X, F l i X ∂P := fun F hF => by
    rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun i _ => hF l i]
    exact Finset.sum_congr rfl fun l _ => integral_finsetSum _ fun i _ => hF l i
  have hsumI : ∀ F : Fin N → ℕ → Config N d → ℝ, (∀ l i, Integrable (F l i) P) →
      Integrable (fun X => ∑ l, ∑ i ∈ A.s R, F l i X) P := fun F hF =>
    integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun i _ => hF l i
  have h1 : ∫ X, ∑ l, ∑ i ∈ A.s R, c * T1 l i X ∂P = ∑ l, ∑ i ∈ A.s R, c * ∫ X, T1 l i X ∂P := by
    rw [hsum (fun l i X => c * T1 l i X) fun l i => (hI l i).1.const_mul c]
    simp only [integral_const_mul]
  have h2 : ∫ X, ∑ l, ∑ i ∈ A.s R, c * T2 l i X ∂P = ∑ l, ∑ i ∈ A.s R, c * ∫ X, T2 l i X ∂P := by
    rw [hsum (fun l i X => c * T2 l i X) fun l i => (hI l i).2.1.const_mul c]
    simp only [integral_const_mul]
  have h3 : ∫ X, ∑ l, ∑ i ∈ A.s R, c * (lam (i + 1) * T3 l i X) ∂P =
      ∑ l, ∑ i ∈ A.s R, c * (lam (i + 1) * ∫ X, T3 l i X ∂P) := by
    rw [hsum (fun l i X => c * (lam (i + 1) * T3 l i X))
      fun l i => ((hI l i).2.2.const_mul (lam (i + 1))).const_mul c]
    simp only [integral_const_mul]
  have hE2 : ∫ X, Ψ X ^ 2 *
      (∑ i ∈ A.s R, lam (i + 1) * fluct eC N i X * TR A R (fun n => fluct eC N n X) i
        - ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * ANmat eC N X i j) ∂P =
      ∑ l, ∑ i ∈ A.s R, c * (lam (i + 1) * ∫ X, T3 l i X ∂P) -
        ∑ l, ∑ i ∈ A.s R, c * ∫ X, T2 l i X ∂P := by
    rw [integral_congr_ae (Eventually.of_forall E2), integral_sub
      (hsumI (fun l i X => c * (lam (i + 1) * T3 l i X))
        fun l i => ((hI l i).2.2.const_mul (lam (i + 1))).const_mul c)
      (hsumI (fun l i X => c * T2 l i X) fun l i => (hI l i).2.1.const_mul c), h3, h2]
  rw [hE2, integral_congr_ae (Eventually.of_forall E1), integral_const_mul, h1]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => hrel l i

/-- **(E1) The Schrödinger identity** (eq:schrodinger) for `U_{N,R}`, every `Ψ ∈ H¹(Q_N)`:
`∫|∇Ψ + ½Ψ∇U_{N,R}|² dQ_N = ∫|∇Ψ|² dQ_N + ∫ V_{N,R} Ψ² dQ_N`.

Proof (about 60 lines): `weakGradC_URN_ae` (Replace; `hac := minimizer_ac hyp hμ`) shows
`shEn μ Ψ (URN A R N)` is the `shEn`-integral with `gradURN` in place of `weakGradC (URN …)`;
`hasWeakGrad` and a uniform bound `|gradURN| ≤ L` from `exists_bound_of_contDiff`/`exists_bound_cgrad`
(NBody2:36-42, finite sums); `shEn_expand` (with `U := URN A R N`); `cross_term_URN` for the middle
term (after the a.e. replacement `weakGradC (URN) = gradURN`); `sum_gradURN_sq` for
`gradSqC (URN …) = ∑ (gradURN)² = (TZ)ᵀ A (TZ)` a.e.; combine:
`∫ gradSqC Ψ + ½ ∫ Ψ²(ZᵀΛTZ - tr TA) + ¼ ∫ Ψ² (TZ)ᵀA(TZ) = ∫ gradSqC Ψ + ∫ VNR Ψ²`
by the definition of `VNR` (`integral_add`, `integral_const_mul`, `ring`-level finite sum algebra;
all integrands bounded × `Ψ²`). -/
theorem schrodinger_identity (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (R : ℕ) {N : ℕ}
    (hN : 1 ≤ N) {Ψ : Config N d → ℝ} (hΨ : MemH1C (QN (μ : Measure (Torus d)) N) Ψ) :
    shEn (μ : Measure (Torus d)) Ψ (URN A R N) ≠ ⊤ ∧
      (shEn (μ : Measure (Torus d)) Ψ (URN A R N)).toReal =
        (refEnergy (μ : Measure (Torus d)) Ψ).toReal +
          ∫ X, VNR A lam eC R N X * Ψ X ^ 2 ∂QN (μ : Measure (Torus d)) N := by
  classical
  have hac : (μ : Measure (Torus d)) ≪ haar d := minimizer_ac hyp hμ
  have hae := weakGradC_URN_ae hac A hφ heC R hN
  obtain ⟨L, hL⟩ := gradURN_bdd hφ A R N
  have hU : HasWeakGrad (URN A R N ∘ unflat) := ⟨_, isWeakGrad_URN A hφ heC R hN⟩
  have hLae : ∀ᵐ X ∂QN (μ : Measure (Torus d)) N, ∀ (i : Fin N) (k : Fin d),
      |weakGradC (URN A R N) X i k| ≤ L := hae.mono fun X hX i k => by rw [hX i k]; exact hL X i k
  obtain ⟨hne, hval⟩ := shEn_expand hac hΨ hU hLae
  refine ⟨hne, ?_⟩
  rw [hval]
  have hmid : ∫ X, Ψ X * ∑ i, ∑ k, weakGradC Ψ X i k * weakGradC (URN A R N) X i k
        ∂QN (μ : Measure (Torus d)) N =
      ∫ X, Ψ X * ∑ l, ∑ k, weakGradC Ψ X l k * gradURN A eC R N X l k
        ∂QN (μ : Measure (Torus d)) N := by
    refine integral_congr_ae (hae.mono fun X hX => ?_)
    simp only [hX]
  have hsq : ∫ X, Ψ X ^ 2 * gradSqC (URN A R N) X ∂QN (μ : Measure (Torus d)) N =
      ∫ X, Ψ X ^ 2 * ∑ i ∈ A.s R, ∑ j ∈ A.s R, TR A R (fun n => fluct eC N n X) i *
        ANmat eC N X i j * TR A R (fun n => fluct eC N n X) j ∂QN (μ : Measure (Torus d)) N := by
    refine integral_congr_ae (hae.mono fun X hX => ?_)
    simp only [gradSqC, hX]
    rw [sum_gradURN_sq]
  rw [hmid, hsq, cross_term_URN hyp hμ he hφ heC A R hN hΨ]
  -- integrability
  have hPsi : Integrable (fun X => Ψ X ^ 2) (QN (μ : Measure (Torus d)) N) :=
    (memLp_of_memH1C_pi hΨ).integrable_sq
  have hg1 : BM (fun X : Config N d => ∑ i ∈ A.s R, lam (i + 1) * fluct eC N i X *
        TR A R (fun n => fluct eC N n X) i
      - ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * ANmat eC N X i j) :=
    (BM.sum _ fun i _ => ((BM_fluct hφ N i).const_mul (lam (i + 1))).mul (BM_TR hφ A R i)).sub
      (BM.sum _ fun i _ => BM.sum _ fun j _ => (BM_ANmat hφ N i j).const_mul (A.a R i j))
  have hg2 : BM (fun X : Config N d => ∑ i ∈ A.s R, ∑ j ∈ A.s R, TR A R (fun n => fluct eC N n X) i *
        ANmat eC N X i j * TR A R (fun n => fluct eC N n X) j) :=
    BM.sum _ fun i _ => BM.sum _ fun j _ => ((BM_TR hφ A R i).mul (BM_ANmat hφ N i j)).mul (BM_TR hφ A R j)
  have hi1 := hPsi.mul_bdd hg1.2.aestronglyMeasurable
    (c := hg1.1.choose) (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]; exact hg1.1.choose_spec X)
  have hi2 := hPsi.mul_bdd hg2.2.aestronglyMeasurable
    (c := hg2.1.choose) (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]; exact hg2.1.choose_spec X)
  have hV : ∫ X, VNR A lam eC R N X * Ψ X ^ 2 ∂QN (μ : Measure (Torus d)) N =
      ∫ X, ((1 / 2) * (Ψ X ^ 2 * (∑ i ∈ A.s R, lam (i + 1) * fluct eC N i X *
        TR A R (fun n => fluct eC N n X) i
      - ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * ANmat eC N X i j)) +
        (1 / 4) * (Ψ X ^ 2 * ∑ i ∈ A.s R, ∑ j ∈ A.s R, TR A R (fun n => fluct eC N n X) i *
        ANmat eC N X i j * TR A R (fun n => fluct eC N n X) j)) ∂QN (μ : Measure (Torus d)) N := by
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    simp only [VNR]
    ring
  rw [hV, integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul]
  ring

/-! ### E2: the limit of `V_{N,R}` -/

end Schro

end SharpLSI.FL
