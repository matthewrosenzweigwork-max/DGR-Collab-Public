import LeanResearch.PeriodicAttractiveLogGas.FiniteBoxPartition
import LeanResearch.PeriodicAttractiveLogGas.IntegerBoxConditionalEntropy

/-! Actual normalization and drift costs for the source local-box criterion.
The constants and primitive inputs remain explicit. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.FiniteBoxLocalization
open DyadicShellPartition FiniteBoxPartition IntegerBoxMassGeometry
open FiniteEntropyLocalization IntegerBoxConditionalEntropy FiniteGraph FibreEntropy

/-- Primitive global coordinate bounds give the actual capped radius bound. -/
theorem radius_sq_bound {D N : ℕ} (hN : 0 < N) {C : ℝ} (hC : 0 ≤ C)
    (center y : Fin D → ℤ)
    (hy : ∀ i, |((y i - center i : ℤ) : ℝ)| ≤ C * N) :
    radius N center y ^ 2 ≤ C^2 * N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hS : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hn : ‖fun i => ((y i - center i : ℤ) : ℝ)‖ ≤ C * N :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg hC hNr.le)).mpr (by
      intro i; simpa only [Real.norm_eq_abs] using hy i)
  have hr : radius N center y ≤ C * Real.sqrt N := by
    unfold radius
    apply (div_le_iff₀ hS).mpr
    simpa only [mul_assoc, ← pow_two, Real.sq_sqrt hNr.le] using hn
  have hh := (sq_le_sq₀ (radius_nonneg N center y) (mul_nonneg hC hS.le)).mpr hr
  simpa only [mul_pow, Real.sq_sqrt hNr.le] using hh

theorem quadratic_le_capped {ρ N L : ℝ} (hN : 0 ≤ N) (hR : ρ^2 ≤ L*N) :
    1 + ρ^2 ≤ max 1 L * (1 + min (ρ^2) N) := by
  have hm : 1 ≤ max 1 L := le_max_left _ _
  by_cases h : ρ^2 ≤ N
  · rw [min_eq_left h]
    nlinarith [mul_nonneg (show 0 ≤ max 1 L - 1 by linarith) (sq_nonneg ρ)]
  · rw [min_eq_right (by linarith : N ≤ ρ^2)]
    have hh := mul_le_mul_of_nonneg_right (le_max_right 1 L) hN
    nlinarith only [hR, hh, hm]

/-- Additive drift constants are retained; W need not be nonnegative. -/
theorem cost_le_affine_drift {T W q A c C : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (hT : T ≤ A*(1+q)) (hW : c*q-C ≤ W) :
    T ≤ (A/c)*W + A*(1+C/c) := by
  have hh := mul_le_mul_of_nonneg_left hW (div_nonneg hA hc.le)
  have he : A*(1+q) = (A/c)*(c*q-C) + A*(1+C/c) := by
    field_simp
    ring
  rw [he] at hT
  linarith only [hT, hh]

def gammaConstant (D : ℕ) (ε C : ℝ) : ℝ :=
  16 * ((2^(D+1)+1 : ℕ) : ℝ)^2 * variationConstant D ε^2 * C * max 1 (C^2)

theorem gammaConstant_nonneg (D : ℕ) (ε : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ gammaConstant D ε C := by
  unfold gammaConstant
  positivity

theorem source_Gamma_capped {α : Type*} [Fintype α] {D N : ℕ}
    (hN : 1 ≤ N) {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hlarge : 32 ≤ ε * Real.sqrt (N : ℝ))
    (center : Fin D → ℤ) (y : α → Fin D → ℤ) (r : α → α → ℝ)
    (hr : ∀ x z, 0 ≤ r x z)
    (hjump : ∀ x z, r x z ≠ 0 → ∀ i, |y x i-y z i| ≤ 1)
    (x : α) (hrate : (∑ z, r x z) ≤ C*N)
    (hbound : ∀ i, |((y x i-center i : ℤ) : ℝ)| ≤ C*N) :
    localizationCost r (sourceChi N ε center y) x ≤
      gammaConstant D ε C * (1+min (radius N center (y x)^2) (N : ℝ)) := by
  have hR := radius_sq_bound (by omega : 0 < N) hC center (y x) hbound
  have hc := quadratic_le_capped (Nat.cast_nonneg N) hR
  have hh := localizationCost_sourceChi hN hε hlarge hC center y r hr hjump x hrate
  have hm := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ 16 * ((2^(D+1)+1 : ℕ) : ℝ)^2 * variationConstant D ε^2 * C by positivity)
  exact hh.trans (hm.trans_eq (by unfold gammaConstant; ring))

/-- The literal global point lower bound controls its inverse logarithm. -/
theorem global_point_log {D N : ℕ} (hN : 1 ≤ N) {c C p : ℝ}
    (hc : 0 < c) (_hC : 0 ≤ C) (hp : 0 < p)
    (hm : c*(N : ℝ)^(-(D : ℝ)/2)*Real.exp (-C*N) ≤ p) :
    Real.log p⁻¹ ≤ ((D : ℝ) + |Real.log c| + C)*N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow := Real.rpow_pos_of_pos hNr (-(D : ℝ)/2)
  have hh := (Real.log_le_log_iff
    (mul_pos (mul_pos hc hpow) (Real.exp_pos _)) hp).mpr hm
  rw [Real.log_mul (mul_ne_zero hc.ne' hpow.ne') (Real.exp_ne_zero _),
    Real.log_mul hc.ne' hpow.ne', Real.log_rpow hNr, Real.log_exp] at hh
  rw [Real.log_inv]
  have hlog : Real.log (N : ℝ) ≤ N := by linarith [Real.log_le_sub_one_of_pos hNr]
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hd := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (D : ℝ)/2 by positivity)
  have ha := mul_le_mul_of_nonneg_left hN1 (abs_nonneg (Real.log c))
  have hn := mul_nonneg (Nat.cast_nonneg D : (0 : ℝ) ≤ D) hNr.le
  nlinarith [neg_le_abs (Real.log c)]

/-- An active singleton absorbs the particle-size mass cost in its actual radius. -/
theorem tail_point_log {D N : ℕ} (hN : 1 ≤ N) {ε c C p ρ : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hC : 0 ≤ C) (hp : 0 < p)
    (hlarge : 8 ≤ ε * Real.sqrt (N : ℝ))
    (htail : tail (cutoff ε N) ρ ≠ 0)
    (hm : c*(N : ℝ)^(-(D : ℝ)/2)*Real.exp (-C*N) ≤ p) :
    Real.log p⁻¹ ≤
      (256*((D : ℝ)+|Real.log c|+C)/ε^2) * (1+ρ^2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hS : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have ht := (tail_cutoff_radius hlarge htail).le
  have ht0 : 0 ≤ ε * Real.sqrt (N : ℝ)/16 := by positivity
  have hs := (sq_le_sq₀ ht0 (ht0.trans ht)).mpr ht
  rw [div_pow, mul_pow, Real.sq_sqrt hNr.le] at hs
  have hn : (N : ℝ) ≤ 256*(1+ρ^2)/ε^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    nlinarith only [hs]
  have hA : 0 ≤ (D : ℝ)+|Real.log c|+C := by positivity
  have hh := mul_le_mul_of_nonneg_left hn hA
  exact (global_point_log hN hc hC hp hm).trans (hh.trans_eq (by ring))

/-- The actual finite index family, including zero pieces. -/
abbrev SourceIndex {D : ℕ} (N : ℕ) (ε : ℝ) (Ω : Finset (Fin D → ℤ)) (x₀ : ↥Ω) :=
  Index ↥Ω D (queryBound x₀.val (fun x : ↥Ω => x.val)) (cutoff ε N)

/-- Inactive box pieces use a harmless positive singleton block. The function
itself is still the literal zero source piece, so no artificial box law enters. -/
def blocks {D : ℕ} (N : ℕ) (ε : ℝ) (Ω : Finset (Fin D → ℤ)) (x₀ : ↥Ω)
    (i : SourceIndex N ε Ω x₀) : Finset ↥Ω := by
  classical
  exact match i with
  | Sum.inl (j,c) =>
    if ∃ x, sourcePieces N ε x₀.val (fun z : ↥Ω => z.val) (Sum.inl (j,c)) x ≠ 0 then
      boxInOuter Ω (scale N j.val) x₀.val (fun k => (c k).val)
    else {x₀}
  | Sum.inr z => {z}

theorem sourceChi_ne_zero_piece {α : Type*} [Fintype α] {D N : ℕ}
    (ε : ℝ) (center : Fin D → ℤ) (y : α → Fin D → ℤ)
    (i : Index α D (queryBound center y) (cutoff ε N)) (x : α)
    (hx : sourceChi N ε center y i x ≠ 0) :
    sourcePieces N ε center y i x ≠ 0 := by
  intro hz
  exact hx (FiniteSquaredPartition.partition_eq_zero _ _ _ hz)

theorem active_box_data {D N : ℕ} (ε : ℝ) (Ω : Finset (Fin D → ℤ)) (x₀ x : ↥Ω)
    (j : Fin (cutoff ε N + 1))
    (c : ProductTentPartition.Centers D (queryBound x₀.val (fun z : ↥Ω => z.val)))
    (hx : sourcePieces N ε x₀.val (fun z : ↥Ω => z.val) (Sum.inl (j,c)) x ≠ 0) :
    shell j.val (radius N x₀.val x.val) ≠ 0 ∧
      ProductTentPartition.productTent (scale N j.val) (fun k => (c k).val)
        (fun k => x.val k-x₀.val k) ≠ 0 :=
  mul_ne_zero_iff.mp hx

theorem blocks_nonempty {D N : ℕ} (hN : 0 < N) (ε : ℝ)
    (Ω : Finset (Fin D → ℤ)) (x₀ : ↥Ω) (i : SourceIndex N ε Ω x₀) :
    (blocks N ε Ω x₀ i).Nonempty := by
  classical
  rcases i with ⟨j,c⟩ | z
  · by_cases ha : ∃ x, sourcePieces N ε x₀.val (fun z : ↥Ω => z.val)
        (Sum.inl (j,c)) x ≠ 0
    · obtain ⟨x,hx⟩ := ha
      have ha : ∃ z, sourcePieces N ε x₀.val (fun z : ↥Ω => z.val)
          (Sum.inl (j,c)) z ≠ 0 := ⟨x,hx⟩
      have ht := (active_box_data ε Ω x₀ x j c hx).2
      refine ⟨x, ?_⟩
      simp only [blocks, ite_eq_left ha, boxInOuter, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact tent_mem_containingBox (scale_pos hN j.val) _ _ _ ht
    · simpa only [blocks, ite_eq_right ha] using Finset.singleton_nonempty x₀
  · simpa only [blocks] using Finset.singleton_nonempty z

theorem sourceChi_block_support {D N : ℕ} (hN : 0 < N) (ε : ℝ)
    (Ω : Finset (Fin D → ℤ)) (x₀ : ↥Ω) (i : SourceIndex N ε Ω x₀) (x : ↥Ω)
    (hx : x ∉ blocks N ε Ω x₀ i) :
    sourceChi N ε x₀.val (fun z : ↥Ω => z.val) i x = 0 := by
  classical
  by_contra hn
  have hg := sourceChi_ne_zero_piece ε x₀.val (fun z : ↥Ω => z.val) i x hn
  apply hx
  rcases i with ⟨j,c⟩ | z
  · have ht := (active_box_data ε Ω x₀ x j c hg).2
    have ha : ∃ z, sourcePieces N ε x₀.val (fun z : ↥Ω => z.val)
        (Sum.inl (j,c)) z ≠ 0 := ⟨x,hg⟩
    simp only [blocks, ite_eq_left ha, boxInOuter, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact tent_mem_containingBox (scale_pos hN j.val) _ _ _ ht
  · have hz := chi_singleton_support (R := queryBound x₀.val (fun z : ↥Ω => z.val))
      (fun j => scale N j.val) (fun z : ↥Ω => radius N x₀.val z.val)
      (fun z : ↥Ω => fun k => z.val k-x₀.val k) z x hn
    simpa only [blocks, Finset.mem_singleton] using hz.1

theorem conditional_energy_nonneg {α : Type*} [Fintype α] (w F : α → ℝ)
    (r : α → α → ℝ) (B : Finset α) (hw : ∀ x, 0 ≤ w x) (hr : ∀ x z, 0 ≤ r x z) :
    0 ≤ energy (conditionalWeight w B) (restrictedRates r B) F := by
  classical
  unfold energy
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro z _
  apply mul_nonneg _ (sq_nonneg _)
  apply mul_nonneg (conditionalWeight_nonneg w B hw x)
  unfold restrictedRates
  split_ifs
  · exact hr x z
  · exact le_rfl

def localConstant (D : ℕ) (C c : ℝ) : ℝ :=
  9*Real.exp (40*D*C)*(2+1/Real.exp 1)/c

theorem localConstant_nonneg (D : ℕ) (C : ℝ) {c : ℝ} (hc : 0 < c) :
    0 ≤ localConstant D C c := by
  unfold localConstant
  positivity

theorem singleton_lsi {α : Type*} [Fintype α] (w F : α → ℝ)
    (r : α → α → ℝ) (x : α) (hw : ∀ x, 0 < w x) (hr : ∀ x z, 0 ≤ r x z)
    {A : ℝ} (hA : 0 ≤ A) :
    finiteEntropy (conditionalWeight w {x}) (fun z => F z^2) ≤
      A * energy (conditionalWeight w {x}) (restrictedRates r {x}) F := by
  rw [singleton_conditional_entropy _ _ x (hw x)]
  exact mul_nonneg hA (conditional_energy_nonneg w F r {x} (fun z => (hw z).le) hr)

/-- Every block in the actual finite family satisfies its conditional LSI.
Inactive box indices and tail indices use their genuine singleton law. -/
theorem blocks_conditional_lsi {D N : ℕ} (hN : 1 ≤ N) {ε C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hlarge : 8 ≤ ε * Real.sqrt (N : ℝ))
    (Ω : Finset (Fin D → ℤ)) (x₀ : ↥Ω) (w : (Fin D → ℤ) → ℝ)
    (F : ↥Ω → ℝ) (r : ↥Ω → ↥Ω → ℝ)
    (hΩ : ∀ z, (∀ i, |((z i-x₀.val i : ℤ) : ℝ)| ≤ 2*ε*N) → z ∈ Ω)
    (hw : ∀ z ∈ Ω, 0 < w z) (hr : ∀ x z, 0 ≤ r x z)
    (hbal : ∀ x z : ↥Ω, w x.val * r x z = w z.val * r z x)
    (hinc : LogIncrementBound x₀.val (2*ε*N) N C w)
    (hcoord : ∀ x z : ↥Ω,
      (∀ k, |((x.val k-x₀.val k : ℤ) : ℝ)| ≤ 2*ε*N) →
      (∀ k, |((z.val k-x₀.val k : ℤ) : ℝ)| ≤ 2*ε*N) →
      ∀ k, z.val = Function.update x.val k (x.val k+1) → c*N ≤ r x z)
    (i : SourceIndex N ε Ω x₀) :
    finiteEntropy (conditionalWeight (fun z : ↥Ω => w z.val) (blocks N ε Ω x₀ i))
        (fun z => F z^2) ≤
      localConstant D C c *
        energy (conditionalWeight (fun z : ↥Ω => w z.val) (blocks N ε Ω x₀ i))
          (restrictedRates r (blocks N ε Ω x₀ i)) F := by
  classical
  have hw' : ∀ z : ↥Ω, 0 < w z.val := fun z => hw z.val z.property
  have hA := localConstant_nonneg D C hc
  rcases i with ⟨j,b⟩ | z
  · by_cases ha : ∃ x, sourcePieces N ε x₀.val (fun z : ↥Ω => z.val)
        (Sum.inl (j,b)) x ≠ 0
    · obtain ⟨x,hx⟩ := ha
      have ha : ∃ z, sourcePieces N ε x₀.val (fun z : ↥Ω => z.val)
          (Sum.inl (j,b)) z ≠ 0 := ⟨x,hx⟩
      have hd := active_box_data ε Ω x₀ x j b hx
      simp only [blocks, ite_eq_left ha]
      exact source_conditional_box_lsi hN hC hc hlarge (by omega) Ω x₀.val
        (fun k => (b k).val) x.val w F r hΩ hd.1 hd.2 hw hr hbal hinc hcoord
    · simp only [blocks, ite_eq_right ha]
      exact singleton_lsi _ F r x₀ hw' hr hA
  · simp only [blocks]
    exact singleton_lsi _ F r z hw' hr hA

def thetaConstant (D : ℕ) (ε C c : ℝ) : ℝ :=
  ((D : ℝ)*(Real.log 2+1)+|Real.log c|+132*D*C) +
    256*((D : ℝ)+|Real.log c|+C)/ε^2

theorem thetaConstant_nonneg (D : ℕ) (ε c : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ thetaConstant D ε C c := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold thetaConstant
  positivity

/-- Actual box volumes cancel the log N cost. Only active singleton pieces
use the global exponential lower mass, and their radius absorbs that cost. -/
theorem source_Theta {D N : ℕ} (hN : 1 ≤ N) {ε C c : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C) (hc : 0 < c)
    (hlarge : 8 ≤ ε * Real.sqrt (N : ℝ))
    (Ω : Finset (Fin D → ℤ)) (x₀ : ↥Ω) (w : (Fin D → ℤ) → ℝ)
    (hΩ : ∀ z, (∀ k, |((z k-x₀.val k : ℤ) : ℝ)| ≤ 2*ε*N) → z ∈ Ω)
    (hw : ∀ z ∈ Ω, 0 < w z)
    (hcenter : c*(N : ℝ)^(-(D : ℝ)/2) ≤ w x₀.val)
    (hinc : LogIncrementBound x₀.val (2*ε*N) N C w) (x : ↥Ω)
    (hglobal : c*(N : ℝ)^(-(D : ℝ)/2)*Real.exp (-C*N) ≤ w x.val) :
    normalizationCost (fun z : ↥Ω => w z.val) (blocks N ε Ω x₀)
      (sourceChi N ε x₀.val (fun z : ↥Ω => z.val)) x ≤
        thetaConstant D ε C c * (1+radius N x₀.val x.val^2) := by
  classical
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hb : 0 ≤ (D : ℝ)*(Real.log 2+1)+|Real.log c|+132*D*C := by positivity
  have ht : 0 ≤ 256*((D : ℝ)+|Real.log c|+C)/ε^2 := by positivity
  have hbθ : (D : ℝ)*(Real.log 2+1)+|Real.log c|+132*D*C ≤
      thetaConstant D ε C c := by unfold thetaConstant; linarith only [ht]
  have htθ : 256*((D : ℝ)+|Real.log c|+C)/ε^2 ≤
      thetaConstant D ε C c := by unfold thetaConstant; linarith only [hb]
  have hrho : 0 ≤ 1+radius N x₀.val x.val^2 := by positivity
  have hpoint (i : SourceIndex N ε Ω x₀)
      (hi : sourceChi N ε x₀.val (fun z : ↥Ω => z.val) i x ≠ 0) :
      Real.log (setMass (fun z : ↥Ω => w z.val) (blocks N ε Ω x₀ i))⁻¹ ≤
        thetaConstant D ε C c * (1+radius N x₀.val x.val^2) := by
    have hg := sourceChi_ne_zero_piece ε x₀.val (fun z : ↥Ω => z.val) i x hi
    rcases i with ⟨j,b⟩ | z
    · have hd := active_box_data ε Ω x₀ x j b hg
      have ha : ∃ z, sourcePieces N ε x₀.val (fun z : ↥Ω => z.val)
          (Sum.inl (j,b)) z ≠ 0 := ⟨x,hg⟩
      simp only [blocks, ite_eq_left ha]
      have hh := (source_outer_box_normalization hN hε.le hC hc hlarge (by omega)
        Ω x₀.val (fun k => (b k).val) x.val w hΩ hd.1 hd.2 hw hcenter hinc).2
      exact hh.trans (mul_le_mul_of_nonneg_right hbθ hrho)
    · have hz := chi_singleton_support (R := queryBound x₀.val (fun z : ↥Ω => z.val))
        (fun j => scale N j.val) (fun z : ↥Ω => radius N x₀.val z.val)
        (fun z : ↥Ω => fun k => z.val k-x₀.val k) z x hi
      obtain ⟨rfl,htail⟩ := hz
      have hM : setMass (fun z : ↥Ω => w z.val) {x} = w x.val := by
        simp [setMass, restrictedWeight]
      simp only [blocks, hM]
      exact (tail_point_log hN hε hc hC (hw x.val x.property) hlarge htail hglobal).trans
        (mul_le_mul_of_nonneg_right htθ hrho)
  calc
    _ ≤ ∑ i : SourceIndex N ε Ω x₀,
        sourceChi N ε x₀.val (fun z : ↥Ω => z.val) i x^2 *
          (thetaConstant D ε C c * (1+radius N x₀.val x.val^2)) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : sourceChi N ε x₀.val (fun z : ↥Ω => z.val) i x = 0
      · simp only [hi, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left (hpoint i hi) (sq_nonneg _)
    _ = _ := by
      rw [← Finset.sum_mul, sourceChi_sq_sum (by omega : 0 < N), one_mul]

theorem source_Theta_capped {D N : ℕ} (hN : 1 ≤ N) {ε C c : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C) (hc : 0 < c)
    (hlarge : 8 ≤ ε * Real.sqrt (N : ℝ))
    (Ω : Finset (Fin D → ℤ)) (x₀ : ↥Ω) (w : (Fin D → ℤ) → ℝ)
    (hΩ : ∀ z, (∀ k, |((z k-x₀.val k : ℤ) : ℝ)| ≤ 2*ε*N) → z ∈ Ω)
    (hw : ∀ z ∈ Ω, 0 < w z)
    (hcenter : c*(N : ℝ)^(-(D : ℝ)/2) ≤ w x₀.val)
    (hinc : LogIncrementBound x₀.val (2*ε*N) N C w) (x : ↥Ω)
    (hglobal : c*(N : ℝ)^(-(D : ℝ)/2)*Real.exp (-C*N) ≤ w x.val)
    (hbound : ∀ k, |((x.val k-x₀.val k : ℤ) : ℝ)| ≤ C*N) :
    normalizationCost (fun z : ↥Ω => w z.val) (blocks N ε Ω x₀)
      (sourceChi N ε x₀.val (fun z : ↥Ω => z.val)) x ≤
        (thetaConstant D ε C c * max 1 (C^2)) *
          (1+min (radius N x₀.val x.val^2) (N : ℝ)) := by
  have hh := source_Theta hN hε hC hc hlarge Ω x₀ w hΩ hw hcenter hinc x hglobal
  have hR := radius_sq_bound (by omega : 0 < N) hC x₀.val x.val hbound
  have hq := quadratic_le_capped (Nat.cast_nonneg N) hR
  exact hh.trans ((mul_le_mul_of_nonneg_left hq (thetaConstant_nonneg D ε c hC)).trans_eq
    (by ring))

/-- Coefficients depend only on the fixed data, never on N or the finite domain. -/
def entropyConstant (D : ℕ) (ε C c : ℝ) : ℝ :=
  localConstant D C c * (2+gammaConstant D ε C/c) +
    thetaConstant D ε C c * max 1 (C^2)/c

def defectConstant (D : ℕ) (ε C c : ℝ) : ℝ :=
  (localConstant D C c * gammaConstant D ε C + thetaConstant D ε C c * max 1 (C^2)) *
    (1+C/c)

theorem constants_nonneg (D : ℕ) (ε : ℝ) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    0 ≤ entropyConstant D ε C c ∧ 0 ≤ defectConstant D ε C c := by
  have hL := localConstant_nonneg D C hc
  have hG := gammaConstant_nonneg D ε hC
  have hT := thetaConstant_nonneg D ε c hC
  constructor <;> dsimp only [entropyConstant, defectConstant] <;> positivity

/-- Explicit fixed large-particle threshold used by the actual tail partition. -/
def particleThreshold (ε : ℝ) : ℕ := max 1 ⌈(32/ε)^2⌉₊

theorem particleThreshold_bounds {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (hN : particleThreshold ε ≤ N) : 1 ≤ N ∧ 32 ≤ ε*Real.sqrt (N : ℝ) := by
  have h1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hn : (⌈(32/ε)^2⌉₊ : ℝ) ≤ N := by
    exact_mod_cast (le_max_right 1 ⌈(32/ε)^2⌉₊).trans hN
  have hsq : (32/ε)^2 ≤ (N : ℝ) := (Nat.le_ceil _).trans hn
  have hS : 32/ε ≤ Real.sqrt (N : ℝ) := by
    nlinarith [Real.sqrt_nonneg (N : ℝ), Real.sq_sqrt (Nat.cast_nonneg N)]
  have hh := mul_le_mul_of_nonneg_left hS hε.le
  have he : ε*(32/ε) = 32 := by field_simp
  exact ⟨h1, he ▸ hh⟩

/-- The actual local-box criterion with all four primitive source assumptions.
The entire outer graph is used. The mass and inner-cube hypotheses are retained
as in the source even where the stronger finite algebra does not need them. -/
theorem local_box_criterion {D N : ℕ} (_hD : 1 ≤ D) {ε C c : ℝ}
    (hε : 0 < ε) (hC : 0 < C) (hc : 0 < c)
    (hN : particleThreshold ε ≤ N)
    (Ω : Finset (Fin D → ℤ)) (x₀ : ↥Ω) (K : Finset ↥Ω)
    (w : (Fin D → ℤ) → ℝ) (F V : ↥Ω → ℝ) (r : ↥Ω → ↥Ω → ℝ)
    (_hx₀ : x₀ ∈ K) (hw : ∀ z ∈ Ω, 0 < w z)
    (_hmass : (∑ z : ↥Ω, w z.val) ≤ 1)
    (hr : ∀ x z, 0 ≤ r x z)
    (hbal : ∀ x z : ↥Ω, w x.val*r x z = w z.val*r z x)
    (hbound : ∀ x : ↥Ω, ∀ k, |((x.val k-x₀.val k : ℤ) : ℝ)| ≤ C*N)
    (hjump : ∀ x z, r x z ≠ 0 → ∀ k, |x.val k-z.val k| ≤ 1)
    (hrate : ∀ x, (∑ z, r x z) ≤ C*N)
    (hΩ : ∀ z, (∀ k, |((z k-x₀.val k : ℤ) : ℝ)| ≤ 2*ε*N) → z ∈ Ω)
    (_hK : ∀ x : ↥Ω, (∀ k, |((x.val k-x₀.val k : ℤ) : ℝ)| ≤ 2*ε*N) → x ∈ K)
    (hcoord : ∀ x z : ↥Ω,
      (∀ k, |((x.val k-x₀.val k : ℤ) : ℝ)| ≤ 2*ε*N) →
      (∀ k, |((z.val k-x₀.val k : ℤ) : ℝ)| ≤ 2*ε*N) →
      ∀ k, z.val = Function.update x.val k (x.val k+1) → c*N ≤ r x z)
    (hinc : LogIncrementBound x₀.val (2*ε*N) N C w)
    (hcenter : c*(N : ℝ)^(-(D : ℝ)/2) ≤ w x₀.val)
    (hglobal : ∀ x ∈ K, c*(N : ℝ)^(-(D : ℝ)/2)*Real.exp (-C*N) ≤ w x.val)
    (hV : ∀ x, 0 < V x)
    (hdrift : ∀ x ∈ K, c*min (radius N x₀.val x.val^2) (N : ℝ)-C ≤
      groundStatePotential r V x)
    (hF : ∀ x, x ∉ K → F x = 0) :
    finiteEntropy (fun z : ↥Ω => w z.val) (fun z => F z^2) ≤
      entropyConstant D ε C c * energy (fun z : ↥Ω => w z.val) r F +
        defectConstant D ε C c * ∑ z : ↥Ω, w z.val*F z^2 := by
  classical
  obtain ⟨hN1,hlarge⟩ := particleThreshold_bounds hε hN
  have h8 : 8 ≤ ε*Real.sqrt (N : ℝ) := by linarith only [hlarge]
  let χ := sourceChi N ε x₀.val (fun z : ↥Ω => z.val)
  let B := blocks N ε Ω x₀
  let A₁ := thetaConstant D ε C c * max 1 (C^2)
  let A₂ := gammaConstant D ε C
  have hA₁ : 0 ≤ A₁ := mul_nonneg (thetaConstant_nonneg D ε c hC.le) (by positivity)
  have hA₂ : 0 ≤ A₂ := gammaConstant_nonneg D ε hC.le
  have hTheta : ∀ x ∈ K, normalizationCost (fun z : ↥Ω => w z.val) B χ x ≤
      (A₁/c)*groundStatePotential r V x + A₁*(1+C/c) := by
    intro x hx
    apply cost_le_affine_drift hA₁ hc _ (hdrift x hx)
    exact source_Theta_capped hN1 hε hC.le hc h8 Ω x₀ w hΩ hw hcenter hinc x
      (hglobal x hx) (hbound x)
  have hGamma : ∀ x ∈ K, localizationCost r χ x ≤
      (A₂/c)*groundStatePotential r V x + A₂*(1+C/c) := by
    intro x hx
    apply cost_le_affine_drift hA₂ hc _ (hdrift x hx)
    exact source_Gamma_capped hN1 hε hC.le hlarge x₀.val (fun z : ↥Ω => z.val)
      r hr hjump x (hrate x) (hbound x)
  have hh := entropy_from_localization (fun z : ↥Ω => w z.val) F V r K B χ
    (fun z => hw z.val z.property) hr hbal hV (localConstant_nonneg D C hc)
    (div_nonneg hA₁ hc.le) (div_nonneg hA₂ hc.le)
    (blocks_nonempty (by omega : 0 < N) ε Ω x₀)
    (sourceChi_sq_sum (by omega : 0 < N) ε x₀.val (fun z : ↥Ω => z.val))
    (sourceChi_block_support (by omega : 0 < N) ε Ω x₀) hF
    (fun i => blocks_conditional_lsi hN1 hC.le hc h8 Ω x₀ w (fun z => χ i z*F z)
      r hΩ hw hr hbal hinc hcoord i) hTheta hGamma
  have he : localConstant D C c * (A₂*(1+C/c)) + A₁*(1+C/c) =
      defectConstant D ε C c := by
    dsimp only [A₁, A₂, defectConstant]
    ring
  simpa only [A₁, A₂, entropyConstant, he] using hh

end PeriodicAttractiveLogGas.FiniteBoxLocalization
