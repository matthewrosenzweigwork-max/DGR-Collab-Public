import FullLabeledLSI.Paper.Prop23SchroA
import FullLabeledLSI.Paper.Sec6MomentsZ

/-! # Prop 2.3 WP-E2: the limit of V_{N,R} -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-! ### Generic auxiliary lemmas (no hypotheses on the minimizer) -/

section SchroCAux

instance schroC_isProb (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (N : ℕ) :
    IsProbabilityMeasure (QN μ N) := by
  unfold QN; infer_instance

/-- `∑_l g(X_l)` is measurable and bounded (hence in `L^∞`). -/
theorem schroC_sum_memLp {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {g : Torus d → ℝ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) (N : ℕ) :
    Measurable (fun X : Config N d => ∑ l, g (X l)) ∧
      MemLp (fun X : Config N d => ∑ l, g (X l)) ∞ (QN μ N) := by
  have hm : Measurable (fun X : Config N d => ∑ l, g (X l)) :=
    Finset.measurable_sum _ fun l _ => hg.comp (measurable_pi_apply l)
  refine ⟨hm, memLp_top_of_bound hm.aestronglyMeasurable (N * B) (Eventually.of_forall fun X => ?_)⟩
  rw [Real.norm_eq_abs]
  calc |∑ l, g (X l)| ≤ ∑ l, |g (X l)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin N, B := Finset.sum_le_sum fun l _ => hB _
    _ = N * B := by simp

/-- An `L^∞` function with `∫ f^{2k} ≤ C` has `L^{p}` norm `≤ C^{1/p}`, `p = 2k`. -/
theorem schroC_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {f : Ω → ℝ} (hf : MemLp f ∞ ν) (k p : ℕ) (hp : p = 2 * k) (hk : 0 < k) {C : ℝ}
    (hC : ∫ x, f x ^ (2 * k) ∂ν ≤ C) :
    eLpNorm f (p : ℝ≥0∞) ν ≤ ENNReal.ofReal (C ^ (1 / (p : ℝ))) := by
  subst hp
  have hk' : (2 * k : ℕ) ≠ 0 := by omega
  have hp0 : ((2 * k : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk'
  have hptop : ((2 * k : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hmem : MemLp f ((2 * k : ℕ) : ℝ≥0∞) ν := hf.mono_exponent le_top
  have heven : Even (2 * k) := ⟨k, by ring⟩
  have hint : Integrable (fun x => f x ^ (2 * k)) ν := by
    have := hmem.integrable_norm_pow hk'
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs]
    exact heven.pow_abs _
  have hnn : ∀ x, 0 ≤ f x ^ (2 * k) := fun x => heven.pow_nonneg _
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_natCast]
  have h1 : ∀ x, ‖f x‖ₑ ^ ((2 * k : ℕ) : ℝ) = ENNReal.ofReal (f x ^ (2 * k)) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by positivity),
      Real.rpow_natCast, heven.pow_abs]
  simp_rw [h1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn),
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hnn) (by positivity)]
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow (integral_nonneg hnn) hC (by positivity))

theorem schroC_holder_nat (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a : ℝ)⁻¹ + (b : ℝ)⁻¹ = (c : ℝ)⁻¹) :
    ENNReal.HolderTriple (a : ℝ≥0∞) (b : ℝ≥0∞) (c : ℝ≥0∞) := by
  have key : ∀ n : ℕ, 0 < n → (n : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((n : ℝ)⁻¹) := fun n hn => by
    rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast]
  constructor
  rw [key a ha, key b hb, key c hc, ← ENNReal.ofReal_add (by positivity) (by positivity), h]

theorem schroC_holder {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {p q r : ℝ≥0∞}
    [ENNReal.HolderTriple p q r] {φ f : Ω → ℝ} (hφ : AEStronglyMeasurable φ ν)
    (hf : AEStronglyMeasurable f ν) :
    eLpNorm (fun x => φ x * f x) r ν ≤ eLpNorm φ p ν * eLpNorm f q ν :=
  eLpNorm_smul_le_mul_eLpNorm hφ hf

theorem schroC_eLpNorm_const_mul {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (c : ℝ)
    (f : Ω → ℝ) (p : ℝ≥0∞) : eLpNorm (fun x => c * f x) p ν = ‖c‖ₑ * eLpNorm f p ν :=
  eLpNorm_const_smul c f p ν

theorem schroC_eLpNorm_lin {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (s : Finset ℕ)
    (c : ℕ → ℝ) (f : ℕ → Ω → ℝ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    eLpNorm (fun x => ∑ m ∈ s, c m * f m x) p ν ≤ ∑ m ∈ s, ‖c m‖ₑ * eLpNorm (f m) p ν := by
  calc eLpNorm (fun x => ∑ m ∈ s, c m * f m x) p ν
      = eLpNorm (∑ m ∈ s, (fun x => c m * f m x)) p ν := by
        rw [← Finset.sum_fn]
    _ ≤ ∑ m ∈ s, eLpNorm (fun x => c m * f m x) p ν := eLpNorm_sum_le hp
    _ = ∑ m ∈ s, ‖c m‖ₑ * eLpNorm (f m) p ν :=
        Finset.sum_congr rfl fun m _ => schroC_eLpNorm_const_mul ν _ _ _

theorem schroC_tendsto_sum {ι : Type*} (s : Finset ι) (f : ι → (N : ℕ) → Config N d → ℝ)
    (ν : (N : ℕ) → Measure (Config N d)) (q : ℝ≥0∞) (hq1 : 1 ≤ q)
    (h : ∀ i ∈ s, Tendsto (fun N => eLpNorm (f i N) q (ν N)) atTop (𝓝 0)) :
    Tendsto (fun N => eLpNorm (fun X => ∑ i ∈ s, f i N X) q (ν N)) atTop (𝓝 0) := by
  have hsum : Tendsto (fun N => ∑ i ∈ s, eLpNorm (f i N) q (ν N)) atTop (𝓝 (∑ _i ∈ s, (0 : ℝ≥0∞))) :=
    tendsto_finsetSum s h
  simp only [Finset.sum_const_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun N => zero_le)
    (fun N => ?_)
  calc eLpNorm (fun X => ∑ i ∈ s, f i N X) q (ν N)
      = eLpNorm (∑ i ∈ s, f i N) q (ν N) := by rw [← Finset.sum_fn]
    _ ≤ ∑ i ∈ s, eLpNorm (f i N) q (ν N) := eLpNorm_sum_le hq1

/-- Measurability of the error expression. -/
theorem schroC_F_meas (s : Finset ℕ) (a : ℕ → ℕ → ℝ)
    (Z : ℕ → (N : ℕ) → Config N d → ℝ) (D : ℕ → ℕ → (N : ℕ) → Config N d → ℝ)
    (hZm : ∀ n N, Measurable (Z n N)) (hDm : ∀ i j N, Measurable (D i j N)) (N : ℕ) :
    Measurable (fun X : Config N d =>
        (1 / 4 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, (∑ m ∈ s, a i m * Z m N X) * D i j N X *
            (∑ m ∈ s, a j m * Z m N X)
          - (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, a i j * D i j N X) := by
  refine (Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun j _ => ?_) _).sub (Measurable.const_mul
      (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_) _)
  · exact ((Finset.measurable_sum _ fun m _ => (hZm m N).const_mul _).mul (hDm i j N)).mul
      (Finset.measurable_sum _ fun m _ => (hZm m N).const_mul _)
  · exact (hDm i j N).const_mul _

/-- **Main estimate (abstract)**: three-factor Hölder with even moments. -/
theorem schroC_main {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (s : Finset ℕ) (a : ℕ → ℕ → ℝ)
    (Z : ℕ → (N : ℕ) → Config N d → ℝ) (D : ℕ → ℕ → (N : ℕ) → Config N d → ℝ)
    (hZm : ∀ n N, Measurable (Z n N)) (hZb : ∀ n N, MemLp (Z n N) ∞ (QN μ N))
    (hZmom : ∀ n k, ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∫ X, (Z n N X) ^ (2 * k) ∂QN μ N ≤ C)
    (hDm : ∀ i j N, Measurable (D i j N)) (hDb : ∀ i j N, MemLp (D i j N) ∞ (QN μ N))
    (hDmom : ∀ i j k, ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∫ X, (D i j N X) ^ (2 * k) ∂QN μ N ≤ C * ((N : ℝ)⁻¹) ^ k)
    (q : ℝ≥0∞) (hq1 : 1 ≤ q) (hq : q ≠ ⊤) :
    Tendsto (fun N : ℕ => eLpNorm (fun X : Config N d =>
        (1 / 4 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, (∑ m ∈ s, a i m * Z m N X) * D i j N X *
            (∑ m ∈ s, a j m * Z m N X)
          - (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, a i j * D i j N X) q (QN μ N)) atTop (𝓝 0) := by
  obtain ⟨n0, hn0⟩ := ENNReal.exists_nat_gt hq
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = n0 + 1 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = 2 * (3 * M) := ⟨_, rfl⟩
  have hqP2 : q ≤ ((2 * M : ℕ) : ℝ≥0∞) :=
    hn0.le.trans (by exact_mod_cast (by omega : n0 ≤ 2 * M))
  have h2MP : ((2 * M : ℕ) : ℝ≥0∞) ≤ (P : ℝ≥0∞) := by exact_mod_cast (by omega : 2 * M ≤ P)
  have hqP : q ≤ (P : ℝ≥0∞) := hqP2.trans h2MP
  have hP1 : (1 : ℝ≥0∞) ≤ (P : ℝ≥0∞) := by exact_mod_cast (by omega : 1 ≤ P)
  have h1 : ENNReal.HolderTriple ((3 * M : ℕ) : ℝ≥0∞) (P : ℝ≥0∞) ((2 * M : ℕ) : ℝ≥0∞) :=
    schroC_holder_nat _ _ _ (by omega) (by omega) (by omega) (by
      have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
      rw [hP]; push_cast; field_simp; ring)
  have h2 : ENNReal.HolderTriple (P : ℝ≥0∞) (P : ℝ≥0∞) ((3 * M : ℕ) : ℝ≥0∞) :=
    schroC_holder_nat _ _ _ (by omega) (by omega) (by omega) (by
      have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
      rw [hP]; push_cast; field_simp; ring)
  -- `D` tends to zero in `L^P`
  have hDt : ∀ i j, Tendsto (fun N : ℕ => eLpNorm (D i j N) (P : ℝ≥0∞) (QN μ N)) atTop (𝓝 0) := by
    intro i j
    obtain ⟨C, hC⟩ := hDmom i j (3 * M)
    have hlim : Tendsto (fun N : ℕ => ENNReal.ofReal
        ((C * ((N : ℝ)⁻¹) ^ (3 * M)) ^ (1 / (P : ℝ)))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun N : ℕ => C * ((N : ℝ)⁻¹) ^ (3 * M)) atTop (𝓝 (C * 0 ^ (3 * M))) :=
        ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).pow (3 * M)).const_mul C
      have h1 := h0.rpow_const (p := 1 / (P : ℝ)) (Or.inr (by positivity))
      have h3 := ENNReal.tendsto_ofReal h1
      have hPpos : (0 : ℝ) < 1 / (P : ℝ) := by
        have : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
        positivity
      have hz : (C * (0 : ℝ) ^ (3 * M)) ^ (1 / (P : ℝ)) = 0 := by
        rw [zero_pow (by omega), mul_zero, Real.zero_rpow hPpos.ne']
      rw [hz, ENNReal.ofReal_zero] at h3
      exact h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun N => zero_le) ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact schroC_eLpNorm_le (hDb i j N) (3 * M) P hP (by omega) (hC N hN)
  -- uniform bound on `Z` in `L^P`
  choose C hC using fun m => hZmom m (3 * M)
  set K : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal ((C m) ^ (1 / (P : ℝ))) with hK
  have hZbd : ∀ m N, 1 ≤ N → eLpNorm (Z m N) (P : ℝ≥0∞) (QN μ N) ≤ K m := fun m N hN =>
    schroC_eLpNorm_le (hZb m N) (3 * M) P hP (by omega) (hC m N hN)
  set KT : ℕ → ℝ≥0∞ := fun i => ∑ m ∈ s, ‖a i m‖ₑ * K m with hKT
  have hKTtop : ∀ i, KT i ≠ ⊤ := fun i =>
    (ENNReal.sum_lt_top.2 fun m _ => ENNReal.mul_lt_top enorm_lt_top ENNReal.ofReal_lt_top).ne
  have hTbd : ∀ i N, 1 ≤ N →
      eLpNorm (fun X : Config N d => ∑ m ∈ s, a i m * Z m N X) (P : ℝ≥0∞) (QN μ N) ≤ KT i :=
    fun i N hN =>
      (schroC_eLpNorm_lin (QN μ N) s (a i) (fun m => Z m N) _ hP1).trans
        (Finset.sum_le_sum fun m _ => by gcongr; exact hZbd m N hN)
  have hTm : ∀ i N, Measurable (fun X : Config N d => ∑ m ∈ s, a i m * Z m N X) :=
    fun i N => Finset.measurable_sum _ fun m _ => (hZm m N).const_mul _
  -- the cubic terms
  have hterm : ∀ i ∈ s, ∀ j ∈ s, Tendsto (fun N : ℕ => eLpNorm (fun X : Config N d =>
      (∑ m ∈ s, a i m * Z m N X) * D i j N X * (∑ m ∈ s, a j m * Z m N X)) q (QN μ N))
      atTop (𝓝 0) := by
    intro i _ j _
    have hlim : Tendsto (fun N : ℕ => KT i * eLpNorm (D i j N) (P : ℝ≥0∞) (QN μ N) * KT j)
        atTop (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const
        (ENNReal.Tendsto.const_mul (hDt i j) (Or.inr (hKTtop i))) (Or.inr (hKTtop j))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun N => zero_le) ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    calc eLpNorm (fun X : Config N d =>
          (∑ m ∈ s, a i m * Z m N X) * D i j N X * (∑ m ∈ s, a j m * Z m N X)) q (QN μ N)
        ≤ eLpNorm (fun X : Config N d =>
          (∑ m ∈ s, a i m * Z m N X) * D i j N X * (∑ m ∈ s, a j m * Z m N X))
            ((2 * M : ℕ) : ℝ≥0∞) (QN μ N) := eLpNorm_le_eLpNorm_of_exponent_le hqP2
      _ ≤ eLpNorm (fun X : Config N d => (∑ m ∈ s, a i m * Z m N X) * D i j N X)
            ((3 * M : ℕ) : ℝ≥0∞) (QN μ N) *
          eLpNorm (fun X : Config N d => ∑ m ∈ s, a j m * Z m N X) (P : ℝ≥0∞) (QN μ N) :=
        schroC_holder ((((hTm i N).mul (hDm i j N))).aestronglyMeasurable)
          ((hTm j N).aestronglyMeasurable)
      _ ≤ (eLpNorm (fun X : Config N d => ∑ m ∈ s, a i m * Z m N X) (P : ℝ≥0∞) (QN μ N) *
            eLpNorm (D i j N) (P : ℝ≥0∞) (QN μ N)) *
          eLpNorm (fun X : Config N d => ∑ m ∈ s, a j m * Z m N X) (P : ℝ≥0∞) (QN μ N) := by
        gcongr
        exact schroC_holder (hTm i N).aestronglyMeasurable (hDm i j N).aestronglyMeasurable
      _ ≤ (KT i * eLpNorm (D i j N) (P : ℝ≥0∞) (QN μ N)) * KT j := by
        gcongr
        · exact hTbd i N hN
        · exact hTbd j N hN
  -- the linear terms
  have hlin : ∀ i ∈ s, ∀ j ∈ s, Tendsto (fun N : ℕ => eLpNorm (fun X : Config N d =>
      a i j * D i j N X) q (QN μ N)) atTop (𝓝 0) := by
    intro i _ j _
    have hlim : Tendsto (fun N : ℕ => ‖a i j‖ₑ * eLpNorm (D i j N) (P : ℝ≥0∞) (QN μ N))
        atTop (𝓝 0) := by
      have : Tendsto (fun N : ℕ => ‖a i j‖ₑ * eLpNorm (D i j N) (P : ℝ≥0∞) (QN μ N))
          atTop (𝓝 (‖a i j‖ₑ * 0)) :=
        ENNReal.Tendsto.const_mul (hDt i j) (Or.inr enorm_ne_top)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun N => zero_le) (fun N => ?_)
    rw [schroC_eLpNorm_const_mul]
    gcongr
    exact eLpNorm_le_eLpNorm_of_exponent_le hqP
  have hS1 : Tendsto (fun N : ℕ => eLpNorm (fun X : Config N d => ∑ i ∈ s, ∑ j ∈ s,
      (∑ m ∈ s, a i m * Z m N X) * D i j N X * (∑ m ∈ s, a j m * Z m N X)) q (QN μ N))
      atTop (𝓝 0) :=
    schroC_tendsto_sum s (fun i N X => ∑ j ∈ s,
      (∑ m ∈ s, a i m * Z m N X) * D i j N X * (∑ m ∈ s, a j m * Z m N X))
      (fun N => QN μ N) q hq1 fun i hi =>
      schroC_tendsto_sum s (fun j N X =>
        (∑ m ∈ s, a i m * Z m N X) * D i j N X * (∑ m ∈ s, a j m * Z m N X))
        (fun N => QN μ N) q hq1 fun j hj => hterm i hi j hj
  have hS2 : Tendsto (fun N : ℕ => eLpNorm (fun X : Config N d => ∑ i ∈ s, ∑ j ∈ s,
      a i j * D i j N X) q (QN μ N)) atTop (𝓝 0) :=
    schroC_tendsto_sum s (fun i N X => ∑ j ∈ s, a i j * D i j N X)
      (fun N => QN μ N) q hq1 fun i hi =>
      schroC_tendsto_sum s (fun j N X => a i j * D i j N X)
        (fun N => QN μ N) q hq1 fun j hj => hlin i hi j hj
  have hfin : Tendsto (fun N : ℕ => ‖(1 / 4 : ℝ)‖ₑ * eLpNorm (fun X : Config N d =>
        ∑ i ∈ s, ∑ j ∈ s, (∑ m ∈ s, a i m * Z m N X) * D i j N X * (∑ m ∈ s, a j m * Z m N X))
        q (QN μ N) + ‖(1 / 2 : ℝ)‖ₑ * eLpNorm (fun X : Config N d => ∑ i ∈ s, ∑ j ∈ s,
          a i j * D i j N X) q (QN μ N)) atTop (𝓝 0) := by
    have e1 : Tendsto (fun N : ℕ => ‖(1 / 4 : ℝ)‖ₑ * eLpNorm (fun X : Config N d =>
        ∑ i ∈ s, ∑ j ∈ s, (∑ m ∈ s, a i m * Z m N X) * D i j N X * (∑ m ∈ s, a j m * Z m N X))
        q (QN μ N)) atTop (𝓝 (‖(1 / 4 : ℝ)‖ₑ * 0)) :=
      ENNReal.Tendsto.const_mul hS1 (Or.inr enorm_ne_top)
    have e2 : Tendsto (fun N : ℕ => ‖(1 / 2 : ℝ)‖ₑ * eLpNorm (fun X : Config N d =>
        ∑ i ∈ s, ∑ j ∈ s, a i j * D i j N X) q (QN μ N)) atTop (𝓝 (‖(1 / 2 : ℝ)‖ₑ * 0)) :=
      ENNReal.Tendsto.const_mul hS2 (Or.inr enorm_ne_top)
    simpa using e1.add e2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfin
    (fun N => zero_le) (fun N => ?_)
  have hsub := eLpNorm_sub_le (f := fun X : Config N d => (1 / 4 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
      (∑ m ∈ s, a i m * Z m N X) * D i j N X * (∑ m ∈ s, a j m * Z m N X))
    (g := fun X : Config N d => (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, a i j * D i j N X)
    (p := q) (μ := QN μ N) hq1
  rw [schroC_eLpNorm_const_mul, schroC_eLpNorm_const_mul] at hsub
  exact hsub

end SchroCAux

/-! ### Auxiliary lemmas about `eC`, `ANmat`, `fluct` -/

section SchroCEC

variable {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}

theorem schroC_term_facts (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (a b : ℕ) :
    (∀ m : Fin d, Measurable (fun x => cgrad (eC a) x m * cgrad (eC b) x m)) ∧
      ∃ B : ℝ, ∀ x (m : Fin d), |cgrad (eC a) x m * cgrad (eC b) x m| ≤ B := by
  refine ⟨fun m => (measurable_cgrad (hφ a) m).mul (measurable_cgrad (hφ b) m), ?_⟩
  obtain ⟨B1, h1⟩ := exists_bound_cgrad (hφ a)
  obtain ⟨B2, h2⟩ := exists_bound_cgrad (hφ b)
  refine ⟨|B1| * |B2|, fun x m => ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((h1 x m).trans (le_abs_self _)) ((h2 x m).trans (le_abs_self _))
    (abs_nonneg _) (abs_nonneg _)

theorem schroC_S_facts (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (a b : ℕ) :
    Measurable (fun x => ∑ m : Fin d, cgrad (eC a) x m * cgrad (eC b) x m) ∧
      ∃ B : ℝ, ∀ x, |∑ m : Fin d, cgrad (eC a) x m * cgrad (eC b) x m| ≤ B := by
  obtain ⟨hm, B, hB⟩ := schroC_term_facts hφ a b
  refine ⟨Finset.measurable_sum _ fun m _ => hm m, d * B, fun x => ?_⟩
  calc |∑ m : Fin d, cgrad (eC a) x m * cgrad (eC b) x m|
      ≤ ∑ m : Fin d, |cgrad (eC a) x m * cgrad (eC b) x m| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m : Fin d, B := Finset.sum_le_sum fun m _ => hB x m
    _ = d * B := by simp

theorem schroC_D_facts {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (i j N : ℕ) :
    Measurable (fun X : Config N d => ANmat eC N X i j - if i = j then lam (i + 1) else 0) ∧
      MemLp (fun X : Config N d => ANmat eC N X i j - if i = j then lam (i + 1) else 0) ∞
        (QN μ N) := by
  obtain ⟨hSm, B, hB⟩ := schroC_S_facts hφ (i + 1) (j + 1)
  obtain ⟨hm, hL⟩ := schroC_sum_memLp (μ := μ) hSm hB N
  have hfun : (fun X : Config N d => ANmat eC N X i j - if i = j then lam (i + 1) else 0) =
      fun X => (N : ℝ)⁻¹ * (∑ l : Fin N, ∑ m : Fin d,
        cgrad (eC (i + 1)) (X l) m * cgrad (eC (j + 1)) (X l) m) -
          (if i = j then lam (i + 1) else 0) := rfl
  rw [hfun]
  exact ⟨(hm.const_mul _).sub_const _, (hL.const_mul _).sub (memLp_const _)⟩

theorem schroC_Z_facts {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (n N : ℕ) :
    Measurable (fun X : Config N d => fluct eC N n X) ∧
      MemLp (fun X : Config N d => fluct eC N n X) ∞ (QN μ N) := by
  obtain ⟨B, hB⟩ := exists_bound_of_contDiff (hφ (n + 1))
  obtain ⟨hm, hL⟩ := schroC_sum_memLp (μ := μ) (measurable_of_contDiff (hφ (n + 1))) hB N
  exact ⟨hm.const_mul _, hL.const_mul _⟩

/-- A.e. in `Q_N`, all the `eC j (X l)` agree with `e j (X l)`. -/
theorem schroC_ae_all {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hac : μ ≪ haar d) (heC : ∀ j, eC j =ᵐ[haar d] e j) (N : ℕ) :
    ∀ᵐ X ∂QN μ N, ∀ (l : Fin N) (j : ℕ), eC j (X l) = e j (X l) := by
  rw [ae_all_iff]; intro l
  rw [ae_all_iff]; intro j
  exact (measurePreserving_eval (fun _ : Fin N => μ) l).quasiMeasurePreserving.ae
    (hac.ae_le (heC j))

/-- `V_{N,R} - v_R(Z_N)` (with `fluct e`) agrees `Q_N`-a.e. with the explicit expression
of `VNR_sub_vR_eq` (with `fluct eC`). -/
theorem schroC_g_ae {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hac : μ ≪ haar d) (heC : ∀ j, eC j =ᵐ[haar d] e j) (A : FiniteRankApprox W μ e) (R N : ℕ) :
    (fun X : Config N d => VNR A lam eC R N X - vR A lam R (fun n => fluct e N n X)) =ᵐ[QN μ N]
      (fun X : Config N d => (1 / 4 : ℝ) * ∑ i ∈ A.s R, ∑ j ∈ A.s R,
          (∑ m ∈ A.s R, A.a R i m * fluct eC N m X) *
            (ANmat eC N X i j - if i = j then lam (i + 1) else 0) *
            (∑ m ∈ A.s R, A.a R j m * fluct eC N m X)
        - (1 / 2 : ℝ) * ∑ i ∈ A.s R, ∑ j ∈ A.s R,
          A.a R i j * (ANmat eC N X i j - if i = j then lam (i + 1) else 0)) := by
  filter_upwards [schroC_ae_all hac heC N] with X hX
  have hz : (fun n => fluct e N n X) = fun n => fluct eC N n X := by
    funext n
    unfold fluct
    congr 1
    exact Finset.sum_congr rfl fun l _ => (hX l (n + 1)).symm
  show VNR A lam eC R N X - vR A lam R (fun n => fluct e N n X) = _
  rw [hz]
  exact VNR_sub_vR_eq A lam eC R N X

/-- The Hölder step `∫ Ψ² |g| ≤ ‖Ψ‖_{2p}² ‖g‖_{p'}` (cf. `holder_sq_mul` of `Prop23ReplaceC`). -/
theorem schroC_holder_sq_mul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Ψ g : Ω → ℝ}
    {p : ℝ} (hp : 1 < p) (hΨ : AEMeasurable Ψ P) (hg : AEMeasurable g P) :
    ∫⁻ ω, ENNReal.ofReal (Ψ ω ^ 2 * |g ω|) ∂P ≤
      (∫⁻ ω, ENNReal.ofReal (|Ψ ω| ^ (2 * p)) ∂P) ^ (1 / p) *
        eLpNorm g (ENNReal.ofReal (p / (p - 1))) P := by
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  have hq0 : 0 < p / (p - 1) := hpq.symm.pos
  have hF : AEMeasurable (fun ω => ENNReal.ofReal (Ψ ω ^ 2)) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hΨ.pow_const 2)
  have hG : AEMeasurable (fun ω => ‖g ω‖ₑ) P := hg.enorm
  have h1 : ∀ ω, ENNReal.ofReal (Ψ ω ^ 2 * |g ω|) =
      ENNReal.ofReal (Ψ ω ^ 2) * ‖g ω‖ₑ := by
    intro ω
    rw [ENNReal.ofReal_mul (sq_nonneg _), Real.enorm_eq_ofReal_abs]
  have h2 : ∀ ω, ENNReal.ofReal (Ψ ω ^ 2) ^ p = ENNReal.ofReal (|Ψ ω| ^ (2 * p)) := by
    intro ω
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by linarith), Real.rpow_mul (abs_nonneg _)]
    congr 1
    rw [← sq_abs (Ψ ω)]
    norm_cast
  have h3 : eLpNorm g (ENNReal.ofReal (p / (p - 1))) P =
      (∫⁻ ω, ‖g ω‖ₑ ^ (p / (p - 1)) ∂P) ^ (1 / (p / (p - 1))) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq0) ENNReal.ofReal_ne_top
      hg.aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le]
  calc ∫⁻ ω, ENNReal.ofReal (Ψ ω ^ 2 * |g ω|) ∂P
      = ∫⁻ ω, ((fun ω => ENNReal.ofReal (Ψ ω ^ 2)) * (fun ω => ‖g ω‖ₑ)) ω ∂P := by
        simp only [h1, Pi.mul_apply]
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Ψ ω ^ 2) ^ p ∂P) ^ (1 / p) *
          (∫⁻ ω, ‖g ω‖ₑ ^ (p / (p - 1)) ∂P) ^ (1 / (p / (p - 1))) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq hF hG
    _ = _ := by simp only [h2, h3]

end SchroCEC

section Schro

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} (hyp : Hyp V W KV KW)
  {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
  (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
include hyp hμ he hφ heC

/-- **One-particle Dirichlet matrix for the `C¹` representatives** (the proof of
`sum_integral_cgrad_eC` of `Prop23SchroB`, re-proved here to keep this file independent of it). -/
theorem schroC_cgrad_integral (a b : ℕ) :
    ∑ k : Fin d, ∫ x, cgrad (eC a) x k * cgrad (eC b) x k ∂(μ : Measure (Torus d)) =
      lam a * (if a = b then 1 else 0) := by
  rw [← sum_integral_grad_e hyp hμ he a b]
  have hac := minimizer_ac hyp hμ
  have hwg : ∀ j, weakGrad (e j) =ᵐ[haar d] fun y k => cgrad (eC j) y k := fun j =>
    weakGrad_ae_eq (appA_isWeakGrad_congr_ae (isWeakGrad_of_contDiff (hφ j)) (heC j))
  refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
  filter_upwards [hac.ae_le (hwg a), hac.ae_le (hwg b)] with x ha hb
  rw [show weakGrad (e a) x k = cgrad (eC a) x k from congrFun ha k,
    show weakGrad (e b) x k = cgrad (eC b) x k from congrFun hb k]

/-- **LLN for `A_N`**: `E (A_{N,ij} - λ_{i+1}δ_ij)^{2k} ≤ C_k N^{-k}`, for `N ≥ 1`
(`C` depends on `i, j, k`, `μ, eC`, not on `N`).

Proof (about 60-80 lines): `g(x) := ∑_k ∂_k eC(i+1)(x) ∂_k eC(j+1)(x) - λ_{i+1} δ_ij` is measurable
(`measurable_cgrad`, NBody2:60), bounded (`exists_bound_cgrad`, NBody2:42) and `μ`-centered
(`sum_integral_cgrad_eC`, `integral_sub`, probability); `ANmat - λδ = N⁻¹ ∑_l g(X_l)`;
`Sec6.sum_moment_bound k` (lane 3, `Sec6MomentsZ.lean:256`; applies with `α := Torus d`,
`μ := (μ : Measure _)`, and `Measure.pi fun _ => μ = QN μ N` by `rfl`) gives
`E (∑ g)^{2k} ≤ C N^k B^{2k}`; multiply by `N^{-2k}`. -/
theorem ANmat_moment (i j k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ X, (ANmat eC N X i j - if i = j then lam (i + 1) else 0) ^ (2 * k)
          ∂QN (μ : Measure (Torus d)) N ≤ C * ((N : ℝ)⁻¹) ^ k := by
  obtain ⟨hSm, B, hB⟩ := schroC_S_facts hφ (i + 1) (j + 1)
  obtain ⟨hterm, Bt, hBt⟩ := schroC_term_facts hφ (i + 1) (j + 1)
  set c : ℝ := if i = j then lam (i + 1) else 0 with hc
  set S : Torus d → ℝ := fun x => ∑ m : Fin d,
    cgrad (eC (i + 1)) x m * cgrad (eC (j + 1)) x m with hS
  have hSint : Integrable S (μ : Measure (Torus d)) :=
    Integrable.of_bound hSm.aestronglyMeasurable B
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
  have hSc : ∫ x, S x ∂(μ : Measure (Torus d)) = c := by
    simp only [hS]
    rw [integral_finsetSum]
    · rw [schroC_cgrad_integral hyp hμ he hφ heC (i + 1) (j + 1)]
      simp [hc]
    · intro m _
      exact Integrable.of_bound (hterm m).aestronglyMeasurable Bt
        (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hBt x m)
  set g : Torus d → ℝ := fun x => S x - c with hg
  have hgm : Measurable g := hSm.sub_const c
  have hgB : ∀ x, |g x| ≤ |B| + |c| := fun x =>
    (abs_sub _ _).trans (add_le_add ((hB x).trans (le_abs_self _)) le_rfl)
  have hcent : ∫ x, g x ∂(μ : Measure (Torus d)) = 0 := by
    simp only [hg]
    rw [integral_sub hSint (integrable_const c), hSc]
    simp
  obtain ⟨C0, hC0, hCm⟩ := Sec6.sum_moment_bound k
  refine ⟨C0 * (|B| + |c|) ^ (2 * k), by positivity, fun N hN => ?_⟩
  have key := hCm (Torus d) (μ : Measure (Torus d)) N g (|B| + |c|) hgm
    (Eventually.of_forall hgB) hcent
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hid : ∀ X : Config N d, ANmat eC N X i j - c = (N : ℝ)⁻¹ * ∑ l, g (X l) := by
    intro X
    simp only [ANmat, hg, hS, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hinv : ((N : ℝ)⁻¹) ^ k * (N : ℝ) ^ k = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hNpos.ne', one_pow]
  calc ∫ X, (ANmat eC N X i j - c) ^ (2 * k) ∂QN (μ : Measure (Torus d)) N
      = ∫ X, ((N : ℝ)⁻¹) ^ (2 * k) * (∑ l, g (X l)) ^ (2 * k)
          ∂QN (μ : Measure (Torus d)) N := by
        refine integral_congr_ae (Eventually.of_forall fun X => ?_)
        simp only [hid X, mul_pow]
    _ = ((N : ℝ)⁻¹) ^ (2 * k) * ∫ X, (∑ l, g (X l)) ^ (2 * k)
          ∂QN (μ : Measure (Torus d)) N := integral_const_mul _ _
    _ ≤ ((N : ℝ)⁻¹) ^ (2 * k) * (C0 * (N : ℝ) ^ k * (|B| + |c|) ^ (2 * k)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = C0 * (|B| + |c|) ^ (2 * k) * (((N : ℝ)⁻¹) ^ k * (((N : ℝ)⁻¹) ^ k * (N : ℝ) ^ k)) := by
        rw [two_mul, pow_add]; ring
    _ = C0 * (|B| + |c|) ^ (2 * k) * ((N : ℝ)⁻¹) ^ k := by rw [hinv, mul_one]

/-- **Uniform moments of the fluctuation vector**: `sup_{N ≥ 1} E (Z_{N,n+1})^{2k} < ∞`.

Proof (about 40 lines): `eC (n+1)` is measurable, bounded, and `μ`-centered
(`he.orthonormal (n+1) 0`, `he.zero`, `eC =ᵐ[μ] e`, `minimizer_ac`); apply
`Sec6.fluct_moment_bound k` (lane 3, `Sec6MomentsZ.lean:267`). -/
theorem fluct_moment_eC (n k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ X, (fluct eC N n X) ^ (2 * k) ∂QN (μ : Measure (Torus d)) N ≤ C := by
  have hac := minimizer_ac hyp hμ
  obtain ⟨C0, hC0, hCm⟩ := Sec6.fluct_moment_bound k
  obtain ⟨B, hB⟩ := exists_bound_of_contDiff (hφ (n + 1))
  have hcent : ∫ x, eC (n + 1) x ∂(μ : Measure (Torus d)) = 0 := by
    have h1 : ∫ x, eC (n + 1) x ∂(μ : Measure (Torus d)) =
        ∫ x, e (n + 1) x ∂(μ : Measure (Torus d)) :=
      integral_congr_ae (hac.ae_le (heC (n + 1)))
    have h2 := he.orthonormal (n + 1) 0
    rw [he.zero] at h2
    simpa [h1] using h2
  refine ⟨C0 * B ^ (2 * k), mul_nonneg hC0 (by rw [pow_mul]; positivity), fun N hN => ?_⟩
  exact hCm (Torus d) (μ : Measure (Torus d)) N hN (eC (n + 1)) B
    (measurable_of_contDiff (hφ (n + 1))) (Eventually.of_forall hB) hcent

/-- **(E2) (eq:v-limit)**: for fixed `R` and every finite `q ≥ 1`,
`‖V_{N,R} - v_R(Z_N)‖_{L^q(Q_N)} → 0` as `N → ∞`.

Proof (about 120-160 lines): by `fluct eC N n =ᵐ[Q_N] fluct e N n` (`μ`-a.e. equality of
`eC j` and `e j` pulled back through the coordinate projections; `eLpNorm_congr_ae`) reduce to
`vR` at `fluct eC`; `VNR_sub_vR_eq` writes the difference as a finite sum of terms
`TZ_i D_ij TZ_j` and `a_ij D_ij`, `D_ij := ANmat - λδ`.  Choose `k` with `2k ≥ 3 q.toReal`; on
a probability space `‖·‖_q ≤ ‖·‖_{2k}`/Hölder: `‖TZ_i D_ij TZ_j‖_q ≤ ‖TZ_i‖_{3q} ‖D_ij‖_{3q} ‖TZ_j‖_{3q}`
(`eLpNorm_mul_le`/`MemLp.mul` with `HolderTriple`; or: `|x y z| ≤ (|x|³+|y|³+|z|³)/3`-type bound
avoided by the three-factor Hölder), `‖TZ_i‖_{3q} ≤ ∑_j |a_ij| ‖Z_j‖_{3q}` bounded uniformly in
`N` by `fluct_moment_eC`, and `‖D_ij‖_{2k} = (E D^{2k})^{1/2k} ≤ (C N^{-k})^{1/2k} → 0` by
`ANmat_moment`.  `eLpNorm_sum_le`/`eLpNorm_add_le` for the finite sums; `tendsto_finset_sum`. -/
theorem VNR_tendsto_vR (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (R : ℕ) (q : ℝ≥0∞)
    (hq1 : 1 ≤ q) (hq : q ≠ ⊤) :
    Tendsto (fun N : ℕ => eLpNorm
        (fun X => VNR A lam eC R N X - vR A lam R (fun n => fluct e N n X)) q
        (QN (μ : Measure (Torus d)) N)) atTop (𝓝 0) := by
  have hac := minimizer_ac hyp hμ
  have hmain := schroC_main (μ := (μ : Measure (Torus d))) (A.s R) (A.a R)
    (fun n N X => fluct eC N n X)
    (fun i j N X => ANmat eC N X i j - if i = j then lam (i + 1) else 0)
    (fun n N => (schroC_Z_facts (μ := (μ : Measure (Torus d))) hφ n N).1)
    (fun n N => (schroC_Z_facts (μ := (μ : Measure (Torus d))) hφ n N).2)
    (fun n k => by
      obtain ⟨C, -, hC⟩ := fluct_moment_eC hyp hμ he hφ heC n k
      exact ⟨C, hC⟩)
    (fun i j N => (schroC_D_facts (μ := (μ : Measure (Torus d))) hφ i j N).1)
    (fun i j N => (schroC_D_facts (μ := (μ : Measure (Torus d))) hφ i j N).2)
    (fun i j k => by
      obtain ⟨C, -, hC⟩ := ANmat_moment hyp hμ he hφ heC i j k
      exact ⟨C, hC⟩) q hq1 hq
  refine (tendsto_congr fun N => ?_).2 hmain
  exact eLpNorm_congr_ae (schroC_g_ae hac heC A R N)

/-- **(E2), consumer form** (what WP-F needs): `∫ Ψ² (V_{N,R} - v_R(Z_N)) dQ_N → 0` uniformly over
the `L^{2p}`-ball `∫|Ψ|^{2p} ≤ M` (in the application `Ψ = psiG f`, `p, M` from WP-A).

Proof (about 40 lines): `holder_sq_mul` (Replace) with `g := VNR - vR(Z)`, bound
`|∫ Ψ² g| ≤ ∫⁻ ofReal (Ψ² |g|) ≤ M^{1/p} ‖g‖_{p/(p-1)}` (toReal), and `VNR_tendsto_vR` with
`q := ofReal (p/(p-1))`. -/
theorem integral_VNR_sub_vR_small (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (R : ℕ)
    {p : ℝ} (hp : 1 < p) (M : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ Ψ : Config N d → ℝ,
      AEStronglyMeasurable Ψ (QN (μ : Measure (Torus d)) N) →
      ∫⁻ X, ENNReal.ofReal (|Ψ X| ^ (2 * p)) ∂QN (μ : Measure (Torus d)) N ≤ ENNReal.ofReal M →
      |∫ X, Ψ X ^ 2 * (VNR A lam eC R N X - vR A lam R (fun n => fluct e N n X))
          ∂QN (μ : Measure (Torus d)) N| ≤ ε := by
  intro ε hε
  have hac := minimizer_ac hyp hμ
  have hp1 : 0 < p - 1 := by linarith
  have hq1 : 1 ≤ ENNReal.ofReal (p / (p - 1)) :=
    ENNReal.one_le_ofReal.2 ((one_le_div hp1).2 (by linarith))
  have hT := VNR_tendsto_vR hyp hμ he hφ heC A R (ENNReal.ofReal (p / (p - 1))) hq1
    ENNReal.ofReal_ne_top
  have hLtop : ENNReal.ofReal M ^ (1 / p) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hT2 : Tendsto (fun N : ℕ => ENNReal.ofReal M ^ (1 / p) * eLpNorm
      (fun X => VNR A lam eC R N X - vR A lam R (fun n => fluct e N n X))
      (ENNReal.ofReal (p / (p - 1))) (QN (μ : Measure (Torus d)) N)) atTop
      (𝓝 (ENNReal.ofReal M ^ (1 / p) * 0)) :=
    ENNReal.Tendsto.const_mul hT (Or.inr hLtop)
  rw [mul_zero] at hT2
  have hev := (tendsto_order.1 hT2).2 (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  filter_upwards [hev] with N hN Ψ hΨ hΨint
  have hFm := schroC_F_meas (A.s R) (A.a R) (fun n N X => fluct eC N n X)
    (fun i j N X => ANmat eC N X i j - if i = j then lam (i + 1) else 0)
    (fun n N => (schroC_Z_facts (μ := (μ : Measure (Torus d))) hφ n N).1)
    (fun i j N => (schroC_D_facts (μ := (μ : Measure (Torus d))) hφ i j N).1) N
  have hgm : AEMeasurable
      (fun X : Config N d => VNR A lam eC R N X - vR A lam R (fun n => fluct e N n X))
      (QN (μ : Measure (Torus d)) N) :=
    hFm.aemeasurable.congr (schroC_g_ae hac heC A R N).symm
  set g : Config N d → ℝ :=
    fun X => VNR A lam eC R N X - vR A lam R (fun n => fluct e N n X) with hg
  have h1 := schroC_holder_sq_mul (QN (μ : Measure (Torus d)) N) hp hΨ.aemeasurable hgm
  have h2 : ∫⁻ X, ENNReal.ofReal (Ψ X ^ 2 * |g X|) ∂QN (μ : Measure (Torus d)) N ≤
      ENNReal.ofReal ε :=
    h1.trans (le_of_lt (lt_of_le_of_lt (by gcongr) hN))
  have h3 : ∫ X, Ψ X ^ 2 * |g X| ∂QN (μ : Measure (Torus d)) N ≤ ε := by
    have hfm : AEStronglyMeasurable (fun X : Config N d => Ψ X ^ 2 * |g X|)
        (QN (μ : Measure (Torus d)) N) := (hΨ.pow 2).mul hgm.aestronglyMeasurable.norm
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun X => Ψ X ^ 2 * |g X|)
      (Eventually.of_forall fun X => by positivity) hfm]
    exact ENNReal.toReal_le_of_le_ofReal hε.le h2
  calc |∫ X, Ψ X ^ 2 * g X ∂QN (μ : Measure (Torus d)) N|
      = ‖∫ X, Ψ X ^ 2 * g X ∂QN (μ : Measure (Torus d)) N‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ X, ‖Ψ X ^ 2 * g X‖ ∂QN (μ : Measure (Torus d)) N := norm_integral_le_integral_norm _
    _ = ∫ X, Ψ X ^ 2 * |g X| ∂QN (μ : Measure (Torus d)) N := by
        refine integral_congr_ae (Eventually.of_forall fun X => ?_)
        simp only [norm_mul, norm_pow, Real.norm_eq_abs, sq_abs]
    _ ≤ ε := h3

end Schro

end SharpLSI.FL
