import Mathlib

/-!
# Polynomial domination

A family `F i ω` is *polynomially dominated* by a base function `S ≥ 0` if
`|F i ω| ≤ C (1 + S ω)^N` with `C, N` independent of `i` and `ω`. If `S ∈ L^p` for all finite `p`,
such families are integrable (uniformly dominated by an integrable function), and so are their products
with an `L²` weight. This is the integrability bookkeeping for the Gross lemma.
-/

namespace SharpLSI.FL.Gross

open MeasureTheory

section PolyDom

variable {Ω ι : Type*}

/-- Polynomial domination of a family by `S` (uniform in the index). -/
def PolyDom (S : Ω → ℝ) (F : ι → Ω → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ i ω, |F i ω| ≤ C * (1 + S ω) ^ N

namespace PolyDom

variable {S : Ω → ℝ} {F G : ι → Ω → ℝ}

lemma one_le (hS : ∀ ω, 0 ≤ S ω) (ω : Ω) : (1 : ℝ) ≤ 1 + S ω := by linarith [hS ω]

lemma mono (h : PolyDom S F) (hle : ∀ i ω, |G i ω| ≤ |F i ω|) : PolyDom S G := by
  obtain ⟨C, hC, N, hb⟩ := h
  exact ⟨C, hC, N, fun i ω => (hle i ω).trans (hb i ω)⟩

lemma of_bound (hS : ∀ ω, 0 ≤ S ω) (C : ℝ) (N : ℕ)
    (h : ∀ i ω, |F i ω| ≤ C * (1 + S ω) ^ N) : PolyDom S F := by
  refine ⟨|C|, abs_nonneg _, N, fun i ω => (h i ω).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith [hS ω]) _)

lemma const_family (b : ι → ℝ) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ i, |b i| ≤ C) :
    PolyDom S (fun i (_ : Ω) => b i) :=
  ⟨C, hC, 0, fun i ω => by simpa using hb i⟩

lemma const (c : ℝ) : PolyDom S (fun (_ : ι) (_ : Ω) => c) :=
  ⟨|c|, abs_nonneg _, 0, fun i ω => by simp⟩

lemma base (hS : ∀ ω, 0 ≤ S ω) : PolyDom S (fun (_ : ι) ω => S ω) := by
  refine ⟨1, zero_le_one, 1, fun i ω => ?_⟩
  rw [abs_of_nonneg (hS ω)]; linarith [hS ω]

lemma add (hS : ∀ ω, 0 ≤ S ω) (h1 : PolyDom S F) (h2 : PolyDom S G) :
    PolyDom S (fun i ω => F i ω + G i ω) := by
  obtain ⟨C1, hC1, N1, h1⟩ := h1
  obtain ⟨C2, hC2, N2, h2⟩ := h2
  refine ⟨C1 + C2, add_nonneg hC1 hC2, max N1 N2, fun i ω => ?_⟩
  have hy : (1 : ℝ) ≤ 1 + S ω := one_le hS ω
  calc |F i ω + G i ω| ≤ |F i ω| + |G i ω| := abs_add_le _ _
    _ ≤ C1 * (1 + S ω) ^ N1 + C2 * (1 + S ω) ^ N2 := add_le_add (h1 i ω) (h2 i ω)
    _ ≤ C1 * (1 + S ω) ^ (max N1 N2) + C2 * (1 + S ω) ^ (max N1 N2) :=
        add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy (le_max_left _ _)) hC1)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy (le_max_right _ _)) hC2)
    _ = (C1 + C2) * (1 + S ω) ^ (max N1 N2) := by ring

lemma mul (hS : ∀ ω, 0 ≤ S ω) (h1 : PolyDom S F) (h2 : PolyDom S G) :
    PolyDom S (fun i ω => F i ω * G i ω) := by
  obtain ⟨C1, hC1, N1, h1⟩ := h1
  obtain ⟨C2, hC2, N2, h2⟩ := h2
  refine ⟨C1 * C2, mul_nonneg hC1 hC2, N1 + N2, fun i ω => ?_⟩
  have hy : (0 : ℝ) ≤ 1 + S ω := by linarith [hS ω]
  calc |F i ω * G i ω| = |F i ω| * |G i ω| := abs_mul _ _
    _ ≤ (C1 * (1 + S ω) ^ N1) * (C2 * (1 + S ω) ^ N2) :=
        mul_le_mul (h1 i ω) (h2 i ω) (abs_nonneg _) (mul_nonneg hC1 (pow_nonneg hy _))
    _ = C1 * C2 * (1 + S ω) ^ (N1 + N2) := by ring

lemma neg (h : PolyDom S F) : PolyDom S (fun i ω => -F i ω) :=
  h.mono fun i ω => by simp

lemma sub (hS : ∀ ω, 0 ≤ S ω) (h1 : PolyDom S F) (h2 : PolyDom S G) :
    PolyDom S (fun i ω => F i ω - G i ω) := by
  have := h1.add hS h2.neg
  simpa [sub_eq_add_neg] using this

lemma abs (h : PolyDom S F) : PolyDom S (fun i ω => |F i ω|) :=
  h.mono fun i ω => by simp

lemma pow (hS : ∀ ω, 0 ≤ S ω) (h : PolyDom S F) (n : ℕ) :
    PolyDom S (fun i ω => F i ω ^ n) := by
  induction n with
  | zero => simpa using (PolyDom.const (S := S) (ι := ι) 1)
  | succ n ih =>
    have := ih.mul hS h
    simpa [pow_succ] using this

lemma rpow_le_one_add_pow {x p : ℝ} {n : ℕ} (hx : 0 ≤ x) (hp0 : 0 ≤ p) (hpn : p ≤ n) :
    x ^ p ≤ (1 + x) ^ n := by
  rcases le_total x 1 with h1 | h1
  · calc x ^ p ≤ 1 := Real.rpow_le_one hx h1 hp0
      _ ≤ (1 + x) ^ n := one_le_pow₀ (by linarith)
  · calc x ^ p ≤ x ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hpn
      _ = x ^ n := Real.rpow_natCast x n
      _ ≤ (1 + x) ^ n := pow_le_pow_left₀ hx (by linarith) n

lemma rpow (hS : ∀ ω, 0 ≤ S ω) (h : PolyDom S F) (hnn : ∀ i ω, 0 ≤ F i ω) {p : ι → ℝ} {P : ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hpP : ∀ i, p i ≤ P) : PolyDom S (fun i ω => F i ω ^ p i) := by
  have h1 : PolyDom S (fun i ω => (1 + F i ω) ^ ⌈P⌉₊) :=
    ((PolyDom.const (S := S) (ι := ι) 1).add hS h).pow hS _
  refine h1.mono fun i ω => ?_
  rw [abs_of_nonneg (Real.rpow_nonneg (hnn i ω) _),
    abs_of_nonneg (pow_nonneg (by linarith [hnn i ω]) _)]
  exact rpow_le_one_add_pow (hnn i ω) (hp0 i) ((hpP i).trans (Nat.le_ceil P))

end PolyDom

end PolyDom

section Integrability

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {S : Ω → ℝ} {F : ι → Ω → ℝ}

lemma integrable_one_add_pow (hS : ∀ ω, 0 ≤ S ω) (hSm : ∀ n : ℕ, MemLp S n P) (N : ℕ) :
    Integrable (fun ω => (1 + S ω) ^ N) P := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hm : MemLp (fun ω => 1 + S ω) N P := (memLp_const (1 : ℝ)).add (hSm N)
    have := hm.integrable_norm_pow hN.ne'
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith [hS ω])]

lemma PolyDom.integrable (hS : ∀ ω, 0 ≤ S ω) (hSm : ∀ n : ℕ, MemLp S n P) (h : PolyDom S F)
    (i : ι) (hmeas : AEStronglyMeasurable (F i) P) : Integrable (F i) P := by
  obtain ⟨C, hC, N, hb⟩ := h
  refine Integrable.mono' ((integrable_one_add_pow hS hSm N).const_mul C) hmeas
    (Filter.Eventually.of_forall fun ω => ?_)
  simpa [Real.norm_eq_abs] using hb i ω

lemma PolyDom.integrable_mul (hS : ∀ ω, 0 ≤ S ω) (hSm : ∀ n : ℕ, MemLp S n P) (h : PolyDom S F)
    {G : Ω → ℝ} (hG : MemLp G 2 P) (i : ι) (hmeas : AEStronglyMeasurable (F i) P) :
    Integrable (fun ω => F i ω * G ω) P := by
  obtain ⟨C, hC, N, hb⟩ := h
  have h1 : Integrable (fun ω => (1 + S ω) ^ (2 * N)) P := integrable_one_add_pow hS hSm (2 * N)
  have h2 : Integrable (fun ω => G ω ^ 2) P := hG.integrable_sq
  refine Integrable.mono' ((h1.add h2).const_mul (C / 2)) (hmeas.mul hG.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  have hy : (0 : ℝ) ≤ 1 + S ω := by linarith [hS ω]
  rw [Real.norm_eq_abs, abs_mul]
  have h3 : |F i ω| * |G ω| ≤ C * (1 + S ω) ^ N * |G ω| :=
    mul_le_mul_of_nonneg_right (hb i ω) (abs_nonneg _)
  have h4 : (1 + S ω) ^ N * |G ω| ≤ ((1 + S ω) ^ (2 * N) + G ω ^ 2) / 2 := by
    have := two_mul_le_add_sq ((1 + S ω) ^ N) |G ω|
    have e1 : ((1 + S ω) ^ N) ^ 2 = (1 + S ω) ^ (2 * N) := by rw [← pow_mul, mul_comm]
    have e2 : |G ω| ^ 2 = G ω ^ 2 := sq_abs _
    rw [e1, e2] at this
    linarith
  calc |F i ω| * |G ω| ≤ C * (1 + S ω) ^ N * |G ω| := h3
    _ = C * ((1 + S ω) ^ N * |G ω|) := by ring
    _ ≤ C * (((1 + S ω) ^ (2 * N) + G ω ^ 2) / 2) := mul_le_mul_of_nonneg_left h4 hC
    _ = C / 2 * ((1 + S ω) ^ (2 * N) + G ω ^ 2) := by ring

end Integrability

end SharpLSI.FL.Gross
