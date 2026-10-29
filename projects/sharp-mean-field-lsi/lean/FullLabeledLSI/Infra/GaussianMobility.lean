import FullLabeledLSI.Paper.HybridMatrix

/-!
# The collective map `Gc`, the tilted covariance form `Sig`, and the mobility comparison

Pure algebra (plan, sections 2-3). Flat index `k : Fin (N * J)` stands for the pair
`(i, m) = finProdFinEquiv.symm k` (`i` a label in `Fin N`, `m` a mode in `Fin J`).
For a finite set `B ⊆ Fin N` of retained labels, `n = N - |B|`:
* `Gcm J B : Matrix (Fin J) (Fin (N*J)) ℝ` with `(Gc y)_m = n^{-1/2} ∑_{i ∉ B} y_{(i,m)}`;
  `Gcm_mul_transpose`: `Gcm * Gcmᵀ = 1` (for `|B| < N`).
* `Smat B Cm = 1 + Gcmᵀ (Cm - 1) Gcm` (the covariance of the tilted Gaussian, `Cm = CJ`),
  `Atot B Tm = 1 + Gcmᵀ Tm Gcm` (its precision matrix); `Atot_mul_Smat`: `Atot * Smat = 1`.
* `Sig_le_mobility`: `ρ · Sig(v,v) ≤ ∑_k λ_{mode k + 1} v_k²`.
-/

noncomputable section
open MeasureTheory Matrix Finset
open scoped ENNReal

namespace SharpLSI.FL

variable {N J : ℕ}

/-- The label of a flat index. -/
abbrev flatLab (k : Fin (N * J)) : Fin N := (finProdFinEquiv.symm k).1

/-- The mode of a flat index. -/
abbrev flatMode (k : Fin (N * J)) : Fin J := (finProdFinEquiv.symm k).2

/-- `n = N - |B|` as a real number. -/
def lowN (N : ℕ) (B : Finset (Fin N)) : ℝ := ((N - B.card : ℕ) : ℝ)

theorem lowN_eq_card_compl (B : Finset (Fin N)) : lowN N B = (Bᶜ.card : ℝ) := by
  unfold lowN
  rw [Finset.card_compl, Fintype.card_fin]

theorem lowN_pos {B : Finset (Fin N)} (hB : B.card < N) : 0 < lowN N B := by
  unfold lowN
  have : 0 < N - B.card := by omega
  exact_mod_cast this

/-- The collective matrix `Gc`, `(Gc y)_m = n^{-1/2} ∑_{i ∉ B} y_{(i,m)}`. -/
def Gcm (J : ℕ) (B : Finset (Fin N)) : Matrix (Fin J) (Fin (N * J)) ℝ :=
  Matrix.of fun m k => if flatMode k = m ∧ flatLab k ∉ B then (Real.sqrt (lowN N B))⁻¹ else 0

/-- The collective map. -/
def Gc (J : ℕ) (B : Finset (Fin N)) (y : Fin (N * J) → ℝ) : Fin J → ℝ := Gcm J B *ᵥ y

theorem Gc_apply (B : Finset (Fin N)) (y : Fin (N * J) → ℝ) (m : Fin J) :
    Gc J B y m = (Real.sqrt (lowN N B))⁻¹ * ∑ i ∈ Bᶜ, y (finProdFinEquiv (i, m)) := by
  unfold Gc Gcm
  simp only [mulVec, dotProduct, Matrix.of_apply]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [flatMode, flatLab, Equiv.symm_apply_apply]
  have h : ∀ x : Fin N, ∑ x_1 : Fin J, (if x_1 = m ∧ x ∉ B then (√(lowN N B))⁻¹ else 0) *
      y (finProdFinEquiv (x, x_1)) =
      if x ∈ Bᶜ then (√(lowN N B))⁻¹ * y (finProdFinEquiv (x, m)) else 0 := by
    intro x
    by_cases hx : x ∈ B
    · simp [hx]
    · simp [hx, ite_and]
  simp_rw [h]
  rw [Finset.mul_sum, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x; simp


theorem Gcm_mul_transpose {B : Finset (Fin N)} (hB : B.card < N) :
    Gcm J B * (Gcm J B)ᵀ = 1 := by
  have hn := lowN_pos hB
  have hc : (Real.sqrt (lowN N B))⁻¹ * (Real.sqrt (lowN N B))⁻¹ = (lowN N B)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hn.le]
  ext m m'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Gcm, Matrix.of_apply]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [flatMode, flatLab, Equiv.symm_apply_apply]
  by_cases h : m = m'
  · subst h
    have e1 : ∀ i : Fin N, ∑ x_1 : Fin J, (if x_1 = m ∧ i ∉ B then (Real.sqrt (lowN N B))⁻¹ else 0) *
        (if x_1 = m ∧ i ∉ B then (Real.sqrt (lowN N B))⁻¹ else 0) =
        if i ∈ Bᶜ then (lowN N B)⁻¹ else 0 := by
      intro i
      by_cases hi : i ∈ B
      · simp [hi]
      · simp [hi, hc]
    simp_rw [e1]
    rw [← Finset.sum_filter]
    simp only [Matrix.one_apply_eq, Finset.sum_const, nsmul_eq_mul]
    have : Finset.filter (fun x => x ∈ Bᶜ) Finset.univ = Bᶜ := by ext x; simp
    rw [this, ← lowN_eq_card_compl]
    field_simp
  · have : ∀ i : Fin N, ∑ x_1 : Fin J, (if x_1 = m ∧ i ∉ B then (Real.sqrt (lowN N B))⁻¹ else 0) *
        (if x_1 = m' ∧ i ∉ B then (Real.sqrt (lowN N B))⁻¹ else 0) = 0 := by
      intro i
      refine Finset.sum_eq_zero fun x_1 _ => ?_
      by_cases h1 : x_1 = m
      · have : x_1 ≠ m' := fun h2 => h (h1.symm.trans h2)
        simp [this]
      · simp [h1]
    rw [Matrix.one_apply_ne h]
    exact Finset.sum_eq_zero fun i _ => this i


/-- The covariance matrix of the tilted Gaussian, `1 + Gcᵀ (CJ - 1) Gc`. -/
def Smat (B : Finset (Fin N)) (Cm : Matrix (Fin J) (Fin J) ℝ) :
    Matrix (Fin (N * J)) (Fin (N * J)) ℝ :=
  1 + (Gcm J B)ᵀ * (Cm - 1) * Gcm J B

/-- The precision matrix of the tilted Gaussian, `1 + Gcᵀ Tm Gc`. -/
def Atot (B : Finset (Fin N)) (Tm : Matrix (Fin J) (Fin J) ℝ) :
    Matrix (Fin (N * J)) (Fin (N * J)) ℝ :=
  1 + (Gcm J B)ᵀ * Tm * Gcm J B

/-- The covariance form `Sig(v, w) = ⟨v, S w⟩ = ⟨v,w⟩ + ⟨Gc v, (CJ - 1) Gc w⟩`. -/
def Sig (B : Finset (Fin N)) (Cm : Matrix (Fin J) (Fin J) ℝ) (v w : Fin (N * J) → ℝ) : ℝ :=
  v ⬝ᵥ (Smat B Cm *ᵥ w)

theorem sandwich_mul {M : ℕ} (P : Matrix (Fin M) (Fin J) ℝ) (Q : Matrix (Fin J) (Fin M) ℝ)
    (hQP : Q * P = 1) (T C : Matrix (Fin J) (Fin J) ℝ) :
    (1 + P * T * Q) * (1 + P * (C - 1) * Q) = 1 + P * ((1 + T) * C - 1) * Q := by
  have h1 : P * T * Q * (P * (C - 1) * Q) = P * (T * (C - 1)) * Q := by
    calc P * T * Q * (P * (C - 1) * Q) = P * T * (Q * P) * (C - 1) * Q := by
          simp only [Matrix.mul_assoc]
      _ = P * (T * (C - 1)) * Q := by rw [hQP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have h0 : (1 + P * T * Q) * (1 + P * (C - 1) * Q) =
      1 + P * (C - 1) * Q + P * T * Q + P * T * Q * (P * (C - 1) * Q) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [h0, h1]
  have h3 : (1 + T) * C - 1 = (C - 1) + T + T * (C - 1) := by noncomm_ring
  have h2 : P * ((1 + T) * C - 1) * Q = P * (C - 1) * Q + P * T * Q + P * (T * (C - 1)) * Q := by
    rw [h3]; simp only [Matrix.mul_add, Matrix.add_mul]
  rw [h2]; abel

theorem Atot_mul_Smat {B : Finset (Fin N)} (hB : B.card < N) {Tm Cm : Matrix (Fin J) (Fin J) ℝ}
    (h : (1 + Tm) * Cm = 1) : Atot B Tm * Smat B Cm = 1 := by
  unfold Atot Smat
  rw [sandwich_mul _ _ (Gcm_mul_transpose hB), h]
  simp

theorem Smat_mul_Atot {B : Finset (Fin N)} (hB : B.card < N) {Tm Cm : Matrix (Fin J) (Fin J) ℝ}
    (h : (1 + Tm) * Cm = 1) : Smat B Cm * Atot B Tm = 1 :=
  mul_eq_one_comm.mp (Atot_mul_Smat hB h)

theorem Smat_transpose (B : Finset (Fin N)) {Cm : Matrix (Fin J) (Fin J) ℝ} (hC : Cmᵀ = Cm) :
    (Smat B Cm)ᵀ = Smat B Cm := by
  unfold Smat
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_sub, Matrix.transpose_one, hC]
  simp only [Matrix.mul_assoc]

theorem Atot_transpose (B : Finset (Fin N)) {Tm : Matrix (Fin J) (Fin J) ℝ} (hT : Tmᵀ = Tm) :
    (Atot B Tm)ᵀ = Atot B Tm := by
  unfold Atot
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hT]
  simp only [Matrix.mul_assoc]


theorem dotProduct_Gcm_transpose (B : Finset (Fin N)) (y : Fin (N * J) → ℝ) (a : Fin J → ℝ) :
    y ⬝ᵥ ((Gcm J B)ᵀ *ᵥ a) = a ⬝ᵥ (Gc J B y) := by
  unfold Gc
  rw [dotProduct_transpose_mulVec]

theorem Gcm_transpose_sq {B : Finset (Fin N)} (hB : B.card < N) (a : Fin J → ℝ) :
    ((Gcm J B)ᵀ *ᵥ a) ⬝ᵥ ((Gcm J B)ᵀ *ᵥ a) = a ⬝ᵥ a := by
  rw [dotProduct_Gcm_transpose, Gc, Matrix.mulVec_mulVec, Gcm_mul_transpose hB, Matrix.one_mulVec]

/-- `|Gc y|² ≤ |y|²`. -/
theorem Gc_sq_le {B : Finset (Fin N)} (hB : B.card < N) (y : Fin (N * J) → ℝ) :
    Gc J B y ⬝ᵥ Gc J B y ≤ y ⬝ᵥ y := by
  set a := Gc J B y with ha
  set w := (Gcm J B)ᵀ *ᵥ a with hw
  have h1 : y ⬝ᵥ w = a ⬝ᵥ a := dotProduct_Gcm_transpose B y a
  have h2 : w ⬝ᵥ w = a ⬝ᵥ a := Gcm_transpose_sq hB a
  have h3 : 0 ≤ (y - w) ⬝ᵥ (y - w) := dotProduct_self_star_nonneg (y - w)
  have h4 : (y - w) ⬝ᵥ (y - w) = y ⬝ᵥ y - 2 * (y ⬝ᵥ w) + w ⬝ᵥ w := by
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm w y]; ring
  linarith

theorem Sig_self (B : Finset (Fin N)) (Cm : Matrix (Fin J) (Fin J) ℝ) (v : Fin (N * J) → ℝ) :
    Sig B Cm v v = v ⬝ᵥ v + Gc J B v ⬝ᵥ ((Cm - 1) *ᵥ Gc J B v) := by
  unfold Sig Smat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  rw [dotProduct_Gcm_transpose]
  exact congrArg _ (dotProduct_comm _ _)

theorem Sig_self_eq (B : Finset (Fin N)) (Cm : Matrix (Fin J) (Fin J) ℝ) (v : Fin (N * J) → ℝ) :
    Sig B Cm v v = v ⬝ᵥ v - Gc J B v ⬝ᵥ Gc J B v + Gc J B v ⬝ᵥ (Cm *ᵥ Gc J B v) := by
  rw [Sig_self, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]; ring

theorem Sig_self_nonneg {B : Finset (Fin N)} (hB : B.card < N) {Cm : Matrix (Fin J) (Fin J) ℝ}
    (hC : ∀ s : Fin J → ℝ, 0 ≤ s ⬝ᵥ (Cm *ᵥ s)) (v : Fin (N * J) → ℝ) : 0 ≤ Sig B Cm v v := by
  rw [Sig_self_eq]
  have := Gc_sq_le hB v
  have := hC (Gc J B v)
  linarith

theorem Smat_posSemidef {B : Finset (Fin N)} (hB : B.card < N) {Cm : Matrix (Fin J) (Fin J) ℝ}
    (hCt : Cmᵀ = Cm) (hC : ∀ s : Fin J → ℝ, 0 ≤ s ⬝ᵥ (Cm *ᵥ s)) : (Smat B Cm).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact Smat_transpose B hCt
  · simpa [Sig] using Sig_self_nonneg hB hC x

theorem Atot_self (B : Finset (Fin N)) (Tm : Matrix (Fin J) (Fin J) ℝ) (v : Fin (N * J) → ℝ) :
    v ⬝ᵥ (Atot B Tm *ᵥ v) = v ⬝ᵥ v + Gc J B v ⬝ᵥ (Tm *ᵥ Gc J B v) := by
  unfold Atot
  rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  rw [dotProduct_Gcm_transpose]
  exact congrArg _ (dotProduct_comm _ _)

/-- Quadratic lower bound for `Atot` from the one for `1 + Tm` (with `c ≤ 1`). -/
theorem Atot_lower {B : Finset (Fin N)} (hB : B.card < N) {Tm : Matrix (Fin J) (Fin J) ℝ}
    {c : ℝ} (hc1 : c ≤ 1) (hT : ∀ a : Fin J → ℝ, c * (a ⬝ᵥ a) ≤ a ⬝ᵥ a + a ⬝ᵥ (Tm *ᵥ a))
    (v : Fin (N * J) → ℝ) : c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Atot B Tm *ᵥ v) := by
  rw [Atot_self]
  have h1 := Gc_sq_le hB v
  have h2 := hT (Gc J B v)
  have h3 : 0 ≤ v ⬝ᵥ v - Gc J B v ⬝ᵥ Gc J B v := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 hc1) h3]


/-- Pythagoras for the mean: `∑ f² = ∑ (f - mean)² + (∑ f)²/|S|`. -/
theorem sum_sq_decomp {ι : Type*} (S : Finset ι) (f : ι → ℝ) (hS : (S.card : ℝ) ≠ 0) :
    ∑ i ∈ S, f i ^ 2 = ∑ i ∈ S, (f i - (∑ j ∈ S, f j) / S.card) ^ 2 + (∑ j ∈ S, f j) ^ 2 / S.card := by
  set t := ∑ j ∈ S, f j with ht
  have : ∑ i ∈ S, (f i - t / S.card) ^ 2 = ∑ i ∈ S, f i ^ 2 - 2 * (t / S.card) * t +
      S.card * (t / S.card) ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, ← ht, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [this]
  field_simp
  ring

/-- The mobility comparison in coordinates. -/
theorem Sig_le_mobility_core {B : Finset (Fin N)} (hB : B.card < N)
    {Cm : Matrix (Fin J) (Fin J) ℝ} {ρ : ℝ} {lamv : Fin J → ℝ}
    (hsq : ∀ s : Fin J → ℝ, ρ * (s ⬝ᵥ s) ≤ ∑ m, lamv m * s m ^ 2)
    (hq : ∀ s : Fin J → ℝ, ρ * (s ⬝ᵥ (Cm *ᵥ s)) ≤ ∑ m, lamv m * s m ^ 2)
    (v : Fin (N * J) → ℝ) :
    ρ * Sig B Cm v v ≤ ∑ k, lamv (flatMode k) * v k ^ 2 := by
  have hn := lowN_pos hB
  have hnc : (Bᶜ.card : ℝ) = lowN N B := (lowN_eq_card_compl B).symm
  set V : Fin N → Fin J → ℝ := fun i m => v (finProdFinEquiv (i, m)) with hV
  set sv : Fin J → ℝ := fun m => ∑ i ∈ Bᶜ, V i m with hsv
  set n := lowN N B with hndef
  have hsqrt : (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ = n⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hn.le]
  have hg : Gc J B v = (Real.sqrt n)⁻¹ • sv := by
    funext m; rw [Gc_apply]; rfl
  -- the three sums
  have hvv : v ⬝ᵥ v = ∑ i, ∑ m, V i m ^ 2 := by
    simp only [dotProduct]
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    simp [hV, sq]
  have hrhs : ∑ k, lamv (flatMode k) * v k ^ 2 = ∑ i, ∑ m, lamv m * V i m ^ 2 := by
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    simp [hV, flatMode]
  have hgg : Gc J B v ⬝ᵥ Gc J B v = n⁻¹ * (sv ⬝ᵥ sv) := by
    rw [hg, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, hsqrt]
  have hgC : Gc J B v ⬝ᵥ (Cm *ᵥ Gc J B v) = n⁻¹ * (sv ⬝ᵥ (Cm *ᵥ sv)) := by
    rw [hg, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, hsqrt]
  rw [Sig_self_eq, hgg, hgC, hvv, hrhs]
  -- centered variables
  set w : Fin N → Fin J → ℝ := fun i m => V i m - sv m / n with hw
  have hdec : ∀ m, ∑ i ∈ Bᶜ, V i m ^ 2 = ∑ i ∈ Bᶜ, w i m ^ 2 + sv m ^ 2 / n := by
    intro m
    have h := sum_sq_decomp Bᶜ (fun i => V i m) (by rw [hnc]; exact hn.ne')
    rw [hnc] at h
    exact h
  have hsplit : ∀ F : Fin N → ℝ, ∑ i, F i = ∑ i ∈ B, F i + ∑ i ∈ Bᶜ, F i := fun F => by
    exact (Finset.sum_add_sum_compl B F).symm
  -- unweighted
  have hU : ∑ i, ∑ m, V i m ^ 2 - n⁻¹ * (sv ⬝ᵥ sv) =
      ∑ i ∈ B, ∑ m, V i m ^ 2 + ∑ i ∈ Bᶜ, ∑ m, w i m ^ 2 := by
    rw [hsplit (fun i => ∑ m, V i m ^ 2)]
    have : ∑ i ∈ Bᶜ, ∑ m, V i m ^ 2 = ∑ i ∈ Bᶜ, ∑ m, w i m ^ 2 + n⁻¹ * (sv ⬝ᵥ sv) := by
      rw [Finset.sum_comm, Finset.sum_congr rfl fun m _ => hdec m,
        Finset.sum_add_distrib, Finset.sum_comm (f := fun i m => w i m ^ 2)]
      congr 1
      simp only [dotProduct, sq, Finset.mul_sum, div_eq_inv_mul]
    rw [this]; ring
  -- weighted
  have hW : ∑ i, ∑ m, lamv m * V i m ^ 2 =
      ∑ i ∈ B, ∑ m, lamv m * V i m ^ 2 + ∑ i ∈ Bᶜ, ∑ m, lamv m * w i m ^ 2 +
        n⁻¹ * ∑ m, lamv m * sv m ^ 2 := by
    rw [hsplit (fun i => ∑ m, lamv m * V i m ^ 2)]
    have : ∑ i ∈ Bᶜ, ∑ m, lamv m * V i m ^ 2 =
        ∑ i ∈ Bᶜ, ∑ m, lamv m * w i m ^ 2 + n⁻¹ * ∑ m, lamv m * sv m ^ 2 := by
      have hm : ∀ m, ∑ i ∈ Bᶜ, lamv m * V i m ^ 2 =
          ∑ i ∈ Bᶜ, lamv m * w i m ^ 2 + n⁻¹ * (lamv m * sv m ^ 2) := by
        intro m
        rw [← Finset.mul_sum, ← Finset.mul_sum, hdec m]
        ring
      rw [Finset.sum_comm, Finset.sum_congr rfl fun m _ => hm m, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_comm (f := fun i m => lamv m * w i m ^ 2)]
    rw [this]; ring
  -- the three comparisons
  have h1 : ∑ i ∈ B, ρ * ∑ m, V i m ^ 2 ≤ ∑ i ∈ B, ∑ m, lamv m * V i m ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have := hsq (V i)
    simpa [dotProduct, sq] using this
  have h2 : ∑ i ∈ Bᶜ, ρ * ∑ m, w i m ^ 2 ≤ ∑ i ∈ Bᶜ, ∑ m, lamv m * w i m ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have := hsq (w i)
    simpa [dotProduct, sq] using this
  have h3 : ρ * (n⁻¹ * (sv ⬝ᵥ (Cm *ᵥ sv))) ≤ n⁻¹ * ∑ m, lamv m * sv m ^ 2 := by
    have := mul_le_mul_of_nonneg_left (hq sv) (inv_nonneg.2 hn.le)
    linarith
  rw [← Finset.mul_sum] at h1 h2
  have hL : ∑ i, ∑ m, V i m ^ 2 - n⁻¹ * (sv ⬝ᵥ sv) + n⁻¹ * (sv ⬝ᵥ (Cm *ᵥ sv)) =
      (∑ i ∈ B, ∑ m, V i m ^ 2 + ∑ i ∈ Bᶜ, ∑ m, w i m ^ 2) + n⁻¹ * (sv ⬝ᵥ (Cm *ᵥ sv)) := by
    rw [← hU]
  rw [hL, hW]
  nlinarith [h1, h2, h3]


theorem dotProduct_CJ (C : ℕ → ℕ → ℝ) (s : Fin J → ℝ) :
    s ⬝ᵥ (CJ C J *ᵥ s) = ∑ k : Fin J, ∑ l : Fin J, C k l * s k * s l := by
  simp only [dotProduct, mulVec, CJ_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

section final
variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

/-- **Mobility comparison** (plan, section 3): with `ρ = (bRate μ lam C).toReal`,
`ρ · Sig(v,v) ≤ ∑_{(i,m)} λ_{m+1} v_{(i,m)}²` for every `v` on the flat index. -/
theorem Sig_le_mobility (he : IsRefEigenbasis μ e lam) (hrl : rLS μ ≤ ENNReal.ofReal (lam 1))
    {B : Finset (Fin N)} (hB : B.card < N) (C : ℕ → ℕ → ℝ) (v : Fin (N * J) → ℝ) :
    (bRate μ lam C).toReal * Sig B (CJ C J) v v ≤
      ∑ k : Fin (N * J), lam ((flatMode k : ℕ) + 1) * v k ^ 2 := by
  refine Sig_le_mobility_core (lamv := fun m : Fin J => lam ((m : ℕ) + 1)) hB ?_ ?_ v
  · intro s
    have := rho_le_sq he hrl (C := C) s
    simpa [dotProduct, sq] using this
  · intro s
    have := rho_le_quad he (C := C) s
    rwa [← dotProduct_CJ] at this

end final

end SharpLSI.FL
