import DGRHS.Decoupling.FiniteCubeNoiseStep
import DGRHS.Decoupling.FiniteCubeCharacterMask
import DGRHS.Concentration.FiniteEntropy

noncomputable section
open MeasureTheory ProbabilityTheory DGRHS.Decoupling

namespace DGRHS.Decoupling.FiniteCube

/-- The checked counting mean, specialized to the finite Boolean cube. -/
def cubeAvg {n : ℕ} (f : Cube n → ℝ) : ℝ := avgOn f

def cubeHeadAverage {n : ℕ} (f : Cube (n+1) → ℝ) : Cube n → ℝ :=
  fun x => (f (Fin.cons false x) + f (Fin.cons true x)) / 2

def cubeHeadDifference {n : ℕ} (f : Cube (n+1) → ℝ) : Cube n → ℝ :=
  fun x => (f (Fin.cons true x) - f (Fin.cons false x)) / 2

lemma cubeHeadAverage_add {n : ℕ} (f g : Cube (n+1) → ℝ) :
    cubeHeadAverage (f + g) = cubeHeadAverage f + cubeHeadAverage g := by
  funext x
  simp [cubeHeadAverage]
  ring

lemma cubeHeadDifference_add {n : ℕ} (f g : Cube (n+1) → ℝ) :
    cubeHeadDifference (f + g) = cubeHeadDifference f + cubeHeadDifference g := by
  funext x
  simp [cubeHeadDifference]
  ring

lemma cubeHeadAverage_smul {n : ℕ} (a : ℝ) (f : Cube (n+1) → ℝ) :
    cubeHeadAverage (a • f) = a • cubeHeadAverage f := by
  funext x
  simp [cubeHeadAverage]
  ring

lemma cubeHeadDifference_smul {n : ℕ} (a : ℝ) (f : Cube (n+1) → ℝ) :
    cubeHeadDifference (a • f) = a • cubeHeadDifference f := by
  funext x
  simp [cubeHeadDifference]
  ring

/-- Recursive Boolean noise, with the head coordinate isolated. -/
def cubeNoise (ρ : ℝ) : (n : ℕ) → (Cube n → ℝ) → Cube n → ℝ
  | 0, f, ω => f ω
  | n+1, f, ω =>
      cubeNoise ρ n (cubeHeadAverage f) (cubeTail ω) +
        ρ * rademacherSign (ω 0) *
          cubeNoise ρ n (cubeHeadDifference f) (cubeTail ω)

theorem cubeNoise_zero (ρ : ℝ) : ∀ n,
    cubeNoise ρ n (fun _ => 0) = fun _ => 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have hA : cubeHeadAverage (fun _ : Cube (n+1) => 0) =
          fun _ : Cube n => 0 := by
        funext x
        simp [cubeHeadAverage]
      have hB : cubeHeadDifference (fun _ : Cube (n+1) => 0) =
          fun _ : Cube n => 0 := by
        funext x
        simp [cubeHeadDifference]
      funext ω
      change cubeNoise ρ n (cubeHeadAverage (fun _ : Cube (n+1) => 0))
          (cubeTail ω) +
        ρ * rademacherSign (ω 0) *
          cubeNoise ρ n (cubeHeadDifference (fun _ : Cube (n+1) => 0))
            (cubeTail ω) = 0
      rw [hA, hB, ih]
      ring

theorem cubeNoise_add (ρ : ℝ) : ∀ n (f g : Cube n → ℝ),
    cubeNoise ρ n (f + g) = cubeNoise ρ n f + cubeNoise ρ n g := by
  intro n
  induction n with
  | zero => intro f g; rfl
  | succ n ih =>
      intro f g
      funext ω
      change cubeNoise ρ n (cubeHeadAverage (f + g)) (cubeTail ω) +
          ρ * rademacherSign (ω 0) *
            cubeNoise ρ n (cubeHeadDifference (f + g)) (cubeTail ω) =
        (cubeNoise ρ n (cubeHeadAverage f) (cubeTail ω) +
          ρ * rademacherSign (ω 0) *
            cubeNoise ρ n (cubeHeadDifference f) (cubeTail ω)) +
        (cubeNoise ρ n (cubeHeadAverage g) (cubeTail ω) +
          ρ * rademacherSign (ω 0) *
            cubeNoise ρ n (cubeHeadDifference g) (cubeTail ω))
      rw [cubeHeadAverage_add, cubeHeadDifference_add,
        ih (cubeHeadAverage f) (cubeHeadAverage g),
        ih (cubeHeadDifference f) (cubeHeadDifference g)]
      simp only [Pi.add_apply]
      ring

theorem cubeNoise_smul (ρ : ℝ) : ∀ n (a : ℝ) (f : Cube n → ℝ),
    cubeNoise ρ n (a • f) = a • cubeNoise ρ n f := by
  intro n
  induction n with
  | zero => intro a f; rfl
  | succ n ih =>
      intro a f
      funext ω
      change cubeNoise ρ n (cubeHeadAverage (a • f)) (cubeTail ω) +
          ρ * rademacherSign (ω 0) *
            cubeNoise ρ n (cubeHeadDifference (a • f)) (cubeTail ω) =
        a • (cubeNoise ρ n (cubeHeadAverage f) (cubeTail ω) +
          ρ * rademacherSign (ω 0) *
            cubeNoise ρ n (cubeHeadDifference f) (cubeTail ω))
      rw [cubeHeadAverage_smul, cubeHeadDifference_smul,
        ih a (cubeHeadAverage f), ih a (cubeHeadDifference f)]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring

theorem cubeNoise_finset_sum {α : Type*} [Fintype α] (ρ : ℝ) {n : ℕ}
    (s : Finset α) (f : α → Cube n → ℝ) :
    cubeNoise ρ n (fun ω => ∑ a ∈ s, f a ω) =
      fun ω => ∑ a ∈ s, cubeNoise ρ n (f a) ω := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact cubeNoise_zero ρ n
  | @insert a s ha ih =>
      have hfun :
          (fun ω => ∑ b ∈ insert a s, f b ω) =
            f a + (fun ω => ∑ b ∈ s, f b ω) := by
        funext ω
        simp [Finset.sum_insert, ha]
      rw [hfun, cubeNoise_add, ih]
      funext ω
      simp [Finset.sum_insert, ha]

lemma avgOn_unique_eq {X : Type*} [Fintype X] [Unique X] (f : X → ℝ) :
    avgOn f = f default := by
  unfold avgOn
  simp

lemma avgOn_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (g : Y → ℝ) :
    avgOn (fun x => g (e x)) = avgOn g := by
  have hcard : Fintype.card X = Fintype.card Y := Fintype.card_congr e
  have hsum : (∑ x : X, g (e x)) = ∑ y : Y, g y := by
    apply Fintype.sum_equiv e
    intro x
    rfl
  unfold avgOn
  rw [hsum, hcard]

lemma cubeAvg_headTail {n : ℕ} (f : Cube (n+1) → ℝ) :
    cubeAvg f = avgOn (fun z : Bool × Cube n =>
      f ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n+1) => Bool) 0).symm z)) := by
  let e : Cube (n+1) ≃ Bool × Cube n :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Bool) 0
  exact (avgOn_equiv e.symm f).symm

lemma cubeAvg_split {n : ℕ} (f : Cube (n+1) → ℝ) :
    cubeAvg f =
      (cubeAvg (fun x : Cube n => f (Fin.cons false x)) +
       cubeAvg (fun x : Cube n => f (Fin.cons true x))) / 2 := by
  let e : Cube (n+1) ≃ Bool × Cube n :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Bool) 0
  calc
    cubeAvg f = avgOn (fun z : Bool × Cube n => f (e.symm z)) :=
      cubeAvg_headTail f
    _ = (avgOn (fun x : Cube n => f (Fin.cons false x)) +
         avgOn (fun x : Cube n => f (Fin.cons true x))) / 2 := by
      rw [avgOn_bool_prod]
      congr 1
      apply congrArg₂ (fun x y : ℝ => x + y)
      · apply avgOn_congr
        intro x
        have he : e.symm (false, x) = Fin.cons false x := by
          change (MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n+1) => Bool) 0).symm (false, x) = _
          exact DGRHS.Concentration.pi_split_zero false x
        simpa [e] using congrArg f he
      · apply avgOn_congr
        intro x
        have he : e.symm (true, x) = Fin.cons true x := by
          change (MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n+1) => Bool) 0).symm (true, x) = _
          exact DGRHS.Concentration.pi_split_zero true x
        simpa [e] using congrArg f he

lemma cubeAvg_two_slices_square {n : ℕ} (f : Cube (n+1) → ℝ) :
    cubeAvg (fun ω => f ω ^ 2) =
      cubeAvg (fun x : Cube n =>
        ((f (Fin.cons false x) + f (Fin.cons true x)) / 2) ^ 2) +
      cubeAvg (fun x : Cube n =>
        ((f (Fin.cons true x) - f (Fin.cons false x)) / 2) ^ 2) := by
  let f₀ : Cube n → ℝ := fun x => f (Fin.cons false x)
  let f₁ : Cube n → ℝ := fun x => f (Fin.cons true x)
  let a : Cube n → ℝ := fun x => (f₀ x + f₁ x) / 2
  let b : Cube n → ℝ := fun x => (f₁ x - f₀ x) / 2
  have hpoint : ∀ x, a x ^ 2 + b x ^ 2 = (f₀ x ^ 2 + f₁ x ^ 2) / 2 := by
    intro x
    dsimp [a, b]
    ring
  calc
    cubeAvg (fun ω => f ω ^ 2) =
        (cubeAvg (fun x => f₀ x ^ 2) + cubeAvg (fun x => f₁ x ^ 2)) / 2 :=
      cubeAvg_split (fun ω => f ω ^ 2)
    _ = cubeAvg (fun x => (f₀ x ^ 2 + f₁ x ^ 2) / 2) := by
      symm
      exact avgOn_half_add _ _
    _ = cubeAvg (fun x => a x ^ 2 + b x ^ 2) := by
      apply avgOn_congr
      intro x
      exact (hpoint x).symm
    _ = cubeAvg (fun x => a x ^ 2) + cubeAvg (fun x => b x ^ 2) :=
      avgOn_add _ _

/-- Recursive fourth-moment contraction. The base and all dimensions include the empty cube. -/
theorem cubeNoise_fourth_le (ρ : ℝ) (hρ : ρ ^ 2 = 1 / 3) :
    ∀ n (f : Cube n → ℝ),
      cubeAvg (fun ω => cubeNoise ρ n f ω ^ 4) ≤
        (cubeAvg (fun ω => f ω ^ 2)) ^ 2 := by
  intro n
  induction n with
  | zero =>
      intro f
      letI : Unique (Cube 0) := {
        default := fun i => Fin.elim0 i
        uniq := by
          intro x
          funext i
          exact Fin.elim0 i
      }
      change avgOn (fun ω : Cube 0 => f ω ^ 4) ≤
        (avgOn (fun ω : Cube 0 => f ω ^ 2)) ^ 2
      rw [avgOn_unique_eq, avgOn_unique_eq]
      have hpow : ∀ x : Cube 0, f x ^ 4 = (f x ^ 2) ^ 2 := by
        intro x
        ring
      exact (hpow _).le
  | succ n ih =>
      intro f
      let a : Cube n → ℝ := cubeHeadAverage f
      let b : Cube n → ℝ := cubeHeadDifference f
      let A : Cube n → ℝ := cubeNoise ρ n a
      let B : Cube n → ℝ := cubeNoise ρ n b
      have hA : cubeAvg (fun x => A x ^ 4) ≤
          (cubeAvg (fun x => a x ^ 2)) ^ 2 := ih a
      have hB : cubeAvg (fun x => B x ^ 4) ≤
          (cubeAvg (fun x => b x ^ 2)) ^ 2 := ih b
      have hleft : cubeAvg (fun ω => cubeNoise ρ (n+1) f ω ^ 4) =
          avgOn (fun z : Bool × Cube n =>
            (A z.2 + ρ * rademacherSign z.1 * B z.2) ^ 4) := by
        rw [cubeAvg_headTail]
        apply avgOn_congr
        intro z
        rcases z with ⟨σ, x⟩
        simp only [DGRHS.Concentration.pi_split_zero]
        have htail : cubeTail (Fin.cons σ x) = x := by
          funext i
          rfl
        change (cubeNoise ρ n (cubeHeadAverage f) (cubeTail (Fin.cons σ x)) +
          ρ * rademacherSign σ *
            cubeNoise ρ n (cubeHeadDifference f) (cubeTail (Fin.cons σ x))) ^ 4 = _
        rw [htail]
      have hstep := avg_noiseStep_fourth_le ρ hρ a b A B hA hB
      calc
        cubeAvg (fun ω => cubeNoise ρ (n+1) f ω ^ 4) =
            avgOn (fun z : Bool × Cube n =>
              (A z.2 + ρ * rademacherSign z.1 * B z.2) ^ 4) := hleft
        _ ≤ (cubeAvg (fun x => a x ^ 2) + cubeAvg (fun x => b x ^ 2)) ^ 2 := by
          simpa [cubeAvg] using hstep
        _ = (cubeAvg (fun ω => f ω ^ 2)) ^ 2 := by
          have hslices := congrArg (fun x : ℝ => x ^ 2) (cubeAvg_two_slices_square f)
          simpa [a, b, cubeHeadAverage, cubeHeadDifference] using hslices.symm

/-- Noise eigenvalue on the shared recursive Walsh basis. -/
theorem cubeNoise_walsh_eigenvalue (ρ : ℝ) :
    ∀ n (s : Cube n),
      cubeNoise ρ n (cubeWalsh n s) =
        fun ω => ρ ^ cubeWalshDegree n s * cubeWalsh n s ω := by
  intro n
  induction n with
  | zero =>
      intro s
      funext ω
      simp [cubeNoise, cubeWalsh, cubeWalshDegree]
  | succ n ih =>
      intro s
      let st : Cube n := cubeTail s
      have iht := ih st
      cases h0 : s 0 with
      | false =>
          have ha : (fun x : Cube n =>
              (cubeWalsh (n+1) s (Fin.cons false x) +
               cubeWalsh (n+1) s (Fin.cons true x)) / 2) = cubeWalsh n st := by
            funext x
            have hfalse : cubeTail (Fin.cons false x) = x := rfl
            have htrue : cubeTail (Fin.cons true x) = x := rfl
            simp [cubeWalsh, st, h0, hfalse, htrue]
          have hb : (fun x : Cube n =>
              (cubeWalsh (n+1) s (Fin.cons true x) -
               cubeWalsh (n+1) s (Fin.cons false x)) / 2) = 0 := by
            funext x
            have hfalse : cubeTail (Fin.cons false x) = x := rfl
            have htrue : cubeTail (Fin.cons true x) = x := rfl
            simp [cubeWalsh, st, h0, hfalse, htrue]
          funext ω
          change cubeNoise ρ n
              (cubeHeadAverage (cubeWalsh (n+1) s)) (cubeTail ω) +
            ρ * rademacherSign (ω 0) * cubeNoise ρ n
              (cubeHeadDifference (cubeWalsh (n+1) s)) (cubeTail ω) =
            ρ ^ cubeWalshDegree (n+1) s * cubeWalsh (n+1) s ω
          rw [show cubeHeadAverage (cubeWalsh (n+1) s) =
                (fun x : Cube n =>
                  (cubeWalsh (n+1) s (Fin.cons false x) +
                   cubeWalsh (n+1) s (Fin.cons true x)) / 2) by rfl,
            show cubeHeadDifference (cubeWalsh (n+1) s) =
                (fun x : Cube n =>
                  (cubeWalsh (n+1) s (Fin.cons true x) -
                   cubeWalsh (n+1) s (Fin.cons false x)) / 2) by rfl,
            ha, hb]
          have hzero : (0 : Cube n → ℝ) = fun _ => 0 := rfl
          rw [hzero, cubeNoise_zero ρ n, iht]
          simp [cubeWalsh, cubeWalshDegree, cubeTail, st, h0, rademacherSign]
      | true =>
          have ha : (fun x : Cube n =>
              (cubeWalsh (n+1) s (Fin.cons false x) +
               cubeWalsh (n+1) s (Fin.cons true x)) / 2) = 0 := by
            funext x
            have hfalse : cubeTail (Fin.cons false x) = x := rfl
            have htrue : cubeTail (Fin.cons true x) = x := rfl
            simp [cubeWalsh, st, h0, hfalse, htrue, rademacherSign]
          have hb : (fun x : Cube n =>
              (cubeWalsh (n+1) s (Fin.cons true x) -
               cubeWalsh (n+1) s (Fin.cons false x)) / 2) = cubeWalsh n st := by
            funext x
            have hfalse : cubeTail (Fin.cons false x) = x := rfl
            have htrue : cubeTail (Fin.cons true x) = x := rfl
            simp [cubeWalsh, st, h0, hfalse, htrue, rademacherSign]
          funext ω
          change cubeNoise ρ n
              (cubeHeadAverage (cubeWalsh (n+1) s)) (cubeTail ω) +
            ρ * rademacherSign (ω 0) * cubeNoise ρ n
              (cubeHeadDifference (cubeWalsh (n+1) s)) (cubeTail ω) =
            ρ ^ cubeWalshDegree (n+1) s * cubeWalsh (n+1) s ω
          rw [show cubeHeadAverage (cubeWalsh (n+1) s) =
                (fun x : Cube n =>
                  (cubeWalsh (n+1) s (Fin.cons false x) +
                   cubeWalsh (n+1) s (Fin.cons true x)) / 2) by rfl,
            show cubeHeadDifference (cubeWalsh (n+1) s) =
                (fun x : Cube n =>
                  (cubeWalsh (n+1) s (Fin.cons true x) -
                   cubeWalsh (n+1) s (Fin.cons false x)) / 2) by rfl,
            ha, hb]
          have hzero : (0 : Cube n → ℝ) = fun _ => 0 := rfl
          rw [hzero, cubeNoise_zero ρ n, iht]
          simp only [cubeNoise, zero_add, cubeWalsh, cubeWalshDegree,
            cubeTail, st, h0]
          simp [rademacherSign]
          rw [pow_add]
          simp
          ring

lemma cubeAvg_nonneg {n : ℕ} (f : Cube n → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ cubeAvg f := by
  unfold cubeAvg
  exact avgOn_nonneg f hf

lemma integral_fairBool_eq_half_sum (g : Bool → ℝ) :
    (∫ b, g b ∂fairBool) = (g false + g true) / 2 := by
  unfold fairBool
  rw [PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, Fintype.sum_bool]
  ring

/-- Counting mean equals the checked fair-Bool product-law integral. -/
lemma cubeAvg_eq_selectorLaw_integral {n : ℕ} (f : Cube n → ℝ) :
    cubeAvg f = ∫ ω, f ω ∂selectorLaw (Fin n) := by
  classical
  revert f
  induction n with
  | zero =>
      intro f
      letI : Unique (Cube 0) := {
        default := fun i => Fin.elim0 i
        uniq := by
          intro x
          funext i
          exact Fin.elim0 i
      }
      have hf : f = fun _ : Cube 0 => f default := by
        funext ω
        congr 1
        exact Subsingleton.elim _ _
      rw [hf]
      calc
        cubeAvg (fun _ : Cube 0 => f default) = f default := avgOn_unique_eq _
        _ = ∫ _ : Cube 0, f default ∂selectorLaw (Fin 0) := by simp
  | succ n ih =>
      intro f
      let μ : Fin (n+1) → Measure Bool := fun _ => fairBool
      have hInt : Integrable f (Measure.pi μ) := Integrable.of_finite
      have hsplit := DGRHS.Concentration.pi_cons_integral μ hInt
      have hfalse : cubeAvg (fun x : Cube n => f (Fin.cons false x)) =
          ∫ x, f (Fin.cons false x) ∂Measure.pi
            (fun _ : Fin n => fairBool) := ih _
      have htrue : cubeAvg (fun x : Cube n => f (Fin.cons true x)) =
          ∫ x, f (Fin.cons true x) ∂Measure.pi
            (fun _ : Fin n => fairBool) := ih _
      change cubeAvg f = ∫ ω, f ω ∂Measure.pi μ
      rw [hsplit, integral_fairBool_eq_half_sum, ← hfalse, ← htrue]
      exact cubeAvg_split f

/-- The coefficient Parseval identity imported from the proposed mask module,
    converted to the exact average used by the checked noise step. -/
def cubeWalshPolynomial {n : ℕ} (c : Cube n → ℝ) : Cube n → ℝ :=
  fun ω => ∑ s : Cube n, c s * cubeWalsh n s ω

theorem cubeWalshPolynomial_parseval {n : ℕ} (c : Cube n → ℝ) :
    cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 2) = ∑ s : Cube n, c s ^ 2 := by
  rw [cubeAvg_eq_selectorLaw_integral]
  simpa [cubeWalshPolynomial, finiteBoolWalshPolynomial,
    cubeWalsh_eq_boolMaskCharacter] using integral_finiteBoolWalshPolynomial_sq c

/-- Finite Walsh polynomial action of the recursive noise operator. -/
theorem cubeNoise_walshPolynomial (ρ : ℝ) {n : ℕ} (c : Cube n → ℝ) :
    cubeNoise ρ n (cubeWalshPolynomial c) =
      cubeWalshPolynomial (fun s => ρ ^ cubeWalshDegree n s * c s) := by
  classical
  funext ω
  change cubeNoise ρ n
      (fun ω => ∑ s ∈ (Finset.univ : Finset (Cube n)),
        c s * cubeWalsh n s ω) ω =
    ∑ s ∈ (Finset.univ : Finset (Cube n)),
      (ρ ^ cubeWalshDegree n s * c s) * cubeWalsh n s ω
  rw [cubeNoise_finset_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hscale := congrFun (cubeNoise_smul ρ n (c s) (cubeWalsh n s)) ω
  rw [cubeNoise_walsh_eigenvalue] at hscale
  have hfun : c s • cubeWalsh n s =
      (fun ω => c s * cubeWalsh n s ω) := by
    funext x
    rfl
  rw [hfun] at hscale
  have hscale' : cubeNoise ρ n (fun ω => c s * cubeWalsh n s ω) ω =
      c s * (ρ ^ cubeWalshDegree n s * cubeWalsh n s ω) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hscale
  calc
    cubeNoise ρ n (fun ω => c s * cubeWalsh n s ω) ω =
        c s * (ρ ^ cubeWalshDegree n s * cubeWalsh n s ω) := hscale'
    _ = (ρ ^ cubeWalshDegree n s * c s) * cubeWalsh n s ω := by ring

def cubeInverseNoiseCoefficients {n : ℕ} (ρ : ℝ) (c : Cube n → ℝ) : Cube n → ℝ :=
  fun s => (ρ⁻¹) ^ cubeWalshDegree n s * c s

lemma cubeNoise_inverse_walshPolynomial {n k : ℕ} (ρ : ℝ)
    (hρ : ρ ^ 2 = 1 / 3) (c : Cube n → ℝ) :
    cubeNoise ρ n (cubeWalshPolynomial (cubeInverseNoiseCoefficients ρ c)) =
      cubeWalshPolynomial c := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h] at hρ
    norm_num at hρ
  have hcancel (d : ℕ) : ρ ^ d * (ρ⁻¹) ^ d = 1 := by
    calc
      ρ ^ d * (ρ⁻¹) ^ d = (ρ * ρ⁻¹) ^ d := by rw [mul_pow]
      _ = 1 := by rw [mul_inv_cancel₀ hρ0]; simp
  rw [cubeNoise_walshPolynomial]
  unfold cubeWalshPolynomial cubeInverseNoiseCoefficients
  funext ω
  apply Finset.sum_congr rfl
  intro s hs
  calc
    (ρ ^ cubeWalshDegree n s *
        ((ρ⁻¹) ^ cubeWalshDegree n s * c s)) * cubeWalsh n s ω =
      (ρ ^ cubeWalshDegree n s * (ρ⁻¹) ^ cubeWalshDegree n s) *
        (c s * cubeWalsh n s ω) := by ring
    _ = c s * cubeWalsh n s ω := by rw [hcancel (cubeWalshDegree n s)]; ring

lemma pow_square_comm (a : ℝ) (d : ℕ) : (a ^ d) ^ 2 = (a ^ 2) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        (a ^ (d+1)) ^ 2 = (a ^ d * a) ^ 2 := by
          rw [pow_succ (a := a) (n := d)]
        _ = (a ^ d) ^ 2 * a ^ 2 := by ring
        _ = (a ^ 2) ^ d * a ^ 2 := by rw [ih]
        _ = (a ^ 2) ^ (d+1) := by
          rw [pow_succ (a := a ^ 2) (n := d)]

lemma pow_three_mono {d k : ℕ} (hdk : d ≤ k) :
    (3 : ℝ) ^ d ≤ 3 ^ k := by
  induction hdk with
  | refl => exact le_rfl
  | @step k h ih =>
      calc
        (3 : ℝ) ^ d ≤ 3 ^ k := ih
        _ ≤ 3 ^ k * 3 := by nlinarith [pow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) k]
        _ = 3 ^ (k+1) := by rw [pow_succ (a := (3 : ℝ)) (n := k)]

lemma inverse_rho_sq {ρ : ℝ} (hρ : ρ ^ 2 = 1 / 3) : (ρ⁻¹) ^ 2 = 3 := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h] at hρ
    norm_num at hρ
  field_simp [hρ0]
  nlinarith [hρ]

lemma cubeInverseNoise_parseval_le {n k : ℕ} {ρ : ℝ}
    (hρ : ρ ^ 2 = 1 / 3) (c : Cube n → ℝ)
    (hdegree : ∀ s, c s ≠ 0 → cubeWalshDegree n s ≤ k) :
    cubeAvg (fun ω => cubeWalshPolynomial (cubeInverseNoiseCoefficients ρ c) ω ^ 2) ≤
      (3 : ℝ) ^ k * cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 2) := by
  rw [cubeWalshPolynomial_parseval, cubeWalshPolynomial_parseval]
  calc
    ∑ s : Cube n, cubeInverseNoiseCoefficients ρ c s ^ 2 ≤
        ∑ s : Cube n, (3 : ℝ) ^ k * c s ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      by_cases hc : c s = 0
      · simp [cubeInverseNoiseCoefficients, hc]
      · have hd := hdegree s hc
        have hweight :
            ((ρ⁻¹) ^ cubeWalshDegree n s) ^ 2 ≤ (3 : ℝ) ^ k := by
          rw [pow_square_comm, inverse_rho_sq hρ]
          exact pow_three_mono hd
        dsimp [cubeInverseNoiseCoefficients]
        calc
          ((ρ⁻¹) ^ cubeWalshDegree n s * c s) ^ 2 =
              ((ρ⁻¹) ^ cubeWalshDegree n s) ^ 2 * c s ^ 2 := by ring
          _ ≤ (3 : ℝ) ^ k * c s ^ 2 :=
              mul_le_mul_of_nonneg_right hweight (sq_nonneg (c s))
    _ = (3 : ℝ) ^ k * ∑ s : Cube n, c s ^ 2 := by
      rw [← Finset.mul_sum]

lemma three_pow_sq_eq_nine_pow (k : ℕ) :
    ((3 : ℝ) ^ k) ^ 2 = (9 : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      calc
        ((3 : ℝ) ^ (k+1)) ^ 2 = ((3 : ℝ) ^ k * 3) ^ 2 := by
          rw [pow_succ (a := (3 : ℝ)) (n := k)]
        _ = ((3 : ℝ) ^ k) ^ 2 * 9 := by ring
        _ = (9 : ℝ) ^ k * 9 := by rw [ih]
        _ = (9 : ℝ) ^ (k+1) := by
          rw [pow_succ (a := (9 : ℝ)) (n := k)]

/-- Exact degree-`≤ k` fourth-moment estimate for every finite Walsh polynomial. -/
theorem cubeWalshPolynomial_fourth_le_of_degree
    (n k : ℕ) (c : Cube n → ℝ) (ρ : ℝ) (hρ : ρ ^ 2 = 1 / 3)
    (hdegree : ∀ s, c s ≠ 0 → cubeWalshDegree n s ≤ k) :
    cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 4) ≤
      (9 : ℝ) ^ k * (cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 2)) ^ 2 := by
  let q := cubeInverseNoiseCoefficients ρ c
  have hnoise : cubeNoise ρ n (cubeWalshPolynomial q) = cubeWalshPolynomial c := by
    simpa [q] using cubeNoise_inverse_walshPolynomial (n := n) (k := 0) ρ hρ c
  have hcontract := cubeNoise_fourth_le ρ hρ n (cubeWalshPolynomial q)
  have hL2 := cubeInverseNoise_parseval_le hρ c hdegree
  have hPnonneg : 0 ≤ cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 2) :=
    cubeAvg_nonneg _ (fun ω => sq_nonneg _)
  have hQnonneg : 0 ≤ cubeAvg (fun ω => cubeWalshPolynomial q ω ^ 2) :=
    cubeAvg_nonneg _ (fun ω => sq_nonneg _)
  have hboundnonneg :
      0 ≤ (3 : ℝ) ^ k * cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 2) :=
    mul_nonneg (pow_nonneg (by norm_num) _) hPnonneg
  have hsq := mul_le_mul hL2 hL2 hQnonneg hboundnonneg
  have hsq' : (cubeAvg (fun ω => cubeWalshPolynomial q ω ^ 2)) ^ 2 ≤
      ((3 : ℝ) ^ k * cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 2)) ^ 2 := by
    simpa [pow_two] using hsq
  calc
    cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 4) =
        cubeAvg (fun ω => cubeNoise ρ n (cubeWalshPolynomial q) ω ^ 4) := by
          rw [hnoise]
    _ ≤ (cubeAvg (fun ω => cubeWalshPolynomial q ω ^ 2)) ^ 2 := hcontract
    _ ≤ ((3 : ℝ) ^ k * cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 2)) ^ 2 := hsq'
    _ = ((3 : ℝ) ^ k) ^ 2 *
          (cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 2)) ^ 2 := by ring
    _ = (9 : ℝ) ^ k * (cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 2)) ^ 2 := by
          rw [three_pow_sq_eq_nine_pow]

end DGRHS.Decoupling.FiniteCube

#print axioms DGRHS.Decoupling.FiniteCube.cubeHeadAverage_add
#print axioms DGRHS.Decoupling.FiniteCube.cubeHeadDifference_add
#print axioms DGRHS.Decoupling.FiniteCube.cubeHeadAverage_smul
#print axioms DGRHS.Decoupling.FiniteCube.cubeHeadDifference_smul
#print axioms DGRHS.Decoupling.FiniteCube.cubeNoise_zero
#print axioms DGRHS.Decoupling.FiniteCube.cubeNoise_add
#print axioms DGRHS.Decoupling.FiniteCube.cubeNoise_smul
#print axioms DGRHS.Decoupling.FiniteCube.cubeNoise_finset_sum
#print axioms DGRHS.Decoupling.FiniteCube.avgOn_unique_eq
#print axioms DGRHS.Decoupling.FiniteCube.avgOn_equiv
#print axioms DGRHS.Decoupling.FiniteCube.cubeAvg_headTail
#print axioms DGRHS.Decoupling.FiniteCube.cubeAvg_split
#print axioms DGRHS.Decoupling.FiniteCube.cubeAvg_two_slices_square
#print axioms DGRHS.Decoupling.FiniteCube.cubeNoise_fourth_le
#print axioms DGRHS.Decoupling.FiniteCube.cubeNoise_walsh_eigenvalue
#print axioms DGRHS.Decoupling.FiniteCube.cubeAvg_nonneg
#print axioms DGRHS.Decoupling.FiniteCube.integral_fairBool_eq_half_sum
#print axioms DGRHS.Decoupling.FiniteCube.cubeAvg_eq_selectorLaw_integral
#print axioms DGRHS.Decoupling.FiniteCube.cubeWalshPolynomial_parseval
#print axioms DGRHS.Decoupling.FiniteCube.cubeNoise_walshPolynomial
#print axioms DGRHS.Decoupling.FiniteCube.cubeNoise_inverse_walshPolynomial
#print axioms DGRHS.Decoupling.FiniteCube.pow_square_comm
#print axioms DGRHS.Decoupling.FiniteCube.pow_three_mono
#print axioms DGRHS.Decoupling.FiniteCube.inverse_rho_sq
#print axioms DGRHS.Decoupling.FiniteCube.cubeInverseNoise_parseval_le
#print axioms DGRHS.Decoupling.FiniteCube.three_pow_sq_eq_nine_pow
#print axioms DGRHS.Decoupling.FiniteCube.cubeWalshPolynomial_fourth_le_of_degree
