import DGRHS.Gaussian.PeriodicCollisionCoordinates

/-! Coefficient-exact lower bound near a simultaneous collision. The ambient
relative-coordinate norm is the product sup norm; conversion to the Euclidean
pair radius is explicit, with constants independent of the configuration. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicCollisionRadius (ι : Type u) [Fintype ι] : ℝ := 1/(4*(Fintype.card ι:ℝ))
def periodicCollisionLowerConstant (ι : Type u) [Fintype ι] : ℝ :=
  DGRHS.Gaussian.gaussianLogCounterterm 1-1/4-periodicShortHeatMean ι-periodicLongGreenBound ι-
    Real.log (2*(Fintype.card ι:ℝ))

lemma periodicCollisionRadius_pos : 0<periodicCollisionRadius ι := by
  unfold periodicCollisionRadius
  positivity

lemma periodicCollisionRadius_le_quarter : periodicCollisionRadius ι≤1/4 := by
  have hd : (1:ℝ)≤Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  unfold periodicCollisionRadius
  apply (div_le_iff₀ (by positivity : (0:ℝ)<4*(Fintype.card ι:ℝ))).mpr
  linarith

lemma periodicCollisionBall_subset_cube (n : ℕ) :
    ball (0:Fin n → ι → ℝ) (periodicCollisionRadius ι)⊆periodicRelativeCube n ι := by
  intro x hx j k
  have hn := mem_ball_zero_iff.mp hx
  have hk : |x j k|≤‖x‖ := by
    exact (show |x j k|≤‖x j‖ by simpa using norm_le_pi_norm (x j) k).trans (norm_le_pi_norm x j)
  have hr := periodicCollisionRadius_le_quarter (ι := ι)
  have ha := abs_le.mp hk
  constructor <;> linarith

lemma periodicEuclidean_norm_le_card_sup (x : ι → ℝ) :
    ‖WithLp.toLp 2 x‖≤(Fintype.card ι:ℝ)*‖x‖ := by
  have hd : (1:ℝ)≤Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have hs : ‖WithLp.toLp 2 x‖^2≤(Fintype.card ι:ℝ)*‖x‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : ι,‖x‖^2 := Finset.sum_le_sum (fun i _ => by
        have hi : |x i|≤‖x‖ := by simpa using norm_le_pi_norm x i
        change (x i)^2≤‖x‖^2
        nlinarith [sq_abs (x i),mul_nonneg (sub_nonneg.mpr hi) (add_nonneg (norm_nonneg x) (abs_nonneg (x i)))])
      _ = _ := by simp
  have hc : (Fintype.card ι:ℝ)*‖x‖^2≤((Fintype.card ι:ℝ)*‖x‖)^2 := by
    nlinarith [sq_nonneg ‖x‖,mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg ‖x‖)]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg x))).mp (hs.trans hc)

lemma periodic_cons_norm_le (n : ℕ) (x : Fin n → ι → ℝ) (i : Fin (n+1)) :
    ‖(Fin.cons (α := fun _ : Fin (n+1) => ι → ℝ) 0 x) i‖≤‖x‖ := by
  exact Fin.cases (by simpa using norm_nonneg x) (fun j => by simpa using norm_le_pi_norm x j) i

lemma periodic_cons_cast (n : ℕ) (x : Fin n → ι → ℝ) (i : Fin (n+1)) (k : ι) :
    (Fin.cons (α := fun _ : Fin (n+1) => PeriodicTorus ι) 0 (fun j l => (x j l:UnitAddCircle))) i k=
      (((Fin.cons (α := fun _ : Fin (n+1) => ι → ℝ) 0 x) i k):UnitAddCircle) := by
  exact Fin.cases (by simp) (fun j => by simp) i

lemma periodicCollision_pair_lower (n : ℕ) (x : Fin n → ι → ℝ)
    (hx : x∈ball 0 (periodicCollisionRadius ι)) (hx0 : x≠0)
    (hi : Function.Injective (Fin.cons (α := fun _ : Fin (n+1) => ι → ℝ) 0 x)) (i j : Fin (n+1)) (hij : i≠j) :
    -Real.log ‖x‖+periodicCollisionLowerConstant ι≤
      periodicPhysicalGreen ((Fin.cons (α := fun _ : Fin (n+1) => PeriodicTorus ι) 0 (fun j k => (x j k:UnitAddCircle))) i-
        (Fin.cons (α := fun _ : Fin (n+1) => PeriodicTorus ι) 0 (fun j k => (x j k:UnitAddCircle))) j) := by
  let z : ι → ℝ := (Fin.cons (α := fun _ : Fin (n+1) => ι → ℝ) 0 x) i-(Fin.cons (α := fun _ : Fin (n+1) => ι → ℝ) 0 x) j
  have hz0 : z≠0 := sub_ne_zero.mpr (fun h => hij (hi h))
  have hn : ‖z‖≤2*‖x‖ := (norm_sub_le _ _).trans (by
    linarith [periodic_cons_norm_le n x i,periodic_cons_norm_le n x j])
  have hxb : ‖x‖<periodicCollisionRadius ι := mem_ball_zero_iff.mp hx
  have hxq : ‖x‖<1/4 := hxb.trans_le periodicCollisionRadius_le_quarter
  have hzchart : ∀ k,|z k|≤1/2 := by
    intro k
    have hk : |z k|≤‖z‖ := by simpa using norm_le_pi_norm z k
    linarith
  have hd : (0:ℝ)<Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have hzr : ‖WithLp.toLp 2 z‖≤2*(Fintype.card ι:ℝ)*‖x‖ :=
    (periodicEuclidean_norm_le_card_sup z).trans (by nlinarith [mul_le_mul_of_nonneg_left hn hd.le])
  have hr1 : 2*(Fintype.card ι:ℝ)*‖x‖≤1 := by
    have h := (lt_div_iff₀ (by positivity : (0:ℝ)<4*(Fintype.card ι:ℝ))).mp hxb
    nlinarith
  have hzne : WithLp.toLp 2 z≠0 := by intro h;apply hz0;exact congrArg WithLp.ofLp h
  have hl := (periodicPhysicalGreen_log_bounds (WithLp.toLp 2 z) hzchart hzne (hzr.trans hr1)).1
  have hlog := Real.log_le_log (norm_pos_iff.mpr hzne) hzr
  rw [Real.log_mul (by positivity : (2*(Fintype.card ι:ℝ))≠0) (norm_pos_iff.mpr hx0).ne'] at hlog
  have hc : (fun k => ((WithLp.toLp 2 z) k:UnitAddCircle))=
      (Fin.cons (α := fun _ : Fin (n+1) => PeriodicTorus ι) 0 (fun j k => (x j k:UnitAddCircle))) i-
        (Fin.cons (α := fun _ : Fin (n+1) => PeriodicTorus ι) 0 (fun j k => (x j k:UnitAddCircle))) j := by
    ext k
    simp [z,periodic_cons_cast]
  rw [hc] at hl
  unfold periodicCollisionLowerConstant
  linarith

lemma periodic_offdiagonal_constant_sum (N : ℕ) (C : ℝ) :
    (∑ i : Fin N,∑ j : Fin N,if i=j then 0 else C)=(N:ℝ)*((N:ℝ)-1)*C := by
  have he (i j : Fin N) : (if i=j then (0:ℝ) else C)=C-(if i=j then C else 0) := by
    split_ifs <;> ring
  simp_rw [he,Finset.sum_sub_distrib]
  simp
  ring

lemma periodicCollision_exponent_lower (β : ℝ) (hβ : 0≤β) (n : ℕ)
    (x : Fin n → ι → ℝ) (hx : x∈ball 0 (periodicCollisionRadius ι)) (hx0 : x≠0)
    (hi : Function.Injective (Fin.cons (α := fun _ : Fin (n+1) => ι → ℝ) 0 x)) :
    β*(n:ℝ)/2*(-Real.log ‖x‖+periodicCollisionLowerConstant ι)≤
      periodicPhysicalParticleExponent β (n+1)
        (Fin.cons (α := fun _ : Fin (n+1) => PeriodicTorus ι) 0 (fun j k => (x j k:UnitAddCircle))) := by
  have hs : (∑ i : Fin (n+1),∑ j : Fin (n+1),if i=j then 0 else -Real.log ‖x‖+periodicCollisionLowerConstant ι)≤
      ∑ i : Fin (n+1),∑ j : Fin (n+1),if i=j then 0 else
        periodicPhysicalGreen ((Fin.cons (α := fun _ : Fin (n+1) => PeriodicTorus ι) 0 (fun j k => (x j k:UnitAddCircle))) i-
        (Fin.cons (α := fun _ : Fin (n+1) => PeriodicTorus ι) 0 (fun j k => (x j k:UnitAddCircle))) j) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i=j
    · simp [hij]
    · simpa only [if_neg hij] using periodicCollision_pair_lower n x hx hx0 hi i j hij
  have h := mul_le_mul_of_nonneg_left hs (show 0≤β/(2*((n+1:ℕ):ℝ)) by positivity)
  rw [periodic_offdiagonal_constant_sum] at h
  unfold periodicPhysicalParticleExponent
  convert h using 1
  push_cast
  field_simp
  <;> ring

lemma periodicCollision_density_lower (β : ℝ) (hβ : 0≤β) (n : ℕ)
    (x : Fin n → ι → ℝ) (hx : x∈ball 0 (periodicCollisionRadius ι)) (hx0 : x≠0)
    (hi : Function.Injective (Fin.cons (α := fun _ : Fin (n+1) => ι → ℝ) 0 x)) :
    ENNReal.ofReal (Real.exp (β*(n:ℝ)/2*periodicCollisionLowerConstant ι))*
      ENNReal.ofReal (‖x‖^(-(β*(n:ℝ)/2)))≤
      periodicAnchoredDensity β n (fun j k => (x j k:UnitAddCircle)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  change _≤Real.exp _
  calc
    _ = Real.exp (β*(n:ℝ)/2*(-Real.log ‖x‖+periodicCollisionLowerConstant ι)) := by
      rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hx0),← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (periodicCollision_exponent_lower β hβ n x hx hx0 hi)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicCollision_pair_lower
#print axioms DGRHS.Periodic.periodicCollision_exponent_lower
#print axioms DGRHS.Periodic.periodicCollision_density_lower
#check @DGRHS.Periodic.periodicCollision_density_lower
