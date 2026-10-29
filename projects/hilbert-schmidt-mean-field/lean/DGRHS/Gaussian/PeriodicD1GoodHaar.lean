import DGRHS.Gaussian.PeriodicD1GoodAlgebra
import DGRHS.Gaussian.PeriodicCosineTrial
import DGRHS.Decoupling.Product
import DGRHS.Concentration.ReplacementEntropy

/-! Uncompiled draft. Good's recurrence and zero-exponent boundary for actual
normalized Haar integrals. Natural polynomial weights are proper by continuity
on a compact torus. The zero-exponent coordinate is genuinely integrated out.
The two resampling/product laws imported here are unchanged checked predecessors. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical
namespace DGRHS.Periodic
variable {N : ℕ}

def periodicD1GoodNodes (x : Fin N → UnitAddCircle) (i : Fin N) : ℂ := fourier 1 (x i)

def periodicD1GoodIntegral (s : Finset (Fin N)) (a : Fin N → ℕ) : ℂ :=
  ∫ x : Fin N → UnitAddCircle,periodicD1GoodWeight s a (periodicD1GoodNodes x)
    ∂periodicHaar (Fin N)

lemma periodicD1GoodNode_ne_zero (x : Fin N → UnitAddCircle) (i : Fin N) :
    periodicD1GoodNodes x i≠0 := by
  have h : ‖periodicD1GoodNodes x i‖=1 := by simp [periodicD1GoodNodes,fourier_apply]
  intro hz
  simp only [hz,norm_zero] at h
  exact zero_ne_one h

lemma periodicD1GoodRow_continuous (s : Finset (Fin N)) (i : Fin N) :
    Continuous (fun x => periodicD1GoodRow s (periodicD1GoodNodes x) i) := by
  unfold periodicD1GoodRow
  apply continuous_finsetProd
  intro j hj
  exact continuous_const.sub
    (((fourier 1).continuous.comp (continuous_apply i)).div
      ((fourier 1).continuous.comp (continuous_apply j))
      (fun x => periodicD1GoodNode_ne_zero x j))

lemma periodicD1GoodWeight_continuous (s : Finset (Fin N)) (a : Fin N → ℕ) :
    Continuous (fun x => periodicD1GoodWeight s a (periodicD1GoodNodes x)) := by
  unfold periodicD1GoodWeight
  apply continuous_finsetProd
  intro i hi
  exact (periodicD1GoodRow_continuous s i).pow (a i)

lemma periodicD1GoodWeight_integrable (s : Finset (Fin N)) (a : Fin N → ℕ) :
    Integrable (fun x => periodicD1GoodWeight s a (periodicD1GoodNodes x))
      (periodicHaar (Fin N)) :=
  (periodicD1GoodWeight_continuous s a).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma periodicD1GoodNodes_injective_ae :
    ∀ᵐ x : Fin N → UnitAddCircle ∂periodicHaar (Fin N),
      Function.Injective (periodicD1GoodNodes x) := by
  have hv : (volume : Measure UnitAddCircle)=AddCircle.haarAddCircle := by
    simpa only [ENNReal.ofReal_one,one_smul] using
      AddCircle.volume_eq_smul_haarAddCircle (T := 1)
  let : NullSingletonClass (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    ⟨fun x => by simpa [hv] using AddCircle.volume_closedBall (T := 1) (x := x) 0⟩
  have hpair (i j : Fin N) (hij : i≠j) :
      ∀ᵐ x : Fin N → UnitAddCircle ∂periodicHaar (Fin N),x i≠x j := by
    have hp : ∀ᵐ p : UnitAddCircle × UnitAddCircle
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle,
        p.1≠p.2 := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
      exact Eventually.of_forall (fun x =>
        (Measure.ae_ne (AddCircle.haarAddCircle : Measure UnitAddCircle) x).mono
          (fun _ h => h.symm))
    exact (DGRHS.Decoupling.pair_eval_measurePreserving
      (AddCircle.haarAddCircle : Measure UnitAddCircle) i j hij).quasiMeasurePreserving.ae hp
  have hall : ∀ᵐ x : Fin N → UnitAddCircle ∂periodicHaar (Fin N),
      ∀ i j,i≠j → x i≠x j := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i=j
    · exact Eventually.of_forall (fun _ h => False.elim (h hij))
    · exact (hpair i j hij).mono (fun _ h _ => h)
  filter_upwards [hall] with x hx
  intro i j he
  by_contra hij
  apply hx i j hij
  apply AddCircle.injective_toCircle (by norm_num : (1:ℝ)≠0)
  apply Subtype.ext
  simpa only [periodicD1GoodNodes,fourier_one] using he

/-- The actual finite Haar integral satisfies Good's decreasing-exponent recurrence. -/
theorem periodicD1GoodIntegral_recurrence (s : Finset (Fin N)) (hs : s.Nonempty)
    (a : Fin N → ℕ) (ha : ∀ i∈s,0<a i) :
    periodicD1GoodIntegral s a=
      ∑ i∈s,periodicD1GoodIntegral s (Function.update a i (a i-1)) := by
  unfold periodicD1GoodIntegral
  rw [←integral_finsetSum s (fun i hi => periodicD1GoodWeight_integrable s _)]
  apply integral_congr_ae
  filter_upwards [periodicD1GoodNodes_injective_ae] with x hx
  exact periodicD1GoodWeight_recurrence s hs a ha (periodicD1GoodNodes x)
    (fun j _ => periodicD1GoodNode_ne_zero x j) hx.injOn

lemma periodicD1GoodIntegral_empty (a : Fin N → ℕ) :
    periodicD1GoodIntegral ∅ a=1 := by
  simp [periodicD1GoodIntegral,periodicD1GoodWeight_empty]

lemma periodicD1GoodIntegral_zero (s : Finset (Fin N)) :
    periodicD1GoodIntegral s (fun _ => 0)=1 := by
  simp [periodicD1GoodIntegral,periodicD1GoodWeight_zero]

lemma periodicD1Circle_inverse_character (t : UnitAddCircle) :
    (fourier 1 t)⁻¹=fourier (-1) t := by
  have hn : fourier 1 t≠0 := by
    have h : ‖fourier 1 t‖=1 := by simp [fourier_apply]
    intro hz
    simp only [hz,norm_zero] at h
    exact zero_ne_one h
  apply mul_left_cancel₀ hn
  rw [mul_inv_cancel₀ hn,←fourier_add]
  norm_num [fourier_zero]

lemma periodicD1Circle_inverse_character_pow (n : ℕ) (t : UnitAddCircle) :
    (fourier (-1) t)^n=fourier (-(n:ℤ)) t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,ih,show -((n+1:ℕ):ℤ)=-(n:ℤ)+(-1) by omega,fourier_add]

lemma periodicD1Circle_polynomial_integrable (p : Polynomial ℂ) :
    Integrable (fun t : UnitAddCircle => p.eval (fourier (-1) t)) AddCircle.haarAddCircle :=
  (p.continuous.comp (fourier (-1)).continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Exact Haar integration of every polynomial in the inverse circle coordinate. -/
lemma periodicD1Circle_polynomial_integral (p : Polynomial ℂ) :
    (∫ t : UnitAddCircle,p.eval (fourier (-1) t) ∂AddCircle.haarAddCircle)=p.eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    rw [integral_add (periodicD1Circle_polynomial_integrable p)
      (periodicD1Circle_polynomial_integrable q),hp,hq]
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    simp_rw [periodicD1Circle_inverse_character_pow]
    rw [integral_const_mul,periodicCircle_fourier_integral]
    by_cases hn : n=0
    · simp [hn]
    · have hn' : -(n:ℤ)≠0 := by exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)
      simp [hn,hn']

def periodicD1GoodBoundaryPolynomial (s : Finset (Fin N)) (a : Fin N → ℕ)
    (x : Fin N → UnitAddCircle) (k : Fin N) : Polynomial ℂ :=
  ∏ i∈s.erase k,(1-Polynomial.C (periodicD1GoodNodes x i)*Polynomial.X)^a i

lemma periodicD1GoodBoundaryPolynomial_eval_zero (s : Finset (Fin N)) (a : Fin N → ℕ)
    (x : Fin N → UnitAddCircle) (k : Fin N) :
    (periodicD1GoodBoundaryPolynomial s a x k).eval 0=1 := by
  simp [periodicD1GoodBoundaryPolynomial,Polynomial.eval_prod,Polynomial.eval_pow,
    Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X]

lemma periodicD1GoodWeight_coordinate_factor (s : Finset (Fin N)) (a : Fin N → ℕ)
    (x : Fin N → UnitAddCircle) {k : Fin N} (hk : k∈s) (ha : a k=0)
    (t : UnitAddCircle) :
    periodicD1GoodWeight s a (periodicD1GoodNodes (Function.update x k t))=
      periodicD1GoodWeight (s.erase k) a (periodicD1GoodNodes x) *
        (periodicD1GoodBoundaryPolynomial s a x k).eval (fourier (-1) t) := by
  rw [periodicD1GoodWeight_zero_exponent s a _ hk ha]
  congr 1
  · apply periodicD1GoodWeight_congr_nodes
    intro i hi
    simp only [periodicD1GoodNodes,Function.update_of_ne (Finset.mem_erase.mp hi).1]
  · simp only [periodicD1GoodBoundaryPolynomial,Polynomial.eval_prod,Polynomial.eval_pow,
      Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [periodicD1GoodNodes,Function.update_self,
      Function.update_of_ne (Finset.mem_erase.mp hi).1,div_eq_mul_inv,
      periodicD1Circle_inverse_character]

lemma periodicD1GoodWeight_coordinate_integral (s : Finset (Fin N)) (a : Fin N → ℕ)
    (x : Fin N → UnitAddCircle) {k : Fin N} (hk : k∈s) (ha : a k=0) :
    (∫ t : UnitAddCircle,periodicD1GoodWeight s a
      (periodicD1GoodNodes (Function.update x k t)) ∂AddCircle.haarAddCircle)=
        periodicD1GoodWeight (s.erase k) a (periodicD1GoodNodes x) := by
  simp_rw [periodicD1GoodWeight_coordinate_factor s a x hk ha]
  rw [integral_const_mul,periodicD1Circle_polynomial_integral,
    periodicD1GoodBoundaryPolynomial_eval_zero,mul_one]

/-- Good's deletion boundary for the literal Haar integral; properness is derived. -/
theorem periodicD1GoodIntegral_boundary (s : Finset (Fin N)) (a : Fin N → ℕ)
    {k : Fin N} (hk : k∈s) (ha : a k=0) :
    periodicD1GoodIntegral s a=periodicD1GoodIntegral (s.erase k) a := by
  have hm : MeasurePreserving
      (fun p : (Fin N → UnitAddCircle) × UnitAddCircle => Function.update p.1 k p.2)
      ((periodicHaar (Fin N)).prod AddCircle.haarAddCircle) (periodicHaar (Fin N)) :=
    DGRHS.Concentration.measurePreserving_coordinate_splice
      (fun _ : Fin N => (AddCircle.haarAddCircle : Measure UnitAddCircle)) k
  have hi := periodicD1GoodWeight_integrable s a
  have hp : Integrable (fun p : (Fin N → UnitAddCircle) × UnitAddCircle =>
      periodicD1GoodWeight s a (periodicD1GoodNodes (Function.update p.1 k p.2)))
      ((periodicHaar (Fin N)).prod AddCircle.haarAddCircle) :=
    hm.integrable_comp_of_integrable hi
  have heq : (∫ p : (Fin N → UnitAddCircle) × UnitAddCircle,
      periodicD1GoodWeight s a (periodicD1GoodNodes (Function.update p.1 k p.2))
      ∂(periodicHaar (Fin N)).prod AddCircle.haarAddCircle)=periodicD1GoodIntegral s a := by
    have h := integral_map hm.aemeasurable
      (show AEStronglyMeasurable (fun x => periodicD1GoodWeight s a (periodicD1GoodNodes x))
        (Measure.map (fun p : (Fin N → UnitAddCircle) × UnitAddCircle =>
          Function.update p.1 k p.2) ((periodicHaar (Fin N)).prod AddCircle.haarAddCircle)) from by
        rw [hm.map_eq]
        exact hi.aestronglyMeasurable)
    rw [hm.map_eq] at h
    exact h.symm
  rw [←heq,integral_prod _ hp]
  simp_rw [periodicD1GoodWeight_coordinate_integral s a _ hk ha]
  rfl

end DGRHS.Periodic
