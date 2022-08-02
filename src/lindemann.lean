/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import data.complex.exponential
import data.polynomial.basic
import data.polynomial.taylor
import data.polynomial.iterated_deriv
import ring_theory.algebraic
import measure_theory.integral.set_integral
import measure_theory.integral.interval_integral
import analysis.complex.basic
import analysis.special_functions.polynomials
import field_theory.polynomial_galois_group
import algebra.monoid_algebra.to_direct_sum
import resultant

namespace euclidean_domain
variables {R : Type*} [euclidean_domain R]

lemma pow_sub {a : R} (a0 : a ≠ 0) {m n : ℕ} (hmn : n ≤ m) : a ^ (m - n) = a ^ m / a ^ n := by
{ have : a ^ n * a ^ (m - n) = a ^ n * a ^ m / a ^ n,
  { rw [← pow_add, add_tsub_cancel_of_le hmn, mul_div_cancel_left], exact pow_ne_zero _ a0, },
  rwa [mul_div_assoc _ (pow_dvd_pow a hmn), mul_right_inj'] at this, exact pow_ne_zero _ a0, }

end euclidean_domain

noncomputable theory

open_locale big_operators polynomial classical
open finset

namespace nat

lemma desc_factorial_eq_prod_range (n : ℕ) :
  ∀ k, n.desc_factorial k = ∏ i in range k, (n - i)
| 0       := rfl
| (k + 1) := by rw [desc_factorial, prod_range_succ, mul_comm, desc_factorial_eq_prod_range k]

end nat

@[simp] lemma map_ite {A B : Type*} (f : A → B) (P : Prop) [decidable P] (a b : A) :
  f (if P then a else b) = if P then f a else f b :=
by split_ifs; refl

section

lemma no_zero_smul_divisors.of_algebra_map_injective'
  {R A : Type*} [comm_semiring R] [semiring A] [algebra R A] [no_zero_divisors A]
  (h : function.injective (algebra_map R A)) : no_zero_smul_divisors R A :=
⟨λ c x hcx, (mul_eq_zero.mp ((algebra.smul_def c x).symm.trans hcx)).imp_left
  (map_eq_zero_iff (algebra_map R A) h).mp⟩

end

section
variables {R : Type*}

section char_zero_domain

section
variables [ring R] [no_zero_divisors R] [char_zero R]

@[priority 100] -- see note [lower instance priority]
instance char_zero.no_zero_smul_divisors_int : no_zero_smul_divisors ℤ R :=
no_zero_smul_divisors.of_algebra_map_injective $ (algebra_map ℤ R).injective_int

end

section

variables [semiring R] [no_zero_divisors R] [char_zero R]

@[priority 100] -- see note [lower instance priority]
instance char_zero.no_zero_smul_divisors_nat : no_zero_smul_divisors ℕ R :=
no_zero_smul_divisors.of_algebra_map_injective' $ (algebra_map ℕ R).injective_nat

end

end char_zero_domain

end

namespace polynomial

section
variables {R S : Type*} [semiring R] [semiring S]

lemma map_eq_zero_of_injective
  (f : R →+* S) (hf : function.injective f) {p : R[X]} :
  p.map f = 0 ↔ p = 0 :=
begin
  split, swap, { intro h, rw [h, polynomial.map_zero], },
  rw [← polynomial.map_zero f],
  exact λ h, polynomial.map_injective _ hf h,
end

lemma map_ne_zero_of_injective
  (f : R →+* S) (hf : function.injective f) {p : R[X]} :
  p.map f ≠ 0 ↔ p ≠ 0 :=
not_iff_not_of_iff (map_eq_zero_of_injective f hf)

lemma support_map_subset' [semiring R] [semiring S] (f : R →+* S) (p : R[X]) :
  (map f p).support ⊆ p.support :=
begin
  intros x,
  contrapose!,
  simp { contextual := tt },
end

end

variables {R : Type*} [semiring R]

section
variable {S : Type*}

@[simp]
theorem derivative_map' [semiring S] (p : R[X]) (f : R →+* S) :
  (p.map f).derivative = p.derivative.map f := by
{ let n := max p.nat_degree ((map f p).nat_degree),
  rw [derivative_apply, derivative_apply],
  rw [sum_over_range' _ _ (n + 1) ((le_max_left _ _).trans_lt (lt_add_one _))],
  rw [sum_over_range' _ _ (n + 1) ((le_max_right _ _).trans_lt (lt_add_one _))],
  simp only [polynomial.map_sum, polynomial.map_mul, polynomial.map_C, map_mul, coeff_map,
    map_nat_cast, polynomial.map_nat_cast, polynomial.map_pow, map_X],
  all_goals { intro n, rw [zero_mul, C_0, zero_mul], } }

@[simp]
theorem iterate_derivative_map' [semiring S] (p : R[X]) (f : R →+* S) (k : ℕ):
  polynomial.derivative^[k] (p.map f) = (polynomial.derivative^[k] p).map f :=
begin
  induction k with k ih generalizing p,
  { simp, },
  { simp [ih], },
end

end

lemma sum_ideriv_apply_of_lt' {p : R[X]} {n : ℕ} (hn : p.nat_degree < n) :
  ∑ i in range (p.nat_degree + 1), p.iterated_deriv i =
  ∑ i in range n, p.iterated_deriv i := by
{ obtain ⟨m, hm⟩ := nat.exists_eq_add_of_lt hn, rw [hm, add_right_comm],
  rw [sum_range_add _ _ m], convert (add_zero _).symm, apply sum_eq_zero,
  intros x hx, rw [add_comm, iterated_deriv, function.iterate_add_apply],
  convert iterate_derivative_zero, rw [iterate_derivative_eq_zero], exact lt_add_one _, }

lemma sum_ideriv_apply_of_le' {p : R[X]} {n : ℕ} (hn : p.nat_degree ≤ n) :
  ∑ i in range (p.nat_degree + 1), p.iterated_deriv i =
  ∑ i in range (n + 1), p.iterated_deriv i :=
sum_ideriv_apply_of_lt' (nat.lt_add_one_iff.mpr hn)

def sum_ideriv : R[X] →ₗ[R] R[X] :=
{ to_fun := λ p, ∑ i in range (p.nat_degree + 1), p.iterated_deriv i,
  map_add' := λ p q, by
  { let x := max ((p + q).nat_degree + 1) (max (p.nat_degree + 1) (q.nat_degree + 1)),
    have hpq : ((p + q).nat_degree + 1) ≤ x := le_max_left _ _,
    have hp : (p.nat_degree + 1) ≤ x := (le_max_left _ _).trans (le_max_right _ _),
    have hq : (q.nat_degree + 1) ≤ x := (le_max_right _ _).trans (le_max_right _ _),
    simp_rw [sum_ideriv_apply_of_lt' hpq, sum_ideriv_apply_of_lt' hp,
      sum_ideriv_apply_of_lt' hq, ← sum_add_distrib, iterated_deriv_add], },
  map_smul' := λ a p, by dsimp;
    simp_rw [sum_ideriv_apply_of_le' (nat_degree_smul_le _ _), iterated_deriv_smul, smul_sum] }

lemma sum_ideriv_apply (p : R[X]) :
  p.sum_ideriv = ∑ i in range (p.nat_degree + 1), p.iterated_deriv i := rfl

lemma sum_ideriv_apply_of_lt {p : R[X]} {n : ℕ} (hn : p.nat_degree < n) :
  p.sum_ideriv = ∑ i in range n, p.iterated_deriv i :=
sum_ideriv_apply_of_lt' hn

lemma sum_ideriv_apply_of_le {p : R[X]} {n : ℕ} (hn : p.nat_degree ≤ n) :
  p.sum_ideriv = ∑ i in range (n + 1), p.iterated_deriv i :=
sum_ideriv_apply_of_le' hn

lemma sum_ideriv_zero : (0 : R[X]).sum_ideriv = 0 :=
by rw [sum_ideriv_apply, nat_degree_zero, zero_add, sum_range_one, iterated_deriv_zero_right]

lemma sum_ideriv_C (a : R) : (C a).sum_ideriv = C a :=
by rw [sum_ideriv_apply, nat_degree_C, zero_add, sum_range_one, iterated_deriv_zero_right]

@[simp]
theorem sum_ideriv_map {S : Type*} [comm_semiring S] (p : R[X]) (f : R →+* S) :
  (p.map f).sum_ideriv = p.sum_ideriv.map f := by
{ let n := max (p.map f).nat_degree p.nat_degree,
  rw [sum_ideriv_apply_of_le (le_max_left _ _ : _ ≤ n)],
  rw [sum_ideriv_apply_of_le (le_max_right _ _ : _ ≤ n)],
  simp_rw [polynomial.map_sum, iterated_deriv],
  apply sum_congr rfl, intros x hx,
  rw [iterate_derivative_map' p f x], }

lemma sum_ideriv_eq_self_add (p : R[X]) :
  p.sum_ideriv = p + p.sum_ideriv.derivative := by
{ rw [sum_ideriv_apply, derivative_sum, sum_range_succ', sum_range_succ, add_comm,
    ← add_zero (finset.sum _ _)], simp_rw [← iterated_deriv_succ], congr',
  rw [iterated_deriv_eq_zero_of_nat_degree_lt _ _ (nat.lt_succ_self _)], }

lemma sum_ideriv_derivative (p : R[X]) :
  p.derivative.sum_ideriv = p.sum_ideriv.derivative := by
{ rw [sum_ideriv_apply_of_le ((nat_degree_derivative_le p).trans tsub_le_self),
    sum_ideriv_apply, derivative_sum],
  simp_rw [iterated_deriv, ← function.iterate_succ_apply, function.iterate_succ_apply'], }

def iterated_deriv_linear_map (n : ℕ) : R[X] →ₗ[R] R[X] :=
{ to_fun := λ p, p.iterated_deriv n,
  map_add' := λ p q, iterated_deriv_add p q n,
  map_smul' := λ a p, iterated_deriv_smul p n a }

lemma iterated_deriv_linear_map_apply (p : R[X]) (n : ℕ) :
  iterated_deriv_linear_map n p = p.iterated_deriv n := rfl

variables (f p q : R[X]) (n k : ℕ)

lemma coeff_iterated_deriv_as_prod_range' :
  ∀ m : ℕ, (iterated_deriv f k).coeff m = (∏ i in range k, (m + k - i)) • f.coeff (m + k) :=
begin
  induction k with k ih,
  { simp },
  intro m,
  calc (f.iterated_deriv k.succ).coeff m
      = (∏ i in range k, (m + k.succ - i)) • f.coeff (m + k.succ) * (m + 1) :
    by rw [iterated_deriv_succ, coeff_derivative, ih m.succ, nat.succ_add, nat.add_succ]
  ... = ((∏ i in range k, (m + k.succ - i)) * (m + 1)) • f.coeff (m + k.succ) :
    by rw [← nat.cast_add_one, ← nsmul_eq_mul', smul_smul, mul_comm]
  ... = (∏ i in range k.succ, (m + k.succ - i)) • f.coeff (m + k.succ) :
    by rw [prod_range_succ, add_tsub_assoc_of_le k.le_succ, nat.succ_sub le_rfl, tsub_self]
end

lemma coeff_iterated_deriv_as_desc_factorial (m : ℕ) :
  (iterated_deriv f k).coeff m = (m + k).desc_factorial k • f.coeff (m + k) :=
by rw [coeff_iterated_deriv_as_prod_range', ← nat.desc_factorial_eq_prod_range]

end polynomial

open polynomial
open_locale nat

variables {R : Type*} [comm_ring R] [is_domain R]

@[simp] lemma derivative_X_sub_C_pow (r : R) :
  ∀ (n : ℕ), derivative ((X - C r) ^ n : R[X]) = (n : R[X]) * (X - C r) ^ (n - 1)
| 0       := by rw [pow_zero, nat.cast_zero, derivative_one, zero_mul]
| 1       := by rw [pow_one, nat.cast_one, derivative_sub, derivative_X, derivative_C, tsub_self,
  pow_zero, sub_zero, mul_one]
| (n + 1 + 1) := by rw [pow_succ, derivative_mul, derivative_X_sub_C_pow, mul_comm (_ - _),
  mul_assoc, ← pow_succ', add_tsub_cancel_right, add_tsub_cancel_right, ← add_mul, derivative_sub,
  derivative_X, derivative_C, sub_zero, nat.cast_add (_ + _), add_comm ↑_, nat.cast_one]

lemma iterated_deriv_X_sub_C_pow (r : R) (k : ℕ) :
  ∀ (n : ℕ), iterated_deriv ((X - C r) ^ k : R[X]) n = k.desc_factorial n • (X - C r) ^ (k - n)
| 0       := by rw [iterated_deriv_zero_right, nat.desc_factorial, one_smul, tsub_zero]
| (n + 1) := by rw [iterated_deriv_succ, iterated_deriv_X_sub_C_pow n, derivative_smul,
  derivative_X_sub_C_pow, nat.desc_factorial, ← nsmul_eq_mul, smul_smul, mul_comm, tsub_tsub]

lemma iterated_deriv_dvd_factorial (p : R[X]) (k : ℕ) :
  ∃ (p' : R[X]), p.iterated_deriv k = k! * p' :=
by use ∑ (x : ℕ) in (p.iterated_deriv k).support, (x + k).choose k • C (p.coeff (x + k)) * X ^ x;
  conv_lhs { rw [(p.iterated_deriv k).as_sum_support_C_mul_X_pow], };
  rw [← nsmul_eq_mul, smul_sum]; congr'; funext i;
calc C ((p.iterated_deriv k).coeff i) * X ^ i
    = C ((i + k).desc_factorial k • p.coeff (i + k)) * X ^ i :
      by rw [coeff_iterated_deriv_as_desc_factorial]
... = C ((k! * (i + k).choose k) • p.coeff (i + k)) * X ^ i :
      by rw [nat.desc_factorial_eq_factorial_mul_choose]
... = (k! * (i + k).choose k) • C (p.coeff (i + k)) * X ^ i :
      by rw [smul_C]
... = k! • (i + k).choose k • C (p.coeff (i + k)) * X ^ i :
      by rw [mul_smul]
... = k! • ((i + k).choose k • C (p.coeff (i + k)) * X ^ i) :
      by rw [smul_mul_assoc]

def iterated_deriv_small (p : R[X]) (r : R) (q : ℕ)
  {p' : R[X]} (hp : p = (X - C r) ^ q * p')
  {k : ℕ} (hk : k < q) :
  (p.iterated_deriv k).eval r = 0 := by
{ have h : ∀ x, (X - C r : R[X]) ^ (q - (k - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (k - x) - 1),
  { intros x, rw [← pow_add, add_tsub_cancel_of_le], rw [nat.lt_iff_add_one_le] at hk,
    exact (le_tsub_of_add_le_left hk).trans (tsub_le_tsub_left (tsub_le_self : _ ≤ k) _), },
  simp_rw [hp, iterated_deriv_mul, iterated_deriv_X_sub_C_pow, ← smul_mul_assoc, smul_smul, h,
    ← mul_smul_comm, mul_assoc, ← mul_sum, eval_mul, pow_one, eval_sub, eval_X, eval_C, sub_self,
    zero_mul], }

def iterated_deriv_of_eq (p : R[X]) (r : R) (q : ℕ)
  {p' : R[X]} (hp : p = (X - C r) ^ q * p') :
  (p.iterated_deriv q).eval r = q! * eval r p' := by
{ have h : ∀ x ≥ 1, x ≤ q →
    (X - C r : R[X]) ^ (q - (q - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (q - x) - 1),
  { intros x h h', rw [← pow_add, add_tsub_cancel_of_le], rwa [tsub_tsub_cancel_of_le h'], },
  simp_rw [hp, iterated_deriv_mul, iterated_deriv_X_sub_C_pow, ← smul_mul_assoc, smul_smul],
  rw [sum_range_succ', nat.choose_zero_right, one_mul, tsub_zero, nat.desc_factorial_self,
    tsub_self, pow_zero, smul_mul_assoc, one_mul, iterated_deriv_zero_right, eval_add, eval_smul],
  convert zero_add _, rw [← coe_eval_ring_hom, map_sum], apply sum_eq_zero, intros x hx,
  rw [coe_eval_ring_hom, h (x + 1) le_add_self (nat.add_one_le_iff.mpr (mem_range.mp hx)),
    pow_one, eval_mul, eval_smul, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
    smul_zero, zero_mul], rw [nsmul_eq_mul], }

section
variables {A : Type*} [comm_ring A] [algebra R A]

lemma is_integral.aeval {x : A} (h : is_integral R x) (p : R[X]) :
  is_integral R (aeval x p) := by
{ rw [aeval_eq_sum_range],
  apply is_integral.sum,
  intros i hi,
  apply is_integral_smul,
  exact h.pow _, }

end

def iterated_deriv_large (p : R[X]) (r : R)
  (q : ℕ) {k : ℕ} (hk : q ≤ k) :
  ∃ n', (p.iterated_deriv k).eval r = q! * n' := by
{ obtain ⟨p', hp'⟩ := iterated_deriv_dvd_factorial p k,
  use (k.desc_factorial (k - q) : ℤ) • p'.eval r,
  rw [hp', eval_mul, ← C_eq_nat_cast, eval_C,
    ← nat.factorial_mul_desc_factorial (tsub_le_self : k - q ≤ k), tsub_tsub_cancel_of_le hk,
    nat.cast_mul, zsmul_eq_mul, int.cast_coe_nat, mul_assoc], }

lemma sum_ideriv_sl (p : R[X]) (r : R)
  (q : ℕ) {p' : R[X]} (hp : p = (X - C r) ^ q * p') :
  ∃ n', p.sum_ideriv.eval r = q! * n' := by
{ have h : ∀ k, ∃ n', (p.iterated_deriv k).eval r = q! * n',
  { intros k, cases lt_or_ge k q with hk hk,
    { use 0, rw [mul_zero, iterated_deriv_small p r q hp hk], },
    { exact iterated_deriv_large p r q hk, }, },
  let c := λ k, classical.some (h k),
  have hc : ∀ k, (p.iterated_deriv k).eval r = q! * c k := λ k, classical.some_spec (h k),
  use (range (p.nat_degree + 1)).sum c,
  simp_rw [sum_ideriv_apply, ← coe_eval_ring_hom, map_sum, coe_eval_ring_hom, hc, ← mul_sum], }

lemma sum_ideriv_sl' (p : R[X]) (r : R)
  {q : ℕ} (hq : 0 < q)
  {p' : R[X]} (hp : p = (X - C r) ^ (q - 1) * p') :
  ∃ n', p.sum_ideriv.eval r = (q - 1)! * p'.eval r + q! * n' := by
{ cases eq_or_ne p 0 with p0 p0,
  { use 0, rw [p0] at ⊢ hp,
    replace hp := (mul_eq_zero.mp hp.symm).resolve_left _,
    rw [sum_ideriv_zero, hp, eval_zero, mul_zero, mul_zero, add_zero],
    exact λ h, X_sub_C_ne_zero r (pow_eq_zero h), },
  have : range (p.nat_degree + 1) = range q ∪ Ico q (p.nat_degree + 1),
  { rw [range_eq_Ico, Ico_union_Ico_eq_Ico hq.le],
    have h := congr_arg nat_degree hp.symm,
    rw [nat_degree_mul, nat_degree_pow, nat_degree_X_sub_C, mul_one] at h,
    replace h := le_iff_exists_add.mpr ⟨p'.nat_degree, h.symm⟩,
    exact tsub_le_iff_right.mp h,
    { exact pow_ne_zero _ (X_sub_C_ne_zero r), },
    { intros p0', rw [p0', mul_zero] at hp, exact p0 hp, }, },
  let c := λ k, if hk : q ≤ k then classical.some (iterated_deriv_large p r q hk) else 0,
  have hc : ∀ k (hk : q ≤ k), (p.iterated_deriv k).eval r = q! * c k := λ k hk,
    by { simp_rw [c, dif_pos hk], exact classical.some_spec (iterated_deriv_large p r q hk), },
  use ∑ (x : ℕ) in Ico q (p.nat_degree + 1), c x, rw [← zero_add (↑(q - 1)! * p'.eval r)],
  rw [sum_ideriv_apply, ← coe_eval_ring_hom, map_sum, coe_eval_ring_hom, this, sum_union,
    (by rw [tsub_add_cancel_of_le (nat.one_le_of_lt hq)] : range q = range (q - 1 + 1)),
    sum_range_succ], congr' 1, congr' 1,
  { exact sum_eq_zero (λ x hx, iterated_deriv_small p r _ hp (mem_range.mp hx)), },
  { rw [← iterated_deriv_of_eq _ _ _ hp], },
  { rw [mul_sum, sum_congr rfl], intros k hk, exact hc k (mem_Ico.mp hk).1, },
  { rw [range_eq_Ico, disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem],
    intros x hx, rw [mem_inter, mem_Ico, mem_Ico] at hx, exact hx.1.2.not_le hx.2.1, }, }

lemma remove_X_factor {x : ℝ} (hx : x ≠ 0) (p' : ℤ[X]) (p0' : p' ≠ 0) (p_ann' : aeval x p' = 0) :
  ∃ (p : ℤ[X]) (p0 : p ≠ 0) (hp : ¬ X ∣ p), aeval x p = 0 := by
{ revert p0' p_ann', refine unique_factorization_monoid.induction_on_prime p' (absurd rfl) _ _,
  { intros p p_unit p0 p_ann,
    obtain ⟨r, unit_r, hr⟩ := polynomial.is_unit_iff.mp p_unit,
    rw [← hr, aeval_C, algebra_map_int_eq, ring_hom.eq_int_cast, int.cast_eq_zero] at p_ann,
    rw [int.is_unit_iff, p_ann, zero_eq_neg] at unit_r,
    exact (unit_r.elim zero_ne_one one_ne_zero).elim, },
  { intros a p a0 prime_p h pa0 pa_ann, obtain ⟨p0, a0⟩ := mul_ne_zero_iff.mp pa0,
    rw [aeval_mul, mul_eq_zero] at pa_ann,
    refine pa_ann.elim (λ p_ann, _) (λ a_ann, h a0 a_ann),
    refine ⟨p, p0, λ hX, _, p_ann⟩,
    obtain ⟨u, hu⟩ := (@prime_X ℤ _ _).associated_of_dvd prime_p hX,
    obtain ⟨r, unit_r, hr⟩ := polynomial.is_unit_iff.mp u.is_unit, rw [int.is_unit_iff] at unit_r,
    rw [← hu, ← hr, aeval_mul, aeval_X, aeval_C,
        algebra_map_int_eq, ring_hom.eq_int_cast] at p_ann,
    exact unit_r.elim (λ h', hx (by rwa [h', int.cast_one, mul_one] at p_ann))
      (λ h', hx
        (by rwa [h', int.cast_neg, mul_neg, int.cast_one, mul_one, neg_eq_zero] at p_ann)), }, }

namespace complex

section
variables {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} {s : set ℝ}

open filter asymptotics set function
open_locale classical topological_space
open complex

lemma deriv_within_cexp_real (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, complex.exp (f x)) s x = complex.exp (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.cexp.deriv_within hxs

@[simp] lemma deriv_cexp_real (hc : differentiable_at ℝ f x) :
  deriv (λx, complex.exp (f x)) x = complex.exp (f x) * (deriv f x) :=
hc.has_deriv_at.cexp.deriv

end

end complex

open complex

lemma differentiable_at.real_of_complex {e : ℂ → ℂ} {z : ℝ} (h : differentiable_at ℂ e ↑z) :
  differentiable_at ℝ (λ (x : ℝ), e ↑x) z :=
(h.restrict_scalars ℝ).comp z of_real_clm.differentiable.differentiable_at

lemma differentiable.real_of_complex {e : ℂ → ℂ} (h : differentiable ℂ e) :
  differentiable ℝ (λ (x : ℝ), e ↑x) :=
(h.restrict_scalars ℝ).comp of_real_clm.differentiable

lemma deriv_eq_f (p : ℂ[X]) (s : ℂ) :
  deriv (λ (x : ℝ), -(exp (-(x • exp (s.arg • I))) * p.sum_ideriv.eval (x • exp (s.arg • I))) /
    exp (s.arg • I)) =
  λ (x : ℝ), exp (-(x • exp (s.arg • I))) * p.eval (x • exp (s.arg • I)) := by
{ have h : (λ (y : ℝ), p.sum_ideriv.eval (y • exp (s.arg • I))) =
    (λ x, p.sum_ideriv.eval x) ∘ (λ y, y • exp (s.arg • I)) := rfl,
  funext, rw [deriv_div_const, deriv.neg, deriv_mul, deriv_cexp_real, deriv.neg],
  any_goals { simp_rw [h] }, clear h,
  rw [deriv_smul_const, deriv_id'', deriv.comp, polynomial.deriv, deriv_smul_const, deriv_id''],
  simp_rw [derivative_map, one_smul, mul_assoc, ← mul_add],
  have h : exp (s.arg • I) * p.sum_ideriv.eval (x • exp (s.arg • I)) -
    p.sum_ideriv.derivative.eval (x • exp (s.arg • I)) * exp (s.arg • I) =
    p.eval (x • exp (s.arg • I)) * exp (s.arg • I) := by
  { conv_lhs { congr, rw [sum_ideriv_eq_self_add], },
    rw [mul_comm, eval_add, add_mul, add_sub_cancel], },
  rw [← mul_neg, neg_add', neg_mul, neg_neg, h, ← mul_assoc, mul_div_cancel],
  exact exp_ne_zero _,
  any_goals { apply differentiable.differentiable_at },
  rotate 5, apply @differentiable.real_of_complex (λ c : ℂ, exp (-(c * exp (s.arg • I)))),
  rotate 1, apply differentiable.comp, apply @differentiable.restrict_scalars ℝ _ ℂ,
  any_goals { repeat
  { apply differentiable.neg <|>
    apply differentiable.cexp <|>
    apply differentiable.mul_const <|>
    apply polynomial.differentiable <|>
    apply differentiable.smul_const <|>
    exact differentiable_id } }, }

lemma integral_f_eq (p : ℂ[X]) (s : ℂ) :
  ∫ x in 0..s.abs, exp (-(x • exp (s.arg • I))) * p.eval (x • exp (s.arg • I)) =
    -(exp (-s) * p.sum_ideriv.eval s ) / exp (s.arg • I) -
    -(p.sum_ideriv.eval 0) / exp (s.arg • I) := by
{ convert interval_integral.integral_deriv_eq_sub' (λ (x : ℝ), -(exp (-(x • exp (s.arg • I))) *
    p.sum_ideriv.eval (x • exp (s.arg • I))) / exp (s.arg • I)) (deriv_eq_f p s) _ _,
  any_goals { simp_rw [real_smul, abs_mul_exp_arg_mul_I], },
  { simp_rw [zero_smul, neg_zero', complex.exp_zero, one_mul], },
  { intros x hx, apply (differentiable.mul _ _).neg.div_const.differentiable_at,
    apply @differentiable.real_of_complex (λ c : ℂ, exp (-(c * exp (s.arg • I)))),
    refine (differentiable_id.mul_const _).neg.cexp,
    convert_to differentiable ℝ ((λ (y : ℂ), p.sum_ideriv.eval y) ∘
      (λ (x : ℝ), x • exp (s.arg • I))),
    apply differentiable.comp,
    apply @differentiable.restrict_scalars ℝ _ ℂ, exact polynomial.differentiable _,
    exact differentiable_id'.smul_const _, },
  { refine ((continuous_id'.smul continuous_const).neg.cexp.mul _).continuous_on,
    convert_to continuous ((λ (y : ℂ), p.eval y) ∘ (λ (x : ℝ), x • exp (s.arg • I))),
    exact p.continuous_aeval.comp (continuous_id'.smul continuous_const), }, }

def P (p : ℂ[X]) (s : ℂ) := exp s * p.sum_ideriv.eval (0 : ℂ) - p.sum_ideriv.eval s

lemma P_le' (p : ℕ → ℂ[X]) (s : ℂ)
  (h : ∃ c, ∀ (q : ℕ) (x ∈ set.Ioc 0 s.abs), ((p q).eval (x • exp (s.arg • I))).abs ≤ c ^ q) :
  ∃ c ≥ 0, ∀ (q : ℕ), (P (p q) s).abs ≤
  real.exp s.re * (real.exp s.abs * c ^ q * s.abs) := by
{ simp_rw [P], cases h with c hc, replace hc := λ q x hx, (hc q x hx).trans (le_abs_self _),
  simp_rw [_root_.abs_pow] at hc, use [|c|, abs_nonneg _], intros q,
  have h := integral_f_eq (p q) s,
  rw [← sub_div, eq_div_iff (exp_ne_zero _), ← @mul_right_inj' _ _ (exp s) _ _ (exp_ne_zero _),
    neg_sub_neg, mul_sub, ← mul_assoc _ (exp _), ← exp_add, add_neg_self, exp_zero, one_mul] at h,
  replace h := congr_arg complex.abs h,
  simp_rw [complex.abs_mul, abs_exp, smul_re, I_re, smul_zero, real.exp_zero, mul_one] at h,
  rw [← h, mul_le_mul_left (real.exp_pos _), ← complex.norm_eq_abs,
    interval_integral.integral_of_le (complex.abs_nonneg _)], clear h,
  convert measure_theory.norm_set_integral_le_of_norm_le_const' _ _ _,
  { rw [real.volume_Ioc, sub_zero, ennreal.to_real_of_real (complex.abs_nonneg _)], },
  { rw [real.volume_Ioc, sub_zero], exact ennreal.of_real_lt_top, },
  { exact measurable_set_Ioc, },
  intros x hx, rw [norm_mul], refine mul_le_mul _ (hc q x hx) (norm_nonneg _) (real.exp_pos _).le,
  rw [norm_eq_abs, abs_exp, real.exp_le_exp], apply (re_le_abs _).trans, rw [← norm_eq_abs,
    norm_neg, norm_smul, norm_eq_abs, abs_exp, smul_re, I_re, smul_zero, real.exp_zero, mul_one,
    real.norm_eq_abs, abs_eq_self.mpr hx.1.le], exact hx.2, }

lemma P_le (p : ℕ → ℂ[X]) (s : ℂ)
  (h : ∃ c, ∀ (q : ℕ) (x ∈ set.Ioc 0 s.abs), ((p q).eval (x • exp (s.arg • I))).abs ≤ c ^ q) :
  ∃ c ≥ 0, ∀ q ≥ 1, (P (p q) s).abs ≤ c ^ q := by
{ simp_rw [P], obtain ⟨c', hc', h'⟩ := P_le' p s h, clear h,
  let c₁ := max (real.exp s.re) 1,
  let c₂ := max (real.exp s.abs) 1, have h₂ : 0 ≤ real.exp s.abs := (real.exp_pos _).le,
  let c₃ := max s.abs 1,            have h₃ : 0 ≤ s.abs := abs_nonneg _,
  have hc : ∀ {x : ℝ}, 0 ≤ max x 1 := λ x, zero_le_one.trans (le_max_right _ _),
  use [c₁ * (c₂ * c' * c₃), mul_nonneg hc (mul_nonneg (mul_nonneg hc hc') hc)],
  intros q hq, refine (h' q).trans _, simp_rw [mul_pow],
  have hcq : ∀ {x : ℝ}, 0 ≤ max x 1 ^ q := λ x, pow_nonneg hc q,
  have hcq' := pow_nonneg hc' q,
  have le_max_one_pow : ∀ {x : ℝ}, x ≤ max x 1 ^ q := λ x, (max_cases x 1).elim
    (λ h, h.1.symm ▸ le_self_pow h.2 hq) (λ h, by rw [h.1, one_pow]; exact h.2.le),
  refine mul_le_mul le_max_one_pow _ (mul_nonneg (mul_nonneg h₂ hcq') h₃) hcq,
  refine mul_le_mul _ le_max_one_pow h₃ (mul_nonneg hcq hcq'),
  refine mul_le_mul le_max_one_pow le_rfl hcq' hcq, }

variables {ι : Type*} [fintype ι]
  (c : ι → ℤ) (t : ι → ℤ[X])
/-
  (t0 : ∀ i, t i ≠ 0)
  (ht : ∀ i j, i ≠ j →
    multiset.disjoint ((t i).map (algebra_map ℤ ℂ)).roots ((t j).map (algebra_map ℤ ℂ)).roots)-/

lemma sum_P_eq (hct : ∑ i, c i • (((t i).map (algebra_map ℤ ℂ)).roots.map exp).sum = 0) (p : ℂ[X]) :
  ∑ i, c i • (((t i).map (algebra_map ℤ ℂ)).roots.map (P p)).sum =
  -∑ i, c i • (((t i).map (algebra_map ℤ ℂ)).roots.map (λ r, p.sum_ideriv.eval r)).sum :=
by simp_rw [P, multiset.sum_map_sub, smul_sub, sum_sub_distrib, multiset.sum_map_mul_right,
  ← smul_mul_assoc, ← sum_mul, hct, zero_mul, zero_sub]

def F (q : ℕ) (p : ℤ[X]) : ℤ[X] :=
p ^ (q - 1)

def F_ℂ (q : ℕ) (p : ℤ[X]) : ℂ[X] :=
(F q p).map (algebra_map ℤ ℂ)

lemma F_eq (q : ℕ) (p : ℤ[X]) :
  F_ℂ q p = C ((p.map (algebra_map ℤ ℂ)).leading_coeff ^ (q - 1)) *
    ((p.map (algebra_map ℤ ℂ)).roots.map (λ (r : ℂ), (X - C r) ^ (q - 1))).prod := by
{ rw [F_ℂ, F, polynomial.map_pow, multiset.prod_map_pow, C_pow, ← mul_pow], congr' 1,
  have : (p.map (algebra_map ℤ ℂ)).roots.card = (p.map (algebra_map ℤ ℂ)).nat_degree :=
    splits_iff_card_roots.mp (is_alg_closed.splits _),
  rw [C_leading_coeff_mul_prod_multiset_X_sub_C this], }

section
open list

@[simp, to_additive]
lemma list.prod_map_erase {ι M : Type*}
  [decidable_eq ι] [comm_monoid M] (f : ι → M) {a} :
  ∀ {l : list ι}, a ∈ l → f a * ((l.erase a).map f).prod = (l.map f).prod
| (b :: l) h :=
  begin
    obtain rfl | ⟨ne, h⟩ := decidable.list.eq_or_ne_mem_of_mem h,
    { simp only [list.map, list.erase_cons_head, list.prod_cons] },
    { simp only [list.map, list.erase, if_neg (mt eq.symm ne),
      list.prod_cons, list.prod_map_erase h, mul_left_comm (f a) (f b)], }
  end

@[simp, to_additive]
lemma multiset.prod_map_erase {ι α : Type*} [comm_monoid α]
  {m : multiset ι} (f : ι → α)
  [decidable_eq ι] {a : ι} (h : a ∈ m) :
  f a * ((m.erase a).map f).prod = (m.map f).prod :=
by rw [← m.coe_to_list, multiset.coe_erase, multiset.coe_map, multiset.coe_map,
multiset.coe_prod, multiset.coe_prod, list.prod_map_erase f ((m.mem_to_list a).2 h)]
end

lemma eval_root_derivative (p : ℂ[X]) {r : ℂ} (hr : r ∈ p.roots) :
  p.derivative.eval r = p.leading_coeff * ((p.roots.erase r).map (λ x, r - x)).prod := by
{ have : p.roots.card = p.nat_degree :=
    splits_iff_card_roots.mp (is_alg_closed.splits _),
  conv_lhs { rw [← C_leading_coeff_mul_prod_multiset_X_sub_C this], },
  simp_rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_prod, derivative_sub,
    derivative_X, derivative_C, sub_zero, mul_one, ← coe_eval_ring_hom, map_mul, map_multiset_sum,
    multiset.map_map, function.comp, map_multiset_prod, multiset.map_map, function.comp, map_sub,
    coe_eval_ring_hom, eval_C, eval_X], congr' 1,
  have : (p.roots.map (λ y, ((p.roots.erase y).map (λ (x : ℂ), r - x)).prod)).sum =
    ((p.roots.erase r).map (λ x, r - x)).prod +
    ((p.roots.erase r).map (λ y, ((p.roots.erase y).map (λ x, r - x)).prod)).sum,
  { rw [multiset.sum_map_erase (λ y, ((p.roots.erase y).map (λ x, r - x)).prod) hr], },
  rw [this, add_right_eq_self, ← @multiset.sum_map_zero ℂ _ _ (p.roots.erase r)],
  congr' 1, refine multiset.map_congr rfl (λ x hx, _),
  rw [multiset.prod_eq_zero_iff, multiset.mem_map],
  refine ⟨r, _, sub_self _⟩,
  rcases eq_or_ne r x with rfl | h,
  { exact hx }, exact (multiset.mem_erase_of_ne h).mpr hr, }

lemma eval_root_derivative' (p : ℂ[X]) {r : ℂ} (hr : r ∈ p.roots) :
  p.derivative.eval r =
    (C p.leading_coeff * ((p.roots.erase r).map (λ x, X - C x)).prod).eval r :=
by simp_rw [eval_root_derivative _ hr, eval_mul, eval_multiset_prod, multiset.map_map,
  function.comp, eval_sub, eval_X, eval_C]
/-
def aeval_of_mem_roots (p : ℤ[X]) {x : ℂ} (hx : x ∈ (p.map (algebra_map ℤ ℂ)).roots) :
  aeval x p = 0 := by
{ rcases eq_or_ne p 0 with rfl | p0, { rw [aeval_zero], },
  have map_p0 : p.map (algebra_map ℤ ℂ) ≠ 0 :=
    (polynomial.map_ne_zero_of_injective _ (algebra_map ℤ ℂ).injective_int).mpr p0,
  rw [aeval_def, eval₂_eq_eval_map], exact (mem_roots map_p0).mp hx, }

def mem_roots_iff_aeval {p : ℤ[X]} (p0 : p ≠ 0) (x : ℂ) :
  x ∈ (p.map (algebra_map ℤ ℂ)).roots ↔ aeval x p = 0 := by
{ refine ⟨aeval_of_mem_roots _, λ h, _⟩,
  have map_p0 : p.map (algebra_map ℤ ℂ) ≠ 0 :=
    (polynomial.map_ne_zero_of_injective _ (algebra_map ℤ ℂ).injective_int).mpr p0,
  rw [mem_roots map_p0], rwa [aeval_def, eval₂_eq_eval_map] at h, }

lemma eval_F_ℂ {q : ℕ} (q0 : 0 < q) {p : ℤ[X]} (p0 : p ≠ 0)
  {r : ℂ} (hr : r ∈ (p.map (algebra_map ℤ ℂ)).roots) :
  (F_ℂ q p).eval r = 37 :=
begin
  have : (F_ℂ q p).eval r = (p.map (algebra_map ℤ ℂ) ^ q).derivative.eval r / q,
  { rw [F_ℂ, F, eq_div_iff (nat.cast_ne_zero.mpr (pos_iff_ne_zero.mp q0) : (q : ℂ) ≠ 0), mul_comm,
      ← eval_C_mul, derivative_pow, derivative_map, mul_assoc, polynomial.map_mul,
      polynomial.map_pow, C_eq_nat_cast], },
  have hr' : r ∈ (p.map (algebra_map ℤ ℂ) ^ q).roots,
  { rwa [← polynomial.map_pow, mem_roots_iff_aeval (pow_ne_zero _ p0), map_pow,
      (pow_eq_zero_iff q0 : _ ↔ _ = (0 : ℂ)), ← mem_roots_iff_aeval p0], },
  rw [this, derivative_eval_root _ hr', leading_coeff_pow],
  
end
-/

lemma F_sum_ideriv_eval (p : ℤ[X]) {r : ℂ} (hr : r ∈ (p.map (algebra_map ℤ ℂ)).roots)
  {q : ℕ} (hq : 0 < q) :
  ∃ n', (F_ℂ q p).sum_ideriv.eval r =
    (q - 1)! * (p.map (algebra_map ℤ ℂ)).derivative.eval r ^ (q - 1) + q! * n' := by
{ rw [eval_root_derivative' _ hr, ← eval_pow],
  refine sum_ideriv_sl' _ _ hq _,
  rw [F_eq, ← multiset.prod_map_erase _ hr, mul_left_comm, mul_pow, multiset.prod_map_pow,
    C_pow], }

lemma sum_P_F_eq (q : ℕ)
  (hct : ∑ i, c i • (((t i).map (algebra_map ℤ ℂ)).roots.map exp).sum = 0) (p : ℤ[X]) :
  ∑ i, c i • (((t i).map (algebra_map ℤ ℂ)).roots.map (P (F_ℂ q p))).sum =
  -∑ i, c i • (((t i).map (algebra_map ℤ ℂ)).roots.map (λ r, (F_ℂ q p).sum_ideriv.eval r)).sum + 1 :=
begin
  simp_rw [sum_P_eq _ _ hct, ← coe_eval_ring_hom, ← map_multiset_sum],
  
end


/-
lemma lemma_A (M : multiset (ℤ × ℤ[X])) (m0 : ∀ (m : ℤ × ℤ[X]), m ∈ M → m.2 ≠ 0)
  (ht : (M.map (λ m : ℤ × ℤ[X],
    m.1 • ((m.2.map (algebra_map ℤ ℂ)).roots.map (λ r, exp r)).sum)).sum = 0) :
  ∀ (m : ℤ × ℤ[X]), m ∈ M → m.1 = 0 := by
{ let f : ∀ q (prime_q : nat.prime q),
    ∀ (m : ℤ × ℤ[X]), m ∈ M → ∀ (r : ℂ), r ∈ (m.2.map (algebra_map ℤ ℂ)).roots → ℂ[X] :=
    λ q prime_q m hm r hr, (M.map (λ m : ℤ × ℤ[X],
      ((m.2.map (algebra_map ℤ ℂ)).roots.map (λ r, (X - C r) ^ q)).sum)).prod / (X - C r),
  let I : ∀ (s : ℝ) q (prime_q : nat.prime q),
    ∀ (m : ℤ × ℤ[X]), m ∈ M → ∀ (r : ℂ), r ∈ (m.2.map (algebra_map ℤ ℂ)).roots → ℂ :=
    λ s q prime_q m hm r hr, 
  
}-/
.
/-
@[simps apply]
def finsupp.map_domain.add_equiv {α : Type*} {β : Type*} {M : Type*} [add_comm_monoid M]
  (f : α ≃ β) :
  (α →₀ M) ≃+ (β →₀ M) :=
{ to_fun := (finsupp.equiv_map_domain f : (α →₀ M) → (β →₀ M)),
  inv_fun := (finsupp.equiv_map_domain f.symm : (β →₀ M) → (α →₀ M)),
  map_add' := λ x y,
    by simp_rw [finsupp.equiv_map_domain_eq_map_domain, finsupp.map_domain_add],
  ..finsupp.equiv_congr_left f }

namespace add_monoid_algebra

@[simps apply]
def ring_equiv_congr_left {R : Type*} {S : Type*} {G : Type*}
  [semiring R] [semiring S] [add_monoid G] (f : R ≃+* S) :
  add_monoid_algebra R G ≃+* add_monoid_algebra S G :=
{ to_fun := (finsupp.map_range f f.map_zero :
    (add_monoid_algebra R G) → (add_monoid_algebra S G)),
  inv_fun := (finsupp.map_range f.symm f.symm.map_zero :
    (add_monoid_algebra S G) → (add_monoid_algebra R G)),
  map_mul' := λ x y,
  begin
    ext, simp_rw [mul_apply, mul_def,
      finsupp.map_range_apply, finsupp.sum_apply, map_finsupp_sum],
    rw [finsupp.sum_map_range_index], congrm finsupp.sum x (λ g1 r1, _),
    rw [finsupp.sum_map_range_index], congrm finsupp.sum y (λ g2 r2, _),
    { rw [finsupp.single_apply], split_ifs; simp only [map_mul, map_zero], contradiction, },
    all_goals { intro, simp only [mul_zero, zero_mul], simp only [if_t_t, finsupp.sum_zero], },
  end,
  ..finsupp.map_range.add_equiv f.to_add_equiv }

@[simps apply]
def ring_equiv_of_add_equiv_right {R : Type*} {G : Type*} {H : Type*}
  [semiring R] [add_monoid G] [add_monoid H] (f : G ≃+ H) :
  add_monoid_algebra R G ≃+* add_monoid_algebra R H :=
{ to_fun := (finsupp.equiv_map_domain f : add_monoid_algebra R G → add_monoid_algebra R H),
  inv_fun := (finsupp.equiv_map_domain f.symm : add_monoid_algebra R H → add_monoid_algebra R G),
  map_mul' := λ x y,
  begin
    ext, simp_rw [mul_apply, mul_def,
      finsupp.equiv_map_domain_apply, finsupp.sum_apply, finsupp.equiv_map_domain_eq_map_domain],
    rw [finsupp.sum_map_domain_index], congrm finsupp.sum x (λ g1 r1, _),
    rw [finsupp.sum_map_domain_index], congrm finsupp.sum y (λ g2 r2, _),
    { rw [finsupp.single_apply, equiv.eq_symm_apply, add_equiv.coe_to_equiv, map_add], },
    all_goals { intro, simp only [mul_zero, zero_mul], simp only [if_t_t, finsupp.sum_zero], },
    all_goals { intros m₁ m₂, simp only [mul_add, add_mul, ite_add_zero, finsupp.sum_add], },
  end,
  ..finsupp.map_domain.add_equiv f.to_equiv }

@[simps apply]
def ring_hom_of_add_monoid_hom_right {R : Type*} {G : Type*} {H : Type*}
  [semiring R] [add_monoid G] [add_monoid H] (f : G →+ H) :
  add_monoid_algebra R G →+* add_monoid_algebra R H :=
{ to_fun := finsupp.map_domain f,
  map_one' := by simp_rw [one_def, finsupp.map_domain_single, map_zero],
  map_mul' := λ x y,
  begin
    simp_rw [mul_def, finsupp.map_domain_sum],
    rw [finsupp.sum_map_domain_index], congrm finsupp.sum x (λ g1 r1, _),
    rw [finsupp.sum_map_domain_index], congrm finsupp.sum y (λ g2 r2, _),
    { rw [finsupp.map_domain_single, map_add], },
    all_goals { intro, simp only [mul_zero, zero_mul, finsupp.single_zero, finsupp.sum_zero], },
    all_goals { intros m₁ m₂, simp only [mul_add, add_mul, finsupp.single_add, finsupp.sum_add], },
  end,
  ..finsupp.map_domain.add_monoid_hom f }

private lemma eq_zero_or_eq_zero_of_mul_eq_zero_finite
  {R : Type*} {S : Type*} {M : Type*} [ring R] [is_domain R] [linear_ordered_semiring S]
  [add_comm_group M] [module S M] [module.free S M] [module.finite S M]
  (p q : add_monoid_algebra R M) (h : p * q = 0) : p = 0 ∨ q = 0 :=
begin
  
end

@[simps apply]
def finsupp.rename {R : Type*} {S : Type*} {ι : Type*} {ι' : Type*}
  [semiring R] [semiring S] (f : ι → ι') :
  add_monoid_algebra R (ι →₀ S) →+* add_monoid_algebra R (ι' →₀ S) :=
{ to_fun := ring_hom_of_add_monoid_hom_right
    (finsupp.map_domain.add_monoid_hom f : (ι →₀ S) →+ (ι' →₀ S)),
  ..ring_hom_of_add_monoid_hom_right _ }

@[simp] lemma finsupp.rename_rename {R : Type*} {S : Type*} {ι : Type*} {σ : Type*} {τ : Type*}
  [semiring R] [semiring S]
  (f : ι → σ) (g : σ → τ) (p : add_monoid_algebra R (ι →₀ S)) :
  finsupp.rename g (finsupp.rename f p) = finsupp.rename (g ∘ f) p :=
begin
  simp_rw [finsupp.rename_apply, ring_hom_of_add_monoid_hom_right_apply],
  conv_rhs { rw [finsupp.map_domain.add_monoid_hom_comp, add_monoid_hom.coe_comp,
    finsupp.map_domain_comp], },
end

lemma finsupp.rename_injective {R : Type*} {S : Type*} {ι : Type*} {ι' : Type*}
  [semiring R] [semiring S] (f : ι → ι') (hf : function.injective f) :
  function.injective (add_monoid_algebra.finsupp.rename f :
    add_monoid_algebra R (ι →₀ S) → add_monoid_algebra R (ι' →₀ S)) :=
finsupp.map_domain_injective (finsupp.map_domain_injective hf)

theorem finsupp.exists_finset_rename {R : Type*} {S : Type*} {ι : Type*}
  [semiring R] [semiring S] (p : add_monoid_algebra R (ι →₀ S)) :
  ∃ (s : finset ι) (q : add_monoid_algebra R ({x // x ∈ s} →₀ S)),
    p = finsupp.rename coe q :=
begin
  let s := p.support.bUnion (λ m, m.support),
  set f : add_monoid_algebra R (ι →₀ S) → add_monoid_algebra R (s →₀ S) :=
    ring_hom_of_add_monoid_hom_right
    (finsupp.comap_domain.add_monoid_hom subtype.coe_injective : (ι →₀ S) →+ (s →₀ S)) with hf,
  use s, use f p,
  simp_rw [hf, finsupp.rename_apply,
    ring_hom_of_add_monoid_hom_right_apply,
    ← finsupp.map_domain_comp, function.comp,
    finsupp.comap_domain.add_monoid_hom_apply, finsupp.map_domain.add_monoid_hom_apply],
  rw [finsupp.map_domain], conv_lhs { rw [← finsupp.sum_single p] },
  apply finsupp.sum_congr, intros x hx, congr' 1,
  rw [finsupp.map_domain_comap_domain coe subtype.coe_injective], rw [subtype.range_coe],
  intros a ha, simp_rw [← finset.mem_def, mem_bUnion], exact ⟨x, hx, ha⟩,
end

@[simps] def finsupp.option_equiv_left {R : Type*} {S : Type*} {ι : Type*}
  [comm_semiring R] [semiring S] :
  add_monoid_algebra R (option ι →₀ S) ≃ₐ[R] add_monoid_algebra (add_monoid_algebra R (ι →₀ S)) ι :=
alg_equiv.of_alg_hom

private lemma eq_zero_or_eq_zero_of_mul_eq_zero
  {R : Type*} (S : Type*) {M : Type*} [ring R] [is_domain R] [linear_ordered_semiring S]
  [add_comm_group M] [module S M] [module.free S M]
  (p q : add_monoid_algebra R M) (h : p * q = 0) : p = 0 ∨ q = 0 :=
begin
  have rp := ring_equiv_of_add_equiv_right (module.free.repr S M).to_add_equiv p,
  have rq := ring_equiv_of_add_equiv_right (module.free.repr S M).to_add_equiv q,
  have : rp * rq = 0 → rp = 0 ∨ rq = 0 := λ rh, by
  { obtain ⟨s, rp, rfl⟩ := finsupp.exists_finset_rename rp,
    obtain ⟨t, rq, rfl⟩ := finsupp.exists_finset_rename rq,
    have :
      finsupp.rename
        (subtype.map id (finset.subset_union_left s t) : {x // x ∈ s} → {x // x ∈ s ∪ t}) rp *
      finsupp.rename
        (subtype.map id (finset.subset_union_right s t) : {x // x ∈ t} → {x // x ∈ s ∪ t}) rq = 0,
    { apply finsupp.rename_injective _ subtype.val_injective,
      simpa only [map_mul, map_zero, finsupp.rename_rename, mul_eq_zero] using rh, },
    letI := mv_polynomial.is_domain_fintype R {x // x ∈ (s ∪ t)},
    rw mul_eq_zero at this,
    cases this; [left, right],
    all_goals { simpa using congr_arg (rename subtype.val) this }
  },
  revert h, simpa only [← map_mul, ring_equiv.map_eq_zero_iff] using this,
end

def is_domain
  {R : Type*} (S : Type*) {M : Type*} [ring R] [is_domain R] [linear_ordered_semiring S]
  [add_comm_group M] [module S M] [module.free S M] :
  is_domain (add_monoid_algebra R M) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero S,
  .. (infer_instance : nontrivial (add_monoid_algebra R M)), }

end add_monoid_algebra

theorem eq_zero_or_eq_zero_of_mul_eq_zero
  {R : Type*} [comm_ring R] [is_domain R] {σ : Type*}
  (p q : mv_polynomial σ R) (h : p * q = 0) : p = 0 ∨ q = 0 :=
begin
  obtain ⟨s, p, rfl⟩ := mv_polynomial.exists_finset_rename p,
  obtain ⟨t, q, rfl⟩ := mv_polynomial.exists_finset_rename q,
  have :
    mv_polynomial.rename (subtype.map id (finset.subset_union_left s t) : {x // x ∈ s} → {x // x ∈ s ∪ t}) p *
    mv_polynomial.rename (subtype.map id (finset.subset_union_right s t) : {x // x ∈ t} → {x // x ∈ s ∪ t}) q = 0,
  { apply mv_polynomial.rename_injective _ subtype.val_injective,
    simpa only [map_mul, map_zero, mv_polynomial.rename_rename, mul_eq_zero] using h, },
  letI := mv_polynomial.is_domain_fintype R {x // x ∈ (s ∪ t)},
  rw mul_eq_zero at this,
  cases this; [left, right],
  all_goals { simpa using congr_arg (rename subtype.val) this }
end
-/
.

section
variables {K : Type*} {L : Type*}
variables [field K] [field L] [algebra K L] {p : polynomial K}

open intermediate_field

lemma adjoin_root_set_is_splitting_field {p : polynomial K} (hp : p.splits (algebra_map K L)) :
  p.is_splitting_field K (adjoin K (p.root_set L)) := sorry

end

section
variables (s : finset ℂ)

abbreviation Poly : ℚ[X] := ∏ x in s, minpoly ℚ x

abbreviation K' (s : finset ℂ) : intermediate_field ℚ ℂ :=
intermediate_field.adjoin ℚ ((Poly s).root_set ℂ)

instance : is_splitting_field ℚ (K' s) (Poly s) :=
adjoin_root_set_is_splitting_field (is_alg_closed.splits_codomain (Poly s))

abbreviation K : Type* := (Poly s).splitting_field

instance : is_domain (add_monoid_algebra (K s) (K s)) := sorry

abbreviation Gal : Type* := (Poly s).gal

abbreviation Lift : K' s ≃ₐ[ℚ] K s := is_splitting_field.alg_equiv (K' s) (Poly s)

instance algebra_K : algebra (K s) ℂ :=
((K' s).val.comp (Lift s).symm.to_alg_hom).to_ring_hom.to_algebra

lemma algebra_map_K_apply (x) : algebra_map (K s) ℂ x = ((Lift s).symm x : ℂ) :=
rfl

def exp_monoid_hom : multiplicative ℂ →* ℂ :=
{ to_fun := λ x, exp x.to_add,
  map_one' := by rw [to_add_one, exp_zero],
  map_mul' := λ x y, by rw [to_add_mul, exp_add], }

def Eval : add_monoid_algebra (K s) (K s) →ₐ[K s] ℂ :=
add_monoid_algebra.lift (K s) (K s) ℂ
  (exp_monoid_hom.comp (add_monoid_hom.to_multiplicative (algebra_map (K s) ℂ).to_add_monoid_hom))

lemma Eval_apply (x : add_monoid_algebra (K s) (K s)) :
  Eval s x = x.sum (λ a c, c • exp (algebra_map (K s) ℂ a)) := rfl

lemma Poly_ne_zero (hs : ∀ x ∈ s, is_integral ℚ x) : Poly s ≠ 0 :=
prod_ne_zero_iff.mpr (λ x hx, minpoly.ne_zero (hs x hx))

section
variables {ι : Type*} [fintype ι]

abbreviation Range (u : ι → ℂ) (v : ι → ℂ) : finset ℂ := univ.image u ∪ univ.image v

lemma linear_independent_exp_aux' (s : finset ℂ)
  (f : add_monoid_algebra (K s) (K s)) (f0 : f ≠ 0) (hf : f ∈ (Eval s).to_ring_hom.ker) :
  ∃ (w : ℤ) (q : finset (K s)) (w' : q → ℤ),
    (w + ∑ x : q, w' x * ∑ f : (Gal s),
      exp (algebra_map (K s) ℂ (f x)) : ℂ) = 0 := by
{ 
  let v : ∏ f : Gal s,
  
}

#check add_monoid_algebra.map_domain_alg_hom
#check finsupp.map_domain
#check alg_equiv.of_alg

lemma linear_independent_exp_aux
  (u : ι → ℂ) (hu : ∀ i, is_integral ℚ (u i)) (u_inj : function.injective u)
  (v : ι → ℂ) (hv : ∀ i, is_integral ℚ (v i)) (v0 : v ≠ 0)
  (h : ∑ i, v i * exp (u i) = 0) :
  ∃ (w : ℤ) (q : finset (K (Range u v))) (w' : q → ℤ),
    (w + ∑ x : q, w' x * ∑ f : (Gal (Range u v)),
      exp (algebra_map (K (Range u v)) ℂ (f x)) : ℂ) = 0 := by
{ let s := Range u v,
  have hs : ∀ x ∈ s, is_integral ℚ x,
  { intros x hx,
    cases mem_union.mp hx with hxu hxv,
    { obtain ⟨i, _, rfl⟩ := finset.mem_image.mp hxu,
      exact hu i, },
    { obtain ⟨i, _, rfl⟩ := finset.mem_image.mp hxv,
      exact hv i, }, },
  have u_mem : ∀ i, u i ∈ K' s,
  { intros i,
    apply intermediate_field.subset_adjoin,
    rw [mem_root_set (Poly_ne_zero s hs), map_prod, prod_eq_zero_iff],
    exact ⟨u i, mem_union_left _ (finset.mem_image.mpr ⟨i, mem_univ _, rfl⟩), minpoly.aeval _ _⟩, },
  have v_mem : ∀ i, v i ∈ K' s,
  { intros i,
    apply intermediate_field.subset_adjoin,
    rw [mem_root_set (Poly_ne_zero s hs), map_prod, prod_eq_zero_iff],
    exact ⟨v i, mem_union_right _ (finset.mem_image.mpr ⟨i, mem_univ _, rfl⟩), minpoly.aeval _ _⟩, },
  let ι' : set ι := {i | v i ≠ 0},
  let u' : ∀ i, K s := λ i : ι', Lift s ⟨u i, u_mem i⟩,
  let v' : ∀ i, K s := λ i : ι', Lift s ⟨v i, v_mem i⟩,
  have u'_inj : function.injective u' :=
    λ i j hij, subtype.coe_injective (u_inj (subtype.mk.inj ((Lift s).injective hij))),
  have v'_ne_zero : ∀ i, v' i ≠ 0 := λ i, by
  { rw [ne.def, add_equiv_class.map_eq_zero_iff, ← add_submonoid_class.coe_eq_zero, subtype.coe_mk],
    exact i.2, },
  replace h : ∑ i, (algebra_map (K s) ℂ (v' i)) * exp (algebra_map (K s) ℂ (u' i)) = 0,
  { simp_rw [algebra_map_K_apply, alg_equiv.symm_apply_apply, ← h],
    symmetry, apply sum_congr_set,
    { intros x hx, refl, },
    intros x hx,
    rw [set.mem_set_of_eq, not_not] at hx,
    rw [hx, zero_mul], },
  
  let f : add_monoid_algebra (K s) (K s) :=
  { support := image u' univ,
    to_fun := λ x, if hx : x ∈ image u' univ
      then v' (u'_inj.inv_of_mem_range ⟨x, mem_image_univ_iff_mem_range.mp hx⟩) else 0,
    mem_support_to_fun := λ x, ⟨λ hx, by { rw [dif_pos hx], exact v'_ne_zero _, },
                                by { contrapose!, intros hx, rw [dif_neg hx], }⟩ },
  have f_apply : ∀ x (hx : x ∈ image u' univ),
    f x = v' (u'_inj.inv_of_mem_range ⟨x, mem_image_univ_iff_mem_range.mp hx⟩),
  { intros x hx, rw [finsupp.coe_mk, dif_pos hx], },
  replace hf : Eval s f = 0,
  { rw [Eval_apply, ← h, finsupp.sum, (_ : f.support = image u' univ)], swap, { refl, },
    rw [sum_image, sum_congr rfl], swap, { exact λ i hi j hj hij, u'_inj hij, },
    intros x hx,
    rw [f_apply, u'_inj.right_inv_of_inv_of_mem_range], { refl },
    exact mem_image_of_mem _ (mem_univ _), },
  have f0 : f ≠ 0,
  { rw [ne.def, function.funext_iff] at v0, push_neg at v0,
    cases v0 with i hi,
    rw [pi.zero_apply] at hi,
    have h : f (u' ⟨i, hi⟩) ≠ 0,
    { rw [f_apply], exact v'_ne_zero _, exact mem_image_of_mem _ (mem_univ _), },
    intros f0,
    rw [f0, finsupp.zero_apply] at h,
    exact absurd rfl h, },
  rw [← alg_hom.coe_to_ring_hom, ← ring_hom.mem_ker] at hf,
  exact linear_independent_exp_aux' s f f0 hf, }

#check ring_hom.field_range
#check lift_of_splits s
#check function.injective.inv_of_mem_range
#check function.injective.inv_of_mem_range
#check ring_hom.ker
#check ring_hom.is_domain
#exit

end
lemma linear_independent_exp (s : finset (integral_closure ℚ ℂ)) :
  linear_independent (integral_closure ℚ ℂ) (λ x : s, exp x) := by
{ sorry
  
}

lemma linear_independent_exp' (s : finset ℂ) (hs : ∀ x ∈ s, is_algebraic ℤ x) :
  linear_independent (integral_closure ℚ ℂ) (λ x : s, exp x) := by
{ have hs' : ∀ x ∈ s, is_integral ℚ x := λ x hx, is_algebraic_iff_is_integral.mp
    (is_algebraic_of_larger_base_of_injective ((algebra_map ℤ ℚ).injective_int) (hs x hx)),
  let s' : finset (integral_closure ℚ ℂ) := finset.subtype _ s,
  have := linear_independent_exp s',
  refine (linear_independent_equiv' _ _).mp this,
  { exact
    { to_fun    := λ ⟨x, hx⟩, ⟨↑x, finset.mem_subtype.mp hx⟩,
      inv_fun   := λ ⟨x, hx⟩, ⟨⟨x, hs' x hx⟩, finset.mem_subtype.mpr (by rwa [subtype.coe_mk])⟩,
      left_inv  := λ ⟨x, hx⟩, by rw [subtype.mk_eq_mk, set_like.eta],
      right_inv := λ ⟨x, hx⟩, by rw [subtype.mk_eq_mk, subtype.coe_mk], }, },
  funext x, cases x, simp only [equiv.coe_fn_mk, function.comp_app, subtype.coe_mk, coe_coe], }

lemma linear_independent_exp'' (s : finset ℂ) (hs : ∀ x ∈ s, is_algebraic ℤ x)
  (g : ℂ → ℂ) (hg : ∀ x ∈ s, is_algebraic ℤ (g x)) (h : ∑ x in s, g x * exp x = 0) :
  ∀ x ∈ s, g x = 0 := by
{ have hs' : ∀ x ∈ s, is_integral ℚ x := λ x hx, is_algebraic_iff_is_integral.mp
    (is_algebraic_of_larger_base_of_injective ((algebra_map ℤ ℚ).injective_int) (hs x hx)),
  have hg' : ∀ x ∈ s, is_integral ℚ (g x) := λ x hx, is_algebraic_iff_is_integral.mp
    (is_algebraic_of_larger_base_of_injective ((algebra_map ℤ ℚ).injective_int) (hg x hx)),
  have := linear_independent_exp' s hs,
  rw [fintype.linear_independent_iff] at this,
  have h' : ∑ (x : s), (⟨g x.1, hg' x.1 x.2⟩ : integral_closure ℚ ℂ) • exp ↑x = 0,
  { simp_rw [subalgebra.smul_def, subtype.coe_mk, subtype.val_eq_coe],
    convert_to ∑ (x : s), (λ (x : ℂ), g x * exp x) ↑x = 0,
    rwa [sum_coe_sort], },
  intros x hx,
  specialize this (λ (x : s), ⟨g x.1, hg' x.1 x.2⟩) h' ⟨x, hx⟩,
  rwa [← subtype.coe_inj, subtype.coe_mk, subalgebra.coe_zero] at this, }

/-- `X ^ n + a` is monic. -/
lemma monic_X_pow_add_C {R : Type*} [ring R] (a : R) {n : ℕ} (h : n ≠ 0) : (X ^ n + C a).monic :=
begin
  obtain ⟨k, hk⟩ := nat.exists_eq_succ_of_ne_zero h,
  convert monic_X_pow_add _,
  exact le_trans degree_C_le nat.with_bot.coe_nonneg,
end

lemma complex.is_integral_int_I : is_integral ℤ I := by
{ refine ⟨X^2 + C 1, monic_X_pow_add_C _ two_ne_zero, _⟩,
  rw [eval₂_add, eval₂_X_pow, eval₂_C, I_sq, ring_hom.eq_int_cast, int.cast_one, add_left_neg], }

lemma complex.is_integral_rat_I : is_integral ℚ I :=
is_integral_of_is_scalar_tower _ complex.is_integral_int_I

open complex

lemma transcendental_pi : transcendental ℤ real.pi := by
{ intro h,
  have pi_is_integral' : is_integral ℚ real.pi := is_algebraic_iff_is_integral.mp
    (is_algebraic_of_larger_base_of_injective ((algebra_map ℤ ℚ).injective_int) h),
  have pi_is_integral : is_integral ℚ (algebra_map ℝ ℂ real.pi) :=
    (is_integral_algebra_map_iff ((algebra_map ℝ ℂ).injective)).mpr pi_is_integral',
  have hs : ∀ (x : ℂ), x ∈ ({real.pi * I, 0} : finset ℂ) → is_algebraic ℤ x,
  { intros x hx, simp only [finset.mem_insert, finset.mem_singleton] at hx,
    rw [is_fraction_ring.is_algebraic_iff ℤ ℚ ℂ, is_algebraic_iff_is_integral],
    cases hx, { rw [hx], exact is_integral_mul pi_is_integral complex.is_integral_rat_I, },
    rw [hx], exact is_integral_zero, },
  have := linear_independent_exp'' {real.pi * I, 0} hs (λ s, 1) _ _ 0 _,
  { simpa only [one_ne_zero] using this, },
  { intros x hx, simp only [finset.mem_insert, finset.mem_singleton] at hx,
    rw [is_fraction_ring.is_algebraic_iff ℤ ℚ ℂ, is_algebraic_iff_is_integral],
    exact is_integral_one, },
  { rw [sum_pair (mul_ne_zero (of_real_ne_zero.mpr real.pi_ne_zero) I_ne_zero)],
    simp_rw [exp_pi_mul_I, exp_zero], ring, },
  simp only [eq_self_iff_true, or_true, finset.mem_insert, finset.mem_singleton, zero_eq_mul,
    of_real_eq_zero], }
