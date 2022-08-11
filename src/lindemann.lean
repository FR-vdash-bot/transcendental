/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import data.complex.exponential
import data.polynomial.iterated_deriv
import ring_theory.algebraic
import measure_theory.integral.set_integral
import measure_theory.integral.interval_integral
import analysis.complex.basic
import analysis.special_functions.polynomials
import field_theory.polynomial_galois_group

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

variables {R : Type*}

section semiring
variables {S : Type*} [semiring R]

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

lemma sum_ideriv_derivative (p : R[X]) :
  p.derivative.sum_ideriv = p.sum_ideriv.derivative := by
{ rw [sum_ideriv_apply_of_le ((nat_degree_derivative_le p).trans tsub_le_self),
    sum_ideriv_apply, derivative_sum],
  simp_rw [iterated_deriv, ← function.iterate_succ_apply, function.iterate_succ_apply'], }

lemma sum_ideriv_eq_self_add (p : R[X]) :
  p.sum_ideriv = p + p.derivative.sum_ideriv := by
{ rw [sum_ideriv_derivative, sum_ideriv_apply, derivative_sum, sum_range_succ', sum_range_succ,
    add_comm, ← add_zero (finset.sum _ _)], simp_rw [← iterated_deriv_succ], congr',
  rw [iterated_deriv_eq_zero_of_nat_degree_lt _ _ (nat.lt_succ_self _)], }

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

end semiring

section ring
variables [ring R]

lemma sum_ideriv_sub (p : R[X]) :
  p.sum_ideriv - p.derivative.sum_ideriv = p :=
by rw [sum_ideriv_eq_self_add, add_sub_cancel]

def sum_ideriv_linear_equiv : R[X] ≃ₗ[R] R[X] :=
{ to_fun := λ p, ∑ i in range (p.nat_degree + 1), p.iterated_deriv i,
  inv_fun := λ p, p - p.derivative,
  left_inv := λ p, by simp_rw [← sum_ideriv_apply, ← sum_ideriv_derivative, sum_ideriv_sub],
  right_inv := λ p, by simp_rw [← sum_ideriv_apply, map_sub, sum_ideriv_sub],
  .. sum_ideriv }

lemma sum_ideriv_linear_equiv_apply (p : R[X]) :
  p.sum_ideriv_linear_equiv = ∑ i in range (p.nat_degree + 1), p.iterated_deriv i := rfl

lemma sum_ideriv_linear_equiv_symm_apply (p : R[X]) :
  sum_ideriv_linear_equiv.symm p = p - p.derivative := rfl

lemma sum_ideriv_linear_equiv_eq_sum_ideriv (p : R[X]) :
  p.sum_ideriv_linear_equiv = p.sum_ideriv := rfl

end ring

end polynomial

open polynomial
open_locale nat

variables {R A : Type*} [comm_ring R] [is_domain R]
  [comm_ring A] [is_domain A] [algebra R A]

@[simp] lemma derivative_X_sub_C_pow (r : R) :
  ∀ (n : ℕ), derivative ((X - C r) ^ n : R[X]) = n • (X - C r) ^ (n - 1)
| 0       := by rw [pow_zero, nsmul_eq_mul, nat.cast_zero, derivative_one, zero_mul]
| 1       := by rw [pow_one, nsmul_eq_mul, nat.cast_one, derivative_sub, derivative_X,
  derivative_C, tsub_self, pow_zero, sub_zero, mul_one]
| (n + 1 + 1) := by rw [pow_succ, derivative_mul, derivative_X_sub_C_pow, nsmul_eq_mul,
  nsmul_eq_mul, mul_comm (_ - _), mul_assoc, ← pow_succ', add_tsub_cancel_right,
  add_tsub_cancel_right, ← add_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
  nat.cast_add (_ + _), add_comm ↑_, nat.cast_one]

lemma iterated_deriv_X_sub_C_pow (r : R) (k : ℕ) :
  ∀ (n : ℕ), iterated_deriv ((X - C r) ^ k : R[X]) n = k.desc_factorial n • (X - C r) ^ (k - n)
| 0       := by rw [iterated_deriv_zero_right, nat.desc_factorial, one_smul, tsub_zero]
| (n + 1) := by rw [iterated_deriv_succ, iterated_deriv_X_sub_C_pow n, derivative_smul,
  derivative_X_sub_C_pow, nat.desc_factorial, smul_smul, mul_comm, tsub_tsub]

lemma iterated_deriv_eq_factorial_mul (p : R[X]) (k : ℕ) :
  ∃ (gp : R[X]), p.iterated_deriv k = k! • gp :=
begin
  use ∑ (x : ℕ) in (p.iterated_deriv k).support, (x + k).choose k • C (p.coeff (x + k)) * X ^ x,
  conv_lhs { rw [(p.iterated_deriv k).as_sum_support_C_mul_X_pow], },
  rw [smul_sum], congr', funext i,
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
        by rw [smul_mul_assoc],
end

lemma iterated_deriv_small (p : R[X]) (q : ℕ) (r : A)
  {p' : A[X]} (hp : p.map (algebra_map R A) = (X - C r) ^ q * p')
  {k : ℕ} (hk : k < q) :
  aeval r (p.iterated_deriv k) = 0 :=
begin
  have h : ∀ x, (X - C r) ^ (q - (k - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (k - x) - 1),
  { intros x, rw [← pow_add, add_tsub_cancel_of_le], rw [nat.lt_iff_add_one_le] at hk,
    exact (le_tsub_of_add_le_left hk).trans (tsub_le_tsub_left (tsub_le_self : _ ≤ k) _), },
  rw [aeval_def, eval₂_eq_eval_map, iterated_deriv, ← iterate_derivative_map, ← iterated_deriv],
  simp_rw [hp, iterated_deriv_mul, iterated_deriv_X_sub_C_pow, ← smul_mul_assoc, smul_smul, h,
    ← mul_smul_comm, mul_assoc, ← mul_sum, eval_mul, pow_one, eval_sub, eval_X, eval_C, sub_self,
    zero_mul],
end

lemma iterated_deriv_of_eq (p : R[X]) (q : ℕ) (r : A)
  {p' : A[X]} (hp : p.map (algebra_map R A) = (X - C r) ^ q * p') :
  aeval r (p.iterated_deriv q) = q! • p'.eval r :=
begin
  have h : ∀ x ≥ 1, x ≤ q →
    (X - C r) ^ (q - (q - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (q - x) - 1),
  { intros x h h', rw [← pow_add, add_tsub_cancel_of_le], rwa [tsub_tsub_cancel_of_le h'], },
  rw [aeval_def, eval₂_eq_eval_map, iterated_deriv, ← iterate_derivative_map, ← iterated_deriv],
  simp_rw [hp, iterated_deriv_mul, iterated_deriv_X_sub_C_pow, ← smul_mul_assoc, smul_smul],
  rw [sum_range_succ', nat.choose_zero_right, one_mul, tsub_zero, nat.desc_factorial_self,
    tsub_self, pow_zero, smul_mul_assoc, one_mul, iterated_deriv_zero_right, eval_add, eval_smul],
  convert zero_add _, rw [← coe_eval_ring_hom, map_sum], apply sum_eq_zero, intros x hx,
  rw [coe_eval_ring_hom, h (x + 1) le_add_self (nat.add_one_le_iff.mpr (mem_range.mp hx)),
    pow_one, eval_mul, eval_smul, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
    smul_zero, zero_mul],
end

variable (A)

lemma iterated_deriv_large (p : R[X]) (q : ℕ)
  {k : ℕ} (hk : q ≤ k) :
  ∃ (gp : R[X]), ∀ (r : A), aeval r (p.iterated_deriv k) = q! • aeval r gp :=
begin
  obtain ⟨p', hp'⟩ := iterated_deriv_eq_factorial_mul p k,
  use (k.desc_factorial (k - q) : ℤ) • p',
  intros r,
  rw [hp', aeval_def, eval₂_eq_eval_map, nsmul_eq_mul, polynomial.map_mul,
    polynomial.map_nat_cast],
  rw [eval_mul, eval_nat_cast,
    ← nat.factorial_mul_desc_factorial (tsub_le_self : k - q ≤ k), tsub_tsub_cancel_of_le hk,
    nat.cast_mul, mul_assoc],
  rw [aeval_def, eval₂_eq_eval_map, zsmul_eq_mul, polynomial.map_mul,
    map_int_cast, eval_mul, eval_int_cast, int.cast_coe_nat, nsmul_eq_mul],
end

lemma sum_ideriv_sl (p : R[X]) (q : ℕ) :
  ∃ (gp : R[X]), ∀ (r : A) {p' : A[X]} (hp : p.map (algebra_map R A) = (X - C r) ^ q * p'),
    aeval r p.sum_ideriv = q! • aeval r gp :=
begin
  have h : ∀ k,
    ∃ (gp : R[X]), ∀ (r : A) {p' : A[X]} (hp : p.map (algebra_map R A) = (X - C r) ^ q * p'),
    aeval r (p.iterated_deriv k) = q! • aeval r gp,
  { intros k, cases lt_or_ge k q with hk hk,
    { use 0, intros r p' hp, rw [map_zero, smul_zero, iterated_deriv_small p q r hp hk], },
    { obtain ⟨gp, h⟩ := iterated_deriv_large A p q hk, refine ⟨gp, λ r p' hp, h r⟩, }, },
  let c := λ k, (h k).some,
  have hc : ∀ k, ∀ (r : A) {p' : A[X]} (hp : p.map (algebra_map R A) = (X - C r) ^ q * p'),
    aeval r (p.iterated_deriv k) = q! • aeval r (c k) := λ k, (h k).some_spec,
  use (range (p.nat_degree + 1)).sum c,
  intros r p' hp,
  rw [sum_ideriv_apply, map_sum], simp_rw [hc _ r hp, map_sum, smul_sum],
end

lemma sum_ideriv_sl' (p : R[X]) {q : ℕ} (hq : 0 < q) :
  ∃ (gp : R[X]), ∀ (inj_amap : function.injective (algebra_map R A))
    (r : A) {p' : A[X]} (hp : p.map (algebra_map R A) = (X - C r) ^ (q - 1) * p'),
    aeval r p.sum_ideriv = (q - 1)! • p'.eval r + q! • aeval r gp :=
begin
  rcases eq_or_ne p 0 with rfl | p0,
  { use 0, intros inj_amap r p' hp,
    rw [map_zero, map_zero, smul_zero, add_zero], rw [polynomial.map_zero] at hp,
    replace hp := (mul_eq_zero.mp hp.symm).resolve_left _,
    rw [hp, eval_zero, smul_zero],
    exact λ h, X_sub_C_ne_zero r (pow_eq_zero h), },
  let c := λ k, if hk : q ≤ k then (iterated_deriv_large A p q hk).some else 0,
  have hc : ∀ k (hk : q ≤ k) (r : A), aeval r (p.iterated_deriv k) = q! • aeval r (c k) := λ k hk,
    by { simp_rw [c, dif_pos hk], exact (iterated_deriv_large A p q hk).some_spec, },
  use ∑ (x : ℕ) in Ico q (p.nat_degree + 1), c x,
  intros inj_amap r p' hp,
  have : range (p.nat_degree + 1) = range q ∪ Ico q (p.nat_degree + 1),
  { rw [range_eq_Ico, Ico_union_Ico_eq_Ico hq.le],
    have h := nat_degree_map_le (algebra_map R A) p,
    rw [congr_arg nat_degree hp, nat_degree_mul, nat_degree_pow, nat_degree_X_sub_C, mul_one,
      ← nat.sub_add_comm (nat.one_le_of_lt hq), tsub_le_iff_right] at h,
    exact le_of_add_le_left h,
    { exact pow_ne_zero _ (X_sub_C_ne_zero r), },
    { rintros rfl, rw [mul_zero, map_eq_zero_of_injective _ inj_amap] at hp, exact p0 hp, }, },
  rw [← zero_add ((q - 1)! • p'.eval r)],
  rw [sum_ideriv_apply, map_sum, map_sum, this, sum_union,
    (by rw [tsub_add_cancel_of_le (nat.one_le_of_lt hq)] : range q = range (q - 1 + 1)),
    sum_range_succ], congr' 1, congr' 1,
  { exact sum_eq_zero (λ x hx, iterated_deriv_small p _ r hp (mem_range.mp hx)), },
  { rw [← iterated_deriv_of_eq _ _ _ hp], },
  { rw [smul_sum, sum_congr rfl], intros k hk, exact hc k (mem_Ico.mp hk).1 r, },
  { rw [range_eq_Ico, disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem],
    intros x hx, rw [mem_inter, mem_Ico, mem_Ico] at hx, exact hx.1.2.not_le hx.2.1, },
end

variable {A}

lemma remove_X_factor {x : ℝ} (hx : x ≠ 0) (p' : ℤ[X]) (p0' : p' ≠ 0) (p_ann' : aeval x p' = 0) :
  ∃ (p : ℤ[X]) (p0 : p ≠ 0) (hp : ¬ X ∣ p), aeval x p = 0 :=
begin
  revert p0' p_ann', refine unique_factorization_monoid.induction_on_prime p' (absurd rfl) _ _,
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
        (by rwa [h', int.cast_neg, mul_neg, int.cast_one, mul_one, neg_eq_zero] at p_ann)), },
end

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
  λ (x : ℝ), exp (-(x • exp (s.arg • I))) * p.eval (x • exp (s.arg • I)) :=
begin
  have h : (λ (y : ℝ), p.sum_ideriv.eval (y • exp (s.arg • I))) =
    (λ x, p.sum_ideriv.eval x) ∘ (λ y, y • exp (s.arg • I)) := rfl,
  funext, rw [deriv_div_const, deriv.neg, deriv_mul, deriv_cexp, deriv.neg],
  any_goals { simp_rw [h] }, clear h,
  rw [deriv_smul_const, deriv_id'', deriv.comp, polynomial.deriv, deriv_smul_const, deriv_id''],
  simp_rw [derivative_map, one_smul, mul_assoc, ← mul_add],
  have h : exp (s.arg • I) * p.sum_ideriv.eval (x • exp (s.arg • I)) -
    p.sum_ideriv.derivative.eval (x • exp (s.arg • I)) * exp (s.arg • I) =
    p.eval (x • exp (s.arg • I)) * exp (s.arg • I) := by
  { conv_lhs { congr, rw [sum_ideriv_eq_self_add, sum_ideriv_derivative], },
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
    exact differentiable_id }, },
end

lemma integral_f_eq (p : ℂ[X]) (s : ℂ) :
  ∫ x in 0..s.abs, exp (-(x • exp (s.arg • I))) * p.eval (x • exp (s.arg • I)) =
    -(exp (-s) * p.sum_ideriv.eval s ) / exp (s.arg • I) -
    -(p.sum_ideriv.eval 0) / exp (s.arg • I) :=
begin
  convert interval_integral.integral_deriv_eq_sub' (λ (x : ℝ), -(exp (-(x • exp (s.arg • I))) *
    p.sum_ideriv.eval (x • exp (s.arg • I))) / exp (s.arg • I)) (deriv_eq_f p s) _ _,
  any_goals { simp_rw [real_smul, abs_mul_exp_arg_mul_I], },
  { simp_rw [zero_smul, neg_zero', complex.exp_zero, one_mul], },
  { intros x hx, apply (differentiable.mul _ _).neg.div_const.differentiable_at,
    apply @differentiable.real_of_complex (λ c : ℂ, exp (-(c * exp (s.arg • I)))),
    refine (differentiable_id.mul_const _).neg.cexp,
    change differentiable ℝ ((λ (y : ℂ), p.sum_ideriv.eval y) ∘
      (λ (x : ℝ), x • exp (s.arg • I))),
    apply differentiable.comp,
    apply @differentiable.restrict_scalars ℝ _ ℂ, exact polynomial.differentiable _,
    exact differentiable_id'.smul_const _, },
  { refine ((continuous_id'.smul continuous_const).neg.cexp.mul _).continuous_on,
    change continuous ((λ (y : ℂ), p.eval y) ∘ (λ (x : ℝ), x • exp (s.arg • I))),
    exact p.continuous_aeval.comp (continuous_id'.smul continuous_const), },
end

def P (p : ℂ[X]) (s : ℂ) := exp s * p.sum_ideriv.eval 0 - p.sum_ideriv.eval s

lemma P_le' (p : ℕ → ℂ[X]) (s : ℂ)
  (h : ∃ c, ∀ (q : ℕ) (x ∈ set.Ioc 0 s.abs), ((p q).eval (x • exp (s.arg • I))).abs ≤ c ^ q) :
  ∃ c ≥ 0, ∀ (q : ℕ), (P (p q) s).abs ≤
  real.exp s.re * (real.exp s.abs * c ^ q * s.abs) :=
begin
  simp_rw [P], cases h with c hc, replace hc := λ q x hx, (hc q x hx).trans (le_abs_self _),
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
    real.norm_eq_abs, abs_eq_self.mpr hx.1.le], exact hx.2,
end

lemma P_le (p : ℕ → ℂ[X]) (s : ℂ)
  (h : ∃ c, ∀ (q : ℕ) (x ∈ set.Ioc 0 s.abs), ((p q).eval (x • exp (s.arg • I))).abs ≤ c ^ q) :
  ∃ c ≥ 0, ∀ q ≥ 1, (P (p q) s).abs ≤ c ^ q :=
begin
  simp_rw [P], obtain ⟨c', hc', h'⟩ := P_le' p s h, clear h,
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
  refine mul_le_mul le_max_one_pow le_rfl hcq' hcq,
end

lemma exp_polynomial_approx (p : ℤ[X]) (p0 : p.eval 0 ≠ 0) :
  ∃ c, ∀ (q > (eval 0 p).nat_abs) (q_prime : nat.prime q),
  ∃ (n : ℤ) (hn : n % q ≠ 0) (gp : ℤ[X]), ∀ {r : ℂ} (hr : r ∈ (p.map (algebra_map ℤ ℂ)).roots),
    (n • exp r - q • aeval r gp : ℂ).abs ≤ c ^ q / (q - 1)! :=
begin
  let p' := λ q, (X ^ (q - 1) * p ^ q).map (algebra_map ℤ ℂ),
  have : ∀ s : ℂ, ∃ c, ∀ (q : ℕ) (x ∈ set.Ioc 0 s.abs),
    ((p' q).eval (x • exp (s.arg • I))).abs ≤ c ^ q,
  { intros s, dsimp only [p'],
    simp_rw [polynomial.map_mul, polynomial.map_pow, map_X, eval_mul, eval_pow, eval_X,
      complex.abs_mul, complex.abs_pow, real_smul, complex.abs_mul, abs_exp_of_real_mul_I,
      abs_of_real, mul_one, ← eval₂_eq_eval_map, ← aeval_def],
    have : metric.bounded
      ((λ x, max (|x|) 1 * ((aeval (↑x * exp (↑s.arg * I)) p)).abs) '' set.Ioc 0 (abs s)),
    { have h :
        ((λ x, max (|x|) 1 * ((aeval (↑x * exp (↑s.arg * I)) p)).abs) '' set.Ioc 0 (abs s)) ⊆
        ((λ x, max (|x|) 1 * ((aeval (↑x * exp (↑s.arg * I)) p)).abs) '' set.Icc 0 (abs s)),
      { exact set.image_subset _ set.Ioc_subset_Icc_self, },
      refine (is_compact.image is_compact_Icc _).bounded.mono h,
      { refine (continuous_id.abs.max continuous_const).mul _,
        refine complex.continuous_abs.comp ((p.continuous_aeval).comp _),
        exact continuous_of_real.mul continuous_const, }, },
    cases this.exists_norm_le with c h,
    use c, intros q x hx,
    specialize h (max (|x|) 1 * (aeval (↑x * exp (↑s.arg * I)) p).abs) (set.mem_image_of_mem _ hx),
    refine le_trans _ (pow_le_pow_of_le_left (norm_nonneg _) h _),
    simp_rw [norm_mul, real.norm_eq_abs, complex.abs_abs, mul_pow],
    refine mul_le_mul_of_nonneg_right _ (pow_nonneg (complex.abs_nonneg _) _),
    rw [max_def], split_ifs with h1x,
    { rw [_root_.abs_abs], exact pow_le_pow h1x (nat.sub_le _ _), },
    { push_neg at h1x,
      rw [_root_.abs_one, one_pow], exact pow_le_one _ (abs_nonneg _) h1x.le, }, },
  let c' := λ r, (P_le p' r (this r)).some,
  have c'0 : ∀ r, 0 ≤ c' r := λ r, (P_le p' r (this r)).some_spec.some,
  have Pp'_le : ∀ (r : ℂ) (q ≥ 1), abs (P (p' q) r) ≤ c' r ^ q :=
    λ r, (P_le p' r (this r)).some_spec.some_spec,
  let c := if h : ((p.map (algebra_map ℤ ℂ)).roots.map c').to_finset.nonempty
    then ((p.map (algebra_map ℤ ℂ)).roots.map c').to_finset.max' h else 0,
  have hc : ∀ x ∈ (p.map (algebra_map ℤ ℂ)).roots, c' x ≤ c,
  { intros x hx, dsimp only [c],
    split_ifs,
    { apply finset.le_max', rw [multiset.mem_to_finset],
      refine multiset.mem_map_of_mem _ hx, },
    { rw [nonempty_iff_ne_empty, ne.def, multiset.to_finset_eq_empty,
        multiset.eq_zero_iff_forall_not_mem] at h, push_neg at h,
      exact absurd (multiset.mem_map_of_mem _ hx) (h (c' x)), }, },
  use c,
  intros q q_gt q_prime,
  have q0 : 0 < q := nat.prime.pos q_prime,
  obtain ⟨gp', h'⟩ := sum_ideriv_sl' ℤ (X ^ (q - 1) * p ^ q) q0,
  simp_rw [ring_hom.algebra_map_to_algebra, map_id] at h',
  specialize h' (ring_hom.injective_int _) 0 (by rw [C_0, sub_zero]),
  rw [eval_pow] at h',
  use p.eval 0 ^ q + q • aeval 0 gp',
  split,
  { rw [int.add_mod, nsmul_eq_mul, int.mul_mod_right, add_zero, int.mod_mod, ne.def,
      ← int.dvd_iff_mod_eq_zero],
    intros h,
    replace h := int.prime.dvd_pow' q_prime h, rw [int.coe_nat_dvd_left] at h,
    replace h := nat.le_of_dvd (int.nat_abs_pos_of_ne_zero p0) h,
    revert h, rwa [imp_false, not_le], },
  obtain ⟨gp, h⟩ := sum_ideriv_sl ℂ (X ^ (q - 1) * p ^ q) q,
  use gp,
  intros r hr,
  have : (X ^ (q - 1) * p ^ q).map (algebra_map ℤ ℂ) = (X - C r) ^ q * (X ^ (q - 1) *
    (C (map (algebra_map ℤ ℂ) p).leading_coeff *
      (((p.map (algebra_map ℤ ℂ)).roots.erase r).map (λ (a : ℂ), X - C a)).prod) ^ q),
  { rw [mul_left_comm, ← mul_pow, mul_left_comm (_ - _), multiset.prod_map_erase hr],
    have : (p.map (algebra_map ℤ ℂ)).roots.card = (p.map (algebra_map ℤ ℂ)).nat_degree :=
      splits_iff_card_roots.mp (is_alg_closed.splits _),
    rw [C_leading_coeff_mul_prod_multiset_X_sub_C this, polynomial.map_mul, polynomial.map_pow,
      polynomial.map_pow, map_X], },
  specialize h r this, clear this,
  rw [le_div_iff (nat.cast_pos.mpr (nat.factorial_pos _) : (0 : ℝ) < _), ← abs_of_nat,
    ← complex.abs_mul, mul_comm, mul_sub, ← nsmul_eq_mul, ← nsmul_eq_mul, smul_smul,
    mul_comm, nat.mul_factorial_pred q0, ← h],
  rw [nsmul_eq_mul, ← int.cast_coe_nat, ← zsmul_eq_mul, smul_smul, mul_add, ← nsmul_eq_mul,
    ← nsmul_eq_mul, smul_smul, mul_comm, nat.mul_factorial_pred q0, ← h', zsmul_eq_mul,
    aeval_def, eval₂_at_zero, ring_hom.eq_int_cast, int.cast_id, ← int.coe_cast_ring_hom,
    ← algebra_map_int_eq, ← eval₂_at_zero, aeval_def, eval₂_eq_eval_map, eval₂_eq_eval_map,
    mul_comm, ← sum_ideriv_map, ← P],
  exact (Pp'_le r q (nat.one_le_of_lt q0)).trans (pow_le_pow_of_le_left (c'0 r) (hc r hr) _),
end
/-
variables {ι : Type*} [fintype ι]
  (c : ι → ℤ) (t : ι → ℤ[X])
/-
  (t0 : ∀ i, t i ≠ 0)
  (ht : ∀ i j, i ≠ j →
    multiset.disjoint ((t i).map (algebra_map ℤ ℂ)).roots ((t j).map (algebra_map ℤ ℂ)).roots)-/

lemma sum_P_eq (hct : ∑ i, c i • (((t i).map (algebra_map ℤ ℂ)).roots.map exp).sum = 0) (p : ℂ[X]) :
  ∑ i, c i • (((t i).map (algebra_map ℤ ℂ)).roots.map (P p)).sum =
  -∑ i, c i • (((t i).map (algebra_map ℤ ℂ)).roots.map (λ x, p.sum_ideriv.eval x)).sum :=
by simp_rw [P, multiset.sum_map_sub, smul_sub, sum_sub_distrib, multiset.sum_map_mul_right,
  ← smul_mul_assoc, ← sum_mul, hct, zero_mul, zero_sub]

def F (q : ℕ) (p : ℤ[X]) (p' : ℂ[X]) : ℂ[X] :=
p.map (algebra_map ℤ ℂ) ^ (q - 1) * p'

namespace polynomial

def erase_root (p : ℤ[X]) (r : ℂ) : ℂ[X] :=
(((p.map (algebra_map ℤ ℂ)).roots.erase r).map (λ x, X - C x)).prod

lemma eval_erase_root_mem (p : ℤ[X]) (r : ℂ)
  (x : ℂ) (hx : x ∈ (p.map (algebra_map ℤ ℂ)).roots.erase r) :
  (p.erase_root r).eval x = 0 := by
by rw [erase_root, ← multiset.prod_map_erase _ hx, mul_comm, eval_mul_X_sub_C]

end polynomial

lemma F_eq (q : ℕ) (p : ℤ[X]) (p' : ℂ[X]) :
  F q p p' = C ((p.map (algebra_map ℤ ℂ)).leading_coeff ^ (q - 1)) *
    ((p.map (algebra_map ℤ ℂ)).roots.map (λ x, (X - C x) ^ (q - 1))).prod * p' := by
{ rw [F, multiset.prod_map_pow, C_pow, ← mul_pow],
  have : (p.map (algebra_map ℤ ℂ)).roots.card = (p.map (algebra_map ℤ ℂ)).nat_degree :=
    splits_iff_card_roots.mp (is_alg_closed.splits _),
  rw [C_leading_coeff_mul_prod_multiset_X_sub_C this], }

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

lemma F_sum_ideriv_eval {q : ℕ} (hq : 0 < q)
  (p : ℤ[X]) (p' : ℂ[X]) {r : ℂ} (hr : r ∈ (p.map (algebra_map ℤ ℂ)).roots) :
  ∃ n' : ℤ, (F q p p').sum_ideriv.eval r = ---- ℤ 改成数域？
    (q - 1)! * ((p.map (algebra_map ℤ ℂ)).derivative ^ (q - 1) * p').eval r + q! * n' := by
{ rw [eval_mul, eval_pow, eval_root_derivative' _ hr, ← eval_pow, ← eval_mul],
  refine sum_ideriv_sl' _ _ hq _,
  rw [F_eq, ← multiset.prod_map_erase _ hr, mul_left_comm, mul_pow, multiset.prod_map_pow,
    C_pow, mul_assoc], }

lemma sum_P_F_eq {q : ℕ} (hq : 0 < q)
  (hct : ∑ i, c i • (((t i).map (algebra_map ℤ ℂ)).roots.map exp).sum = 0)
  (p : ℤ[X]) {r : ℂ} (hr : r ∈ (p.map (algebra_map ℤ ℂ)).roots) :
  ∑ i, c i • (((t i).map (algebra_map ℤ ℂ)).roots.map (P (F q p (p.erase_root r)))).sum =
  37 :=
  -- -∑ i, c i • (((t i).map (algebra_map ℤ ℂ)).roots.map (λ x, (F q p (p.erase_root x)).sum_ideriv.eval r)).sum + 1 :=
begin
 /- have F0 : (F q p (p.erase_root r)).sum_ideriv ≠ 0,
  { rw [← sum_ideriv_linear_equiv_eq_sum_ideriv, linear_equiv.map_ne_zero_iff, F,
      map_ne_zero_of_injective _ (algebra_map ℤ ℂ).injective_int], exact pow_ne_zero _ hp, },-/
  let n' : ∀ x : ℂ, ℤ := λ x, if hx : x ∈ (p.map (algebra_map ℤ ℂ)).roots
    then (F_sum_ideriv_eval hq p (p.erase_root r) hx).some else 0,
  obtain ⟨n', h⟩ := F_sum_ideriv_eval hq p (p.erase_root r) hr,
  simp_rw [sum_P_eq _ _ hct],
  
 --   ← function.comp (resultant_right this) ((λ (x : ℂ), X - C x)),
  --  ← map_multiset_sum],
end
-/
.

namespace add_monoid_algebra

@[simps]
def ring_equiv_congr_left {R S G : Type*} [semiring R] [semiring S] [add_monoid G]
  (f : R ≃+* S) :
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

@[simps]
def alg_equiv_congr_left {k R S G : Type*} [comm_semiring k] [semiring R] [algebra k R]
  [semiring S] [algebra k S] [add_monoid G] (f : R ≃ₐ[k] S) :
  add_monoid_algebra R G ≃ₐ[k] add_monoid_algebra S G :=
{ to_fun := (finsupp.map_range f f.map_zero :
    (add_monoid_algebra R G) → (add_monoid_algebra S G)),
  inv_fun := (finsupp.map_range f.symm f.symm.map_zero :
    (add_monoid_algebra S G) → (add_monoid_algebra R G)),
  commutes' := λ r,
  begin
    ext,
    simp_rw [add_monoid_algebra.coe_algebra_map, function.comp_app, finsupp.map_range_single],
    congr' 2,
    change f.to_alg_hom ((algebra_map k R) r) = (algebra_map k S) r,
    rw [alg_hom.map_algebra_map],
  end,
  ..ring_equiv_congr_left f.to_ring_equiv }

@[simps]
def alg_aut_congr_left {k R G : Type*}
  [comm_semiring k] [semiring R] [algebra k R] [add_monoid G] :
  (R ≃ₐ[k] R) →* add_monoid_algebra R G ≃ₐ[k] add_monoid_algebra R G :=
{ to_fun := λ f, alg_equiv_congr_left f,
  map_one' := by { ext, refl, },
  map_mul' := λ x y, by { ext, refl, }, }

@[simps]
def map_domain_ring_equiv (k : Type*) [semiring k]
  {G H : Type*} [add_monoid G] [add_monoid H] (f : G ≃+ H) :
  add_monoid_algebra k G ≃+* add_monoid_algebra k H :=
{ to_fun := finsupp.equiv_map_domain f,
  inv_fun := finsupp.equiv_map_domain f.symm,
  map_mul' := λ x y,
  begin
    simp_rw [← finsupp.dom_congr_apply],
    induction x using finsupp.induction_linear,
    { simp only [map_zero, zero_mul], }, { simp only [add_mul, map_add, *], },
    induction y using finsupp.induction_linear;
    simp only [mul_zero, zero_mul, map_zero, mul_add, map_add, *],
    ext, simp only [finsupp.dom_congr_apply, single_mul_single, finsupp.equiv_map_domain_single,
      add_equiv.coe_to_equiv, map_add],
  end,
  ..finsupp.dom_congr f.to_equiv }

@[simps]
def map_domain_alg_equiv (k A : Type*) [comm_semiring k] [semiring A] [algebra k A]
  {G H : Type*} [add_monoid G] [add_monoid H] (f : G ≃+ H) :
  add_monoid_algebra A G ≃ₐ[k] add_monoid_algebra A H :=
{ to_fun := finsupp.equiv_map_domain f,
  inv_fun := finsupp.equiv_map_domain f.symm,
  commutes' := λ r, by simp only [function.comp_app, finsupp.equiv_map_domain_single,
      add_monoid_algebra.coe_algebra_map, map_zero, add_equiv.coe_to_equiv],
  ..map_domain_ring_equiv A f }

@[simps]
def map_domain_alg_aut (k A : Type*) [comm_semiring k] [semiring A] [algebra k A]
  {G : Type*} [add_monoid G] :
  (add_aut G) →* add_monoid_algebra A G ≃ₐ[k] add_monoid_algebra A G :=
{ to_fun := map_domain_alg_equiv k A,
  map_one' := by { ext, refl, },
  map_mul' := λ x y, by { ext, refl, }, }

/-

private lemma eq_zero_or_eq_zero_of_mul_eq_zero_finite
  {R : Type*} {S : Type*} {M : Type*} [ring R] [is_domain R] [linear_ordered_semiring S]
  [add_comm_group M] [module S M] [module.free S M] [module.finite S M]
  (p q : add_monoid_algebra R M) (h : p * q = 0) : p = 0 ∨ q = 0 :=
begin
  
end

@[simps]
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
-/
end add_monoid_algebra
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

abbreviation K' : intermediate_field ℚ ℂ :=
intermediate_field.adjoin ℚ ((Poly s).root_set ℂ)

instance : is_splitting_field ℚ (K' s) (Poly s) :=
adjoin_root_set_is_splitting_field (is_alg_closed.splits_codomain (Poly s))

abbreviation K : Type* := (Poly s).splitting_field

instance : is_galois ℚ (K s) := {}

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

noncomputable!
def rat_coeff : subalgebra ℚ (add_monoid_algebra (K s) (K s)) :=
{ carrier := λ x, ∀ i : K s, x i ∈ (⊥ : intermediate_field ℚ (K s)),
  mul_mem' := λ a b ha hb i,
  begin
    rw [add_monoid_algebra.mul_apply],
    refine sum_mem (λ c hc, sum_mem (λ d hd, _)),
    dsimp only, split_ifs, exacts [mul_mem (ha c) (hb d), zero_mem _],
  end,
  add_mem' := λ a b ha hb i, by { rw [finsupp.add_apply], exact add_mem (ha i) (hb i), },
  algebra_map_mem' := λ r hr,
  begin
    rw [add_monoid_algebra.coe_algebra_map, function.comp_app, finsupp.single_apply],
    split_ifs, exacts [intermediate_field.algebra_map_mem _ _, zero_mem _],
  end }

noncomputable!
def map_domain_fixed : subalgebra (K s) (add_monoid_algebra (K s) (K s)) :=
{ carrier := λ x, ∀ f : Gal s, add_monoid_algebra.map_domain_alg_aut ℚ _ f.to_add_equiv x = x,
  mul_mem' := λ a b ha hb f, by rw [map_mul, ha, hb],
  add_mem' := λ a b ha hb f, by rw [map_add, ha, hb],
  algebra_map_mem' := λ r f,
  begin
    change finsupp.equiv_map_domain f.to_equiv (finsupp.single _ _) = finsupp.single _ _,
    rw [finsupp.equiv_map_domain_single],
    change finsupp.single (f 0) _ = _, rw [alg_equiv.map_zero],
  end }

lemma mem_map_domain_fixed_iff (x : add_monoid_algebra (K s) (K s)) :
  x ∈ map_domain_fixed s ↔ (∀ i j, i ∈ mul_action.orbit (Gal s) j → x i = x j) :=
begin
  simp_rw [mul_action.mem_orbit_iff],
  change (∀ (f : Gal s), finsupp.equiv_map_domain ↑(alg_equiv.to_add_equiv f) x = x) ↔ _,
  refine ⟨λ h i j hij, _, λ h f, _⟩,
  { obtain ⟨f, rfl⟩ := hij,
    rw [alg_equiv.smul_def, ← finsupp.congr_fun (h f) (f j)],
    change x (f.symm (f j)) = _, rw [alg_equiv.symm_apply_apply], },
  { ext i, change x (f.symm i) = x i,
    refine (h i ((alg_equiv.symm f) i) ⟨f, _⟩).symm,
    rw [alg_equiv.smul_def, alg_equiv.apply_symm_apply], }
end

noncomputable!
def map_domain_fixed_equiv_subtype :
  map_domain_fixed s ≃
    {f : add_monoid_algebra (K s) (K s) // (mul_action.orbit_rel (Gal s) (K s)) ≤ setoid.ker f} :=
{ to_fun := λ f, ⟨f, (mem_map_domain_fixed_iff s f).mp f.2⟩,
  inv_fun := λ f, ⟨f, (mem_map_domain_fixed_iff s f).mpr f.2⟩,
  left_inv := λ f, by simp_rw [← subtype.coe_inj, subtype.coe_mk],
  right_inv := λ f, by simp_rw [← subtype.coe_inj, subtype.coe_mk], }

namespace quot

attribute [reducible, elab_as_eliminator]
protected def lift_finsupp {α : Type*} {r : α → α → Prop} {β : Type*} [has_zero β]
  (f : α →₀ β) (h : ∀ a b, r a b → f a = f b) : quot r →₀ β := by
{ refine ⟨finset.image (mk r) f.support, quot.lift f h, λ a, ⟨_, a.ind (λ b, _)⟩⟩,
  { rw [mem_image], rintros ⟨b, hb, rfl⟩, exact finsupp.mem_support_iff.mp hb, },
  { rw [lift_mk _ h], refine λ hb, mem_image_of_mem _ (finsupp.mem_support_iff.mpr hb), }, }

end quot

namespace quotient

attribute [reducible, elab_as_eliminator]
protected def lift_finsupp {α : Type*} {β : Type*} [s : setoid α] [has_zero β] (f : α →₀ β) :
  (∀ a b, a ≈ b → f a = f b) → quotient s →₀ β :=
quot.lift_finsupp f

end quotient

namespace mul_action

@[to_additive]
instance (α : Type*) {β : Type*} [monoid α] [fintype α] [mul_action α β] (b : β) :
  fintype (orbit α b) := set.fintype_range _

@[to_additive]
instance (α : Type*) {β : Type*} [group α] [fintype α] [mul_action α β]
  (x : mul_action.orbit_rel.quotient α β) :
  fintype x.orbit :=
by { rw [x.orbit_eq_orbit_out quotient.out_eq'], apply_instance, }

end mul_action

instance is_conj.setoid' := mul_action.orbit_rel (Gal s) (K s)
abbreviation conj_classes' := mul_action.orbit_rel.quotient (Gal s) (K s)

noncomputable!
def sum_conj_equiv : map_domain_fixed s ≃ (conj_classes' s →₀ K s) :=
begin
  refine (map_domain_fixed_equiv_subtype s).trans _,
  refine
  { to_fun := λ f, quotient.lift_finsupp (f : add_monoid_algebra (K s) (K s)) f.2,
    inv_fun := λ f, ⟨_, _⟩,
    left_inv := _,
    right_inv := _, },
  { refine ⟨f.support.bUnion (λ i, i.orbit.to_finset), λ x, f (quotient.mk' x), λ i, _⟩,
    simp_rw [mem_bUnion, set.mem_to_finset, mul_action.orbit_rel.quotient.mem_orbit,
      finsupp.mem_support_iff, exists_prop, exists_eq_right'], },
  { change ∀ i j, i ∈ mul_action.orbit (Gal s) j → f (quotient.mk' i) = f (quotient.mk' j),
    exact λ i j h, congr_arg f (quotient.sound' h), },
  { exact λ _, subtype.eq $ finsupp.ext $ λ x, rfl, },
  { refine λ f, finsupp.ext $ λ x, quotient.induction_on' x $ λ i, rfl, }
end

lemma sum_conj_equiv_apply (f : map_domain_fixed s) :
  sum_conj_equiv s f = quotient.lift_finsupp (f : add_monoid_algebra (K s) (K s))
    ((mem_map_domain_fixed_iff s f).mp f.2) := rfl

@[simp]
lemma sum_conj_equiv_apply_apply_mk (f : map_domain_fixed s) (i : K s) :
  sum_conj_equiv s f (quotient.mk i) = f i := rfl

@[simp]
lemma sum_conj_equiv_apply_apply_mk' (f : map_domain_fixed s) (i : K s) :
  sum_conj_equiv s f (quotient.mk' i) = f i := rfl

@[simp]
lemma sum_conj_equiv_symm_apply_apply (f : conj_classes' s →₀ K s) (i : K s) :
  (sum_conj_equiv s).symm f i = f (quotient.mk i) := rfl

@[simp]
lemma sum_conj_equiv_symm_apply_apply' (f : conj_classes' s →₀ K s) (i : K s) :
  (sum_conj_equiv s).symm f i = f (quotient.mk' i) := rfl

@[simp]
lemma sum_conj_equiv_apply_apply (f : map_domain_fixed s) (i : conj_classes' s) :
  sum_conj_equiv s f i = f i.out :=
by rw [← quotient.out_eq i, sum_conj_equiv_apply_apply_mk, quotient.out_eq]

@[simps]
noncomputable!
def sum_conj_linear_equiv : map_domain_fixed s ≃ₗ[K s] (conj_classes' s →₀ K s) :=
{ map_add' := λ x y, by { ext i, simp_rw [equiv.to_fun_as_coe, finsupp.coe_add, pi.add_apply,
    sum_conj_equiv_apply_apply], refl, },
  map_smul' := λ r x, by { ext i, simp_rw [equiv.to_fun_as_coe, finsupp.coe_smul, pi.smul_apply,
    sum_conj_equiv_apply_apply], refl, },
  ..sum_conj_equiv s, }

lemma linear_independent_exp_aux3 (s : finset ℂ)
  (x : add_monoid_algebra (K s) (K s)) (x0 : x ≠ 0) (x_ker : x ∈ (Eval s).to_ring_hom.ker)
  (x_mem : x ∈ rat_coeff s) :
  ∃ (w : ℤ) (q : finset (K s)) (w' : q → ℤ),
    (w + ∑ x : q, w' x * ∑ f : Gal s,
      exp (algebra_map (K s) ℂ (f x)) : ℂ) = 0 := by
{ let V := ∏ f : Gal s, add_monoid_algebra.map_domain_alg_aut ℚ _ f.to_add_equiv x,
  have hV : ∀ f : Gal s, add_monoid_algebra.map_domain_alg_aut ℚ _ f.to_add_equiv V = V,
  { intros f, dsimp only [V],
    rw [map_prod], simp_rw [← alg_equiv.trans_apply, ← alg_equiv.aut_mul, ← map_mul],
    exact (group.mul_left_bijective f).prod_comp
      (λ g, add_monoid_algebra.map_domain_alg_aut ℚ _ g.to_add_equiv x), },
  have V_ker : V ∈ (Eval s).to_ring_hom.ker,
  { dsimp only [V],
    suffices : (λ f : Gal s, (add_monoid_algebra.map_domain_alg_aut ℚ _ f.to_add_equiv) x) 1 *
      ∏ (f : Gal s) in univ.erase 1,
        add_monoid_algebra.map_domain_alg_aut ℚ _ f.to_add_equiv x ∈ (Eval s).to_ring_hom.ker,
    { rwa [mul_prod_erase (univ : finset (Gal s)) _ (mem_univ _)] at this, },
    change (finsupp.equiv_map_domain (equiv.refl _) x * _ : add_monoid_algebra (K s) (K s)) ∈ _,
    rw [finsupp.equiv_map_domain_refl], exact ideal.mul_mem_right _ _ x_ker, },
  have V_mem : V ∈ rat_coeff s,
  { dsimp only [V], refine subalgebra.prod_mem _ (λ f hf, _),
    intros i, change finsupp.equiv_map_domain f.to_equiv x i ∈ _,
    rw [finsupp.equiv_map_domain_apply], exact x_mem _, },
  have : fintype.card (Gal s) • V =
    ∑ f : Gal s, add_monoid_algebra.map_domain_alg_aut ℚ _ f.to_add_equiv V,
  { simp_rw [hV, sum_const, card_univ], },
  
}
/-
  replace hV : V ∈ map_domain_fixed s := hV,-/
lemma linear_independent_exp_aux2 (s : finset ℂ)
  (x : add_monoid_algebra (K s) (K s)) (x0 : x ≠ 0) (x_ker : x ∈ (Eval s).to_ring_hom.ker) :
  ∃ (w : ℤ) (q : finset (K s)) (w' : q → ℤ),
    (w + ∑ x : q, w' x * ∑ f : Gal s,
      exp (algebra_map (K s) ℂ (f x)) : ℂ) = 0 := by
{ let U := ∏ f : Gal s, add_monoid_algebra.alg_aut_congr_left f x,
  have hU : ∀ f : Gal s, add_monoid_algebra.alg_aut_congr_left f U = U,
  { intros f, dsimp only [U],
    simp_rw [map_prod, ← alg_equiv.trans_apply, ← alg_equiv.aut_mul, ← map_mul],
    exact (group.mul_left_bijective f).prod_comp
      (λ g, add_monoid_algebra.alg_aut_congr_left g x), },
  have U0 : U ≠ 0,
  { dsimp only [U], rw [prod_ne_zero_iff], intros f hf,
    rwa [add_equiv_class.map_ne_zero_iff], },
  have U_ker : U ∈ (Eval s).to_ring_hom.ker,
  { dsimp only [U],
    suffices : (λ f : Gal s, (add_monoid_algebra.alg_aut_congr_left f) x) 1 *
      ∏ (f : Gal s) in univ.erase 1,
        (add_monoid_algebra.alg_aut_congr_left f) x ∈ (Eval s).to_ring_hom.ker,
    { rwa [mul_prod_erase (univ : finset (Gal s)) _ (mem_univ _)] at this, },
    change finsupp.map_range id rfl _ * _ ∈ _,
    rw [finsupp.map_range_id], exact ideal.mul_mem_right _ _ x_ker, },
  have U_mem : ∀ i : K s, U i ∈ intermediate_field.fixed_field (⊤ : subgroup (K s ≃ₐ[ℚ] K s)),
  { intros i, dsimp [intermediate_field.fixed_field, fixed_points.intermediate_field],
    rintros ⟨f, hf⟩, rw [subgroup.smul_def, subgroup.coe_mk],
    replace hU : (add_monoid_algebra.alg_aut_congr_left f) U i = U i, { rw [hU f], },
    rwa [add_monoid_algebra.alg_aut_congr_left_apply,
      add_monoid_algebra.alg_equiv_congr_left_apply, finsupp.map_range_apply] at hU, },
  replace U_mem : U ∈ rat_coeff s,
  { intros i, specialize U_mem i,
    rwa [((@is_galois.tfae ℚ _ (K s) _ _ _).out 0 1).mp infer_instance] at U_mem, },
  exact linear_independent_exp_aux3 s U U0 U_ker U_mem, }

#check prod_induction_nonempty
#check finsupp.equiv_congr_left
#check finsupp.map_range_apply

variables {ι : Type*} [fintype ι]

abbreviation Range (u : ι → ℂ) (v : ι → ℂ) : finset ℂ := univ.image u ∪ univ.image v

lemma linear_independent_exp_aux1
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
  let u' : ∀ i, K s := λ i : ι, Lift s ⟨u i, u_mem i⟩,
  let v' : ∀ i, K s := λ i : ι, Lift s ⟨v i, v_mem i⟩,
  have u'_inj : function.injective u' :=
    λ i j hij, u_inj (subtype.mk.inj ((Lift s).injective hij)),
  replace h : ∑ i, (algebra_map (K s) ℂ (v' i)) * exp (algebra_map (K s) ℂ (u' i)) = 0,
  { simp_rw [algebra_map_K_apply, alg_equiv.symm_apply_apply, ← h],
    symmetry, apply sum_congr rfl,
    intros x hx, refl, },
  
  let f : add_monoid_algebra (K s) (K s) := finsupp.on_finset (image u' univ)
    (λ x, if hx : x ∈ image u' univ
      then v' (u'_inj.inv_of_mem_range ⟨x, mem_image_univ_iff_mem_range.mp hx⟩) else 0)
    (λ x, by { contrapose!, intros hx, rw [dif_neg hx], }),
  replace hf : Eval s f = 0,
  { rw [Eval_apply, ← h, finsupp.on_finset_sum _ (λ a, _)], swap, { rw [zero_smul], },
    rw [sum_image, sum_congr rfl], swap, { exact λ i hi j hj hij, u'_inj hij, },
    intros x hx,
    rw [dif_pos, u'_inj.right_inv_of_inv_of_mem_range], { refl },
    exact mem_image_of_mem _ (mem_univ _), },
  have f0 : f ≠ 0,
  { rw [ne.def, function.funext_iff] at v0, push_neg at v0,
    cases v0 with i hi,
    rw [pi.zero_apply] at hi,
    have h : f (u' i) ≠ 0,
    { rwa [finsupp.on_finset_apply, dif_pos, u'_inj.right_inv_of_inv_of_mem_range, ne.def,
        add_equiv_class.map_eq_zero_iff, ← add_submonoid_class.coe_eq_zero],
      exact mem_image_of_mem _ (mem_univ _), },
    intros f0,
    rw [f0, finsupp.zero_apply] at h,
    exact absurd rfl h, },
  rw [← alg_hom.coe_to_ring_hom, ← ring_hom.mem_ker] at hf,
  exact linear_independent_exp_aux2 s f f0 hf, }

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
    change ∑ (x : s), (λ (x : ℂ), g x * exp x) ↑x = 0,
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
