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

noncomputable theory

open_locale big_operators polynomial
open finset

namespace nat

lemma desc_factorial_eq_prod_range (n : ℕ) :
  ∀ k, n.desc_factorial k = ∏ i in range k, (n - i)
| 0       := rfl
| (k + 1) := by rw [desc_factorial, prod_range_succ, mul_comm, desc_factorial_eq_prod_range k]

end nat

namespace polynomial

variables {R : Type*} [comm_semiring R] -- [semiring R]

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

lemma iterated_deriv_X_pow :
  ∀ n : ℕ, iterated_deriv (X ^ k : R[X]) n = k.desc_factorial n • X ^ (k - n)
| 0       := by rw [iterated_deriv_zero_right, nat.desc_factorial, one_smul, tsub_zero]
| (n + 1) := by rw [iterated_deriv_succ, iterated_deriv_X_pow n, derivative_smul, derivative_X_pow,
  nat.desc_factorial, ← nsmul_eq_mul, smul_smul, mul_comm, tsub_tsub]

lemma iterated_deriv_taylor (p : R[X]) (r : R) :
  ∀ n : ℕ, (taylor r p).iterated_deriv n = taylor r (p.iterated_deriv n)
| 0       := by simp_rw [iterated_deriv_zero_right]
| (n + 1) := by simp_rw [iterated_deriv_succ, iterated_deriv_taylor n, taylor_apply,
  derivative_comp, derivative_add, derivative_X, derivative_C, add_zero, one_mul]

end polynomial

open polynomial
open_locale nat

namespace e_transcendental
open real

lemma lemma₁ (p : ℤ[X]) {x : ℝ} (hx : 0 < x) : ∃ (c ∈ set.Ioo 0 x),
  aeval x p.sum_ideriv - exp x * aeval 0 p.sum_ideriv = -(x * exp (x - c) * aeval c p) := by
{ obtain ⟨c, hc, h⟩ := exists_deriv_eq_slope (λ x, exp (-x) * aeval x p.sum_ideriv) hx _ _,
  { use [c, hc], dsimp only at h,
    rw [sub_zero, eq_div_iff hx.ne.symm, exp_neg 0, exp_zero, inv_one, one_mul] at h,
    replace h := (@mul_eq_mul_left_iff _ _ (exp x) _ _).mpr (or.inl h),
    rw [mul_sub, ← mul_assoc, ← mul_assoc, ← exp_add, add_neg_self, exp_zero, one_mul] at h,
    rw [← h, mul_comm, mul_assoc, ← mul_neg, mul_eq_mul_left_iff, neg_mul_eq_mul_neg], left,
    rw [exp_sub, div_mul_eq_mul_div, mul_div_assoc, mul_eq_mul_left_iff], left,
    rw [deriv_mul, _root_.deriv_exp, deriv_neg, div_eq_mul_inv, ← exp_neg, mul_comm _ (exp _),
      mul_assoc, ← mul_add, mul_eq_mul_left_iff], left,
    simp_rw [aeval_def, ← eval_map, polynomial.deriv, neg_one_mul, ← eval_neg, ← eval_add,
      derivative_map, ← polynomial.map_neg, ← polynomial.map_add],
    refine congr_arg _ (congr_arg _ _),
    rw [neg_add_eq_iff_eq_add, eq_add_neg_iff_add_eq, add_comm, ← sum_ideriv_eq_self_add],
    { exact differentiable_at.neg differentiable_at_id, },
    { exact differentiable_at.exp (differentiable_at.neg differentiable_at_id), },
    { simp_rw [aeval_def, ← eval_map], exact polynomial.differentiable_at _, }, },
  { exact continuous_on.mul (continuous_on.exp (continuous_on.neg continuous_on_id))
      (polynomial.continuous_on_aeval _), },
  { simp_rw [aeval_def, ← eval_map], exact differentiable_on.mul
      (differentiable_on.exp (differentiable_on.neg differentiable_on_id))
      (polynomial.differentiable_on _), }, }

lemma lemma₂ (ann : ℤ[X]) (hann : aeval (exp 1) ann = 0) (p : ℤ[X]) :
  ∃ (b : ℕ → ℝ) (hb : ∀ i < ann.nat_degree, b i ∈ set.Ioo 0 (i + 1 : ℝ)),
    ∑ i in range (ann.nat_degree + 1), ann.coeff i • aeval (i : ℝ) p.sum_ideriv =
    ∑ i in range ann.nat_degree, ann.coeff (i + 1) •
      -((i + 1) • (exp ((i + 1 : ℕ) - b i) * aeval (b i) p)) := by
{ have lt_succ : ∀ (i : ℕ), (0 : ℝ) < i + 1,
  { intros i, convert_to ((0 : ℕ) : ℝ) < (i + 1 : ℕ),
    { rw [nat.cast_zero] },
    { rw [nat.cast_add, nat.cast_one] },
    rw [nat.cast_lt], exact nat.zero_lt_succ _ },
  have lem := λ i, lemma₁ p (lt_succ i),
  let b := λ i, (lem i).some, use b,
  have hb : ∀ i, b i ∈ set.Ioo 0 (i + 1 : ℝ) := λ i, (lem i).some_spec.some,
  have hb' : ∀ (i : ℕ), aeval (i + 1 : ℝ) (sum_ideriv p) - exp (i + 1) * aeval 0 (sum_ideriv p) =
                        -((i + 1) * exp ((i + 1 : ℕ) - b i) * aeval (b i) p),
  { intros i, convert (lem i).some_spec.some_spec, rw [nat.cast_add, nat.cast_one], },
  use λ i _, hb i,
  have hc0 : (ann.coeff 0 : ℝ) = -∑ i in range ann.nat_degree, ann.coeff (i + 1) • exp 1 ^ (i + 1),
  { rw [eq_neg_iff_add_eq_zero, add_comm], convert hann,
    rw [aeval_eq_sum_range, sum_range_succ', pow_zero, int.smul_one_eq_coe], },
  simp_rw [← rpow_nat_cast, ← exp_mul, one_mul] at hc0,
  rw [sum_range_succ', zsmul_eq_mul, hc0, neg_mul, ← sub_eq_add_neg, sum_mul, ← sum_sub_distrib],
  congr, funext i, rw [smul_mul_assoc, ← smul_sub], apply congr_arg,
  specialize hb' i, rw [nat.cast_zero, nat.cast_add, nat.cast_one, hb',
                        nsmul_eq_mul, nat.cast_add, nat.cast_one, mul_assoc], }

lemma lemma₃ (p : ℤ[X]) (k : ℕ) : ∃ p', p.iterated_deriv k = k! * p' :=
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

lemma lemma₄ (p : ℤ[X]) (q : ℕ) {p' : ℤ[X]} (hp : p = X ^ q * p') {k : ℕ} (hk : k < q) :
  (p.iterated_deriv k).eval 0 = 0 := by
{ have h : ∀ x, (X : ℤ[X]) ^ (q - (k - x)) = X ^ 1 * X ^ (q - (k - x) - 1),
  { intros x, rw [← pow_add, add_tsub_cancel_of_le], rw [nat.lt_iff_add_one_le] at hk,
    exact (le_tsub_of_add_le_left hk).trans (tsub_le_tsub_left (tsub_le_self : _ ≤ k) _), },
  simp_rw [hp, iterated_deriv_mul, iterated_deriv_X_pow, ← smul_mul_assoc, smul_smul, h,
    ← mul_smul_comm, mul_assoc, ← mul_sum, eval_mul, pow_one, eval_X, zero_mul], }

lemma lemma₄' (p : ℤ[X]) (q : ℕ) {k : ℕ} (hk : q ≤ k) :
  ∃ n', (p.iterated_deriv k).eval 0 = q! * n' := by
{ obtain ⟨p', hp'⟩ := lemma₃ p k,
  use ↑(k.desc_factorial (k - q)) * eval 0 p',
  rw [hp', eval_mul, ← C_eq_nat_cast, eval_C,
    ← nat.factorial_mul_desc_factorial (tsub_le_self : k - q ≤ k), tsub_tsub_cancel_of_le hk,
    nat.cast_mul, mul_assoc], }

lemma lemma₅ (p : ℤ[X]) (q : ℕ) {p' : ℤ[X]} (hp : p = X ^ q * p') (k : ℕ) :
  ∃ n', (p.iterated_deriv k).eval 0 = q! * n' := by
{ by_cases hk : k < q,
  { use 0, rw [mul_zero, lemma₄ p q hp hk], },
  { rw [not_lt] at hk, exact lemma₄' p q hk, }, }

def F (n : ℕ) (q : ℕ) : ℤ[X] :=
X ^ q * ∏ i in range n, (X - C (i + 1 : ℤ)) ^ (q + 1)

lemma lemma₆_zero₁ (n : ℕ) (q : ℕ) {k : ℕ} (hk : k < q) :
  ((F n q).iterated_deriv k).eval 0 = 0 :=
lemma₄ (F n q) q rfl hk

lemma lemma₆_zero₂ (n : ℕ) (q : ℕ) {k : ℕ} (hk : q + 1 ≤ k) :
  ∃ n', ((F n q).iterated_deriv k).eval 0 = (q + 1)! * n' :=
lemma₄' (F n q) (q + 1) hk

lemma lemma₆_succ (n : ℕ) (q : ℕ) (k : ℕ) (x : ℕ) (hx : x < n) :
  ∃ n', ((F n q).iterated_deriv k).eval (x + 1) = (q + 1)! * n' := by
{ obtain h := lemma₅ (taylor (x + 1 : ℤ) (F n q)) (q + 1) _ k,
  rwa [iterated_deriv_taylor, taylor_eval, zero_add] at h, swap,
  rw [F, ← mul_prod_erase _ _ (mem_range.mpr hx), ← taylor_alg_hom_apply],
  simp_rw [_root_.map_mul, map_pow, _root_.map_sub, taylor_alg_hom_apply, taylor_X, taylor_C],
  rw [add_sub_cancel, ← mul_assoc, mul_comm (_ ^ q), mul_assoc], }

lemma lemma₇_zero (n : ℕ) (q : ℕ) :
  ∃ n', (F n q).sum_ideriv.eval 0 = q! * ∏ i in range n, (-(i + 1)) ^ (q + 1) + (q + 1)! * n' := by
{ let ub := max (q + 1) ((F n q).nat_degree + 1),
  let u := λ i, if h : q + 1 ≤ i then classical.some (lemma₆_zero₂ n q h) else 0,
  have hu : ∀ (i : ℕ) (h : q + 1 ≤ i), eval 0 ((F n q).iterated_deriv i) = (q + 1)! * u i :=
    λ i h, by simp only [u, dif_pos h]; exact classical.some_spec (lemma₆_zero₂ n q h),
  have := calc (F n q).sum_ideriv.eval 0
      = (∑ (i : ℕ) in range ub, (F n q).iterated_deriv i).eval 0 : _
  ... = ( ∑ (i : ℕ) in range q, (F n q).iterated_deriv i +
          (F n q).iterated_deriv q +
          ∑ (i : ℕ) in Ico (q + 1) ub, (F n q).iterated_deriv i ).eval 0 : _
  ... = (∑ (i : ℕ) in range q, (F n q).iterated_deriv i).eval 0 +
        ((F n q).iterated_deriv q).eval 0 +
        (∑ (i : ℕ) in Ico (q + 1) ub, (F n q).iterated_deriv i).eval 0 : by rw [eval_add, eval_add]
  ... = ∑ (i : ℕ) in range q, ((F n q).iterated_deriv i).eval 0 +
        q! * ∏ i in range n, (-(i + 1)) ^ (q + 1) +
        ∑ (i : ℕ) in Ico (q + 1) ub, ((F n q).iterated_deriv i).eval 0 : _
  ... = ∑ (i : ℕ) in range q, 0 +
        q! * ∏ i in range n, (-(i + 1)) ^ (q + 1) +
        ∑ (i : ℕ) in Ico (q + 1) ub, (q + 1)! * u i : _
  ... = q! * ∏ i in range n, (-(i + 1)) ^ (q + 1) +
        (q + 1)! * ∑ (i : ℕ) in Ico (q + 1) ub, u i : _,
  rw [this], use ∑ (i : ℕ) in Ico (q + 1) ub, u i,
  { rw [sum_ideriv_apply_of_lt],
    exact (nat.lt_add_one_iff.2 le_rfl).trans_le (le_max_right _ _), },
  { apply congr_arg,
    have h₁ : range ub = range (q + 1) ∪ Ico (q + 1) ub,
    { rw [range_eq_Ico, finset.Ico_union_Ico_eq_Ico (nat.zero_le _) (le_max_left _ _)], },
    rw [h₁, sum_union, sum_range_succ],
    rintros i h, rw [inf_eq_inter, mem_inter, mem_range, mem_Ico, nat.lt_add_one_iff] at h,
    exact h.1.not_lt h.2.1, },
  { congr' 2, { rw [← coe_eval_ring_hom, map_sum], },
    { rw [F, iterated_deriv_mul, sum_range_succ', eval_add],
      convert_to 0 + (q! : ℤ) * ∏ (i : ℕ) in range n, (-(i + 1 : ℤ)) ^ (q + 1) =
                 q! * ∏ (i : ℕ) in range n, (-(i + 1)) ^ (q + 1),
      { congr' 1,
        { rw [← coe_eval_ring_hom, map_sum], apply sum_eq_zero, intros x hx, rw [mem_range] at hx,
          rw [coe_eval_ring_hom, eval_smul, iterated_deriv_X_pow, tsub_tsub_cancel_of_le, pow_add,
              pow_one, eval_mul, eval_smul, eval_mul, eval_X,
              mul_zero, smul_zero, zero_mul, smul_zero],
          rwa [nat.add_one_le_iff], },
        { simp_rw [nat.choose_zero_right, one_smul, tsub_zero, iterated_deriv_X_pow, tsub_self,
            pow_zero, smul_one_mul, nat.desc_factorial_self, eval_smul,
            iterated_deriv_zero_right, eval_prod, eval_pow, eval_sub, eval_X, eval_C, zero_sub],
          simp only [nsmul_eq_mul, mul_eq_mul_left_iff, prod_congr, eq_self_iff_true], }, },
        rw [zero_add], },
    { rw [← coe_eval_ring_hom, map_sum], }, },
  { congr' 1, congr' 1,
    { rw [sum_congr], refl, intros x hx, rw [mem_range] at hx, rwa [lemma₆_zero₁], },
    { rw [sum_congr], refl, intros x hx, rw [mem_Ico] at hx, exact hu x hx.1, }, },
  { rw [sum_eq_zero (λ _ _, rfl)], congr' 1, rw [zero_add], rw [mul_sum], }, }

lemma lemma₇_succ (n : ℕ) (q : ℕ) (x : ℕ) (hx : x < n) :
  ∃ n', (F n q).sum_ideriv.eval (x + 1) = (q + 1)! * n' := by
{ let c := λ k, classical.some (lemma₆_succ n q k x hx),
  have hc : ∀ (k : ℕ), eval (↑x + 1) ((F n q).iterated_deriv k) = (q + 1)! * c k :=
    λ k, classical.some_spec (lemma₆_succ n q k x hx),
  simp_rw [sum_ideriv_apply, ← coe_eval_ring_hom, map_sum, coe_eval_ring_hom, hc, ← mul_sum],
  use (range ((F n q).nat_degree + 1)).sum c, }

lemma hF (q : ℕ) (ann : ℤ[X]) (hann : aeval (exp 1) ann = 0) :
  ∃ (b : ℕ → ℝ) (hb : ∀ i < ann.nat_degree, b i ∈ set.Ioo 0 (i + 1 : ℝ)),
    ∑ i in range (ann.nat_degree + 1),
      ann.coeff i • aeval (i : ℝ) (F ann.nat_degree q).sum_ideriv =
    ∑ i in range ann.nat_degree, ann.coeff (i + 1) •
      -((i + 1) • (exp ((i + 1 : ℕ) - b i) * aeval (b i) (F ann.nat_degree q))) :=
lemma₂ ann hann (F ann.nat_degree q)

lemma hF_lhs' (q : ℕ) (ann : ℤ[X]) (hann : aeval (exp 1) ann = 0) :
  ∃ n',
    ∑ i in range (ann.nat_degree + 1),
      ann.coeff i • aeval (i : ℝ) (F ann.nat_degree q).sum_ideriv =
    (q! * (ann.coeff 0 * ∏ i in range ann.nat_degree, (-(i + 1 : ℕ)) ^ (q + 1)) +
      (q + 1)! * n' : ℤ) := by
{ obtain ⟨uz, huz⟩ := lemma₇_zero ann.nat_degree q,
  let us := λ x, if hx : x < ann.nat_degree then
    classical.some (lemma₇_succ ann.nat_degree q x hx) else 0,
  have hus : ∀ (x : ℕ) (hx : x < ann.nat_degree),
    eval (x + 1 : ℤ) (sum_ideriv (F ann.nat_degree q)) = (q + 1)! * us x :=
  λ x (hx : x < ann.nat_degree), by simp only [us, dif_pos hx]; exact
    classical.some_spec (lemma₇_succ ann.nat_degree q x hx),
  use ann.coeff 0 * uz + ∑ i in range ann.nat_degree, ann.coeff (i + 1) * us i,
  convert_to ↑∑ i in range (ann.nat_degree + 1),
    ann.coeff i * (F ann.nat_degree q).sum_ideriv.eval i = _,
  { rw [int.cast_sum, sum_congr], refl, intros x hx,
    rw [int.cast_mul, zsmul_eq_mul, mul_eq_mul_left_iff], left,
    rw [aeval_def, eval₂_eq_eval_map],
    simp only [ring_hom.eq_int_cast, eval_nat_cast_map], },
  { rw [int.cast_inj, sum_range_succ', int.coe_nat_zero, huz, add_comm, mul_add,
      add_assoc, mul_add], simp_rw [← mul_assoc, mul_comm (ann.coeff 0)], congr' 2,
    convert_to _ = ↑(q + 1)! * ∑ i in range ann.nat_degree, ann.coeff (i + 1) * us i,
    rw [mul_sum, sum_congr], refl, intros x hx, rw [mem_range] at hx,
    rw [int.coe_nat_succ, hus x hx, ← mul_assoc, ← mul_assoc, mul_comm (ann.coeff (x + 1))], }, }

lemma hF_lhs (q : ℕ) (prime_q : q.prime) (ann : ℤ[X]) (hann : aeval (exp 1) ann = 0)
  (coeff0 : ann.coeff 0 ≠ 0) (hcq : (ann.coeff 0).nat_abs + 1 ≤ q) (hnq : ann.nat_degree + 1 ≤ q) :
  ∃ (n' r : ℤ) (hr : 0 < r ∧ r < q),
    ∑ i in range (ann.nat_degree + 1),
      ann.coeff i • aeval (i : ℝ) (F ann.nat_degree (q - 1)).sum_ideriv =
    ((q - 1)! * r + q! * n' : ℤ) := by
{ obtain ⟨n'', h''⟩ := hF_lhs' (q - 1) ann hann,
  have q_0 : q ≠ 0 := prime_q.ne_zero,
  have q_pos : 0 < q := nat.pos_of_ne_zero q_0,
  have int_q_0 : (q : ℤ) ≠ 0 := int.coe_nat_ne_zero.mpr q_0,
  have int_q_pos : 0 < (q : ℤ) := int.coe_nat_pos.mpr q_pos,
  have prime_int_q := nat.prime_iff_prime_int.mp prime_q,
  rw [tsub_add_cancel_of_le (nat.one_le_of_lt q_pos)] at h'',
  let n : ℤ := ann.coeff 0 * ∏ (i : ℕ) in range ann.nat_degree, (-(i + 1 : ℕ)) ^ q,
  let n' := n / q + n'', let r := n % q, have h' := n.div_add_mod (q + 1),
  use [n', r], refine ⟨⟨_, int.mod_lt_of_pos _ int_q_pos⟩, _⟩,
  { simp only [r, n], apply lt_of_le_of_ne (int.mod_nonneg _ int_q_0),
    symmetry, rw [ne.def, euclidean_domain.mod_eq_zero], intros q_dvd,
    replace q_dvd := (int.prime.dvd_mul' prime_q q_dvd).resolve_left _, swap,
    { rw [int.coe_nat_dvd_left], apply nat.not_dvd_of_pos_of_lt,
      exacts [int.nat_abs_pos_of_ne_zero coeff0, nat.add_one_le_iff.mp hcq], },
    rw [prime.dvd_finset_prod_iff prime_int_q] at q_dvd,
    obtain ⟨a, ha, q_dvd⟩ := q_dvd, replace q_dvd := prime_int_q.dvd_of_dvd_pow q_dvd,
    rw [int.coe_nat_dvd_left, int.nat_abs_neg, int.nat_abs_of_nat] at q_dvd,
    revert q_dvd, apply nat.not_dvd_of_pos_of_lt (nat.zero_lt_succ _),
    rw [mem_range, ← add_lt_add_iff_right 1] at ha, exact ha.trans_le hnq, },
  simp_rw [h'', int.cast_inj, n', r, mul_add, ← add_assoc, add_left_inj,
    ← nat.mul_factorial_pred q_pos, int.coe_nat_mul, mul_comm (q : ℤ), mul_assoc, ← mul_add],
  refine (mul_right_inj' _).mpr _, rw [int.coe_nat_ne_zero], exact nat.factorial_ne_zero _,
  rw [int.mod_add_div], }

lemma abs_aeval_le (n : ℕ) (q : ℕ) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ n) :
  |(aeval x (F n q))| ≤ (n ^ q * (n ^ (q + 1)) ^ n : ℕ) := by
{ simp_rw [F, map_mul, map_pow, map_prod, map_pow, map_sub, aeval_X, aeval_C],
  simp only [algebra_map_int_eq, int.cast_coe_nat, int.cast_add, ring_hom.eq_int_cast,
    int.cast_one, prod_congr],
  simp_rw [abs_mul, nat.cast_mul, nat.cast_pow], apply mul_le_mul,
  { rw [abs_pow], apply pow_le_pow_of_le_left (abs_nonneg x), rw [abs_le],
    refine ⟨(right.neg_nonpos_iff.mpr _).trans hx.1, hx.2⟩, exact nat.cast_nonneg n, },
  { rw [abs_prod, pow_eq_prod_const], apply prod_le_prod, { exact λ _ _, abs_nonneg _, },
    intros i hi, rw [abs_pow], apply pow_le_pow_of_le_left (abs_nonneg (x - (i + 1))), rw [abs_le],
    rw [mem_range, nat.lt_iff_add_one_le] at hi, split,
    simp only [neg_le_sub_iff_le_add], apply le_add_of_nonneg_of_le hx.1,
    rwa [← nat.cast_add_one, nat.cast_le], refine (sub_le_self _ _).trans hx.2,
    rw [← nat.cast_add_one], exact nat.cast_nonneg _, },
  exacts [abs_nonneg _, pow_nonneg (nat.cast_nonneg _) _], }

lemma pow_le_sq_pow (n k : ℕ) (h : 0 < n) : n ^ k ≤ (n ^ 2) ^ (k / 2 + 1) := by
{ rw [← pow_mul], apply nat.pow_le_pow_of_le_right h,
  refine (nat.lt_mul_div_succ _ zero_lt_two).le, }

lemma hF_rhs (ann : ℤ[X]) (hann : aeval (exp 1) ann = 0) (ann0 : ann ≠ 0) :
  ∃ Q, ∀ q ≥ Q,
    ∀ (b : ℕ → ℝ) (hb : ∀ i < ann.nat_degree, b i ∈ set.Ioo 0 ((i + 1 : ℕ) : ℝ)),
      |∑ i in range ann.nat_degree, ann.coeff (i + 1) •
        -((i + 1) • (exp ((i + 1 : ℕ) - b i) * aeval (b i) (F ann.nat_degree q) : ℝ))| < q! := by
{ by_cases n0 : ann.nat_degree = 0,
  { have h := eq_C_of_nat_degree_eq_zero n0,
    rw [h, aeval_C, algebra_map_int_eq, ring_hom.eq_int_cast, int.cast_eq_zero] at hann,
    rw [hann, C_0] at h, exact absurd h ann0, },
  let coeff_max := ((range ann.nat_degree).image (λ i, |(ann.coeff (i + 1) : ℝ)|)).max'
    (nonempty.image (nonempty_range_iff.mpr n0) _),
  let Q := (((ann.nat_degree ^ ann.nat_degree) ^ 2) ^ 2 +
    ⌈ann.nat_degree • coeff_max * ann.nat_degree • exp (ann.nat_degree)⌉₊ + 1) * 2 + 1,
  use Q, intros q hq b hb',
  have n_pos := nat.pos_of_ne_zero n0,
  have coeff_max_nonneg : 0 ≤ coeff_max := by {
    refine (abs_nonneg (ann.coeff (0 + 1) : ℝ)).trans (le_max' _ _ (mem_image.mpr ⟨0, _, rfl⟩)),
    rwa [mem_range], },
  refine (calc |∑ i in range ann.nat_degree, ann.coeff (i + 1) •
          -((i + 1) • (exp ((i + 1 : ℕ) - b i) * aeval (b i) (F ann.nat_degree q)))|
      ≤ ∑ i in range ann.nat_degree, |ann.coeff (i + 1) •
          -((i + 1) • (exp ((i + 1 : ℕ) - b i) * aeval (b i) (F ann.nat_degree q)))|
      : abv_sum_le_sum_abv _ _
  ... ≤ ∑ i in range ann.nat_degree, coeff_max *
          (ann.nat_degree • (exp ann.nat_degree *
           (ann.nat_degree ^ q * (ann.nat_degree ^ (q + 1)) ^ ann.nat_degree : ℕ))) : by
      { apply sum_le_sum, intros i hi, rw [zsmul_eq_mul, abs_mul, abs_neg],
        have hi' := mem_range.mp hi, have hi'' := nat.add_one_le_iff.mpr hi',
        refine mul_le_mul _ _ (abs_nonneg _) coeff_max_nonneg,
        { apply le_max', rw [mem_image], exact ⟨i, hi, rfl⟩, },
        rw [abs_nsmul, nsmul_eq_mul, nsmul_eq_mul],
        refine mul_le_mul (by rwa [nat.cast_le]) _ (abs_nonneg _) (nat.cast_nonneg _),
        rw [abs_mul], refine mul_le_mul _ _ (abs_nonneg _) ((exp_pos _).le),
        { rw [abs_exp, exp_le_exp],
          refine (sub_le_self _ (hb' i hi').1.le).trans (nat.cast_le.mpr hi''), },
        refine abs_aeval_le ann.nat_degree q (b i) ⟨(hb' i hi').1.le, _⟩,
        exact (hb' i hi').2.le.trans (nat.cast_le.mpr hi''), }
  ... ≤ ann.nat_degree • (coeff_max *
          (ann.nat_degree • (exp ann.nat_degree *
           (ann.nat_degree ^ q * (ann.nat_degree ^ (q + 1)) ^ ann.nat_degree : ℕ))))
      : by rw [sum_const, card_range]).trans_lt _,
  have le_pow_self : ann.nat_degree ≤ ann.nat_degree ^ ann.nat_degree,
  { cases ann.nat_degree, { exact nat.zero_le _, },
    rw [pow_succ], apply le_mul_of_one_le_right (nat.zero_le _),
    rw [← one_pow n], exact pow_le_pow_of_le (le_add_of_nonneg_left (nat.zero_le _)), },
  have one_le_np := (nat.one_le_iff_ne_zero.mpr n0).trans le_pow_self,
  simp_rw [← smul_mul_assoc, ← mul_assoc, ← pow_mul, mul_comm, pow_mul],
  refine (_ : _ ≤ ((⌈(ann.nat_degree • coeff_max) * (ann.nat_degree • exp (ann.nat_degree))⌉₊ *
    (((ann.nat_degree ^ ann.nat_degree) ^ 2) ^ 2) ^ ((q + 1) / 2 + 1) : ℕ) : ℝ)).trans_lt _,
  { rw [nat.cast_mul (nat.ceil _)],
    refine mul_le_mul (nat.le_ceil _) _ (nat.cast_nonneg _) (le_trans _ (nat.le_ceil _)),
    rw [nat.cast_le],
    refine le_trans _ (pow_le_sq_pow _ (q + 1) ((one_le_sq_iff (nat.zero_le _)).mpr one_le_np)),
    rw [pow_two, mul_pow], refine mul_le_mul_of_nonneg_right _ (nat.zero_le _),
    exact calc ann.nat_degree ^ q
        = ann.nat_degree ^ q * 1
        : (mul_one _).symm
    ... ≤ (ann.nat_degree ^ ann.nat_degree) ^ q * (ann.nat_degree ^ ann.nat_degree)
        : mul_le_mul (pow_le_pow_of_le le_pow_self) one_le_np (zero_le _) (zero_le _)
    ... = (ann.nat_degree ^ ann.nat_degree) ^ (q + 1)
        : by rw [pow_add, pow_one],
    exact mul_nonneg (nsmul_nonneg coeff_max_nonneg _) (nsmul_nonneg (exp_pos _).le _), },
  have hq' := le_of_mul_le_mul_right
    (calc ((((ann.nat_degree ^ ann.nat_degree) ^ 2) ^ 2 +
        ⌈ann.nat_degree • coeff_max * ann.nat_degree • exp (ann.nat_degree)⌉₊ + 1 + 1) * 2)
      = Q + 1                         : by rw [add_mul, mul_two 1, ← add_assoc]
  ... ≤ q + 1                         : add_le_add_right hq 1
  ... = (q + 1) * 2 - (q + 1)         : by rw [mul_two, add_tsub_cancel_left]
  ... ≤ (q + 1) * 2 - (q + 1) / 2 * 2 : tsub_le_tsub_left (nat.div_mul_le_self _ _) _
  ... = ((q + 1) - (q + 1) / 2) * 2   : by rw [tsub_mul]) zero_lt_two,
  simp_rw [le_tsub_iff_left (nat.div_le_self _ _), ← add_assoc, add_le_add_iff_right] at hq',
  obtain ⟨c, hc⟩ := nat.exists_eq_add_of_le hq', rw [nat.cast_lt], conv_rhs { rw [hc], },
  refine lt_of_lt_of_le _ (nat.factorial_le (nat.le_add_right _ c)), rw [nat.factorial],
  have nppp_pos := pow_pos (pow_pos (pow_pos n_pos ann.nat_degree) 2) 2,
  have one_le_nppp := nat.one_le_of_lt nppp_pos,
  refine mul_lt_mul _ _ (pow_pos nppp_pos _) (nat.zero_le _),
  { rw [nat.lt_succ_iff], exact nat.le_add_left _ _, },
  refine le_trans _ (nat.factorial_le (nat.le_add_right _ _)),
  conv_rhs { rw [add_comm, ← (@tsub_add_cancel_iff_le _ _ _ _ 1 _).mpr one_le_nppp, add_assoc], },
  refine le_trans _ nat.factorial_mul_pow_le_factorial,
  rw [nat.succ_eq_add_one, tsub_add_cancel_of_le one_le_nppp, add_comm 1],
  exact le_mul_of_one_le_left (nat.zero_le _) (nat.one_le_of_lt (nat.factorial_pos _)), }

end e_transcendental

lemma remove_X_factor {x : ℝ} (hx : x ≠ 0) (p' : ℤ[X]) (p0' : p' ≠ 0) (p_ann' : aeval x p' = 0) :
  ∃ (p : ℤ[X]) (p0 : p ≠ 0) (hp : ¬ X ∣ p), aeval x p = 0 := by
{ revert p0' p_ann', refine unique_factorization_monoid.induction_on_prime p' (absurd rfl) _ _,
  { intros p p_unit p0 p_ann, obtain ⟨r, unit_r, hr⟩ := polynomial.is_unit_iff.mp p_unit,
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

section
open real e_transcendental

theorem e_transcendental : transcendental ℤ (exp 1) := by
{ rintro ⟨p', ⟨p0', p_ann'⟩⟩,
  obtain ⟨p, p0, hp, p_ann⟩ := remove_X_factor (exp_ne_zero 1) p' p0' p_ann',
  have coeff0 : p.coeff 0 ≠ 0 := (not_iff_not_of_iff polynomial.X_dvd_iff).mp hp,
  obtain ⟨Q, hQ⟩ := hF_rhs p p_ann p0,
  obtain ⟨q, hq, prime_q⟩ :=
    nat.exists_infinite_primes (max (Q + 1) (max ((p.coeff 0).nat_abs + 1) (p.nat_degree + 1))),
  have hQq : Q + 1 ≤ q                   := le_of_max_le_left hq,
  have hcq : (p.coeff 0).nat_abs + 1 ≤ q := le_of_max_le_left (le_of_max_le_right hq),
  have hnq : p.nat_degree + 1 ≤ q        := le_of_max_le_right (le_of_max_le_right hq),
  have q_0 : q ≠ 0 := prime_q.ne_zero,
  have q_pos : 0 < q := nat.pos_of_ne_zero q_0,
  obtain ⟨nl, r, hr, hl⟩ := hF_lhs q prime_q p p_ann coeff0 hcq hnq,
  obtain ⟨b, hb, h⟩ := hF (q - 1) p p_ann,
  replace hb : ∀ (i : ℕ), i < p.nat_degree → b i ∈ set.Ioo 0 ((i + 1 : ℕ) : ℝ),
  { intros i hi, convert hb i hi, rw [nat.cast_add, nat.cast_one], },
  --, rw [← nat.cast_one, ← nat.cast_add]
  specialize hQ (q - 1) (le_tsub_of_add_le_right hQq) b hb,
  rw [hl] at h, rw [← h] at hQ,
  replace hQ : ((|(q - 1)! * r + q! * nl| : ℤ) : ℝ) < (((q - 1)! : ℤ) : ℝ),
  { norm_cast at ⊢ hQ, exact hQ, },
  rw [int.cast_lt] at hQ,
  simp_rw [← nat.mul_factorial_pred q_pos, mul_comm q, int.coe_nat_mul, mul_assoc, ← mul_add,
    abs_mul, int.coe_nat_abs] at hQ,
  conv_rhs at hQ { rw [← mul_one ((q - 1)! : ℤ)], },
  replace hQ := lt_of_mul_lt_mul_left hQ (int.coe_nat_nonneg _),
  rw [← int.zero_add 1, int.lt_add_one_iff] at hQ,
  replace hQ := le_antisymm hQ (abs_nonneg _),
  rw [abs_eq_zero] at hQ,
  have hQ_mod : (r + ↑q * nl) % q = r :=
    by rw [int.add_mod, int.mul_mod, int.mod_self, zero_mul, int.zero_mod, add_zero, int.mod_mod,
      int.mod_eq_of_lt hr.1.le hr.2],
  have hQ_mod_pos : 0 < (r + ↑q * nl) % ↑q := hQ_mod.symm ▸ hr.1,
  exact (ne_of_lt hQ_mod_pos).symm (hQ.symm ▸ int.zero_mod _), }

end
