/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import ring_theory.polynomial.vieta

open equiv (perm)
open_locale big_operators polynomial
noncomputable theory

namespace is_scalar_tower
namespace mv_polynomial
variables {R A B σ : Type*}
variables [comm_semiring R] [comm_semiring A] [comm_semiring B]
variables [algebra R A] [algebra A B] [algebra R B] [is_scalar_tower R A B]

lemma algebra_map_aeval (f : σ → A) (p : mv_polynomial σ R) :
  algebra_map A B (mv_polynomial.aeval f p) = mv_polynomial.aeval (algebra_map A B ∘ f) p :=
by rw [mv_polynomial.aeval_def, mv_polynomial.aeval_def, ← mv_polynomial.coe_eval₂_hom,
  mv_polynomial.map_eval₂_hom, ←is_scalar_tower.algebra_map_eq, mv_polynomial.coe_eval₂_hom]

end mv_polynomial
end is_scalar_tower

namespace list

variables {R : Type*} {S : Type*}
variables [monoid R] [monoid S] [mul_action S R] [is_scalar_tower S R R] [smul_comm_class S R R]

@[simp] lemma prod_map_smul (l : list R) (s : S) :
  (l.map (λ x, s • x)).prod = s ^ l.length • l.prod :=
begin
  induction l with hd tl ih,
  { simp },
  { simp [ih, pow_add, smul_mul_smul, pow_mul_comm'], },
end

end list

namespace multiset

section

variables {R : Type*} {S : Type*}
variables [comm_monoid R] [monoid S] [mul_action S R] [is_scalar_tower S R R]
  [smul_comm_class S R R]

@[simp] lemma prod_map_smul (m : multiset R) (s : S) :
  (m.map (λ x, s • x)).prod = s ^ m.card • m.prod :=
quot.induction_on m $ by simp

end

variables {R : Type*} {S : Type*}
variables [comm_semiring R] [monoid S] [distrib_mul_action S R] [is_scalar_tower S R R]
  [smul_comm_class S R R]

lemma pow_smul_esymm (s : S) (n : ℕ) (m : multiset R) :
  s ^ n • m.esymm n = (m.map (λ x, s • x)).esymm n :=
begin
  rw [esymm, smul_sum, map_map, function.comp],
  refine (_ : _ = ((powerset_len n m).map (λ x : multiset R, s ^ x.card • x.prod)).sum).trans _,
  { refine congr_arg _ (map_congr rfl (λ x hx, _)),
    rw [(mem_powerset_len.1 hx).2], },
  simp_rw [← prod_map_smul, esymm, powerset_len_map, map_map],
end

end multiset

namespace mv_polynomial

variables {σ τ : Type*} {R S A : Type*}

section comm_semiring
variables [comm_semiring R] [fintype σ] [fintype τ]

lemma aeval_esymm_eq_multiset.esymm [comm_semiring S] [algebra R S] (f : σ → S) (n : ℕ) :
  aeval f (esymm σ R n) = (finset.univ.val.map f).esymm n :=
begin
  simp_rw [esymm, map_sum, map_prod, aeval_X],
  rw [multiset.esymm, finset.sum_eq_multiset_sum],
  conv_lhs { congr, congr, funext, rw finset.prod_eq_multiset_prod },
  rw [multiset.powerset_len_map, ← finset.map_val_val_powerset_len, multiset.map_map,
    multiset.map_map],
end

namespace symmetric_subalgebra
variables (σ R)

/-- **Fundamental theorem of symmetric polynomials** -/
noncomputable!
def equiv_mv_polynomial :
  symmetric_subalgebra σ R ≃ₐ[R] mv_polynomial (fin (fintype.card σ)) R := sorry

variables {σ R}

lemma equiv_mv_polynomial_symm_apply
  (p : mv_polynomial (fin (fintype.card σ)) R) :
(equiv_mv_polynomial σ R).symm p = aeval (λ i : fin (fintype.card σ),
  (⟨esymm σ R (i + 1), esymm_is_symmetric _ _ _⟩ : symmetric_subalgebra σ R)) p := sorry
/-
lemma equiv_mv_polynomial_apply_aeval
  (p : mv_polynomial (fin (fintype.card σ)) R) :
equiv_mv_polynomial σ R (aeval (λ i : fin (fintype.card σ),
  (⟨esymm σ R (i + 1), esymm_is_symmetric _ _ _⟩ : symmetric_subalgebra σ R)) p) = p :=
alg_equiv.injective (equiv_mv_polynomial σ R).symm
  ((alg_equiv.symm_apply_apply _ _).trans (equiv_mv_polynomial_symm_apply _ _ _).symm)
-/

variables (σ R) [comm_semiring S] [algebra R S]

def aeval_multiset (m : multiset S) :
  symmetric_subalgebra σ R →ₐ[R] S :=
(aeval (λ i : fin (fintype.card σ), m.esymm (i + 1))).comp (equiv_mv_polynomial σ R)

variables {σ R}

lemma aeval_multiset_apply (m : multiset S) (p : symmetric_subalgebra σ R) :
  aeval_multiset σ R m p =
    aeval (λ i : fin _, m.esymm (i + 1)) (equiv_mv_polynomial σ R p) := rfl

def aeval_multiset_map (f : σ → S) (p : symmetric_subalgebra σ R) :
  aeval_multiset σ R (finset.univ.val.map f) p = aeval f (p : mv_polynomial σ R) :=
begin
  rw [aeval_multiset_apply],
  have : aeval f ↑p = aeval f ↑((equiv_mv_polynomial σ R).symm (equiv_mv_polynomial σ R p)),
  { rw [alg_equiv.symm_apply_apply], },
  rw [this, equiv_mv_polynomial_symm_apply],
  change _ = aeval f ((symmetric_subalgebra σ R).val.comp (aeval _) (equiv_mv_polynomial σ R p)),
  rw [comp_aeval],
  have : (λ (i : fin (fintype.card σ)), (finset.univ.val.map f).esymm (↑i + 1)) =
    (λ (i : fin (fintype.card σ)), aeval f (esymm σ R (↑i + 1))),
  { simp_rw [aeval_esymm_eq_multiset.esymm], },
  rw [this, ← comp_aeval], refl,
end

def aeval_multiset_map' (f : τ → S) (p : symmetric_subalgebra σ R)
  (h : fintype.card σ = fintype.card τ) :
  aeval_multiset σ R (finset.univ.val.map f) p =
    aeval (f ∘ fintype.equiv_of_card_eq h) (p : mv_polynomial σ R) :=
begin
  rw [← aeval_multiset_map (f ∘ fintype.equiv_of_card_eq h) p,
    ← multiset.map_map f (fintype.equiv_of_card_eq h)], congr',
  refine (congr_arg finset.val (finset.map_univ_equiv (fintype.equiv_of_card_eq h)).symm).trans _,
  rw [finset.map_val], refl,
end

end symmetric_subalgebra

end comm_semiring

section comm_ring
variables [comm_ring R] [fintype σ] [comm_ring S] [algebra R S]
  [comm_ring A] [is_domain A] [algebra S A] [algebra R A] [is_scalar_tower R S A]

namespace symmetric_subalgebra

variables (σ R)

def scale_aeval_roots (q : S[X]) :
  symmetric_subalgebra σ R →ₐ[R] S :=
(aeval (λ i : fin (fintype.card σ), q.leading_coeff ^ (i : ℕ) * (-1) ^ (↑i + 1) *
  q.coeff (q.nat_degree - (i + 1)))).comp (equiv_mv_polynomial σ R)

variables {σ R}

lemma scale_aeval_roots_apply (q : S[X]) (p : symmetric_subalgebra σ R) :
  scale_aeval_roots σ R q p = aeval (λ i : fin _, q.leading_coeff ^ (i : ℕ) * (-1) ^ (↑i + 1) *
    q.coeff (q.nat_degree - (i + 1))) (equiv_mv_polynomial σ R p) := rfl

lemma scale_aeval_roots_eq_aeval_multiset (q : S[X]) (p : symmetric_subalgebra σ R)
  (inj : function.injective (algebra_map S A)) (h : fintype.card σ ≤ q.nat_degree)
  (hroots : (q.map (algebra_map S A)).roots.card = q.nat_degree) :
  algebra_map S A (scale_aeval_roots σ R q p) =
    aeval_multiset σ R ((q.map (algebra_map S A)).roots.map (λ x, q.leading_coeff • x)) p :=
begin
  rw [scale_aeval_roots_apply],
  refine (_ : _ = aeval (λ i : fin _, algebra_map S A (q.leading_coeff ^ (↑i + 1)) *
    (q.map (algebra_map S A)).roots.esymm (↑i + 1)) (equiv_mv_polynomial σ R p)).trans _,
  { simp_rw [is_scalar_tower.mv_polynomial.algebra_map_aeval, function.comp, map_mul,
      ← polynomial.coeff_map],
    congr', funext i,
    have hroots' : (q.map (algebra_map S A)).roots.card = (q.map (algebra_map S A)).nat_degree,
    { rw [hroots, polynomial.nat_degree_map_eq_of_injective inj], },
    rw [polynomial.coeff_eq_esymm_roots_of_card hroots',
      polynomial.nat_degree_map_eq_of_injective inj, polynomial.leading_coeff_map' inj,
      ← mul_assoc, mul_left_comm, ← mul_assoc, ← mul_assoc, mul_assoc _ _ (_ ^ _),
      pow_add q.leading_coeff, mul_comm _ (_ ^ 1), pow_one, map_mul],
    congr' 1,
    work_on_goal 1 { rw [mul_right_eq_self₀, map_pow, map_neg, map_one,
      tsub_tsub_cancel_of_le, ← mul_pow,
      neg_one_mul, neg_neg, one_pow, eq_self_iff_true, true_or], trivial, },
    work_on_goal 2 { rw [tsub_tsub_cancel_of_le], },
    work_on_goal 3 { rw [polynomial.nat_degree_map_eq_of_injective inj], exact tsub_le_self, },
    all_goals { exact nat.add_one_le_iff.mpr (i.2.trans_le h), }, },
  simp_rw [← algebra.smul_def, multiset.pow_smul_esymm, ← aeval_multiset_apply],
end

variables (σ)

def sum_polynomial (p : R[X]) : symmetric_subalgebra σ R :=
⟨∑ i, polynomial.aeval (X i) p, λ e, begin
  simp_rw [map_sum, rename, ← polynomial.aeval_alg_hom_apply, aeval_X, function.comp],
  rw [← equiv.sum_comp e (λ i, polynomial.aeval (X i) p)],
end⟩

lemma coe_sum_polynomial (p : R[X]) :
  (sum_polynomial σ p : mv_polynomial σ R) = ∑ i, polynomial.aeval (X i) p := rfl

variables {σ}

lemma aeval_multiset_sum_polynomial (m : multiset S) (p : R[X]) (hm : m.card = fintype.card σ) :
  aeval_multiset σ R m (sum_polynomial σ p) = (m.map (λ x, polynomial.aeval x p)).sum :=
begin
  have : m = finset.univ.val.map (λ i : fin m.to_list.length, m.to_list.nth_le i i.2),
  { have to_finset_fin_range : ∀ n, (list.fin_range n).to_finset = finset.univ :=
      λ n, finset.eq_univ_iff_forall.mpr $ λ x, list.mem_to_finset.mpr $ list.mem_fin_range x,
    have : (finset.univ.val : multiset (fin m.to_list.length)) = list.fin_range m.to_list.length,
    { rw [← to_finset_fin_range, list.to_finset_val, list.dedup_eq_self.mpr],
      exact list.nodup_fin_range _, },
    rw [this, multiset.coe_map],
    conv_lhs { rw [← m.coe_to_list], },
    refine congr_arg coe (list.ext_le _ (λ n h₁ h₂, _)),
    { rw [list.length_map, list.length_fin_range], },
    rw [list.nth_le_map', list.nth_le_fin_range], refl, },
  conv_lhs { rw [this], },
  rw [aeval_multiset_map'], swap, { rw [fintype.card_fin, multiset.length_to_list, hm], },
  rw [coe_sum_polynomial, map_sum], simp_rw [← polynomial.aeval_alg_hom_apply, aeval_X,
    function.comp],-- (fintype.equiv_of_card_eq _)],
  generalize_proofs h,
  refine (_ : _ =
    ∑ x : fin m.to_list.length, (polynomial.aeval (m.to_list.nth_le x _)) p).trans _, swap,
  exact equiv.sum_comp (fintype.equiv_of_card_eq _),
  congr',
  
end
#check list.fin_range
#check image_multiset

end symmetric_subalgebra

end comm_ring

variables (σ R)

variables {σ R}

end mv_polynomial
