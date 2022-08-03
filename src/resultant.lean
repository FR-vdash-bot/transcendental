/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import linear_algebra.determinant
import linear_algebra.matrix.block
import ring_theory.localization.fraction_ring

noncomputable theory

open_locale polynomial big_operators matrix

namespace polynomial

section
variables {R : Type*} [semiring R]
variables {S : Type*} [semiring S]

lemma degree_add_lt_of_degree_lt {p q : R[X]} {n : ℕ} (hp : degree p < n)
  (hq : degree q < n) : degree (p + q) < n :=
(degree_add_le p q).trans_lt (max_lt hp hq)

protected def degree_le.map (f : R →+* S) {n : with_bot ℕ} : degree_le R n → degree_le S n :=
λ p, ⟨(p : R[X]).map f, mem_degree_le.mpr ((degree_map_le f p).trans (mem_degree_le.mp p.2))⟩

protected def degree_le.mul {n₁ n₂ : with_bot ℕ} (p₁ : degree_le R n₁) (p₂ : degree_le R n₂) :
  degree_le R (n₁ + n₂) :=
⟨↑p₁ * ↑p₂, mem_degree_le.mpr $ (degree_mul_le _ _).trans $
                                  add_le_add (mem_degree_le.mp p₁.2) (mem_degree_le.mp p₂.2)⟩

protected def degree_le.map_mul (f : R →+* S)
  {n₁ n₂ : with_bot ℕ} (p₁ : degree_le R n₁) (p₂ : degree_le R n₂) :
  degree_le.map f (degree_le.mul p₁ p₂) =
    degree_le.mul (degree_le.map f p₁) (degree_le.map f p₂) :=
by simp_rw [degree_le.map, degree_le.mul, submodule.coe_mk, polynomial.map_mul]

protected def degree_lt.map {n : ℕ} (f : R →+* S) : degree_lt R n → degree_lt S n :=
λ p, ⟨(p : R[X]).map f, mem_degree_lt.mpr ((degree_map_le f p).trans_lt (mem_degree_lt.mp p.2))⟩

@[simps apply]
def degree_lt_add_assoc {m n o : ℕ} :
  ↥(degree_lt R (m + n + o)) ≃ₗ[R] ↥(degree_lt R (m + (n + o))) :=
{ to_fun := λ x, ⟨x, add_assoc m n o ▸ x.2⟩,
  inv_fun := λ x, ⟨x, (add_assoc m n o).symm ▸ x.2⟩,
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl,
  left_inv := λ ⟨x, hx⟩, rfl,
  right_inv := λ ⟨x, hx⟩, rfl, }

end

section
variables (R : Type*) [comm_ring R]

/-- The monomials form a basis on `polynomial.degree_lt R`. -/
def degree_lt.basis_monomials (n : ℕ) : basis (fin n) R (degree_lt R n) :=
basis.of_repr ((degree_lt_equiv R n).trans (finsupp.linear_equiv_fun_on_fintype R R _).symm)

@[simp] lemma degree_lt.coe_basis_monomials (n : ℕ) :
  (degree_lt.basis_monomials R n : (fin n) → (degree_lt R n)) = λ s, ⟨monomial s 1,
    mem_degree_lt.mpr ((degree_monomial_le s 1).trans_lt (with_bot.coe_lt_coe.mpr s.2))⟩ := by
{ funext n',
  convert_to (degree_lt_equiv R n).symm (finsupp.linear_equiv_fun_on_fintype R R _ _) = _,
  rw [linear_equiv.symm_apply_eq, finsupp.linear_equiv_fun_on_fintype_single],
  convert_to _ = λ n'', ((monomial n') 1 : R[X]).coeff ↑n'', funext n'',
  simp_rw [pi.single_apply, coeff_monomial, ← fin.ext_iff, @comm _ (=)], }

end

end polynomial

open polynomial

namespace submodule

variables {R : Type*} [semiring R] {M : Type*} [add_comm_monoid M]
  {module_M : module R M} (p : submodule R M)

@[simp] lemma mk_zero : (⟨(0 : M), zero_mem p⟩ : p) = 0 := (submodule.mk_eq_zero _ _).mpr rfl

end submodule

namespace basis

section prod

variables {R : Type*} [comm_ring R]

variables {ι ι' : Type*}
variables {M : Type*} [add_comm_monoid M] [module R M]
variables {M' : Type*} [add_comm_monoid M'] [module R M']
variables (b : basis ι R M) (b' : basis ι' R M')

lemma prod_apply_inl (i) :
  b.prod b' (sum.inl i) = ⟨b i, 0⟩ :=
by ext; simp only [prod_apply_inl_fst, prod_apply_inl_snd]

lemma prod_apply_inr (i) :
  b.prod b' (sum.inr i) = ⟨0, b' i⟩ :=
by ext; simp only [prod_apply_inr_fst, prod_apply_inr_snd]

end prod

variables {R : Type*} [semiring R]

section reindex

variables {ι : Type*} {ι' : Type*} {ι'' : Type*}
variables {M : Type*}

variables [add_comm_monoid M] [module R M]
variables (b : basis ι R M)
variables (e : ι ≃ ι') (e' : ι' ≃ ι'')

lemma reindex_reindex : (b.reindex e).reindex e' = b.reindex (e.trans e') :=
by { ext, simp_rw [reindex_apply, equiv.symm_trans_apply], }

lemma reindex_reindex_symm_cancel : (b.reindex e).reindex e.symm = b :=
by rw [reindex_reindex, equiv.self_trans_symm, basis.reindex_refl]

end reindex

section map

variables {ι : Type*}
variables {M : Type*} [add_comm_monoid M] [module R M]
variables {M' : Type*} [add_comm_monoid M'] [module R M']
variables {M'' : Type*} [add_comm_monoid M''] [module R M'']
variables (b : basis ι R M)
variables (f : M ≃ₗ[R] M') (f' : M' ≃ₗ[R] M'')

lemma map_refl : b.map (linear_equiv.refl R M) = b :=
by { ext, rw [map_apply, linear_equiv.refl_apply], }

lemma map_map : (b.map f).map f' = b.map (f.trans f') :=
by { ext, simp_rw [map_apply, linear_equiv.trans_apply], }

lemma map_map_symm_cancel : (b.map f).map f.symm = b :=
by rw [map_map, linear_equiv.self_trans_symm, basis.map_refl]

end map

end basis

namespace prod

variables {α β γ : Type*} [comm_monoid α] [comm_monoid β] {s : finset γ} {f : γ → α} {g : γ → β}

@[to_additive]
lemma prod_mk : ∏ c in s, (f c, g c) = (∏ c in s, f c, ∏ c in s, g c) :=
by ext; simp only [fst_prod, snd_prod]

end prod

namespace matrix

variables {R : Type*} [comm_ring R]

variables {M₁ : Type*} [add_comm_group M₁] [module R M₁]
variables {M₂ : Type*} [add_comm_group M₂] [module R M₂]
variables {M₃ : Type*} [add_comm_group M₃] [module R M₃]
variables {M₄ : Type*} [add_comm_group M₄] [module R M₄]
variables {m n : Type*} [decidable_eq m] [decidable_eq n] [fintype m] [fintype n]
variables {l o : Type*} [decidable_eq l] [decidable_eq o] [fintype l] [fintype o]

@[simp] lemma to_lin_reindex (v₁ : basis o R M₁) (v₂ : basis l R M₂)
  (eₘ : m ≃ l) (eₙ : n ≃ o) (M : matrix m n R) :
  to_lin v₁ v₂ (reindex eₘ eₙ M) =
    to_lin (v₁.reindex eₙ.symm) (v₂.reindex eₘ.symm) M := by
{ ext,
  simp_rw [to_lin_apply, ← finset.univ_map_equiv_to_embedding eₘ,
    finset.sum_map finset.univ eₘ.to_embedding],
  apply fintype.sum_congr, intros i, congr' 1,
  { rw [equiv.to_embedding_apply, basis.coe_reindex_repr, equiv.symm_symm, reindex_apply],
    simp_rw [mul_vec, dot_product, ← finset.univ_map_equiv_to_embedding eₙ,
      finset.sum_map finset.univ eₙ.to_embedding],
    apply fintype.sum_congr, intros j, congr' 1,
    simp_rw [minor_apply, equiv.to_embedding_apply, equiv.symm_apply_apply], },
  simp_rw [equiv.to_embedding_apply, basis.coe_reindex, function.comp_app, equiv.symm_symm], }

lemma to_lin_map_left (v₁ : basis n R M₁) (v₂ : basis m R M₂)
  (f : M₁ ≃ₗ[R] M₃) (M : matrix m n R) :
  to_lin (v₁.map f) v₂ M = (to_lin v₁ v₂ M).comp (f.symm : M₃ →ₗ[R] M₁) :=
by { ext, simp_rw [linear_map.coe_comp, function.comp_app, linear_equiv.coe_coe,
  to_lin_apply, basis.map_repr, linear_equiv.trans_apply], }

lemma to_lin_map_left_apply (v₁ : basis n R M₁) (v₂ : basis m R M₂)
  (f : M₁ ≃ₗ[R] M₃) (M : matrix m n R) (x) :
  to_lin (v₁.map f) v₂ M x = (to_lin v₁ v₂ M) (f.symm x) :=
by { rw [to_lin_map_left], refl, }

lemma to_lin_map_right (v₁ : basis n R M₁) (v₂ : basis m R M₂)
  (f : M₂ ≃ₗ[R] M₃) (M : matrix m n R) :
  to_lin v₁ (v₂.map f) M = (f : M₂ →ₗ[R] M₃).comp (to_lin v₁ v₂ M) :=
by { ext, simp_rw [linear_map.coe_comp, function.comp_app, linear_equiv.coe_coe,
  to_lin_apply, map_sum, linear_equiv.map_smulₛₗ, ring_hom.id_apply, basis.map_apply], }

lemma to_lin_map_right_apply (v₁ : basis n R M₁) (v₂ : basis m R M₂)
  (f : M₂ ≃ₗ[R] M₃) (M : matrix m n R) (x) :
  to_lin v₁ (v₂.map f) M x = f (to_lin v₁ v₂ M x) :=
by { rw [to_lin_map_right], refl, }

lemma to_lin_from_blocks
  (v₁ : basis l R M₁) (v₂ : basis m R M₂) (v₃ : basis n R M₃) (v₄ : basis o R M₄)
  (A : matrix n l R) (B : matrix n m R) (C : matrix o l R) (D : matrix o m R) :
  to_lin (v₁.prod v₂) (v₃.prod v₄) (from_blocks A B C D) =
    ((to_lin v₁ v₃ A).comp (linear_map.fst _ _ _) +
     (to_lin v₂ v₃ B).comp (linear_map.snd _ _ _)).prod
    ((to_lin v₁ v₄ C).comp (linear_map.fst _ _ _) +
     (to_lin v₂ v₄ D).comp (linear_map.snd _ _ _)) := by
{ apply (v₁.prod v₂).ext, intro i, rw [to_lin_self],
  cases i; simp only [linear_map.prod_apply, pi.prod, linear_map.add_apply, linear_map.comp_apply,
    linear_map.fst_apply, linear_map.snd_apply, basis.prod_apply_inl, basis.prod_apply_inr,
    map_zero, add_zero, zero_add, to_lin_self, finset.sum_on_sum,
    from_blocks_apply₁₁, from_blocks_apply₂₁, from_blocks_apply₁₂, from_blocks_apply₂₂,
    basis.prod_apply_inl, basis.prod_apply_inr, prod.smul_mk, smul_zero, prod.sum_mk,
    finset.sum_const_zero, prod.mk_add_mk], }

lemma to_lin_from_blocks_apply
  (v₁ : basis l R M₁) (v₂ : basis m R M₂) (v₃ : basis n R M₃) (v₄ : basis o R M₄)
  (A : matrix n l R) (B : matrix n m R) (C : matrix o l R) (D : matrix o m R) (x) :
  to_lin (v₁.prod v₂) (v₃.prod v₄) (from_blocks A B C D) x =
    (to_lin v₁ v₃ A x.1 + to_lin v₂ v₃ B x.2, to_lin v₁ v₄ C x.1 + to_lin v₂ v₄ D x.2) :=
by { rw [to_lin_from_blocks], refl, }

end matrix

namespace linear_equiv

/-- Product of modules is associative up to linear isomorphism. -/
@[simps apply]
def prod_assoc (R M M' M'' : Type*) [semiring R]
  [add_comm_monoid M] [add_comm_monoid M'] [add_comm_monoid M'']
  [module R M] [module R M'] [module R M''] : ((M × M') × M'') ≃ₗ[R] (M × M' × M'') :=
{ to_fun := λ x, (x.1.1, x.1.2, x.2),
  inv_fun := λ x, ((x.1, x.2.1), x.2.2),
  map_add' := λ ⟨⟨x, x'⟩, x''⟩ ⟨⟨y, y'⟩, y''⟩, rfl,
  map_smul' := λ r ⟨⟨x, x'⟩, x''⟩, rfl,
  left_inv := λ ⟨⟨x, x'⟩, x''⟩, rfl,
  right_inv := λ ⟨x, x', x''⟩, rfl, }

lemma prod_assoc_symm_apply (R M M' M'' : Type*) [semiring R]
  [add_comm_monoid M] [add_comm_monoid M'] [add_comm_monoid M'']
  [module R M] [module R M'] [module R M''] (x : M × M' × M'') :
  (prod_assoc R M M' M'').symm x = ((x.1, x.2.1), x.2.2) := rfl

end linear_equiv

variables {R : Type*} [comm_ring R]
variables {S : Type*} [comm_ring S]
variables (f : R →+* S)

@[simps apply] def resultant_aux {m n : ℕ} (p : degree_le R m) (q : degree_le R n) :
  degree_lt R n × degree_lt R m →ₗ[R] degree_lt R (n + m) :=
{ to_fun := λ x, ⟨p * x.1 + q * x.2, mem_degree_lt.mpr (by
  { refine degree_add_lt_of_degree_lt _ _,
    { rw [with_bot.coe_add, add_comm], refine (degree_mul_le _ _).trans_lt _,
      refine with_bot.add_lt_add_of_le_of_lt with_bot.coe_ne_bot _ _,
      exacts [mem_degree_le.mp p.2, mem_degree_lt.mp x.1.2], },
    { rw [with_bot.coe_add], refine (degree_mul_le _ _).trans_lt _,
      refine with_bot.add_lt_add_of_le_of_lt with_bot.coe_ne_bot _ _,
      exacts [mem_degree_le.mp q.2, mem_degree_lt.mp x.2.2], }, })⟩,
  map_add' := λ ⟨x₁, x₂⟩ ⟨y₁, y₂⟩,
    by { convert_to (⟨p * (x₁ + y₁) + q * (x₂ + y₂), _⟩ : degree_lt R (n + m)) =
      ⟨p * x₁ + q * x₂ + (p * y₁ + q * y₂), _⟩, rw [subtype.mk_eq_mk], ring, },
  map_smul' := λ s ⟨x₁, x₂⟩,
    by { convert_to (⟨↑p * s • x₁ + ↑q * s • x₂, _⟩ : degree_lt R (n + m)) =
      ⟨s • (↑p * x₁ + ↑q * x₂), _⟩,
      rw [subtype.mk_eq_mk, smul_add, mul_smul_comm, mul_smul_comm], } }

@[simps apply] def resultant_aux_linear_map {m n : ℕ} :
  degree_le R m × degree_le R n →ₗ[R] degree_lt R n × degree_lt R m →ₗ[R] degree_lt R (n + m) :=
{ to_fun := λ f, resultant_aux f.1 f.2,
  map_add' := λ f g, linear_map.ext (λ x, subtype.eq (by
  { rw [linear_map.add_apply, resultant_aux_apply, resultant_aux_apply, resultant_aux_apply,
      subtype.val_eq_coe, subtype.coe_mk,
      subtype.val_eq_coe, submodule.coe_add, subtype.coe_mk, subtype.coe_mk,
      prod.fst_add, prod.snd_add, submodule.coe_add, submodule.coe_add], ring, })),
  map_smul' := λ r f, linear_map.ext (λ x, subtype.eq (by
  { rw [linear_map.smul_apply, ring_hom.id_apply, resultant_aux_apply, resultant_aux_apply,
      subtype.val_eq_coe, subtype.coe_mk,
      subtype.val_eq_coe, submodule.coe_smul, subtype.coe_mk,
      prod.smul_fst, prod.smul_snd, submodule.coe_smul, submodule.coe_smul,
      smul_add, smul_mul_assoc, smul_mul_assoc], })), }

lemma resultant_aux_linear_map_apply_mk {m n : ℕ} (f₁ : degree_le R m) (f₂ : degree_le R n) :
  resultant_aux_linear_map (f₁, f₂) = resultant_aux f₁ f₂ :=
resultant_aux_linear_map_apply _

/-- The Sylvester matrix of two polynomials -/
def sylvester_matrix (m n : ℕ) (p : degree_le R m) (q : degree_le R n) :
  matrix (fin (n + m)) (fin (n + m)) R :=
linear_map.to_matrix
  (((degree_lt.basis_monomials R n).prod (degree_lt.basis_monomials R m)).reindex
    fin_sum_fin_equiv)
  (degree_lt.basis_monomials R (n + m))
  (resultant_aux p q)

lemma sylvester_matrix_eq (m n : ℕ) (p : degree_le R m) (q : degree_le R n) :
  sylvester_matrix m n p q = matrix.of (λ (i : fin (n + m)) (j : fin (n + m)), if ↑j < n
    then (↑p * X ^ (j : ℕ)).coeff i
    else (↑q * X ^ (j - n : ℕ)).coeff i) := by
{ nontriviality R,
  let v₁ := ((degree_lt.basis_monomials R n).prod (degree_lt.basis_monomials R m)).reindex
    fin_sum_fin_equiv,
  let v₂ := degree_lt.basis_monomials R (n + m),
  refine (matrix.to_lin v₁ v₂).injective _,
  rw [sylvester_matrix, matrix.to_lin_to_matrix],
  apply v₁.ext, intros i, rw [matrix.to_lin_self, resultant_aux_apply, ← set_like.coe_eq_coe,
    set_like.coe_mk, submodule.coe_sum, basis.reindex_apply, degree_lt.coe_basis_monomials],
  conv_rhs { congr, skip, funext,
    dsimp only, rw [submodule.coe_smul, matrix.of_apply, set_like.coe_mk], },
  cases lt_or_ge (i : ℕ) n with h h,
  { have : i = fin.cast_add m (⟨i, h⟩ : fin n) := by rw [fin.cast_add_mk, fin.eta],
    rw [this, fin_sum_fin_equiv_symm_apply_cast_add, basis.prod_apply_inl_fst,
      basis.prod_apply_inl_snd, submodule.coe_zero, mul_zero, add_zero,
      degree_lt.coe_basis_monomials, set_like.coe_mk, fin.coe_mk, monomial_one_right_eq_X_pow],
    simp_rw [this.symm, if_pos h, smul_monomial, smul_eq_mul, mul_one],
    rw [fin.sum_univ_eq_sum_range (λ n, monomial n _), ← as_sum_range'],
    conv_rhs { rw [add_comm], }, refine nat_degree_mul_le.trans_lt (add_lt_add_of_le_of_lt _ _),
    exact nat_degree_le_of_degree_le (mem_degree_le.mp p.2), simpa only [nat_degree_X_pow], },
  { have h' := (tsub_lt_iff_left h).mpr i.2,
    have : i = fin.nat_add n (⟨i - n, h'⟩ : fin m) :=
      by rw [fin.nat_add_mk, fin.eq_mk_iff_coe_eq, add_tsub_cancel_of_le h],
    rw [this, fin_sum_fin_equiv_symm_apply_nat_add, basis.prod_apply_inr_fst,
      basis.prod_apply_inr_snd, submodule.coe_zero, mul_zero, zero_add,
      degree_lt.coe_basis_monomials, set_like.coe_mk, fin.coe_mk, monomial_one_right_eq_X_pow],
    simp_rw [this.symm, if_neg (not_lt_of_ge h), smul_monomial, smul_eq_mul, mul_one],
    rw [fin.sum_univ_eq_sum_range (λ n, monomial n _), ← as_sum_range'],
    refine nat_degree_mul_le.trans_lt (add_lt_add_of_le_of_lt _ _),
    exact nat_degree_le_of_degree_le (mem_degree_le.mp q.2), simpa only [nat_degree_X_pow], }, }

lemma sylvester_matrix_apply (m n : ℕ) (p : degree_le R m) (q : degree_le R n)
  (i j : fin (n + m)) : sylvester_matrix m n p q i j = if ↑j < n
    then (↑p * X ^ (j : ℕ)).coeff i
    else (↑q * X ^ (j - n : ℕ)).coeff i :=
by rw [sylvester_matrix_eq, matrix.of_apply]

def resultant' : ∀ (m n : with_bot ℕ), degree_le R m → degree_le R n → R
| (m : ℕ) (n : ℕ) := λ p q, (sylvester_matrix m n p q).det
| _       _       := λ _ _, 0

/-
```
def sylvester_matrix {m n : ℕ} (p : degree_le R m) (q : degree_le R n) :
  matrix (fin (n + m)) (fin (n + m)) R :=
linear_map.to_matrix
  (((degree_lt.basis_monomials R n).prod (degree_lt.basis_monomials R m)).reindex
    fin_sum_fin_equiv)
  (degree_lt.basis_monomials R (n + m))
  (resultant_aux p q)
```
```
def resultant' : ∀ {m n : with_bot ℕ}, degree_le R m → degree_le R n → R
| (m' : ℕ) (n' : ℕ) := λ p q, (sylvester_matrix m' n' p q).det
| _        _        := λ _ _, 0
```
After making `m` and `n` explicit, we can see `m` and `n` now.
But we had to deal with far more defeq now, many proofs fails...
-/

lemma resultant'_degree_le_coe (m n : ℕ) (p : degree_le R m) (q : degree_le R n) :
resultant' m n p q = (sylvester_matrix m n p q).det := rfl

lemma resultant'_degree_le_bot_left (n : with_bot ℕ) (p : degree_le R ⊥) (q : degree_le R n) :
  resultant' ⊥ n p q = 0 :=
by cases n; refl

lemma resultant'_degree_le_bot_right (m : with_bot ℕ) (p : degree_le R m) (q : degree_le R ⊥) :
  resultant' m ⊥ p q = 0 :=
by cases m; refl

lemma resultant'_mk_congr
  {m n : with_bot ℕ}
  {p : R[X]} {pmem : p ∈ degree_le R m} {q : R[X]} {qmem : q ∈ degree_le R n}
  {m' n' : with_bot ℕ}
  {p' : R[X]} {p'mem : p' ∈ degree_le R m'} {q' : R[X]} {q'mem : q' ∈ degree_le R n'}
  (hm : m = m') (hn : n = n') (hp : p = p') (hq : q = q') :
  resultant' m n ⟨p, pmem⟩ ⟨q, qmem⟩ = resultant' m' n' ⟨p', p'mem⟩ ⟨q', q'mem⟩ :=
by { cases hm, cases hn, cases hp, cases hq, refl, }

lemma resultant'_congr {m n : with_bot ℕ} {p : degree_le R m} {q : degree_le R n}
  {m' n' : with_bot ℕ} {p' : degree_le R m'} {q' : degree_le R n'}
  (hm : m = m') (hn : n = n') (hp : (p : R[X]) = p') (hq : (q : R[X]) = q') :
  resultant' m n p q = resultant' m' n' p' q' := by
{ have := @resultant'_mk_congr _ _ _ _ p.1 p.2 q.1 q.2 _ _ p'.1 p'.2 q'.1 q'.2 hm hn hp hq,
  simpa only [subtype.eta] using this, }

lemma resultant'_congr' {m n : with_bot ℕ} {p : degree_le R m} {q : degree_le R n}
  {m' n' : with_bot ℕ} (hm : m = m') (hn : n = n') :
  resultant' m n p q = resultant' m' n' ⟨p, hm ▸ p.2⟩ ⟨q, hn ▸ q.2⟩ :=
by { apply resultant'_congr hm hn, rw [subtype.coe_mk], rw [subtype.coe_mk], }

lemma resultant'_mk_congr' {m n : with_bot ℕ}
  {p : R[X]} {pmem : p ∈ degree_le R m} {q : R[X]} {qmem : q ∈ degree_le R n}
  {m' n' : with_bot ℕ} (hm : m = m') (hn : n = n') :
  resultant' m n ⟨p, pmem⟩ ⟨q, qmem⟩ = resultant' m' n' ⟨p, hm ▸ pmem⟩ ⟨q, hn ▸ qmem⟩ :=
by apply resultant'_mk_congr hm hn rfl rfl

@[simp] lemma map_resultant' (m n : with_bot ℕ) (p : degree_le R m) (q : degree_le R n) :
  f (resultant' m n p q) = resultant' m n (degree_le.map f p) (degree_le.map f q) := by
{ cases m; cases n; simp ! only [map_zero],
  convert_to f (matrix.det _) = matrix.det _,
  simp_rw [ring_hom.map_det, sylvester_matrix_eq, ring_hom.map_matrix_apply], congr' 1, funext i j,
  simp_rw [matrix.map_apply, matrix.of_apply], split_ifs; simp_rw [← coeff_map, polynomial.map_mul,
    polynomial.map_pow, polynomial.map_X, degree_le.map, submodule.coe_mk], }

@[simps apply] def fin_add_comm {m n : ℕ} : fin (m + n) ≃ fin (n + m) :=
⟨ λ x, ⟨x, add_comm m n ▸ x.2⟩, λ x, ⟨x, add_comm n m ▸ x.2⟩,
  λ x, by simp_rw [fin.coe_mk, fin.eta], λ x, by simp_rw [fin.coe_mk, fin.eta]⟩

@[simps apply] def fin_add_assoc {m n o : ℕ} : fin (m + n + o) ≃ fin (m + (n + o)) :=
⟨ λ x, ⟨x, add_assoc m n o ▸ x.2⟩, λ x, ⟨x, (add_assoc m n o).symm ▸ x.2⟩,
  λ x, by simp_rw [fin.coe_mk, fin.eta], λ x, by simp_rw [fin.coe_mk, fin.eta]⟩

@[simp] def fin_add_comm_symm {m n : ℕ} : (@fin_add_comm m n).symm = @fin_add_comm n m := rfl

@[simp] lemma fin_add_flip_apply_left {m n : ℕ} {k : fin (m + n)} (h : ↑k < m) :
  fin_add_flip k = ⟨n + ↑k, add_lt_add_left h n⟩ :=
by convert fin_add_flip_apply_mk_left h; rw [fin.eta]

@[simp] lemma fin_add_flip_apply_right {m n : ℕ} {k : fin (m + n)} (h : m ≤ ↑k) :
  fin_add_flip k = ⟨↑k - m, tsub_le_self.trans_lt $ add_comm m n ▸ k.2⟩ :=
by convert fin_add_flip_apply_mk_right h k.2; rw [fin.eta]

lemma fin_add_comm_fin_add_flip_eq_add {m n : ℕ} (x : fin (m + n)) :
  by haveI pos : fact (0 < m + n) := ⟨fin.pos_iff_nonempty.mpr ⟨x⟩⟩; exact
  fin_add_comm (fin_add_flip x) = x + fin.of_nat' n := by
{ cases lt_or_ge ↑x m with h h,
  { simp_rw [fin_add_comm_apply, fin_add_flip_apply_left h, fin.of_nat', ← subtype.coe_inj,
      fin.coe_mk, fin.coe_eq_val, fin.add_def, nat.add_mod_mod, add_comm n],
    exact (nat.mod_eq_of_lt (add_lt_add_right h n)).symm, },
  { simp_rw [fin_add_comm_apply, fin_add_flip_apply_right h, fin.of_nat', ← subtype.coe_inj,
      fin.coe_mk, fin.coe_eq_val, fin.add_def, nat.add_mod_mod, ← fin.coe_eq_val,
      nat.mod_eq_sub_mod (add_le_add_right h n), add_tsub_add_eq_tsub_right],
    exact (nat.mod_eq_of_lt (tsub_le_self.trans_lt x.2)).symm, }, }

lemma of_nat_zero' {n : ℕ} [n0 : fact (0 < n)] : @fin.of_nat' n _ 0 = ⟨0, n0.1⟩ := rfl

-- Maybe `0`, `1`, `fin.of_nat` should be made to support cases other than `fin n.succ`.
lemma fin_rotate_pow_eq_add {m n : ℕ} (x : fin m) :
  by haveI pos : fact (0 < m) := ⟨fin.pos_iff_nonempty.mpr ⟨x⟩⟩; exact
  (fin_rotate m ^ n) x = x + fin.of_nat' n := by
{ induction n with n h,
  { rw [pow_zero, equiv.perm.coe_one, id.def, ← subtype.coe_inj, of_nat_zero', fin.coe_add,
    fin.coe_mk, add_zero], exact (nat.mod_eq_of_lt x.2).symm, },
  { cases m, { exact x.elim0, },
    rw [pow_succ, equiv.perm.coe_mul, function.comp_app, h, fin_rotate_succ_apply],
    simp_rw [← subtype.coe_inj, fin.coe_eq_val, fin.add_def, fin.val_eq_coe,
      fin.coe_of_nat_eq_mod', fin.coe_one', nat.add_mod_mod, nat.mod_add_mod, add_assoc], }, }

lemma fin_add_flip_trans_eq {m n : ℕ} :
  (@fin_add_flip m n).trans fin_add_comm = (fin_rotate (m + n)) ^ n := by
{ nontriviality fin (m + n),
  ext x, rw [equiv.coe_trans, function.comp_app, fin_add_comm_fin_add_flip_eq_add,
    fin_rotate_pow_eq_add], }

lemma resultant'_degree_le_zero (p : degree_le R (0 : ℕ)) (q : degree_le R (0 : ℕ)) :
  resultant' 0 0 p q = 1 :=
matrix.det_fin_zero

lemma resultant'_comm (m n : ℕ) (p : degree_le R m) (q : degree_le R n) :
  resultant' m n p q = (-1) ^ (m * n) * resultant' n m q p := by
{ cases nat.eq_zero_or_pos (n + m) with nm0,
  { obtain ⟨n0, m0⟩ := add_eq_zero_iff.mp nm0,
    revert p q, rw [n0, m0], intros p q, dsimp only [with_bot.coe_zero] at *,
    simp_rw [resultant'_degree_le_zero, mul_zero, pow_zero, one_mul], },
  have : sylvester_matrix n m q p = (λ i, (matrix.reindex fin_add_comm fin_add_comm
    (sylvester_matrix m n p q))ᵀ (fin_add_flip.trans fin_add_comm i))ᵀ,
  { funext i j,
    simp_rw [matrix.transpose, matrix.reindex_apply, matrix.minor_apply, sylvester_matrix_apply,
      equiv.coe_trans, function.comp_app, fin_add_comm_symm, fin_add_comm_apply, fin.coe_mk],
    have : ↑(fin_add_flip j) < n ↔ ¬ ↑j < m,
    { split,
      { intros h h',
        rw [fin_add_flip_apply_left h', fin.coe_mk] at h, exact absurd h le_self_add.not_lt, },
      { intros h', rw [not_lt] at h',
        rw [fin_add_flip_apply_right h', fin.coe_mk, tsub_lt_iff_left h'], exact j.2, }, },
    simp_rw [this], split_ifs with h',
    { rw [fin_add_flip_apply_left h', fin.coe_mk, add_tsub_cancel_left], },
    { rw [not_lt] at h', rw [fin_add_flip_apply_right h', fin.coe_mk], }, },
  simp_rw [resultant', this, matrix.det_transpose, matrix.det_permute, matrix.det_transpose,
    matrix.det_reindex_self, fin_add_flip_trans_eq, map_pow, ← mul_assoc],
  rw [add_comm] at h, rw [← tsub_add_cancel_of_le (nat.one_le_of_lt h), sign_fin_rotate],
  simp only [coe_coe, units.coe_pow, int.cast_pow, units.coe_neg_one, int.cast_neg, int.cast_one],
  have : (-1 : R) ^ (m + n - 1) = (-1) ^ (m + n + 1),
  { conv_rhs { rw [(_ : 1 = 2 - 1), ← nat.add_sub_assoc one_le_two,
      ← tsub_add_eq_add_tsub (nat.one_le_of_lt h), pow_add, neg_one_sq, mul_one], }, },
  rw [this, ← pow_mul, ← pow_add],
  cases eq_or_ne (-1 : R) 1 with h' h', { rw [h', one_pow, one_mul], },
  rw [(neg_one_pow_eq_one_iff_even h').mpr], { rw [one_mul], },
  rw [add_assoc, add_mul, ← add_assoc, mul_comm (_ + _)],
  exact (even_add_self _).add n.even_mul_succ_self, }

lemma resultant'_comm' {m n : with_bot ℕ} (mbot : m ≠ ⊥) (nbot : n ≠ ⊥)
  (p : degree_le R m) (q : degree_le R n) :
  resultant' m n p q = (-1) ^ (m.unbot mbot * n.unbot nbot) * resultant' n m q p :=
by { cases m, exact absurd rfl mbot,
  cases n, exact absurd rfl nbot, exact resultant'_comm m n p q, }

private
def resultant'_add_mul_hprq {m n o : ℕ} (h : o + n ≤ m) {p q r : R[X]}
  (hp : p ∈ degree_le R m) (hq : q ∈ degree_le R n) (hr : r ∈ degree_le R o) :
  p + r * q ∈ degree_le R m := by
{ apply submodule.add_mem _ hp, apply mem_degree_le.mpr,
  refine ((degree_mul_le _ _).trans (_ : r.degree + q.degree ≤ o + n)).trans _,
  { exact add_le_add (mem_degree_le.mp hr) (mem_degree_le.mp hq), },
  rwa [← with_bot.coe_add, with_bot.coe_le_coe], }

private
def resultant'_add_mul_hrxy {m n o : ℕ} (h : o + n ≤ m) {r x y : R[X]}
  (hr : r ∈ degree_le R o) (hx : x ∈ degree_lt R n) (hy : y ∈ degree_lt R m) :
  r * x + y ∈ degree_lt R m := by
{ apply submodule.add_mem _ _ hy, apply mem_degree_lt.mpr,
  refine ((degree_mul_le _ _).trans_lt (_ : r.degree + x.degree < o + n)).trans_le _,
  { exact with_bot.add_lt_add_of_le_of_lt with_bot.coe_ne_bot
      (mem_degree_le.mp hr) (mem_degree_lt.mp hx), },
  rwa [← with_bot.coe_add, with_bot.coe_le_coe], }

@[simps apply]
def resultant'_add_mul_aux {m n o : ℕ} (h : o + n ≤ m) {r : R[X]} (hr : r ∈ degree_le R o) :
  degree_lt R n × degree_lt R m →ₗ[R] degree_lt R n × degree_lt R m :=
{ to_fun := λ x, (x.1, ⟨r * x.1 + x.2, resultant'_add_mul_hrxy h hr x.1.2 x.2.2⟩),
  map_add' := λ ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩, by
  { simp_rw [prod.mk_add_mk, prod.mk.inj_iff], split;
    simp only [← subtype.coe_inj, submodule.coe_add, subtype.coe_mk], ring, },
  map_smul' := λ s ⟨⟨x, hx⟩, ⟨y, hy⟩⟩, by
  { simp_rw [prod.smul_mk, ring_hom.id_apply, prod.mk.inj_iff], split;
    simp only [← subtype.coe_inj, submodule.coe_smul, submodule.coe_add, subtype.coe_mk,
      smul_add, mul_smul_comm], }, }

@[simps apply]
def degree_lt.mul_left {m n o : ℕ} (h : o + n ≤ m) {r : R[X]} (hr : r ∈ degree_le R o) :
  degree_lt R n →ₗ[R] degree_lt R m :=
{ to_fun := λ x, ⟨r * x, mem_degree_lt.mpr $ (degree_mul_le _ _).trans_lt $
    (with_bot.add_lt_add_of_le_of_lt with_bot.coe_ne_bot (mem_degree_le.mp hr)
    (mem_degree_lt.mp x.2)).trans_le (with_bot.coe_le_coe.mpr h)⟩,
  map_add' := λ x y, by { simp_rw [submodule.coe_add, mul_add], refl, },
  map_smul' := λ s ⟨x, y⟩, by { simp_rw [submodule.coe_smul, mul_smul_comm], refl, }, }

lemma resultant'_add_mul_left {m n o : ℕ} (h : o + n ≤ m) {p q r : R[X]}
  (hp : p ∈ degree_le R m) (hq : q ∈ degree_le R n) (hr : r ∈ degree_le R o) :
  resultant' m n ⟨p + r * q, resultant'_add_mul_hprq h hp hq hr⟩ ⟨q, hq⟩
    = resultant' m n ⟨p, hp⟩ ⟨q, hq⟩ := by
{ have hprq := resultant'_add_mul_hprq h hp hq hr,
  rw [resultant'_degree_le_coe, sylvester_matrix],
  have : resultant_aux ⟨p + r * q, hprq⟩ ⟨q, hq⟩ =
    (resultant_aux ⟨p, hp⟩ ⟨q, hq⟩).comp (resultant'_add_mul_aux h hr),
  { apply linear_map.ext, rintros ⟨x, y⟩,
    dsimp only [linear_map.comp_apply, resultant_aux_apply, resultant'_add_mul_aux_apply,
      subtype.coe_mk], rw [subtype.mk_eq_mk], ring, },
  rw [this, linear_map.to_matrix_comp _ (((degree_lt.basis_monomials R n).prod
    (degree_lt.basis_monomials R m)).reindex fin_sum_fin_equiv)],
  rw [matrix.det_mul, ← @mul_one R _ (resultant' _ _ _ _),
    ← sylvester_matrix, ← resultant'_degree_le_coe], congr' 1,
  let b := (degree_lt.basis_monomials R n).prod (degree_lt.basis_monomials R m),
  rw [linear_map.det_to_matrix_eq_det_to_matrix _ b],
  have : linear_map.to_matrix b b (resultant'_add_mul_aux h hr) =
    matrix.from_blocks 1 0 (linear_map.to_matrix (degree_lt.basis_monomials R n)
    (degree_lt.basis_monomials R m) (degree_lt.mul_left h hr)) 1,
  { refine (matrix.to_lin b b).injective _, rw [matrix.to_lin_to_matrix],
    apply linear_map.ext, rintros ⟨x, y⟩,
    rw [matrix.to_lin_from_blocks_apply], dsimp only,
    rw [matrix.to_lin_one (degree_lt.basis_monomials R n)],
    rw [matrix.to_lin_to_matrix (degree_lt.basis_monomials R n) (degree_lt.basis_monomials R m)],
    rw [matrix.to_lin_one (degree_lt.basis_monomials R m)],
    rw [resultant'_add_mul_aux_apply],
    conv_rhs { congr, congr, rw [linear_map.id_apply], skip, rw [map_zero, linear_map.zero_apply],
      skip, congr, skip, rw [linear_map.id_apply], }, dsimp only,
    rw [add_zero, degree_lt.mul_left_apply], refl, },
  rw [this, matrix.det_from_blocks_zero₁₂, matrix.det_one, matrix.det_one, one_mul], }

lemma resultant'_add_mul_right {m n o : ℕ} (h : o + m ≤ n) {p q r : R[X]}
  (hp : p ∈ degree_le R m) (hq : q ∈ degree_le R n) (hr : r ∈ degree_le R o) :
  resultant' m n ⟨p, hp⟩ ⟨q + r * p, resultant'_add_mul_hprq h hq hp hr⟩
    = resultant' m n ⟨p, hp⟩ ⟨q, hq⟩ :=
by rw [resultant'_comm _ _ ⟨p, hp⟩, resultant'_comm _ _ ⟨p, hp⟩, resultant'_add_mul_left]

lemma resultant'_degree_le_coe_zero_left (n : ℕ) (p : degree_le R (0 : ℕ)) (q : degree_le R n) :
  resultant' (0 : ℕ) n p q = (p : R[X]).coeff 0 ^ n := by
{ rw [resultant'_degree_le_coe, matrix.det_of_upper_triangular],
  calc ∏ (i : fin (n + 0)), sylvester_matrix _ _ p q i i
      = ∏ (i : fin (n + 0)), (↑p * X ^ ↑i).coeff (0 + ↑i) : by
      { apply fintype.prod_congr, intro i,
        rw [sylvester_matrix_apply, if_pos (by convert i.2 : ↑i < n), zero_add], }
  ... = ∏ (i : fin (n + 0)), (p : R[X]).coeff 0 : by simp_rw [coeff_mul_X_pow]
  ... = (p : R[X]).coeff 0 ^ n : by rw [finset.prod_const, finset.card_fin, add_zero],
  intros i j hij, rw [sylvester_matrix_apply, if_pos (by convert j.2 : ↑j < n)],
  nontriviality R,
  rw [coeff_eq_zero_of_nat_degree_lt], apply nat_degree_mul_le.trans_lt,
  rwa [(@nat_degree_eq_zero_iff_degree_le_zero _ _ ↑p).mpr (mem_degree_le.mp p.2), zero_add,
    nat_degree_X_pow, subtype.coe_lt_coe], }

lemma resultant'_degree_le_coe_zero_right (m : ℕ) (p : degree_le R m) (q : degree_le R (0 : ℕ)) :
  resultant' m (0 : ℕ) p q = (q : R[X]).coeff 0 ^ m :=
by rw [resultant'_comm, resultant'_degree_le_coe_zero_left, mul_zero, pow_zero, one_mul]

lemma resultant'_degree_le_zero_left (n : ℕ) (p : degree_le R 0) (q : degree_le R n) :
  resultant' 0 n p q = (p : R[X]).coeff 0 ^ n :=
resultant'_degree_le_coe_zero_left n p q

lemma resultant'_degree_le_zero_right (m : ℕ) (p : degree_le R m) (q : degree_le R (0 : ℕ)) :
  resultant' m 0 p q = (q : R[X]).coeff 0 ^ m :=
resultant'_degree_le_coe_zero_right m p q

lemma resultant'_degree_le_coe_zero_left' (n : with_bot ℕ)
  (p : degree_le R 0) (q : degree_le R n) :
  resultant' (0 : ℕ) n p q = if h : n = ⊥ then 0 else (p : R[X]).coeff 0 ^ n.unbot h := by
{ induction n using with_bot.rec_bot_coe, { rw [dif_pos rfl, resultant'_degree_le_bot_right], },
  rw [dif_neg with_bot.coe_ne_bot, resultant'_degree_le_coe_zero_left, with_bot.unbot_coe], }

lemma resultant'_degree_le_coe_zero_right' (m : with_bot ℕ)
  (p : degree_le R m) (q : degree_le R (0 : ℕ)) :
  resultant' m (0 : ℕ) p q = if h : m = ⊥ then 0 else (q : R[X]).coeff 0 ^ m.unbot h := by
{ induction m using with_bot.rec_bot_coe, { rw [dif_pos rfl, resultant'_degree_le_bot_left], },
  rw [dif_neg with_bot.coe_ne_bot, resultant'_degree_le_coe_zero_right, with_bot.unbot_coe], }

lemma resultant'_degree_le_zero_left' (n : with_bot ℕ)
  (p : degree_le R 0) (q : degree_le R n) :
  resultant' 0 n p q = if h : n = ⊥ then 0 else (p : R[X]).coeff 0 ^ n.unbot h :=
resultant'_degree_le_coe_zero_left' n p q

lemma resultant'_degree_le_zero_right' (m : with_bot ℕ)
  (p : degree_le R m) (q : degree_le R (0 : ℕ)) :
  resultant' m 0 p q = if h : m = ⊥ then 0 else (q : R[X]).coeff 0 ^ m.unbot h :=
resultant'_degree_le_coe_zero_right' m p q

lemma resultant'_zero_left (m : with_bot ℕ) {n : ℕ} (n0 : 0 < n) (q : degree_le R n) :
  resultant' m n 0 q = 0 := by
{ induction m using with_bot.rec_bot_coe, { simp ! only, },
  let fin_zero : fin (n + m) := ⟨0, n0.trans_le le_self_add⟩,
  rw [resultant'_degree_le_coe, matrix.det_eq_zero_of_column_eq_zero fin_zero], intro i,
  rw [sylvester_matrix_apply, subtype.coe_mk, if_pos n0, submodule.coe_zero, zero_mul,
    coeff_zero], }

lemma resultant'_zero_right {m : ℕ} (n : with_bot ℕ) (m0 : 0 < m) (p : degree_le R m) :
  resultant' m n p 0 = 0 :=
by { induction n using with_bot.rec_bot_coe, { simp ! only, },
  rw [resultant'_comm, resultant'_zero_left n m0, mul_zero], }

lemma resultant'_zero_left' (m : with_bot ℕ) {n : with_bot ℕ} (n0 : 0 < n) (q : degree_le R n) :
  resultant' m n 0 q = 0 := by
{ induction n using with_bot.rec_bot_coe,
  { exact absurd n0 (with_bot.bot_lt_coe (0 : ℕ)).not_lt, },
  rw [← with_bot.coe_zero, with_bot.coe_lt_coe] at n0,
  exact resultant'_zero_left m n0 q, }

lemma resultant'_zero_right' {m : with_bot ℕ} (n : with_bot ℕ) (m0 : 0 < m) (p : degree_le R m) :
  resultant' m n p 0 = 0 := by
{ induction m using with_bot.rec_bot_coe,
  { exact absurd m0 (with_bot.bot_lt_coe (0 : ℕ)).not_lt, },
  induction n using with_bot.rec_bot_coe, { simp ! only, },
  rw [resultant'_comm, resultant'_zero_left' n m0, mul_zero], }

private
lemma resultant'_mul_left_field_aux {R : Type*} [field R] (m₁ m₂ n : ℕ)
  (p₁ : degree_le R m₁) (p₂ : degree_le R m₂) (q : degree_le R n) :
  sylvester_matrix (m₁ + m₂ : ℕ) n (degree_le.mul p₁ p₂ : _) q ⬝
    matrix.reindex fin_sum_fin_equiv fin_sum_fin_equiv
    (matrix.from_blocks (1 : matrix (fin n) (fin n) R) 0 0
      (sylvester_matrix m₂ m₁ p₂ ⟨1, mem_degree_le.mpr (degree_one_le.trans
        (with_bot.coe_le_coe.mpr zero_le'))⟩)) =
  matrix.reindex fin_add_assoc fin_add_assoc
  (sylvester_matrix m₂ (n + m₁ : ℕ) p₂ ⟨q, mem_degree_le.mpr ((mem_degree_le.mp q.2).trans
    (with_bot.coe_le_coe.mpr le_self_add))⟩ ⬝
  matrix.reindex fin_sum_fin_equiv fin_sum_fin_equiv
  (matrix.from_blocks (sylvester_matrix m₁ n p₁ q) 0 0 (1 : matrix (fin m₂) (fin m₂) R))) := by
{ let v₁ := ((degree_lt.basis_monomials R n).prod (((degree_lt.basis_monomials R m₁).prod
    (degree_lt.basis_monomials R m₂)).reindex fin_sum_fin_equiv)).reindex fin_sum_fin_equiv,
  let v₂ := ((degree_lt.basis_monomials R n).prod
    (degree_lt.basis_monomials R (m₁ + m₂))).reindex fin_sum_fin_equiv,
  let v₃ := degree_lt.basis_monomials R (n + (m₁ + m₂)),
  let v₁' := ((((degree_lt.basis_monomials R n).prod (degree_lt.basis_monomials R m₁)).reindex
    fin_sum_fin_equiv).prod (degree_lt.basis_monomials R m₂)).reindex fin_sum_fin_equiv,
  let v₂' := ((degree_lt.basis_monomials R (n + m₁)).prod
    (degree_lt.basis_monomials R m₂)).reindex fin_sum_fin_equiv,
  let v₃' := (degree_lt.basis_monomials R (n + m₁ + m₂)),
  refine (matrix.to_lin v₁ v₃).injective _, apply v₁.ext, intros i,
  rw [matrix.to_lin_mul_apply v₁ v₂ v₃, matrix.to_lin_reindex, sylvester_matrix,
    matrix.to_lin_to_matrix, basis.reindex_reindex_symm_cancel, basis.reindex_reindex_symm_cancel,
    matrix.to_lin_from_blocks_apply,
    map_zero, linear_map.zero_apply, add_zero, map_zero, linear_map.zero_apply, zero_add,
    matrix.to_lin_one, linear_map.id_apply, sylvester_matrix, matrix.to_lin_to_matrix],
  suffices hv₁ : v₁.reindex fin_add_assoc.symm = v₁'.map (linear_equiv.prod_assoc _ _ _ _),
  { have hv₃ : v₃.reindex fin_add_assoc.symm = v₃'.map degree_lt_add_assoc,
    { apply basis.eq_of_apply_eq, intro i,
      rw [basis.reindex_apply, basis.map_apply, equiv.symm_symm],
      simp_rw [polynomial.degree_lt.coe_basis_monomials,
        fin_add_assoc_apply, degree_lt_add_assoc_apply, submodule.coe_mk, fin.coe_mk], },
    rw [matrix.to_lin_reindex, matrix.to_lin_mul_apply _ v₂', hv₁, hv₃,
      sylvester_matrix, matrix.to_lin_map_right_apply, matrix.to_lin_to_matrix,
      matrix.to_lin_map_left_apply, matrix.to_lin_reindex, basis.reindex_reindex_symm_cancel,
      basis.reindex_reindex_symm_cancel, matrix.to_lin_from_blocks_apply,
      map_zero, linear_map.zero_apply, add_zero, map_zero, linear_map.zero_apply, zero_add,
      matrix.to_lin_one, linear_map.id_apply, sylvester_matrix, matrix.to_lin_to_matrix,
      subtype.ext_iff, degree_le.mul],
    repeat { rw [degree_lt_add_assoc_apply] <|>
             rw [resultant_aux_apply] <|>
             rw [subtype.coe_mk] <|>
             rw [linear_equiv.prod_assoc_symm_apply] <|>
             dsimp only, },
    ring, },
  apply basis.eq_of_apply_eq, intro i,
  rw [basis.map_apply, ← linear_equiv.symm_apply_eq],
  rw [basis.reindex_apply, equiv.symm_symm, basis.reindex_apply, basis.reindex_apply],
  cases lt_or_ge (i : ℕ) n with hi hi,
  { have h₁ : fin_add_assoc i = fin.cast_add (m₁ + m₂) (⟨i, hi⟩ : fin n),
    { rw [fin.cast_add_mk, fin_add_assoc_apply], },
    rw [h₁, fin_sum_fin_equiv_symm_apply_cast_add, basis.prod_apply_inl],
    have h₂' : i = fin.cast_add m₂ (⟨i, hi.trans_le le_self_add⟩ : fin (n + m₁)),
    { rw [fin.cast_add_mk, fin.eta], },
    conv_rhs { rw [h₂', fin_sum_fin_equiv_symm_apply_cast_add, basis.prod_apply_inl], },
    have h₁' : (⟨i, hi.trans_le le_self_add⟩ : fin (n + m₁)) = fin.cast_add m₁ (⟨i, hi⟩ : fin n),
    { rw [fin.cast_add_mk], },
    rw [h₁', basis.reindex_apply, fin_sum_fin_equiv_symm_apply_cast_add, basis.prod_apply_inl],
    refl, },
  { have prop₁ := (tsub_lt_iff_left hi).mpr (fin_add_assoc i).2,
    have h₁ : fin_add_assoc i = fin.nat_add n (⟨i - n, prop₁⟩ : fin (m₁ + m₂)),
    { rw [fin.nat_add_mk, fin_add_assoc_apply, fin.mk.inj_iff, add_tsub_cancel_of_le hi], },
    rw [h₁, fin_sum_fin_equiv_symm_apply_nat_add, basis.prod_apply_inr, basis.reindex_apply],
    cases lt_or_ge (i : ℕ) (n + m₁) with hi' hi',
    { have prop₂ : ↑i - n < m₁ := (tsub_lt_iff_left hi).mpr hi',
      have h₂ : (⟨i - n, prop₁⟩ : fin (m₁ + m₂)) = fin.cast_add m₂ (⟨i - n, prop₂⟩ : fin m₁),
      { rw [fin.cast_add_mk], },
      rw [h₂, fin_sum_fin_equiv_symm_apply_cast_add, basis.prod_apply_inl],
      have h₂' : i = fin.cast_add m₂ (⟨i, hi'⟩ : fin (n + m₁)),
      { rw [fin.cast_add_mk, fin.eta], },
      conv_rhs { rw [h₂', fin_sum_fin_equiv_symm_apply_cast_add, basis.prod_apply_inl], },
      have h₁' : (⟨i, hi'⟩ : fin (n + m₁)) = fin.nat_add n (⟨i - n, prop₂⟩ : fin m₁),
      { rw [fin.nat_add_mk, subtype.mk_eq_mk, add_tsub_cancel_of_le hi], },
      conv_rhs { rw [h₁', basis.reindex_apply, fin_sum_fin_equiv_symm_apply_nat_add,
        basis.prod_apply_inr], }, refl, },
    { have hi'' : m₁ ≤ ↑i - n := (le_tsub_iff_left hi).mpr hi',
      have prop₂ : ↑i - n - m₁ < m₂ := (tsub_lt_iff_left hi'').mpr prop₁,
      have h₂ : (⟨i - n, prop₁⟩ : fin (m₁ + m₂)) = fin.nat_add m₁ (⟨i - n - m₁, prop₂⟩ : fin m₂),
      { rw [fin.nat_add_mk, subtype.mk_eq_mk, add_tsub_cancel_of_le hi''], },
      rw [h₂, fin_sum_fin_equiv_symm_apply_nat_add, basis.prod_apply_inr],
      have h₂' : i = fin.nat_add (n + m₁) (⟨i - n - m₁, prop₂⟩ : fin m₂),
      { rw [fin.nat_add_mk, fin.eq_mk_iff_coe_eq, tsub_tsub, add_tsub_cancel_of_le hi'], },
      conv_rhs { rw [h₂', fin_sum_fin_equiv_symm_apply_nat_add, basis.prod_apply_inr], },
      refl, }, }, }

lemma resultant'_one_left (m n : ℕ) (q : degree_le R n) :
  resultant' m n ⟨1, mem_degree_le.mpr (degree_one_le.trans (with_bot.coe_le_coe.mpr zero_le'))⟩ q
    = (q : R[X]).coeff n ^ m := by
{ nontriviality R,
  rw [resultant'_degree_le_coe],
  suffices h : ∀ (i j : fin (n + m)), j < i → (sylvester_matrix m n
    ⟨1, mem_degree_le.mpr (degree_one_le.trans (with_bot.coe_le_coe.mpr zero_le'))⟩ q) i j = 0,
  { rw [matrix.det_of_upper_triangular _ h, sylvester_matrix_eq], dsimp only [subtype.coe_mk],
    simp_rw [matrix.of_apply, fin.prod_univ_eq_prod_range (λ i, ite (i < n)
      ((1 * X ^ i : R[X]).coeff i) ((↑q * X ^ (i - n) : R[X]).coeff i)), finset.prod_range_add],
    convert_to (∏ (i : ℕ) in finset.range n, (1 * X ^ i).coeff i) *
      ∏ (x : ℕ) in finset.range m, (↑q * X ^ (n + x - n)).coeff (n + x) = _, congr' 1,
    { apply finset.prod_congr rfl, intros x hx, rw [if_pos (finset.mem_range.mp hx)], },
    { apply finset.prod_congr rfl, intros x hx, rw [if_neg (le_self_add).not_lt], },
    simp_rw [add_tsub_cancel_left, coeff_mul_X_pow, one_mul, coeff_X_pow_self],
    rw [finset.prod_const_one, one_mul, finset.prod_const, finset.card_range], },
  intros i j hij, rw [sylvester_matrix_apply], dsimp only [subtype.coe_mk], split_ifs with hn,
  { simp_rw [one_mul, coeff_X_pow, subtype.coe_inj, if_neg hij.ne.symm], },
  { push_neg at hn, rw [← subtype.coe_lt_coe] at hij,
    rw [← add_tsub_cancel_of_le (hn.trans hij.le)],
    rw [← tsub_lt_tsub_iff_right hn] at hij,
    apply coeff_eq_zero_of_nat_degree_lt, apply nat_degree_mul_le.trans_lt,
    apply add_lt_add_of_le_of_lt (nat_degree_le_of_degree_le (mem_degree_le.mp q.2)),
    rwa [nat_degree_X_pow], }, }

lemma resultant'_one_right (m n : ℕ) (p : degree_le R m) :
  resultant' m n p ⟨1, mem_degree_le.mpr (degree_one_le.trans (with_bot.coe_le_coe.mpr zero_le'))⟩
    = (-1) ^ (m * n) * (p : R[X]).coeff m ^ n :=
by rw [resultant'_comm, resultant'_one_left]

lemma resultant'_shrink_left' (m n o : ℕ) (p : degree_le R m) (q : degree_le R n) :
  resultant' (m + o : ℕ) n ⟨↑p, mem_degree_le.mpr ((mem_degree_le.mp p.2).trans
    (with_bot.coe_le_coe.mpr le_self_add))⟩ q =
  (q : R[X]).coeff n ^ o * resultant' m n p q := by
{ let : fin (n + (m + o)) ≃ fin (n + m) ⊕ fin o :=
    (fin_sum_fin_equiv.trans fin_add_assoc).symm,
  have hl : ∀ {i},
    (fin_add_assoc $ fin_sum_fin_equiv $ (sum.inl i : fin (n + m) ⊕ fin o) : ℕ) = ↑i,
  { intro i,
    rw [fin_add_assoc_apply, subtype.coe_mk, fin_sum_fin_equiv_apply_left, fin.coe_cast_add], },
  have hr : ∀ {i},
    (fin_add_assoc $ fin_sum_fin_equiv $ (sum.inr i : fin (n + m) ⊕ fin o) : ℕ) = n + m + ↑i,
  { intro i,
    rw [fin_add_assoc_apply, subtype.coe_mk, fin_sum_fin_equiv_apply_right, fin.coe_nat_add], },
  rw [resultant'_degree_le_coe, ← matrix.det_reindex_self this,
    ← matrix.from_blocks_to_blocks (matrix.reindex this this _)],
  have h₁₁ : (matrix.reindex this this (sylvester_matrix _ _ ⟨↑p, _⟩ q)).to_blocks₁₁ =
    sylvester_matrix _ _ p q,
  { ext, simp_rw [matrix.to_blocks₁₁, matrix.reindex_apply, matrix.minor_apply,
      equiv.symm_symm, equiv.trans_apply, matrix.of_apply],
    rw [sylvester_matrix_apply, sylvester_matrix_apply, subtype.coe_mk],
    simp_rw [hl], },
  have h₂₁ : (matrix.reindex this this (sylvester_matrix _ _ ⟨↑p, _⟩ q)).to_blocks₂₁ = 0,
  { ext, simp_rw [pi.zero_apply, matrix.to_blocks₂₁, matrix.reindex_apply, matrix.minor_apply,
      equiv.symm_symm, equiv.trans_apply, matrix.of_apply],
    rw [sylvester_matrix_apply, subtype.coe_mk],
    simp_rw [hl, hr],
    nontriviality R,
    split_ifs with hn; apply coeff_eq_zero_of_nat_degree_lt; apply nat_degree_mul_le.trans_lt;
      refine (_ : _ < _).trans_le le_self_add; rw [nat_degree_X_pow],
    { conv_rhs { rw [add_comm] },
      exact add_lt_add_of_le_of_lt (nat_degree_le_of_degree_le (mem_degree_le.mp p.2)) hn, },
    { apply add_lt_add_of_le_of_lt (nat_degree_le_of_degree_le (mem_degree_le.mp q.2)),
      push_neg at hn, exact (tsub_lt_iff_left hn).mpr j.2, }, },
  rw [h₁₁, h₂₁, matrix.det_from_blocks_zero₂₁, mul_comm], congr' 1,
  have h₂₂ : ∀ (i j : fin o), j < i → (matrix.reindex this this (sylvester_matrix (m + o : ℕ) n
    ⟨↑p, mem_degree_le.mpr ((mem_degree_le.mp p.2).trans (with_bot.coe_le_coe.mpr le_self_add))⟩
    q)).to_blocks₂₂ i j = 0,
  { intros i j hij, simp_rw [matrix.to_blocks₂₂, matrix.reindex_apply, matrix.minor_apply,
      equiv.symm_symm, equiv.trans_apply, matrix.of_apply],
    rw [sylvester_matrix_apply, subtype.coe_mk], simp_rw [hr],
    rw [add_assoc, if_neg le_self_add.not_lt],
    nontriviality R,
    apply coeff_eq_zero_of_nat_degree_lt, apply nat_degree_mul_le.trans_lt,
    rw [nat_degree_X_pow, add_tsub_cancel_left, add_assoc],
    apply add_lt_add_of_le_of_lt (nat_degree_le_of_degree_le (mem_degree_le.mp q.2)),
    rwa [add_lt_add_iff_left, subtype.coe_lt_coe], },
  rw [matrix.det_of_upper_triangular _ h₂₂, sylvester_matrix_eq], dsimp only [subtype.coe_mk],
  simp_rw [matrix.to_blocks₂₂, matrix.reindex_apply, matrix.minor_apply, matrix.of_apply,
    equiv.symm_symm, equiv.trans_apply, hr],
  simp_rw [add_assoc, if_neg le_self_add.not_lt, add_tsub_cancel_left, coeff_mul_X_pow,
    finset.prod_const, finset.card_fin], }

lemma resultant'_shrink_right' (m n o : ℕ) (p : degree_le R m) (q : degree_le R n) :
  resultant' m (n + o : ℕ) p ⟨↑q, mem_degree_le.mpr ((mem_degree_le.mp q.2).trans
    (with_bot.coe_le_coe.mpr le_self_add))⟩ =
  (-1) ^ (m * o) * (p : R[X]).coeff m ^ o * resultant' m n p q :=
by rw [resultant'_comm, resultant'_shrink_left', resultant'_comm _ _ p, ← mul_assoc, ← mul_assoc,
  mul_right_comm (_ ^ (m * o)), mul_add, add_comm, pow_add]

lemma resultant'_shrink_left (m₁ m₂ n : ℕ) (hm : m₂ ≤ m₁) (q : degree_le R n) {p : R[X]}
  (hp₁ : p ∈ degree_le R m₁) (hp₂ : p ∈ degree_le R m₂) :
  resultant' m₁ n ⟨p, hp₁⟩ q = (q : R[X]).coeff n ^ (m₁ - m₂) * resultant' m₂ n ⟨p, hp₂⟩ q := by
{ rw [← add_tsub_cancel_of_le hm] at hp₁,
  rw [← resultant'_shrink_left' m₂ n (m₁ - m₂) ⟨p, hp₂⟩ q],
  apply resultant'_congr _ rfl _ rfl, { rw [add_tsub_cancel_of_le hm], },
  rw [subtype.coe_mk, subtype.coe_mk, subtype.coe_mk], }

lemma resultant'_shrink_right (m n₁ n₂ : ℕ) (hn : n₂ ≤ n₁) (p : degree_le R m) {q : R[X]}
  (hq₁ : q ∈ degree_le R n₁) (hq₂ : q ∈ degree_le R n₂) :
  resultant' m n₁ p ⟨q, hq₁⟩ =
    (-1) ^ (m * (n₁ - n₂)) * (p : R[X]).coeff m ^ (n₁ - n₂) * resultant' m n₂ p ⟨q, hq₂⟩ := by
{ rw [resultant'_comm, resultant'_shrink_left _ _ _ hn p hq₁ hq₂, resultant'_comm _ _ p],
  ring_nf, rw [← pow_add, ← add_mul, add_tsub_cancel_of_le hn], ring, }

private
lemma resultant'_mul_left_field' {R : Type*} [field R] (m₁ m₂ n : ℕ)
  (p₁ : degree_le R m₁) (p₂ : degree_le R m₂) (q : degree_le R n)
  (hp₂ : (p₂ : R[X]).coeff m₂ ≠ 0) :
  resultant' (m₁ + m₂ : ℕ) n (degree_le.mul p₁ p₂ : _) q =
    resultant' m₁ n p₁ q * resultant' m₂ n p₂ q := by
{ have := congr_arg matrix.det (resultant'_mul_left_field_aux m₁ m₂ n p₁ p₂ q),
  simp only [matrix.det_reindex_self, matrix.det_mul, matrix.det_from_blocks_zero₁₂,
    matrix.det_one, mul_one, one_mul] at this,
  simp_rw [← resultant'_degree_le_coe, resultant'_one_right, resultant'_shrink_right'] at this,
  have h : (-1) ^ (m₂ * m₁) * (p₂ : R[X]).coeff m₂ ^ m₁ *
    resultant' _ _ p₂ q * resultant' _ _ p₁ q = resultant' _ _ p₁ q * resultant' _ _ p₂ q *
      ((-1) ^ (m₂ * m₁) * (p₂ : R[X]).coeff m₂ ^ m₁) := by ring,
  rwa [h, mul_left_inj'] at this,
  refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ hp₂), }

private
lemma resultant'_mul_left_field {R : Type*} [field R] (m₁ m₂ n : ℕ)
  (p₁ : degree_le R m₁) (p₂ : degree_le R m₂) (q : degree_le R n) :
  resultant' (m₁ + m₂ : ℕ) n (degree_le.mul p₁ p₂ : _) q =
    resultant' m₁ n p₁ q * resultant' m₂ n p₂ q := by
{ cases n.eq_zero_or_pos with n0 n0,
  { revert q, rw [n0], intro q, simp_rw [resultant'_degree_le_coe_zero_right, pow_add], },
  cases eq_or_ne p₂ (0 : degree_le R m₂) with p₂0 p₂0,
  { rw [p₂0, degree_le.mul], conv_lhs { congr, congr, rw [submodule.coe_zero, mul_zero], },
    rw [submodule.mk_zero],
    conv_lhs { rw [resultant'_zero_left (m₁ + m₂ : ℕ) n0], },
    conv_rhs { rw [resultant'_zero_left m₂ n0], },
    rw [mul_zero], },
  have cp₂0 : (p₂ : R[X]) ≠ 0 := λ h, p₂0 (subtype.coe_inj.mp h),
  let m₂' := (p₂ : R[X]).nat_degree,
  have hm₂ : m₂' ≤ m₂,
  { apply with_bot.coe_le_coe.mp, rw [← degree_eq_nat_degree cp₂0], exact mem_degree_le.mp p₂.2, },
  let p₂' : degree_le R m₂' := ⟨↑p₂, mem_degree_le.mpr (degree_le_nat_degree)⟩,
  have coe_p₂' : (p₂' : R[X]) = ↑p₂ := rfl,
  have := resultant'_mul_left_field' _ _ _ p₁ p₂' q _, swap,
  { rwa [coe_p₂', coeff_nat_degree, leading_coeff_ne_zero], },
  let p₁p₂' : degree_le R (m₁ + m₂' : ℕ) := (degree_le.mul p₁ p₂' : _),
  have ex₁ := resultant'_shrink_left' (m₁ + m₂' : ℕ) n (m₂ - m₂') p₁p₂' q,
  have ex₂ := resultant'_shrink_left' m₂' n (m₂ - m₂') p₂' q,
  have h₁ : ∀ {h}, resultant' (m₁ + m₂' + (m₂ - m₂') : ℕ) n ⟨↑p₁p₂', h⟩ q =
    resultant' (m₁ + m₂ : ℕ) n (degree_le.mul p₁ p₂ : _) q,
  { have : m₁ + m₂' + (m₂ - m₂') = m₁ + m₂, { rw [add_assoc, add_tsub_cancel_of_le hm₂], },
    rw [this], intro h, refl, },
  have h₂ : ∀ {h}, resultant' (m₂' + (m₂ - m₂') : ℕ) n ⟨↑p₂', h⟩ q = resultant' m₂ n p₂ q,
  { have : m₂' + (m₂ - m₂') = m₂, { rw [add_tsub_cancel_of_le hm₂], },
    rw [this], intro h, refl, },
  rw [h₁] at ex₁, rw [h₂] at ex₂, rw [ex₁, ex₂, this], ring, }

private
lemma resultant'_mul_left_domain [is_domain R] (m₁ m₂ n : ℕ)
  (p₁ : degree_le R m₁) (p₂ : degree_le R m₂) (q : degree_le R n) :
  resultant' (m₁ + m₂ : ℕ) n (degree_le.mul p₁ p₂ : _) q =
    resultant' m₁ n p₁ q * resultant' m₂ n p₂ q := by
{ haveI := field (fraction_ring R),
  apply is_fraction_ring.injective R (fraction_ring R),
  simp_rw [map_mul, map_resultant', degree_le.map_mul, resultant'_mul_left_field], }

lemma resultant'_mul_left (m₁ m₂ n : with_bot ℕ)
  (p₁ : degree_le R m₁) (p₂ : degree_le R m₂) (q : degree_le R n) :
  resultant' (m₁ + m₂) n (degree_le.mul p₁ p₂ : _) q =
    resultant' m₁ n p₁ q * resultant' m₂ n p₂ q := by
{ cases m₁; cases m₂; cases n; simp ! only [mul_zero, zero_mul],
  convert_to matrix.det _ = matrix.det _ * matrix.det _,
  let f : ∀ {m : ℕ} (p : degree_le R m), degree_le (mv_polynomial R ℤ) m := λ m p, by
  { use (p : R[X]).sum (λ n x, C (mv_polynomial.X x) * X ^ n),
    rw [mem_degree_le], apply (degree_sum_le _ _).trans, rw [finset.sup_le_iff],
    intros b hb, apply (degree_C_mul_X_pow_le _ _).trans,
    exact (le_degree_of_mem_supp _ hb).trans (mem_degree_le.mp p.2), },
  have hf : resultant' (m₁ + m₂) n (degree_le.mul (f p₁) (f p₂) : _) (f q) =
    resultant' m₁ n (f p₁) (f q) * resultant' m₂ n (f p₂) (f q) :=
  resultant'_mul_left_domain _ _ _ _ _ _,
  let f' : mv_polynomial R ℤ →+* R := (mv_polynomial.aeval (λ x : R, x) : _ →ₐ[ℤ] _),
  have f_cancel : ∀ {m : ℕ} (p : degree_le R m), degree_le.map f' (f p) = p := λ m p, by
  { rw [degree_le.map, ← set_like.coe_eq_coe, set_like.coe_mk, set_like.coe_mk, ← coe_map_ring_hom,
      sum_def, map_sum, coe_map_ring_hom],
    simp_rw [polynomial.map_mul, polynomial.map_pow, map_C, map_X, alg_hom.coe_to_ring_hom,
      mv_polynomial.aeval_X], rw [← as_sum_support_C_mul_X_pow], },
  replace hf := congr_arg f' hf,
  simpa only [map_mul, map_resultant', degree_le.map_mul, f_cancel] using hf, }

lemma resultant'_mul_right (m n₁ n₂ : with_bot ℕ)
  (p : degree_le R m) (q₁ : degree_le R n₁) (q₂ : degree_le R n₂) :
  resultant' m (n₁ + n₂) p (degree_le.mul q₁ q₂ : _) =
    resultant' m n₁ p q₁ * resultant' m n₂ p q₂ := by
{ cases m; cases n₁; cases n₂; simp ! only [mul_zero, zero_mul],
  convert_to matrix.det _ = matrix.det _ * matrix.det _,
  simp_rw [← resultant'_degree_le_coe, resultant'_comm _ _ p], dsimp only [with_bot.coe_add],
  simp_rw [resultant'_mul_left, mul_add, pow_add], ring, }

/-- The resultant of two polynomials -/
def resultant [comm_ring R] (p q : R[X]) : R :=
resultant' p.degree q.degree ⟨p, mem_degree_le.mpr le_rfl⟩ ⟨q, mem_degree_le.mpr le_rfl⟩

lemma resultant_zero_left (q : R[X]) :
  resultant 0 q = 0 :=
by rw [resultant, submodule.mk_zero, degree_zero, resultant'_degree_le_bot_left]

lemma resultant_zero_right (p : R[X]) :
  resultant p 0 = 0 :=
by rw [resultant, submodule.mk_zero, degree_zero, resultant'_degree_le_bot_right]

lemma resultant_C_left' {x : R} (x0 : x ≠ 0) {q : R[X]} (q0 : q ≠ 0) :
  resultant (C x) q = x ^ q.nat_degree :=
by rw [resultant, resultant'_mk_congr' (degree_C x0) (degree_eq_nat_degree q0),
    resultant'_degree_le_zero_left, subtype.coe_mk, coeff_C_zero]

lemma resultant_C_right' {x : R} (x0 : x ≠ 0) {p : R[X]} (p0 : p ≠ 0) :
  resultant p (C x) = x ^ p.nat_degree :=
by rw [resultant, resultant'_mk_congr' (degree_eq_nat_degree p0) (degree_C x0),
    resultant'_degree_le_zero_right, subtype.coe_mk, coeff_C_zero]

lemma resultant_C_left (x : R) {q : R[X]} (n0 : q.nat_degree > 0) :
  resultant (C x) q = x ^ q.nat_degree := by
{ cases eq_or_ne x 0 with x0 x0, { rw [x0, C_0, resultant_zero_left, zero_pow n0], },
  have q0 : q ≠ 0, { intros q0, rw [q0, nat_degree_zero] at n0, exact le_rfl.not_lt n0, },
  rw [resultant, resultant'_mk_congr' (degree_C x0) (degree_eq_nat_degree q0),
    resultant'_degree_le_zero_left, subtype.coe_mk, coeff_C_zero], }

lemma resultant_C_right {x : R} {p : R[X]} (m0 : p.nat_degree > 0)  :
  resultant p (C x) = x ^ p.nat_degree := by
{ cases eq_or_ne x 0 with x0 x0, { rw [x0, C_0, resultant_zero_right, zero_pow m0], },
  have p0 : p ≠ 0, { intros p0, rw [p0, nat_degree_zero] at m0, exact le_rfl.not_lt m0, },
  rw [resultant, resultant'_mk_congr' (degree_eq_nat_degree p0) (degree_C x0),
    resultant'_degree_le_zero_right, subtype.coe_mk, coeff_C_zero], }

lemma resultant_one_left {q : R[X]} (q0 : q ≠ 0) :
  resultant 1 q = 1 :=
by { nontriviality R, rw [← C_1, resultant_C_left' (one_ne_zero : (1 : R) ≠ 0) q0, one_pow], }

lemma resultant_one_right {p : R[X]} (p0 : p ≠ 0) :
  resultant p 1 = 1 :=
by { nontriviality R, rw [← C_1, resultant_C_right' (one_ne_zero : (1 : R) ≠ 0) p0, one_pow], }

lemma resultant_comm {p q : R[X]} (p0 : p ≠ 0) (q0 : q ≠ 0) :
  resultant p q = (-1) ^ (p.nat_degree * q.nat_degree) * resultant q p := by
{ rw [resultant, resultant, resultant'_comm' ((not_iff_not_of_iff degree_eq_bot).mpr p0)
    ((not_iff_not_of_iff degree_eq_bot).mpr q0)],
  simp_rw [degree_eq_nat_degree p0, degree_eq_nat_degree q0, with_bot.unbot_coe], }

lemma resultant_mul_left [no_zero_divisors R] (p₁ p₂ q : R[X]) :
  resultant (p₁ * p₂) q = resultant p₁ q * resultant p₂ q := by
{ simp_rw [resultant, ← resultant'_mul_left, degree_le.mul, subtype.coe_mk],
  exact resultant'_congr' degree_mul rfl, }

lemma resultant_mul_right [no_zero_divisors R] (p q₁ q₂ : R[X]) :
  resultant p (q₁ * q₂) = resultant p q₁ * resultant p q₂ := by
{ simp_rw [resultant, ← resultant'_mul_right, degree_le.mul, subtype.coe_mk],
  exact resultant'_congr' rfl degree_mul, }

@[simps apply]
def resultant_left {R : Type*} [comm_ring R] [no_zero_divisors R]
  {q : R[X]} (q0 : q ≠ 0) : R[X] →*₀ R :=
{ to_fun    := λ p, resultant p q,
  map_zero' := resultant_zero_left q,
  map_one'  := resultant_one_left q0,
  map_mul'  := λ p₁ p₂, resultant_mul_left p₁ p₂ q, }

@[simps apply]
def resultant_right {R : Type*} [comm_ring R] [no_zero_divisors R]
  {p : R[X]} (p0 : p ≠ 0) : R[X] →*₀ R :=
{ to_fun    := λ q, resultant p q,
  map_zero' := resultant_zero_right p,
  map_one'  := resultant_one_right p0,
  map_mul'  := λ q₁ q₂, resultant_mul_right p q₁ q₂, }

lemma map_resultant_of_degree_map_eq (p q : R[X])
  (hp : p.degree = (p.map f).degree) (hq : q.degree = (q.map f).degree) :
  f (resultant p q) = resultant (p.map f) (q.map f) := by
{ rw [resultant, resultant, map_resultant'],
  exact resultant'_mk_congr hp hq (by rw [subtype.coe_mk]) (by rw [subtype.coe_mk]), }

lemma map_resultant_of_injective {f : R →+* S}
  (hf : function.injective f) (p q : R[X]) :
  f (resultant p q) = resultant (p.map f) (q.map f) :=
map_resultant_of_degree_map_eq f p q (degree_map_eq_of_injective hf p).symm
  (degree_map_eq_of_injective hf q).symm

lemma map_resultant_of_leading_coeff_ne_zero {f : R →+* S}
  (p q : R[X]) (hfp : f (leading_coeff p) ≠ 0) (hfq : f (leading_coeff q) ≠ 0) :
  f (resultant p q) = resultant (p.map f) (q.map f) :=
map_resultant_of_degree_map_eq f p q (degree_map_eq_of_leading_coeff_ne_zero f hfp).symm
  (degree_map_eq_of_leading_coeff_ne_zero f hfq).symm

lemma resultant_add_mul_left {R : Type*} [field R]
  {p q r : R[X]} (prq0 : p + r * q ≠ 0) (p0 : p ≠ 0) :
  resultant (p + r * q) q =
    q.leading_coeff ^ ((p + r * q).nat_degree - p.nat_degree : ℤ) * resultant p q := by
{ cases eq_or_ne r 0 with r0 r0, { rw [r0, zero_mul, add_zero, sub_self, zpow_zero, one_mul], },
  cases eq_or_ne q 0 with q0 q0, { simp_rw [q0, resultant_zero_right, mul_zero], },
  rw [resultant, resultant],
  have mem_degree_le_degree : ∀ {p : R[X]}, p ∈ degree_le R p.degree :=
    λ p, mem_degree_le.mpr le_rfl,
  have mem_degree_le_nat_degree : ∀ {p : R[X]}, p ∈ degree_le R p.nat_degree :=
    λ p, mem_degree_le.mpr degree_le_nat_degree,
  have h : ∀ {p q : R[X]} (p0 : p ≠ 0) (q0 : q ≠ 0),
    resultant' _ _ ⟨p, mem_degree_le_degree⟩ ⟨q, mem_degree_le_degree⟩ =
    resultant' _ _ ⟨p, mem_degree_le_nat_degree⟩ ⟨q, mem_degree_le_nat_degree⟩ :=
  λ p q p0 q0, resultant'_congr' (degree_eq_nat_degree p0) (degree_eq_nat_degree q0),
  rw [h prq0 q0, h p0 q0],
  have := @resultant'_add_mul_left _ _
    ((p + r * q).nat_degree + (p.nat_degree + (r.nat_degree + q.nat_degree)))
    q.nat_degree r.nat_degree (le_add_self.trans le_add_self) p q r
    (mem_degree_le.mpr (degree_le_nat_degree.trans (with_bot.coe_le_coe.mpr
      (le_self_add.trans le_add_self))))
    mem_degree_le_nat_degree mem_degree_le_nat_degree,
  rw [resultant'_shrink_left _ _ _ le_self_add _ _ mem_degree_le_nat_degree] at this,
  rw [resultant'_shrink_left _ _ _ _ _ _ (@mem_degree_le_nat_degree p)] at this, swap,
  { exact le_self_add.trans le_add_self, },
  rwa [subtype.coe_mk, mul_comm, ← eq_div_iff, mul_div_right_comm, ← zpow_coe_nat, ← zpow_coe_nat,
    ← zpow_sub₀, int.coe_nat_sub, int.coe_nat_sub, sub_sub_sub_cancel_left] at this,
  { exact le_self_add, }, { exact le_self_add.trans le_add_self, },
  swap, apply pow_ne_zero, any_goals { rwa [coeff_nat_degree, leading_coeff_ne_zero], }, }

lemma resultant_add_mul_left' {R : Type*} [field R]
  (p q r : R[X]) (n0 : q.degree ≠ 0) :
  resultant (p + r * q) q =
    q.leading_coeff ^ ((p + r * q).nat_degree - p.nat_degree : ℤ) * resultant p q := by
{ cases eq_or_ne r 0 with r0 r0, { rw [r0, zero_mul, add_zero, sub_self, zpow_zero, one_mul], },
  cases eq_or_ne q 0 with q0 q0, { simp_rw [q0, resultant_zero_right, mul_zero], },
  have n0' : 0 < q.nat_degree,
  { rwa [degree_eq_nat_degree q0, ← with_bot.coe_zero, ne.def, with_bot.coe_eq_coe, ← ne.def,
      ← pos_iff_ne_zero] at n0, },
  
  rw [resultant, resultant],
  have mem_degree_le_degree : ∀ {p : R[X]}, p ∈ degree_le R p.degree :=
    λ p, mem_degree_le.mpr le_rfl,
  have mem_degree_le_nat_degree : ∀ {p : R[X]}, p ∈ degree_le R p.nat_degree :=
    λ p, mem_degree_le.mpr degree_le_nat_degree,
  have := @resultant'_add_mul_left _ _
    ((p + r * q).nat_degree + (p.nat_degree + (r.nat_degree + q.nat_degree)))
    q.nat_degree r.nat_degree (le_add_self.trans le_add_self) p q r
    (mem_degree_le.mpr (degree_le_nat_degree.trans (with_bot.coe_le_coe.mpr
      (le_self_add.trans le_add_self))))
    mem_degree_le_nat_degree mem_degree_le_nat_degree,
  rw [resultant'_shrink_left _ _ _ le_self_add _ _ mem_degree_le_nat_degree] at this,
  rw [resultant'_shrink_left _ _ _ _ _ _ (@mem_degree_le_nat_degree p)] at this, swap,
  { exact le_self_add.trans le_add_self, },
  rw [subtype.coe_mk, mul_comm, ← eq_div_iff, mul_div_right_comm, ← zpow_coe_nat, ← zpow_coe_nat,
    ← zpow_sub₀, int.coe_nat_sub, int.coe_nat_sub, sub_sub_sub_cancel_left] at this,
  rotate 1, { exact le_self_add, }, { exact le_self_add.trans le_add_self, },
  swap, apply pow_ne_zero, any_goals { rwa [coeff_nat_degree, leading_coeff_ne_zero], },
  have h : ∀ {p q : R[X]} (p0 : p ≠ 0) (q0 : q ≠ 0),
    resultant' _ _ ⟨p, mem_degree_le_degree⟩ ⟨q, mem_degree_le_degree⟩ =
    resultant' _ _ ⟨p, mem_degree_le_nat_degree⟩ ⟨q, mem_degree_le_nat_degree⟩ :=
  λ p q p0 q0, resultant'_congr' (degree_eq_nat_degree p0) (degree_eq_nat_degree q0),
  
  cases eq_or_ne (p + r * q) 0 with prq0 prq0,
  { rw [prq0, resultant'_mk_congr' degree_zero rfl, resultant'_degree_le_bot_left],
    rw [prq0, resultant'_mk_congr' (with_bot.coe_eq_coe.mpr nat_degree_zero) rfl,
      resultant'_degree_le_coe_zero_left, subtype.coe_mk, coeff_zero, zero_pow n0'] at this,
    cases eq_or_ne p 0 with p0 p0,
    { rw [p0, zero_add] at prq0, exact absurd prq0 (mul_ne_zero r0 q0), },
    rw [h p0 q0], exact this, },
  rw [h prq0 q0],
  cases eq_or_ne p 0 with p0 p0,
  { rw [this, p0, submodule.mk_zero, resultant'_zero_left _ n0'], apply congr_arg,
    rw [resultant'_mk_congr' rfl (degree_eq_nat_degree q0), submodule.mk_zero,
      resultant'_zero_left _ n0'], },
  rw [h p0 q0], exact this, }

lemma resultant_sub_mul_left {R : Type*} [field R]
  {p q r : R[X]} (prq0 : p - r * q ≠ 0) (p0 : p ≠ 0) :
  resultant (p - r * q) q =
    q.leading_coeff ^ ((p - r * q).nat_degree - p.nat_degree : ℤ) * resultant p q :=
by { rw [sub_eq_add_neg, ← neg_mul] at *, exact resultant_add_mul_left prq0 p0, }

lemma resultant_sub_mul_left' {R : Type*} [field R]
  (p q r : R[X]) (n0 : q.degree ≠ 0) :
  resultant (p - r * q) q =
    q.leading_coeff ^ ((p - r * q).nat_degree - p.nat_degree : ℤ) * resultant p q :=
by { rw [sub_eq_add_neg, ← neg_mul] at *, exact resultant_add_mul_left' _ _ _ n0, }

private
lemma resultant_X_sub_C_right_field {R : Type*} [field R]
  (x : R) (p : R[X]) :
  resultant p (X - C x) = p.eval x := by
{ cases eq_or_ne p 0 with p0 p0, { rw [p0, resultant_zero_left, eval_zero], },
  conv_lhs { rw [← euclidean_domain.mod_add_div' p (X - C x)] },
  rw [resultant_add_mul_left'], swap, { rw [degree_X_sub_C], exact one_ne_zero },
  rw [euclidean_domain.mod_add_div', leading_coeff_X_sub_C, one_zpow, one_mul,
    mod_X_sub_C_eq_C_eval, resultant_C_left]; rw [nat_degree_X_sub_C],
  exacts [pow_one _, zero_lt_one], }

private
lemma resultant_X_sub_C_right_domain [is_domain R]
  (x : R) (p : R[X]) :
  resultant p (X - C x) = p.eval x := by
{ haveI := field (fraction_ring R),
  have hf := is_fraction_ring.injective R (fraction_ring R),
  apply hf,
  rw [map_resultant_of_injective hf, polynomial.map_sub, polynomial.map_X, polynomial.map_C,
    resultant_X_sub_C_right_field, eval_map, eval₂_hom], }

lemma resultant_X_sub_C_right (x : R) (p : R[X]) :
  resultant p (X - C x) = p.eval x := by
{ nontriviality R,
  let f : ∀ (p : R[X]), (mv_polynomial R ℤ)[X] :=
    λ p, p.sum (λ n x, C (mv_polynomial.X x) * X ^ n),
  have hf : resultant (f p) (X - C (mv_polynomial.X x)) = (f p).eval (mv_polynomial.X x) :=
  resultant_X_sub_C_right_domain _ _,
  let f' : mv_polynomial R ℤ →+* R := (mv_polynomial.aeval (λ x : R, x) : _ →ₐ[ℤ] _),
  have f'_X : ∀ (x : R), f' (mv_polynomial.X x) = x,
  { intro x, dsimp only [f', alg_hom.coe_to_ring_hom], rw [mv_polynomial.aeval_X], },
  have f_cancel : ∀ (p : R[X]), (f p).map f' = p,
  { intro p, dsimp only [f, sum_def],
    simp_rw [polynomial.map_sum, polynomial.map_mul, polynomial.map_pow, map_C, map_X,
      alg_hom.coe_to_ring_hom, mv_polynomial.aeval_X], rw [← as_sum_support_C_mul_X_pow], },
  replace hf := congr_arg f' hf,
  have h₁ : (f p).degree ≤ p.degree,
  { refine (degree_sum_le _ _).trans (finset.sup_le (λ b hb, _)), dsimp only,
    exact (degree_C_mul_X_pow_le _ _).trans (le_degree_of_mem_supp b hb), },
  have h₂ : ((f p).map f').degree ≤ (f p).degree := degree_map_le _ _,
  conv_rhs at h₁ { rw [← f_cancel p], },
  rw [map_resultant_of_degree_map_eq _ _ _ (antisymm h₁ h₂)] at hf,
  simp_rw [polynomial.map_sub, map_X, map_C, ← eval₂_hom, ← eval_map, f'_X, f_cancel] at hf,
  exact hf, simp_rw [polynomial.map_sub, map_X, map_C, degree_X_sub_C], }
