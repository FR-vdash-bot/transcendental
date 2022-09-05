/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import ring_theory.polynomial.vieta

open equiv (perm)
open_locale big_operators
noncomputable theory

namespace mv_polynomial

variables {σ : Type*} {R : Type*}
variables {τ : Type*} {S : Type*}
variables [comm_semiring R] [fintype σ]

lemma aeval_esymm [comm_semiring S] [algebra R S] (f : σ → S) (n : ℕ) :
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

variables (σ R)

def aeval_multiset [comm_semiring S] [algebra R S] (m : multiset S) :
  symmetric_subalgebra σ R →ₐ[R] S :=
(aeval (λ i : fin (fintype.card σ), m.esymm (i + 1))).comp (equiv_mv_polynomial σ R)

variables {σ R}

def aeval_multiset_map [comm_semiring S] [algebra R S] (f : σ → S)
  (p : symmetric_subalgebra σ R) :
  aeval_multiset σ R (multiset.map f finset.univ.val) p = aeval f (p : mv_polynomial σ R) :=
begin
  rw [aeval_multiset, alg_hom.comp_apply],
  /-
  have : aeval f ↑φ = aeval f ↑((equiv_mv_polynomial σ R).symm (equiv_mv_polynomial σ R p)),
  { rw [alg_equiv.symm_apply_apply], },
  rw [this, equiv_mv_polynomial_symm_apply],
  change _ = aeval f (algebra_map (symmetric_subalgebra σ R) (mv_polynomial σ R) _),
  haveI : is_scalar_tower R (symmetric_subalgebra σ R) (mv_polynomial σ R) :=
    subalgebra.is_scalar_tower_mid _,
  rw [map_aeval, ← is_scalar_tower.algebra_map_eq, coe_eval₂_hom, ← aeval_def],
  change _ = (aeval f).to_ring_hom
    (aeval (λ i : fin (fintype.card σ), esymm σ R (i + 1)) (equiv_mv_polynomial σ R p)),
  rw [map_aeval],-/
end
#check is_scalar_tower.algebra_map_eq
end symmetric_subalgebra

variables {σ R}

end mv_polynomial
