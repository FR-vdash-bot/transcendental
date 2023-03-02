
import field_theory.polynomial_galois_group

open polynomial
open_locale polynomial big_operators

namespace mul_action

@[to_additive]
instance (α : Type*) {β : Type*} [monoid α] [fintype α] [mul_action α β] [decidable_eq β] (b : β) :
  fintype (orbit α b) := set.fintype_range _

@[to_additive]
instance (α : Type*) {β : Type*} [group α] [fintype α] [mul_action α β] [decidable_eq β]
  (x : mul_action.orbit_rel.quotient α β) :
  fintype x.orbit :=
quotient.rec_on_subsingleton' x (λ a, set.fintype_range _)

end mul_action

namespace minpoly

lemma eq_of_alg_hom_eq {K S T : Type*} [field K] [ring S] [ring T]
  [algebra K S] [algebra K T]
  (f : S →ₐ[K] T) (hf : function.injective f)
  {x : S} {y : T} (hx : is_integral K x) (h : y = f x) :
  minpoly K x = minpoly K y :=
minpoly.unique _ _ (minpoly.monic hx)
  (by rw [h, aeval_alg_hom_apply, minpoly.aeval, alg_hom.map_zero])
  (λ q q_monic root_q, minpoly.min _ _ q_monic
    (by rwa [h, aeval_alg_hom_apply, map_eq_zero_iff _ hf] at root_q))

end minpoly

section heq
universes u₁ u₂ u₃

namespace fun_like

variables {F F' : Sort u₁} {α α' : Sort u₂} {β : α → Sort u₃} {β' : α' → Sort u₃}
  [i : fun_like F α β] [i' : fun_like F' α' β']

lemma ext_heq {f : F} {f' : F'}
  (h₁ : F = F') (h₂ : α = α') (h₃ : β == β') (h₄ : i == i')
  (h : ∀ x x', x == x' → f x == f' x') :
  f == f' := 
by { unfreezingI { cases h₁, cases h₂, cases h₃, cases h₄, },
  exact heq_of_eq (fun_like.ext f f' (λ x, eq_of_heq (h x x heq.rfl))), }

lemma congr_heq {f : F} {f' : F'} {x : α} {x' : α'}
  (h₁ : f == f') (h₂ : x == x') (h₃ : β == β') (h₄ : i == i') :
  f x == f' x' :=
by { unfreezingI { cases h₁, cases h₂, cases h₃, cases h₄, }, refl, }

end fun_like

universe u

lemma cast_heq' {α β α' : Sort u} (h : α = β) {a : α} {a' : α'} (h' : a == a') : cast h a == a' :=
by { cases h, cases h', refl, }

end heq

namespace alg_equiv
variables {R : Type*} [comm_semiring R] {A₁ A₂ : Type*}
variables [semiring A₁] [semiring A₂]
variables [algebra R A₁] [algebra R A₂]
variables (e : A₁ ≃ₐ[R] A₂)

lemma symm_apply_eq {x y} : e.symm x = y ↔ x = e y :=
e.to_equiv.symm_apply_eq

end alg_equiv

namespace intermediate_field

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] {α : E}

lemma adjoin_root_equiv_adjoin_symm_apply_gen (h : is_integral F α) :
  (adjoin_root_equiv_adjoin F h).symm (adjoin_simple.gen F α) =
    adjoin_root.root (minpoly F α) :=
by rw [alg_equiv.symm_apply_eq, adjoin_root_equiv_adjoin_apply_root]

end intermediate_field

namespace polynomial

variables {T : Type*} [comm_ring T]

noncomputable abbreviation aroots (p : T[X]) (S) [comm_ring S] [is_domain S] [algebra T S] : multiset S :=
(p.map (algebra_map T S)).roots

lemma aroots_def (p : T[X]) (S) [comm_ring S] [is_domain S] [algebra T S] :
  p.aroots S = (p.map (algebra_map T S)).roots := rfl

lemma aroots_map (p : T[X]) (S) (A) [comm_ring S] [is_domain S] [algebra T S]
  [comm_ring A] [is_domain A] [algebra S A] [algebra T A] [is_scalar_tower T S A] :
(p.map (algebra_map T S)).aroots A = p.aroots A :=
by rw [aroots_def, map_map, ← is_scalar_tower.algebra_map_eq T S A]

end polynomial



section gal_conj_classes
variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

def is_gal_conj.setoid := mul_action.orbit_rel (E ≃ₐ[F] E) E
def gal_conj_classes := mul_action.orbit_rel.quotient (E ≃ₐ[F] E) E

local attribute [instance] is_gal_conj.setoid

variable {E}

def is_gal_conj (x y : E) : Prop := (is_gal_conj.setoid F E).r x y

-- need to fix the precedence
notation (name := is_gal_conj) x ` ≈g[`:50 F `] ` y := is_gal_conj F x y

instance [decidable_eq E] [fintype (E ≃ₐ[F] E)] (x y : E) : decidable (x ≈g[F] y) :=
  fintype.decidable_exists_fintype

instance [decidable_eq E] [fintype (E ≃ₐ[F] E)] : decidable_eq (gal_conj_classes F E) :=
@quotient.decidable_eq _ (is_gal_conj.setoid F E) (is_gal_conj.decidable F)

namespace is_gal_conj

instance : is_equiv E (is_gal_conj F) := quotient.has_equiv.equiv.is_equiv

@[refl] lemma refl (x : E) : x ≈g[F] x := refl x
@[symm] lemma symm {x y : E} : (x ≈g[F] y) → (y ≈g[F] x) := symm
@[trans] lemma trans {x y z : E} : (x ≈g[F] y) → (y ≈g[F] z) → (x ≈g[F] z) := trans

end is_gal_conj

namespace gal_conj_classes

def mk (x : E) : gal_conj_classes F E := ⟦x⟧

instance : has_zero (gal_conj_classes F E) := ⟨mk F 0⟩

lemma zero_def : (0 : gal_conj_classes F E) = mk F 0 := rfl

variable {F}

noncomputable def out (c : gal_conj_classes F E) : E := c.out

@[simp] theorem eq {x y : E} : mk F x = mk F y ↔ x ≈g[F] y := quotient.eq
@[simp] theorem out_eq (q : gal_conj_classes F E) : mk F q.out = q := q.out_eq
theorem mk_out (x : E) : (mk F x).out ≈ x := quotient.mk_out x
lemma mk_eq_iff_out {x : E} {c : gal_conj_classes F E} :
  mk F x = c ↔ x ≈g[F] c.out := quotient.mk_eq_iff_out
lemma eq_mk_iff_out {c : gal_conj_classes F E} {x : E} :
  c = mk F x ↔ c.out ≈g[F] x := quotient.eq_mk_iff_out
@[simp] lemma out_equiv_out {c₁ c₂ : gal_conj_classes F E} :
  (c₁.out ≈g[F] c₂.out) ↔ c₁ = c₂ := @quotient.out_equiv_out _ _ c₁ c₂

lemma equiv_zero_iff (x : E) : (x ≈g[F] 0) ↔ x = 0 :=
begin
  refine ⟨λ h, _, λ h, by rw [h]⟩,
  cases h with a ha,
  simp_rw [← ha, alg_equiv.smul_def, map_zero],
end

lemma out_eq_zero_iff (c : gal_conj_classes F E) : c.out = 0 ↔ c = 0 :=
by rw [zero_def, eq_mk_iff_out, equiv_zero_iff]

lemma zero_out : (0 : gal_conj_classes F E).out = 0 :=
(out_eq_zero_iff 0).mpr rfl

lemma mk_eq_zero_iff (x : E) : mk F x = 0 ↔ x = 0 :=
by rw [mk_eq_iff_out, zero_out, equiv_zero_iff]

lemma mk_zero : mk F (0 : E) = 0 :=
(mk_eq_zero_iff 0).mpr rfl

def orbit (c : gal_conj_classes F E) : set E := c.orbit

instance [decidable_eq E] [fintype (E ≃ₐ[F] E)] (c : gal_conj_classes F E) :
  fintype c.orbit :=
quotient.rec_on_subsingleton' c (λ a, set.fintype_range _)

lemma mem_orbit {x : E} {c : gal_conj_classes F E} :
  x ∈ c.orbit ↔ mk F x = c := mul_action.orbit_rel.quotient.mem_orbit

lemma orbit_zero : (0 : gal_conj_classes F E).orbit = {0} :=
by { ext, rw [mem_orbit, mk_eq_zero_iff], refl, }

instance : has_neg (gal_conj_classes F E) :=
  ⟨quotient.lift (λ (x : E), mk F (-x)) begin
    rintros _ y ⟨f, rfl⟩, rw [eq],
    use f, change f (-y) = -f y, rw [alg_equiv.map_neg],
end⟩

lemma mk_neg (x : E) : mk F (-x) = -mk F x := rfl

instance : has_involutive_neg (gal_conj_classes F E) :=
{ neg_neg := λ x, by rw [← out_eq x, ← mk_neg, ← mk_neg, neg_neg],
  ..(infer_instance : has_neg (gal_conj_classes F E)), }

lemma exist_mem_orbit_add_eq_zero (x y : gal_conj_classes F E) :
  (∃ (a b : E), (a ∈ x.orbit ∧ b ∈ y.orbit) ∧ a + b = 0) ↔ x = -y :=
begin
  simp_rw [mem_orbit],
  split,
  { rintros ⟨a, b, ⟨rfl, rfl⟩, h⟩,
    rw [← mk_neg, eq, add_eq_zero_iff_eq_neg.mp h], },
  { rintro rfl,
    refine ⟨-y.out, y.out, _⟩,
    simp_rw [mk_neg, out_eq, neg_add_self, eq_self_iff_true, true_and], },
end

variable [is_separable F E]

noncomputable def minpoly : gal_conj_classes F E → F[X] :=
quotient.lift (minpoly F) (λ (a b : E) ⟨f, h⟩, minpoly.eq_of_alg_hom_eq
  f.symm.to_alg_hom f.symm.injective
  (is_separable.is_integral F a) (h ▸ (f.symm_apply_apply b).symm))

lemma minpoly_mk (x : E) : minpoly (mk F x) = _root_.minpoly F x := rfl

lemma minpoly_out (c : gal_conj_classes F E) : _root_.minpoly F c.out = minpoly c :=
by rw [← c.out_eq, minpoly_mk, c.out_eq]

lemma minpoly.monic (c : gal_conj_classes F E) : (minpoly c).monic :=
by { rw [← c.out_eq, minpoly_mk], exact minpoly.monic (is_separable.is_integral F _), }

lemma minpoly.ne_zero (c : gal_conj_classes F E) : minpoly c ≠ 0 :=
by { rw [← c.out_eq, minpoly_mk], exact minpoly.ne_zero (is_separable.is_integral F _), }

lemma minpoly.irreducible (c : gal_conj_classes F E) : irreducible (minpoly c) :=
by { rw [← c.out_eq, minpoly_mk], exact minpoly.irreducible (is_separable.is_integral F _), }

lemma minpoly.splits [n : normal F E] (c : gal_conj_classes F E) :
  splits (algebra_map F E) (minpoly c) :=
by { rw [← c.out_eq, minpoly_mk], exact n.splits c.out, }

lemma minpoly.separable (c : gal_conj_classes F E) : separable (minpoly c) :=
by { rw [← c.out_eq, minpoly_mk], exact is_separable.separable F c.out, }

lemma minpoly.inj [normal F E] {c d : gal_conj_classes F E} (h : minpoly c = minpoly d) : c = d :=
begin
  let fc := intermediate_field.adjoin_root_equiv_adjoin F (is_separable.is_integral F c.out),
  let fd := intermediate_field.adjoin_root_equiv_adjoin F (is_separable.is_integral F d.out),
  let congr_f : adjoin_root (_root_.minpoly F c.out) ≃ₐ[F] adjoin_root (_root_.minpoly F d.out),
  { rw [minpoly_out, minpoly_out, h], },
  have congr_f_apply : ∀ x, congr_f x == x,
  { intro x, change congr_f x == (alg_equiv.refl : _ ≃ₐ[F] _) x,
    dsimp only [congr_f],
    refine fun_like.congr_heq _ heq.rfl _ _,
    { simp_rw [eq_mpr_eq_cast, cast_cast],
      refine cast_heq' _ (fun_like.ext_heq _ _ _ _ _),
      any_goals { rw [minpoly_out, h], },
      rintros x₁ x₂ rfl, refl, },
    all_goals { rw [minpoly_out, minpoly_out, h], }, },
  let f' := fc.symm.trans (congr_f.trans fd),
  let f := f'.lift_normal E,
  rw [← out_equiv_out],
  refine ⟨f.symm, _⟩,
  dsimp only [f, alg_equiv.smul_def],
  simp_rw [alg_equiv.symm_apply_eq, ← intermediate_field.adjoin_simple.algebra_map_gen F c.out,
    ← intermediate_field.adjoin_simple.algebra_map_gen F d.out, alg_equiv.lift_normal_commutes],
  apply congr_arg,
  simp_rw [f', alg_equiv.trans_apply, ← fd.symm_apply_eq, fc, fd,
    intermediate_field.adjoin_root_equiv_adjoin_symm_apply_gen],
  refine eq_of_heq (heq.trans _ (congr_f_apply _).symm),
  rw [minpoly_out, minpoly_out, h],
end

lemma minpoly.injective [normal F E] : function.injective (@minpoly F _ E _ _ _) :=
λ x y, minpoly.inj

lemma minpoly.nodup_aroots (c : gal_conj_classes F E) :
  ((minpoly c).aroots E).nodup :=
nodup_roots (minpoly.separable c).map

lemma aeval_minpoly_iff [normal F E] (x : E) (c : gal_conj_classes F E) :
  aeval x (minpoly c) = 0 ↔ mk F x = c :=
begin
  symmetry, split, { rintros rfl, exact minpoly.aeval _ _, },
  intros h,
  apply minpoly.inj,
  rw [minpoly_mk, ← minpoly.eq_of_irreducible (minpoly.irreducible c) h],
  rw [(minpoly.monic c).leading_coeff, inv_one, map_one, mul_one],
end

lemma root_set_minpoly_eq_orbit [normal F E] (c : gal_conj_classes F E) :
  (minpoly c).root_set E = c.orbit :=
begin
  ext x, rw [mem_orbit],
  simp_rw [mem_root_set, aeval_minpoly_iff x c],
  simp [minpoly.ne_zero c],
end

lemma aroots_minpoly_eq_orbit_val [decidable_eq E] [fintype (E ≃ₐ[F] E)] [normal F E]
  (c : gal_conj_classes F E) : (minpoly c).aroots E = c.orbit.to_finset.1 :=
begin
  simp_rw [← root_set_minpoly_eq_orbit, root_set_def, finset.to_finset_coe,
    multiset.to_finset_val], symmetry, rw [multiset.dedup_eq_self],
  exact nodup_roots ((separable_map _).mpr (minpoly.separable c)),
end

lemma orbit_eq_mk_aroots_minpoly [decidable_eq E] [fintype (E ≃ₐ[F] E)] [normal F E]
  (c : gal_conj_classes F E) :
  c.orbit.to_finset = ⟨(minpoly c).aroots E, minpoly.nodup_aroots c⟩ :=
by simpa only [aroots_minpoly_eq_orbit_val]

lemma minpoly.map_eq_prod [decidable_eq E] [fintype (E ≃ₐ[F] E)] [normal F E]
  (c : gal_conj_classes F E) :
  (minpoly c).map (algebra_map F E) = ∏ x in c.orbit.to_finset, (X - C x) :=
begin
  simp_rw [← root_set_minpoly_eq_orbit, finset.prod_eq_multiset_prod, root_set_def,
    finset.to_finset_coe, multiset.to_finset_val],
  rw [multiset.dedup_eq_self.mpr (nodup_roots _),
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (monic.map _ _)],
  { rw [splits_iff_card_roots.mp], rw [splits_id_iff_splits], exact minpoly.splits c, },
  { exact minpoly.monic c, },
  { exact (minpoly.separable c).map, },
end
/-
def class_of_roots_irreducible
  {q : F[X]} (q_splits : q.splits (algebra_map F E))
  (hq : _root_.irreducible q) : gal_conj_classes F E :=
⟦root_of_splits (algebra_map F E) q_splits (degree_pos_of_irreducible hq).ne'⟧

lemma minpoly_class_of_roots_irreducible_of_monic
  {q : F[X]} (q_splits : splits (algebra_map F E) q)
  (hq : _root_.irreducible q) (q_monic : q.monic) :
  (class_of_roots_irreducible q_splits hq).minpoly = q :=
begin
  dsimp only [class_of_roots_irreducible], rw [minpoly_mk],
  exact (minpoly.eq_of_irreducible_of_monic hq (map_root_of_splits _ _ _) q_monic).symm,
end

lemma minpoly_class_of_roots_irreducible
  {q : F[X]} (q_splits : splits (algebra_map F E) q)
  (hq : _root_.irreducible q) :
  (class_of_roots_irreducible q_splits hq).minpoly = q * C q.leading_coeff⁻¹ :=
begin
  dsimp only [class_of_roots_irreducible], rw [minpoly_mk],
  exact (minpoly.eq_of_irreducible hq (map_root_of_splits _ _ _)).symm,
end

lemma class_of_roots_irreducible_minpoly (c : gal_conj_classes F E)
  (h₁ : c.minpoly.splits (algebra_map F E)) (h₂ : irreducible c.minpoly) :
  class_of_roots_irreducible h₁ h₂ = c :=
begin
  dsimp only [class_of_roots_irreducible], apply minpoly.inj, rw [minpoly_mk],
  exact minpoly_class_of_roots_irreducible_of_monic _ _ (minpoly.monic c),
end

lemma root_set_C_mul (q : F[X]) {a : F} (a0 : a ≠ 0) :
  q.root_set E = (C a * q).root_set E :=
by { simp_rw [root_set, map_mul, map_C,
  roots_C_mul _ (((algebra_map F E).map_ne_zero).mpr a0)], }

lemma root_set_mul_C (q : F[X]) {a : F} (a0 : a ≠ 0) :
  q.root_set E = (q * C a).root_set E :=
by { rw [mul_comm], exact root_set_C_mul q a0, }

lemma root_set_eq_orbit {q : F[X]} (q_splits : splits (algebra_map F E) q)
  (hq : _root_.irreducible q) :
  q.root_set E = (class_of_roots_irreducible q_splits hq).orbit :=
begin
  rw [← root_set_minpoly_eq_orbit, minpoly_class_of_roots_irreducible, root_set_mul_C],
  exact inv_ne_zero (leading_coeff_ne_zero.mpr hq.ne_zero),
end

lemma aroots_eq_orbit {q : F[X]} (q_splits : splits (algebra_map F E) q)
  (hq : _root_.irreducible q) :
  q.aroots E =
    (class_of_roots_irreducible q_splits hq).orbit.to_finset.1 :=
begin
  simp_rw [← root_set_eq_orbit q_splits hq, root_set_def, to_finset_coe,
    multiset.to_finset_val], symmetry, rw [multiset.dedup_eq_self],
  exact nodup_roots ((separable_map _).mpr hq.separable),
end

def classes_of_roots {q : F[X]} (q_splits : q.splits (algebra_map F E)) :
  multiset (gal_conj_classes F E) :=
(unique_factorization_monoid.normalized_factors q).pmap
  (λ (q : F[X]) (hq : q.splits (algebra_map F E) ∧ irreducible q),
    class_of_roots_irreducible hq.1 hq.2)
  (λ d hd,
  begin
    refine ⟨_, unique_factorization_monoid.irreducible_of_normalized_factor _ hd⟩,
    have d_dvd_q := unique_factorization_monoid.dvd_of_mem_normalized_factors hd,
    refine splits_of_splits_of_dvd _ _ q_splits d_dvd_q,
    rintros rfl, simpa [unique_factorization_monoid.normalized_factors_zero] using hd,
  end)

section

open list multiset

variables {α : Type*} {β : Type*} {γ : Type*}

variables (a : α) (s t : multiset α) (f g : α → multiset β)

namespace multiset

theorem pmap_congr' {p q : α → Prop} {f : Π a, p a → β} {g : Π a, q a → β}
  (s : multiset α) {H₁ H₂} :
  (∀ (a ∈ s) h₁ h₂, f a h₁ = g a h₂) → pmap f s H₁ = pmap g s H₂ := sorry

lemma count_dedup (m : multiset α) (a : α) :
  m.dedup.count a = if a ∈ m then 1 else 0 :=
by { rcases m, simp [count_dedup], }

@[simp]
lemma dedup_bind_dedup (m : multiset α) (f : α → multiset γ) :
  (m.dedup.bind f).dedup = (m.bind f).dedup :=
by { ext x, simp_rw [count_dedup, multiset.mem_bind, multiset.mem_dedup], }

@[simp]
lemma dedup_dedup (m : multiset α) :
  m.dedup.dedup = m.dedup :=
by { ext x, simp_rw [count_dedup, multiset.mem_dedup], }

@[simp]
lemma to_finset_dedup (m : multiset α) :
  m.dedup.to_finset = m.to_finset :=
by simp_rw [multiset.to_finset, dedup_dedup]

@[simp]
lemma to_finset_bind_dedup (m : multiset α) (f : α → multiset γ) :
  (m.dedup.bind f).to_finset = (m.bind f).to_finset :=
by simp_rw [multiset.to_finset, dedup_bind_dedup]

end multiset

end

lemma classes_of_roots_zero :
  classes_of_roots (splits_zero (algebra_map F E)) = 0 :=
by simp_rw [classes_of_roots, unique_factorization_monoid.normalized_factors_zero,
  multiset.pmap_zero]

section
/-
`monic_normalize` caused following instance defeq problem:
`(λ (a b : F), classical.prop_decidable (a = b)) = (λ (a b : F), rat.decidable_eq a b)`
`classical.prop_decidable` is in `monic_normalize`
-/
lemma monic_normalize' {K : Type*} [field K] [decidable_eq K] {p : K[X]}
  (hp0 : p ≠ 0) : monic (normalize p) :=
begin
  rw [ne.def, ← leading_coeff_eq_zero, ← ne.def, ← is_unit_iff_ne_zero] at hp0,
  rw [monic, leading_coeff_normalize, normalize_eq_one],
  apply hp0,
end

variables {α : Type*}
local infix ` ~ᵤ ` : 50 := associated
variables [cancel_comm_monoid_with_zero α] [decidable_eq α] [normalization_monoid α]
variables [unique_factorization_monoid α]

open unique_factorization_monoid
namespace unique_factorization_monoid

lemma associated_iff_normalized_factors_eq_normalized_factors {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
  x ~ᵤ y ↔ normalized_factors x = normalized_factors y :=
begin
  split,
  { intro h,
    apply le_antisymm; rw [← dvd_iff_normalized_factors_le_normalized_factors],
    all_goals { simp [*, h.dvd, h.symm.dvd], }, },
  { intro h,
    apply associated_of_dvd_dvd; rw [dvd_iff_normalized_factors_le_normalized_factors],
    all_goals { simp [*, h.le, h.ge], }, },
end

end unique_factorization_monoid

end

lemma prod_classes_of_roots_map_minpoly_of_monic
  {q : F[X]} (q_splits : splits (algebra_map F E) q) (q0 : q ≠ 0)
  (q_monic : q.monic) :
  ((classes_of_roots q_splits).map (λ c, minpoly c)).prod = q :=
begin
  simp_rw [classes_of_roots, multiset.map_pmap],
  suffices :
    (multiset.pmap (λ (q : F[X]) (h : q.splits (algebra_map F E) ∧ irreducible q),
      q) (unique_factorization_monoid.normalized_factors q) _).prod = q,
  { refine eq.trans _ this, swap, congr' 1,
    rw [(λ _ _ _ _ _, iff.rfl : ∀ {α β} {f g : α → β} (a : α), f a = g a ↔ f a = g a)], -- hack
    -- I wonder if there is a better method
    refine multiset.pmap_congr' _ (λ d hd _ _, minpoly_class_of_roots_irreducible_of_monic _ _ _),
    swap, rw [← unique_factorization_monoid.normalize_normalized_factor _ hd],
    have : d ≠ 0 := (unique_factorization_monoid.irreducible_of_normalized_factor _ hd).ne_zero,
    exact monic_normalize' this, },
  rw [multiset.pmap_eq_map, multiset.map_id'],
  refine eq_of_monic_of_associated _ q_monic
    (unique_factorization_monoid.normalized_factors_prod q0),
  refine monic_multiset_prod_of_monic _ _ (λ d hd, monic_normalize' _),
  exact (unique_factorization_monoid.irreducible_of_factor _ hd).ne_zero,
end

lemma prod_classes_of_roots_map_minpoly
  {q : F[X]} (q_splits : splits (algebra_map F E) q) (q0 : q ≠ 0) :
  ((classes_of_roots q_splits).map (λ c, minpoly c)).prod = q * C q.leading_coeff⁻¹ :=
begin
  rw [← @prod_classes_of_roots_map_minpoly_of_monic p (q * C q.leading_coeff⁻¹)], rotate 1,
  { exact splits_mul _ q_splits (splits_C _ _), },
  { refine mul_ne_zero q0 _, rwa [ne.def, C_eq_zero, inv_eq_zero, leading_coeff_eq_zero], },
  { exact monic_mul_leading_coeff_inv q0, },
  congr' 2, dsimp only [classes_of_roots],
  have l0 := inv_ne_zero (leading_coeff_ne_zero.mpr q0),
  have ql0 := mul_ne_zero q0 (C_eq_zero.not.mpr l0),
  have : associated q (q * C q.leading_coeff⁻¹),
  { refine associated_mul_unit_right _ _ _,
    rwa [is_unit_C, is_unit_iff_ne_zero], },
  simp_rw [(unique_factorization_monoid.associated_iff_normalized_factors_eq_normalized_factors
    q0 ql0).mp this],
end

lemma leading_coeff_mul_prod_classes_of_roots_map_minpoly
  {q : F[X]} (q_splits : splits (algebra_map F E) q) :
  C q.leading_coeff * ((classes_of_roots q_splits).map (λ c, minpoly c)).prod = q :=
begin
  rcases eq_or_ne q 0 with rfl | q0, { rw [leading_coeff_zero, C_0, zero_mul], },
  rw [prod_classes_of_roots_map_minpoly q_splits q0, mul_left_comm, ← C_mul, mul_inv_cancel,
    C_1, mul_one],
  exact leading_coeff_ne_zero.mpr q0,
end

lemma aroots_eq_classes_of_roots_bind_orbit
  {q : F[X]} (q_splits : splits (algebra_map F E) q) :
  q.aroots E =
    (classes_of_roots q_splits).bind (λ c, c.orbit.to_finset.1) :=
begin
  rcases eq_or_ne q 0 with rfl | q0,
  { rw [classes_of_roots_zero, multiset.zero_bind, map_zero, roots_zero], },
  conv_lhs { rw [← leading_coeff_mul_prod_classes_of_roots_map_minpoly q_splits], },
  rw [map_mul, map_multiset_prod, map_C, roots_C_mul, roots_multiset_prod,
    multiset.bind_map, multiset.bind_map],
  simp_rw [roots_minpoly_eq_orbit_val],
  { intros h, simp_rw [multiset.mem_map] at h,
    obtain ⟨_, ⟨⟨y, _, rfl⟩, h⟩⟩ := h,
    rw [map_eq_zero] at h,
    exact minpoly.ne_zero y h, },
  { rwa [ring_hom.map_ne_zero, leading_coeff_ne_zero], },
end

lemma root_set_eq_classes_of_roots_bUnion_orbit
  {q : F[X]} (q_splits : splits (algebra_map F E) q) :
  q.root_set E =
    ⋃ c ∈ ((classes_of_roots q_splits).to_finset : set (gal_conj_classes F E)), (c : _).orbit :=
begin
  refine eq.trans _ (eq.trans
    (congr_arg (λ (m : multiset E), (m.to_finset : set E))
    (roots_eq_classes_of_roots_bind_orbit q_splits)) _),
  { exact root_set_def _ _, },
  convert_to _ = ⋃ (c : gal_conj_classes F E) (H : c ∈ ↑((classes_of_roots q_splits).to_finset)),
    (c.orbit.to_finset : set E),
  { simp_rw [set.coe_to_finset], },
  rw [← coe_bUnion, finset.bUnion, finset.coe_inj, multiset.to_finset_val],
  convert (multiset.to_finset_bind_dedup _ _).symm,
end
-/

end gal_conj_classes

end gal_conj_classes