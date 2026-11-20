import Mathlib

open TensorProduct

noncomputable section

namespace GlobalTheory

abbrev AugCot {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R) : Type _ := sorry


namespace AugCot

section Basic

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R)

def projKer : A →ₗ[R] RingHom.ker ε := sorry




@[simp] lemma coe_projKer (a : A) : (projKer ε a : A) = a - algebraMap R A (ε a) := by sorry

@[simp] lemma projKer_coe (x : RingHom.ker ε) : projKer ε x = x := by sorry



def d : A →ₗ[R] AugCot ε := sorry


lemma d_apply (a : A) : d ε a = (RingHom.ker ε).toCotangent (projKer ε a) := by sorry

@[simp] lemma d_coe (x : RingHom.ker ε) : d ε x = (RingHom.ker ε).toCotangent x := by sorry


lemma d_of_mem {a : A} (ha : a ∈ RingHom.ker ε) :
    d ε a = (RingHom.ker ε).toCotangent ⟨a, ha⟩ := by sorry

lemma d_surjective : Function.Surjective (d ε) := by sorry




lemma d_eq_zero_iff (a : A) : d ε a = 0 ↔ a - algebraMap R A (ε a) ∈ RingHom.ker ε ^ 2 := by sorry


@[simp] lemma d_algebraMap (r : R) : d ε (algebraMap R A r) = 0 := by sorry


@[simp] lemma d_one : d ε 1 = 0 := by sorry


lemma smul_eq (a : A) (x : AugCot ε) : a • x = ε a • x := by sorry




lemma d_mul (a b : A) : d ε (a * b) = ε a • d ε b + ε b • d ε a := by sorry










variable {N : Type*} [AddCommGroup N] [Module R N]

variable {ε} in

lemma hom_ext {f g : AugCot ε →ₗ[R] N} (h : ∀ a, f (d ε a) = g (d ε a)) : f = g := by sorry




variable (N) in

def pointDer : Submodule R (A →ₗ[R] N) where
  carrier := sorry






variable {ε} in
lemma mem_pointDer {D : A →ₗ[R] N} :
    D ∈ pointDer ε N ↔ ∀ a b, D (a * b) = ε a • D b + ε b • D a := by sorry

variable {ε} in
lemma pointDer_algebraMap {D : A →ₗ[R] N} (hD : ∀ a b, D (a * b) = ε a • D b + ε b • D a)
    (r : R) : D (algebraMap R A r) = 0 := by sorry





def lift (D : A →ₗ[R] N) (hD : ∀ a b, D (a * b) = ε a • D b + ε b • D a) : AugCot ε →ₗ[R] N := sorry






@[simp] lemma lift_toCotangent (D : A →ₗ[R] N) (hD : ∀ a b, D (a * b) = ε a • D b + ε b • D a)
    (x : RingHom.ker ε) : lift ε D hD ((RingHom.ker ε).toCotangent x) = D x := by sorry

@[simp] lemma lift_d (D : A →ₗ[R] N) (hD : ∀ a b, D (a * b) = ε a • D b + ε b • D a) (a : A) :
    lift ε D hD (d ε a) = D a := by sorry


variable (N) in

def pointDerEquiv : pointDer ε N ≃ₗ[R] (AugCot ε →ₗ[R] N) where
  toFun D := sorry






@[simp] lemma pointDerEquiv_d (D : pointDer ε N) (a : A) :
    pointDerEquiv ε N D (d ε a) = D.1 a := by sorry

@[simp] lemma pointDerEquiv_symm_apply (f : AugCot ε →ₗ[R] N) (a : A) :
    ((pointDerEquiv ε N).symm f).1 a = f (d ε a) := by sorry

def derivationEquiv [Module A N] [IsScalarTower R A N] (h : ∀ (a : A) (n : N), a • n = ε a • n) :
    Derivation R A N ≃ₗ[R] (AugCot ε →ₗ[R] N) where
  toFun D := sorry






@[simp] lemma derivationEquiv_d [Module A N] [IsScalarTower R A N]
    (h : ∀ (a : A) (n : N), a • n = ε a • n) (D : Derivation R A N) (a : A) :
    derivationEquiv ε h D (d ε a) = D a := by sorry

@[simp] lemma derivationEquiv_symm_apply [Module A N] [IsScalarTower R A N]
    (h : ∀ (a : A) (n : N), a • n = ε a • n) (f : AugCot ε →ₗ[R] N) (a : A) :
    (derivationEquiv ε h).symm f a = f (d ε a) := by sorry

lemma isScalarTower_of_smul_eq [Module A N] (h : ∀ (a : A) (n : N), a • n = ε a • n) :
    IsScalarTower R A N := by sorry


def derivation : Derivation R A (AugCot ε) := sorry


@[simp] lemma derivation_apply (a : A) : derivation ε a = d ε a := by sorry

section Kaehler

variable [Algebra A R] (h : ∀ a, algebraMap A R a = ε a)

include h in
lemma isScalarTower_of_algebraMap_eq : IsScalarTower A R (AugCot ε) := by sorry


include h in
lemma isScalarTower_base : IsScalarTower R A R := by sorry


def toKaehler : AugCot ε →ₗ[R] R ⊗[A] Ω[A⁄R] := sorry





@[simp] lemma toKaehler_d (a : A) :
    toKaehler ε h (d ε a) = 1 ⊗ₜ KaehlerDifferential.D R A a := by sorry

def ofKaehler : Ω[A⁄R] →ₗ[A] AugCot ε := sorry

omit [Algebra A R] in
@[simp] lemma ofKaehler_D (a : A) : ofKaehler ε (KaehlerDifferential.D R A a) = d ε a := by sorry


lemma toKaehler_ofKaehler (m : Ω[A⁄R]) : toKaehler ε h (ofKaehler ε m) = 1 ⊗ₜ m := by sorry











def kaehlerEquiv : AugCot ε ≃ₗ[R] R ⊗[A] Ω[A⁄R] := sorry










@[simp] lemma kaehlerEquiv_d (a : A) :
    kaehlerEquiv ε h (d ε a) = 1 ⊗ₜ KaehlerDifferential.D R A a := by sorry

@[simp] lemma kaehlerEquiv_symm_tmul (r : R) (m : Ω[A⁄R]) :
    (kaehlerEquiv ε h).symm (r ⊗ₜ m) = r • ofKaehler ε m := by sorry




lemma isBaseChange_ofKaehler :
    haveI := by sorry




end Kaehler

section SqZero

variable [Module Rᵐᵒᵖ N] [IsCentralScalar R N]

def toSqZero (f : AugCot ε →ₗ[R] N) : A →ₐ[R] TrivSqZeroExt R N := sorry






@[simp] lemma fst_toSqZero (f : AugCot ε →ₗ[R] N) (a : A) : (toSqZero ε f a).fst = ε a := by sorry


@[simp] lemma snd_toSqZero (f : AugCot ε →ₗ[R] N) (a : A) :
    (toSqZero ε f a).snd = f (d ε a) := by sorry


def ofSqZero (φ : A →ₐ[R] TrivSqZeroExt R N) (hφ : ∀ a, (φ a).fst = ε a) : AugCot ε →ₗ[R] N := sorry


@[simp] lemma ofSqZero_d (φ : A →ₐ[R] TrivSqZeroExt R N) (hφ : ∀ a, (φ a).fst = ε a) (a : A) :
    ofSqZero ε φ hφ (d ε a) = (φ a).snd := by sorry

variable (N) in

def sqZeroEquiv :
    {φ : A →ₐ[R] TrivSqZeroExt R N // (TrivSqZeroExt.fstHom R R N).comp φ = ε} ≃
      (AugCot ε →ₗ[R] N) where
  toFun φ := sorry









@[simp] lemma sqZeroEquiv_d
    (φ : {φ : A →ₐ[R] TrivSqZeroExt R N // (TrivSqZeroExt.fstHom R R N).comp φ = ε}) (a : A) :
    sqZeroEquiv ε N φ (d ε a) = (φ.1 a).snd := by sorry


@[simp] lemma sqZeroEquiv_symm_apply (f : AugCot ε →ₗ[R] N) :
    ((sqZeroEquiv ε N).symm f).1 = toSqZero ε f := by sorry

end SqZero

end Basic

section Map

variable {R A B C : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [CommRing C] [Algebra R C] {εA : A →ₐ[R] R} {εB : B →ₐ[R] R} {εC : C →ₐ[R] R}

lemma ker_eq_comap (φ : A →ₐ[R] B) (h : εB.comp φ = εA) :
    RingHom.ker εA = (RingHom.ker εB).comap φ := by sorry


def map (φ : A →ₐ[R] B) (h : εB.comp φ = εA) : AugCot εA →ₗ[R] AugCot εB := sorry


@[simp] lemma map_toCotangent (φ : A →ₐ[R] B) (h : εB.comp φ = εA) (x : RingHom.ker εA) :
    map φ h ((RingHom.ker εA).toCotangent x) =
      (RingHom.ker εB).toCotangent ⟨φ x, (ker_eq_comap φ h).le x.2⟩ := by sorry

@[simp] lemma map_d (φ : A →ₐ[R] B) (h : εB.comp φ = εA) (a : A) :
    map φ h (d εA a) = d εB (φ a) := by sorry





@[simp] lemma map_id : map (AlgHom.id R A) (AlgHom.comp_id εA) = LinearMap.id := by sorry


lemma map_comp (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) (h : εB.comp φ = εA) (h' : εC.comp ψ = εB)
    (h'' : εC.comp (ψ.comp φ) = εA := by rw [← AlgHom.comp_assoc, h', h]) :
    map (ψ.comp φ) h'' = map ψ h' ∘ₗ map φ h := by sorry


def congr (e : A ≃ₐ[R] B) (h : εB.comp e = εA) : AugCot εA ≃ₗ[R] AugCot εB := sorry




@[simp] lemma congr_d (e : A ≃ₐ[R] B) (h : εB.comp e = εA) (a : A) :
    congr e h (d εA a) = d εB (e a) := by sorry

@[simp] lemma congr_symm_d (e : A ≃ₐ[R] B) (h : εB.comp e = εA) (b : B) :
    (congr e h).symm (d εB b) = d εA (e.symm b) := by sorry


lemma map_ofKaehler [Algebra A B] [IsScalarTower R A B]
    (h : εB.comp (IsScalarTower.toAlgHom R A B) = εA) (m : Ω[A⁄R]) :
    map _ h (ofKaehler εA m) = ofKaehler εB (KaehlerDifferential.map R R A B m) := by sorry










lemma map_surjective (φ : A →ₐ[R] B) (h : εB.comp φ = εA) (hφ : Function.Surjective φ) :
    Function.Surjective (map φ h) := by sorry





lemma ker_le (φ : A →ₐ[R] B) (h : εB.comp φ = εA) : RingHom.ker φ ≤ RingHom.ker εA := by sorry




def kerMap (φ : A →ₐ[R] B) (h : εB.comp φ = εA) : RingHom.ker φ →ₗ[R] AugCot εA := sorry


@[simp] lemma kerMap_apply (φ : A →ₐ[R] B) (h : εB.comp φ = εA) (x : RingHom.ker φ) :
    kerMap φ h x = d εA x := by sorry

lemma exact_kerMap_map (φ : A →ₐ[R] B) (h : εB.comp φ = εA) (hφ : Function.Surjective φ) :
    Function.Exact (kerMap φ h) (map φ h) := by sorry


















lemma isNilpotent_ker_fst (N : Type*) [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N]
    [IsCentralScalar R N] :
    IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom R R N : TrivSqZeroExt R N →+* R)) := by sorry








lemma exists_leftInverse_map (φ : A →ₐ[R] B) (h : εB.comp φ = εA)
    (hφ : (φ : A →+* B).FormallySmooth) :
    ∃ s : AugCot εB →ₗ[R] AugCot εA, s ∘ₗ map φ h = LinearMap.id := by sorry



























lemma map_injective_of_formallySmooth (φ : A →ₐ[R] B) (h : εB.comp φ = εA)
    (hφ : (φ : A →+* B).FormallySmooth) : Function.Injective (map φ h) := by sorry



lemma map_surjective_of_formallyUnramified (φ : A →ₐ[R] B) (h : εB.comp φ = εA)
    (hφ : (φ : A →+* B).FormallyUnramified) : Function.Surjective (map φ h) := by sorry
































lemma map_bijective_of_formallyEtale (φ : A →ₐ[R] B) (h : εB.comp φ = εA)
    (hφ : (φ : A →+* B).FormallyEtale) : Function.Bijective (map φ h) := by sorry






lemma map_bijective_of_etale (φ : A →ₐ[R] B) (h : εB.comp φ = εA)
    (hφ : (φ : A →+* B).Etale) : Function.Bijective (map φ h) := by sorry




section Tower

variable [Algebra A B] [IsScalarTower R A B]

lemma map_bijective [Algebra.FormallyEtale A B]
    (h : εB.comp (IsScalarTower.toAlgHom R A B) = εA) : Function.Bijective (map _ h) := by sorry


def etaleEquiv [Algebra.FormallyEtale A B] (h : εB.comp (IsScalarTower.toAlgHom R A B) = εA) :
    AugCot εA ≃ₗ[R] AugCot εB := sorry

@[simp] lemma etaleEquiv_d [Algebra.FormallyEtale A B]
    (h : εB.comp (IsScalarTower.toAlgHom R A B) = εA) (a : A) :
    etaleEquiv h (d εA a) = d εB (algebraMap A B a) := by sorry

lemma map_bijective_of_isLocalization (M : Submonoid A) [IsLocalization M B]
    (h : εB.comp (IsScalarTower.toAlgHom R A B) = εA) : Function.Bijective (map _ h) := by sorry



variable (εA B) in

def locAug (M : Submonoid A) [IsLocalization M B] (hM : ∀ m : M, IsUnit (εA m)) : B →ₐ[R] R := sorry


lemma locAug_comp (M : Submonoid A) [IsLocalization M B] (hM : ∀ m : M, IsUnit (εA m)) :
    (locAug B εA M hM).comp (IsScalarTower.toAlgHom R A B) = εA := by sorry


variable (εA B) in

def locEquiv (M : Submonoid A) [IsLocalization M B] (hM : ∀ m : M, IsUnit (εA m)) :
    AugCot εA ≃ₗ[R] AugCot (locAug B εA M hM) := sorry


@[simp] lemma locEquiv_d (M : Submonoid A) [IsLocalization M B] (hM : ∀ m : M, IsUnit (εA m))
    (a : A) : locEquiv B εA M hM (d εA a) = d _ (algebraMap A B a) := by sorry


variable (εA B) in

def awayAug (f : A) [IsLocalization.Away f B] (hf : IsUnit (εA f)) : B →ₐ[R] R := sorry


lemma awayAug_comp (f : A) [IsLocalization.Away f B] (hf : IsUnit (εA f)) :
    (awayAug B εA f hf).comp (IsScalarTower.toAlgHom R A B) = εA := by sorry

variable (εA B) in

def awayEquiv (f : A) [IsLocalization.Away f B] (hf : IsUnit (εA f)) :
    AugCot εA ≃ₗ[R] AugCot (awayAug B εA f hf) := sorry

@[simp] lemma awayEquiv_d (f : A) [IsLocalization.Away f B] (hf : IsUnit (εA f)) (a : A) :
    awayEquiv B εA f hf (d εA a) = d _ (algebraMap A B a) := by sorry

end Tower

variable (εA εB) in

abbrev tensorAug : A ⊗[R] B →ₐ[R] R := sorry

lemma tensorAug_comp_includeLeft :
    (tensorAug εA εB).comp Algebra.TensorProduct.includeLeft = εA := by sorry


lemma tensorAug_comp_includeRight :
    (tensorAug εA εB).comp Algebra.TensorProduct.includeRight = εB := by sorry


lemma d_tmul (a : A) (b : B) : d (tensorAug εA εB) (a ⊗ₜ b) =
    εB b • d (tensorAug εA εB) (a ⊗ₜ 1) + εA a • d (tensorAug εA εB) (1 ⊗ₜ b) := by sorry




variable (εA εB) in

def tensorEquiv : AugCot (tensorAug εA εB) ≃ₗ[R] AugCot εA × AugCot εB := sorry















@[simp] lemma tensorEquiv_symm_apply (x : AugCot εA) (y : AugCot εB) :
    (tensorEquiv εA εB).symm (x, y) =
      map _ tensorAug_comp_includeLeft x + map _ tensorAug_comp_includeRight y := by sorry

@[simp] lemma tensorEquiv_d_tmul (a : A) (b : B) :
    tensorEquiv εA εB (d _ (a ⊗ₜ b)) = (εB b • d εA a, εA a • d εB b) := by sorry



end Map

section BaseChange

variable {R R' A A' : Type*} [CommRing R] [CommRing R'] [CommRing A] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra R A'] [IsScalarTower R R' A']
  {ε : A →ₐ[R] R} {ε' : A' →ₐ[R'] R'}

def mapBase (φ : A →ₐ[R] A') (h : ∀ a, ε' (φ a) = algebraMap R R' (ε a)) :
    AugCot ε →ₗ[R] AugCot ε' := sorry


@[simp] lemma mapBase_d (φ : A →ₐ[R] A') (h : ∀ a, ε' (φ a) = algebraMap R R' (ε a)) (a : A) :
    mapBase φ h (d ε a) = d ε' (φ a) := by sorry

lemma isBaseChange_mapBase (φ : A →ₐ[R] A') (h : ∀ a, ε' (φ a) = algebraMap R R' (ε a))
    (hφ : IsBaseChange R' φ.toLinearMap) : IsBaseChange R' (mapBase φ h) := by sorry


































lemma isBaseChange_of_isPushout [Algebra A A'] [IsScalarTower R A A']
    [hP : Algebra.IsPushout R R' A A']
    (h : ∀ a, ε' (IsScalarTower.toAlgHom R A A' a) = algebraMap R R' (ε a)) :
    IsBaseChange R' (mapBase (IsScalarTower.toAlgHom R A A') h) := by sorry


variable (R' ε) in

def baseChangeAug : R' ⊗[R] A →ₐ[R'] R' := sorry



@[simp] lemma baseChangeAug_tmul (r : R') (a : A) :
    baseChangeAug R' ε (r ⊗ₜ a) = r * algebraMap R R' (ε a) := by sorry


variable (R' ε) in
lemma isBaseChange_baseChangeAug :
    IsBaseChange R' (mapBase (ε := ε) (ε' := baseChangeAug R' ε)
      Algebra.TensorProduct.includeRight (fun a => by simp)) := by sorry


variable (R' ε) in

def baseChangeEquiv : R' ⊗[R] AugCot ε ≃ₗ[R'] AugCot (baseChangeAug R' ε) := sorry


@[simp] lemma baseChangeEquiv_tmul_d (r : R') (a : A) :
    baseChangeEquiv R' ε (r ⊗ₜ d ε a) = r • d _ (1 ⊗ₜ a) := by sorry


end BaseChange

section Smooth

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R)

lemma finite_of_kaehler [Module.Finite A Ω[A⁄R]] : Module.Finite R (AugCot ε) := by sorry



lemma projective_of_kaehler [Module.Projective A Ω[A⁄R]] : Module.Projective R (AugCot ε) := by sorry



lemma free_of_kaehler [Module.Free A Ω[A⁄R]] : Module.Free R (AugCot ε) := by sorry



lemma finrank_eq_of_free [Nontrivial R] [Module.Free A Ω[A⁄R]] :
    Module.finrank R (AugCot ε) = Module.finrank A Ω[A⁄R] := by sorry




instance finite [Algebra.EssFiniteType R A] : Module.Finite R (AugCot ε) := sorry

instance projective [Algebra.FormallySmooth R A] : Module.Projective R (AugCot ε) := sorry


lemma rankAtStalk_eq [Module.Finite A Ω[A⁄R]] [Module.Flat A Ω[A⁄R]] (p : PrimeSpectrum R) :
    Module.rankAtStalk (AugCot ε) p = Module.rankAtStalk Ω[A⁄R] (p.comap (ε : A →+* R)) := by sorry





instance free_of_isLocalRing [IsLocalRing R] [Algebra.FormallySmooth R A]
    [Algebra.EssFiniteType R A] : Module.Free R (AugCot ε) := sorry


instance free_of_isStandardSmooth [Algebra.IsStandardSmooth R A] : Module.Free R (AugCot ε) := sorry


lemma finrank_kaehler_of_isStandardSmoothOfRelativeDimension [Nontrivial A] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] : Module.finrank A Ω[A⁄R] = n := by sorry



lemma finrank_of_isStandardSmoothOfRelativeDimension [Nontrivial R] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] : Module.finrank R (AugCot ε) = n := by sorry




lemma nonempty_basis_of_isStandardSmoothOfRelativeDimension (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] :
    Nonempty (Module.Basis (Fin n) R (AugCot ε)) := by sorry






end Smooth

section RelDim

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R) {n : ℕ}

lemma smooth_of_locally
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A)) :
    Algebra.Smooth R A := by sorry




lemma rankAtStalk_kaehler_of_locally
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A))
    (q : PrimeSpectrum A) : Module.rankAtStalk Ω[A⁄R] q = n := by sorry





















lemma rankAtStalk_of_locally
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A))
    (p : PrimeSpectrum R) : Module.rankAtStalk (AugCot ε) p = n := by sorry



lemma finrank_of_locally [IsLocalRing R]
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A)) :
    Module.finrank R (AugCot ε) = n := by sorry




lemma nonempty_basis_of_locally [IsLocalRing R]
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A)) :
    Nonempty (Module.Basis (Fin n) R (AugCot ε)) := by sorry



open AlgebraicGeometry in

lemma locally_iff_smoothOfRelativeDimension :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A) ↔
      SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by sorry



end RelDim

section Affine

variable {R σ : Type*} [CommRing R] (x : σ → R)

open MvPolynomial

def mvPolynomialBasis : Module.Basis σ R (AugCot (aeval x : MvPolynomial σ R →ₐ[R] R)) := sorry





@[simp] lemma mvPolynomialBasis_apply (i : σ) :
    mvPolynomialBasis x i = d (aeval x : MvPolynomial σ R →ₐ[R] R) (X i) := by sorry






end Affine

end AugCot

open AugCot in

theorem augCot_properties.{u} {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (ε : A →ₐ[R] R) :

    (∀ a : A, d ε a = (RingHom.ker ε).toCotangent
      ⟨a - algebraMap R A (ε a), by simp [RingHom.mem_ker]⟩) ∧

    (letI : Algebra A R := (ε : A →+* R).toAlgebra
     ∃ e : AugCot ε ≃ₗ[R] R ⊗[A] Ω[A⁄R],
      ∀ a, e (d ε a) = 1 ⊗ₜ KaehlerDifferential.D R A a) ∧

    (∀ (N : Type u) [AddCommGroup N] [Module R N],
      letI : Module A N := Module.compHom N (ε : A →+* R)
      haveI : IsScalarTower R A N := isScalarTower_of_smul_eq ε fun _ _ => rfl
      ∃ e : Derivation R A N ≃ₗ[R] (AugCot ε →ₗ[R] N), ∀ D a, e D (d ε a) = D a) ∧

    (∀ (N : Type u) [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N],
      ∃ e : {φ : A →ₐ[R] TrivSqZeroExt R N // (TrivSqZeroExt.fstHom R R N).comp φ = ε} ≃
        (AugCot ε →ₗ[R] N), ∀ φ a, e φ (d ε a) = (φ.1 a).snd) ∧

    (∀ (R' : Type u) [CommRing R'] [Algebra R R'],
      (∀ r a, baseChangeAug R' ε (r ⊗ₜ a) = r * algebraMap R R' (ε a)) ∧
      ∃ e : R' ⊗[R] AugCot ε ≃ₗ[R'] AugCot (baseChangeAug R' ε),
        ∀ r a, e (r ⊗ₜ d ε a) = r • d _ (1 ⊗ₜ a)) ∧

    (map (AlgHom.id R A) (AlgHom.comp_id ε) = LinearMap.id) ∧
    (∀ (B : Type u) [CommRing B] [Algebra R B] (εB : B →ₐ[R] R) (φ : A →ₐ[R] B)
      (h : εB.comp φ = ε),
      (∀ a, map φ h (d ε a) = d εB (φ a)) ∧
      (∀ (C : Type u) [CommRing C] [Algebra R C] (εC : C →ₐ[R] R) (ψ : B →ₐ[R] C)
        (h' : εC.comp ψ = εB) (h'' : εC.comp (ψ.comp φ) = ε),
        map (ψ.comp φ) h'' = map ψ h' ∘ₗ map φ h) ∧

      ((φ : A →+* B).Etale → Function.Bijective (map φ h)) ∧

      (Function.Surjective φ →
        (∀ x : RingHom.ker φ, kerMap φ h x = (RingHom.ker ε).toCotangent ⟨x, ker_le φ h x.2⟩) ∧
        Function.Exact (kerMap φ h) (map φ h) ∧ Function.Surjective (map φ h))) ∧

    (∀ (f : A) (B : Type u) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
      [IsLocalization.Away f B],
      (IsUnit (ε f) → ∃ εB : B →ₐ[R] R, εB.comp (IsScalarTower.toAlgHom R A B) = ε) ∧
      ∀ (εB : B →ₐ[R] R) (h : εB.comp (IsScalarTower.toAlgHom R A B) = ε),
        Function.Bijective (map _ h)) ∧

    (∀ (B : Type u) [CommRing B] [Algebra R B] (εB : B →ₐ[R] R),
      ∃ e : AugCot (Algebra.TensorProduct.productMap ε εB) ≃ₗ[R] AugCot ε × AugCot εB,
        ∀ a b, e (d _ (a ⊗ₜ b)) = (εB b • d ε a, ε a • d εB b)) ∧

    (Algebra.Smooth R A → Module.Finite R (AugCot ε) ∧ Module.Projective R (AugCot ε) ∧
      (IsLocalRing R → Module.Free R (AugCot ε))) ∧
    (Algebra.IsStandardSmooth R A → Module.Free R (AugCot ε)) ∧
    (∀ n : ℕ, Algebra.IsStandardSmoothOfRelativeDimension n R A →
      Nonempty (Module.Basis (Fin n) R (AugCot ε))) ∧
    (∀ n : ℕ, AlgebraicGeometry.SmoothOfRelativeDimension n
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A))) →
      Algebra.Smooth R A ∧ (∀ p : PrimeSpectrum R, Module.rankAtStalk (AugCot ε) p = n) ∧
      (IsLocalRing R → Nonempty (Module.Basis (Fin n) R (AugCot ε)))) := by sorry



















end GlobalTheory
