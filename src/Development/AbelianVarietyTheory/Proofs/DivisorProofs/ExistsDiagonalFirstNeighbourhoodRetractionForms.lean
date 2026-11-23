module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowerCompatRelFiltrationTwoSidedRelEqBotOfBasStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormsMapOfDividedPowerDerivationStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormQuotientClassEqOfRelDifferences

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers TrivSqZeroExt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm
open GlobalTheory.CrysConn

namespace GlobalTheory.PDForm.Nbhd

section Ring

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

@[reducible] def opK : Module Bᵐᵒᵖ (K1 R δ) := Module.compHom _ ((RingHom.id B).fromOpposite mul_comm)

attribute [local instance] opK

theorem isCentral_K : IsCentralScalar B (K1 R δ) := ⟨fun _ _ ↦ rfl⟩

theorem isTower_K : IsScalarTower R Bᵐᵒᵖ (K1 R δ) := ⟨fun r b m ↦ smul_assoc r b.unop m⟩

attribute [local instance] isCentral_K isTower_K

def kdD : Derivation R B (K1 R δ) := (N1 R δ).mkQ.compDer (D R B)

theorem kdD_apply (b : B) : kdD (R := R) δ b = kd0 R δ b := rfl

theorem isDPDer_kdD : IsDPDer δ (kdD (R := R) δ) := fun n a ha ↦ by
  rw [kdD_apply, kdD_apply, divPowerCompatFunctionDifferential_apply, divPowerCompatFunctionDifferential_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  change ι1 _ ∈ rel R δ
  exact Ideal.subset_span ⟨n, a, ha, rfl⟩

end Ring

section Site

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {t : X ⟶ Sp R}

attribute [local instance] opK isCentral_K isTower_K

abbrev ER (T : Thick κ t) : Type := TrivSqZeroExt T.B (K1 R T.δ)

@[reducible] def nb (T : Thick κ t) : Thick κ t where
  B := ER T
  J := T.J.comap (pr T.B (K1 R T.δ))
  δ := extDP (K1 R T.δ) T.δ
  nil := isDPNilpotent_extend _ T.nil
  dp := IsDPMorphism.comp _ (isDPMorphism_inl (K1 R T.δ) T.δ) T.dp
  B₀ := T.B₀
  π := T.π.comp (pr T.B (K1 R T.δ))
  surj y := let ⟨b, hb⟩ := T.surj y; ⟨inl b, hb⟩
  ker x := T.ker x.fst
  x := T.x
  w := T.w

def kmS {T T' : Thick κ t} (φ : T ⟶ T') : K1 R T.δ →ₛₗ[(φ.φ : T.B →+* T'.B)] K1 R T'.δ where
  toFun := km1 (SemiHom.of_algHom φ.φ) φ.dp
  map_add' := map_add _
  map_smul' b x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormMap_mk, divPowerCompatOneFormMap_mk, SemiHom.oneFormMap_smul_semilinear, Submodule.Quotient.mk_smul]

def nbAlg {T T' : Thick κ t} (φ : T ⟶ T') : ER T →ₐ[R] ER T' :=
  { extMap (φ.φ : T.B →+* T'.B) (kmS φ) with
    commutes' := fun r ↦ by
      ext
      · exact (add_zero _).trans (φ.φ.commutes r)
      · exact (zero_add _).trans (map_zero _) }

@[simp] theorem nbAlg_fst {T T' : Thick κ t} (φ : T ⟶ T') (x : ER T) : (nbAlg φ x).fst = φ.φ x.fst := add_zero _

@[simp] theorem nbAlg_snd {T T' : Thick κ t} (φ : T ⟶ T') (x : ER T) :
    (nbAlg φ x).snd = km1 (SemiHom.of_algHom φ.φ) φ.dp x.snd := zero_add _

def nbMap {T T' : Thick κ t} (φ : T ⟶ T') : nb T ⟶ nb T' where
  φ := nbAlg φ
  φ₀ := φ.φ₀
  comm b := by
    change φ.φ₀ (T.π b.fst) = T'.π (nbAlg φ b).fst
    rw [nbAlg_fst, φ.comm]
  dp := isDPMorphism_extMap φ.dp (kmS φ)
  pt := φ.pt

@[reducible] def nbF : Thick κ t ⥤ Thick κ t where
  obj := nb
  map := nbMap
  map_id T := Thick.hom_ext fun x ↦ by
    change nbAlg (𝟙 T) x = x
    ext
    · simp
    · rw [nbAlg_snd]
      exact divPowerCompatOneFormMap_id _ _ (fun _ ↦ rfl) _
  map_comp φ ψ := Thick.hom_ext fun x ↦ by
    change nbAlg (φ ≫ ψ) x = nbAlg ψ (nbAlg φ x)
    ext
    · simp
    · rw [nbAlg_snd, nbAlg_snd, nbAlg_snd]
      exact (divPowerCompatOneFormMap_comp _ _ _ _ _ _ (fun _ ↦ rfl) _).symm

def inlMap (T : Thick κ t) : T ⟶ nb T where
  φ := { inlHom T.B (K1 R T.δ) with commutes' := fun _ ↦ rfl }
  φ₀ := RingHom.id _
  comm _ := rfl
  dp := isDPMorphism_inl (K1 R T.δ) T.δ
  pt := by rw [spMap_id, Category.id_comp]

def difMap (T : Thick κ t) : T ⟶ nb T where
  φ := derSec (kdD T.δ)
  φ₀ := RingHom.id _
  comm b := by
    change T.π b = T.π (derSec (kdD T.δ) b).fst
    rw [fst_derSec]
  dp := (isDPDer_kdD T.δ).isDPMorphism
  pt := by rw [spMap_id, Category.id_comp]

def uN : 𝟭 (Thick κ t) ⟶ nbF where
  app := inlMap
  naturality T T' φ := Thick.hom_ext fun b ↦ by
    change inl (φ.φ b) = nbAlg φ (inl b)
    ext
    · simp
    · rw [nbAlg_snd]; simp

def vN : 𝟭 (Thick κ t) ⟶ nbF where
  app := difMap
  naturality T T' φ := Thick.hom_ext fun b ↦ by
    change derSec (kdD T'.δ) (φ.φ b) = nbAlg φ (derSec (kdD T.δ) b)
    ext
    · simp
    · rw [nbAlg_snd, snd_derSec, snd_derSec, kdD_apply, kdD_apply]
      exact (divPowerCompatOneFormMap_functionDifferential _ _ b).symm

end Site

end GlobalTheory.PDForm.Nbhd

namespace GlobalTheory.PDForm.Nbhd

section Retr

variable {R B C : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  {J : Ideal B} (δ : DividedPowers J) {JC : Ideal C} (δC : DividedPowers JC) (ρ : DR R C → DR R B)

theorem oneForm_quotient_class_eq_of_rel_differences {x : DR R C} {ω ω' : Ω[B⁄R]} (h : ρ x - ι1 ω ∈ rel R δ) (h' : ρ x - ι1 ω' ∈ rel R δ) :
    (Submodule.Quotient.mk ω : K1 R δ) = Submodule.Quotient.mk ω' := by
  rw [Submodule.Quotient.eq]
  change ι1 (ω - ω') ∈ rel R δ
  have := sub_mem h' h
  rwa [sub_sub_sub_cancel_left, ← map_sub] at this

theorem mk_eq {j : ℕ} {x : DR R C} {y y' : Om R B j} (h : ρ x - y ∈ rel R δ) (h' : ρ x - y' ∈ rel R δ) :
    (Submodule.Quotient.mk y : K R δ j) = Submodule.Quotient.mk y' := by
  rw [Submodule.Quotient.eq]
  change ((y - y' : Om R B j) : DR R B) ∈ rel R δ
  have := sub_mem h' h
  rwa [sub_sub_sub_cancel_left, ← Submodule.coe_sub] at this

variable {δ ρ}

def oneFormRetractionToK1 (hadd : ∀ x y, ρ (x + y) - ρ x - ρ y ∈ rel R δ) (hrel : ∀ x ∈ rel R δC, ρ x ∈ rel R δ)
    (hone : ∀ x, ∃ ω, ρ (ι1 x) - ι1 ω ∈ rel R δ) : Ω[C⁄R] →+ K1 R δ where
  toFun x := Submodule.Quotient.mk (hone x).choose
  map_zero' := by
    have h0 : ρ (ι1 (0 : Ω[C⁄R])) - ι1 (0 : Ω[B⁄R]) ∈ rel R δ := by
      rw [map_zero, map_zero, sub_zero]; exact hrel 0 (zero_mem _)
    rw [oneForm_quotient_class_eq_of_rel_differences δ ρ (hone 0).choose_spec h0, Submodule.Quotient.mk_zero]
  map_add' x y := by
    rw [← Submodule.Quotient.mk_add]
    refine oneForm_quotient_class_eq_of_rel_differences δ ρ (hone (x + y)).choose_spec ?_
    have := add_mem (add_mem (hadd (ι1 x) (ι1 y)) (hone x).choose_spec) (hone y).choose_spec
    rw [map_add (f := _), map_add (f := _)]
    convert this using 1
    abel

def r1 (hadd : ∀ x y, ρ (x + y) - ρ x - ρ y ∈ rel R δ) (hrel : ∀ x ∈ rel R δC, ρ x ∈ rel R δ)
    (hone : ∀ x, ∃ ω, ρ (ι1 x) - ι1 ω ∈ rel R δ) : K1 R δC →+ K1 R δ :=
  QuotientAddGroup.lift (N1 R δC).toAddSubgroup (oneFormRetractionToK1 δC hadd hrel hone) fun x hx ↦ by
    change Submodule.Quotient.mk _ = 0
    have h0 : ρ (ι1 x) - ι1 (0 : Ω[B⁄R]) ∈ rel R δ := by
      rw [map_zero, sub_zero]; exact hrel _ hx
    rw [oneForm_quotient_class_eq_of_rel_differences δ ρ (hone x).choose_spec h0, Submodule.Quotient.mk_zero]

theorem divPowerCompatOneForm_retraction_spec (hadd : ∀ x y, ρ (x + y) - ρ x - ρ y ∈ rel R δ) (hrel : ∀ x ∈ rel R δC, ρ x ∈ rel R δ)
    (hone : ∀ x, ∃ ω, ρ (ι1 x) - ι1 ω ∈ rel R δ) {x : Ω[C⁄R]} {ω : Ω[B⁄R]} (h : ρ (ι1 x) - ι1 ω ∈ rel R δ) :
    r1 δC hadd hrel hone (Submodule.Quotient.mk x) = Submodule.Quotient.mk ω :=
  oneForm_quotient_class_eq_of_rel_differences δ ρ (hone x).choose_spec h

def rPre (hadd : ∀ x y, ρ (x + y) - ρ x - ρ y ∈ rel R δ) (hrel : ∀ x ∈ rel R δC, ρ x ∈ rel R δ)
    (hdeg : ∀ (j : ℕ), ∀ x ∈ ⋀[C]^j Ω[C⁄R], ∃ y ∈ ⋀[B]^j Ω[B⁄R], ρ x - y ∈ rel R δ) (j : ℕ) :
    Om R C j →+ K R δ j where
  toFun x := Submodule.Quotient.mk ⟨(hdeg j x x.2).choose, (hdeg j x x.2).choose_spec.1⟩
  map_zero' := by
    have h0 : ρ ((0 : Om R C j) : DR R C) - ((0 : Om R B j) : DR R B) ∈ rel R δ := by
      rw [ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, sub_zero]; exact hrel 0 (zero_mem _)
    rw [mk_eq δ ρ (hdeg j _ (0 : Om R C j).2).choose_spec.2 h0, Submodule.Quotient.mk_zero]
  map_add' x y := by
    rw [← Submodule.Quotient.mk_add]
    refine mk_eq δ ρ (hdeg j _ (x + y).2).choose_spec.2 ?_
    have := add_mem (add_mem (hadd x y) (hdeg j _ x.2).choose_spec.2) (hdeg j _ y.2).choose_spec.2
    rw [Submodule.coe_add, Submodule.coe_add]
    convert this using 1
    abel

def rK (hadd : ∀ x y, ρ (x + y) - ρ x - ρ y ∈ rel R δ) (hrel : ∀ x ∈ rel R δC, ρ x ∈ rel R δ)
    (hdeg : ∀ (j : ℕ), ∀ x ∈ ⋀[C]^j Ω[C⁄R], ∃ y ∈ ⋀[B]^j Ω[B⁄R], ρ x - y ∈ rel R δ) (j : ℕ) :
    K R δC j →+ K R δ j :=
  QuotientAddGroup.lift (N R δC j).toAddSubgroup (rPre δC hadd hrel hdeg j) fun x hx ↦ by
    change Submodule.Quotient.mk _ = 0
    have h0 : ρ (x : DR R C) - ((0 : Om R B j) : DR R B) ∈ rel R δ := by
      rw [ZeroMemClass.coe_zero, sub_zero]; exact hrel _ hx
    rw [mk_eq δ ρ (hdeg j _ x.2).choose_spec.2 h0, Submodule.Quotient.mk_zero]

theorem rK_spec (hadd : ∀ x y, ρ (x + y) - ρ x - ρ y ∈ rel R δ) (hrel : ∀ x ∈ rel R δC, ρ x ∈ rel R δ)
    (hdeg : ∀ (j : ℕ), ∀ x ∈ ⋀[C]^j Ω[C⁄R], ∃ y ∈ ⋀[B]^j Ω[B⁄R], ρ x - y ∈ rel R δ) {j : ℕ}
    {x : Om R C j} {y : Om R B j} (h : ρ x - y ∈ rel R δ) :
    rK δC hadd hrel hdeg j (Submodule.Quotient.mk x) = Submodule.Quotient.mk y :=
  mk_eq δ ρ (hdeg j _ x.2).choose_spec.2 h

end Retr

section Agree

variable {R B C : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  {J : Ideal B} {δ : DividedPowers J}

theorem agree (hr : ∀ x ∈ rel R δ, ∀ y, x * y ∈ rel R δ) (f g : DR R C → DR R B)
    (fa : ∀ x y, f (x + y) - f x - f y ∈ rel R δ) (fm : ∀ x y, f (x * y) - f x * f y ∈ rel R δ)
    (ga : ∀ x y, g (x + y) - g x - g y ∈ rel R δ) (gm : ∀ x y, g (x * y) - g x * g y ∈ rel R δ)
    (h0 : ∀ c, f (algebraMap C _ c) - g (algebraMap C _ c) ∈ rel R δ)
    (h1 : ∀ c, f (ι1 (D R C c)) - g (ι1 (D R C c)) ∈ rel R δ) (x : DR R C) : f x - g x ∈ rel R δ := by
  induction x using indDR with
  | h c => exact h0 c
  | hd c => exact h1 c
  | hm x y hx hy =>
    have := add_mem (sub_mem (fm x y) (gm x y)) (add_mem (hr _ hx (f y)) (Ideal.mul_mem_left _ (g x) hy))
    convert this using 1
    noncomm_ring
  | ha x y hx hy =>
    have := add_mem (sub_mem (fa x y) (ga x y)) (add_mem hx hy)
    convert this using 1
    abel

theorem algebraMapInv_eq_zero {M : Type} [AddCommGroup M] [Module B M] {j : ℕ} (hj : j ≠ 0) {x : ExteriorAlgebra B M}
    (hx : x ∈ ⋀[B]^j M) : ExteriorAlgebra.algebraMapInv x = 0 := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap b => exact absurd rfl hj
  | add x y i _ _ hx hy => rw [map_add (f := _), hx hj, hy hj, add_zero]
  | mem_mul m hm i x hx ih =>
    obtain ⟨ω, rfl⟩ := hm
    have : ExteriorAlgebra.algebraMapInv (ExteriorAlgebra.ι B ω) = 0 := by
      simp [ExteriorAlgebra.algebraMapInv]
    rw [map_mul, this, zero_mul]

end Agree

end GlobalTheory.PDForm.Nbhd

namespace GlobalTheory.PDForm.Nbhd

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {t : X ⟶ Sp R}

attribute [local instance] opK isCentral_K isTower_K

abbrev fstA (T : Thick κ t) : ER T →ₐ[R] T.B := fstHom R T.B (K1 R T.δ)

def sndA (T : Thick κ t) : ER T →+ K1 R T.δ where
  toFun := snd
  map_zero' := rfl
  map_add' := snd_add

theorem sndA_apply (T : Thick κ t) (x : ER T) : sndA T x = x.snd := rfl

theorem sndA_mul (T : Thick κ t) (x y : ER T) :
    sndA T (x * y) = fstA T x • sndA T y + fstA T y • sndA T x := by
  rw [sndA_apply, sndA_apply, sndA_apply, snd_mul]
  rfl

theorem sndA_algebraMap (T : Thick κ t) (r : R) : sndA T (algebraMap R (ER T) r) = 0 := rfl

theorem sndA_dpow (T : Thick κ t) (n : ℕ) (a : ER T) (_ : a ∈ (nb T).J) :
    sndA T ((nb T).δ.dpow (n + 1) a) = fstA T ((nb T).δ.dpow n a) • sndA T a := by
  change ((extDP (K1 R T.δ) T.δ).dpow (n + 1) a).snd = ((extDP (K1 R T.δ) T.δ).dpow n a).fst • a.snd
  rw [snd_extDP, fst_extDP]
  rfl

section Agree

variable (hr : ∀ T : Thick κ t, ∀ x ∈ rel R T.δ, ∀ y, x * y ∈ rel R T.δ)


include hr in
theorem natAgree {T T' : Thick κ t} (φ : T ⟶ T') (ρ : DR R (ER T) → DR R T.B) (ρ' : DR R (ER T') → DR R T'.B)
    (ha : ∀ x y, ρ (x + y) - ρ x - ρ y ∈ rel R T.δ) (hm : ∀ x y, ρ (x * y) - ρ x * ρ y ∈ rel R T.δ)
    (h0 : ∀ c, ρ (algebraMap (ER T) (DR R (ER T)) c) - algebraMap T.B (DR R T.B) (fstA T c) ∈ rel R T.δ)
    (h1 : ∀ c ω, Submodule.Quotient.mk ω = sndA T c → ρ (ι1 (D R (ER T) c)) - ι1 ω ∈ rel R T.δ)
    (ha' : ∀ x y, ρ' (x + y) - ρ' x - ρ' y ∈ rel R T'.δ) (hm' : ∀ x y, ρ' (x * y) - ρ' x * ρ' y ∈ rel R T'.δ)
    (h0' : ∀ c, ρ' (algebraMap (ER T') (DR R (ER T')) c) - algebraMap T'.B (DR R T'.B) (fstA T' c) ∈ rel R T'.δ)
    (h1' : ∀ c ω, Submodule.Quotient.mk ω = sndA T' c → ρ' (ι1 (D R (ER T') c)) - ι1 ω ∈ rel R T'.δ)
    (x : DR R (ER T)) :
    ρ' ((SemiHom.of_algHom (nbAlg φ)).mDR x) - (SemiHom.of_algHom φ.φ).mDR (ρ x) ∈ rel R T'.δ := by
  set h := SemiHom.of_algHom φ.φ
  set he := SemiHom.of_algHom (nbAlg φ)
  have mr : ∀ z ∈ rel R T.δ, h.mDR z ∈ rel R T'.δ := fun z hz ↦ mDR_mem_rel h φ.dp hz
  refine agree (C := ER T) (hr T') (fun x ↦ ρ' (he.mDR x)) (fun x ↦ h.mDR (ρ x))
    (fun x y ↦ by rw [map_add (f := _)]; exact ha' _ _) (fun x y ↦ by rw [map_mul]; exact hm' _ _)
    (fun x y ↦ by have := mr _ (ha x y); rwa [map_sub, map_sub] at this)
    (fun x y ↦ by have := mr _ (hm x y); rwa [map_sub, map_mul] at this) (fun c ↦ ?_) (fun c ↦ ?_) x
  · have e1 := h0' (nbAlg φ c)
    have e2 := mr _ (h0 c)
    rw [map_sub, SemiHom.mDR_algebraMap] at e2
    have k1 : he.mDR (algebraMap (ER T) (DR R (ER T)) c) = algebraMap (ER T') (DR R (ER T')) (nbAlg φ c) :=
      SemiHom.mDR_algebraMap _ _
    have k2 : fstA T' (nbAlg φ c) = φ.φ (fstA T c) := nbAlg_fst φ c
    rw [k2] at e1
    simp only [RingHom.coe_coe] at e2
    change ρ' (he.mDR (algebraMap (ER T) (DR R (ER T)) c)) - h.mDR (ρ (algebraMap (ER T) (DR R (ER T)) c)) ∈ _
    rw [k1]
    convert sub_mem e1 e2 using 1
    abel
  · obtain ⟨ω, hω⟩ := Submodule.Quotient.mk_surjective _ (sndA T c)
    have e1 := h1' (nbAlg φ c) (h.m1 ω) (by
      rw [sndA_apply, nbAlg_snd, ← sndA_apply, ← hω, divPowerCompatOneFormMap_mk])
    have e2 := mr _ (h1 c ω hω)
    rw [map_sub, SemiHom.mDR_ι] at e2
    have k1 : he.mDR (ι1 (D R (ER T) c)) = ι1 (D R (ER T') (nbAlg φ c)) := by
      rw [SemiHom.mDR_ι, SemiHom.m1_D]; rfl
    have e3 : ρ' (he.mDR (ι1 (D R (ER T) c))) - ι1 (h.m1 ω) ∈ rel R T'.δ := by rw [k1]; exact e1
    have e4 := sub_mem e3 e2
    rw [sub_sub_sub_cancel_right] at e4
    exact e4


include hr in
theorem uAgree (T : Thick κ t) (ρ : DR R (ER T) → DR R T.B)
    (ha : ∀ x y, ρ (x + y) - ρ x - ρ y ∈ rel R T.δ) (hm : ∀ x y, ρ (x * y) - ρ x * ρ y ∈ rel R T.δ)
    (h0 : ∀ c, ρ (algebraMap (ER T) (DR R (ER T)) c) - algebraMap T.B (DR R T.B) (fstA T c) ∈ rel R T.δ)
    (h1 : ∀ c ω, Submodule.Quotient.mk ω = sndA T c → ρ (ι1 (D R (ER T) c)) - ι1 ω ∈ rel R T.δ)
    (x : DR R T.B) :
    ρ ((SemiHom.of_algHom (inlMap T).φ).mDR x) - algebraMap T.B (DR R T.B) (ExteriorAlgebra.algebraMapInv x)
      ∈ rel R T.δ := by
  set h := SemiHom.of_algHom (inlMap T).φ
  refine agree (C := T.B) (hr T) (fun x ↦ ρ (h.mDR x)) (fun x ↦ algebraMap T.B (DR R T.B) (ExteriorAlgebra.algebraMapInv x))
    (fun x y ↦ by rw [map_add (f := _)]; exact ha _ _) (fun x y ↦ by rw [map_mul]; exact hm _ _) (fun x y ↦ by simp)
    (fun x y ↦ by simp) (fun b ↦ ?_) (fun b ↦ ?_) x
  · have e := h0 ((inlMap T).φ b)
    simp only [SemiHom.mDR_algebraMap, AlgHom.commutes]
    exact e
  · have e := h1 ((inlMap T).φ b) 0 (by rw [Submodule.Quotient.mk_zero]; rfl)
    have z : ExteriorAlgebra.algebraMapInv (ι1 (D R T.B b)) = 0 := by simp [ExteriorAlgebra.algebraMapInv]
    simp only [SemiHom.mDR_ι, SemiHom.m1_D, z, map_zero, sub_zero] at e ⊢
    exact e


include hr in
theorem vAgree (T : Thick κ t) (ρ : DR R (ER T) → DR R T.B)
    (ha : ∀ x y, ρ (x + y) - ρ x - ρ y ∈ rel R T.δ) (hm : ∀ x y, ρ (x * y) - ρ x * ρ y ∈ rel R T.δ)
    (h0 : ∀ c, ρ (algebraMap (ER T) (DR R (ER T)) c) - algebraMap T.B (DR R T.B) (fstA T c) ∈ rel R T.δ)
    (h1 : ∀ c ω, Submodule.Quotient.mk ω = sndA T c → ρ (ι1 (D R (ER T) c)) - ι1 ω ∈ rel R T.δ)
    (x : DR R T.B) : ρ ((SemiHom.of_algHom (difMap T).φ).mDR x) - x ∈ rel R T.δ := by
  set h := SemiHom.of_algHom (difMap T).φ
  refine agree (C := T.B) (hr T) (fun x ↦ ρ (h.mDR x)) id
    (fun x y ↦ by rw [map_add (f := _)]; exact ha _ _) (fun x y ↦ by rw [map_mul]; exact hm _ _) (fun x y ↦ by simp)
    (fun x y ↦ by simp) (fun b ↦ ?_) (fun b ↦ ?_) x
  · have e := h0 ((difMap T).φ b)
    have hf : fstA T ((difMap T).φ b) = b := fst_derSec _ b
    rw [hf] at e
    simp only [SemiHom.mDR_algebraMap, id]
    exact e
  · have e := h1 ((difMap T).φ b) (D R T.B b) rfl
    simp only [SemiHom.mDR_ι, SemiHom.m1_D, id]
    exact e

end Agree

end GlobalTheory.PDForm.Nbhd
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalFirstNeighbourhoodRetractionForms

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers TrivSqZeroExt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm
open GlobalTheory.CrysConn

namespace GlobalTheory.PDForm.Nbhd

open GlobalTheory.SmoothLift

attribute [local instance] opK isCentral_K isTower_K



theorem exists_retraction : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R), ∃ (S : Thick κ t ⥤ Thick κ t) (u v : 𝟭 _ ⟶ S)
    (r1 : ∀ T, (KK κ t).M1.obj (S.obj T) →+ (KK κ t).M1.obj T)
    (r2 : ∀ T, (KK κ t).M2.obj (S.obj T) →+ (KK κ t).M2.obj T)
    (r3 : ∀ T, (KK κ t).M3.obj (S.obj T) →+ (KK κ t).M3.obj T),
    ((∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r1 T' ((KK κ t).M1.map (S.map φ) x) = (KK κ t).M1.map φ (r1 T x)) ∧
      (∀ T x, r1 T ((KK κ t).M1.map (u.app T) x) = 0) ∧ (∀ T x, r1 T ((KK κ t).M1.map (v.app T) x) = x)) ∧
    ((∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r2 T' ((KK κ t).M2.map (S.map φ) x) = (KK κ t).M2.map φ (r2 T x)) ∧
      (∀ T x, r2 T ((KK κ t).M2.map (u.app T) x) = 0) ∧ (∀ T x, r2 T ((KK κ t).M2.map (v.app T) x) = x)) ∧
    (∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r3 T' ((KK κ t).M3.map (S.map φ) x) = (KK κ t).M3.map φ (r3 T x)) ∧
      (∀ T x, r3 T ((KK κ t).M3.map (u.app T) x) = 0) ∧ (∀ T x, r3 T ((KK κ t).M3.map (v.app T) x) = x) := by
  intro R _ I κ X t
  have hr : ∀ T : Thick κ t, ∀ x ∈ rel R T.δ, ∀ y, x * y ∈ rel R T.δ := fun T ↦ (GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base.1 R T.B T.J T.δ).1
  have H := fun T : Thick κ t ↦ GlobalTheory.T.exists_formsMap_of_dividedPowerDerivation R T.B T.J T.δ (ER T) (nb T).J (nb T).δ (fstA T) (sndA T)
    (sndA_mul T) (sndA_algebraMap T) (fun n a ha ↦ sndA_dpow T n a ha)
  choose ρ ha hm h0 h1 hrel hone hdeg using H
  have natK : ∀ (j : ℕ) (T T' : Thick κ t) (φ : T ⟶ T') (x : K R (nb T).δ j),
      rK (nb T').δ (ha T') (hrel T') (hdeg T') j (km (SemiHom.of_algHom (nbAlg φ)) (nbF.map φ).dp j x) =
        km (SemiHom.of_algHom φ.φ) φ.dp j (rK (nb T).δ (ha T) (hrel T) (hdeg T) j x) := by
    intro j T T' φ x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx : (x : DR R (ER T)) ∈ ⋀[ER T]^j Ω[ER T⁄R] := x.2
    have hd := hdeg T j _ hx
    let y := hd.choose
    have hy : y ∈ ⋀[T.B]^j Ω[T.B⁄R] := hd.choose_spec.1
    have hρy : ρ T x - y ∈ rel R T.δ := hd.choose_spec.2
    rw [rK_spec (nb T).δ (ha T) (hrel T) (hdeg T) (y := ⟨y, hy⟩) hρy, km_mk]
    have e := add_mem (natAgree hr φ (ρ T) (ρ T') (ha T) (hm T) (h0 T) (h1 T) (ha T') (hm T') (h0 T') (h1 T') x)
      (mDR_mem_rel (SemiHom.of_algHom φ.φ) φ.dp hρy)
    rw [map_sub, sub_add_sub_cancel] at e
    exact rK_spec (nb T').δ (ha T') (hrel T') (hdeg T') (x := (SemiHom.of_algHom (nbAlg φ)).mOm j x)
      (y := (SemiHom.of_algHom φ.φ).mOm j ⟨y, hy⟩) e
  have uK : ∀ (j : ℕ), j ≠ 0 → ∀ (T : Thick κ t) (x : K R T.δ j),
      rK (nb T).δ (ha T) (hrel T) (hdeg T) j (km (SemiHom.of_algHom (inlMap T).φ) (inlMap T).dp j x) = 0 := by
    intro j hj T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e := uAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) x
    rw [algebraMapInv_eq_zero hj x.2, map_zero] at e
    have e' : ρ T ((SemiHom.of_algHom (inlMap T).φ).mDR x) - ((0 : Om R T.B j) : DR R T.B) ∈ rel R T.δ := by
      rw [ZeroMemClass.coe_zero]; exact e
    exact (rK_spec (nb T).δ (ha T) (hrel T) (hdeg T) (x := (SemiHom.of_algHom (inlMap T).φ).mOm j x) e').trans
      (Submodule.Quotient.mk_zero _)
  have vK : ∀ (j : ℕ) (T : Thick κ t) (x : K R T.δ j),
      rK (nb T).δ (ha T) (hrel T) (hdeg T) j (km (SemiHom.of_algHom (difMap T).φ) (difMap T).dp j x) = x := by
    intro j T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact rK_spec (nb T).δ (ha T) (hrel T) (hdeg T) (x := (SemiHom.of_algHom (difMap T).φ).mOm j x) (y := x)
      (vAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) x)
  refine ⟨nbF, uN, vN, fun T ↦ r1 (nb T).δ (ha T) (hrel T) (hone T), fun T ↦ rK (nb T).δ (ha T) (hrel T) (hdeg T) 2,
    fun T ↦ rK (nb T).δ (ha T) (hrel T) (hdeg T) 3, ⟨?_, ?_, ?_⟩, ⟨fun T T' φ x ↦ natK 2 T T' φ x,
      fun T x ↦ uK 2 (by norm_num) T x, fun T x ↦ vK 2 T x⟩, fun T T' φ x ↦ natK 3 T T' φ x,
      fun T x ↦ uK 3 (by norm_num) T x, fun T x ↦ vK 3 T x⟩
  · intro T T' φ x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hd := hone T x
    let ω := hd.choose
    have hω : ρ T (ι1 x) - ι1 ω ∈ rel R T.δ := hd.choose_spec
    have e := add_mem (natAgree hr φ (ρ T) (ρ T') (ha T) (hm T) (h0 T) (h1 T) (ha T') (hm T') (h0 T') (h1 T') (ι1 x))
      (mDR_mem_rel (SemiHom.of_algHom φ.φ) φ.dp hω)
    rw [map_sub, sub_add_sub_cancel, SemiHom.mDR_ι, SemiHom.mDR_ι] at e
    have l := divPowerCompatOneForm_retraction_spec (nb T).δ (ha T) (hrel T) (hone T) (x := x) hω
    exact (divPowerCompatOneForm_retraction_spec (nb T').δ (ha T') (hrel T') (hone T') (x := (SemiHom.of_algHom (nbAlg φ)).m1 x)
      (ω := (SemiHom.of_algHom φ.φ).m1 ω) e).trans (congrArg (km1 (SemiHom.of_algHom φ.φ) φ.dp) l).symm
  · intro T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e := uAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) (ι1 x)
    have z : ExteriorAlgebra.algebraMapInv (ι1 x) = 0 := by simp [ExteriorAlgebra.algebraMapInv]
    rw [z, map_zero, SemiHom.mDR_ι] at e
    have e' : ρ T (ι1 ((SemiHom.of_algHom (inlMap T).φ).m1 x)) - ι1 (0 : Ω[T.B⁄R]) ∈ rel R T.δ := by
      rw [map_zero]; exact e
    exact (divPowerCompatOneForm_retraction_spec (nb T).δ (ha T) (hrel T) (hone T) (x := (SemiHom.of_algHom (inlMap T).φ).m1 x) e').trans
      (Submodule.Quotient.mk_zero _)
  · intro T x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e := vAgree hr T (ρ T) (ha T) (hm T) (h0 T) (h1 T) (ι1 x)
    rw [SemiHom.mDR_ι] at e
    exact divPowerCompatOneForm_retraction_spec (nb T).δ (ha T) (hrel T) (hone T) (x := (SemiHom.of_algHom (difMap T).φ).m1 x) (ω := x) e

end GlobalTheory.PDForm.Nbhd
end
end
end
