module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIffEtaleAt
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarEtaleIntegralClosureRootUniformizerStatement
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureOfIsArtinianRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureTorsorOfFractionFieldsStatement
public import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorFieldEqProdGaloisStatement
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.TensorProduct.Pi

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosurePiOfEtale

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.PiClosure

noncomputable def integralClosurePiEquiv (R : Type) [CommRing R] (ι : Type) [Finite ι]
    (E : ι → Type) [∀ i, CommRing (E i)] [∀ i, Algebra R (E i)] :
    integralClosure R (∀ i, E i) ≃ₐ[R] ∀ i, integralClosure R (E i) :=
  AlgEquiv.ofBijective
    (AlgHom.pi fun i =>
      ((Pi.evalAlgHom R E i).comp (integralClosure R (∀ i, E i)).val).codRestrict
        (integralClosure R (E i)) fun x => x.2.map (Pi.evalAlgHom R E i))
    (by
      constructor
      · intro x y hxy
        apply Subtype.ext
        funext i
        exact congrArg Subtype.val (congrFun hxy i)
      · intro l
        refine ⟨⟨fun i => (l i).1,
          GlobalTheory.PurityProd.isIntegral_of_forall_apply (fun i => (l i).1) fun i => (l i).2⟩, ?_⟩
        funext i
        rfl)

theorem etale_integralClosure_pi : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (E : ι → Type) [∀ i, CommRing (E i)]
    [∀ i, Algebra R (E i)], (∀ i, Algebra.Etale R (integralClosure R (E i))) →
    Algebra.Etale R (integralClosure R (∀ i, E i)) := by
  intro R _ ι _ E _ _ h
  haveI : Algebra.Etale R (∀ i, integralClosure R (E i)) := inferInstance
  exact Algebra.Etale.of_equiv (integralClosurePiEquiv R ι E).symm

end GlobalTheory.PiClosure
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosurePiOfEtaleStatement

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etale_integralClosure_pi_of_etale : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (E : ι → Type) [∀ i, CommRing (E i)]
    [∀ i, Algebra R (E i)], (∀ i, Algebra.Etale R (integralClosure R (E i))) →
    Algebra.Etale R (integralClosure R (∀ i, E i)) := by
  first | (exact @GlobalTheory.PiClosure.etale_integralClosure_pi) | (exact GlobalTheory.PiClosure.etale_integralClosure_pi) | (intros; apply GlobalTheory.PiClosure.etale_integralClosure_pi  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationIdxDvdOfGaloisDegreeDvdUnitDvr

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.RamGalDVR

theorem isSeparable_of_natCast_finrank_ne_zero' {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (h : (Module.finrank F E : F) ≠ 0) : Algebra.IsSeparable F E := by
  refine ⟨fun x => ?_⟩
  have hint : IsIntegral F x := IsIntegral.of_finite F x
  have hdvd := minpoly.degree_dvd hint
  show (minpoly F x).Separable
  rw [Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hint)]
  intro hd
  set n := (minpoly F x).natDegree with hn
  have hpos : 0 < n := minpoly.natDegree_pos hint
  have hc := congrArg (fun p : Polynomial F => p.coeff (n - 1)) hd
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hc
  rw [Nat.sub_add_cancel hpos] at hc
  have hlead : (minpoly F x).coeff n = 1 := minpoly.monic hint
  rw [hlead, one_mul] at hc
  have hn0 : (n : F) = 0 := by
    have : ((n - 1 : ℕ) : F) + 1 = ((n - 1 + 1 : ℕ) : F) := by push_cast; ring
    rw [this, Nat.sub_add_cancel hpos] at hc
    exact hc
  obtain ⟨c, hc'⟩ := hdvd
  exact h (by rw [hc', Nat.cast_mul, hn0, zero_mul])

theorem isSeparable_of_isField {F E : Type*} [CommRing F] [CommRing E] [Algebra F E]
    [Module.Finite F E] (hF : IsField F) (hE : IsField E)
    (h : (Module.finrank F E : F) ≠ 0) : Algebra.IsSeparable F E := by
  letI := hF.toField
  letI := hE.toField
  exact @isSeparable_of_natCast_finrank_ne_zero' F E _ _ ‹Algebra F E› ‹Module.Finite F E› h

theorem ramGal : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Field K] [Algebra S K]
    [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [IsGalois K L] (q : ℕ), 0 < q → IsUnit (q : S) →
    Module.finrank K L ∣ q →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ q) ∧
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ q _ hq hdeg
  set B := integralClosure S L
  have : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have : Module.Finite S B := IsIntegralClosure.finite S K L B
  have : IsGaloisGroup (L ≃ₐ[K] L) S B := IsGaloisGroup.of_isFractionRing _ _ _ K L
  have hinj : Function.Injective (algebraMap S L) := by
    rw [IsScalarTower.algebraMap_eq S K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective S K)
  have : FaithfulSMul S B :=
    (faithfulSMul_iff_algebraMap_injective S _).2 (fun a b h => hinj (congrArg Subtype.val h))
  have : Module.Flat S B :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (maximalIdeal S) B (L ≃ₐ[K] L)
  rw [IsGalois.card_aut_eq_finrank] at hfund
  have hef : Ideal.ramificationIdxIn (maximalIdeal S) B * Ideal.inertiaDegIn (maximalIdeal S) B ∣ q :=
    (Dvd.intro_left _ hfund).trans hdeg
  have hlies : ∀ P : Ideal B, P.IsMaximal → P.LiesOver (maximalIdeal S) := by
    intro P hP
    refine ⟨?_⟩
    have : (P.under S).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
    exact (IsLocalRing.eq_maximalIdeal this).symm
  refine ⟨fun P hP => ?_, fun P hP _ => ?_⟩
  · have := hlies P hP
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal S) P (L ≃ₐ[K] L)]
    exact (Dvd.intro _ rfl).trans hef
  · have := hP
    have : (maximalIdeal S).IsMaximal := IsLocalRing.maximalIdeal.isMaximal S
    have hf : Module.finrank (S ⧸ maximalIdeal S) (B ⧸ P) ∣ q := by
      rw [← Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal S) P,
        ← Ideal.inertiaDegIn_eq_inertiaDeg (maximalIdeal S) P (L ≃ₐ[K] L)]
      exact (Dvd.intro_left _ rfl).trans hef
    have : Module.Finite S (B ⧸ P) := inferInstance
    have : Module.Finite (S ⧸ maximalIdeal S) (B ⧸ P) :=
      Module.Finite.of_restrictScalars_finite S _ _
    refine isSeparable_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 inferInstance)
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hP) ?_
    obtain ⟨c, hc⟩ := hf
    intro h0
    have hu : IsUnit ((q : S) : S ⧸ maximalIdeal S) := hq.map (Ideal.Quotient.mk _)
    rw [map_natCast, hc, Nat.cast_mul, h0, zero_mul] at hu
    exact not_isUnit_zero hu

end GlobalTheory.RamGalDVR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationIdxDvdOfGaloisDegreeDvdUnitDvrStatement

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.ramificationIdx_dvd_of_galois_degree_dvd_unit_dvr : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Field K] [Algebra S K]
    [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [IsGalois K L] (q : ℕ), 0 < q → IsUnit (q : S) →
    Module.finrank K L ∣ q →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ q) ∧
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) := by
  first | (exact @GlobalTheory.RamGalDVR.ramGal) | (exact GlobalTheory.RamGalDVR.ramGal) | (intros; apply GlobalTheory.RamGalDVR.ramGal  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.M2ModelEstablished

section

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AbhHeightOne

theorem closureEtaleAt_of_etale_integralClosure_localization : ∀ (A₁ R₁ D₁ : Type) [CommRing A₁] [CommRing R₁] [Algebra A₁ R₁] [CommRing D₁]
    [Algebra (GlobalTheory.LocAcyc.GenFib A₁ R₁) D₁] (P₁ : Ideal R₁) [P₁.IsPrime],
    (letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ D₁).toAlgebra;
      Algebra.Etale (Localization.AtPrime P₁)
        (integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] D₁))) →
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ R₁ D₁ P₁ := by
  intro A₁ R₁ D₁ _ _ _ _ _ P₁ _ h
  letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ D₁).toAlgebra
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A₁ R₁ D₁
  unfold GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt
  let e : GlobalTheory.KeyOriginNoeth.closure A₁ R₁ D₁ ≃ₐ[R₁] integralClosure R₁ D₁ :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hb := TensorProduct.toIntegralClosure_bijective_of_isLocalization (R := R₁)
    (S := Localization.AtPrime P₁) (B := D₁) P₁.primeCompl
  let Φ : Localization.AtPrime P₁ ⊗[R₁] GlobalTheory.KeyOriginNoeth.closure A₁ R₁ D₁ ≃ₐ[Localization.AtPrime P₁]
      integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] D₁) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl e).trans (AlgEquiv.ofBijective _ hb)
  exact Algebra.Etale.of_equiv Φ.symm

theorem etale_integralClosure_of_torsor_field : ∀ (S S₁ K K₁ : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    ∀ (M : Type) [CommRing M] [Algebra K M] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)),
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] M)) := by
  intro S S₁ K K₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinj q hq hqu π hπ y hy M _ _ act htor
  obtain ⟨ι, _, L, _, _, hfd, hgal, hdeg, ⟨e⟩⟩ := GlobalTheory.T.zmodTorsor_field_eq_prod_galois K M q act hq htor
  have hi : ∀ i, Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] L i)) := fun i => by
    letI : Algebra S (L i) := ((algebraMap K (L i)).comp (algebraMap S K)).toAlgebra
    haveI : IsScalarTower S K (L i) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI := hfd i
    haveI := hgal i
    obtain ⟨hram, hsep⟩ := GlobalTheory.T.ramificationIdx_dvd_of_galois_degree_dvd_unit_dvr S K (L i) q hq hqu (hdeg i)
    exact GlobalTheory.T.abhyankar_etale_integralClosure_root_uniformizer S S₁ K K₁ (L i) hinj q hq hqu π hπ y hy hram hsep
  classical
  haveI := GlobalTheory.T.etale_integralClosure_pi_of_etale S₁ ι (fun i => K₁ ⊗[K] L i) hi
  let Ψ : K₁ ⊗[K] M ≃ₐ[K₁] ∀ i, K₁ ⊗[K] L i :=
    (Algebra.TensorProduct.congr AlgEquiv.refl e).trans (Algebra.TensorProduct.piRight K K₁ K₁ L)
  exact Algebra.Etale.of_equiv (Ψ.restrictScalars S₁).symm.mapIntegralClosure

theorem closureEtaleAt_of_root_of_uniformiser : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R],
    Function.Injective (algebraMap A R) →
    ∀ (A₁ R₁ : Type) [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [Algebra A₁ R₁],
    Function.Injective (algebraMap A₁ R₁) →
    ∀ (f : A →+* A₁), Function.Injective f → ∀ (φ : R →+* R₁),
    φ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp φ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA] (q : ℕ)
      (act : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    0 < q → IsUnit (q : A) → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q act →
    ∀ (P₁ : Ideal R₁) [P₁.IsPrime],
    IsDiscreteValuationRing (Localization.AtPrime P₁) →
    IsDiscreteValuationRing (Localization.AtPrime (P₁.comap φ)) →
    ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) →
    ∀ y : R₁, y ^ q = φ (algebraMap A R π) →
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ R₁ (GlobalTheory.KeyOriginBC.BC β DA) P₁ := by
  intro A R _ _ _ _ _ hAR A₁ R₁ _ _ _ _ _ hA₁R₁ f hf φ hφ β hβ DA _ _ q act hq hqu htor P₁ _ hd₁ hd π hπ y hy
  exact closureEtaleAt_of_etale_integralClosure_localization A₁ R₁ _ P₁ (GlobalTheory.T.etale_integralClosure_torsor_of_fraction_fields etale_integralClosure_of_torsor_field A R hAR A₁ R₁ hA₁R₁ f hf φ hφ β hβ DA q act hq hqu htor P₁ hd₁ hd π hπ y hy)

end GlobalTheory.AbhHeightOne
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreBaseChangeInjective

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.generic_fibre_base_change_injective : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R],
    Function.Injective (algebraMap A R) →
    ∀ (A₁ R₁ : Type) [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [Algebra A₁ R₁],
    Function.Injective (algebraMap A₁ R₁) →
    ∀ (f : A →+* A₁), Function.Injective f → ∀ (φ : R →+* R₁),
    φ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp φ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA] (q : ℕ)
      (act : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    0 < q → IsUnit (q : A) → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q act →
    ∀ (P₁ : Ideal R₁) [P₁.IsPrime],
    IsDiscreteValuationRing (Localization.AtPrime P₁) →
    IsDiscreteValuationRing (Localization.AtPrime (P₁.comap φ)) →
    ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) →
    ∀ y : R₁, y ^ q = φ (algebraMap A R π) →
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ R₁ (GlobalTheory.KeyOriginBC.BC β DA) P₁ := by
  first | (exact @GlobalTheory.AbhHeightOne.closureEtaleAt_of_root_of_uniformiser) | (exact GlobalTheory.AbhHeightOne.closureEtaleAt_of_root_of_uniformiser) | (intros; apply GlobalTheory.AbhHeightOne.closureEtaleAt_of_root_of_uniformiser  <;> assumption)
end
end
