module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomAdicCompletionExtend
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfMaximalIdealLeRadicalCompleteNakayamaStatement
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CohenStructureFiniteOverNormalCompleteSubring
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfMemClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteOfRigidAtB
import Mathlib.Tactic.Linter.Style
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveFiniteOfUniqueEmbeddingCompleteNormalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegResidueFieldOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GDimcpl
import Mathlib.RingTheory.KrullDimension.Field
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomAdicCompletionExtendStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_comp : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (φ : A →+* R), IsLocalHom φ → ∃ ψ : AdicCompletion (maximalIdeal A) A →+* R, IsLocalHom ψ ∧ ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) = φ := by
  first | exact @GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend | exact GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend | (intros; apply GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimEqLocalDomain

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory


open IsLocalRing in
theorem _root_.GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain :
    ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R]
      [IsLocalRing R] (ψ : B →+* R), ψ.Finite → ringKrullDim R = ringKrullDim B →
      Function.Injective ψ := by
  intro B R _ _ _ _ _ _ ψ hψ hdim
  letI : Algebra B R := ψ.toAlgebra
  haveI : Module.Finite B R := hψ
  have hlt : ringKrullDim B < ⊤ := ringKrullDim_lt_top
  have hne : ringKrullDim B ≠ ⊥ := fun h =>
    (WithBot.bot_lt_coe (0 : ℕ∞)).not_ge (h ▸ (ringKrullDim_nonneg_of_nontrivial (R := B)))
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hne
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℕ∞) = m := by
    refine ENat.ne_top_iff_exists.mp ?_
    rintro rfl
    exact hlt.ne hm.symm
  exact _root_.GlobalTheory.CohenStructure.injective_of_ringKrullDim_eq (A := B) (S := R) hm.symm
    (hdim.trans hm.symm)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimEqLocalDomainStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.injective_of_finite_of_ringKrullDim_eq_localDomain : ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R] [IsLocalRing R] (ψ : B →+* R), ψ.Finite → ringKrullDim R = ringKrullDim B → Function.Injective ψ := by
  first | exact @GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain | exact GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain | (intros; apply GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteTautologicalChartClosedPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem quasiFinite_of_tautB : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → (∀ p : Sp (ChartRing k m e), ξ p = ξ (closedPoint _) → p = closedPoint _) ∧ ((residue (ChartRing k m e)).comp (Scheme.stalkClosedPointTo ξ).hom).Finite := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU hS k _ m e C hC ξ hξ
  obtain ⟨⟨_, _, _, _, ⟨_, _, hft⟩, _⟩, ⟨n, s, ε, τ₀, h1, h2, h3, h4, hP⟩⟩ := hC
  have hb : ξ ≫ π ≫ zs = spMap C.b := by
    refine GlobalTheory.ChartQF.eq_spMap_of_injective (algebraMap _ (FractionRing (ChartRing k m e)))
      (IsFractionRing.injective _ _) _ _ ?_
    have e1 : i ≫ zs = pullback.snd _ _ := hU.1.2.2.2.2.1
    have e2 : j ≫ π = i := hU.2.2.2.2.1.2.2.2.2.1
    show jK _ ≫ _ = jK _ ≫ _
    rw [← Category.assoc, ← hξ, Category.assoc, reassoc_of% e2, e1, C.y_over]
  exact GlobalTheory.ChartQF.quasiFinite_of_pointRigid ξ (π ≫ zs) C.b hb hft fun K _ _ ev k₀ hk hemb hq hd =>
    hP K ev k₀ hk hemb (hS _ C (GlobalTheory.ChartQF.base_chartRing C.toFam) ξ hξ n s ε τ₀ h1 h2 h3 h4 K ev k₀ hk hq hd)

end GlobalTheory.UCanon
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteTautologicalChartClosedPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.quasiFinite_tautologicalChart_closedPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → (∀ p : Sp (ChartRing k m e), ξ p = ξ (closedPoint _) → p = closedPoint _) ∧ ((residue (ChartRing k m e)).comp (Scheme.stalkClosedPointTo ξ).hom).Finite := by
  first | exact @GlobalTheory.UCanon.quasiFinite_of_tautB | exact GlobalTheory.UCanon.quasiFinite_of_tautB | (intros; apply GlobalTheory.UCanon.quasiFinite_of_tautB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosedStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.adicCompletion_isDomain_and_isIntegrallyClosed : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], IsDomain (AdicCompletion (maximalIdeal A) A) ∧ IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) := by
  first | exact @GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed | exact GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed | (intros; apply GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartIsEtaleCompletionLocalRing

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TautEtaleB

theorem isEtaleCompletion_of_forall_eq_inj (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R]
    (hAd : IsDomain (AdicCompletion (maximalIdeal A) A))
    (hAn : IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A))
    (hR : IsAdicComplete (maximalIdeal R) R) (φ : A →+* R) (hφ : IsLocalHom φ)
    (hprim : maximalIdeal R ≤ ((maximalIdeal A).map φ).radical)
    (hres : ((residue R).comp φ).Finite) (hdim : ringKrullDim R = ringKrullDim A)
    (hinj : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R']
      [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' →
      ∀ f g : R →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g →
        f.comp φ = g.comp φ → f = g) :
    GlobalTheory.Toroidal.IsEtaleCompletion φ := by
  let B := AdicCompletion (maximalIdeal A) A
  haveI : IsNoetherianRing B := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  obtain ⟨ψ, hψl, hψ⟩ := GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_comp A R hR φ hφ
  have hmap : (maximalIdeal B).map ψ = (maximalIdeal A).map φ := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hψ]
  have hresψ : ((residue R).comp ψ).Finite := by
    have e : ((residue R).comp ψ).comp (algebraMap A B) = (residue R).comp φ := by
      rw [RingHom.comp_assoc, hψ]
    exact RingHom.Finite.of_comp_finite (e ▸ hres)
  have hfin : ψ.Finite := GlobalTheory.T.finite_of_maximalIdeal_le_radical_complete_nakayama B R ψ inferInstance hψl (hmap ▸ hprim) hresψ
  have hdB : ringKrullDim R = ringKrullDim B := by rw [hdim, UpperTheory.V.CA.g_dimcpl]
  have hi : Function.Injective ψ := GlobalTheory.T.injective_of_finite_of_ringKrullDim_eq_localDomain B R ψ hfin hdB
  have hs : Function.Surjective ψ := GlobalTheory.T.surjective_finite_of_unique_embedding_complete_normal B R ψ inferInstance hi hfin
    (fun R' _ _ _ _ _ _ hR' f g hf' hg' hf hg h => hinj R' hR' f g hf' hg' hf hg (by
      rw [← hψ, ← RingHom.comp_assoc, h, RingHom.comp_assoc]))
  refine ⟨?_, ?_, hres⟩
  · rw [← hψ]
    refine RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian _)) ?_
    exact RingHom.Flat.of_bijective ⟨hi, hs⟩
  · rw [← hmap]
    exact map_maximalIdeal_of_surjective ψ hs

theorem charZero_essFiniteType_stalk (K : Type) [Field K] [CharZero K] [FiniteDimensional ℚ K] {X : Scheme.{0}}
    (f : X ⟶ Sp K) [LocallyOfFiniteType f] (x : X) :
    CharZero (X.presheaf.stalk x) ∧ Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := by
  let y : PrimeSpectrum K := f x
  letI : Algebra K ((Sp K).presheaf.stalk (f x)) := StructureSheaf.stalkAlgebra _ y
  haveI : IsLocalization.AtPrime ((Sp K).presheaf.stalk (f x)) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := algebraMap K ((Sp K).presheaf.stalk (f x))
  have h₁ : (f.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap f x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  have hσ : Function.Injective ((f.stalkMap x).hom.comp φ) := RingHom.injective _
  refine ⟨charZero_of_injective_ringHom hσ, ?_⟩
  have hQ : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  have hK : Algebra.EssFiniteType ℤ K := Algebra.EssFiniteType.comp ℤ ℚ K
  refine RingHom.essFiniteType_algebraMap.1 ?_
  convert (RingHom.essFiniteType_algebraMap.2 hK).comp (h₂.comp h₁) using 1
  exact Subsingleton.elim _ _

theorem exists_fracMap {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (ψ : A →+* B)
    (hψ : Function.Injective ψ) : ∃ fK : FractionRing A →+* FractionRing B, spMap fK ≫ jK A = jK B ≫ spMap ψ := by
  have hg : Function.Injective ((algebraMap B (FractionRing B)).comp ψ) :=
    (IsFractionRing.injective B (FractionRing B)).comp hψ
  let fK : FractionRing A →+* FractionRing B :=
    IsFractionRing.lift (K := FractionRing A) (L := FractionRing B) (g := (algebraMap B (FractionRing B)).comp ψ) hg
  have e0 : fK.comp (algebraMap A (FractionRing A)) = (algebraMap B (FractionRing B)).comp ψ := by
    ext x
    rw [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (K := FractionRing A) (L := FractionRing B) hg x
  refine ⟨fK, ?_⟩
  have e1 : CommRingCat.ofHom (algebraMap A (FractionRing A)) ≫ CommRingCat.ofHom fK =
      CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap B (FractionRing B)) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e0]
  have e2 := congrArg Spec.map e1
  rw [Spec.map_comp, Spec.map_comp] at e2
  exact e2

theorem tautB_isEtaleCompletion : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep k _ m e C hT ξ hξ
  obtain ⟨hqf, hfin⟩ := GlobalTheory.T.quasiFinite_tautologicalChart_closedPoint Xo c φ hpq hpf hns zs i OZ N d J π j BD hU hSep C hT ξ hξ
  have hdimS := ringKrullDim_stalk_eq_of_isTaut hU C hT.1 ξ hξ hfin
  haveI hcF : CharZero (ChartRing k m e) := (C.b.charZero_iff C.b.injective).1 inferInstance
  have hAdm := GlobalTheory.MumfordChart.admissibleBase_chartRing k m e
  haveI : IsNoetherianRing (ChartRing k m e) := hAdm.1
  haveI : IsIntegrallyClosed (ChartRing k m e) := hAdm.2.2.1
  have hRc : IsAdicComplete (maximalIdeal (ChartRing k m e)) (ChartRing k m e) := hAdm.2.2.2
  have hdimR : ringKrullDim (ChartRing k m e) = ((m + e : ℕ) : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries k (Fin m ⊕ Fin e), ringKrullDim_eq_zero_of_field]
    simp [Nat.card_sum]
  obtain ⟨⟨-, -, -, -, hizs, -⟩, -, -, -, ⟨⟨hnorm, -⟩, hproj, -, -, hji, -⟩, -⟩ := hU
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI := c.fin
  set x := ξ (closedPoint (ChartRing k m e)) with hx
  haveI : IsDomain (S.presheaf.stalk x) := hnorm.isDomain_stalk x
  haveI : IsIntegrallyClosed (S.presheaf.stalk x) := hnorm.isIntegrallyClosed_stalk x
  obtain ⟨hc0, hess⟩ := charZero_essFiniteType_stalk c.F (π ≫ zs) x
  haveI := hc0
  haveI := hess
  haveI : IsNoetherianRing (S.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  obtain ⟨hAd, hAn⟩ := GlobalTheory.T.adicCompletion_isDomain_and_isIntegrallyClosed (S.presheaf.stalk x)
  set ψ := (Scheme.stalkClosedPointTo ξ).hom with hψ
  have eξ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have hpt : ∀ p : Sp (ChartRing k m e), ξ p = S.fromSpecStalk x (Spec.map (Scheme.stalkClosedPointTo ξ) p) := by
    intro p
    conv_lhs => rw [← eξ]
    rfl
  have hprim : maximalIdeal (ChartRing k m e) ≤ ((maximalIdeal (S.presheaf.stalk x)).map ψ).radical := by
    intro r hr
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hle, hP⟩
    have hc : Ideal.comap ψ P = maximalIdeal (S.presheaf.stalk x) :=
      ((maximalIdeal.isMaximal _).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.1 hle)).symm
    have hq : (⟨P, hP⟩ : Sp (ChartRing k m e)) = closedPoint (ChartRing k m e) := by
      refine hqf _ ((hpt _).trans (Eq.trans ?_ (hpt (closedPoint _)).symm))
      congr 1
      refine PrimeSpectrum.ext ?_
      show Ideal.comap ψ P = Ideal.comap ψ (maximalIdeal (ChartRing k m e))
      rw [hc]
      refine le_antisymm ?_ (le_maximalIdeal (Ideal.comap_ne_top _ (maximalIdeal.isMaximal _).ne_top))
      intro a ha
      exact map_nonunit ψ a ha
    have hP' : P = maximalIdeal (ChartRing k m e) := congrArg PrimeSpectrum.asIdeal hq
    rw [hP']
    exact hr
  have hinj : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R']
      [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' →
      ∀ f g : ChartRing k m e →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g →
        f.comp ψ = g.comp ψ → f = g := by
    intro R' _ _ _ _ _ _ hR' f g hfi hgi hfl hgl hfg
    have hB : GlobalTheory.Mum.Base R' := ⟨⟨inferInstance, inferInstance, inferInstance, hR'⟩, inferInstance⟩
    obtain ⟨fK, hfK⟩ := exists_fracMap f hfi
    obtain ⟨gK, hgK⟩ := exists_fracMap g hgi
    obtain ⟨-, -, -, hInj, -⟩ := hT.1
    refine hInj R' hB f g hfi hgi hfl hgl (spMap fK) (spMap gK) hfK hgK ?_
    have hsp : spMap f ≫ Spec.map (Scheme.stalkClosedPointTo ξ) = spMap g ≫ Spec.map (Scheme.stalkClosedPointTo ξ) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext a
      exact congrArg (fun h : S.presheaf.stalk x →+* R' => h a) hfg
    have hfξ : spMap f ≫ ξ = spMap g ≫ ξ := by
      calc spMap f ≫ ξ = spMap f ≫ (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ S.fromSpecStalk x) := by rw [eξ]
        _ = spMap g ≫ (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ S.fromSpecStalk x) := by
          rw [← Category.assoc, hsp, Category.assoc]
        _ = spMap g ≫ ξ := by rw [eξ]
    rw [← cancel_mono j, Category.assoc, Category.assoc, hξ, ← Category.assoc, ← Category.assoc, hfK, hgK,
      Category.assoc, Category.assoc, hfξ]
  exact isEtaleCompletion_of_forall_eq_inj (S.presheaf.stalk x) (ChartRing k m e) hAd hAn hRc ψ inferInstance hprim hfin
    (by rw [hdimR, hdimS]) hinj

end GlobalTheory.TautEtaleB
end
end
