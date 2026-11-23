module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalChartResidueFieldDimensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalDataRigidAlongStratum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyHasPointRigidCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBaseInjectionsAgreeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalInjectionsAgreeCanonicalFamilyCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPointRigidBoundaryFamilyOfRigidCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenPartClassifiedMonomialBoundaryFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteOfRigidAtB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalFamilyThroughDegeneratingFamilyStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfIdlAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealEqSpanMonomialOfOrdersAlongCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialBoundaryFamilyPullUnitaryTraitFormStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalDataRigidAlongStratumStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.canonical_data_rigid_along_stratum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), GlobalTheory.RigChart.IsRigid C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) := by
  first | exact @GlobalTheory.UCanon.isRigid_canon | exact GlobalTheory.UCanon.isRigid_canon | (intros; apply GlobalTheory.UCanon.isRigid_canon <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyLocalInjectionsEqSamePoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.inj_of_canon : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R), Canon C → Inj C := by
  intro E _ _ _ H Dw l Xo c φ h₁ h₂ h₃ R _ _ _ hR C Cn R' _ _ _ hR' θ₁ θ₂ i₁ i₂ l₁ l₂ κ₁ κ₂ e₁ e₂ e
  have : IsNoetherianRing R' := hR'.1.1
  refine GlobalTheory.TChart.cuniq _ R R' Cn.ψ Cn.compl θ₁ θ₂ l₁ l₂ (MvPolynomial.ringHom_ext (fun w => ?_) (fun k => ?_))
  · exact RingHom.congr_fun
      (GlobalTheory.T.canonicalFamily_base_injections_agree Xo c φ h₁ h₂ h₃ R hR C Cn R' hR' θ₁ θ₂ i₁ i₂ l₁ l₂ κ₁ κ₂ e₁ e₂ e) w
  · exact GlobalTheory.T.localInjections_agree_canonicalFamily_coordinates Xo c φ h₁ h₂ h₃ R hR C Cn R' hR' θ₁ θ₂ i₁ i₂ l₁ l₂ κ₁ κ₂ e₁ e₂ e k
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyLocalInjectionsEqSamePointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.canonicalFamily_localInjections_eq_same_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R), Canon C → Inj C := by
  first | exact @GlobalTheory.UCanon.inj_of_canon | exact GlobalTheory.UCanon.inj_of_canon | (intros; apply GlobalTheory.UCanon.inj_of_canon <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyIsPointRigidTautologicalChart

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem isTautB_of_canon : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), Canon C → (∃ hm : C.m = m, ∀ i, C.s i = bdParam k m e (Fin.cast hm i)) → IsTautB C := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hnsi k _ m e C hC hms
  obtain ⟨hm, hs⟩ := hms
  have hB : GlobalTheory.Mum.Base (ChartRing k m e) := GlobalTheory.ChartQF.base_chartRing C.toFam
  have hR : HasRigidCoords C := GlobalTheory.T.canonicalFamily_has_pointRigid_coordinates Xo c φ (ChartRing k m e) hB C hC
  obtain ⟨hft, hdim⟩ := GlobalTheory.T.canonicalChart_residueField_dimension Xo c φ C hC
  obtain ⟨N, s, ε, τ₀, h1, h2, h3, h4, -⟩ := id hR
  exact ⟨⟨hm, hs, GlobalTheory.T.openPart_classified_monomialBoundaryFamily Xo c φ _ hB C, GlobalTheory.T.canonicalFamily_localInjections_eq_same_point Xo c φ hpq hfan hnsi _ hB C hC,
    ⟨GlobalTheory.T.canonical_data_rigid_along_stratum Xo c φ _ hB C hC, GlobalTheory.T.isPointRigidBoundaryFamily_of_rigidCoordinates Xo c φ _ C hR, hft⟩, ⟨N, s, ε, τ₀, h1, h2, h3, h4⟩, hdim⟩, hR⟩

end GlobalTheory.UCanon
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyIsPointRigidTautologicalChartStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.canonicalFamily_isPointRigid_tautologicalChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), Canon C → (∃ hm : C.m = m, ∀ i, C.s i = bdParam k m e (Fin.cast hm i)) → IsTautB C := by
  first | exact @GlobalTheory.UCanon.isTautB_of_canon | exact GlobalTheory.UCanon.isTautB_of_canon | (intros; apply GlobalTheory.UCanon.isTautB_of_canon <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionRingMap

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart

theorem bdParam_ne_zero (k : Type) [Field k] (m e : ℕ) (i : Fin m) : bdParam k m e i ≠ 0 := fun h => by
  have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin e) 1)) h
  simp [bdParam, MvPowerSeries.coeff_X] at this

theorem exists_fractionRing_map {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (ψ : A →+* B)
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

theorem exists_lift_normBl {X Z S : Scheme.{0}} (i : X ⟶ Z) (π : S ⟶ Z) (j : X ⟶ S) (J : Z.IdealSheafData)
    (hN : GlobalTheory.Poinc.IsNormBl π J) (hji : j ≫ π = i) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsIntegrallyClosed R] (a : Sp R ⟶ Z) (y : Sp (FractionRing R) ⟶ X) (hy : jK R ≫ a = y ≫ i) (f : R) (hf : f ≠ 0)
    (hJ : idlAlong J a = Ideal.span {f}) : ∃ ξ : Sp R ⟶ S, jK R ≫ ξ = y ≫ j := by
  obtain ⟨-, S₀, π₀, ν, U, hB, hνπ, hfin, -, -, -⟩ := hN
  have hE : FinalTheorems.EffCartier (J.comap a) := GlobalTheory.NormBlLift.effCartier_comap_of_idlAlong J a f hf hJ
  have hEK : FinalTheorems.EffCartier (J.comap (jK R ≫ a)) := by
    refine GlobalTheory.NormBlLift.effCartier_comap_of_idlAlong J (jK R ≫ a) (algebraMap R (FractionRing R) f) ?_ ?_
    · exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf
    · rw [show jK R = spMap (algebraMap R (FractionRing R)) from rfl, GlobalTheory.TraitOrder.idlAlong_comp, hJ,
        Ideal.map_span, Set.image_singleton]
  obtain ⟨b, hb, -⟩ := hB.2 _ a hE
  have hK : (y ≫ j) ≫ ν = jK R ≫ b := by
    refine (hB.2 _ _ hEK).unique ?_ ?_
    · rw [Category.assoc, Category.assoc, hνπ, hji, hy]
    · rw [Category.assoc, hb]
  obtain ⟨c, ⟨hc1, -⟩, -⟩ := GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK
  exact ⟨c, hc1⟩

theorem taut_exists_map : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → ∃ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep k _ m e C hT
  obtain ⟨hm, hs, -⟩ := hT
  have hcF : CharZero (ChartRing k m e) := (C.b.charZero_iff C.b.injective).1 inferInstance
  haveI : CharZero k := (MvPowerSeries.C (σ := Fin m ⊕ Fin e) (R := k)).charZero
  have hAdm := GlobalTheory.MumfordChart.admissibleBase_chartRing k m e
  have hBase : GlobalTheory.Mum.Base (ChartRing k m e) := ⟨hAdm, hcF⟩
  haveI : IsIntegrallyClosed (ChartRing k m e) := hAdm.2.2.1
  obtain ⟨⟨-, -, hi, -, -, -, -⟩, -, hext, ⟨-, -, hval⟩, ⟨hbl, -, -, -, hji, -, -, -⟩, -⟩ := hU
  obtain ⟨ξZ, hξZ, -⟩ := hext _ hBase C.t ⟨C.P⟩ C.y C.gen (spMap C.b) C.y_over.symm
  haveI : Module.Projective (𝓞 E) C.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) C.P.D.toPre.X
  have hPF := hpf C.P.D.toPre.X C.rank
  have hnat : ∀ i, ∃ n : ℕ, φ.evalZ ((l.M' : ℤ) • C.δ i) = n := fun i =>
    hPF.exists_nat (Submodule.smul_mem _ _ (C.cone.mem i)) (fun y => by
      simpa using mul_nonneg (by positivity : (0 : ℤ) ≤ l.M') (C.cone.nonneg i y))
  choose b hb using hnat
  let a : Fin m → ℕ := fun i => d * b (Fin.cast hm.symm i)
  have hprod : ∏ i, bdParam k m e i ^ a i = ∏ i : Fin C.m, C.s i ^ (d * b i) :=
    (Fintype.prod_equiv (finCongr hm) _ _ (fun j => by simp [a, hs j])).symm
  have hI : idlAlong J ξZ = Ideal.span {∏ i, bdParam k m e i ^ a i} := by
    refine GlobalTheory.MonoVal.eq_span_monomial_of_forall_cdvr k m e _ a fun W _ _ _ hW ψ hψi hψl => ?_
    haveI := hW.1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    have hne : ∀ i, ψ (C.s i) ≠ 0 := fun i h0 => by
      have : C.s i = 0 := hψi (h0.trans (map_zero ψ).symm)
      rw [hs i] at this
      exact bdParam_ne_zero k m e _ this
    choose w hw using fun i => IsDiscreteValuationRing.associated_pow_irreducible (hne i) hϖ
    obtain ⟨fK, hκ⟩ := exists_fractionRing_map ψ hψi
    obtain ⟨t, tK, P, h1, h2, be, hbe, hmono, hφ⟩ :=
      GlobalTheory.T.monomialBoundaryFamily_pull_unitaryTrait_form Xo c φ _ hBase C W hW ψ hψi hψl ϖ hϖ w hw (spMap fK) hκ
    obtain ⟨n, hn, hIn⟩ := hval W hW ϖ hϖ (spMap ψ ≫ ξZ) (spMap fK ≫ C.y)
      (by rw [Category.assoc, ← hξZ, ← Category.assoc, hκ, Category.assoc]) t tK h1 h2 P be hbe hmono
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, hIn, hprod, map_prod]
    refine Ideal.span_singleton_eq_span_singleton.2 ?_
    have hnw : n = ∑ i, w i * (d * b i) := by
      have : (n : ℝ) = ∑ i, (w i : ℝ) * (d * b i) := by
        rw [hn, hφ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hb i]; ring
      exact_mod_cast this
    have : Associated (∏ i, ψ (C.s i ^ (d * b i))) (∏ i : Fin C.m, (ϖ ^ w i) ^ (d * b i)) :=
      Associated.prod _ _ _ fun i _ => by rw [map_pow]; exact (hw i).pow_pow
    rw [hnw]
    refine (this.trans ?_).symm
    rw [← Finset.prod_pow_eq_pow_sum]
    simp only [← pow_mul]
    exact Associated.refl _
  have hf0 : ∏ i, bdParam k m e i ^ a i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (bdParam_ne_zero k m e _)
  obtain ⟨ξ, hξ⟩ := exists_lift_normBl i π j J hbl hji _ ξZ C.y hξZ _ hf0 hI
  exact ⟨ξ, hξ.symm⟩

end GlobalTheory.UChart
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalChartVersality

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem spMap_isDominant_of_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : IsDominant (spMap f) :=
  ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hf]
    exact bot_le)⟩

theorem spMap_ext_of_injective {A B : Type} [CommRing A] [IsDomain A] [CommRing B] {S : Scheme.{0}} [S.IsSeparated]
    (f : A →+* B) (hf : Function.Injective f) {a b : Sp A ⟶ S} (h : spMap f ≫ a = spMap f ≫ b) : a = b := by
  haveI := spMap_isDominant_of_injective f hf
  exact ext_of_isDominant_of_isSeparated (terminal.from S) (terminal.hom_ext _ _) (spMap f) h

theorem isSeparated_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    X.IsSeparated := by
  obtain ⟨N, ci, hci, hcis⟩ := h
  haveI := hci
  have : IsSeparated f := by
    rw [← hcis, PSpace.str]
    infer_instance
  exact ⟨by rw [← terminal.comp_from f]; infer_instance⟩

end GlobalTheory.UCanon

namespace GlobalTheory.UCanon

theorem exists_taut_through : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), Nontrivial C.P.D.toPre.X → C.y ≫ j = jK V ≫ ξV → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S) (θ : ChartRing k m e →+* V), IsTautB C₁ ∧ C₁.y ≫ j = jK _ ≫ ξ ∧ IsLocalHom θ ∧ spMap θ ≫ ξ = ξV := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep V _ _ _ hB hac C ξV hnt hCV
  obtain ⟨k, hk, m, e, C₁, θ, ⟨hcan⟩, hpar, hθ, hthr⟩ := GlobalTheory.T.exists_canonical_family_through_degenerating_family Xo c φ V hB hac C hnt
  letI := hk
  have hT : IsTautB C₁ := GlobalTheory.T.canonicalFamily_isPointRigid_tautologicalChart Xo c φ hpq hpf hns C₁ hcan hpar
  obtain ⟨ξ, hξ⟩ := GlobalTheory.UChart.taut_exists_map Xo c φ hpq hpf hns zs i OZ N d J π j BD hU hSep C₁ hT.1
  haveI : S.IsSeparated := isSeparated_of_projOver hU.2.2.2.2.1.2.1
  refine ⟨k, hk, m, e, C₁, ξ, θ, hT, hξ, hθ, ?_⟩
  obtain ⟨yo, κ, hgen, hκ, hκy⟩ := hthr

  obtain ⟨hm, hs⟩ := hpar
  have hne : (∏ i, C₁.s i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    rw [hs i]
    exact bdParam_ne_zero k m e _
  set L := Localization.Away (∏ i, C₁.s i)
  have hle : Submonoid.powers (∏ i, C₁.s i) ≤ nonZeroDivisors (ChartRing k m e) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hne
  haveI : IsDomain L := IsLocalization.isDomain_localization hle
  have hu : IsUnit (algebraMap (ChartRing k m e) (FractionRing (ChartRing k m e)) (∏ i, C₁.s i)) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hne)
  let gR : L →+* FractionRing (ChartRing k m e) := IsLocalization.Away.lift (∏ i, C₁.s i) hu
  have hgR : gR.comp (algebraMap (ChartRing k m e) L) = algebraMap (ChartRing k m e) (FractionRing (ChartRing k m e)) :=
    IsLocalization.Away.lift_comp (∏ i, C₁.s i) hu
  have hinj : Function.Injective gR := by
    refine (IsLocalization.lift_injective_iff _).2 fun x y => ?_
    rw [(IsLocalization.injective L hle).eq_iff, (IsFractionRing.injective (ChartRing k m e) (FractionRing (ChartRing k m e))).eq_iff]
  have hg : spMap gR ≫ spMap (algebraMap (ChartRing k m e) L) = jK (ChartRing k m e) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hgR]

  have hopen : spMap (algebraMap (ChartRing k m e) L) ≫ ξ = yo ≫ j := by
    refine spMap_ext_of_injective gR hinj ?_
    rw [← Category.assoc, hg, ← hξ, ← Category.assoc, hgen _ hg]
  refine spMap_ext_of_injective (algebraMap V (FractionRing V)) (IsFractionRing.injective _ _) ?_
  change jK V ≫ _ = jK V ≫ _
  rw [← Category.assoc, ← hκ, Category.assoc, hopen, ← Category.assoc, hκy, hCV]

end GlobalTheory.UCanon
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalChartVersalityStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_tautological_chart_versality : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), Nontrivial C.P.D.toPre.X → C.y ≫ j = jK V ≫ ξV → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S) (θ : ChartRing k m e →+* V), IsTautB C₁ ∧ C₁.y ≫ j = jK _ ≫ ξ ∧ IsLocalHom θ ∧ spMap θ ≫ ξ = ξV := by
  first | exact @GlobalTheory.UCanon.exists_taut_through | exact GlobalTheory.UCanon.exists_taut_through | (intros; apply GlobalTheory.UCanon.exists_taut_through <;> assumption)
end
end
