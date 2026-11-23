module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineLeOrDisjoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralExtIsAlgClosedResidueField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
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
import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.PowerSeries.Inverse
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoFamThrough
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialBoundaryFamilyPullUnitaryTraitForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenPartClassifiedMonomialBoundaryFamilyStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalChartVersalityStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperRestrictOfPsiUnitOn

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section
namespace GlobalTheory.UnifProperChar
section Inertia

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.BXOf GlobalTheory.UnramTorsion

attribute [local instance] gtGroup

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

end Inertia

section Reduction

open GlobalTheory.Published GlobalTheory.Published.AbVarRed

end Reduction

theorem exists_dvr_centre (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) [I.IsPrime] :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : R →+* V),
      IsAlgClosed (ResidueField V) ∧ Function.Injective φ ∧ (maximalIdeal V).comap φ = I := by
  obtain ⟨V, _, _, _, φ, hφ, hc⟩ : ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (φ : R →+* V), Function.Injective φ ∧ (maximalIdeal V).comap φ = I := by
    rcases eq_or_ne I ⊥ with rfl | hI
    · let K := FractionRing R
      let φ : R →+* PowerSeries K := (PowerSeries.C (R := K)).comp (algebraMap R K)
      have hφ : Function.Injective φ := PowerSeries.C_injective.comp (IsFractionRing.injective R K)
      refine ⟨PowerSeries K, inferInstance, inferInstance, inferInstance, φ, hφ, ?_⟩
      refine eq_bot_iff.2 fun r hr => ?_
      rw [Ideal.mem_comap, PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton,
        PowerSeries.X_dvd_iff] at hr
      have : algebraMap R K r = 0 := by simpa [φ] using hr
      exact (Ideal.mem_bot).2 (IsFractionRing.injective R K (this.trans (map_zero _).symm))
    · obtain ⟨V, _, _, hV, -, φ, h1, h2⟩ :=
        exists_complete_discreteValuationRing_of_prime_lt ⊥ I (bot_lt_iff_ne_bot.2 hI)
      exact ⟨V, inferInstance, inferInstance, hV, φ, (RingHom.injective_iff_ker_eq_bot φ).2 h1, h2⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨V', _, _, _, _, h1, h2, -, h3⟩ := GlobalTheory.ClosedResidueExt.exists_unramified_ext V hπ
  refine ⟨V', inferInstance, inferInstance, inferInstance, (algebraMap V V').comp φ, h3, h1.comp hφ, ?_⟩
  rw [← Ideal.comap_comap, ← hc]
  congr 1
  exact eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (algebraMap_isIntegral_iff.mpr h2) (maximalIdeal V'))

end GlobalTheory.UnifProperChar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrAlgClosedResidueInjectiveLocal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompleteClosedDvr

theorem exists_complete_dvr_isAlgClosed : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], ¬ IsField V → Nonempty (ℚ →+* V) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ρ : V →+* W), IsAdicComplete (maximalIdeal W) W ∧ IsAlgClosed (ResidueField W) ∧ Function.Injective ρ ∧ IsLocalHom ρ := by
  intro V _ _ _ _ _ _
  obtain ⟨D, _, _, _, φ, hac, hinj, hc⟩ := GlobalTheory.UnifProperChar.exists_dvr_centre V (maximalIdeal V)
  have : IsLocalHom φ := ((IsLocalRing.local_hom_tfae φ).out 1 5).mpr hc
  have hb := AdicCompletion.residueField_map_bijective_of_fg (R := D)
    (maximalIdeal D).fg_of_isNoetherianRing
  refine ⟨AdicCompletion (maximalIdeal D) D, inferInstance, inferInstance, inferInstance,
    (algebraMap D _).comp φ, inferInstance, ?_,
    (GlobalTheory.injective_and_isLocalHom_adicCompletion_comp φ hinj).1,
    (GlobalTheory.injective_and_isLocalHom_adicCompletion_comp φ hinj).2⟩
  exact IsAlgClosed.of_ringEquiv (ResidueField D) _ (RingEquiv.ofBijective _ hb)

end GlobalTheory.CompleteClosedDvr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrAlgClosedResidueInjectiveLocalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_complete_dvr_algClosed_residue_injective_local : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], ¬ IsField V → Nonempty (ℚ →+* V) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ρ : V →+* W), IsAdicComplete (maximalIdeal W) W ∧ IsAlgClosed (ResidueField W) ∧ Function.Injective ρ ∧ IsLocalHom ρ := by
  first | exact @GlobalTheory.CompleteClosedDvr.exists_complete_dvr_isAlgClosed | exact GlobalTheory.CompleteClosedDvr.exists_complete_dvr_isAlgClosed | (intros; apply GlobalTheory.CompleteClosedDvr.exists_complete_dvr_isAlgClosed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegeneratingMonomialFamilyAlgClosedResidue

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChartGeo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)}

theorem nontrivial_of_not_mem_range {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.Mum.Base V)
    (C : MonoFam Xo c φ V) {S T : Scheme.{0}} (s : S ⟶ T) [IsSeparated s] (j : Xo.XF c ⟶ S) (ξV : Sp V ⟶ S)
    (hs : ∀ f g : Sp V ⟶ S, jK V ≫ f = jK V ≫ g → f ≫ s = g ≫ s)
    (hy : C.y ≫ j = jK V ≫ ξV) (hx : ξV (closedPoint V) ∉ Set.range j) : Nontrivial C.P.D.toPre.X := by
  by_contra hX
  rw [not_nontrivial_iff_subsingleton] at hX
  haveI : IsEmpty (Fin C.m) := ⟨fun i =>
    C.cone.linearIndependent.ne_zero i (LinearMap.ext₂ fun a b => by
      rw [Subsingleton.elim a 0]; simp)⟩
  have hprod : ∏ i, C.s i = 1 := by simp [Finset.univ_eq_empty]
  obtain ⟨yo, -, -, -, hg⟩ := GlobalTheory.T.openPart_classified_monomialBoundaryFamily Xo c φ V hV C
  let A := Localization.Away (∏ i, C.s i)
  let e : V ≃ₐ[V] A := IsLocalization.atUnit V A (∏ i, C.s i) (by rw [hprod]; exact isUnit_one)
  let h : A →+* V := e.symm.toRingEquiv.toRingHom
  have hcomp : h.comp (algebraMap V A) = RingHom.id V := by
    ext r
    show e.symm (algebraMap V A r) = r
    exact e.symm.commutes r
  have hid : spMap h ≫ spMap (algebraMap V A) = 𝟙 _ := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    exact Spec.map_id _
  have hψ : jK V ≫ spMap h ≫ yo = C.y := by
    rw [← Category.assoc]
    exact hg _ (by rw [Category.assoc, hid, Category.comp_id])
  have hgen : jK V ≫ (spMap h ≫ yo) ≫ j = jK V ≫ ξV := by
    rw [← Category.assoc, hψ, hy]
  haveI : IsDominant (jK V) := (GlobalTheory.Mum.Modif.self V).dominant
  have heq : (spMap h ≫ yo) ≫ j = ξV :=
    ext_of_isDominant_of_isSeparated s (hs _ _ hgen) (jK V) hgen
  exact hx ⟨(spMap h ≫ yo) (closedPoint V), by
    show ((spMap h ≫ yo) ≫ j) (closedPoint V) = _
    rw [heq]⟩

end GlobalTheory.UChartGeo

namespace GlobalTheory.UChartGeo



theorem exists_monoFam_algClosed : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), GlobalTheory.Mum.Base V ∧ IsAlgClosed (ResidueField V) ∧ Nontrivial C.P.D.toPre.X ∧ C.y ≫ j = jK V ≫ ξV ∧ ξV (closedPoint V) = x := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hS x hx
  obtain ⟨V, _, _, _, C, ξV, hV, hy, hxV⟩ :=
    GlobalTheory.UChartTrait.exists_monoFam_through Xo c φ hpq hpf hns zs i OZ N d J π j BD hU hS x hx
  obtain ⟨Nn, ιP, hci, hι⟩ := hU.2.2.2.2.1.2.1
  haveI : IsSeparated (π ≫ zs) := by rw [← hι]; infer_instance
  haveI : IsDominant (jK V) := (GlobalTheory.Mum.Modif.self V).dominant
  have hs : ∀ f g : Sp V ⟶ S, jK V ≫ f = jK V ≫ g → f ≫ π ≫ zs = g ≫ π ≫ zs := fun f g hfg =>
    ext_of_isDominant_of_isSeparated (terminal.from (Sp c.F)) (terminal.hom_ext _ _) (jK V) (by
      rw [← Category.assoc, hfg, Category.assoc])
  have hX : Nontrivial C.P.D.toPre.X :=
    nontrivial_of_not_mem_range hV C (π ≫ zs) j ξV hs hy (hxV ▸ hx)
  obtain ⟨y0, hy0⟩ := exists_ne (0 : C.P.D.toPre.X)
  obtain ⟨i0, -⟩ := C.mono.exists_pos (maximalIdeal.isMaximal _).ne_top hy0
  have hnf : ¬ IsField V := by
    intro hf
    have hm := C.s_mem i0
    rw [(IsLocalRing.isField_iff_maximalIdeal_eq).1 hf, Ideal.mem_bot] at hm
    exact C.s_ne_zero i0 hm
  haveI : IsNoetherianRing V := hV.1.1
  haveI : CharZero V := hV.2
  obtain ⟨W, _, _, _, ρ, hcomp, hac, hinj, hloc⟩ := GlobalTheory.T.exists_complete_dvr_algClosed_residue_injective_local V hnf ⟨C.b.comp (algebraMap ℚ c.F)⟩
  haveI : CharZero W := charZero_of_injective_ringHom hinj
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hne : ∀ k, ρ (C.s k) ≠ 0 := fun k h0 => C.s_ne_zero k (hinj (h0.trans (map_zero ρ).symm))
  choose w u hwu using fun k => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hne k) hϖ
  have hW : GlobalTheory.UU.CDVR W := ⟨inferInstance, hcomp, inferInstance⟩
  obtain ⟨t, P, e, be, -, htK, hbe, -, hmono, -⟩ := trait_pull C hV W hW ϖ ρ hinj hloc w u hwu
  have hinj' : Function.Injective ((algebraMap W (FractionRing W)).comp ρ) :=
    (IsFractionRing.injective W (FractionRing W)).comp hinj
  obtain ⟨gam, hgam⟩ : ∃ gam : FractionRing V →+* FractionRing W,
      gam.comp (algebraMap V (FractionRing V)) = (algebraMap W (FractionRing W)).comp ρ :=
    ⟨IsFractionRing.lift hinj', RingHom.ext fun r => by
      rw [RingHom.comp_apply, RingHom.comp_apply]; exact IsFractionRing.lift_algebraMap hinj' r⟩
  have hκ : spMap gam ≫ jK V = jK W ≫ spMap ρ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hgam]
  obtain ⟨tK, h1, h2⟩ := htK (spMap gam) hκ
  have hover : (spMap gam ≫ C.y) ≫ pullback.snd _ _ = jK W ≫ spMap (ρ.comp C.b) := by
    rw [Category.assoc, C.y_over, ← Category.assoc, hκ, Category.assoc]
    congr 1
    exact (Spec.map_comp (CommRingCat.ofHom C.b) (CommRingCat.ofHom ρ)).symm
  let F : Fam Xo c W := ⟨ρ.comp C.b, t, P, spMap gam ≫ C.y, hover, ⟨tK, h1, h2⟩⟩
  let β : LinearMap.BilinForm ℤ P.D.toPre.X := ∑ k, (w k : ℤ) • pull e.toLinearMap (C.δ k)
  have hβ : β ∈ balForms H.bar P.D.toPre.X :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (pull_mem _ (C.cone.mem k))
  have hbeq : be = (l.M' : ℤ) • β := by
    rw [hbe, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext a b
    simp only [LinearMap.smul_apply, pull_apply, smul_eq_mul]
    ring
  have hmono' : IsMonomial F.P.D.toPre ![ϖ] ![(l.M' : ℤ) • β] := hbeq ▸ hmono
  have hϖm : ϖ ∈ maximalIdeal W := (mem_maximalIdeal _).2 hϖ.not_isUnit
  obtain ⟨C', hC'⟩ := F.exists_monoFam hpf hϖm hβ hmono'
  have hyC : C'.toFam.y = spMap gam ≫ C.y := by rw [hC']
  refine ⟨W, inferInstance, inferInstance, inferInstance, C', spMap ρ ≫ ξV,
    ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩, hac, ?_, ?_, ?_⟩
  · rw [hC']
    exact e.symm.injective.nontrivial
  · show C'.toFam.y ≫ j = _
    rw [hyC, Category.assoc, hy, ← Category.assoc, hκ, Category.assoc]
  · show ξV (spMap ρ (closedPoint W)) = x
    have hcl : spMap ρ (closedPoint W) = closedPoint V := IsLocalRing.comap_closedPoint ρ
    rw [hcl, hxV]

end GlobalTheory.UChartGeo
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegeneratingMonomialFamilyAlgClosedResidueStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_degenerating_monomialFamily_algClosed_residue : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), GlobalTheory.Mum.Base V ∧ IsAlgClosed (ResidueField V) ∧ Nontrivial C.P.D.toPre.X ∧ C.y ≫ j = jK V ≫ ξV ∧ ξV (closedPoint V) = x := by
  first | exact @GlobalTheory.UChartGeo.exists_monoFam_algClosed | exact GlobalTheory.UChartGeo.exists_monoFam_algClosed | (intros; apply GlobalTheory.UChartGeo.exists_monoFam_algClosed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointRigidTautologicalChartUnitaryBoundary

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem exists_tautB_chart_at : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S), IsTautB C ∧ C.y ≫ j = jK _ ≫ ξ ∧ ξ (closedPoint _) = x := by
  intro E _ _ _ H Dw l Xo c φ hpq hpol hns Z zs i OZ N d J S π j _ BD hU hS x hx
  obtain ⟨V, _, _, _, C, ξV, hB, hac, hnt, hC, hV⟩ :=
    GlobalTheory.T.exists_degenerating_monomialFamily_algClosed_residue Xo c φ hpq hpol hns zs i OZ N d J π j BD hU hS x hx
  obtain ⟨k, _, m, e, C₁, ξ, θ, hT, hC₁, hθ, hξ⟩ :=
    GlobalTheory.T.exists_tautological_chart_versality Xo c φ hpq hpol hns zs i OZ N d J π j BD hU hS V hB hac C ξV hnt hC
  refine ⟨k, inferInstance, m, e, C₁, ξ, hT, hC₁, ?_⟩
  rw [← hV, ← hξ]
  change _ = ξ.base ((spMap θ).base (closedPoint V))
  have h0 : (spMap θ).base (closedPoint V) = closedPoint (ChartRing k m e) := by
    haveI := hθ
    exact IsLocalRing.comap_closedPoint θ
  rw [h0]

end GlobalTheory.UCanon
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointRigidTautologicalChartUnitaryBoundaryStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_pointRigid_tautological_chart_unitary_boundary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S), IsTautB C ∧ C.y ≫ j = jK _ ≫ ξ ∧ ξ (closedPoint _) = x := by
  first | exact @GlobalTheory.UCanon.exists_tautB_chart_at | exact GlobalTheory.UCanon.exists_tautB_chart_at | (intros; apply GlobalTheory.UCanon.exists_tautB_chart_at <;> assumption)
end
end
