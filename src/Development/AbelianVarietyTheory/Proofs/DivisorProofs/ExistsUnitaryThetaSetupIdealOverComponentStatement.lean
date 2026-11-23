module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupFinrankLeMinSignatureUnitaryTrait
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrIntegralClosureFiniteFractionRi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtPointLiftOfSurjectiveLocFinType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealMapEqSpanPowUniformizerDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperLiftTraitOfGenericLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLatStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBounds
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDescendingDivisorPowerStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelNormalisationDedekind
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfield
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryExistsNormalModelEffCartierAlongTraitsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalZRam

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.LiftOrd

theorem evalZ_ram {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (T T' : UTrait Xo c) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V)
    (hf : Function.Injective f) (hl : IsLocalHom f)
    (hK : ∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a))
    (hy : T'.y = spMap fK ≫ T.y) (m : ℕ) (hm : Associated (f T.ϖ) (T'.ϖ ^ m)) (φ : InvFun (𝓞 E))
    (hφ : IsPolFan H.bar (min Dw.p Dw.q) φ) : φ.evalZ T'.be = m * φ.evalZ T.be := by
  obtain ⟨hdvr, hcpl, hz⟩ := T'.cdvr
  have hB : GlobalTheory.Mum.Base T'.V := ⟨⟨inferInstance, inferInstance, inferInstance, hcpl⟩, hz⟩
  have hself : Associated (RingHom.id T'.V T'.ϖ) (T'.ϖ ^ 1) := by simp [Associated.refl]
  have hid : spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _ := Spec.map_id _
  obtain ⟨e, he⟩ := GlobalTheory.T.traitsOfModuliPoint_have_isomorphic_proportional_lattices E H Dw l Xo c T T' T'.V f (RingHom.id _) fK (RingHom.id _) hB hdvr hf
    Function.injective_id hl inferInstance hK (fun _ => rfl) (by rw [hid, Category.id_comp, hy]) T'.ϖ m 1 T'.irr hm
    hself
  have hon : IsPolFanOn H.bar φ T.P.D.toPre.X := by
    haveI : Module.Projective (𝓞 E) T.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) T.P.D.toPre.X
    exact hφ _ (GlobalTheory.UPoinc.UTrait.finrank_le_min E H Dw l Xo c T)
  have hc : toReal T.be ∈ psdCone (bar := H.bar) (X := T.P.D.toPre.X) :=
    GlobalTheory.PolFan.StrictData.toReal_mem_psdCone ((balForms_eq_levelForms H T.P.D.toPre.X).symm ▸ T.lev)
      fun y => by simpa using T.mono.nonneg 0 y
  rw [← evalR_toReal φ T.be, ← hon.homog _ hc m m.cast_nonneg,
    ← evalZ_pull φ (r := e.toLinearMap) e.surjective, ← evalR_toReal]
  congr 1
  refine LinearMap.ext₂ fun a b => ?_
  have h := he a b
  rw [Nat.cast_one, one_mul] at h
  simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul]
  exact_mod_cast h.symm

end GlobalTheory.UPoinc.LiftOrd

theorem _root_.GlobalTheory.UPoinc.ideal_orders_of_proper_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → IsProper πY → ∀ (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), (∀ y ∈ (J₁.comap πY).support, X₁.π (πY y) ∉ Set.range C.i) → UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ (J₁.comap πY) ι → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) ∧ UValThru Xo c C.i X₁.π Set.univ φ J₁ ι := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C X₁ Y πY hhom hprop ι J₁ hsupp hval
  haveI := hprop
  have hsurj : Function.Surjective πY := by
    have hgen : genericPoint X₁.M.Z ∈ Set.range πY := by
      have w : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
      refine ⟨Y.pt w, ?_⟩
      have h := congrArg (fun h : Sp X₁.Ω₁ ⟶ X₁.M.Z => h w) (show Y.pt ≫ πY = _ from hhom)
      simp only [Scheme.Hom.comp_apply] at h
      rw [h]
      exact X₁.M.pt_apply _
    have hcl : IsClosed (Set.range πY) := πY.isClosedMap.isClosed_range
    intro x
    have : x ∈ closure (Set.range πY) :=
      closure_mono (Set.singleton_subset_iff.2 hgen) (by rw [genericPoint_spec X₁.M.Z]; trivial)
    rwa [hcl.closure_eq] at this
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := hsurj x
    exact hsupp y (by rw [Scheme.IdealSheafData.support_comap]; exact hx)
  intro W _ _ _ hW ϖ hϖ χ y hy _ t tK h1 h2 P be hbe hmono
  let T : UTrait Xo c := ⟨W, hW, ϖ, hϖ, y, t, ⟨tK, h1, h2⟩, P, be, hbe, hmono⟩
  obtain ⟨hdvr, hcpl, hz⟩ := hW
  haveI := hdvr
  haveI := hz

  obtain ⟨K', _, σ, yK, hσ, hyK⟩ := GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft πY inferInstance hsurj
    (FractionRing W) (jK W ≫ χ)
  obtain ⟨V', _, _, _, _, f, τ, hc', hfi, hfl, hff, hτ⟩ :=
    GlobalTheory.exists_complete_dvr_of_finite_fractionRing_hom W hcpl K' σ hσ
  have hfK : ∀ a, (τ.comp σ) (algebraMap W _ a) = algebraMap V' _ (f a) := hτ
  obtain ⟨ξ', hξπ, hξg⟩ := GlobalTheory.proper_lift_trait πY hprop W V' f (τ.comp σ) hfK χ (spMap τ ≫ yK) (by
    rw [Category.assoc, hyK, spMap_comp, Category.assoc])
  have hB' : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
  obtain ⟨T₂, f₂, fK₂, hf₂i, hf₂l, -, hf₂K, hT₂y⟩ :=
    GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c V' hB' inferInstance (spMap (τ.comp σ) ≫ y)
  haveI := hfl
  haveI := hf₂l
  have hjK : ∀ {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (u : R →+* S)
      (uK : FractionRing R →+* FractionRing S), (∀ a, uK (algebraMap R _ a) = algebraMap S _ (u a)) →
      jK S ≫ spMap u = spMap uK ≫ jK R := by
    intro R S _ _ _ _ u uK hu
    change spMap (algebraMap S (FractionRing S)) ≫ spMap u = spMap uK ≫ spMap (algebraMap R (FractionRing R))
    rw [← spMap_comp, ← spMap_comp]
    exact congrArg spMap (RingHom.ext fun a => (hu a).symm)

  have hcomm : T₂.y ≫ C.i = jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π := by
    have e1 := hjK f₂ fK₂ hf₂K
    symm
    calc jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π = (jK T₂.V ≫ spMap f₂) ≫ ξ' ≫ πY ≫ X₁.π := by
          simp only [Category.assoc]
      _ = spMap fK₂ ≫ (jK V' ≫ ξ') ≫ πY ≫ X₁.π := by rw [e1]; simp only [Category.assoc]
      _ = spMap fK₂ ≫ spMap τ ≫ (yK ≫ πY) ≫ X₁.π := by rw [hξg]; simp only [Category.assoc]
      _ = spMap fK₂ ≫ spMap τ ≫ spMap σ ≫ (jK W ≫ χ ≫ X₁.π) := by rw [hyK]; simp only [Category.assoc]
      _ = T₂.y ≫ C.i := by rw [← hy, hT₂y, spMap_comp]; simp only [Category.assoc]
  obtain ⟨tK₂, m₁, m₂⟩ := T₂.gen
  obtain ⟨a', ha', hid⟩ := hval T₂.V T₂.cdvr T₂.ϖ T₂.irr (spMap f₂ ≫ ξ') T₂.y hcomm trivial T₂.t tK₂ m₁ m₂ T₂.P T₂.be
    T₂.lev T₂.mono
  have idlAlong_comp_local {X : Scheme.{0}} (J : X.IdealSheafData) {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
      [IsLocalRing S] (χ : Sp R ⟶ X) (f : R →+* S) : idlAlong J (spMap f ≫ χ) = (idlAlong J χ).map f := by
    have eq_map {A : Type} [CommRing A] [IsLocalRing A] (ψ : Sp A ⟶ X)
        (U : X.affineOpens) (hle : ⊤ ≤ ψ ⁻¹ᵁ U.1) :
        idlAlong J ψ = (J.ideal U).map (ψ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of A)).hom).hom := by
      have hx : ψ (closedPoint A) ∈ U.1 := hle trivial
      unfold idlAlong
      rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
      congr 2
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
    have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
    have hle' : ⊤ ≤ (spMap f ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap f x ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [eq_map χ ⟨U, hU⟩ hle, eq_map _ ⟨U, hU⟩ hle', Ideal.map_map]
    congr 1
    have e : (spMap f ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap f).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  rw [GlobalTheory.PullAlong.idlAlong_comap_eq, Category.assoc, hξπ, ← Category.assoc, ← spMap_comp,
    idlAlong_comp_local] at hid

  set h := f₂.comp f with hh
  have hinj : Function.Injective h := hf₂i.comp hfi
  have hloc : IsLocalHom h := inferInstance
  obtain ⟨hdvr₂, -, -⟩ := T₂.cdvr
  haveI := hdvr₂
  have hne : h ϖ ≠ 0 := (map_ne_zero_iff h hinj).2 hϖ.ne_zero
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne T₂.irr
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | hpos
    · exact absurd ((isUnit_map_iff h ϖ).1 (he.isUnit_iff.2 (by simp))) hϖ.not_isUnit
    · exact hpos
  obtain ⟨b, hb, hI⟩ := GlobalTheory.ideal_map_eq_span_pow_uniformizer W T₂.V h hinj ϖ T₂.ϖ e a' _ hϖ T₂.irr he hid
  have hval2 : φ.evalZ T₂.be = e * φ.evalZ be :=
    GlobalTheory.UPoinc.LiftOrd.evalZ_ram T T₂ h (fK₂.comp (τ.comp σ)) hinj hloc
      (fun a => by rw [RingHom.comp_apply, hfK, hf₂K]; rfl) (by rw [hT₂y]; simp only [spMap_comp, Category.assoc]; first | rfl | skip) e he φ hφ
  refine ⟨b, ?_, hI⟩
  have h1 : (e : ℝ) * b = e * (ι * φ.evalZ be) := by
    rw [← Nat.cast_mul, hb, ha', hval2]; ring
  have h2 : (e : ℝ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
  exact mul_left_cancel₀ h2 h1
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointClosureEqOfIsClopen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem exists_genericPoint_closure_eq_of_isClopen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∃ η ∈ genericPoints (Xo.XF c), closure {C.i η} = A := by
  intro E _ _ _ H Dw _ l Xo c C A hA hirr hne
  obtain ⟨_, hyA, y, rfl⟩ := hne
  have hζ : IsGenericPoint hirr.genericPoint A := hirr.isGenericPoint_genericPoint hA.isClosed
  set ζ := hirr.genericPoint
  have h1 : ζ ⤳ C.i y := hζ.specializes hyA
  have hcomp : C.z (C.i y) = spMap C.b (pullback.snd C.z (spMap C.b) (C.iF y)) := by
    have := congrArg (fun f => f.base (C.iF y)) (pullback.condition (f := C.z) (g := spMap C.b))
    simpa using this
  have hbot : ∀ q : Sp c.F, (spMap C.b q).asIdeal = ⊥ := by
    intro q
    haveI := q.isPrime
    have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime q.asIdeal
    show Ideal.comap C.b q.asIdeal = ⊥
    rw [hq]
    exact Ideal.comap_bot_of_injective C.b C.inj
  have h2 : C.z ζ = C.z (C.i y) := by
    have hs : C.z ζ ⤳ C.z (C.i y) := h1.map C.z.continuous
    have hle : (C.z ζ).asIdeal ≤ (C.z (C.i y)).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 hs
    rw [hcomp, hbot] at hle
    apply PrimeSpectrum.ext
    rw [hcomp, hbot]
    exact le_bot_iff.1 hle
  obtain ⟨p', hp', -⟩ := Scheme.Pullback.exists_preimage_pullback (f := C.z) (g := spMap C.b) ζ
    (pullback.snd C.z (spMap C.b) (C.iF y)) (h2.trans hcomp)
  haveI : IsPreimmersion (pullback.fst C.z (spMap C.b)) := by
    letI := C.b.toAlgebra
    haveI := C.isFractionRing
    haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
    infer_instance
  have h3 : p' ⤳ C.iF y := by
    apply (IsPreimmersion.isEmbedding (pullback.fst C.z (spMap C.b))).specializes_iff.1
    rw [hp']
    exact h1
  haveI := C.iF_open
  obtain ⟨η, hη⟩ := h3.mem_open C.iF.isOpenEmbedding.isOpen_range ⟨y, rfl⟩
  have hCi : C.i η = ζ := by
    rw [← hp', ← hη]
    rfl
  have hinj : Function.Injective C.i := (IsPreimmersion.isEmbedding C.i).injective
  refine ⟨η, ⟨isIrreducible_singleton.closure, fun T hT hle => ?_⟩, by rw [hCi]; exact hζ⟩
  have hη' : IsGenericPoint hT.closure.genericPoint (closure T) :=
    hT.closure.isGenericPoint_genericPoint isClosed_closure
  have hs : hT.closure.genericPoint ⤳ η := hη'.specializes (subset_closure (hle (subset_closure rfl)))
  have hs' : C.i hT.closure.genericPoint ⤳ ζ := hCi ▸ hs.map C.i.continuous
  have hmem : C.i hT.closure.genericPoint ∈ A := hs'.mem_open hA.isOpen hζ.mem
  have heq : hT.closure.genericPoint = η := hinj ((hs'.antisymm (hζ.specializes hmem)).eq.trans hCi.symm)
  rw [← heq, hη']
  exact subset_closure

end GlobalTheory.UPoinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUSetupProj

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.GSetup

theorem exists_uSetup_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ η ∈ genericPoints (Xo.XF c), ∀ B : ℕ, ∃ X₁ : USetup C, B ≤ X₁.S.N ∧ IsProjOver X₁.M.s ∧ ∀ w, X₁.uΩ w = η := by
  intro E _ _ _ H Dw hpq l Xo c C η hη B
  haveI := c.fin
  haveI : NumberField c.F := {}
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim _
  obtain ⟨A, _, φ, j, P, _, hφ, hjs, hjo, hjx⟩ :=
    exists_chart (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) η
  let ev : A →+* P.ResidueField := algebraMap A P.ResidueField
  let y : Sp P.ResidueField ⟶ Xo.XF c := spMap ev ≫ j
  have hy : ∀ w, y w = η := fun w => by
    have hp : spMap ev w = ⟨P, inferInstance⟩ := by
      refine PrimeSpectrum.ext ?_
      show Ideal.comap ev w.asIdeal = P
      rw [Subsingleton.elim w (⊥ : PrimeSpectrum P.ResidueField)]
      exact Ideal.ker_algebraMap_residueField _
    show j (spMap ev w) = η
    rw [hp, hjx]
  haveI : CharZero P.ResidueField := (ev.comp φ).charZero_iff (ev.comp φ).injective |>.1 inferInstance
  obtain ⟨A₀, hS₀, hU₀⟩ := exists_fibre Xo c y
  have ho : Odd H.d := Nat.odd_iff.2 (by have := H.d_mod; omega)
  obtain ⟨k, j₁, hk, hBk, hj₁, big⟩ := exists_big_level A₀.g H.d H.d_prime.two_le B
  obtain ⟨Ω, _, f, A₁, ψ, ze, hf, hA₁, hze, ⟨lev⟩⟩ :=
    exists_level_finite P.ResidueField A₀ ((H.d ^ j₁ * (H.d ^ k) ^ 2) ^ 2) (Nat.one_le_iff_ne_zero.2 (by
      have := H.d_prime.pos; positivity))
  haveI : CharZero Ω := f.charZero_iff f.injective |>.1 inferInstance
  have hU₁ : UOver Xo c A₁ (RingHom.id Ω) (spMap f ≫ y) := by
    refine (uOver_baseChange_iff hA₁.2.1 (LBIso.symm hA₁.2.2) (RingHom.id Ω)).2 ?_
    rw [RingHom.id_comp]
    simpa only [RingHom.comp_id] using hU₀.comp f
  have hS₁ : HypS A₁.A A₁.L := by
    have := A₀.isAb.comm
    have := A₁.isAb.comm
    exact SymBaseChange.hypS_baseChange _ _ _ _ _ ψ _ _ A₀.isLB A₁.isLB hA₁.2.1 (LBIso.symm hA₁.2.2) hS₀
  letI : Algebra C.o c.F := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded
  let β : c.F →+* Ω := f.comp (ev.comp φ)
  obtain ⟨o₁, _, _, κ, ze₁, hded, hκ, hinj, hcomp, hze₁⟩ :=
    exists_base_root C.o c.F Ω β ze _ (Nat.one_le_iff_ne_zero.2 (by have := H.d_prime.pos; positivity)) hze
  have hft : Algebra.FiniteType ℤ o₁ := by
    letI := κ.toAlgebra
    haveI := C.ft
    haveI : Algebra.FiniteType C.o o₁ := hκ.finiteType
    exact Algebra.FiniteType.trans C.ft this
  haveI : ArithBase o₁ Ω := ⟨hded, hft, inferInstance, hinj⟩
  have hun : IsUnit (H.d : o₁) := by simpa using C.unit_d.map κ
  rw [← hze₁] at lev
  have hβ : β.EssFiniteType :=
    RingHom.EssFiniteType.comp (RingHom.EssFiniteType.comp hφ.essFiniteType
      ((RingHom.essFiniteType_algebraMap (R := A) (S := P.ResidueField)).2 inferInstance)) hf.finiteType.essFiniteType
  obtain ⟨R₀, hR₀, hfr, hR₀e⟩ := exists_fg_ratHull C.b (fun y => exists_int_mul_mem y) κ β hcomp hβ φ hφ (f.comp ev) rfl
  let u₀ : Sp (ratHull R₀) ⟶ Xo.XF c := spMap ((f.comp ev).codRestrict (ratHull R₀) hR₀e) ≫ j
  have hu₀ : spMap (ratHull R₀).val.toRingHom ≫ u₀ = spMap f ≫ y := by
    simp only [u₀, y, ← Category.assoc, ← Spec.map_comp]; rfl
  obtain ⟨S, ρ, u, hN, hr, hg, hUS, hpt⟩ :=
    exists_thetaSys_uOver Xo c R₀ hR₀ hfr u₀ A₁ (hu₀ ▸ hU₁) hS₁ H.d k j₁ H.d_prime ho hk hj₁ hun ze₁ lev
  have hbig : S.Big := big j₁ le_rfl o₁ Ω S (hg.trans hA₁.1) hN hr
  have hp : spMap (ratHull S.R).val.toRingHom ≫ u = spMap f ≫ spMap ev ≫ j := hpt.trans hu₀
  haveI : IsProper C.z := ThetaDescent.isProper_of_isProjOver C.proj
  haveI := C.isPreimmersion_i
  haveI : SurjectiveOnStalks (spMap ev) :=
    (SurjectiveOnStalks.Spec_iff (φ := CommRingCat.ofHom ev)).2 (Ideal.surjectiveOnStalks_residueField P)
  have hi : C.i ≫ C.z = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ spMap C.b := by
    simp only [UCompact.i, Category.assoc, pullback.condition]
    rw [← Category.assoc, C.iF_over]
  have hpz : (spMap (ratHull S.R).val.toRingHom ≫ u ≫ C.i) ≫ C.z = spMap ((algebraMap o₁ Ω).comp κ) := by
    rw [show (spMap (ratHull S.R).val.toRingHom ≫ u ≫ C.i) ≫ C.z =
      (spMap (ratHull S.R).val.toRingHom ≫ u) ≫ (C.i ≫ C.z) by simp only [Category.assoc], hp, hi]
    simp only [Category.assoc]
    rw [← Category.assoc j, hjs, hcomp]
    simp only [← Spec.map_comp]
    rfl
  have hst : ((spMap (ratHull S.R).val.toRingHom ≫ u ≫ C.i).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
    rw [← Category.assoc, hp, Category.assoc, Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp (finite_stalkMap_field f hf _)
      (RingHom.Finite.of_surjective _ (Scheme.Hom.stalkMap_surjective _ _))
  obtain ⟨Mdl, π, hMn, hπ, hMp⟩ := GlobalTheory.Poinc.exists_ratModel_normalization C.o o₁ Ω κ hκ C.Z C.z inferInstance
    inferInstance inferInstance _ hpz hst
  have hgen : ∀ w, (spMap (ratHull S.R).val.toRingHom ≫ u) w = η := fun w => by
    rw [hp]
    exact hy _
  have hsc : Mdl.s ≫ spMap κ = π ≫ C.z := by
    refine ext_of_isDominant Mdl.pt ?_
    rw [← Category.assoc, Mdl.pt_s, ← Category.assoc, hMp, hpz]
    exact (Spec.map_comp (CommRingCat.ofHom κ) (CommRingCat.ofHom (algebraMap o₁ Ω))).symm
  have hproj : IsProjOver Mdl.s := by
    haveI := hπ
    obtain ⟨h1, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB C.z).1 C.proj
    haveI : IsProper (Mdl.s ≫ spMap κ) := by rw [hsc]; infer_instance
    haveI : IsProper Mdl.s := IsProper.of_comp Mdl.s (spMap κ)
    exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨this, _, hL.pull_of_isFinite π⟩
  exact ⟨⟨o₁, Ω, S, ρ, hbig, u, hUS, fun w => (hgen w).symm ▸ hη, Mdl, GlobalTheory.IsNormalScheme.of_pred hMn, π, hπ, hMp⟩, hN ▸ hBk, hproj, hgen⟩

end GlobalTheory.UPoinc.GSetup
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryThetaSetupIdealOverComponent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.UPoinc.exists_uSetup_ideal_over_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∃ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι ∧ Set.range X₁.π = A ∧ (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) ∧ UValThru Xo c C.i X₁.π Set.univ φ J₁ ι := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C A hAc hAi hAm
  obtain ⟨η, hη, hcl⟩ := GlobalTheory.UPoinc.exists_genericPoint_closure_eq_of_isClopen E H Dw hpq l Xo c C A hAc hAi hAm
  obtain ⟨X₁, -, hpr, hX₁⟩ := GlobalTheory.UPoinc.GSetup.exists_uSetup_proj E H Dw hpq l Xo c C η hη 0
  have hr := GlobalTheory.UPoinc.USetup.range_π_eq E H Dw hpq l Xo c C X₁ η A hX₁ hcl
  obtain ⟨ι, Y, πY, D, hι, hhom, hprop, hnY, hsupp, hord⟩ := GlobalTheory.T.unitary_exists_normalModel_effCartier_along_traits E H Dw hpq φ hφ l Xo c C X₁ hpr
  obtain ⟨ι', J₁, hι', hsupp', hord'⟩ := GlobalTheory.T.exists_idealSheaf_descending_divisor_power E H Dw hpq φ hφ l Xo c C X₁ ι Y πY D hι hhom hprop hnY hsupp hord
  obtain ⟨hs, ho⟩ := GlobalTheory.UPoinc.ideal_orders_of_proper_model E H Dw hpq φ hφ l Xo c C X₁ Y πY hhom hprop ι' J₁ hsupp' hord'
  exact ⟨X₁, ι', J₁, hι', hr, hs, ho⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryThetaSetupIdealOverComponentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.exists_unitaryThetaSetup_ideal_over_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∃ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι ∧ Set.range X₁.π = A ∧ (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) ∧ UValThru Xo c C.i X₁.π Set.univ φ J₁ ι := by
  first | exact @GlobalTheory.UPoinc.exists_uSetup_ideal_over_component | exact GlobalTheory.UPoinc.exists_uSetup_ideal_over_component | (intros; apply GlobalTheory.UPoinc.exists_uSetup_ideal_over_component <;> assumption)
end
end
