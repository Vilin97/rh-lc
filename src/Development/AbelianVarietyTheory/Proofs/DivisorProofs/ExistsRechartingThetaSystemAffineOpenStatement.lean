module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactificationGenericSubsetModuli
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
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIntCastStalkIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalSectionBasesShrunkAffineChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisExtendsNormalAffineC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVDimEqOfGrpPullbackField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianVarietyPullbackAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOnAffineOpenFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupExtendsNormalAffineChartAfterRescaling
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartRatHullLift

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points

namespace GlobalTheory.UPoinc.ChartAt

theorem isUnit_map_of_ne_zero {o R : Type} [CommRing o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [CommRing R]
    (hR : ∀ n : ℤ, n ≠ 0 → IsUnit (n : R)) (φ : o →+* R) {a : o} (ha : a ≠ 0) : IsUnit (φ a) := by
  by_contra h
  obtain ⟨m, hm, ham⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 h)
  letI := Ideal.Quotient.field m
  haveI : CharZero (R ⧸ m) := charZero_of_inj_zero fun n hn => by
    by_contra h0
    have hu := (hR n (by exact_mod_cast h0)).map (Ideal.Quotient.mk m)
    exact hu.ne_zero (by simpa using hn)
  have hk := ker_eq_bot_of_charZero ((Ideal.Quotient.mk m).comp φ)
  have : a ∈ RingHom.ker ((Ideal.Quotient.mk m).comp φ) := Ideal.Quotient.eq_zero_iff_mem.2 ham
  rw [hk] at this
  exact ha this

theorem exists_affine_chart_ratHull_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (w₀ : X.M.Z), X.π w₀ ∈ Set.range C.i → ∃ (U₀ : X.M.Z.Opens) (u₀ : Sp (ratHull (X.M.ringOn U₀)) ⟶ Xo.XF cf), IsAffineOpen U₀ ∧ w₀ ∈ U₀ ∧ spMap (ratHull (X.M.ringOn U₀)).val.toRingHom ≫ u₀ = X.uΩ := by
  intro E _ _ _ H Dw _ l Xo cf C X w hw
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.iF_open
  haveI := C.ded
  haveI := C.ft
  haveI := C.isPreimmersion_i
  haveI : CharZero X.Ω₁ := by
    obtain ⟨t, -⟩ := Spec.map_surjective (X.uΩ ≫ pullback.snd _ _)
    exact (RingHom.charZero_iff (R := cf.F) t.hom.injective).1 inferInstance
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hg : Topology.IsEmbedding (pullback.fst C.z (spMap C.b) :) := (pullback.fst C.z (spMap C.b)).isEmbedding
  obtain ⟨V, hV, hVe⟩ := hg.isInducing.isOpen_iff.1 C.iF.isOpenEmbedding.isOpen_range
  have hwV : w ∈ X.π ⁻¹ᵁ ⟨V, hV⟩ := by
    obtain ⟨x, hx⟩ := hw
    have : C.iF x ∈ (pullback.fst C.z (spMap C.b) :) ⁻¹' V := hVe ▸ ⟨x, rfl⟩
    show X.π w ∈ V
    rw [← hx]
    exact this
  obtain ⟨U, hU, hwU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X.M.Z) hwV
  have hne : ((U : X.M.Z.Opens) : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  let φ : Γ(X.M.Z, U) ⟶ CommRingCat.of (ratHull (X.M.ringOn U)) :=
    CommRingCat.ofHom ((toRat (X.M.ringOn U)).comp (X.M.sectionsEquiv U hne).toRingHom)
  let f : Sp (ratHull (X.M.ringOn U)) ⟶ X.M.Z := Spec.map φ ≫ hU.fromSpec
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (f ≫ X.π ≫ C.z)
  have hu : ∀ a : nonZeroDivisors C.o, IsUnit (ψ.hom a) := fun a =>
    isUnit_map_of_ne_zero (fun n hn => isUnit_intCast_ratHull _ hn) ψ.hom (nonZeroDivisors.ne_zero a.2)
  let χ : cf.F →+* ratHull (X.M.ringOn U) := IsLocalization.lift (M := nonZeroDivisors C.o) hu
  have hχ : (f ≫ X.π) ≫ C.z = spMap χ ≫ spMap C.b := by
    rw [Category.assoc, ← hψ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun t => spMap t) (IsLocalization.lift_comp (M := nonZeroDivisors C.o) hu).symm
  let g := pullback.lift _ _ hχ
  have hgf : g ≫ pullback.fst _ _ = f ≫ X.π := pullback.lift_fst _ _ _
  have hrange : Set.range g ⊆ Set.range C.iF := by
    rintro _ ⟨y, rfl⟩
    rw [← hVe]
    show (g ≫ pullback.fst C.z (spMap C.b)) y ∈ V
    rw [hgf]
    have : hU.fromSpec (Spec.map φ y) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at this
    exact hUV this
  refine ⟨U, IsOpenImmersion.lift C.iF g hrange, hU, hwU, ?_⟩
  rw [← cancel_mono C.i, Category.assoc, Category.assoc, ← X.comp, UCompact.i, IsOpenImmersion.lift_fac_assoc, hgf]
  have hpt : ⊤ ≤ X.M.pt ⁻¹ᵁ U := X.M.top_le_preimage_pt hne
  have hφ : φ ≫ CommRingCat.ofHom (ratHull (X.M.ringOn U)).val.toRingHom = valMap X.M.pt U hpt := by
    ext a
    show ((X.M.sectionsEquiv U hne a : X.M.ringOn U) : X.Ω₁) = _
    rw [RatModel.coe_sectionsEquiv, ← valR_eq, valF_eq_valR]
  have hf : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ f = X.M.pt := by
    simp only [f, ← Category.assoc]
    rw [spMap, ← Spec.map_comp, hφ, specMap_valMap_fromSpec]
  rw [← hf]
  simp only [Category.assoc]

end GlobalTheory.UPoinc.ChartAt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVCommonPullback

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem exists_polAV_common_pullback : ∀ (Ω : Type) [Field Ω] (T T' : Scheme.{0}) (Q : PolAV T) (P' : PolAV T') (f : Sp Ω ⟶ T) (f' : Sp Ω ⟶ T') (G' : Over (Sp Ω)) [GrpObj G'] (a₁ : G'.left ⟶ Q.A.left) (a₂ : G'.left ⟶ P'.A.left), IsGrpPullback G' Q.A f a₁ → IsGrpPullback G' P'.A f' a₂ → LBIso (Q.L.pull a₁) (P'.L.pull a₂) → ∃ (P₀ : PolAV (Sp Ω)) (a : P₀.A.left ⟶ Q.A.left) (a' : P₀.A.left ⟶ P'.A.left) (e : G'.left ⟶ P₀.A.left), IsIso e ∧ e ≫ a = a₁ ∧ e ≫ a' = a₂ ∧ IsGrpPullback P₀.A Q.A f a ∧ IsGrpPullback P₀.A P'.A f' a' ∧ LBIso P₀.L (Q.L.pull a) ∧ LBIso P₀.L (P'.L.pull a') := by
  intro Ω _ T T' Q P' f f' G' _ a₁ a₂ h₁ h₂ hL
  obtain ⟨P₀, φ, hφ, hL₀⟩ := exists_pol_baseChange Q f
  obtain ⟨e, he, hea⟩ := grpPullback_iso h₁ hφ
  haveI := he
  have hinv : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have hφ' : φ = e.inv.left ≫ a₁ := by
    rw [← hea, ← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
  have hiso : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]⟩⟩
  refine ⟨P₀, φ, e.inv.left ≫ a₂, e.hom.left, hiso, hea, ?_, hφ, ?_, hL₀, ?_⟩
  · rw [← Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left, Category.id_comp]
  · exact ((isGrpPullback_of_iso e.symm).comp h₂).congr (Category.id_comp _) rfl
  · exact LBIso.trans P₀.isLB (pull_isLB Q.isLB _) (pull_isLB P'.isLB _) hL₀
      (GenSpread.lbIso_pull_comp e.inv.left hφ' rfl hL)

end GlobalTheory.UPoinc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVRingOnNear

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc

theorem USetup.exists_polAV_ringOn_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (w₀ : X.M.Z), X.π w₀ ∈ Set.range C.i → ∀ (U₀ : X.M.Z.Opens) (u₀ : Sp (ratHull (X.M.ringOn U₀)) ⟶ Xo.XF cf), IsAffineOpen U₀ → w₀ ∈ U₀ → spMap (ratHull (X.M.ringOn U₀)).val.toRingHom ≫ u₀ = X.uΩ → ∃ (U₁ : X.M.Z.Opens) (h : X.M.ringOn U₀ ≤ X.M.ringOn U₁) (P₁ : PolAV (Sp (X.M.ringOn U₁))), U₁ ≤ U₀ ∧ IsAffineOpen U₁ ∧ w₀ ∈ U₁ ∧ UOver Xo cf P₁ (toRat (X.M.ringOn U₁)) (spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫ u₀) :=
  fun E _ _ _ H Dw _ l Xo cf C X w₀ hw U₀ u₀ hU hwU _ =>
    LocSpread.exists_uOver_ringOn E H Dw l Xo cf C X U₀ u₀ w₀ hU hwU hw

end GlobalTheory.UPoinc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRechartingThetaSystemAffineOpen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory



theorem GlobalTheory.UPoinc.exists_rechart_wit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (w₀ : X.M.Z), X.π w₀ ∈ Set.range C.i → ∃ (U : X.M.Z.Opens) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (fg : (X.M.ringOn U).FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ X.M.ringOn U) (hev : ∀ x k, c₀ * X.S.ev x k ∈ X.M.ringOn U) (ρ' : (X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev).Real) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U ∧ w₀ ∈ U ∧ USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ ∧ ∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ ∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧ w ≫ m ≫ α = spMap (X.M.ringOn U).val.toRingHom ≫ (ρ'.pt x).left := by
  intro E _ _ _ H Dw hpq l Xo cf C X wi w₀ hw₀
  obtain ⟨⟨hL, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  obtain ⟨U₀, u₀, hU₀a, hwU₀, hu₀⟩ := GlobalTheory.UPoinc.ChartAt.exists_affine_chart_ratHull_lift E H Dw hpq l Xo cf C X w₀ hw₀
  obtain ⟨U₁, h₁, P₁, hU₁₀, hU₁a, hwU₁, hP₁⟩ := GlobalTheory.UPoinc.USetup.exists_polAV_ringOn_near E H Dw hpq l Xo cf C X w₀ hw₀ U₀ u₀ hU₀a hwU₀ hu₀
  have hN : 1 ≤ X.S.N := by have := X.S.N_ge; omega
  obtain ⟨U, h, P', φ, hUU₁, hUa, hwU, hφ, hφL, _hgφ, ⟨th, hth⟩, b, hb⟩ :=
    GlobalTheory.Poinc.exists_univBasis_affineChart X.o₁ X.Ω₁ X.M U₁ w₀ hU₁a hwU₁ P₁ X.S.N hN
  let u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf := spMap (Subalgebra.inclusion (ratHull_mono (h₁.trans h))).toRingHom ≫ u₀
  have hu' : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
    rw [← hu₀, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hUO : UOver Xo cf P' (toRat (X.M.ringOn U)) u' := by
    refine (uOver_baseChange_iff hφ hφL (toRat (X.M.ringOn U))).2 ?_
    have h2 := hP₁.comp (Subalgebra.inclusion (ratHull_mono h)).toRingHom
    have e1 : (Subalgebra.inclusion (ratHull_mono h)).toRingHom.comp (toRat (X.M.ringOn U₁)) =
        (toRat (X.M.ringOn U)).comp (Subalgebra.inclusion h).toRingHom := RingHom.ext fun _ => rfl
    have e2 : spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫
        spMap (Subalgebra.inclusion (ratHull_mono h₁)).toRingHom ≫ u₀ = u' := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    rw [e1, e2] at h2
    exact h2
  obtain ⟨G, _, α, β, hα, hβ, hLG⟩ := hUO
  have wβ : wi.β ≫ Xo.univ.t.G.hom = (wi.G.hom ≫ spMap (ratHull (X.M.ringOn U)).val.toRingHom) ≫ u' ≫ pullback.fst _ _ := by
    rw [wi.hβ.1.w, ← hu']
    simp only [Category.assoc]
  let m : wi.G.left ⟶ G.left := hβ.1.lift wi.β (wi.G.hom ≫ spMap (ratHull (X.M.ringOn U)).val.toRingHom) wβ
  have hm₁ : m ≫ β = wi.β := hβ.1.lift_fst _ _ _
  have hm₂ : m ≫ G.hom = wi.G.hom ≫ spMap (ratHull (X.M.ringOn U)).val.toRingHom := hβ.1.lift_snd _ _ _
  have hm : IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m :=
    hβ.cancel (wi.hβ.congr (by rw [← hu']; simp only [Category.assoc]) hm₁.symm) hm₂
  have hmα : IsGrpPullback wi.G P'.A (spMap (X.M.ringOn U).val.toRingHom) (m ≫ α) :=
    (hm.comp hα).congr (spMap_val_toRat (X.M.ringOn U)) rfl
  have hLU := Xo.univ.t.PP.isLB
  have hLρ := X.ρ.P.isLB
  have hLP := P'.isLB
  have hLw : LBIso (X.ρ.P.L.pull wi.α) (P'.L.pull (m ≫ α)) :=
    LBIso.trans (pull_isLB hLρ _) (pull_isLB hLU _) (pull_isLB hLP _) wi.hL
      (LBIso.trans (pull_isLB hLU _) (pull_isLB (pull_isLB hLU _) _) (pull_isLB hLP _)
        (GenSpread.lbIso_pull_pull hLU m hm₁.symm)
        (LBIso.trans (pull_isLB (pull_isLB hLU _) _) (pull_isLB (pull_isLB hLP _) _) (pull_isLB hLP _)
          (GenSpread.lbIso_pullback hLG.symm m) (GenSpread.lbIso_pull_pull hLP m rfl).symm))
  obtain ⟨P₀, a, a', e, he, hea, hea', ha, ha', hl, hl'⟩ :=
    GlobalTheory.UPoinc.exists_polAV_common_pullback X.Ω₁ (Sp X.S.R) (Sp (X.M.ringOn U)) X.ρ.P P' (spMap X.S.R.val.toRingHom) (spMap (X.M.ringOn U).val.toRingHom) wi.G wi.α (m ≫ α)
      wi.hα hmα hLw
  have hne : ((U : Set X.M.Z)).Nonempty := ⟨w₀, hwU⟩
  have hyp : HypS P'.A P'.L :=
    GlobalTheory.Poinc.hypS_of_generic_ringOn X.o₁ X.Ω₁ X.M U hUa hne X.normal X.S.R X.ρ.P P' P₀ _ a a' ha ha' hl hl' X.ρ.hypS
  have hg : P'.g = X.S.g :=
    (GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ P' P₀ _ a' ha').symm.trans
      ((GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ X.ρ.P P₀ _ a ha).trans X.ρ.g_eq)
  have fg : (X.M.ringOn U).FG := GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen _ _ X.M U hUa hne
  have frac : ∀ x : X.Ω₁, ∃ a ∈ (X.M.ringOn U), ∃ b ∈ (X.M.ringOn U), x = a / b := fun x => by
    obtain ⟨p, q, -, e⟩ := RatModel.exists_eq_div hUa hne x
    exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨p, rfl⟩, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨q, rfl⟩, e⟩
  haveI := RatModel.isFractionRing_ringOn hUa hne
  haveI : IsIntegrallyClosed (X.M.ringOn U) :=
    TorsExtend.isIntegrallyClosed_ringOn X.M ((isNormalScheme_iff_pred _).1 X.normal) hUa hne
  haveI := ArithBase.ded (o := X.o₁) (Ω := X.Ω₁)
  haveI : IsNoetherianRing (X.M.ringOn U) := isNoetherianRing_of_fg fg
  have hn : 1 ≤ X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (le_trans one_le_two X.S.N_ge)
  have hu : IsUnit ((X.S.r * X.S.N : ℕ) : (X.M.ringOn U)) := by
    have := X.S.unit.map (algebraMap X.o₁ (X.M.ringOn U))
    rwa [map_natCast] at this
  obtain ⟨pt', hadd, hbij, h₃, hw0⟩ := TorsExtend.exists_labelled hL X.S.R.val.toRingHom X.ρ.P P' P₀ a a' ha ha' hl hl' hn hu
    (M := X.S.Gam) (fun x => by ext k; simp [nsmul_eq_mul, -Nat.cast_mul]) X.ρ.pt X.ρ.pt_add X.ρ.pt_bij
  have hweil : ∀ x y (c : (X.M.ringOn U)ˣ), (c : (X.M.ringOn U)) = algebraMap X.o₁ (X.M.ringOn U) (X.S.ζ ^ (X.S.r * X.S.N * (eStd X.S.g _ x y).val)) →
      WeilIs P'.A P'.L (X.S.r * X.S.N : ℕ) (pt' x) (pt' y) (unitOn c) := fun x y c hc => by
    obtain ⟨c₀, hc₀⟩ := ((X.S.prim.isUnit (by positivity)).pow (X.S.r * X.S.N * (eStd X.S.g _ x y).val)).map
      (algebraMap X.o₁ X.S.R)
    refine h₃ x y c₀ c ?_ (X.ρ.weil x y c₀ hc₀)
    rw [hc₀, hc]
    rfl
  let Q : (P : PolAV (Sp (X.M.ringOn U))) → (X.S.Gam → (baseOver (Sp (X.M.ringOn U)) ⟶ P.A)) → Prop := fun P pt =>
    (∃ (P₀ : PolAV (Sp X.Ω₁)) (a : P₀.A.left ⟶ X.ρ.P.A.left) (a' : P₀.A.left ⟶ P.A.left),
      IsGrpPullback P₀.A X.ρ.P.A (spMap ((RingHom.id _).comp X.S.R.val.toRingHom)) a ∧
      IsGrpPullback P₀.A P.A (spMap (X.M.ringOn U).val.toRingHom) a' ∧ LBIso P₀.L (X.ρ.P.L.pull a) ∧ LBIso P₀.L (P.L.pull a') ∧
      ∀ x, ∃ w : Sp X.Ω₁ ⟶ P₀.A.left, w ≫ a = spMap ((RingHom.id _).comp X.S.R.val.toRingHom) ≫ (X.ρ.pt x).left ∧
        w ≫ a' = spMap (X.M.ringOn U).val.toRingHom ≫ (pt x).left) ∧
    (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ P.A.left) (β : G.left ⟶ Xo.univ.t.G.left),
      IsGrpPullback G P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧
      LBIso (P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
      ∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧
        ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
          w ≫ m ≫ α = spMap (X.M.ringOn U).val.toRingHom ≫ (pt x).left)
  have hQ : Q P' pt' := by
    refine ⟨⟨P₀, a, a', ha, ha', hl, hl', hw0⟩, G, inferInstance, α, β, hα, hβ, hLG, m, hm, hm₁, fun x => ?_⟩
    obtain ⟨w0, h₁, h₂⟩ := hw0 x
    refine ⟨w0 ≫ inv e, ?_, ?_⟩
    · rw [← hea, Category.assoc, IsIso.inv_hom_id_assoc, h₁]
    · rw [← hea', Category.assoc, IsIso.inv_hom_id_assoc]
      exact h₂
  obtain ⟨c₀, hc, hthm, hevm, ρ', ⟨hS₁, G', _, α', β', hα', hβ', hL', m', hm', hm₁', hpt'⟩, hi₀⟩ :=
    GlobalTheory.ThetaExtend.exists_real_rechart hL X.S X.ρ (X.M.ringOn U) fg frac P' P₀ a a' pt' th b ha ha' hl hl' hg hyp hadd hbij hweil
      hw0 hth hb Q hQ
  exact ⟨U, c₀, hc, fg, frac, hthm, hevm, ρ', u', hUa, hwU, hS₁, hi₀, hu', G', inferInstance, α', β', hα', hβ', hL', m',
    hm', hm₁', hpt'⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRechartingThetaSystemAffineOpenStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_recharting_thetaSystem_affineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (w₀ : X.M.Z), X.π w₀ ∈ Set.range C.i → ∃ (U : X.M.Z.Opens) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (fg : (X.M.ringOn U).FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ X.M.ringOn U) (hev : ∀ x k, c₀ * X.S.ev x k ∈ X.M.ringOn U) (ρ' : (X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev).Real) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U ∧ w₀ ∈ U ∧ USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ ∧ ∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ ∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧ w ≫ m ≫ α = spMap (X.M.ringOn U).val.toRingHom ≫ (ρ'.pt x).left := by
  first | exact @GlobalTheory.UPoinc.exists_rechart_wit | exact GlobalTheory.UPoinc.exists_rechart_wit | (intros; apply GlobalTheory.UPoinc.exists_rechart_wit <;> assumption)
end
end
