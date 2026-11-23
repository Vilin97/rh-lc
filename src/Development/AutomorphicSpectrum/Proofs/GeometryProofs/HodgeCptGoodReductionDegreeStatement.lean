module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsCompatibleGenericStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsJoinModelDominatesStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNormalisationStatement
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankAdjoinVarsField
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagFieldChangeStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompFieldExtension
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCptIffNormalSchemeStatement
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConstantsGenericPoint

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem exists_open_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → ∃ (cst₀ : c.F →+* 𝔐.Ω₀) (y₁ : Sp 𝔐.Ω₀ ⟶ Xo.XF c), 𝔐.ξ₀ = y₁ ≫ Y.j ∧ 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) ∧ 𝔐.fn.comp cst₀ = 𝔐.cst := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 y₀ hy
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  haveI := Y.jQ_open
  have hd : 𝔐.ξ ≫ 𝔐.f = spMap 𝔐.fn ≫ 𝔐.ξ₀ := 𝔐.fn_over

  let b₀ : 𝓞 c.F →+* 𝔐.Ω₀ := (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom
  have hb : 𝔐.ξ₀ ≫ Y.s = spMap b₀ := (Spec.map_preimage _).symm
  have hc : 𝔐.fn.comp b₀ = 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have hsp : spMap (𝔐.fn.comp b₀) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      have hm : spMap (𝔐.fn.comp b₀) = spMap 𝔐.fn ≫ spMap b₀ := by
        rw [← Spec.map_comp]; rfl
      rw [hm, ← hb, ← 𝔐.cst_over, ← Category.assoc, ← Category.assoc, hd]
    have := CommRingCat.hom_ext_iff.1 (Spec.map_injective hsp)
    simpa using this
  have hinj : Function.Injective b₀ := by
    intro u v huv
    have h := congrArg 𝔐.fn huv
    have hu : ∀ w, 𝔐.fn (b₀ w) = 𝔐.cst (algebraMap (𝓞 c.F) c.F w) := fun w => RingHom.congr_fun hc w
    rw [hu, hu] at h
    exact IsFractionRing.injective (𝓞 c.F) c.F (𝔐.cst.injective h)
  let cst₀ : c.F →+* 𝔐.Ω₀ := IsFractionRing.lift hinj
  have hl : cst₀.comp (algebraMap (𝓞 c.F) c.F) = b₀ := by
    ext w
    exact IsFractionRing.lift_algebraMap hinj w
  have hfn : 𝔐.fn.comp cst₀ = 𝔐.cst := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) ?_
    rw [RingHom.comp_assoc, hl, hc]
  have hs : 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) := by rw [hl, hb]
  have hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap (g.comp f) = spMap g ≫ spMap f := by
    intro A B C _ _ _ f g
    rw [← Spec.map_comp]; rfl

  let w : Sp 𝔐.Ω₀ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) :=
    pullback.lift 𝔐.ξ₀ (spMap cst₀) (by rw [hs, hcomp])

  let u : c.F →+* Ω := (Spec.preimage (y₀ ≫ pullback.snd _ _)).hom
  have hu : y₀ ≫ pullback.snd _ _ = spMap u := (Spec.map_preimage _).symm
  have huc : u = 𝔐.cst := by
    have hsp : spMap (u.comp (algebraMap (𝓞 c.F) c.F)) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [hcomp, ← hu, ← 𝔐.cst_over, ← Category.assoc 𝔐.ξ, hy, Model.j]
      simp only [Category.assoc]
      rw [pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
    have h1 := CommRingCat.hom_ext_iff.1 (Spec.map_injective hsp)
    have h2 : u.comp (algebraMap (𝓞 c.F) c.F) = 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by simpa using h1
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h2
  have hw : spMap 𝔐.fn ≫ w = y₀ ≫ Y.jQ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← hd, hy, Model.j, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, ← hcomp, hfn, Category.assoc, Y.jQ_over, hu, huc]
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ : ∃ a', (spMap 𝔐.fn) a' = a :=
      ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩
    refine ⟨y₀ a', ?_⟩
    have := congrArg (fun φ => φ a') hw
    simpa using this.symm
  refine ⟨cst₀, IsOpenImmersion.lift Y.jQ w hr, ?_, hs, hfn⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

end GlobalTheory.CompanionTheory.Ar.GenPoint
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConstantsGenericPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_constants_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → ∃ (cst₀ : c.F →+* 𝔐.Ω₀) (y₁ : Sp 𝔐.Ω₀ ⟶ Xo.XF c), 𝔐.ξ₀ = y₁ ≫ Y.j ∧ 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) ∧ 𝔐.fn.comp cst₀ = 𝔐.cst := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenPoint.exists_open_point | exact GlobalTheory.CompanionTheory.Ar.GenPoint.exists_open_point | (intros; apply GlobalTheory.CompanionTheory.Ar.GenPoint.exists_open_point <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankAdjoinVarsFieldStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.finrank_adjoin_vars_field :
    ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) (I : Type) (d : ℕ),
      0 < d →
      (letI : Algebra Ω₀ Ω := fn.toAlgebra
       Module.finrank Ω₀ Ω = d) →
      letI : Algebra Ω₀ (FractionRing (MvPolynomial I Ω)) :=
        ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra
      Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : I =>
        algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q)))
        (FractionRing (MvPolynomial I Ω)) = d := by
  intro Ω₀ Ω _ _ fn I d hd hfin
  let : Algebra Ω₀ Ω := fn.toAlgebra
  have : FiniteDimensional Ω₀ Ω := Module.finite_of_finrank_pos (hfin ▸ hd)
  let : Algebra Ω₀ (FractionRing (MvPolynomial I Ω)) :=
    ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra
  have hdegree :=
    GlobalTheory.CompanionTheory.FieldDeg.finrank_fraction_over_adjoin_X_eq Ω₀ Ω I rfl
  exact hdegree.trans hfin
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompFieldExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_comp_field_extension : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [CharZero Ω] [Field Ω'] [CharZero Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (A' : HodgeCpt Y S y') (g : A'.X ⟶ A.X) (m : SABMap A'.t A.t g) (j₁ : A.Li →+ A'.Li) (y₀ : Sp Ω ⟶ Xo.XF c) (p : ℕ), p ∈ S → GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ g i → A'.f = g ≫ A.f → A'.R = A.R → IsExtOver i j₁ → (∀ v, (A'.M.pt (j₁ v)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt v).left) → A.ξ ≫ A.f = y₀ ≫ Y.j → (∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ A.R p)) → (HT.omP A p).IsVBOn {q | InFibre A.ξ p q} (Module.finrank Ω A.Li) ⊤ → (HT.omP A' p).IsVBOn {q | InFibre A'.ξ p q} (Module.finrank Ω' A'.Li) ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HFlag.omP_ext | exact GlobalTheory.CompanionTheory.Ar.HFlag.omP_ext | (intros; apply GlobalTheory.CompanionTheory.Ar.HFlag.omP_ext <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptGoodReductionDegree

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenFlag

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.FlagBun

section Model

theorem coordTie_along {o : Type} [CommRing o] {X : Scheme.{0}} {Ω : Type} [Field Ω] [Algebra o Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ κ' : Type} {x : κ → Ω} (h : CoordTie o ξ x) (e : κ' → κ)
    (he : Function.Surjective e) (x' : κ' → Ω) (hx : ∀ c, x' c = x (e c)) : CoordTie o ξ x' := by
  obtain rfl : x' = fun c => x (e c) := funext hx
  have hc : ∀ c p, InChart ξ (fun c => x (e c)) c p ↔ InChart ξ x (e c) p := fun c p =>
    and_congr Iff.rfl (he.forall (p := fun c' => x c' / x (e c) ∈ regAt ξ p)).symm
  refine ⟨h.gen, fun p => ?_, fun c h0 => ?_, fun c h0 a => ?_⟩
  · obtain ⟨c, hp⟩ := h.cover p
    obtain ⟨c, rfl⟩ := he c
    exact ⟨c, (hc c p).2 hp⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (e c) h0
    exact ⟨U, hU, fun q => (hq q).trans (exists_congr fun _ => (hc c _).symm)⟩
  · have : (Set.range fun j => x (e j) / x (e c)) = Set.range fun j => x j / x (e c) :=
      he.range_comp fun j => x j / x (e c)
    simpa only [hc, this] using h.ring (e c) h0 a

theorem closure_genField (Ω : Type) [Field Ω] {I : Type} :
    Subfield.closure (Set.range (algebraMap Ω (FractionRing (MvPolynomial I Ω))) ∪
      {a | ∃ l l' : Option I, a = (l.elim 1 fun q => algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)) /
        (l'.elim 1 fun q => algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q))}) = ⊤ := by
  set F := Subfield.closure (Set.range (algebraMap Ω (FractionRing (MvPolynomial I Ω))) ∪
      {a | ∃ l l' : Option I, a = (l.elim 1 fun q => algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)) /
        (l'.elim 1 fun q => algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q))}) with hF
  have hp : ∀ p : MvPolynomial I Ω, algebraMap _ (FractionRing (MvPolynomial I Ω)) p ∈ F := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine Subfield.subset_closure (Or.inl ⟨a, ?_⟩)
      rw [IsScalarTower.algebraMap_apply Ω (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))]
      rfl
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp (Subfield.subset_closure (Or.inr ⟨some i, none, ?_⟩))
      simp
  refine eq_top_iff.2 fun a _ => ?_
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial I Ω) a
  exact div_mem (hp p) (hp q)

end Model

theorem exists_genericFlag : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (d : ℕ), A.ξ ≫ A.f = y₀ ≫ Y.j → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree A p) → (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ A.R p)) → A.IsCover d → ∃ (Ω' : Type) (_ : Field Ω') (_ : CharZero Ω') (i : Ω →+* Ω') (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω') (𝔐 : HodgeCpt Y S y') (g : 𝔐.X ⟶ A.X) (b : ∀ s, Fin (labelRk D s) → 𝔐.Li) (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module 𝔐.Ω₀ Li₀) (M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀) (j : Li₀ →+ 𝔐.Li) (V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀), GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ A.ξ g i ∧ 𝔐.f = g ≫ A.f ∧ 𝔐.R = A.R ∧ (∀ p ∈ S, HT.HTFree 𝔐 p) ∧ (∀ s, Submodule.span Ω' (Set.range (b s)) = 𝔐.Vgen s) ∧ (∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s) ∧ (letI := 𝔐.fn.toAlgebra; IsGenericFlag (Ω' := Ω') j V₀ b d) := by
  intro hW E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y A y₀ d hy hS hHT hζ hcov
  classical
  haveI : Finite (GenIx (labelRk D)) := by unfold GenIx; infer_instance
  let Ω' := GenField Ω (labelRk D)
  let i : Ω →+* Ω' := algebraMap Ω Ω'
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω Ω').injective

  let x : ((k : K) → J k) → Ω := fun c' => ∏ k, y ⟨k, c' k⟩
  let M₁ : PModel ℤ x :=
    { X := A.X, ξ := A.ξ, s := specZIsTerminal.from _, hover := specZIsTerminal.hom_ext _ _, all := A.all, tie := A.tie }
  let w : Option (GenIx (labelRk D)) → Ω' :=
    fun o => o.elim 1 fun q => algebraMap (MvPolynomial (GenIx (labelRk D)) Ω) Ω' (MvPolynomial.X q)
  obtain ⟨M₂, f₂, hd₂⟩ := GlobalTheory.T.exists_join_model_dominates ℤ Ω _ x M₁ Ω' i _ w (fun a => by simp)
    ⟨none, one_ne_zero⟩ (closure_genField Ω)
  obtain ⟨κ₃, _, y₃, M₃, f₃, hd₃, hN, -, -⟩ := GlobalTheory.T.exists_normal_dominating_model ℤ Ω' _ _ M₂ Ω'
  letI : Fintype κ₃ := Fintype.ofFinite κ₃
  let y' : (Σ _ : Unit, κ₃) → Ω' := fun q => y₃ q.2
  have htie : CoordTie ℤ M₃.ξ (fun c' : (k : Unit) → κ₃ => ∏ k, y' ⟨k, c' k⟩) :=
    coordTie_along M₃.tie (fun c' => c' ()) (fun a => ⟨fun _ => a, rfl⟩) _ fun c' => by simp [y']
  have hd₃' : M₃.ξ ≫ f₃ = M₂.ξ := by
    have h := hd₃
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at h
    rw [h, show algebraMap Ω' Ω' = RingHom.id Ω' from rfl, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have hdh : GlobalTheory.CompanionTheory.Ar.Dominates M₃.ξ A.ξ (f₃ ≫ f₂) i := by
    show M₃.ξ ≫ f₃ ≫ f₂ = _
    rw [← Category.assoc, hd₃']
    exact hd₂
  have hnormal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₃.X := (GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω' M₃.ξ M₃.tie.gen M₃.all).2.1 hN

  obtain ⟨A', e, j₁, m, he, hf, hm, hcst, hR, hext, hpt, hHT', hV⟩ := GlobalTheory.T.hodge_cpt_field_extension E H D l Xo c _ _ Y S Ω Ω' i K Unit
    J (fun _ => κ₃) y y' A y₀ M₃.X M₃.ξ (f₃ ≫ f₂) hy hS (fun p hp => (hHT p hp).2) M₃.all
    (by convert htie using 1 <;> first | exact Subsingleton.elim _ _ | skip) hnormal hdh
  have hd' : GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ (e.hom ≫ f₃ ≫ f₂) i := by
    show A'.ξ ≫ e.hom ≫ f₃ ≫ f₂ = _
    rw [← Category.assoc, he]
    exact hdh
  have hf' : A'.f = (e.hom ≫ f₃ ≫ f₂) ≫ A.f := hf.trans (Category.assoc _ _ _).symm
  have hfn : GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ₀ A'.f (i.comp A.fn) := by
    have h : A.ξ ≫ A.f = Spec.map (CommRingCat.ofHom A.fn) ≫ A.ξ₀ := A.fn_over
    have h' : A'.ξ ≫ e.hom ≫ f₃ ≫ f₂ = Spec.map (CommRingCat.ofHom i) ≫ A.ξ := hd'
    show A'.ξ ≫ A'.f = Spec.map (CommRingCat.ofHom (i.comp A.fn)) ≫ A.ξ₀
    have e1 : A'.ξ ≫ A'.f = (A'.ξ ≫ e.hom ≫ f₃ ≫ f₂) ≫ A.f :=
      (congrArg (A'.ξ ≫ ·) hf').trans (Category.assoc _ _ _).symm
    have e2 : Spec.map (CommRingCat.ofHom (i.comp A.fn)) =
        Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom A.fn) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
    rw [e1, h', Category.assoc, h, e2, Category.assoc]
  let 𝔐 : HodgeCpt Y S y' :=
    { A' with Ω₀ := A.Ω₀, fld₀ := A.fld₀, ξ₀ := A.ξ₀, gen₀ := A.gen₀, fn := i.comp A.fn, fn_over := hfn }
  have hy' : 𝔐.ξ ≫ 𝔐.f = (spMap i ≫ y₀) ≫ Y.j := by
    show A'.ξ ≫ A'.f = _
    have h' := hd'
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at h'
    rw [hf', ← Category.assoc, h', Category.assoc, hy, Category.assoc]

  obtain ⟨cst₀, y₁, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_constants_generic_point E H D l Xo c Y S Ω' Unit (fun _ => κ₃) y' 𝔐 (spMap i ≫ y₀) hy'
  obtain ⟨Li₀, _, _, M₀, j, V₀, cb, hj, hsm, hV₀, hcb, hli, hspan⟩ := GlobalTheory.T.constants_compatible_generic E H D l Xo c Y S Ω' Unit
    (fun _ => κ₃) y' 𝔐 (spMap i ≫ y₀) cst₀ y₁ hy' h₁ h₂ h₃
  have hfin := GlobalTheory.T.finrank_adjoin_vars_field 𝔐.Ω₀ Ω A.fn (GenIx (labelRk D)) d hcov.1 hcov.2
  obtain ⟨hsp, hgen⟩ := GlobalTheory.T.generic_flag_field_change 𝔐.Ω₀ Ω A.fn _ (labelRk D) d hcov.1 hfin Li₀ 𝔐.Li j V₀ cb hcb hsm hli
  refine ⟨Ω', inferInstance, inferInstance, i, Unit, inferInstance, fun _ => κ₃, inferInstance, y', 𝔐,
    e.hom ≫ f₃ ≫ f₂, _, Li₀, _, _, M₀, j, V₀, hd', hf', hR, fun p hp => ⟨?_, hHT' p hp⟩,
    fun s => (hsp s).trans (hspan s), hj, hV₀, hgen⟩
  exact GlobalTheory.T.hodge_comp_field_extension hW E H D l Xo c Y S Ω Ω' i K Unit J (fun _ => κ₃) y y' A 𝔐 (e.hom ≫ f₃ ≫ f₂) m j₁ y₀ p hp hd' hf' hR
    hext hpt hy (hζ p hp) (hHT p hp).1

end GlobalTheory.CompanionTheory.Ar.GenFlag
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptGoodReductionDegreeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_cpt_good_reduction_degree : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (d : ℕ), A.ξ ≫ A.f = y₀ ≫ Y.j → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree A p) → (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ A.R p)) → A.IsCover d → ∃ (Ω' : Type) (_ : Field Ω') (_ : CharZero Ω') (i : Ω →+* Ω') (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω') (𝔐 : HodgeCpt Y S y') (g : 𝔐.X ⟶ A.X) (b : ∀ s, Fin (labelRk D s) → 𝔐.Li) (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module 𝔐.Ω₀ Li₀) (M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀) (j : Li₀ →+ 𝔐.Li) (V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀), GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ A.ξ g i ∧ 𝔐.f = g ≫ A.f ∧ 𝔐.R = A.R ∧ (∀ p ∈ S, HT.HTFree 𝔐 p) ∧ (∀ s, Submodule.span Ω' (Set.range (b s)) = 𝔐.Vgen s) ∧ (∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s) ∧ (letI := 𝔐.fn.toAlgebra; IsGenericFlag (Ω' := Ω') j V₀ b d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenFlag.exists_genericFlag | exact GlobalTheory.CompanionTheory.Ar.GenFlag.exists_genericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.GenFlag.exists_genericFlag <;> assumption)
end
end
