module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistAutomorphism
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqOfEqGenericProjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorIffStatement
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
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeIsoCompatStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import Mathlib.NumberTheory.Height.NumberField
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwistedBundlesMatchModels
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwistedGramMatricesMatch

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistFrameCompat

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TwistInterior

theorem genPt_specializes_of_injective {Ω : Type} [Field Ω] {R : CommRingCat.{0}} [IsDomain R]
    (φ : R ⟶ CommRingCat.of Ω) (hφ : Function.Injective φ.hom) (q : Spec R) :
    genPt (Spec.map φ) ⤳ q := by
  refine (PrimeSpectrum.le_iff_specializes (genPt (Spec.map φ) : PrimeSpectrum R) q).1 ?_
  intro a ha
  have hm : φ.hom a ∈ IsLocalRing.maximalIdeal Ω := ha
  have h0 : φ.hom a = 0 := by
    by_contra hne
    exact hm (isUnit_iff_ne_zero.2 hne)
  have : a = 0 := hφ (h0.trans (map_zero φ.hom).symm)
  rw [this]
  exact zero_mem _

theorem lift_transfer {X X' W W' V : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R]
    (e : X' ≅ X) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (hξ : ξ' ≫ e.hom = ξ)
    (hgen : IsCptGen ξ') (hall : ∀ q : X', genPt ξ' ⤳ q) (hdom : ∀ p : X', IsDomain (X'.presheaf.stalk p))
    (sW : W ⟶ Sp R) (hproj : IsProjOver sW)
    (f : X ⟶ W) (f' : X' ⟶ W') (j : V ⟶ W) (j' : V ⟶ W') [Mono j'] (Ψ : V ≅ V) (x x' : Sp Ω ⟶ V)
    (hx : x' ≫ Ψ.inv = x) (hf : ξ ≫ f = x ≫ j) (hf' : ξ' ≫ f' = x' ≫ j') (p : X')
    (hu : ∃ u' : Spec (X'.presheaf.stalk p) ⟶ V, u' ≫ j' = X'.fromSpecStalk p ≫ f') :
    ∃ u : Spec (X.presheaf.stalk (e.hom p)) ⟶ V, u ≫ j = X.fromSpecStalk (e.hom p) ≫ f := by
  obtain ⟨u', hu'⟩ := hu
  haveI := hdom p
  have h' : ξ' (IsLocalRing.closedPoint Ω) ⤳ p := hall p
  let φ : X'.presheaf.stalk p ⟶ CommRingCat.of Ω := X'.presheaf.stalkSpecializes h' ≫ Scheme.stalkClosedPointTo ξ'
  let ξp : Sp Ω ⟶ Spec (X'.presheaf.stalk p) := Spec.map φ
  have hξp : ξp ≫ X'.fromSpecStalk p = ξ' := by
    simp only [ξp, φ]
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ'
  have hgp : ∀ q, genPt ξp ⤳ q := genPt_specializes_of_injective φ (hgen.inj ⟨p, hall p⟩)
  have hxu : ξp ≫ u' = x' := by
    rw [← cancel_mono j', Category.assoc, hu', ← Category.assoc, hξp, hf']
  have heq : u' ≫ Ψ.inv ≫ j = X'.fromSpecStalk p ≫ e.hom ≫ f := by
    refine GlobalTheory.T.eq_of_eq_generic_projective R (Spec (X'.presheaf.stalk p)) W sW Ω ξp _ _ hproj hgp ?_
    have h1 : ξp ≫ u' ≫ Ψ.inv ≫ j = x ≫ j := by rw [reassoc_of% hxu, reassoc_of% hx]
    have h2 : ξp ≫ X'.fromSpecStalk p ≫ e.hom ≫ f = x ≫ j := by rw [reassoc_of% hξp, reassoc_of% hξ, hf]
    rw [h1, h2]
  haveI : IsIso (e.hom.stalkMap p) := inferInstance
  refine ⟨inv (Spec.map (e.hom.stalkMap p)) ≫ u' ≫ Ψ.inv, ?_⟩
  rw [Category.assoc, Category.assoc, heq, ← Scheme.SpecMap_stalkMap_fromSpecStalk_assoc, IsIso.inv_hom_id_assoc]

end GlobalTheory.CompanionTheory.Ar.TwistInterior

namespace GlobalTheory.CompanionTheory.Ar.TwistInterior

theorem interior_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ z : Sp ℂ ⟶ A'.X, A'.Interior z ↔ A.Interior (z ≫ e.hom) := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J _ y A A' e x x' hβ hβ' hΦ hξ hf hf' hfst hsnd _ _ _ z
  have hΦ' : Φ.inv ≫ Xo.s = Xo.s := (Iso.inv_comp_eq Φ).2 hΦ.symm
  let ΦF : Xo.XF c ≅ Xo.XF c :=
    { hom := pullback.lift (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Φ.hom)
        (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
        (by rw [Category.assoc, hΦ, pullback.condition])
      inv := pullback.lift (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Φ.inv)
        (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
        (by rw [Category.assoc, hΦ', pullback.condition])
      hom_inv_id := pullback.hom_ext
        (by simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Iso.hom_inv_id, Category.comp_id,
          Category.id_comp])
        (by simp only [Category.assoc, pullback.lift_snd, Category.id_comp])
      inv_hom_id := pullback.hom_ext
        (by simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Iso.inv_hom_id, Category.comp_id,
          Category.id_comp])
        (by simp only [Category.assoc, pullback.lift_snd, Category.id_comp]) }
  have hxx : x ≫ ΦF.hom = x' := by
    apply pullback.hom_ext
    · simp only [ΦF, Category.assoc, pullback.lift_fst, hfst]
    · simp only [ΦF, Category.assoc, pullback.lift_snd, hsnd]
  obtain ⟨hjY, hA⟩ := GlobalTheory.T.hodge_cpt_interior_iff E H D l Xo c O β Y S Ω K J y A (z ≫ e.hom) hβ
  obtain ⟨hjY', hA'⟩ := GlobalTheory.T.hodge_cpt_interior_iff E H D l Xo c O' β' Y' S Ω K J y A' z hβ'
  have hc : centre (z ≫ e.hom) = e.hom (centre z) := rfl
  rw [hA, hA', hc]
  constructor
  · exact lift_transfer e A.ξ A'.ξ hξ A'.tie.gen A'.all (fun p => (A'.normal p).1) Y.s Y.proj A.f A'.f Y.j Y'.j
      ΦF x x' (by rw [← hxx, Category.assoc, Iso.hom_inv_id, Category.comp_id]) hf hf' (centre z)
  · intro hu
    have key := lift_transfer e.symm A'.ξ A.ξ (by rw [← hξ, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id])
      A.tie.gen A.all (fun p => (A.normal p).1) Y'.s Y'.proj A'.f A.f Y'.j Y.j ΦF.symm x' x
      (by rw [Iso.symm_inv, hxx]) hf' hf (e.hom (centre z)) hu
    have hp : e.symm.hom (e.hom (centre z)) = centre z := by
      rw [Iso.symm_hom, ← Scheme.Hom.comp_apply, e.hom_inv_id]
      rfl
    rwa [hp] at key

end GlobalTheory.CompanionTheory.Ar.TwistInterior
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistFrameCompatStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_component_twist_frame_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ z : Sp ℂ ⟶ A'.X, A'.Interior z ↔ A.Interior (z ≫ e.hom) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwistInterior.interior_iff | exact GlobalTheory.CompanionTheory.Ar.TwistInterior.interior_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.TwistInterior.interior_iff <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelTwistedComparison

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieIntertwining

theorem act_intertwine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : HostAut H) (Ω : Type) [Field Ω]
    (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (tΩ : SAB H (Sp Ω))
    (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ') (V V' : Type) [AddCommGroup V] [Module Ω V]
    [AddCommGroup V'] [Module Ω V'] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V')
    (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (φ : V ≃ₗ[Ω] V'),
    M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M.pt v).left ∧ w.left ≫ m'.φ = (M'.pt (φ v)).left) →
    ∀ a v, φ (ρ (g.s a) v) = ρ' a (φ v) := by
  intro E _ _ _ H g Ω _ X X' ξ ξ' t t' tΩ m m' V V' _ _ _ _ M M' ρ ρ' φ hM hM' tie a v
  obtain ⟨w, hw, hw'⟩ := tie v
  obtain ⟨w₃, hw₃, hw₃'⟩ := tie (ρ (g.s a) v)

  have h1 : (M.pt (ρ (g.s a) v)).left = (M.pt v).left ≫ (t.act.act (g.s a)).left := by
    rw [hM (g.s a) v]; rfl
  have h2 : (w.left ≫ (tΩ.act.act (g.s a)).left) ≫ m.φ = w₃.left ≫ m.φ := by
    rw [hw₃, h1, ← hw, Category.assoc, Category.assoc, m.act]
  have h3 : (w.left ≫ (tΩ.act.act (g.s a)).left) ≫ tΩ.G.hom = w₃.left ≫ tΩ.G.hom := by
    rw [Category.assoc, Over.w, Over.w, Over.w]
  have h4 : w.left ≫ (tΩ.act.act (g.s a)).left = w₃.left := m.cart.1.hom_ext h2 h3
  have h5 : (M'.pt (φ (ρ (g.s a) v))).left = (M'.pt (ρ' a (φ v))).left := by
    have h6 : (tΩ.act.act (g.s a)).left ≫ m'.φ = m'.φ ≫ (t'.act.act a).left := m'.act a
    rw [← hw₃', ← h4, hM' a (φ v), Over.comp_left, ← hw']
    exact (Category.assoc _ _ _).trans ((congrArg (w.left ≫ ·) h6).trans (Category.assoc _ _ _).symm)
  exact M'.inj (Over.OverMorphism.ext h5)

end GlobalTheory.CompanionTheory.Ar.LieIntertwining
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelTwistedComparisonStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_twisted_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : HostAut H) (Ω : Type) [Field Ω]
    (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (tΩ : SAB H (Sp Ω))
    (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ') (V V' : Type) [AddCommGroup V] [Module Ω V]
    [AddCommGroup V'] [Module Ω V'] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V')
    (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (φ : V ≃ₗ[Ω] V'),
    M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M.pt v).left ∧ w.left ≫ m'.φ = (M'.pt (φ v)).left) →
    ∀ a v, φ (ρ (g.s a) v) = ρ' a (φ v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieIntertwining.act_intertwine | exact GlobalTheory.CompanionTheory.Ar.LieIntertwining.act_intertwine | (intros; apply GlobalTheory.CompanionTheory.Ar.LieIntertwining.act_intertwine <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CmpHodgeTied

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CmpTiedK

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem cmpHodgeTied : HodgeComparisonCompatibility := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J _ y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR
  obtain ⟨t, tΩ, k, m, mA, mA', u, u', M₁, φ, hmA, E1, E2, E3, hk, htie, hT, hL⟩ :=
    GlobalTheory.CompanionTheory.Ar.FrameRebase.tied_generic_fibre E H D l Xo c O O' β β' Y Y' g Φ n S Ω K J y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR
  have E1' : m.φ ≫ k.φ ≫ A.m.φ = u.φ ≫ Y.m.φ := by rw [← Category.assoc, ← hmA, E1]
  have hact : ∀ a v, φ (A.ρ (g.s a) v) = A'.ρ a (φ v) :=
    GlobalTheory.T.lie_model_twisted_comparison E H g Ω A.X A'.X A.ξ A'.ξ A.t A'.t tΩ mA mA' A.Li A'.Li A.M A'.M A.ρ A'.ρ φ A.act A'.act
      (fun v => by
        obtain ⟨w, hw, hw'⟩ := htie v
        exact ⟨w, by rw [hmA, ← Category.assoc, hw, hk], hw'⟩)
  refine ⟨φ, fun v => ?_, hact,
    PositivityTheory.UnitarySelfGeneration.twisted_bundles_match_models E H D l Xo c O O' β β' Y Y' g Φ n S Ω K J y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR t tΩ k m mA' u u' M₁ φ E1' E2 E3 hk htie hT hL hact,
    fun z => ⟨GlobalTheory.T.hodge_component_twist_frame_compat E H D l Xo c O O' β β' Y Y' g Φ n S Ω K J y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR z, fun hz r b Γ =>
      (GlobalTheory.T.lie_model_base_change_iso_compat E H A.X A'.X e Ω A.ξ A'.ξ A.t t k A.Li A.M M₁ hξ hk z r b Γ).symm.trans
        (PositivityTheory.UnitarySelfGeneration.twisted_gram_matrices_match E H D l Xo c O O' β β' Y Y' g Φ n S Ω K J y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR t tΩ k m mA' u u' M₁ φ E1' E2 E3 hk htie hT hL z hz r b Γ)⟩⟩
  obtain ⟨w, hw, hw'⟩ := htie v
  have h1 : u'.φ ≫ Y'.oF.t.G.hom = (twistSAB tΩ g).G.hom ≫ x' := u'.cart.1.w
  have h2 : u.φ ≫ Y.oF.t.G.hom = tΩ.G.hom ≫ x := u.cart.1.w
  have key : u'.φ ≫ Y'.oF.t.G.hom ≫ pullback.snd _ _ = u.φ ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ := by
    rw [reassoc_of% h1, reassoc_of% h2, hs]
    rfl
  refine ⟨w.left ≫ u.φ, w.left ≫ u'.φ, ?_, ?_, ?_, ?_⟩
  · simp only [Category.assoc]
    rw [← E1', ← hk v, ← hw]
    simp only [Category.assoc]
  · calc (w.left ≫ u'.φ) ≫ Y'.m.φ = w.left ≫ (u'.φ ≫ Y'.m.φ) := Category.assoc _ _ _
      _ = w.left ≫ (mA'.φ ≫ A'.m.φ) := congrArg (fun f => w.left ≫ f) E2.symm
      _ = (w.left ≫ mA'.φ) ≫ A'.m.φ := (Category.assoc _ _ _).symm
      _ = _ := by rw [hw']
  · calc (w.left ≫ u'.φ) ≫ Y'.m0.toSABMap.φ = w.left ≫ (u'.φ ≫ Y'.m0.toSABMap.φ) := Category.assoc _ _ _
      _ = w.left ≫ (u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ) := congrArg (fun f => w.left ≫ f) E3
      _ = _ := (Category.assoc _ _ _).symm
  · exact (Category.assoc _ _ _).trans ((congrArg (fun f => w.left ≫ f) key).trans (Category.assoc _ _ _).symm)

end GlobalTheory.CompanionTheory.Ar.CmpTiedK

namespace PositivityTheory.UnitarySelfGeneration

theorem cmpHodgeTiedAlt : GlobalTheory.CompanionTheory.Ar.HodgeComparisonCompatibility :=
  @GlobalTheory.CompanionTheory.Ar.CmpTiedK.cmpHodgeTied

end PositivityTheory.UnitarySelfGeneration
end
end
end
