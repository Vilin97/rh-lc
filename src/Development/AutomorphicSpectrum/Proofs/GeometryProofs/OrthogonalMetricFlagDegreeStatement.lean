module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSubFibreSubFib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFlagBasisAtStalkStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitNatCastStalk
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
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
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelProjectiveGenericFibreStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrthogonalMetricHermitianBundleStatement
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFrameSpansGeneric

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem finrank_lieModel_of_algebra (X : Scheme.{0}) (G : Over X) [GrpObj G] [Smooth G.hom] (A : Type) [CommRing A]
    [IsLocalRing A] (x : Sp A ⟶ X) (E₀ : Type) [AddCommGroup E₀] [Module A E₀] (M₀ : LieModel G x E₀) (K : Type)
    [Field K] [Algebra A K] (V : Type) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    (MV : LieModel G (spMap (algebraMap A K) ≫ x) V) : Module.finrank K V = Module.finrank A E₀ := by
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x = spMap (algebraMap A K) ≫ x := rfl
  have hsm : ∀ (a : A) (t : V), a • t = algebraMap A K a • t := fun a t => by
    rw [algebraMap_smul]
  have halg : (dualMap (algebraMap A K)).comp (algebraMap A (DualNumber A)) =
      (algebraMap K (DualNumber K)).comp (algebraMap A K) := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let b : epsAt (spMap (algebraMap A K) ≫ x) ⟶ epsAt x :=
    Over.homMk (spMap (dualMap (algebraMap A K))) (by
      change spMap (dualMap (algebraMap A K)) ≫ Spec.map _ ≫ x = Spec.map _ ≫ spMap (algebraMap A K) ≫ x
      simp only [spMap]
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, halg])
  have htan (e : E₀) : IsTanAt G (spMap (algebraMap A K) ≫ x) (b ≫ M₀.pt e) := by
    have h1 : (Over.homMk (spMap (algebraMap A K)) rfl : Over.mk (spMap (algebraMap A K) ≫ x) ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ G) = 1 := MonObj.comp_one _
    have h2 : spMap (algebraMap A K) ≫ (1 : Over.mk x ⟶ G).left = (1 : Over.mk (spMap (algebraMap A K) ≫ x) ⟶ G).left := by rw [← h1]; rfl
    have hv := M₀.tan e
    unfold IsTanAt at hv ⊢
    rw [← h2, ← hv]
    change Spec.map _ ≫ spMap (dualMap (algebraMap A K)) ≫ (M₀.pt e).left = spMap (algebraMap A K) ≫ Spec.map _ ≫ (M₀.pt e).left
    simp only [spMap]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    congr 1
    exact RingHom.ext fun a => by simp [dualMap]
  have ex : ∀ e, ∃ t, MV.pt t = b ≫ M₀.pt e :=
    fun e => MV.onto _ (htan e)
  choose f hf using ex
  let j : E₀ →ₗ[A] V :=
    { toFun := f
      map_add' := fun a b => MV.inj (by rw [MV.add, hf, hf, hf, M₀.add, comp_mul])
      map_smul' := fun c e => MV.inj (by
        rw [RingHom.id_apply, hsm, LieModel.pt_smul, hf, hf, LieModel.pt_smul, ← Category.assoc]
        have hb : b ≫ LieTangent.epsScale x c =
            LieTangent.epsScale (spMap (algebraMap A K) ≫ x) (algebraMap A K c) ≫ b := by
          apply Over.OverMorphism.ext
          change spMap (dualMap (algebraMap A K)) ≫ Spec.map (CommRingCat.ofHom (epsMul c)) =
            Spec.map (CommRingCat.ofHom (epsMul (algebraMap A K c))) ≫ spMap (dualMap (algebraMap A K))
          simp only [spMap]
          rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
          congr 1
          congr 1
          refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_smul]
        rw [hb, Category.assoc]) }

  have hl : ∀ e, ((MV.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap A K)) ≫ (M₀.pt e).left) := fun e => by
    change (MV.pt (f e)).left ≫ 𝟙 G.left = _
    rw [hf, Category.comp_id]
    rfl
  have hbc : IsBaseChange K j := GlobalTheory.T.lie_model_isBaseChange X G A K x E₀ V M₀ MV j hl
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.lie_model_finite_projective X G A x E₀ M₀
  haveI : Module.Free A E₀ := Module.free_of_flat_of_isLocalRing
  rw [← LinearEquiv.finrank_eq hbc.equiv, Module.finrank_baseChange]

theorem finrank_lieModel_eq (X : Scheme.{0}) (G : Over X) [GrpObj G] [Smooth G.hom] (A : Type) [CommRing A]
    [IsLocalRing A] (x : Sp A ⟶ X) (E₀ : Type) [AddCommGroup E₀] [Module A E₀] (M₀ : LieModel G x E₀) (K : Type)
    [Field K] (c : A →+* K) (y : Sp K ⟶ X) (hy : Spec.map (CommRingCat.ofHom c) ≫ x = y) (V : Type) [AddCommGroup V]
    [Module K V] (MV : LieModel G y V) : Module.finrank K V = Module.finrank A E₀ := by
  subst hy
  letI : Algebra A K := c.toAlgebra
  letI mR : Module A V := Module.compHom V c
  haveI tower : IsScalarTower A K V := ⟨fun a b t => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  exact finrank_lieModel_of_algebra X G A x E₀ M₀ K V MV

theorem lieModel_transport {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X} {Li : Type}
    [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) {L : Type} [Field L] {z z' : Sp L ⟶ X} (hz : z' = z)
    {T : Type} [AddCommGroup T] [Module L T] (TL : LieModel G z T) :
    ∃ MC : LieModel G z' T,
      (∀ t, (MC.pt t).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap L L))) ≫ (TL.pt t).left) ∧
      ∀ e t, M.ValAt z' e (MC.pt t) → M.ValAt z e (TL.pt t) := by
  subst hz
  have hd : dualMap (algebraMap L L) = RingHom.id _ := RingHom.ext fun a =>
    by ext <;> simp [dualMap]
  exact ⟨TL, fun t => by rw [hd, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp], fun _ _ h => h⟩

theorem lieModel_valFrame : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] (zL : Sp L ⟶ X) (T : Type) [AddCommGroup T] [Module L T] (TL : LieModel G zL T) (h : genPt ξ ⤳ centre zL) (Ix : Type) [Fintype Ix] (f : Ix → Li), IsCptGen ξ → LinearIndependent Ω f → Submodule.span Ω (Set.range f) = ⊤ → M.lat ⟨centre zL, h⟩ = Submodule.span (regAt ξ ⟨centre zL, h⟩) (Set.range f) → ∃ w : Ix → T, (∀ i, M.ValAt zL (f i) (TL.pt (w i))) ∧ LinearIndependent L w ∧ Submodule.span L (Set.range w) = ⊤ ∧ ∀ (A : Set Ix) (e : Li) (u : T), e ∈ Submodule.span (regAt ξ ⟨centre zL, h⟩) (f '' A) → M.ValAt zL e (TL.pt u) → u ∈ Submodule.span L (w '' A) := by
  intro X G _ _ _ Ω _ ξ Li _ _ M L _ zL T _ _ TL h Ix _ f hξ hli hsp hlat
  have ex : ∀ i, ∃ w, M.ValAt zL (f i) (TL.pt w) := fun i => by
    have hm : f i ∈ M.lat ⟨centre zL, h⟩ := by
      rw [hlat]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨v, hv⟩ := (M.exists_valAt_iff zL (f i)).2 ⟨h, hm⟩
    obtain ⟨t, rfl⟩ := TL.onto v hv.isTanAt
    exact ⟨t, hv⟩
  choose w hw using ex
  have key : ∀ (A : Set Ix) (e : Li), e ∈ Submodule.span (regAt ξ ⟨centre zL, h⟩) (f '' A) →
      ∃ u ∈ Submodule.span L (w '' A), M.ValAt zL e (TL.pt u) := by
    intro A e he
    induction he using Submodule.span_induction with
    | mem e he =>
      obtain ⟨i, hi, rfl⟩ := he
      exact ⟨w i, Submodule.subset_span ⟨i, hi, rfl⟩, hw i⟩
    | zero => exact ⟨0, zero_mem _, by rw [TL.pt_zero]; exact M.valAt_zero h⟩
    | add a b _ _ ha hb =>
      obtain ⟨u, hu, hv⟩ := ha
      obtain ⟨u', hu', hv'⟩ := hb
      exact ⟨u + u', add_mem hu hu', by rw [TL.add]; exact hv.add hv'⟩
    | smul c a _ ha =>
      obtain ⟨u, hu, hv⟩ := ha
      obtain ⟨_, s, rfl⟩ := c
      refine ⟨(Scheme.stalkClosedPointTo zL).hom s • u, Submodule.smul_mem _ _ hu, ?_⟩
      rw [TL.pt_smul]
      exact hv.smul h s
  have hz : Spec.map (CommRingCat.ofHom (algebraMap L L)) ≫ zL = zL := by
    have e : CommRingCat.ofHom (algebraMap L L) = 𝟙 (CommRingCat.of L) := rfl
    rw [e, Spec.map_id, Category.id_comp]
  obtain ⟨MC, h1, h2⟩ := lieModel_transport M hz TL
  have hc : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap L L)) ≫ zL) :=
    (congrArg centre hz).symm ▸ h
  have hspan : ⊤ ≤ Submodule.span L (Set.range w) := by
    intro t _
    have ht : t ∈ M.fibAt M.lat zL MC :=
      (GlobalTheory.T.lie_lattice_eval_fraction_field X G Ω ξ Li M L zL L T MC hξ inferInstance h hc t).2 ⟨TL.pt t, TL.tan t, h1 t⟩
    refine (Submodule.span_le.2 ?_ : M.fibAt M.lat zL MC ≤ _) ht
    rintro w' ⟨h', e, he, hv⟩
    have he' : e ∈ Submodule.span (regAt ξ ⟨centre zL, h⟩) (f '' Set.univ) := by
      rw [Set.image_univ, ← hlat]
      exact he
    obtain ⟨u, hu, hv'⟩ := key _ _ he'
    have := TL.inj ((h2 _ _ hv).unique hξ hv')
    rw [this]
    rwa [Set.image_univ] at hu
  obtain ⟨E₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre zL)) (X.fromSpecStalk (centre zL))
  have c1 := finrank_lieModel_eq X G _ _ E₀ M₀ Ω (genMap ξ ⟨centre zL, h⟩) ξ (LieTangent.spec_genMap ξ ⟨centre zL, h⟩) Li M
  have c2 := finrank_lieModel_eq X G _ _ E₀ M₀ L (Scheme.stalkClosedPointTo zL).hom zL (LieTangent.spec_centre zL) T TL
  have card : Fintype.card Ix = Module.finrank L T := by
    rw [c2, ← c1, Module.finrank_eq_card_basis (Module.Basis.mk hli hsp.ge)]
  refine ⟨w, hw, linearIndependent_of_top_le_span_of_card_eq_finrank hspan card, top_le_iff.1 hspan, ?_⟩
  intro A e u he hv
  obtain ⟨u', hu', hv'⟩ := key A e he
  rw [TL.inj (hv.unique hξ hv')]
  exact hu'

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFrameSpansGenericStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_frame_spans_generic : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] (zL : Sp L ⟶ X) (T : Type) [AddCommGroup T] [Module L T] (TL : LieModel G zL T) (h : genPt ξ ⤳ centre zL) (Ix : Type) [Fintype Ix] (f : Ix → Li), IsCptGen ξ → LinearIndependent Ω f → Submodule.span Ω (Set.range f) = ⊤ → M.lat ⟨centre zL, h⟩ = Submodule.span (regAt ξ ⟨centre zL, h⟩) (Set.range f) → ∃ w : Ix → T, (∀ i, M.ValAt zL (f i) (TL.pt (w i))) ∧ LinearIndependent L w ∧ Submodule.span L (Set.range w) = ⊤ ∧ ∀ (A : Set Ix) (e : Li) (u : T), e ∈ Submodule.span (regAt ξ ⟨centre zL, h⟩) (f '' A) → M.ValAt zL e (TL.pt u) → u ∈ Submodule.span L (w '' A) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_valFrame | exact GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_valFrame | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_valFrame <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrthogonalMetricFlagDegree

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem flagStep_mono' {Ω E' : Type} [Field Ω] [AddCommGroup E'] [Module Ω E'] {r : ℕ} (b : Fin r → E') {i i' : ℕ} (h : i ≤ i') :
    flagStep Ω b i ≤ flagStep Ω b i' :=
  Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk h)

theorem exists_satFlag {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {L : Type} [Field L] [NumberField L] (M : LieModel G ξ Li)
    (z : Sp (𝓞 L) ⟶ X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier) {r : ℕ}
    (b : Fin r → Li) (hr : ∀ i : ℕ, i ≤ r → Module.finrank (𝓞 L) (subFib M (flagStep Ω b i) z MB) = i) :
    ∃ A : SatFlag B r, ∀ i, A.F i = subFib M (flagStep Ω b i.val) z MB :=
  ⟨{ F := fun i => subFib M (flagStep Ω b i.val) z MB
     mono := fun _ _ hi => subFib_mono M (flagStep_mono' b (Fin.le_def.1 hi)) z MB
     sat := fun _ => subFib_saturated M _ z B MB
     rank := fun i => hr i.val (Nat.lt_succ_iff.1 i.2) }, fun _ => rfl⟩

theorem rank_fib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier),
    Fintype.card (CMType H) * (D.p + D.q) = Module.finrank (𝓞 L) B.carrier ∧
    (∀ s (i : ℕ), i ≤ labelRk D s → Module.finrank (𝓞 L) (subFib 𝔐.M (flagStep Ω (Fl.b s) i) z MB) = i) ∧
    ∀ s (i : ℕ), flagStep Ω (Fl.b s) i ≤ 𝔐.Vgen s := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 _ Fl L _ _ z B MB
  classical
  have hgen : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  haveI hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  have hs : genPt 𝔐.ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z) := 𝔐.all _
  have hu := fun n hn => isUnit_natCast_stalk 𝔐.X L (spMap (algebraMap (𝓞 L) L) ≫ z) n hn
  obtain ⟨b, hb1, hb2, hb3, hb4, hb5, hb6⟩ := GlobalTheory.T.exists_flag_basis_at_stalk E H D l Xo c Y S Ω K J y 𝔐 Fl ⟨_, hs⟩ hu
  obtain ⟨T, _, _, _, _, TL, j, hj, hbc⟩ := GlobalTheory.T.exists_lie_model_base_change 𝔐.X 𝔐.t.G (𝓞 L) L z B.carrier MB
  obtain ⟨w, hw1, hw2, hw3, hw4⟩ := GlobalTheory.T.lie_model_frame_spans_generic 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M L _ T TL hs
    (Σ s, Fin (labelRk D s)) _ hgen hb3 hb4 hb5
  have hbr := fun U => GlobalTheory.T.lie_model_projective_generic_fibre 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M L z B.carrier MB T TL j U hgen hj hbc
  refine ⟨?_, ?_, ?_⟩
  · rw [(hbr ⊥).1]
    have e1 := finrank_span_eq_card hw2
    rw [hw3, finrank_top] at e1
    rw [e1, Fintype.card_sigma, Fintype.sum_sum_type]
    have a1 : ∀ τ : CMType H, Fintype.card (Fin (labelRk D (Sum.inl τ))) = D.p := fun _ => Fintype.card_fin _
    have a2 : ∀ τ : CMType H, Fintype.card (Fin (labelRk D (Sum.inr τ))) = D.q := fun _ => Fintype.card_fin _
    simp only [a1, a2, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  · intro s i hi
    rw [(hbr _).2]
    let g : Fin i → Σ s, Fin (labelRk D s) := fun k => ⟨s, ⟨k.1, lt_of_lt_of_le k.2 hi⟩⟩
    have hg : Function.Injective g := by
      intro a b' hab
      simp only [g, Sigma.mk.injEq, heq_eq_eq, true_and, Fin.mk.injEq] at hab
      exact Fin.ext hab
    have himg : (fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) '' Set.range g = b s '' {k | (k : ℕ) < i} := by
      ext x
      constructor
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨⟨k.1, lt_of_lt_of_le k.2 hi⟩, k.2, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨_, ⟨⟨k.1, hk⟩, rfl⟩, rfl⟩
    have hspan : Submodule.span L {w' | ∃ e ∈ flagStep Ω (Fl.b s) i, 𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w')} =
        Submodule.span L (Set.range (w ∘ g)) := by
      apply le_antisymm
      · refine Submodule.span_le.2 ?_
        rintro w' ⟨e, he, hv⟩
        obtain ⟨h', hl⟩ := (LieModel.exists_valAt_iff 𝔐.M _ e).1 ⟨_, hv⟩
        have h2 := hb2 s i e (by rw [hb1]; exact he) hl
        rw [← himg] at h2
        have := hw4 (Set.range g) e w' h2 hv
        rwa [← Set.range_comp] at this
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨k, rfl⟩
        refine Submodule.subset_span ⟨b s ⟨k.1, lt_of_lt_of_le k.2 hi⟩, ?_, hw1 (g k)⟩
        rw [← hb1]
        exact Submodule.subset_span ⟨_, k.2, rfl⟩
    rw [hspan, finrank_span_eq_card (hw2.comp g hg), Fintype.card_fin]
  · intro s i
    rw [← hb1, ← hb6]
    exact Submodule.span_mono (Set.image_subset_range _ _)

theorem flag_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (h : LieMetric 𝔐.M y), h.Orth 𝔐.t.act → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∃ (A : FlagPair B (CMType H) D.p D.q), A.IsOrthFull ∧ (∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inl τ)) i.val) z MB ((A.W τ).F i)) ∧ ∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inr τ)) i.val) z MB ((A.S τ).F i) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 _ Fl h hO L _ _ z B MB hF
  obtain ⟨h1, h2, h3⟩ := rank_fib E H D l Xo c Y S Ω K J y 𝔐 Fl L z B MB
  have ho := GlobalTheory.T.orthogonal_metric_hermitian_bundle E H D l Xo c Y S Ω K J y 𝔐 h hO L z B MB hF
  have hex : ∀ s, ∃ A : SatFlag B (labelRk D s), ∀ i, A.F i = subFib 𝔐.M (flagStep Ω (Fl.b s) i.val) z MB := by
    intro s
    exact exists_satFlag 𝔐.M z B MB (Fl.b s) (h2 s)
  choose A hA using hex
  have hW : ∀ (τ : CMType H) (i : Fin (D.p + 1)), IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inl τ)) i.val) z MB ((A (.inl τ)).F i) := by
    intro τ i
    rw [hA (.inl τ) i]
    exact isSubFibre_subFib _ _ _ _
  have hS : ∀ (τ : CMType H) (i : Fin (D.q + 1)), IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inr τ)) i.val) z MB ((A (.inr τ)).F i) := by
    intro τ i
    rw [hA (.inr τ) i]
    exact isSubFibre_subFib _ _ _ _
  have hpart : ∀ s, FlagPair.part (⟨fun τ => A (.inl τ), fun τ => A (.inr τ)⟩ : FlagPair B (CMType H) D.p D.q) s =
      subFib 𝔐.M (flagStep Ω (Fl.b s) (labelRk D s)) z MB := by
    rintro (τ | τ)
    · exact hA (.inl τ) (Fin.last _)
    · exact hA (.inr τ) (Fin.last _)
  refine ⟨⟨fun τ => A (.inl τ), fun τ => A (.inr τ)⟩, ⟨?_, h1⟩, hW, hS⟩
  intro a b hab
  rw [hpart, hpart]
  exact ho a b hab _ _ (h3 a _) (h3 b _)

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrthogonalMetricFlagDegreeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.orthogonal_metric_flag_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (h : LieMetric 𝔐.M y), h.Orth 𝔐.t.act → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∃ (A : FlagPair B (CMType H) D.p D.q), A.IsOrthFull ∧ (∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inl τ)) i.val) z MB ((A.W τ).F i)) ∧ ∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inr τ)) i.val) z MB ((A.S τ).F i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFib.flag_fibre | exact GlobalTheory.CompanionTheory.Ar.FlagFib.flag_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFib.flag_fibre <;> assumption)
end
end
