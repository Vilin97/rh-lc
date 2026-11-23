module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiSecPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperCohomologyRestrictAdjointBijective
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHypercohomologyOneBaseChangeFlatBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAffineCoverInfClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechHyperCohomologyCoverRefinement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechDR

theorem restrict_cover_affine_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (U : J → X.Opens), ⨆ i, U i = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) (Monotone.functor (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op)) := by
  intro R _ X s J U hU
  apply restrict_bijective_one_of_basis s
  · intro T
    have hT : IsAffineOpen T.unop.1 := T.unop.2
    let G : Set Γ(X, T.unop.1) := {f | ∃ j, X.basicOpen f ≤ U j}
    have hG : Ideal.span G = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      have hxU : x ∈ ⨆ i, U i := by rw [hU]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxU
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := U j) ⟨x, hj⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨j, hf⟩⟩, hxf⟩
    obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X, T.unop.1)) := by
        ext f
        constructor
        · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
        · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
      exact hR ▸ hF
    · intro i S u hu
      obtain ⟨j, hj⟩ := hFG (F.equivFin.symm i).2
      set f : Γ(X, T.unop.1) := (F.equivFin.symm i).1
      have hW : IsAffineOpen (X.basicOpen f) := hT.basicOpen f
      have hWT : X.basicOpen f ≤ T.unop.1 := X.basicOpen_le f
      have hSW : S.unop.1 ≤ X.basicOpen f := by
        have h1 : X.basicOpen (X.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
          X.basicOpen_of_isUnit hu
        rw [Scheme.basicOpen_res] at h1
        rw [← h1]; exact inf_le_right
      let t : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨⟨_, hW⟩, j, hj⟩
      refine ⟨Opposite.op t, (homOfLE (show (⟨_, hW⟩ : X.affineOpens) ≤ T.unop from hWT)).op,
        (homOfLE (show S.unop ≤ (⟨_, hW⟩ : X.affineOpens) from hSW)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  · intro t₁ t₂ S h₁ h₂
    refine ⟨1, fun _ ↦ 1, ?_, fun _ S' u _ ↦ ?_⟩
    · rw [Ideal.span_eq_top_iff_finite]
      exact ⟨{1}, by simp, by simp⟩
    · obtain ⟨j, hj⟩ := t₁.unop.2
      have hS'S : S'.unop ≤ S.unop := leOfHom u.unop
      have hS1 : S.unop ≤ t₁.unop.1 := leOfHom h₁.unop
      have hS2 : S.unop ≤ t₂.unop.1 := leOfHom h₂.unop
      let t₃ : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨S'.unop, j, le_trans (hS'S.trans hS1) hj⟩
      refine ⟨Opposite.op t₃, ⟨(homOfLE (show t₃ ≤ t₁.unop from hS'S.trans hS1)).op⟩,
        ⟨(homOfLE (show t₃ ≤ t₂.unop from hS'S.trans hS2)).op⟩, ⟨𝟙 _⟩⟩

end GlobalTheory.CechDR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechHyperCohomologyCoverRefinementStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cech_hyper_cohomology_cover_refinement : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (U : J → X.Opens), ⨆ i, U i = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) (Monotone.functor (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op)) := by
  first | exact @GlobalTheory.CechDR.restrict_cover_affine_bijective | exact GlobalTheory.CechDR.restrict_cover_affine_bijective | (intros; apply GlobalTheory.CechDR.restrict_cover_affine_bijective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperCohomologyRestrictAdjointBijectiveStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hyper_cohomology_restrict_adjoint_bijective : ∀ (R : Type) [CommRing R] (C C' : Type) [Category.{0} C] [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C ⥤ C'), (G ⊣ H) → Function.Bijective (pullHyp1 (CoefMap.restrict F G)) := by
  first | exact @GlobalTheory.AdjHyp.main | exact GlobalTheory.AdjHyp.main | (intros; apply GlobalTheory.AdjHyp.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechHyperCohomologyAffineLatticeCover

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoverHyp

theorem restrict_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op)) := by
  intro R _ X s J _ _ U hU hinf hcov
  classical
  haveI := Fintype.ofFinite J
  let B : Type := {V : X.affineOpens // ∃ i, V.1 ≤ (U i).1}
  have hne : ∀ V : B, (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).Nonempty := fun V => by
    obtain ⟨i, hi⟩ := V.2
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  let σ : B → J := fun V => (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).inf' (hne V) id
  let u : J → B := fun i => ⟨U i, i, le_rfl⟩
  have hσ : ∀ V : B, V.1.1 ≤ (U (σ V)).1 := fun V =>
    Finset.inf'_induction (p := fun i => V.1.1 ≤ (U i).1) (hne V) id
      (fun a ha b hb => by rw [hinf]; exact le_inf ha hb) fun i hi => (Finset.mem_filter.1 hi).2
  have gc : GaloisConnection σ u := fun V i =>
    ⟨fun h => (hσ V).trans (hU h), fun h =>
      Finset.inf'_le (s := Finset.univ.filter fun i : J => V.1.1 ≤ (U i).1) (id : J → J)
        (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)⟩
  let incl : Bᵒᵖ ⥤ AffOp X := (Monotone.functor (f := (Subtype.val : B → X.affineOpens)) fun _ _ h ↦ h).op
  have b1 : Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) incl)) :=
    GlobalTheory.T.cech_hyper_cohomology_cover_refinement R X s J (fun i => (U i).1) hcov
  have b2 := GlobalTheory.T.hyper_cohomology_restrict_adjoint_bijective R Bᵒᵖ Jᵒᵖ (incl ⋙ OAff s) gc.monotone_u.functor.op gc.monotone_l.functor.op
    gc.adjunction.op
  have e : ∀ c, pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op) c =
      pullHyp1 (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op)
        (pullHyp1 (CoefMap.restrict (OAff s) incl) c) := fun c =>
    (pullHyp1_eq_of_natTrans (CoefMap.restrict (OAff s) hU.functor.op)
      ((CoefMap.restrict (OAff s) incl).comp (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op))
      (𝟙 _) (fun T b => mp_id (OAff s) _ b) c).trans (pullHyp1_comp _ _ c)
  have := b2.comp b1
  exact (funext e : _ = _) ▸ this

end GlobalTheory.CoverHyp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechHyperCohomologyAffineLatticeCoverStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cech_hyper_cohomology_affine_lattice_cover : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op)) := by
  first | exact @GlobalTheory.CoverHyp.restrict_bijective | exact GlobalTheory.CoverHyp.restrict_bijective | (intros; apply GlobalTheory.CoverHyp.restrict_bijective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestTail

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Div.BaseChangeIso

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (e : M →ₗ[R] N) (e' : M' →ₗ[R'] N') (f : M →ₛₗ[algebraMap R R'] M') (g : N →ₛₗ[algebraMap R R'] N'), Function.Bijective e → Function.Bijective e' → (∀ x, e' (f x) = g (e x)) → (Function.Bijective (liftSemi f) ↔ Function.Bijective (liftSemi g)) := by
  intro R R' _ _ _ M _ _ N _ _ M' _ _ N' _ _ e e' f g he he' hc
  have key : (e' ∘ liftSemi f) = (liftSemi g ∘ e.baseChange R') := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x m => simp [liftSemi_tmul, LinearMap.baseChange_tmul, hc]
    | add x y hx hy => simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
  have hb : Function.Bijective (e.baseChange R') := by
    have h := ((LinearEquiv.ofBijective e he).baseChange R R' M N).bijective
    convert h using 1
    refine congrArg DFunLike.coe ?_
    ext m
    simp
  rw [← Function.Bijective.of_comp_iff' he' (liftSemi f), key, Function.Bijective.of_comp_iff _ hb]

end GlobalTheory.Div.BaseChangeIso
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperCohomologyFlatBaseChange

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Div.HypFlatBaseChange

theorem square {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {X X' : Scheme.{0}}
    {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap σ)
    {J : Type} [Preorder J] (U : J → X.affineOpens) (hU : Monotone U) (U' : J → X'.affineOpens)
    (hU' : Monotone U') (hle : ∀ i, (U' i).1 ≤ φ ⁻¹ᵁ (U i).1)
    (g : CoefMap σ (hU.functor.op ⋙ OAff s) (hU'.functor.op ⋙ OAff s')) (θ : 𝟭 _ ⟶ g.G)
    (hg : ∀ T b, g.α T (mp (hU.functor.op ⋙ OAff s) (θ.app T) b) =
      GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), hle _⟩ b) (c : HH1 s) :
    pullHyp1 (CoefMap.restrict (OAff s') hU'.functor.op) (pullHH1 w c) =
      pullHyp1 g (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op) c) := by
  have hp : Monotone fun i : J ↦ (⟨(U' i, U i), hle i⟩ : Pair φ) := fun i j hij ↦ ⟨hU' hij, hU hij⟩
  have k := congrArg (pullHyp1 (CoefMap.restrict (OPair φ s') hp.functor.op)) (isPull1_pullHH1 w c)
  rw [← pullHyp1_comp, ← pullHyp1_comp] at k
  rw [← pullHyp1_comp]
  have k1 := pullHyp1_eq_of_natTrans
    (F' := hU'.functor.op ⋙ OAff s')
    ((pairRes φ s').comp (CoefMap.restrict (OPair φ s') hp.functor.op))
    (CoefMap.restrict (OAff s') hU'.functor.op) (𝟙 _) (fun T b ↦ mp_id (OAff s') _ b) (pullHH1 w c)
  have k2 := pullHyp1_eq_of_natTrans
    (F' := hU'.functor.op ⋙ OAff s')
    ((pairPull w).comp (CoefMap.restrict (OPair φ s') hp.functor.op))
    ((CoefMap.restrict (OAff s) hU.functor.op).comp g) (Functor.whiskerRight θ hU.functor.op)
    (fun T b ↦ hg T b) c
  exact k1.symm.trans (k.symm.trans k2)

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), IsSeparated s → QuasiCompact s → Function.Bijective (liftSemi (pullHH1 h.w)) := by
  intro R R' _ _ _ _ X X' s s' φ h hs hq
  obtain ⟨J, _, _, U, hU, hinf, hcov⟩ := GlobalTheory.exists_finite_affine_cover_infClosed R X s hs hq
  haveI : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  let U' : J → X'.affineOpens := fun i ↦ ⟨φ ⁻¹ᵁ (U i).1, (U i).2.preimage φ⟩
  have hU' : Monotone U' := fun i j hij x hx ↦ hU hij hx
  have hinf' : ∀ i j, (U' (i ⊓ j)).1 = (U' i).1 ⊓ (U' j).1 := fun i j ↦ by
    change φ ⁻¹ᵁ (U (i ⊓ j)).1 = _
    rw [hinf]; rfl
  have hcov' : ⨆ i, (U' i).1 = ⊤ := by
    change ⨆ i, φ ⁻¹ᵁ (U i).1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, hcov]; rfl
  have hp : Monotone fun i : J ↦ (⟨(U' i, U i), le_rfl⟩ : Pair φ) := fun i j hij ↦ ⟨hU' hij, hU hij⟩
  haveI : Finite Jᵒᵖ := Finite.of_equiv J Opposite.equivToOpposite
  haveI : ∀ T T' : Jᵒᵖ, Finite (T ⟶ T') := fun T T' ↦
    Finite.of_injective (β := T'.unop ⟶ T.unop) Quiver.Hom.unop Quiver.Hom.unop_inj
  have hb := GlobalTheory.T.deRhamHypercohomologyOne_baseChange_flat_bijective R R' Jᵒᵖ (hU.functor.op ⋙ OAff s) (hU'.functor.op ⋙ OAff s')
    (fun T ↦ GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), le_rfl⟩)
    (fun a b ↦ (pairPull h.w).naturality (hp.functor.op.map a) b)
    (fun T ↦ semiHom_secPull h.w ⟨(U' T.unop, U T.unop), le_rfl⟩)
    (fun T f hf ↦ GlobalTheory.CechDR.bijective_liftSemi_secPull R R' X X' s s' φ h ⟨(U' T.unop, U T.unop), le_rfl⟩ rfl f hf)
  have hsq := fun c ↦ square h.w U hU U' hU' (fun _ ↦ le_rfl)
    ⟨𝟭 _, fun T ↦ GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), le_rfl⟩,
      fun a b ↦ (pairPull h.w).naturality (hp.functor.op.map a) b,
      fun T ↦ semiHom_secPull h.w ⟨(U' T.unop, U T.unop), le_rfl⟩⟩ (𝟙 _)
    (fun T b ↦ congrArg (GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), le_rfl⟩)
      (mp_id (hU.functor.op ⋙ OAff s) T b)) c
  exact (GlobalTheory.Div.BaseChangeIso.main R R' (HH1 s) (Hyp1 (hU.functor.op ⋙ OAff s)) (HH1 s')
    (Hyp1 (hU'.functor.op ⋙ OAff s')) (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op))
    (pullHyp1 (CoefMap.restrict (OAff s') hU'.functor.op)) (pullHH1 h.w) _
    (GlobalTheory.T.cech_hyper_cohomology_affine_lattice_cover R X s J U hU hinf hcov) (GlobalTheory.T.cech_hyper_cohomology_affine_lattice_cover R' X' s' J U' hU' hinf' hcov') hsq).2 hb

end GlobalTheory.Div.HypFlatBaseChange
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperCohomologyFlatBaseChangeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hyper_cohomology_flat_base_change : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), IsSeparated s → QuasiCompact s → Function.Bijective (liftSemi (pullHH1 h.w)) := by
  first | exact @GlobalTheory.Div.HypFlatBaseChange.main | exact GlobalTheory.Div.HypFlatBaseChange.main | (intros; apply GlobalTheory.Div.HypFlatBaseChange.main <;> assumption)
end
end
