module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StdSmoothMvPolynomial
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointEqOfReductionCoords
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
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoordReducedFibreClosedPointStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOpensEtaleOfUniqueClassicalPoints
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Linter.HaveILetI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QuasiFiniteAtAffineSpaceHomOfVectorOfCoordStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointEqOfReductionCoordsStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.classical_point_eq_of_reduction_coords : ∀ C : Core, C.HasTests → C.Fib → ∀ (w : C.G.toScheme) (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), C.Coord w W hw u → ∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W.toScheme), C.Cl (a ≫ W.ι ≫ C.GG.hom) → a ≫ W.ι ≫ C.GG.hom = a' ≫ W.ι ≫ C.GG.hom → a (cPt p) = ⟨w, hw⟩ → rPt p ≫ a = rPt p ≫ a' → (∀ i, a.appTop.hom (W.topIso.inv.hom (u i)) = a'.appTop.hom (W.topIso.inv.hom (u i))) → a = a' := by
  first | exact @GlobalTheory.ZJ.classical_eq_of_coord | exact GlobalTheory.ZJ.classical_eq_of_coord | (intros; apply GlobalTheory.ZJ.classical_eq_of_coord <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsDominantHomOfVectorOfQuasiFiniteAt

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem injective_of_quasiFinite_of_isStandardSmoothOfRelativeDimension {R B : Type} [CommRing R]
    [IsDomain R] [CommRing B] [IsDomain B] [Algebra R B] {g : ℕ}
    [Algebra.IsStandardSmoothOfRelativeDimension g R B] (ψ : MvPolynomial (Fin g) R →ₐ[R] B)
    (hψ : ψ.toRingHom.QuasiFinite) : Function.Injective ψ := by
  have key : FaithfulSMul R B ∧ Algebra.trdeg R B = g := by
    obtain ⟨e, he⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial g R B
    letI : Algebra (MvPolynomial (Fin g) R) B := e.toRingHom.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin g) R) B := he
    haveI : IsScalarTower R (MvPolynomial (Fin g) R) B :=
      IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
    obtain ⟨_, _⟩ :=
      AffinePoints.faithfulSMul_and_isAlgebraic_of_etale (MvPolynomial (Fin g) R) B
    refine ⟨FaithfulSMul.trans R (MvPolynomial (Fin g) R) B, ?_⟩
    rw [trdeg_eq_of_isAlgebraic_top R (MvPolynomial (Fin g) R) B, MvPolynomial.trdeg_of_isDomain]
    simp
  obtain ⟨_, htr⟩ := key
  let x : Fin g → B := fun i => ψ (MvPolynomial.X i)
  have hx : ψ = MvPolynomial.aeval x := MvPolynomial.aeval_unique ψ
  have hr : ψ.range = Algebra.adjoin R (Set.range x) := by
    rw [Algebra.adjoin_range_eq_range_aeval, ← hx]
  have h1 : (algebraMap ψ.range B).QuasiFinite :=
    RingHom.QuasiFinite.of_comp (f := algebraMap ψ.range B) (g := ψ.rangeRestrict.toRingHom) hψ
  rw [RingHom.quasiFinite_algebraMap] at h1
  have h2 : Algebra.IsAlgebraic ψ.range B := isAlgebraic_of_quasiFiniteAt ψ.range B ⊥
  rw [hr] at h2
  have h3 := Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite R x (by simp [htr])
  rw [hx]
  exact h3.1

theorem isDominant_of_locallyQuasiFinite_affineSpace {Z : Scheme.{0}} [IsIntegral Z]
    {R B : CommRingCat.{0}} [IsDomain R] [IsDomain B] {g : ℕ} (φ : R ⟶ B)
    (hφ : φ.hom.IsStandardSmoothOfRelativeDimension g) (i : Spec R ⟶ Z) [IsOpenImmersion i]
    (f : Spec B ⟶ 𝔸(Fin g; Z)) [LocallyQuasiFinite f]
    (hf : f ≫ 𝔸(Fin g; Z) ↘ Z = Spec.map φ ≫ i) : IsDominant f := by
  have hp := AffineSpace.isPullback_map (n := Fin g) i
  have : IsOpenImmersion (AffineSpace.map (Fin g) i) :=
    MorphismProperty.of_isPullback hp.flip ‹_›
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective
    (hp.lift f (Spec.map φ) hf ≫ (AffineSpace.SpecIso (Fin g) R).hom)
  have e : f = Spec.map ψ ≫ (AffineSpace.SpecIso (Fin g) R).inv ≫ AffineSpace.map (Fin g) i := by
    rw [hψ]; simp
  have e2 : CommRingCat.ofHom MvPolynomial.C ≫ ψ = φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, ← AffineSpace.SpecIso_inv_over, Category.assoc, Iso.hom_inv_id_assoc,
      IsPullback.lift_snd]
  have hq : LocallyQuasiFinite (Spec.map ψ) := by
    rw [e] at ‹LocallyQuasiFinite f›
    exact .of_comp _ ((AffineSpace.SpecIso (Fin g) R).inv ≫ AffineSpace.map (Fin g) i)
  rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)] at hq
  letI : Algebra R B := φ.hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension g R B := hφ
  have hinj := injective_of_quasiFinite_of_isStandardSmoothOfRelativeDimension
    (R := R) (B := B) (g := g) { ψ.hom with commutes' := fun r => congr($e2 r) } hq
  have : IsDominant (Spec.map ψ) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (by rw [(RingHom.injective_iff_ker_eq_bot ψ.hom).1 hinj]; exact bot_le)⟩
  have : IsDominant (AffineSpace.map (Fin g) i) :=
    ⟨(AffineSpace.map (Fin g) i).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  rw [e]
  infer_instance

theorem isDominant_homOfVector_of_quasiFiniteAt :
    ∀ (X Z : Scheme.{0}) [IsIntegral X] [IsIntegral Z] (t : X ⟶ Z) [LocallyOfFiniteType t] (g : ℕ) (U : X.Opens), (U : Set X).Nonempty → SmoothOfRelativeDimension g (U.ι ≫ t) → ∀ (u : Fin g → Γ(X, ⊤)) (w : X), (AffineSpace.homOfVector t u).QuasiFiniteAt w → IsDominant (AffineSpace.homOfVector t u) := by
  intro X Z _ _ t _ g U hU hs u w hw
  have hf := AffineSpace.homOfVector_over t u
  generalize AffineSpace.homOfVector t u = f at hf hw
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ 𝔸(Fin g; Z) ↘ Z) := by rw [hf]; infer_instance
    exact locallyOfFiniteType_of_comp f (𝔸(Fin g; Z) ↘ Z)
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.isOpen f.quasiFiniteLocus.isOpen hU
    ⟨w, hw⟩
  let W : X.Opens := U ⊓ f.quasiFiniteLocus
  have h1 : SmoothOfRelativeDimension (0 + g) (X.homOfLE (inf_le_left : W ≤ U) ≫ U.ι ≫ t) :=
    inferInstance
  have h2 : LocallyQuasiFinite (X.homOfLE (inf_le_right : W ≤ f.quasiFiniteLocus) ≫
    f.quasiFiniteLocus.ι ≫ f) := inferInstance
  rw [Scheme.homOfLE_ι_assoc] at h1 h2
  rw [zero_add] at h1
  obtain ⟨Z', hZ', V, hV, hx, e, hsm⟩ := h1.exists_isStandardSmoothOfRelativeDimension ⟨x, hxU, hxV⟩
  have : Nonempty W := ⟨⟨x, hxU, hxV⟩⟩
  have : Nonempty V := ⟨⟨_, hx⟩⟩
  have : Nonempty Z' := ⟨⟨_, e hx⟩⟩
  have : IsDominant (hV.fromSpec ≫ W.ι ≫ f) :=
    isDominant_of_locallyQuasiFinite_affineSpace _ hsm hZ'.fromSpec _ (by
      rw [IsAffineOpen.SpecMap_appLE_fromSpec _ hZ' hV e]; simp [hf, W])
  have : IsDominant (W.ι ≫ f) := .of_comp hV.fromSpec _
  exact .of_comp W.ι _

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsDominantHomOfVectorOfQuasiFiniteAtStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.isDominant_homOfVector_of_quasiFiniteAt' : ∀ (X Z : Scheme.{0}) [IsIntegral X] [IsIntegral Z] (t : X ⟶ Z) [LocallyOfFiniteType t] (g : ℕ) (U : X.Opens), (U : Set X).Nonempty → SmoothOfRelativeDimension g (U.ι ≫ t) → ∀ (u : Fin g → Γ(X, ⊤)) (w : X), (AffineSpace.homOfVector t u).QuasiFiniteAt w → IsDominant (AffineSpace.homOfVector t u) := by
  first | exact @GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt | exact GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt | (intros; apply GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothOfRelativeDimensionGroupSchemeOfTests

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory

theorem isStandardSmoothOfRelativeDimension_mvPolynomial_fin (R : Type) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  apply GlobalTheory.CompanionTheory.Ar.LieInh.stdSmooth_mvPolynomial <;> assumption

theorem smoothOfRelativeDimension_affineSpace_fin (S : Scheme.{0}) (n : ℕ) :
    SmoothOfRelativeDimension n (𝔸(Fin n; S) ↘ S) := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} n
  refine MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension n) _ _ ?_
  have := isIso_of_isTerminal specULiftZIsTerminal.{0} terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C)),
    MorphismProperty.cancel_right_of_respectsIso (P := @SmoothOfRelativeDimension n),
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2
    (isStandardSmoothOfRelativeDimension_mvPolynomial_fin (ULift ℤ) n)

namespace ZJ

theorem Core.exists_opens_smoothOfRelativeDimension (C : Core) (hT : C.HasTests) (hF : C.Fib)
    (w : C.G.toScheme) (hc : IsClosed ({w} : Set C.G.toScheme)) :
    ∃ V : C.G.toScheme.Opens, w ∈ V ∧ SmoothOfRelativeDimension C.g (V.ι ≫ C.GG.hom) := by
  obtain ⟨hsep, hlft, -, hint, -, -, ha, hcart, -, -, -, hdom, -⟩ := GlobalTheory.T.abelianSchemeProperClosureData_basic_properties C
  obtain ⟨W, hw, u, -, hu⟩ := GlobalTheory.T.exists_coord_reducedFibre_closedPoint C hT hF w hc
  have hqf := GlobalTheory.T.quasiFiniteAt_affineSpace_homOfVector_of_coord C w W hw u hc hu
  have huniq := GlobalTheory.T.classical_point_eq_of_reduction_coords C hT hF w W hw u hu
  have hint' : IsIntegral C.G.toScheme := hint
  have : Nonempty W.toScheme := ⟨⟨w, hw⟩⟩
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  let t : W.toScheme ⟶ C.Z := W.ι ≫ C.GG.hom
  let u' : Fin C.g → Γ(W.toScheme, ⊤) := fun i => W.topIso.inv.hom (u i)
  let v : W.toScheme ⟶ 𝔸(Fin C.g; C.Z) := AffineSpace.homOfVector t u'
  have hv : v ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z = t := AffineSpace.homOfVector_over _ _
  have : LocallyOfFiniteType t := inferInstanceAs (LocallyOfFiniteType (W.ι ≫ C.GG.hom))
  have : IsSeparated t := inferInstanceAs (IsSeparated (W.ι ≫ C.GG.hom))
  have : IsDominant W.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact W.isOpen.dense ⟨w, hw⟩⟩
  have : IsDominant t := inferInstanceAs (IsDominant (W.ι ≫ C.GG.hom))
  have hA := smoothOfRelativeDimension_affineSpace_fin C.Z C.g
  have : Smooth (𝔸(Fin C.g; C.Z) ↘ C.Z) := SmoothOfRelativeDimension.smooth C.g _
  have : LocallyOfFiniteType v := by
    have : LocallyOfFiniteType (v ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z) := by rw [hv]; infer_instance
    exact locallyOfFiniteType_of_comp v (𝔸(Fin C.g; C.Z) ↘ C.Z)
  have : IsSeparated v := by
    have : IsSeparated (v ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z) := by rw [hv]; infer_instance
    exact IsSeparated.of_comp v (𝔸(Fin C.g; C.Z) ↘ C.Z)
  let U' : W.toScheme.Opens := t ⁻¹ᵁ C.U
  have hU' : (U' : Set W.toScheme).Nonempty := by
    obtain ⟨x, hx⟩ := t.denseRange.exists_mem_open C.U.isOpen C.ne
    exact ⟨x, hx⟩
  have hsm : SmoothOfRelativeDimension C.g (U'.ι ≫ t) := by
    let l : U'.toScheme ⟶ C.A.left := hcart.lift (U'.ι ≫ W.ι) (t ∣_ C.U)
      (by rw [morphismRestrict_ι, Category.assoc])
    have h1 : l ≫ C.a = U'.ι ≫ W.ι := hcart.lift_fst _ _ _
    have h2 : l ≫ C.A.hom = t ∣_ C.U := hcart.lift_snd _ _ _
    have : IsOpenImmersion (l ≫ C.a) := by rw [h1]; infer_instance
    have : IsOpenImmersion l := IsOpenImmersion.of_comp l C.a
    have h3 : U'.ι ≫ t = l ≫ C.A.hom ≫ C.U.ι := by
      rw [reassoc_of% h2, morphismRestrict_ι]
    have := C.dim
    have h4 : SmoothOfRelativeDimension (0 + (C.g + 0)) (l ≫ C.A.hom ≫ C.U.ι) := inferInstance
    rw [h3]
    simpa using h4
  have : IsDominant v := GlobalTheory.T.isDominant_homOfVector_of_quasiFiniteAt' W.toScheme C.Z t C.g U' hU' hsm u' ⟨w, hw⟩ hqf
  have := C.flat
  have := C.lft
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme 𝔸(Fin C.g; C.Z) :=
    forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (𝔸(Fin C.g; C.Z) ↘ C.Z) C.normal
  have hc' : IsClosed ({⟨w, hw⟩} : Set W.toScheme) := by
    have := hc.preimage W.ι.continuous
    convert this using 1
    ext z
    exact Subtype.ext_iff
  have huniq' : ∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W.toScheme),
      a ≫ v = a' ≫ v → a (cPt p) = ⟨w, hw⟩ → rPt p ≫ a = rPt p ≫ a' →
      Set.range (gPt p ≫ a) ⊆ U' → Set.range (gPt p ≫ a') ⊆ U' → a = a' := by
    intro p _ a a' h hp hr hg _
    refine huniq p a a' ?_ ?_ hp hr fun i => ?_
    · change Set.range (gPt p ≫ a ≫ t) ⊆ C.U
      rintro _ ⟨z, rfl⟩
      rw [← Category.assoc, Scheme.Hom.comp_apply]
      exact hg (Set.mem_range_self z)
    · change a ≫ t = a' ≫ t
      rw [← hv, reassoc_of% h]
    · have e : ∀ b : Sp (OO p) ⟶ W.toScheme,
          b.appTop.hom (u' i) = (b ≫ v).appTop.hom (AffineSpace.coord C.Z i) := fun b => by
        rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
        exact congrArg _ (AffineSpace.homOfVector_appTop_coord t u' i).symm
      exact (e a).trans ((congrArg (fun c : Sp (OO p) ⟶ 𝔸(Fin C.g; C.Z) =>
        c.appTop.hom (AffineSpace.coord C.Z i)) h).trans (e a').symm)
  obtain ⟨V, hV, hE⟩ : ∃ V : W.toScheme.Opens, ⟨w, hw⟩ ∈ V ∧ Etale (V.ι ≫ v) :=
    exists_opens_etale_of_unique_classical_points 𝔸(Fin C.g; C.Z)
      (𝔸(Fin C.g; C.Z) ↘ C.Z ≫ C.π) hN W.toScheme v ⟨w, hw⟩ U' hc' hqf hU' huniq'
  have h5 : SmoothOfRelativeDimension (0 + C.g) ((V.ι ≫ v) ≫ 𝔸(Fin C.g; C.Z) ↘ C.Z) :=
    inferInstance
  rw [Category.assoc, hv, zero_add] at h5
  refine ⟨(V.ι ≫ W.ι).opensRange, ⟨⟨⟨w, hw⟩, hV⟩, rfl⟩, ?_⟩
  have h6 : SmoothOfRelativeDimension (0 + C.g)
      ((V.ι ≫ W.ι).isoOpensRange.inv ≫ V.ι ≫ t) := inferInstance
  rw [zero_add] at h6
  convert h6 using 1
  rw [← (V.ι ≫ W.ι).isoOpensRange_inv_comp]
  simp only [Category.assoc, t]

theorem Core.smoothOfRelativeDimension_of_hasTests :
    ∀ C : Core, C.HasTests → C.Fib → SmoothOfRelativeDimension C.g C.GG.hom := by
  intro C hT hF
  obtain ⟨-, hlft, -⟩ := GlobalTheory.T.abelianSchemeProperClosureData_basic_properties C
  have := C.lft
  choose V hV hs using C.exists_opens_smoothOfRelativeDimension hT hF
  let V' : {w : C.G.toScheme // IsClosed ({w} : Set C.G.toScheme)} → C.G.toScheme.Opens :=
    fun w => V w.1 w.2
  have htop : iSup V' = ⊤ :=
    (jacobson_closedPoints_tools_int C.G.toScheme (C.GG.hom ≫ C.π)).2.2.1 _ _ fun x hx =>
      ⟨fun _ => trivial, fun _ => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hV x hx⟩⟩
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} C.g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} C.g) V' htop
    fun w => hs w.1 w.2

end ZJ
end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothOfRelativeDimensionGroupSchemeOfTestsStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_groupScheme_of_tests : ∀ C : Core, C.HasTests → C.Fib → SmoothOfRelativeDimension C.g C.GG.hom := by
  first | exact @GlobalTheory.ZJ.Core.smoothOfRelativeDimension_of_hasTests | exact GlobalTheory.ZJ.Core.smoothOfRelativeDimension_of_hasTests | (intros; apply GlobalTheory.ZJ.Core.smoothOfRelativeDimension_of_hasTests <;> assumption)
end
end
