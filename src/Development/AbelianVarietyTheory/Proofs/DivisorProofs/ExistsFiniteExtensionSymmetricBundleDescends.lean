module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPullbackSectionNonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectClassPrimAndIsoClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionRigidTranslateSameMumfordBundleStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAbelianSchemeThick
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangePolarisationTranslateTwoTorsion

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BaseTransl

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
  {g : G'.left ⟶ G.left}

theorem toBase_injective (hg : IsPullback g G'.hom G.hom f) {T : Over S'} {x x' : T ⟶ G'}
    (h : toBase hg.w x = toBase hg.w x') : x = x' := by
  have e : x.left ≫ g = x'.left ≫ g := congrArg (fun z => z.left) h
  ext
  exact hg.hom_ext e (by rw [Over.w x, Over.w x'])

theorem toBase_one (hg : IsPullback g G'.hom G.hom f)
    (hm : ∀ (T : Over S') (x y : T ⟶ G'), toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y) (T : Over S') :
    toBase hg.w (1 : T ⟶ G') = 1 := by
  have := hm T 1 1
  rw [_root_.mul_one] at this
  exact mul_eq_left.1 this.symm

theorem isGrpPullback_of_toBase (hg : IsPullback g G'.hom G.hom f)
    (hm : ∀ (T : Over S') (x y : T ⟶ G'), toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y) :
    IsGrpPullback G' G f g := by
  refine ⟨hg, fun T x y x₀ y₀ hx hy => ?_⟩
  have ex : x₀ = toBase hg.w x := by ext; exact hx
  have ey : y₀ = toBase hg.w y := by ext; exact hy
  rw [ex, ey, ← hm]
  rfl


open GlobalTheory.RigidTranslate in
theorem exists_baseChange_translate : ∀ (K K' : Type) [Field K] [Field K'] (io : K →+* K') (A : PolAV (Sp K)) (y : Over.mk (spMap io) ⟶ A.A), y * y = 1 → ∃ (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left) (t : 𝟙_ (Over (Sp K')) ⟶ A₁.A), IsGrpPullback A₁.A A.A (spMap io) α₁ ∧ IsSquare α₁ α₁₂ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) ∧ t.left ≫ α₁ = y.left ∧ LBIso A₁.L (GlobalTheory.RigidTranslate.rigTransl (A.L.pull α₁) t) := by
  intro K K' _ _ io A y hy
  obtain ⟨P, g, hg, -, hm, w, hw⟩ := GlobalTheory.polBaseChange_holds (Sp K) (Sp K') (spMap io) A
  have hpb : IsGrpPullback P.A A.A (spMap io) g := isGrpPullback_of_toBase hg hm
  have := P.isAb.comm
  have := P.isAb.proper
  have := A.isAb.comm
  let t₀ : 𝟙_ (Over (Sp K')) ⟶ P.A := Over.homMk (hg.lift y.left (𝟙 _) (by rw [Over.w y, Category.id_comp]; rfl))
    (hg.lift_snd _ _ _)
  have ht₀ : t₀.left ≫ g = y.left := hg.lift_fst _ _ _
  let e : Over.mk ((𝟙_ (Over (Sp K'))).hom ≫ spMap io) ⟶ Over.mk (spMap io) := Over.homMk (𝟙 _) (Category.id_comp _)
  have hte : toBase hg.w t₀ = e ≫ y := by
    ext
    exact ht₀.trans (Category.id_comp _).symm
  have htt : t₀ * t₀ = 1 := by
    refine toBase_injective hg ?_
    rw [hm, hte, toBase_one hg hm, ← MonObj.comp_mul, hy, MonObj.comp_one]
  have hwL : LBIso (A.L.pull g) P.L := ⟨w, hw⟩
  obtain ⟨c, hc⟩ := GlobalTheory.Moduli.cube_of_isLB _ P P.L P.isLB
  let A₁ : PolAV (Sp K') :=
    { A := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, L := rigTransl P.L t₀
      isLB := DVR.linComb_isLB _ P.isLB _ _
      rigid := rigidified_rigTransl P.isLB
      sym := sym_rigTransl htt P.isLB P.sym
      ample := relAmple_rigTransl htt P.isLB P.ample
      ktriv := kTriv_rigTransl htt P.isLB P.ktriv }
  obtain ⟨β₂, hsq, hlam⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ A.A P.A g hpb
  have hLamA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hLamP : (abelian₂ P.A P.L).IsLB := DVR.linComb_isLB _ P.isLB _ _
  have h3 := hlam A.L P.L _ (abelian₂ A.A A.L) (𝟙 _) A.isLB P.isLB hLamA hwL.symm (GlobalTheory.DescendedPrincipal.lbIso_pull_id hLamA).symm
  rw [Category.comp_id] at h3
  have h1 : LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ P.A P.L).pull (𝟙 _)) := lam_rigTransl P.isLB c hc
  refine ⟨A₁, g, β₂, t₀, hpb, hsq, ?_, ht₀, GlobalTheory.PelPrim.lbIso_linComb hwL.symm _ _⟩
  exact LBIso.trans (DVR.linComb_isLB _ A₁.isLB _ _) (pull_isLB hLamP _) (pull_isLB hLamA _) h1
    (LBIso.trans (pull_isLB hLamP _) hLamP (pull_isLB hLamA _) (GlobalTheory.DescendedPrincipal.lbIso_pull_id hLamP) h3)

end GlobalTheory.BaseTransl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangePolarisationTranslateTwoTorsionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_baseChange_polarisation_translate_two_torsion : ∀ (K K' : Type) [Field K] [Field K'] (io : K →+* K') (A : PolAV (Sp K)) (y : Over.mk (spMap io) ⟶ A.A), y * y = 1 → ∃ (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left) (t : 𝟙_ (Over (Sp K')) ⟶ A₁.A), IsGrpPullback A₁.A A.A (spMap io) α₁ ∧ IsSquare α₁ α₁₂ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) ∧ t.left ≫ α₁ = y.left ∧ LBIso A₁.L (GlobalTheory.RigidTranslate.rigTransl (A.L.pull α₁) t) := by
  first | exact @GlobalTheory.BaseTransl.exists_baseChange_translate | exact GlobalTheory.BaseTransl.exists_baseChange_translate | (intros; apply GlobalTheory.BaseTransl.exists_baseChange_translate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionPointAbelianVariety

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TwoTorsionDescent

theorem exists_finite_ext_of_sq_eq_one : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A : PolAV (Sp K)) (G : Over (Sp Ω)) [GrpObj G] (α : G.left ⟶ A.A.left), IsGrpPullback G A.A (spMap ga) α → ∀ x : 𝟙_ (Over (Sp Ω)) ⟶ G, x * x = 1 → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (l : K' →+* Ω) (y : Over.mk (spMap io) ⟶ A.A), io.Finite ∧ l.comp io = ga ∧ y * y = 1 ∧ spMap l ≫ y.left = x.left ≫ α := by
  intro K Ω _ _ _ ga A G _ α h x hx

  set T : Over (Sp K) := Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ spMap ga) with hT
  let zo : T ⟶ A.A := pushHom h (𝟙_ (Over (Sp Ω))) x
  have hzo : zo * zo = 1 := by
    show pushHom h _ x * pushHom h _ x = 1
    rw [← map_mul, hx, map_one]
  have hzl : zo.left = x.left ≫ α := rfl
  have hmul : zo ≫ mulN A.A 2 = toUnit T ≫ η[A.A] := by
    rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, sq, hzo]
    rfl
  let t : T ⟶ torsion A.A 2 := pullback.lift zo (toUnit T) hmul
  have ht : t ≫ torsion.ι A.A 2 = zo := pullback.lift_fst _ _ _

  have h2 : IsUnit ((2 : ℕ) : Γ(Sp K, ⊤)) := by
    have e : ((2 : ℕ) : Γ(Sp K, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (2 : K) := by
      rw [map_ofNat]; rfl
    rw [e]
    exact (IsUnit.mk0 (2 : K) two_ne_zero).map _
  haveI := A.isAb
  have hfin : IsFinite (torsion A.A 2).hom := (GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A.A h2).2.1
  set X := (torsion A.A 2).left
  set p := (torsion A.A 2).hom
  let tl : Sp Ω ⟶ X := t.left
  let w : X := tl (IsLocalRing.closedPoint Ω)
  let φ : X.residueField w ⟶ CommRingCat.of Ω := X.descResidueField (Scheme.stalkClosedPointTo tl)
  have htl : Spec.map φ ≫ X.fromSpecResidueField w = tl :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X tl

  let s : Sp K := p w
  haveI : s.asIdeal.IsPrime := s.isPrime
  haveI : s.asIdeal.IsMaximal := by rw [Ideal.eq_bot_of_prime s.asIdeal]; exact Ideal.bot_isMaximal
  let c : K →+* (Sp K).residueField s :=
    (Scheme.Spec.residueFieldIso (CommRingCat.of K) s).inv.hom.comp (algebraMap K s.asIdeal.ResidueField)
  have hc : spMap c = (Sp K).fromSpecResidueField s := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp]
    rfl
  have hcfin : c.Finite := by
    refine RingHom.Finite.of_surjective _ ?_
    refine (Scheme.Spec.residueFieldIso (CommRingCat.of K) s).commRingCatIsoToRingEquiv.symm.surjective.comp ?_
    have hq : Function.Surjective (Ideal.Quotient.mk s.asIdeal) := Ideal.Quotient.mk_surjective
    have hb := Ideal.bijective_algebraMap_quotient_residueField s.asIdeal
    have e : (algebraMap K s.asIdeal.ResidueField) = (algebraMap (K ⧸ s.asIdeal) s.asIdeal.ResidueField).comp (Ideal.Quotient.mk s.asIdeal) := by
      ext a; rfl
    rw [e]
    exact hb.2.comp hq
  let io : K →+* X.residueField w := (p.residueFieldMap w).hom.comp c
  have hio : io.Finite := (GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite p w).comp hcfin
  have hsio : spMap io = X.fromSpecResidueField w ≫ p := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← hc, ← Spec.map_comp]
    rfl

  have hu : X.fromSpecResidueField w ≫ p = spMap io := hsio.symm
  let u : Over.mk (spMap io) ⟶ torsion A.A 2 := Over.homMk (X.fromSpecResidueField w) hu
  let y : Over.mk (spMap io) ⟶ A.A := u ≫ torsion.ι A.A 2
  have hy : y * y = 1 := by
    have e1 : y * y = y ≫ mulN A.A 2 := by
      rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, sq]
    have e2 : torsion.ι A.A 2 ≫ mulN A.A 2 = pullback.snd (mulN A.A 2) η[A.A] ≫ η[A.A] :=
      pullback.condition
    rw [e1, Category.assoc, e2]
    show (u ≫ pullback.snd (mulN A.A 2) η[A.A]) ≫ η[A.A] = toUnit _ ≫ η[A.A]
    rw [toUnit_unique (u ≫ pullback.snd (mulN A.A 2) η[A.A]) (toUnit _)]
  have hlo : Spec.map φ ≫ X.fromSpecResidueField w ≫ p = spMap ga := by
    rw [← Category.assoc, htl]
    exact Over.w t
  refine ⟨X.residueField w, inferInstance, io, φ.hom, y, hio, ?_, hy, ?_⟩
  · have e : spMap (φ.hom.comp io) = spMap ga := by
      rw [← hlo, ← hsio]
      show _ = Spec.map φ ≫ Spec.map (CommRingCat.ofHom io)
      erw [← Spec.map_comp]
      rfl
    have e' := Spec.map_inj.mp e
    exact congrArg CommRingCat.Hom.hom e'
  · show Spec.map (CommRingCat.ofHom φ.hom) ≫ (X.fromSpecResidueField w ≫ (torsion.ι A.A 2).left) = x.left ≫ α
    rw [CommRingCat.ofHom_hom, ← Category.assoc, htl, ← hzl, ← ht]
    rfl

end GlobalTheory.TwoTorsionDescent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionPointAbelianVarietyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finite_ext_twoTorsion_point_abelianVariety : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A : PolAV (Sp K)) (G : Over (Sp Ω)) [GrpObj G] (α : G.left ⟶ A.A.left), IsGrpPullback G A.A (spMap ga) α → ∀ x : 𝟙_ (Over (Sp Ω)) ⟶ G, x * x = 1 → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (l : K' →+* Ω) (y : Over.mk (spMap io) ⟶ A.A), io.Finite ∧ l.comp io = ga ∧ y * y = 1 ∧ spMap l ≫ y.left = x.left ≫ α := by
  first | exact @GlobalTheory.TwoTorsionDescent.exists_finite_ext_of_sq_eq_one | exact GlobalTheory.TwoTorsionDescent.exists_finite_ext_of_sq_eq_one | (intros; apply GlobalTheory.TwoTorsionDescent.exists_finite_ext_of_sq_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSymmetricBundleDescends

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SymFinExt
open GlobalTheory.RigidTranslate

theorem pull_pol : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (f : Sp R ⟶ Sp R₀) (A : PolAV (Sp R₀)) (G : Over (Sp R)) [GrpObj G] (α : G.left ⟶ A.A.left), IsGrpPullback G A.A f α → (A.L.pull α).IsLB ∧ Rigidified G (A.L.pull α) ∧ Sym G (A.L.pull α) ∧ RelAmple G (A.L.pull α) ∧ KTriv G (A.L.pull α) := by
  intro R R₀ _ _ f A G _ α hα
  have hw := (isGen_iff _).1 (GlobalTheory.UU.pullIso_isGen A.isLB α)
  exact ⟨pull_isLB A.isLB α, GlobalTheory.PolBaseChange.rigidified_pull hα A.rigid, GlobalTheory.PolBaseChange.sym_pull hα A.sym,
    relAmple_pull hα.1 A.isLB (pull_isLB A.isLB α) hw ⊤ (isAffineOpen_top _) (fun _ => trivial) A.ample,
    kTriv_pull hα A.isLB (pull_isLB A.isLB α) hw A.ktriv⟩

theorem isSquare_unique : ∀ {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} (φ : G'.left ⟶ G.left) (φ₂ φ₂' : (G' ⊗ G').left ⟶ (G ⊗ G).left), IsSquare φ φ₂ → IsSquare φ φ₂' → φ₂ = φ₂' := by
  intro S S' G' G φ φ₂ φ₂' h h'
  have e : φ₂ ≫ (G ⊗ G).hom = φ₂' ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), ← Category.assoc, ← Category.assoc, h.1, h'.1]
  let u : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂ rfl
  let v : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂' e.symm
  have : u = v := CartesianMonoidalCategory.hom_ext _ _
    (Over.OverMorphism.ext (by simpa [u, v] using h.1.trans h'.1.symm))
    (Over.OverMorphism.ext (by simpa [u, v] using h.2.trans h'.2.symm))
  exact congrArg (fun z => z.left) this
end GlobalTheory.SymFinExt

namespace GlobalTheory.SymFinExt
open GlobalTheory.RigidTranslate GlobalTheory.GtCoordCompare

theorem lbIso_diff_pull_pull : ∀ (X Y₁ Y₂ Z : Scheme.{0}) (M : LB X) (g₁ : Y₁ ⟶ X) (g₂ : Y₂ ⟶ X) (u₁ v₁ : Y₁ ⟶ Y₁) (u₂ v₂ : Y₂ ⟶ Y₂) (q₁ : Z ⟶ Y₁) (q₂ : Z ⟶ Y₂), M.IsLB → q₁ ≫ u₁ ≫ g₁ = q₂ ≫ u₂ ≫ g₂ → q₁ ≫ v₁ ≫ g₁ = q₂ ≫ v₂ ≫ g₂ → LBIso ((LB.LinComb (M.pull g₁) (K := Fin 2) ![u₁, v₁] ![1, -1]).pull q₁) ((LB.LinComb (M.pull g₂) (K := Fin 2) ![u₂, v₂] ![1, -1]).pull q₂) := by
  intro X Y₁ Y₂ Z M g₁ g₂ u₁ v₁ u₂ v₂ q₁ q₂ hM hu hv
  refine lbIso_of_refines hM
    ((((refines_self (L := M) (fun _ : PUnit => g₁) (fun _ => 1)).linComb _ _)).linComb _ _)
    ((((refines_self (L := M) (fun _ : PUnit => g₂) (fun _ => 1)).linComb _ _)).linComb _ _) _ isGen_one
    fun U _ f => ?_
  simp [Fintype.prod_prod_type, Fin.prod_univ_two, hu, hv]
end GlobalTheory.SymFinExt

namespace GlobalTheory.SymFinExt
open GlobalTheory.RigidTranslate

theorem transl_comp_eq : ∀ {S S₁ S₀ : Scheme.{0}} (G : Over S) (G₁ : Over S₁) (A : Over S₀) [GrpObj G] [GrpObj G₁] [GrpObj A] (f : S ⟶ S₀) (f₁ : S₁ ⟶ S₀) (φ : G.left ⟶ A.left) (φ₁ : G₁.left ⟶ A.left), IsGrpPullback G A f φ → IsGrpPullback G₁ A f₁ φ₁ → ∀ (x : 𝟙_ (Over S) ⟶ G) (t : 𝟙_ (Over S₁) ⟶ G₁) (Z : Scheme.{0}) (q : Z ⟶ G.left) (q₁ : Z ⟶ G₁.left), q ≫ φ = q₁ ≫ φ₁ → q ≫ (toUnit G ≫ x).left ≫ φ = q₁ ≫ (toUnit G₁ ≫ t).left ≫ φ₁ → q ≫ (GlobalTheory.PolTranslate.transl x).left ≫ φ = q₁ ≫ (GlobalTheory.PolTranslate.transl t).left ≫ φ₁ := by
  intro S S₁ S₀ G G₁ A _ _ _ f f₁ φ φ₁ h h₁ x t Z q q₁ e ec
  let T : Over S := Over.mk (q ≫ G.hom)
  let T₁ : Over S₁ := Over.mk (q₁ ≫ G₁.hom)
  let a : T ⟶ G := Over.homMk q rfl
  let a₁ : T₁ ⟶ G₁ := Over.homMk q₁ rfl
  have k : q ≫ (GlobalTheory.PolTranslate.transl x).left = (a * (toUnit T ≫ x)).left := comp_transl_left a x
  have k₁ : q₁ ≫ (GlobalTheory.PolTranslate.transl t).left = (a₁ * (toUnit T₁ ≫ t)).left := comp_transl_left a₁ t
  have hw : (q ≫ G.hom) ≫ f = (q₁ ≫ G₁.hom) ≫ f₁ := by
    rw [Category.assoc, Category.assoc, ← h.1.w, ← h₁.1.w, ← Category.assoc, ← Category.assoc, e]
  let x₀ : Over.mk (T.hom ≫ f) ⟶ A := Over.homMk (a.left ≫ φ) (by
    show (q ≫ φ) ≫ A.hom = (q ≫ G.hom) ≫ f
    rw [Category.assoc, h.1.w, Category.assoc])
  let y₀ : Over.mk (T.hom ≫ f) ⟶ A := Over.homMk ((toUnit T ≫ x).left ≫ φ) (by
    show ((toUnit T ≫ x).left ≫ φ) ≫ A.hom = (q ≫ G.hom) ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w (toUnit T ≫ x)]
    rfl)
  let x₁ : Over.mk (T₁.hom ≫ f₁) ⟶ A := Over.homMk (a₁.left ≫ φ₁) (by
    show (q₁ ≫ φ₁) ≫ A.hom = (q₁ ≫ G₁.hom) ≫ f₁
    rw [Category.assoc, h₁.1.w, Category.assoc])
  let y₁ : Over.mk (T₁.hom ≫ f₁) ⟶ A := Over.homMk ((toUnit T₁ ≫ t).left ≫ φ₁) (by
    show ((toUnit T₁ ≫ t).left ≫ φ₁) ≫ A.hom = (q₁ ≫ G₁.hom) ≫ f₁
    rw [Category.assoc, h₁.1.w, ← Category.assoc, Over.w (toUnit T₁ ≫ t)]
    rfl)
  have E := h.2 T a (toUnit T ≫ x) x₀ y₀ rfl rfl
  have E₁ := h₁.2 T₁ a₁ (toUnit T₁ ≫ t) x₁ y₁ rfl rfl
  let j : Over.mk (T.hom ≫ f) ⟶ Over.mk (T₁.hom ≫ f₁) := Over.homMk (𝟙 Z) (by
    show 𝟙 Z ≫ (q₁ ≫ G₁.hom) ≫ f₁ = (q ≫ G.hom) ≫ f
    rw [Category.id_comp, hw])
  have hx : j ≫ x₁ = x₀ := Over.OverMorphism.ext (by
    show 𝟙 Z ≫ q₁ ≫ φ₁ = q ≫ φ
    rw [Category.id_comp, e])
  have hy : j ≫ y₁ = y₀ := Over.OverMorphism.ext (by
    show 𝟙 Z ≫ (toUnit T₁ ≫ t).left ≫ φ₁ = (toUnit T ≫ x).left ≫ φ
    have k2 : (toUnit T ≫ x).left = q ≫ (toUnit G ≫ x).left := by
      simp only [Over.comp_left]
      show (q ≫ G.hom) ≫ x.left = q ≫ (G.hom ≫ x.left)
      rw [Category.assoc]
    have k3 : (toUnit T₁ ≫ t).left = q₁ ≫ (toUnit G₁ ≫ t).left := by
      simp only [Over.comp_left]
      show (q₁ ≫ G₁.hom) ≫ t.left = q₁ ≫ (G₁.hom ≫ t.left)
      rw [Category.assoc]
    rw [Category.id_comp, k2, k3, Category.assoc, Category.assoc]
    exact ec.symm)
  have H := congrArg (fun z => z.left) (MonObj.comp_mul j x₁ y₁)
  rw [hx, hy] at H
  rw [← Category.assoc, ← Category.assoc, k, k₁, ← E, ← E₁, ← H]
  exact Category.id_comp _
end GlobalTheory.SymFinExt

namespace GlobalTheory.SymFinExt
open GlobalTheory.RigidTranslate

theorem lam_pull_id {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L (L.pull (𝟙 X)) :=
  LBIso.chartPull (chartPullId L) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L (𝟙 X) (𝟙 X) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hL)

theorem exists_finite_ext : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A : PolAV (Sp K)) (A' : PolAV (Sp Ω)) (α : A'.A.left ⟶ A.A.left) (α₂ : (G2 A'.A).left ⟶ (G2 A.A).left), IsGrpPullback A'.A A.A (spMap ga) α → Geo.Tor.IsSquare α α₂ → LBIso (abelian₂ A'.A A'.L) ((abelian₂ A.A A.L).pull α₂) → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω' : Type) (_ : Field Ω') (j : Ω →+* Ω') (l : K' →+* Ω') (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left) (p : pullback A'.A.hom (spMap j) ⟶ A₁.A.left), io.Finite ∧ l.comp io = j.comp ga ∧ IsGrpPullback A₁.A A.A (spMap io) α₁ ∧ Geo.Tor.IsSquare α₁ α₁₂ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) ∧ p ≫ α₁ = pullback.fst _ _ ≫ α ∧ p ≫ A₁.A.hom = pullback.snd _ _ ≫ spMap l ∧ LBIso (A'.L.pull (pullback.fst A'.A.hom (spMap j))) (A₁.L.pull p) := by
  intro K Ω _ _ _ ga A A' α α₂ hα hsq hΛ
  have := A.isAb.comm
  have := A'.isAb.comm
  obtain ⟨hLB, hrig, hsym, hamp, hK⟩ := pull_pol Ω K (spMap ga) A A'.A α hα
  let P : PolAV (Sp Ω) := ⟨A'.A, A'.isAb, A'.g, A'.smoothDim, A.L.pull α, hLB, hrig, hsym, hamp, hK⟩
  have hΛA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  obtain ⟨β₂, hβ, hT⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (spMap ga) A.A A'.A α hα
  have e₁ := hT A.L (A.L.pull α) _ (abelian₂ A.A A.L) (𝟙 _) A.isLB hLB hΛA (GlobalTheory.PolBaseChange.lbIso_refl hLB)
    (lam_pull_id hΛA)
  rw [Category.comp_id, isSquare_unique α β₂ α₂ hβ hsq] at e₁
  have hΛ' : LBIso (abelian₂ P.A A'.L) (abelian₂ P.A P.L) :=
    LBIso.trans (DVR.linComb_isLB _ A'.isLB _ _) (pull_isLB hΛA _) (DVR.linComb_isLB _ hLB _ _) hΛ e₁.symm
  obtain ⟨x, hx2, hxL⟩ := GlobalTheory.T.exists_twoTorsion_rigidTranslate_same_mumfordBundle Ω P A'.L A'.isLB A'.rigid A'.sym hΛ'
  obtain ⟨K', _, io, l, y, hfin, hcomp, hy2, hy⟩ := GlobalTheory.T.exists_finite_ext_twoTorsion_point_abelianVariety K Ω ga A A'.A α hα x hx2
  obtain ⟨A₁, α₁, α₁₂, t, hα₁, hsq₁, hΛ₁, ht, hL₁⟩ := GlobalTheory.T.exists_baseChange_polarisation_translate_two_torsion K K' io A y hy2
  have hid : spMap (RingHom.id Ω) = 𝟙 _ := Spec.map_id _
  have w : (pullback.fst A'.A.hom (spMap (RingHom.id Ω)) ≫ α) ≫ A.A.hom =
      (pullback.snd A'.A.hom (spMap (RingHom.id Ω)) ≫ spMap l) ≫ spMap io := by
    rw [Category.assoc, hα.1.w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc]
    congr 1
    rw [← hcomp, hid, Category.id_comp]
    show Spec.map (CommRingCat.ofHom (l.comp io)) = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  let p := hα₁.1.lift _ _ w
  have hp1 : p ≫ α₁ = pullback.fst _ _ ≫ α := hα₁.1.lift_fst _ _ _
  have hp2 : p ≫ A₁.A.hom = pullback.snd _ _ ≫ spMap l := hα₁.1.lift_snd _ _ _
  refine ⟨K', inferInstance, io, Ω, inferInstance, RingHom.id Ω, l, A₁, α₁, α₁₂, p, hfin, by rw [hcomp]; rfl,
    hα₁, hsq₁, hΛ₁, hp1, hp2, ?_⟩
  have hc : pullback.fst A'.A.hom (spMap (RingHom.id Ω)) ≫ (toUnit A'.A ≫ x).left ≫ α =
      p ≫ (toUnit A₁.A ≫ t).left ≫ α₁ := by
    have hsnd : pullback.snd A'.A.hom (spMap (RingHom.id Ω)) ≫ spMap (RingHom.id Ω) = pullback.snd _ _ := by
      rw [hid, Category.comp_id]
    show pullback.fst _ _ ≫ (A'.A.hom ≫ x.left) ≫ α = p ≫ (A₁.A.hom ≫ t.left) ≫ α₁
    rw [Category.assoc, ← Category.assoc (pullback.fst _ _), pullback.condition, hsnd, Category.assoc,
      ← Category.assoc p, hp2, Category.assoc, ht, hy]
  have htr := transl_comp_eq A'.A A₁.A A.A (spMap ga) (spMap io) α α₁ hα hα₁ x t _ _ p hp1.symm hc
  have hE := lbIso_diff_pull_pull _ _ _ _ A.L α α₁ _ _ _ _ (pullback.fst A'.A.hom (spMap (RingHom.id Ω))) p A.isLB
    htr hc
  have hR₁ : (rigTransl (A.L.pull α₁) t).IsLB := DVR.linComb_isLB _ (pull_isLB A.isLB _) _ _
  have hR : (rigTransl (A.L.pull α) x).IsLB := DVR.linComb_isLB _ (pull_isLB A.isLB _) _ _
  exact LBIso.trans (pull_isLB A'.isLB _) (pull_isLB hR _) (pull_isLB A₁.isLB _) (GlobalTheory.RigidBundleGlue.LBIso.pull hxL _)
    (LBIso.trans (pull_isLB hR _) (pull_isLB hR₁ _) (pull_isLB A₁.isLB _) hE (GlobalTheory.RigidBundleGlue.LBIso.pull hL₁.symm _))

end GlobalTheory.SymFinExt

end
end
end
