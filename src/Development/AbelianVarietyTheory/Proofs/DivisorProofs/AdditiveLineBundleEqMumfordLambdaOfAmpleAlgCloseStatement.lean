module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KernelFiniteFlatHolds
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleProductAcyclicOverAffineFiniteClosedStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleProductAcyclicOfAffineBaseAcyclicStatement
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TheoremOfCubeTwoProjectiveFactors
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Mathlib.AlgebraicGeometry.QuasiAffine

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleRationalPointsFiniteClosed

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KLFinite

theorem finite_of_isFinite {K : Type} [Field K] {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of K)) [IsFinite f] :
    Finite Z := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  letI : Algebra K Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra
  have hmod : Module.Finite K Γ(Z, ⊤) := by
    show ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.Finite
    rw [CommRingCat.hom_comp]
    exact f.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)
  have : IsArtinianRing Γ(Z, ⊤) := IsArtinianRing.of_finite K _
  have : Finite (Spec (.of Γ(Z, ⊤))) := inferInstanceAs (Finite (PrimeSpectrum _))
  exact Finite.of_injective _ Z.isoSpec.hom.isOpenEmbedding.injective

theorem memKL_of_lam_eq_zero {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))} [GrpObj A] {L : LB A.left}
    (hL : L.IsLB) (x : 𝟙_ _ ⟶ A) (h : lam (cls L hL) (toUnit A ≫ x) (𝟙 A) = 0) : MemKL A L x := by
  intro p
  refine ⟨⊤, trivial, ?_⟩
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  refine (cls_eq_zero_iff (pull_isLB hD _)).1 ?_
  rw [cls_pull hD]
  refine (congrArg _ ?_).trans (map_zero _)
  have e := congrArg (CechPic.pull (snd (𝟙_ _) A).left) h
  rw [pull_lam, map_zero, Category.comp_id, ← Category.assoc, comp_toUnit, GlobalTheory.PrimitiveOverField.lam_const,
    toUnit_unique (toUnit _) (fst (𝟙_ _) A)] at e
  refine (cls_linComb hL _ _ hD).trans (Eq.trans ?_ e)
  rw [Fin.sum_univ_two, sub_eq_add_neg]
  exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)

theorem isClosed_point {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))} [IsSeparated A.hom]
    (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A) : IsClosed ({x.left (IsLocalRing.closedPoint K)} : Set A.left) := by
  have hx : x.left ≫ A.hom = 𝟙 _ := Over.w x
  have : IsClosedImmersion (x.left ≫ A.hom) := by rw [hx]; infer_instance
  have : IsClosedImmersion x.left := IsClosedImmersion.of_comp x.left A.hom
  have h := x.left.isClosedEmbedding.isClosedMap {IsLocalRing.closedPoint K}
    (by rw [show ({IsLocalRing.closedPoint K} : Set (Spec (CommRingCat.of K))) = Set.univ from
      Set.eq_univ_of_forall fun z => Subsingleton.elim (α := PrimeSpectrum K) _ _]; exact isClosed_univ)
  exact (congrArg IsClosed Set.image_singleton).mp h

end GlobalTheory.KLFinite

theorem GlobalTheory.KLFinite.kl_finite : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∃ S : Finset A.left, (∀ s ∈ S, IsClosed ({s} : Set A.left)) ∧ ∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A, GlobalTheory.CechPic.lam (cls L hL) (toUnit A ≫ x) (𝟙 A) = 0 → x.left (IsLocalRing.closedPoint K) ∈ S := by
  intro K _ _ A _ hA L hL ha
  obtain ⟨Z, i, -, hfin, -, hZ⟩ := GlobalTheory.kernelFiniteFlat_holds K A hA L hL ha
  have : Finite Z.left := GlobalTheory.KLFinite.finite_of_isFinite Z.hom
  have : IsProper A.hom := hA.proper
  have hr : (Set.range i.left).Finite := Set.finite_range _
  classical
  refine ⟨hr.toFinset.filter (fun s => IsClosed ({s} : Set A.left)), fun s hs => (Finset.mem_filter.1 hs).2,
    fun x hx => ?_⟩
  obtain ⟨z, hz⟩ := (hZ _ x).1 (GlobalTheory.KLFinite.memKL_of_lam_eq_zero hL x hx)
  refine Finset.mem_filter.2 ⟨hr.mem_toFinset.2 ⟨z.left (IsLocalRing.closedPoint K), ?_⟩,
    GlobalTheory.KLFinite.isClosed_point x⟩
  rw [← hz, Over.comp_left]
  rfl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleRationalPointsFiniteClosedStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.kernelOfLineBundle_rationalPoints_finite_closed : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∃ S : Finset A.left, (∀ s ∈ S, IsClosed ({s} : Set A.left)) ∧ ∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A, GlobalTheory.CechPic.lam (cls L hL) (toUnit A ≫ x) (𝟙 A) = 0 → x.left (IsLocalRing.closedPoint K) ∈ S := by
  first | exact @GlobalTheory.KLFinite.kl_finite | exact GlobalTheory.KLFinite.kl_finite | (intros; apply GlobalTheory.KLFinite.kl_finite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TheoremOfCubeTwoProjectiveFactorsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.theorem_of_cube_two_projective_factors : ∀ (k : Type) [Field k] (X Y Z : Over (Sp k)) (x₀ : 𝟙_ (Over (Sp k)) ⟶ X) (y₀ : 𝟙_ (Over (Sp k)) ⟶ Y) (z₀ : 𝟙_ (Over (Sp k)) ⟶ Z), Smooth X.hom → Smooth Y.hom → IsProper X.hom → IsProper Y.hom → IsProjBy X.hom → IsProjBy Y.hom → GeometricallyIntegral X.hom → GeometricallyIntegral Y.hom → ConnectedSpace Z.left → ∀ M : LB (X ⊗ Y ⊗ Z).left, M.IsLB → Triv (M.pull (lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z))).left) → Triv (M.pull (lift (fst X Z) (lift (toUnit (X ⊗ Z) ≫ y₀) (snd X Z))).left) → Triv (M.pull (lift (fst X Y) (lift (snd X Y) (toUnit (X ⊗ Y) ≫ z₀))).left) → Triv M := by
  first | exact @GlobalTheory.CubeGlue.triv_of_triv_faces | exact GlobalTheory.CubeGlue.triv_of_triv_faces | (intros; apply GlobalTheory.CubeGlue.triv_of_triv_faces <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGenThetaOfIsProjBy

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory

theorem exists_gen_theta_of_isProjBy :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ L : LB A.left, L.IsLB → ∃ t : LB.Gen (Theta A L), t.IsGen := by
  intro k _ _ A _ hA hP L hL
  have := hA.comm
  have := hA.geomConnected
  have gi : GeometricallyIntegral A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have conn : ConnectedSpace A.left := by
    have : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    have x : (Sp k : Scheme.{0}) := (default : PrimeSpectrum k)
    have h := A.hom.isConnected_preimage_singleton x
    have e : A.hom ⁻¹' {x} = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim _ _
    rw [e] at h
    exact connectedSpace_iff_univ.2 h
  have face : ∀ {Z : Over (Sp k)} (r : Z ⟶ G3 A) (i : Fin 3), r ≫ x3 A i = toUnit Z ≫ η[A] →
      Triv ((Theta A L).pull r.left) := fun {Z} r i h =>
    (CubeGen.triv_pull_iff L (thφ A (x3 A)) thε r.left).2
      (CubeGen.trivAt_of_formal hL _ (CubeGen.prod_face _ i (toUnit Z).left (congrArg (fun q => q.left) h)))
  exact GlobalTheory.T.theorem_of_cube_two_projective_factors k A A A η[A] η[A] η[A] hA.smooth hA.smooth hA.proper hA.proper hP hP gi gi conn
    (Theta A L) (DVR.linComb_isLB _ hL _ _) (face _ 0 (by simp [x3])) (face _ 1 (by simp [x3]))
    (face _ 2 (by simp [x3]))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleEqMumfordLambdaOfAmpleAlgClose

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AddLineField


open GlobalTheory.PrimitiveOverField in
theorem additive_eq_lam_of_ample : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ N : LB (A ⊗ 𝟙_ (Over (Sp K))).left, Fam A N → ∃ a : 𝟙_ (Over (Sp K)) ⟶ A, Same A N (abelian₂ A L) (𝟙 _) a := by
  intro K _ _ A _ hA L hL hamp N hN
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have hpr : IsProjBy A.hom := by
    obtain ⟨_, _, m, s, hH, hv⟩ := veryAmpleBy_of_relAmple hL hamp (𝟙 A.left) (Category.id_comp _)
      (pull_isLB hL (𝟙 A.left)) (GlobalTheory.lbIso_self (pull_isLB hL _))
    exact ⟨_, hH, m, s, hv⟩
  have hproj : ∀ (R : Type) [CommRing R] (u : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0})
      (π : X ⟶ A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f A.hom u → IsProjBy f :=
    fun R _ u X π f h => GlobalTheory.StabFlat.isProjBy_baseChange hpr h
  have hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen := GlobalTheory.exists_gen_theta_of_isProjBy K A hA hpr L hL
  obtain ⟨S, hS, hSK⟩ := GlobalTheory.T.kernelOfLineBundle_rationalPoints_finite_closed K A hA L hL hamp
  let O : LB A.left := ev N (𝟙 A) (toUnit A)
  have hO : O.IsLB := pull_isLB hN.isLB _
  have hLam : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have pO : ∀ {Y : Over (Sp K)} (u : Y ⟶ A), CechPic.pull u.left (cls O hO) = evc hN.isLB u (toUnit Y) := by
    intro Y u
    rw [cls_ev hN.isLB, pull_evc, Category.comp_id, comp_toUnit]
  have lamO : lam (cls O hO) (fst A A) (snd A A) = 0 := by
    have e := (isAdditive_iff hN.isLB).1 hN.add (A ⊗ A) (fst A A) (snd A A) (toUnit _)
    have e1 := hN.add.evc_one hN.isLB (toUnit (A ⊗ A))
    simp only [lam, pO, e, e1]
    abel
  have key : ∀ x : 𝟙_ (Over (Sp K)) ⟶ A, cls O hO = lam (cls L hL) (toUnit A ≫ x) (𝟙 A) →
      Same A N (abelian₂ A L) (𝟙 _) x := by
    intro x hx
    rw [same_iff hN.isLB hLam]
    have e1 : evc hN.isLB (fst A (𝟙_ (Over (Sp K)))) (snd A _ ≫ 𝟙 _) =
        CechPic.pull (fst A (𝟙_ (Over (Sp K)))).left (cls O hO) := by
      rw [pO, Category.comp_id, toUnit_unique (toUnit _) (snd A _)]
    have e2 : evc hLam (fst A (𝟙_ (Over (Sp K)))) (snd A _ ≫ x) =
        CechPic.pull (fst A (𝟙_ (Over (Sp K)))).left (lam (cls L hL) (toUnit A ≫ x) (𝟙 A)) := by
      have cL : cls (abelian₂ A L) hLam = lam (cls L hL) (fst A A) (snd A A) := cls_cube_two hL _ _ hLam
      rw [evc, cL, pull_lam, pull_lam, lift_fst,
        lift_snd, Category.comp_id, ← Category.assoc, toUnit_unique (fst A _ ≫ toUnit A) (snd A _), lam_comm]
    rw [e1, e2, hx]
  by_contra hno
  have hno' : ∀ x : 𝟙_ (Over (Sp K)) ⟶ A, cls O hO ≠ lam (cls L hL) (toUnit A ≫ x) (𝟙 A) :=
    fun x e => hno ⟨x, key x e⟩
  obtain ⟨F, hF, eF⟩ := cls_surj (lam (cls L hL) (fst A A) (snd A A) - CechPic.pull (snd A A).left (cls O hO))
  have hpq : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  have cst_left : ∀ x : 𝟙_ _ ⟶ A, (toUnit A ≫ x).left = A.hom ≫ x.left := fun x =>
    congrArg (· ≫ x.left) ((Category.comp_id _).symm.trans (Over.w (toUnit A)))
  have s₁ : ∀ x : 𝟙_ _ ⟶ A, cls _ (pull_isLB hF (lift (toUnit A ≫ x) (𝟙 A)).left) =
      lam (cls L hL) (toUnit A ≫ x) (𝟙 A) - cls O hO := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, Over.id_left, pull_id]
  have s₂ : ∀ x : 𝟙_ _ ⟶ A, cls _ (pull_isLB hF (lift (𝟙 A) (toUnit A ≫ x)).left) =
      lam (cls L hL) (toUnit A ≫ x) (𝟙 A) := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, pull_const, sub_zero,
      lam_comm]
  have total : Ac ((fst A A).left ≫ A.hom) F := by
    refine (GlobalTheory.T.lineBundle_product_acyclic_of_affine_base_acyclic K _ _ _ _ _ _ _ hpq inferInstance inferInstance inferInstance inferInstance F hF).1
      fun R _ t Y π f h ht => ac_of_slices hproj hpq h hF fun x hx _ => ?_
    let x' : 𝟙_ _ ⟶ A := Over.homMk x hx
    refine ⟨(lift (toUnit A ≫ x') (𝟙 A)).left, ?_, ?_, ac_of_primitive hA hpr (pull_isLB hF _) ?_ ?_⟩
    · exact (congrArg CommaMorphism.left (lift_fst (toUnit A ≫ x') (𝟙 A))).trans (cst_left x')
    · exact congrArg CommaMorphism.left (lift_snd (toUnit A ≫ x') (𝟙 A))
    · rw [s₁, lam_sub, lam_lam hL hΘ, lamO, sub_zero]
    · rw [s₁, sub_ne_zero]
      exact fun e => hno' x' e.symm
  rw [hpq.w] at total
  let o : Spec (CommRingCat.of K) ⟶ A.left := η[A].left
  have ho : o ≫ A.hom = 𝟙 _ := Over.w η[A]
  have all := GlobalTheory.T.lineBundle_product_acyclic_over_affine_finite_closed K _ _ _ _ _ _ _ hpq.flip inferInstance inferInstance inferInstance
    inferInstance F hF S hS (fun R _ t Y π f h ht hne => ac_of_slices hproj hpq.flip h hF fun x hx hr => by
      let x' : 𝟙_ _ ⟶ A := Over.homMk x hx
      refine ⟨(lift (𝟙 A) (toUnit A ≫ x')).left, ?_, ?_, ac_of_primitive hA hpr (pull_isLB hF _) ?_ ?_⟩
      · exact (congrArg CommaMorphism.left (lift_snd (𝟙 A) (toUnit A ≫ x'))).trans (cst_left x')
      · exact congrArg CommaMorphism.left (lift_fst (𝟙 A) (toUnit A ≫ x'))
      · rw [s₂, lam_lam hL hΘ]
      · rw [s₂]
        intro e
        have hm := hSK x' e
        obtain ⟨y, hy⟩ := hr (IsLocalRing.closedPoint K)
        exact hne y (by rw [hy]; exact hm)) total
  have hs := ac_slice hproj hpq.flip hF all o ho (lift (𝟙 A) (toUnit A ≫ η[A])).left
    ((congrArg CommaMorphism.left (lift_snd (𝟙 A) (toUnit A ≫ η[A]))).trans (cst_left η[A]))
    (congrArg CommaMorphism.left (lift_fst (𝟙 A) (toUnit A ≫ η[A])))
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : Nonempty A.left := ⟨o (IsLocalRing.closedPoint K)⟩
  exact not_ac_of_cls_eq_zero _ (pull_isLB hF _) ((s₂ _).trans (lam_one_left _ _)) hs

end GlobalTheory.AddLineField
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleEqMumfordLambdaOfAmpleAlgCloseStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.additiveLineBundle_eq_mumfordLambda_of_ample_algClosed : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ N : LB (A ⊗ 𝟙_ (Over (Sp K))).left, Fam A N → ∃ a : 𝟙_ (Over (Sp K)) ⟶ A, Same A N (abelian₂ A L) (𝟙 _) a := by
  first | exact @GlobalTheory.AddLineField.additive_eq_lam_of_ample | exact GlobalTheory.AddLineField.additive_eq_lam_of_ample | (intros; apply GlobalTheory.AddLineField.additive_eq_lam_of_ample <;> assumption)
end
end
