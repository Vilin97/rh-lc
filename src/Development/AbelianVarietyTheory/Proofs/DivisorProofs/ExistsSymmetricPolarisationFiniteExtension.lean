module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalvingPointAbelianSchemeFiniteExtStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTrivialRigidTranslateLineBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveBundleEqTranslateAmpleNoetherianLocalStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMumfordBundleInvPullbackPrimitive

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PolDeg.NegPrim
open GlobalTheory.CechPic

variable {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G]

theorem lam_inv_left {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x z : T ⟶ G) :
    lam (cls L hL) x⁻¹ z = - lam (cls L hL) x z := by
  have h := lam_mul_left hL hΘ x⁻¹ x z
  rw [inv_mul_cancel, lam_one_left] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem lam_inv_inv {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x y : T ⟶ G) :
    lam (cls L hL) x⁻¹ y⁻¹ = lam (cls L hL) x y := by
  rw [lam_inv_left hL hΘ, lam_comm, lam_inv_left hL hΘ, lam_comm, neg_neg]

theorem lam_pull_inv (c : Pic G.left) (x y : T ⟶ G) :
    lam (pull (ι[G]).left c) x y = lam c x⁻¹ y⁻¹ := by
  simp only [lam, ← pull_comp, ← Over.comp_left, ← Hom.inv_def, mul_inv, inv_one]

end GlobalTheory.PolDeg.NegPrim

namespace GlobalTheory.PolDeg.NegPrim
open GlobalTheory.CechPic

theorem lam_negPull_sub_isTrivial : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (_ : CubicalStr B M), IsAbelianScheme B → ∃ u : LB.Gen (abelian₂ B (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])), u.IsGen := by
  intro A _ _ _ B _ _ M cub _
  have hΘ : ∃ t : LB.Gen (Theta B M.L), t.IsGen := ⟨cub.t, cub.isGen⟩
  have hN : (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]).IsLB := LB.isLB_linComb M.isLB _ _
  have hΛ : (abelian₂ B (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])).IsLB := LB.isLB_linComb hN _ _
  refine (cls_eq_zero_iff hΛ).1 ?_
  have hc : cls _ hN = pull (ι[B]).left (cls M.L M.isLB) - cls M.L M.isLB := by
    rw [cls_linComb M.isLB, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id, sub_eq_add_neg]
  refine (cls_cube_two hN (fst B B) (snd B B) hΛ).trans ?_
  have e : ∀ (c c' : Pic B.left) (x y : B ⊗ B ⟶ B), lam (c - c') x y = lam c x y - lam c' x y := fun c c' x y => by
    simp only [lam, map_sub]; abel
  rw [hc, e, lam_pull_inv, lam_inv_inv M.isLB hΘ, sub_self]

end GlobalTheory.PolDeg.NegPrim
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMumfordBundleInvPullbackPrimitiveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_generator_mumfordBundle_inv_pullback_primitive : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (_ : CubicalStr B M), IsAbelianScheme B → ∃ u : LB.Gen (abelian₂ B (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])), u.IsGen := by
  first | exact @GlobalTheory.PolDeg.NegPrim.lam_negPull_sub_isTrivial | exact GlobalTheory.PolDeg.NegPrim.lam_negPull_sub_isTrivial | (intros; apply GlobalTheory.PolDeg.NegPrim.lam_negPull_sub_isTrivial <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricRigidifiedTranslateAmpleKTrivial

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymTranslate

open GlobalTheory.CechPic (cls)

theorem exists_sym_translate : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (b : 𝟙_ _ ⟶ B), IsAbelianScheme B → M.IsLB → RelAmple B M → KTriv B M → (∃ t : LB.Gen (Theta B M), t.IsGen) → LBIso (M.pull (ι[B]).left) (M.pull ((toUnit B ≫ b ^ 2) * 𝟙 B).left) → ∃ L : LB B.left, L.IsLB ∧ Rigidified B L ∧ Out.Sym B L ∧ RelAmple B L ∧ KTriv B L ∧ LBIso (abelian₂ B L) (abelian₂ B M) := by
  intro A _ _ _ B _ _ M b hB hM hamp hK hT hiso
  have := hB.proper
  obtain ⟨c, hc⟩ := hT
  have hL' : (GlobalTheory.RigidTranslate.rigTransl M b).IsLB := LB.isLB_linComb hM _ _
  refine ⟨GlobalTheory.RigidTranslate.rigTransl M b, hL', GlobalTheory.RigidTranslate.rigidified_rigTransl hM, ?_,
    GlobalTheory.RigidTranslate.relAmple_rigTransl_of_section b hM hamp, GlobalTheory.RigidTranslate.kTriv_rigTransl_any _ B M hM b hK, ?_⟩
  · have h2 : CechPic.pull (GrpObj.inv : B ⟶ B).left (cls M hM) =
        CechPic.pull ((toUnit B ≫ b ^ 2) * 𝟙 B).left (cls M hM) :=
      (CechPic.cls_eq_iff (pull_isLB hM _) (pull_isLB hM _)).2 hiso
    have h3 := congrArg (CechPic.pull (𝟙 B * (toUnit B ≫ b)⁻¹).left) h2
    rw [← CechPic.pull_comp, ← CechPic.pull_comp, ← Over.comp_left, ← Over.comp_left] at h3
    have e1 : (𝟙 B * (toUnit B ≫ b)⁻¹) ≫ (GrpObj.inv : B ⟶ B) =
        (GrpObj.inv : B ⟶ B) ≫ (𝟙 B * (toUnit B ≫ b)) := by
      rw [← Hom.inv_def, MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, mul_inv, inv_inv,
        Hom.inv_def, Category.id_comp]
    have e2 : (𝟙 B * (toUnit B ≫ b)⁻¹) ≫ ((toUnit B ≫ b ^ 2) * 𝟙 B) = 𝟙 B * (toUnit B ≫ b) := by
      rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, MonObj.comp_pow, sq,
        _root_.mul_comm (𝟙 B), _root_.mul_comm (𝟙 B), _root_.mul_assoc, mul_inv_cancel_left]
    rw [e1, e2, Over.comp_left, CechPic.pull_comp] at h3
    have e3 : (GrpObj.inv : B ⟶ B).left ≫ (toUnit B ≫ b).left = (toUnit B ≫ b).left := by
      rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
    have h4 : cls _ hL' = CechPic.pull (𝟙 B * (toUnit B ≫ b)).left (cls M hM) -
        CechPic.pull (toUnit B ≫ b).left (cls M hM) := by
      rw [CechPic.cls_linComb hM, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, ← sub_eq_add_neg]
      rfl
    refine GlobalTheory.RigSymSubring.sym_of_cls hL' ?_
    rw [h4, map_sub, h3, ← CechPic.pull_comp, e3]
  · have hΛ : (abelian₂ B M).IsLB := LB.isLB_linComb hM _ _
    refine (CechPic.cls_eq_iff (LB.isLB_linComb hL' _ _) hΛ).1
      (((CechPic.cls_eq_iff (LB.isLB_linComb hL' _ _) (pull_isLB hΛ _)).2
        (GlobalTheory.RigidTranslate.lam_rigTransl hM c hc)).trans ?_)
    rw [CechPic.cls_pull hΛ]
    exact CechPic.pull_id _

end GlobalTheory.SymTranslate
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricRigidifiedTranslateAmpleKTrivialStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_symmetric_rigidified_translate_ample_K_trivial : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (b : 𝟙_ _ ⟶ B), IsAbelianScheme B → M.IsLB → RelAmple B M → KTriv B M → (∃ t : LB.Gen (Theta B M), t.IsGen) → LBIso (M.pull (ι[B]).left) (M.pull ((toUnit B ≫ b ^ 2) * 𝟙 B).left) → ∃ L : LB B.left, L.IsLB ∧ Rigidified B L ∧ Out.Sym B L ∧ RelAmple B L ∧ KTriv B L ∧ LBIso (abelian₂ B L) (abelian₂ B M) := by
  first | exact @GlobalTheory.SymTranslate.exists_sym_translate | exact GlobalTheory.SymTranslate.exists_sym_translate | (intros; apply GlobalTheory.SymTranslate.exists_sym_translate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricPolarisationFiniteExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg.SymPol

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}

theorem inv_comm (h : IsGrpPullback G' G f φ) : (ι[G']).left ≫ φ = φ ≫ (ι[G]).left := by
  have e := congrArg (fun z => z.left) (map_inv (pushHom h G') (𝟙 G'))
  rw [Hom.inv_def, Hom.inv_def, Category.id_comp] at e
  refine Eq.trans e ?_
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem exists_half (h : IsGrpPullback G' G f φ) (a : 𝟙_ (Over S) ⟶ G) (b : Over.mk f ⟶ G) (hb : b ^ 2 = toUnit _ ≫ a) :
    ∃ b' : 𝟙_ (Over S') ⟶ G',
      ((toUnit G' ≫ b' ^ 2) * 𝟙 G').left ≫ φ = φ ≫ ((toUnit G ≫ a) * 𝟙 G).left := by
  have w : b.left ≫ G.hom = 𝟙 S' ≫ f := (Over.w b).trans (Category.id_comp _).symm
  let b' : 𝟙_ (Over S') ⟶ G' := Over.homMk (h.1.lift _ _ w) (h.1.lift_snd _ _ _)
  have hb' : b'.left ≫ φ = b.left := h.1.lift_fst _ _ _
  let j : Over.mk (G'.hom ≫ f) ⟶ Over.mk f := Over.homMk G'.hom rfl
  have hu : (toUnit G').left = G'.hom := (Category.comp_id _).symm.trans (Over.w (toUnit G'))
  have e₁ : pushHom h G' (toUnit G' ≫ b') = j ≫ b := Over.OverMorphism.ext (by
    show ((toUnit G').left ≫ b'.left) ≫ φ = G'.hom ≫ b.left
    rw [Category.assoc, hb', hu])
  have e₂ : pushHom h G' ((toUnit G' ≫ b' ^ 2) * 𝟙 G') = pushHom h G' (𝟙 G') ≫ ((toUnit G ≫ a) * 𝟙 G) := by
    rw [map_mul, MonObj.comp_pow, map_pow, e₁, ← MonObj.comp_pow, hb, MonObj.comp_mul, Category.comp_id,
      ← Category.assoc, ← Category.assoc, toUnit_unique (j ≫ toUnit _) (pushHom h G' (𝟙 G') ≫ toUnit G)]
  refine ⟨b', (congrArg (fun z => z.left) e₂).trans ?_⟩
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem exists_gen_theta_pull [IsCommMonObj G] [IsCommMonObj G'] (h : IsGrpPullback G' G f φ) {L : LB G.left}
    (ht : ∃ t : LB.Gen (Theta G L), t.IsGen) : ∃ t : LB.Gen (Theta G' (L.pull φ)), t.IsGen := by
  obtain ⟨t, ht⟩ := ht
  exact gen_chartPull (chartPullLinComb L φ _ _ _ (cubeMapOf h).F3 fun I => (cubeMapOf h).psum_comm I.down) t ht

end GlobalTheory.PolDeg.SymPol


open GlobalTheory.PolDeg.SymPol GlobalTheory.CechPic in
theorem GlobalTheory.PolDeg.exists_symmetric_pol : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R), IsCN R → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ IsGrpPullback P.A Q.B (spMap ρ) β ∧ IsSquare β β₂ ∧ (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) := by
  intro R _ _ _ Q hR
  haveI := hR.1
  have hM := Q.M.isLB
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  obtain ⟨a, ha⟩ := GlobalTheory.T.primitive_bundle_eq_translate_ample_noetherian_local R Q.B Q.g Q.M.L _ Q.isAb Q.smoothDim hM Q.ample Q.ktriv hΘ
    (LB.isLB_linComb hM _ _) (GlobalTheory.T.exists_generator_mumfordBundle_inv_pullback_primitive R Q.B Q.M Q.cub Q.isAb)
  have ea := (cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb hM _ _)).2 ha
  rw [cls_linComb hM, cls_linComb hM, Fin.sum_univ_two, Fin.sum_univ_two] at ea
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, add_left_inj] at ea
  obtain ⟨R', _, _, _, ρ, b, hR', hinj, hfin, hloc, hb⟩ := GlobalTheory.T.exists_halving_point_abelianScheme_finite_ext R Q.B a hR Q.isAb
  haveI := hR'.1
  have h := isGrpPullback_pullback Q.B (spMap ρ)
  have hA : IsAbelianScheme ((Over.pullback (spMap ρ)).obj Q.B) := by
    have := Q.isAb.comm
    have hc : IsCommMonObj ((Over.pullback (spMap ρ)).obj Q.B) := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) h.1 Q.isAb.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 Q.isAb.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 Q.isAb.geomConnected⟩
  haveI := hA.comm
  obtain ⟨b', hb'⟩ := exists_half h a b hb
  have hM' := pull_isLB hM (pullback.fst Q.B.hom (spMap ρ))
  have hid := (cls_eq_iff hM' hM').1 rfl
  obtain ⟨w, hw⟩ := id hid
  obtain ⟨L, hL, hrig, hsym, hamp, hK, hΛ⟩ := GlobalTheory.T.exists_symmetric_rigidified_translate_ample_K_trivial R' _ _ b' hA hM'
    (relAmple_pull h.1 hM hM' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) Q.ample)
    (kTriv_pull h hM hM' ((isGen_iff w).1 hw) Q.ktriv) (exists_gen_theta_pull h hΘ)
    ((cls_eq_iff (pull_isLB hM' _) (pull_isLB hM' _)).1 (by
      rw [cls_pull hM', cls_pull hM', cls_pull hM, ← pull_comp, ← pull_comp, inv_comm h, hb', pull_comp, pull_comp, ea]))
  obtain ⟨β₂, hβ₂⟩ := SiegPull.exists_isSquare h.1.w
  exact ⟨R', _, _, _, ρ,
    { A := (Over.pullback (spMap ρ)).obj Q.B, isAb := hA, g := Q.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 Q.smoothDim
      L := L, isLB := hL, rigid := hrig, sym := hsym, ample := hamp, ktriv := hK }, _, β₂, hR', hinj, hfin, hloc, h, hβ₂,
    LBIso.trans (LB.isLB_linComb hL _ _) (LB.isLB_linComb hM' _ _) (pull_isLB (LB.isLB_linComb hM _ _) _) hΛ
      (SiegPull.lbIso_lam_pull h hid hβ₂)⟩

end
end
end
