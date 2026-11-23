module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationDataOfSemiAbelianSymmetry
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperUniformisedSemiAbelianOverOpenInAbLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsE8IsSharpBasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackEllipticModel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr

-- Source module: Development.AbelianVarietyTheory.Definitions.Divisors.IsPow8F

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

def IsPow8 {S : Scheme.{0}} (P P₈ : PolAV S) (d : ℕ) (pr : Fin 8 → (P₈.A ⟶ P.A)) (inc : P.A ⟶ P₈.A) : Prop :=
  (∀ u, IsMonHom (pr u)) ∧ IsMonHom inc ∧ (∀ (T : Over S) (y : Fin 8 → (T ⟶ P.A)), ∃! x : T ⟶ P₈.A, ∀ u, x ≫ pr u = y u) ∧
    (∀ u, inc ≫ pr u = if u = 0 then 𝟙 P.A else 1) ∧ LBIso (P₈.L.pull inc.left) (lbPow P.L d)

end GlobalTheory.MBLow

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerEvenUnimodularCharZero

section

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.PowEightField

open GlobalTheory.EighthPowerFactor GlobalTheory.CechPic

theorem exists_eighthPower_evenUnimodular_charZero : ∃ d : ℕ, 1 ≤ d ∧ ∀ (K : Type) [Field K] [CharZero K] (P : PolAV (Sp K)), ∃ (Q : PolAV (Sp K)) (pr : Fin 8 → (Q.A ⟶ P.A)) (inc : P.A ⟶ Q.A), Q.g = 8 * P.g ∧ (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) ∧ IsPow8 P Q d pr inc := by
  obtain ⟨W, hW, hbas⟩ := ZM.exists_isE8_isSharpBasis
  have hW0 : 0 < W 0 0 := by
    have h := hW.1.diag_pos (i := 0)
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Int.cast_add] at h
    have : (0 : ℝ) < (W 0 0 : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨(2 * W 0 0).toNat, by omega, ?_⟩
  intro K _ _ P
  have := P.isAb.comm
  obtain ⟨L₁, L₂⟩ := abelianSchemeLaws_all
  obtain ⟨bas, hb⟩ := hbas P.g
  obtain ⟨a, w, w', hw, hw', hs⟩ := exists_matrices hW.2
  let b : ZM.TBase K 1 := ⟨1, by simp, fun K _ β => by simp⟩
  have hc : (siegOne L₁.globalFns P.isAb P.isLB P.g).Principal :=
    ⟨relAmple_diag_lam P.isAb P.isLB (Moduli.cube_of_isLB _ P P.L P.isLB) P.ample,
      fun T x hx => SiegelOfPolarised.eq_one_of_lam P.isLB P.ktriv x hx⟩
  obtain ⟨t, ⟨pr, hpr, hu, hL, -⟩, h₁, h₂, h₃⟩ := exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB P.g _ W _ a w w'
    bas hW hb hw hw' hs 1 K b _ (𝟙 _) (siegOne L₁.globalFns P.isAb P.isLB P.g) (one_pow _) odd_one hc P.smoothDim
  obtain ⟨inc, hinc, -⟩ := hu P.A fun u => if u = 0 then 𝟙 P.A else 1
  refine ⟨t.pol, pr, inc, rfl, ⟨t.act w, t.act w', t.hom w, t.hom w', h₁, h₃, h₂⟩, hpr, ?_, hu, hinc, ?_⟩
  · refine isMonHom_of_coord hpr hu fun u => ?_
    rw [hinc u]
    by_cases h : u = 0
    · subst h; simp only [↓reduceIte]; exact inferInstanceAs (IsMonHom (𝟙 P.A))
    · simp only [h, ↓reduceIte]; exact inferInstanceAs (IsMonHom (toUnit P.A ≫ η[P.A]))
  ·
    have hP : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
    have hQ : t.pol.L.IsLB := t.pol.isLB
    have hlam : cls _ hP = lam (cls P.L P.isLB) (fst P.A P.A) (snd P.A P.A) := cls_cube_two P.isLB _ _ hP
    have hdiag := (cls_eq_iff (LB.isLB_linComb P.isLB _ _) (pull_isLB hP _)).2 (SiegelOfPolarised.lbIso_diag L₁ P)
    rw [cls_lbPow P.isLB, cls_pull hP, hlam, pull_lam, lift_fst, lift_snd] at hdiag
    have e1 := ((cls_eq_iff hQ (LB.isLB_linComb hP _ _)).2 hL).trans (cls_linComb hP _ _ _)
    refine (cls_eq_iff (pull_isLB hQ _) (LB.isLB_linComb P.isLB _ _)).1 ?_
    refine ((congrArg (pull inc.left) e1).trans ?_).trans (cls_lbPow P.isLB _ _).symm
    rw [hlam]
    erw [map_sum]
    rw [Fintype.sum_eq_single ((0 : Fin 8), (0 : Fin 8))]
    · erw [map_zsmul]
      erw [CechPic.pull_lam, CechPic.pull_lam]
      erw [lift_fst, lift_snd]
      dsimp only
      erw [hinc]
      simp only [↓reduceIte]
      rw [← hdiag, ← natCast_zsmul, ← natCast_zsmul, smul_smul, Int.toNat_of_nonneg (by omega)]
      congr 1
      push_cast
      ring
    · rintro ⟨u, v⟩ huv
      erw [map_zsmul]
      erw [CechPic.pull_lam, CechPic.pull_lam]
      erw [lift_fst, lift_snd]
      dsimp only
      have hi1 : ∀ u : Fin 8, u ≠ 0 → inc ≫ pr u = 1 := fun u h => (hinc u).trans (if_neg h)
      by_cases hu0 : u = 0
      · subst hu0
        have hv0 : v ≠ 0 := fun h => huv (by rw [h])
        erw [hi1 v hv0, lam_one_right, smul_zero]
      · erw [hi1 u hu0, lam_one_left, smul_zero]

end GlobalTheory.MBLow.PowEightField
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerSemiAbelianScheme

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem exists_eighthPower_semiAbelianScheme : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∃ (G₈ : Over (Sp R)) (_ : GrpObj G₈) (prG : Fin 8 → (G₈ ⟶ G)), IsSemiAbelian G₈ ∧ (∀ u, IsMonHom (prG u)) ∧ ∀ (T : Over (Sp R)) (y : Fin 8 → (T ⟶ G)), ∃! x : T ⟶ G₈, ∀ u, x ≫ prG u = y u := by
  intro R _ G _ hG
  haveI : IsCommMonObj G := hG.comm
  refine ⟨powObj G 8, inferInstance, powPr G, ?_, fun u => inferInstance, fun T y => ?_⟩
  · exact GlobalTheory.PowGrp.isSemiAbelian_pow _ (powObj G 8) G 8 (powIsPowGrp G 8) hG
  · refine ⟨(powIsLimit G 8).lift (Fan.mk T y), fun u => (powIsLimit G 8).fac (Fan.mk T y) ⟨u⟩, ?_⟩
    intro x hx
    apply (powIsLimit G 8).hom_ext
    rintro ⟨u⟩
    exact (hx u).trans ((powIsLimit G 8).fac (Fan.mk T y) ⟨u⟩).symm

end GlobalTheory.MBLow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationExtensionLocalDomain

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.SplitPowEight

def isPowGrpOfUnique {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (pr : Fin j → (G' ⟶ G))
    (hpr : ∀ u, IsMonHom (pr u))
    (hu : ∀ (T : Over S) (y : Fin j → (T ⟶ G)), ∃! x : T ⟶ G', ∀ u, x ≫ pr u = y u) : IsPowGrp G' G j :=
  ⟨pr, hpr, Fan.IsLimit.mk _ (fun s => (hu s.pt s.proj).choose) (fun s u => (hu s.pt s.proj).choose_spec.1 u)
    fun s m hm => (hu s.pt s.proj).choose_spec.2 m hm⟩

def powPullback {S S' : Scheme.{0}} (f : S' ⟶ S) {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G' G j) : IsPowGrp ((Over.pullback f).obj G') ((Over.pullback f).obj G) j :=
  ⟨fun u => (Over.pullback f).map (p.pr u), fun u => by have := p.hom u; infer_instance,
    isLimitFanMkObjOfIsLimit (Over.pullback f) _ _ p.lim⟩

theorem exists_unif_pow8 : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ ψ : A.A.left ⟶ G.left, IsGrpPullback A.A G (jK V) ψ → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (io : V →+* W) (em : W →+* AlgebraicClosure (FractionRing V)) (D : DegData W (maximalIdeal W)) (Q : PolAV (Sp (FractionRing W))) (H : Over (Sp W)) (_ : GrpObj H) (_ : IsCommMonObj H) (U : Unif (maximalIdeal W) D Q H) (i : (Over.pullback (spMap io)).obj G ⟶ H) (r : Fin 8 → (H ⟶ (Over.pullback (spMap io)).obj G)), GlobalTheory.LN.CDvr W ∧ io.Finite ∧ Function.Injective io ∧ Function.Injective em ∧ (∀ v, em (io v) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ IsSemiAbelian H ∧ GlobalTheory.LN.ToATotal U.toUnifPre ∧ (∀ k, IsMonHom (r k)) ∧ i ≫ r 0 = 𝟙 _ ∧ ∀ (T : Over (Sp W)) (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y := by
  intro V _ _ _ hV A G _ _ hG ψ hψ
  obtain ⟨hd, hc, hch⟩ := hV
  obtain ⟨gen, hgen, -⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V)) hψ
  obtain ⟨G8, _, prG, hG8, hprG, huG⟩ := GlobalTheory.MBLow.exists_eighthPower_semiAbelianScheme V G hG
  have : IsCommMonObj G8 := hG8.comm
  let p8 : IsPowGrp G8 G 8 := isPowGrpOfUnique prG hprG huG
  let F := AlgebraicClosure (FractionRing V)
  have : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective V F).2 (by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V) F]
    exact (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _))
  have : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := FractionRing V) (C := F)).2 inferInstance
  obtain ⟨W, hWd, hWc, hWf, hsplit⟩ := GlobalTheory.Ex.UnifModel.exists_split V F G8 hG8
  have : CharZero F := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective V F)
  have : CharZero W := RingHom.charZero (algebraMap W F)
  have hio : Function.Injective (algebraMap V W) := fun a b h =>
    FaithfulSMul.algebraMap_injective V F (congrArg Subtype.val h)
  let io : V →+* W := algebraMap V W
  let H := (Over.pullback (spMap io)).obj G8
  let pH : IsPowGrp H ((Over.pullback (spMap io)).obj G) 8 := powPullback (spMap io) p8
  have hH : IsSemiAbelian H := IsSemiAbelian.pullback _ G8 hG8
  obtain ⟨A', ψ', hψ'⟩ := GlobalTheory.UnifProperOpen.exists_polGeneric_pullback V A G gen hgen W io hio
  obtain ⟨d, -, hQ⟩ := GlobalTheory.MBLow.PowEightField.exists_eighthPower_evenUnimodular_charZero
  obtain ⟨Q, pr, inc, -, hS, hP⟩ := hQ (FractionRing W) A'
  let pQ : IsPowGrp Q.A A'.A 8 := isPowGrpOfUnique pr hP.1 hP.2.2.1
  obtain ⟨φ₀, hφ₀, -⟩ := GlobalTheory.PowFibre.exists_pow_pullback pH pQ hψ'
  obtain ⟨genH, hgenH, -⟩ := grpPullback_iso (isGrpPullback_pullback H (jK W)) hφ₀
  obtain ⟨L₁, -⟩ := GlobalTheory.abelianSchemeLaws_all
  have hE : ∃ E : SplitExt (Sp (ResidueField W)), E.IsGt ((Over.pullback (spMap (residue W))).obj H) := hsplit
  obtain ⟨s, -⟩ := GlobalTheory.ZH.exists_setting_of_hypS L₁ GlobalTheory.homExtension_semiAbelian_dvr_unconditional W hWc Q H hH hE
    hS genH hgenH
  obtain ⟨D, U, -, -, hU⟩ := GlobalTheory.uniformisation_dvr_unconditional W Q H s
  obtain ⟨i₀, hi₀, -⟩ := huG G (fun _ => 𝟙 G)
  refine ⟨W, inferInstance, inferInstance, inferInstance, io, algebraMap W F, D, Q, H, inferInstance, inferInstance, U,
    (Over.pullback (spMap io)).map i₀, pH.pr, ⟨hWd, hWc, inferInstance⟩, RingHom.finite_algebraMap.2 hWf, hio,
    Subtype.val_injective, fun v => ?_, hH, hU, pH.hom, ?_, fun T x y h => Fan.IsLimit.hom_ext pH.lim _ _ h⟩
  · exact IsScalarTower.algebraMap_apply V (FractionRing V) F v
  · show (Over.pullback (spMap io)).map i₀ ≫ (Over.pullback (spMap io)).map (prG 0) = _
    rw [← CategoryTheory.Functor.map_comp, hi₀ 0, CategoryTheory.Functor.map_id]

end GlobalTheory.SplitPowEight
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationExtensionLocalDomainStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.degeneration_extension_local_domain : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ ψ : A.A.left ⟶ G.left, IsGrpPullback A.A G (jK V) ψ → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (io : V →+* W) (em : W →+* AlgebraicClosure (FractionRing V)) (D : DegData W (maximalIdeal W)) (Q : PolAV (Sp (FractionRing W))) (H : Over (Sp W)) (_ : GrpObj H) (_ : IsCommMonObj H) (U : Unif (maximalIdeal W) D Q H) (i : (Over.pullback (spMap io)).obj G ⟶ H) (r : Fin 8 → (H ⟶ (Over.pullback (spMap io)).obj G)), GlobalTheory.LN.CDvr W ∧ io.Finite ∧ Function.Injective io ∧ Function.Injective em ∧ (∀ v, em (io v) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ IsSemiAbelian H ∧ GlobalTheory.LN.ToATotal U.toUnifPre ∧ (∀ k, IsMonHom (r k)) ∧ i ≫ r 0 = 𝟙 _ ∧ ∀ (T : Over (Sp W)) (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y := by
  first | exact @GlobalTheory.SplitPowEight.exists_unif_pow8 | exact GlobalTheory.SplitPowEight.exists_unif_pow8 | (intros; apply GlobalTheory.SplitPowEight.exists_unif_pow8 <;> assumption)
end
end
