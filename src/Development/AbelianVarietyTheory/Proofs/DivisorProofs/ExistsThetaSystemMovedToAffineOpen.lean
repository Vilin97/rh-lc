module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartLiftToModuliSchemeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonGenericFibreDiagonalEndEighthPowerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8ThetaPowerOverModuliDomainStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalSectionBasesShrunkAffineChart
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisExtendsNormalAffineC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVDimEqOfGrpPullbackField
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianVarietyPullbackAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOnAffineOpenFinitelyGenerated
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerPresentationEndomorphismsPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupExtendsNormalAffineChartAfterRescaling

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalSectionBasesShrunkAffineChartStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_universal_section_bases_shrunk_affineChart : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (w : M.Z), IsAffineOpen U₀ → w ∈ U₀ → ∀ (P : PolAV (Sp (M.ringOn U₀))) (N : ℕ), 1 ≤ N → ∃ (U : M.Z.Opens) (h : M.ringOn U₀ ≤ M.ringOn U) (P' : PolAV (Sp (M.ringOn U))) (φ : P'.A.left ⟶ P.A.left), U ≤ U₀ ∧ IsAffineOpen U ∧ w ∈ U ∧ IsGrpPullback P'.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧ LBIso P'.L (P.L.pull φ) ∧ P'.g = P.g ∧ (∃ th : LB.Sec (LPow P'.A P'.L 1 (baseOver (Sp (M.ringOn U)))), GlobalTheory.ThetaReal.UnivBasis P' 1 (fun _ : Fin 1 => SecM.ofSec P'.A th)) ∧ ∃ b : Fin (N ^ P'.g) → SecM P'.A P'.L (N : ℕ) (baseOver (Sp (M.ringOn U))), GlobalTheory.ThetaReal.UnivBasis P' (N : ℕ) b := by
  first | exact @GlobalTheory.Poinc.exists_univBasis_affineChart | exact GlobalTheory.Poinc.exists_univBasis_affineChart | (intros; apply GlobalTheory.Poinc.exists_univBasis_affineChart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisExtendsNormalAffineCStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.lineBundleSymmetryHypothesis_extends_normal_affineChart : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → (U : Set M.Z).Nonempty → GlobalTheory.IsNormalScheme M.Z → ∀ (R₀ : Type) [CommRing R₀] (P : PolAV (Sp R₀)) (P' : PolAV (Sp (M.ringOn U))) (P₀ : PolAV (Sp Ω)) (f : R₀ →+* Ω) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsGrpPullback P₀.A P.A (spMap f) a → IsGrpPullback P₀.A P'.A (spMap (M.ringOn U).val.toRingHom) a' → LBIso P₀.L (P.L.pull a) → LBIso P₀.L (P'.L.pull a') → HypS P.A P.L → HypS P'.A P'.L := by
  first | exact @GlobalTheory.Poinc.hypS_of_generic_ringOn | exact GlobalTheory.Poinc.hypS_of_generic_ringOn | (intros; apply GlobalTheory.Poinc.hypS_of_generic_ringOn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVDimEqOfGrpPullbackFieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.polAV_dim_eq_of_grpPullback_field : ∀ (K : Type) [Field K] (T : Scheme.{0}) (P : PolAV T) (P₀ : PolAV (Sp K)) (f : Sp K ⟶ T) (a : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A f a → P₀.g = P.g := by
  first | exact @GlobalTheory.polAV_g_eq_of_isGrpPullback | exact GlobalTheory.polAV_g_eq_of_isGrpPullback | (intros; apply GlobalTheory.polAV_g_eq_of_isGrpPullback <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianVarietyPullbackAffineOpenStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.polarized_abelian_variety_pullback_affine_open : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (U : X₁.M.Z.Opens) (P' : PolAV (Sp (X₁.M.ringOn U))) (P₀ : PolAV (Sp X₁.Ω₁)) (a : P₀.A.left ⟶ X₁.ρ.P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsAffineOpen U → (U : Set X₁.M.Z).Nonempty → IsGrpPullback P₀.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a → IsGrpPullback P₀.A P'.A (spMap (X₁.M.ringOn U).val.toRingHom) a' → LBIso P₀.L (X₁.ρ.P.L.pull a) → LBIso P₀.L (P'.L.pull a') → ∃ pt' : X₁.S.Gam → (baseOver (Sp (X₁.M.ringOn U)) ⟶ P'.A), (∀ x y, pt' (x + y) = pt' x * pt' y) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp (X₁.M.ringOn U)) (z : Over.mk x ⟶ P'.A), z ^ (X₁.S.r * X₁.S.N) = 1 → ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp (X₁.M.ringOn U))) ≫ pt' c = z) ∧ (∀ x y (c : (X₁.M.ringOn U)ˣ), (c : (X₁.M.ringOn U)) = algebraMap X₁.o₁ (X₁.M.ringOn U) (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ x y).val)) → WeilIs P'.A P'.L (X₁.S.r * X₁.S.N : ℕ) (pt' x) (pt' y) (unitOn c)) ∧ (∀ x, ∃ w0 : Sp X₁.Ω₁ ⟶ P₀.A.left, w0 ≫ a = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w0 ≫ a' = spMap (X₁.M.ringOn U).val.toRingHom ≫ (pt' x).left) := by
  first | exact @GlobalTheory.Poinc.TorsExtend.exists_labelled_on_chart | exact GlobalTheory.Poinc.TorsExtend.exists_labelled_on_chart | (intros; apply GlobalTheory.Poinc.TorsExtend.exists_labelled_on_chart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOnAffineOpenFinitelyGeneratedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.ringOn_affineOpen_finitelyGenerated : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → (U : Set M.Z).Nonempty → (M.ringOn U).FG := by
  first | exact @GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen | exact GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen | (intros; apply GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpOverOfPolarizedPullback

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc

theorem sharpOver_baseChange : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left), SharpOver F W P u → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → SharpOver F W P' (f ≫ u) := by
  intro g n F W T T' P P' u f φ hS hφ hL
  obtain ⟨c, hc, pr, hpr, huniv, hbun⟩ := hS
  obtain ⟨c', hc', pr', hpr', huniv', hbun', -⟩ :=
    sharpOver_pullback_end g n _ _ F W T T' P P' u f φ c hc pr hpr huniv hbun hφ hL
  exact ⟨c', hc', pr', hpr', huniv', hbun'⟩

end GlobalTheory.Poinc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpOverOfPolarizedPullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.sharpOver_of_polarized_pullback : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left), SharpOver F W P u → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → SharpOver F W P' (f ≫ u) := by
  first | exact @GlobalTheory.Poinc.sharpOver_baseChange | exact GlobalTheory.Poinc.sharpOver_baseChange | (intros; apply GlobalTheory.Poinc.sharpOver_baseChange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupExtendsNormalAffineChartAfterRescalingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.thetaSetup_extends_normal_affineChart_after_rescaling : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (U : X₁.M.Z.Opens) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (fg : (X₁.M.ringOn U).FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ (X₁.M.ringOn U), ∃ b ∈ (X₁.M.ringOn U), x = a / b) (u' : Sp (X₁.M.ringOn U) ⟶ F.X) (P' : PolAV (Sp (X₁.M.ringOn U))) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A)) (P₀ : PolAV (Sp X₁.Ω₁)) (a : P₀.A.left ⟶ X₁.ρ.P.A.left) (a' : P₀.A.left ⟶ P'.A.left) (ε₀ : Matrix (Fin 8) (Fin 8) ℤ → (P₀.A ⟶ P₀.A)) (pt' : X₁.S.Gam → (baseOver (Sp (X₁.M.ringOn U)) ⟶ P'.A)) (th : LB.Sec (LPow P'.A P'.L 1 (baseOver (Sp (X₁.M.ringOn U))))) (b : Fin (X₁.S.N ^ P'.g) → SecM P'.A P'.L (X₁.S.N : ℕ) (baseOver (Sp (X₁.M.ringOn U)))), IsAffineOpen U → (U : Set X₁.M.Z).Nonempty → IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → IsDiagEnd F W P' u' ε' → IsGrpPullback P₀.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a → IsGrpPullback P₀.A P'.A (spMap (X₁.M.ringOn U).val.toRingHom) a' → LBIso P₀.L (X₁.ρ.P.L.pull a) → LBIso P₀.L (P'.L.pull a') → (∀ E, (ε₀ E).left ≫ a = a ≫ (ε₁ E).left ∧ (ε₀ E).left ≫ a' = a' ≫ (ε' E).left) → P'.g = X₁.S.g → HypS P'.A P'.L → (∀ x y, pt' (x + y) = pt' x * pt' y) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp (X₁.M.ringOn U)) (z : Over.mk x ⟶ P'.A), z ^ (X₁.S.r * X₁.S.N) = 1 → ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp (X₁.M.ringOn U))) ≫ pt' c = z) → (∀ x y (c : (X₁.M.ringOn U)ˣ), (c : (X₁.M.ringOn U)) = algebraMap X₁.o₁ (X₁.M.ringOn U) (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ x y).val)) → WeilIs P'.A P'.L (X₁.S.r * X₁.S.N : ℕ) (pt' x) (pt' y) (unitOn c)) → (∀ x, ∃ w0 : Sp X₁.Ω₁ ⟶ P₀.A.left, w0 ≫ a = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w0 ≫ a' = spMap (X₁.M.ringOn U).val.toRingHom ≫ (pt' x).left) → GlobalTheory.ThetaReal.UnivBasis P' 1 (fun _ : Fin 1 => SecM.ofSec P'.A th) → GlobalTheory.ThetaReal.UnivBasis P' (X₁.S.N : ℕ) b → ∃ (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (hth : ∀ x, c₀ * X₁.S.th x ∈ (X₁.M.ringOn U)) (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ (X₁.M.ringOn U)) (ρ' : (X₁.S.rechart c₀ hc (X₁.M.ringOn U) fg frac hth hev).Real) (ε'' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X₁.ρ ε₁ ρ' ε'' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X₁.ρ.i₀ ∧ IsDiagEnd F W ρ'.P u' ε'' := by
  first | exact @GlobalTheory.Poinc.exists_real_rechart_of_univBasis | exact GlobalTheory.Poinc.exists_real_rechart_of_univBasis | (intros; apply GlobalTheory.Poinc.exists_real_rechart_of_univBasis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemMovedToAffineOpen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Poinc.exists_rechart_affine : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ w : X₁.M.Z, X₁.π w ∈ Set.range i → ∃ (U : X₁.M.Z.Opens) (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (fg : (X₁.M.ringOn U).FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ X₁.M.ringOn U, ∃ b ∈ X₁.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ X₁.M.ringOn U) (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ X₁.M.ringOn U) (ρ' : (X₁.S.rechart c₀ hc (X₁.M.ringOn U) fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)) (u' : Sp (X₁.M.ringOn U) ⟶ F.X), IsAffineOpen U ∧ w ∈ U ∧ (∀ w' ∈ U, X₁.π w' ∈ Set.range i) ∧ Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X₁.ρ.i₀ ∧ IsDiagEnd F W ρ'.P u' ε' ∧ spMap (X₁.M.ringOn U).val.toRingHom ≫ u' = spMap X₁.S.R.val.toRingHom ≫ X₁.u := by
  intro g n F W Z i X₁ _hg1 _hn3 _hodd _himm he8 _hti _hproj ε₁ hε₁ w hw
  obtain ⟨U₀, u₀, hU₀a, hwU₀, hU₀i, hu₀⟩ := GlobalTheory.T.exists_affineChart_lift_to_moduli_scheme g n F W Z i X₁ w hw
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.T.exists_e8ThetaPower_over_moduli_domain g n F W he8 (X₁.M.ringOn U₀) u₀
  have hN : 1 ≤ X₁.S.N := by have := X₁.S.N_ge; omega
  obtain ⟨U, h, P', φ, hUU₀, hUa, hwU, hφ, hφL, _hgφ, ⟨th, hth⟩, b, hb⟩ :=
    GlobalTheory.T.exists_universal_section_bases_shrunk_affineChart X₁.o₁ X₁.Ω₁ X₁.M U₀ w hU₀a hwU₀ P₁ X₁.S.N hN
  have hne : ((U : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := ⟨w, hwU⟩
  have hsh : SharpOver F W P' (spMap (Subalgebra.inclusion h).toRingHom ≫ u₀) :=
    GlobalTheory.T.sharpOver_of_polarized_pullback g n F W _ _ P₁ P' u₀ _ φ hP₁ hφ hφL
  have hsp : spMap (X₁.M.ringOn U).val.toRingHom ≫ spMap (Subalgebra.inclusion h).toRingHom =
      spMap (X₁.M.ringOn U₀).val.toRingHom := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  have hcomp : spMap X₁.S.R.val.toRingHom ≫ X₁.u =
      spMap (X₁.M.ringOn U).val.toRingHom ≫ (spMap (Subalgebra.inclusion h).toRingHom ≫ u₀) := by
    rw [← Category.assoc, hsp, hu₀]
  obtain ⟨ε', hε', P₀, a, a', ε₀, ha, ha', hL, hL', hε₀⟩ :=
    GlobalTheory.T.exists_common_genericFibre_diagonalEnd_eighthPower g n F W X₁.S.R (X₁.M.ringOn U) X₁.Ω₁ X₁.S.R.val.toRingHom (X₁.M.ringOn U).val.toRingHom X₁.ρ.P X₁.u ε₁ P' _
      hε₁ hsh hcomp
  have hg' : P'.g = X₁.S.g :=
    (GlobalTheory.T.polAV_dim_eq_of_grpPullback_field X₁.Ω₁ _ P' P₀ _ a' ha').symm.trans ((GlobalTheory.T.polAV_dim_eq_of_grpPullback_field X₁.Ω₁ _ X₁.ρ.P P₀ _ a ha).trans X₁.ρ.g_eq)
  have hyp : HypS P'.A P'.L :=
    GlobalTheory.T.lineBundleSymmetryHypothesis_extends_normal_affineChart X₁.o₁ X₁.Ω₁ X₁.M U hUa hne X₁.normal X₁.S.R X₁.ρ.P P' P₀ _ a a' ha ha' hL hL' X₁.ρ.hypS
  obtain ⟨pt', hadd, hbij, hweil, hmatch⟩ := GlobalTheory.T.polarized_abelian_variety_pullback_affine_open g n F W Z i X₁ U P' P₀ a a' hUa hne ha ha' hL hL'
  have fg : (X₁.M.ringOn U).FG := GlobalTheory.T.ringOn_affineOpen_finitelyGenerated X₁.o₁ X₁.Ω₁ X₁.M U hUa hne
  have frac : ∀ x : X₁.Ω₁, ∃ a ∈ X₁.M.ringOn U, ∃ b ∈ X₁.M.ringOn U, x = a / b := fun x => by
    obtain ⟨p, q, -, e⟩ := RatModel.exists_eq_div hUa hne x
    exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨p, rfl⟩, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨q, rfl⟩, e⟩
  obtain ⟨c₀, hc, hthm, hevm, ρ', ε'', hSame, hi₀, hD⟩ :=
    GlobalTheory.T.thetaSetup_extends_normal_affineChart_after_rescaling g n F W Z i X₁ U ε₁ fg frac _ P' ε' P₀ a a' ε₀ pt' th b hUa hne hε₁ hε' ha ha' hL hL' hε₀ hg' hyp hadd hbij
      hweil hmatch hth hb
  exact ⟨U, c₀, hc, fg, frac, hthm, hevm, ρ', ε'', _, hUa, hwU, fun w' hw' => hU₀i w' (hUU₀ hw'), hSame, hi₀, hD,
    hcomp.symm⟩
end
end
