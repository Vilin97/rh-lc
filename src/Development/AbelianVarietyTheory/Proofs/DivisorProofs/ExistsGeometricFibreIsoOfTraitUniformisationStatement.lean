module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreThetaConstantsAlgebraicOverCompleteAlgCloseStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPrimitiveRootUnitOnIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomDescendsAlgClosedCharZero
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianVarietyDescendsOfRationalThetaPoStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomDescendsAlgClosedCharZeroStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.abelianVariety_hom_descends_algClosed_charZero : ∀ (K Ω : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field Ω] (j : K →+* Ω) (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (B B' : Over (Sp Ω)) [GrpObj B] [GrpObj B'] (b : B.left ⟶ A.left) (b' : B'.left ⟶ A'.left), IsAbelianScheme A → IsAbelianScheme A' → IsGrpPullback B A (spMap j) b → IsGrpPullback B' A' (spMap j) b' → ∀ f : B ⟶ B', IsMonHom f → ∃ f₀ : A ⟶ A', IsMonHom f₀ ∧ b ≫ f₀.left = f.left ≫ b' := by
  first | exact @GlobalTheory.AlgClosedHomDescent.hom_descends | exact GlobalTheory.AlgClosedHomDescent.hom_descends | (intros; apply GlobalTheory.AlgClosedHomDescent.hom_descends <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypSOfBaseChange

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SymDescentAlgClosed

theorem hypS_of_baseChange : ∀ (K Ω : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field Ω] (j : K →+* Ω) (A : PolAV (Sp K)) (B : PolAV (Sp Ω)) (b : B.A.left ⟶ A.A.left), IsGrpPullback B.A A.A (spMap j) b → LBIso B.L (A.L.pull b) → (letI := B.isAb.comm; GlobalTheory.ZH.HypS B.A B.L) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) := by
  intro K Ω _ _ _ _ j A B b h hb hS
  letI := B.isAb.comm
  letI := A.isAb.comm
  obtain ⟨w, wd, hw, hwd, hs, hp, ha⟩ := hS
  obtain ⟨w₀, -, e⟩ := GlobalTheory.T.abelianVariety_hom_descends_algClosed_charZero K Ω j A.A A.A B.A B.A b b A.isAb A.isAb h h w hw
  obtain ⟨wd₀, -, ed⟩ := GlobalTheory.T.abelianVariety_hom_descends_algClosed_charZero K Ω j A.A A.A B.A B.A b b A.isAb A.isAb h h wd hwd
  exact GlobalTheory.SymLevelDescent.hypS_descend j A.isAb h A.isLB B.isLB hb e ed hw hwd hs hp ha

end GlobalTheory.SymDescentAlgClosed
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPtOfMap

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ThetaDown

theorem isThetaPt_of_map : ∀ (B : Scheme.{0}) [IsLocallyNoetherian B] (P : PolAV B) (K C : Type) [Field K] [Field C] (j : K →+* C) (s : Sp K ⟶ B) (x : Sp C ⟶ B) (hx : spMap j ≫ s = x) (k : ℕ) (J : Type) (p : J → (Over.mk s ⟶ P.A)) (w : J → K), (∀ i, p i ^ k ^ 2 = 1) → IsThetaPt P k (fun i => (Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ p i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (j (w i))) → IsThetaPt P k p (fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (w i)) := by
  intro B _ P K C _ _ j s x hx k J p w hp H
  have h₁ : Laws := GlobalTheory.firstFiveLaws.1
  have h₂ : Laws2 := GlobalTheory.firstFiveLaws.2.1
  have hk : Odd k := H.1
  let eC : Γ(Sp C, ⊤) ≃+* C := (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv
  have hkC : (k : C) ≠ 0 := by
    have := H.2.1.map eC.toRingHom
    rw [map_natCast] at this
    exact this.ne_zero
  have hkK : IsUnit (k : K) := IsUnit.mk0 _ fun h0 => hkC (by rw [← map_natCast j, h0, map_zero])
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.Ex.Specialise.exists_isThetaPt_local h₁ h₂ P s hk hkK p hp
  have hC := GlobalTheory.Ex.Specialise.isThetaPt_map h₂ P j hx hw₀
  haveI : IsLocalRing Γ((Over.mk x).left, ⊤) := eC.symm.isLocalRing
  obtain ⟨u, hu⟩ := GlobalTheory.ThetaUniq.exists_unit_over h₁.globalFns P hk
    (GlobalTheory.ThetaUniq.isThetaPtOver_of_local _ x hC) (GlobalTheory.ThetaUniq.isThetaPtOver_of_local _ x H)
  set c : C := eC (u : Γ((Over.mk x).left, ⊤)) with hcdef
  have hc : ∀ i, j (w i) = c * j (w₀ i) := fun i => by
    have q := (congrArg eC (hu i)).trans (map_mul eC _ _)
    exact (eC.apply_symm_apply (j (w i))).symm.trans (q.trans (congrArg (_ * ·) (eC.apply_symm_apply (j (w₀ i)))))
  have hu0 : c ≠ 0 := fun h0 => (u.isUnit.map eC.toRingHom).ne_zero h0
  by_cases hz : ∀ i, w₀ i = 0
  · have e : w = w₀ := funext fun i => j.injective (by rw [hc, hz, map_zero, MulZeroClass.mul_zero])
    subst e
    exact hw₀
  · push_neg at hz
    obtain ⟨i₀, hi₀⟩ := hz
    have hd : j (w i₀ / w₀ i₀) = c := by
      rw [map_div₀, hc, mul_div_assoc, div_self ((map_ne_zero j).2 hi₀), _root_.mul_one]
    have hd0 : w i₀ / w₀ i₀ ≠ 0 := fun h0 => hu0 (by rw [← hd, h0, map_zero])
    have e : ∀ i, w i = (w i₀ / w₀ i₀) * w₀ i := fun i => j.injective (by rw [map_mul, hd, hc])
    have := GlobalTheory.Ex.Specialise.isThetaPt_mul P hw₀ hd0
    convert this using 2 with i
    rw [e i]

end GlobalTheory.Mum.ThetaDown
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisBaseChange

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.MBLow

theorem hypS_of_isPolFibre : ∀ (K K' : Type) [Field K] [Field K'] (f : K →+* K') (P : PolAV (Sp K)) (P' : PolAV (Sp K')) (ψ : P'.A.left ⟶ P.A.left), IsPolFibre f P P' ψ → (letI := P.isAb.comm; GlobalTheory.ZH.HypS P.A P.L) → (letI := P'.isAb.comm; GlobalTheory.ZH.HypS P'.A P'.L) := by
  intro K K' _ _ f P P' ψ h hS
  letI := P.isAb.comm
  letI := P'.isAb.comm
  exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ P.A P'.A (spMap f) ψ P.L P'.L P.isLB P'.isLB h.2.1 h.2.2.symm hS
end GlobalTheory.MBLow
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisBaseChangeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleSymmetryHypothesis_baseChange : ∀ (K K' : Type) [Field K] [Field K'] (f : K →+* K') (P : PolAV (Sp K)) (P' : PolAV (Sp K')) (ψ : P'.A.left ⟶ P.A.left), IsPolFibre f P P' ψ → (letI := P.isAb.comm; GlobalTheory.ZH.HypS P.A P.L) → (letI := P'.isAb.comm; GlobalTheory.ZH.HypS P'.A P'.L) := by
  first | exact @GlobalTheory.MBLow.hypS_of_isPolFibre | exact GlobalTheory.MBLow.hypS_of_isPolFibre | (intros; apply GlobalTheory.MBLow.hypS_of_isPolFibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeometricFibreIsoOfTraitUniformisation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GeoDesc

theorem exists_geomIso_of_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∃ (A₀ : PolAV (Sp (Kb R))) (e₀ : Kb R →+* Kb W), (∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) ∧ (letI := A₀.isAb.comm; GlobalTheory.ZH.HypS A₀.A A₀.L) ∧ GeomIso A₀ A' e₀ (algebraMap (FractionRing W) (Kb W)) := by
  intro R _ _ _ hR D n hn ho hu W _ _ _ hW φ hφ hloc D' G' _ _ A' hD hG hU hS
  haveI : CharZero R := hR.2
  haveI : CharZero (Kb R) := charZero_of_injective_ringHom (f := (algebraMap (FractionRing R) (Kb R)).comp
    (algebraMap R (FractionRing R))) ((algebraMap (FractionRing R) (Kb R)).injective.comp
      (IsFractionRing.injective R (FractionRing R)))
  let φK : FractionRing R →+* FractionRing W :=
    IsFractionRing.lift (g := (algebraMap W (FractionRing W)).comp φ) ((IsFractionRing.injective W (FractionRing W)).comp hφ)
  letI : Algebra (FractionRing R) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp φK).toAlgebra
  haveI : Module.IsTorsionFree (FractionRing R) (Kb W) := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree (FractionRing R) (Kb R) := DivisionSemiring.to_moduleIsTorsionFree
  let e₀ : Kb R →+* Kb W := (IsAlgClosed.lift : Kb R →ₐ[FractionRing R] Kb W).toRingHom
  have he₀ : ∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) =
      algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r)) := by
    intro r
    show (IsAlgClosed.lift : Kb R →ₐ[FractionRing R] Kb W) (algebraMap _ _ _) = _
    rw [AlgHom.commutes]
    show algebraMap (FractionRing W) (Kb W) (φK _) = _
    rw [IsFractionRing.lift_algebraMap]
    rfl
  obtain ⟨B, b, hB⟩ := GlobalTheory.exists_isPolFibre GlobalTheory.polBaseChange_holds (algebraMap (FractionRing W) (Kb W)) A'
  have hth : ∀ j : ℕ, 1 ≤ j → ∃ (Ix : Type) (x : Ix → (baseOver (Sp (Kb W)) ⟶ B.A)) (v : Ix → Kb R),
      (∀ z : baseOver (Sp (Kb W)) ⟶ B.A, z ^ ((n ^ j) ^ 2) = 1 → ∃ i, x i = z) ∧
      IsThetaPt B (n ^ j) x fun i => (Scheme.ΓSpecIso (CommRingCat.of (Kb W))).inv.hom (e₀ (v i)) := by
    intro j hj
    obtain ⟨C, _, jC, Ix, x, v, hcov, htor, hC⟩ :=
      GlobalTheory.T.fibre_thetaConstants_algebraic_over_completeAlgClosed R hR D n hn ho hu W hW φ hφ hloc D' G' A' hD hG hU e₀ he₀ B b hB.2.1 hB.2.2.symm j hj
    exact ⟨Ix, x, v, hcov, GlobalTheory.Mum.ThetaDown.isThetaPt_of_map (Sp (Kb W)) B (Kb W) C jC (𝟙 _) (spMap jC) (Category.comp_id _) (n ^ j) Ix x
      (fun i => e₀ (v i)) htor hC⟩
  obtain ⟨A₀, a, ha, hLa⟩ := GlobalTheory.T.polarisedAbelianVariety_descends_of_rational_thetaPoints (Kb R) (Kb W) e₀ B n hn ho hth
  refine ⟨A₀, e₀, he₀, ?_, B, a, b, ha, hLa, hB.2.1, hB.2.2.symm⟩
  exact GlobalTheory.SymDescentAlgClosed.hypS_of_baseChange (Kb R) (Kb W) e₀ A₀ B a ha hLa (GlobalTheory.T.lineBundleSymmetryHypothesis_baseChange _ _ _ A' B b hB hS)

end GlobalTheory.Mum.GeoDesc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeometricFibreIsoOfTraitUniformisationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_geometricFibreIso_of_traitUniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∃ (A₀ : PolAV (Sp (Kb R))) (e₀ : Kb R →+* Kb W), (∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) ∧ (letI := A₀.isAb.comm; GlobalTheory.ZH.HypS A₀.A A₀.L) ∧ GeomIso A₀ A' e₀ (algebraMap (FractionRing W) (Kb W)) := by
  first | exact @GlobalTheory.Mum.GeoDesc.exists_geomIso_of_unif | exact GlobalTheory.Mum.GeoDesc.exists_geomIso_of_unif | (intros; apply GlobalTheory.Mum.GeoDesc.exists_geomIso_of_unif <;> assumption)
end
end
