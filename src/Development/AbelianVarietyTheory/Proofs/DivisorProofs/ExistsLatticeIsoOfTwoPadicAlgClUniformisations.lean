module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankMumfordBundleCechHomologyOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonCompleteDvrPadicAlgClosureUnitBallsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastMore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianIsoDescendsFromAlgebraicExtensioStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianRelDimEqOfGrpPullbackFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiCoordinateNormChartEqCoordinateNormPadicDVRStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiNormIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Mathlib.NumberTheory.Padics.Complex
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormPsiPullLocalRingsOfIntegers
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationMovesAlongDvrInjectionGivenFibreStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecNeZeroOfLbIso

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianPointLiftsThroughIntermediatePul

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolLift

theorem lift_of_pullback_comp : ∀ {S₀ S₁ S₂ : Scheme.{0}} (f₁ : S₁ ⟶ S₀) (f₂ : S₂ ⟶ S₁) (A : PolAV S₀) (B : PolAV S₁) (P : PolAV S₂) (b : B.A.left ⟶ A.A.left) (a : P.A.left ⟶ A.A.left), IsGrpPullback B.A A.A f₁ b → IsGrpPullback P.A A.A (f₂ ≫ f₁) a → ∃ c : P.A.left ⟶ B.A.left, c ≫ b = a ∧ c ≫ B.A.hom = P.A.hom ≫ f₂ ∧ IsGrpPullback P.A B.A f₂ c ∧ (LBIso P.L (A.L.pull a) → LBIso B.L (A.L.pull b) → LBIso P.L (B.L.pull c)) := by
  intro S₀ S₁ S₂ f₁ f₂ A B P b a hB hP
  have w : a ≫ A.A.hom = (P.A.hom ≫ f₂) ≫ f₁ := by
    rw [hP.1.w, Category.assoc]
  refine ⟨hB.1.lift a (P.A.hom ≫ f₂) w, hB.1.lift_fst _ _ w, hB.1.lift_snd _ _ w, ?_, ?_⟩
  · exact IsGrpPullback.cancel hB (hP.congr rfl (hB.1.lift_fst _ _ w).symm) (hB.1.lift_snd _ _ w)
  · intro hPa hBb
    have e : hB.1.lift a (P.A.hom ≫ f₂) w ≫ b = a := hB.1.lift_fst _ _ w
    have h2 : LBIso (B.L.pull (hB.1.lift a (P.A.hom ≫ f₂) w)) (A.L.pull a) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull B.L _ _ rfl)
        (chartPullSame A.L (fun _ => a) (fun _ => b) _ _ fun _ => e.symm) hBb
    exact LBIso.trans P.isLB (pull_isLB A.isLB a) (pull_isLB B.isLB _) hPa h2.symm

end GlobalTheory.PolLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianPointLiftsThroughIntermediatePulStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.polarisedAbelianPoint_lifts_through_intermediate_pullback : ∀ {S₀ S₁ S₂ : Scheme.{0}} (f₁ : S₁ ⟶ S₀) (f₂ : S₂ ⟶ S₁) (A : PolAV S₀) (B : PolAV S₁) (P : PolAV S₂) (b : B.A.left ⟶ A.A.left) (a : P.A.left ⟶ A.A.left), IsGrpPullback B.A A.A f₁ b → IsGrpPullback P.A A.A (f₂ ≫ f₁) a → ∃ c : P.A.left ⟶ B.A.left, c ≫ b = a ∧ c ≫ B.A.hom = P.A.hom ≫ f₂ ∧ IsGrpPullback P.A B.A f₂ c ∧ (LBIso P.L (A.L.pull a) → LBIso B.L (A.L.pull b) → LBIso P.L (B.L.pull c)) := by
  first | exact @GlobalTheory.PolLift.lift_of_pullback_comp | exact GlobalTheory.PolLift.lift_of_pullback_comp | (intros; apply GlobalTheory.PolLift.lift_of_pullback_comp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormPsiPullLocalRingsOfIntegersStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.norm_psi_pull_localRingsOfIntegers : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)] (φ : V →+* V'), (∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V _ v) = algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ (φ v))) → (∀ v : V', ‖algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ v)‖ ≤ 1) → ∀ (D : DegPre V) (D' : DegPre V') (hD : IsPullDeg φ D D') (χ : D'.X) (j : D.P.L.ι) (j' : D'.P.L.ι), ⊤ ≤ (D.c (hD.xe χ)).left ⁻¹ᵁ D.P.L.U j → ⊤ ≤ (D'.c χ).left ⁻¹ᵁ D'.P.L.U j' → ‖algebraMap (FractionRing V') (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V'))) _ ((D'.psi χ).s fun _ => j').val)‖ = ‖algebraMap (FractionRing V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V))) _ ((D.psi (hD.xe χ)).s fun _ => j).val)‖ := by
  first | exact @GlobalTheory.ZH.PsiNormPull.norm_psi_pull | exact GlobalTheory.ZH.PsiNormPull.norm_psi_pull | (intros; apply GlobalTheory.ZH.PsiNormPull.norm_psi_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiCoordinateNormInvariantDegDataPullback

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UnifTorsK.psiNormAt_pull : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)] (φ : V →+* V'), (∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V _ v) = algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ (φ v))) → (∀ v : V', ‖algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ v)‖ ≤ 1) → ∀ (D : DegPre V) (D' : DegPre V') (hD : IsPullDeg φ D D') (χ : D'.X) (r : ℝ), GlobalTheory.UnifTorsK.PsiNormAt p D (hD.xe χ) r ↔ GlobalTheory.UnifTorsK.PsiNormAt p D' χ r := by
  intro p _ V V' _ _ _ _ _ _ _ _ φ hφ hn D D' hD χ r
  have key := GlobalTheory.T.norm_psi_pull_localRingsOfIntegers p V V' φ hφ hn D D' hD χ
  refine ⟨fun H j' hj' => ?_, fun H j hj => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart D.P.isLB ((D.c (hD.xe χ)).left (IsLocalRing.closedPoint V))
    have hi' := ((IsLocalRing.closedPoint_mem_iff (R := V) ((D.c (hD.xe χ)).left ⁻¹ᵁ D.P.L.U i)).1 hi).ge
    exact (key i (j' PUnit.unit) hi' hj').trans (H (fun _ => i) hi')
  · obtain ⟨i, hi⟩ := exists_chart D'.P.isLB ((D'.c χ).left (IsLocalRing.closedPoint V'))
    have hi' := ((IsLocalRing.closedPoint_mem_iff (R := V') ((D'.c χ).left ⁻¹ᵁ D'.P.L.U i)).1 hi).ge
    exact (key (j PUnit.unit) i hj hi').symm.trans (H (fun _ => i) hi')
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiCoordinateNormInvariantDegDataPullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.psiCoordinate_norm_invariant_degData_pullback : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)] (φ : V →+* V'), (∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V _ v) = algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ (φ v))) → (∀ v : V', ‖algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ v)‖ ≤ 1) → ∀ (D : DegPre V) (D' : DegPre V') (hD : IsPullDeg φ D D') (χ : D'.X) (r : ℝ), GlobalTheory.UnifTorsK.PsiNormAt p D (hD.xe χ) r ↔ GlobalTheory.UnifTorsK.PsiNormAt p D' χ r := by
  first | exact @GlobalTheory.UnifTorsK.psiNormAt_pull | exact GlobalTheory.UnifTorsK.psiNormAt_pull | (intros; apply GlobalTheory.UnifTorsK.psiNormAt_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeIsoOfTwoPadicAlgClUniformisations

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifTorsK

theorem spComp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem bc {S S' : Scheme.{0}} (f : S' ⟶ S) (P : PolAV S) : ∃ (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left),
    P'.g = P.g ∧ IsGrpPullback P'.A P.A f φ ∧ LBIso P'.L (P.L.pull φ) := by
  refine ⟨GlobalTheory.AmpleSpecialisation.baseChange P f, pullback.fst P.A.hom f, rfl, isGrpPullback_pullback P.A f, ?_⟩
  obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom f))
  exact ⟨w, hw⟩

theorem lbcomp {X Y Y' : Scheme.{0}} {L : LB X} {L' : LB Y} {L'' : LB Y'} (hL : L.IsLB) (hL' : L'.IsLB)
    (hL'' : L''.IsLB) {φ : Y ⟶ X} {ψ : Y' ⟶ Y} (h : LBIso L' (L.pull φ)) (h' : LBIso L'' (L'.pull ψ)) :
    LBIso L'' (L.pull (ψ ≫ φ)) := by
  have h₁ : LBIso (L'.pull ψ) ((L.pull φ).pull ψ) := GlobalTheory.RigidBundleGlue.LBIso.pull h ψ
  have h₂ : LBIso ((L.pull φ).pull ψ) (L.pull (ψ ≫ φ)) := GlobalTheory.OriginCohom.lbIso_pull_pull_comp hL φ ψ
  have h₃ : LBIso (L'.pull ψ) (L.pull (ψ ≫ φ)) :=
    LBIso.trans (pull_isLB hL' ψ) (pull_isLB (pull_isLB hL φ) ψ) (pull_isLB hL (ψ ≫ φ)) h₁ h₂
  exact LBIso.trans hL'' (pull_isLB hL' ψ) (pull_isLB hL (ψ ≫ φ)) h' h₃

theorem unit_norm (p : ℕ) [Fact p.Prime] (W : Type) [CommRing W] [IsDomain W] [Algebra (FractionRing W) (PadicAlgCl p)]
    (hn : ∀ x : FractionRing W, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W)))
    {r r' : W} (h : Associated r r') :
    ‖algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ r)‖ =
      ‖algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ r')‖ := by
  obtain ⟨u, rfl⟩ := h
  set emb : W →+* PadicAlgCl p := (algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W))
    with hemb
  have hle : ∀ v : W, ‖emb v‖ ≤ 1 := fun v => (hn _).2 ⟨v, rfl⟩
  have hprod : ‖emb (u : W)‖ * ‖emb ((u⁻¹ : Wˣ) : W)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, _root_.map_one, norm_one]
  have hu : ‖emb (u : W)‖ = 1 :=
    le_antisymm (hle _) (by nlinarith [norm_nonneg (emb (u : W)), norm_nonneg (emb ((u⁻¹ : Wˣ) : W)), hle ((u⁻¹ : Wˣ) : W)])
  have e₁ : ∀ v : W, algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ v) = emb v := fun _ => rfl
  rw [e₁, e₁, map_mul, norm_mul, hu, _root_.mul_one]



theorem main : ∀ {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω'] (S : ThetaSys o Ω) (S' : ThetaSys o' Ω') (ρ : S.Real) (ρ' : S'.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (y₁ : S'.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (u' : ρ'.UTest p y₁) (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a → IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a' → LBIso P₀.L (u.A.L.pull a) → LBIso P₀.L (u'.A.L.pull a') → ∃ e : u.D.toPre.X ≃+ u'.D.toPre.X, (∀ χ r, u.PsiNorm χ r ↔ u'.PsiNorm (e χ) r) ∧ ∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) (pk' : QkPt u'.D.toPre (PadicAlgCl p) m) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A) (w : Sp (PadicAlgCl p) ⟶ P₀.A.left), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' → w ≫ P₀.A.hom = 𝟙 _ → w ≫ a = x.left → w ≫ a' = x'.left → CongMod m pk'.y (e pk.y) := by
  intro o Ω o' Ω' _ _ _ _ _ _ S S' ρ ρ' p _ y₀ y₁ u u' P₀ a a' ha ha' hLa hLa'

  obtain ⟨W₀, _, _, _, _, hW₀c, hW₀n, -, hW₀alg, ⟨φ₀, φK₀, hφK₀, hmax₀, hcp₀⟩,
      ⟨φ₀', φK₀', hφK₀', hmax₀', hcp₀'⟩⟩ :=
    GlobalTheory.T.exists_common_complete_dvr_padicAlgClosure_unitBalls p u.V u'.V u.complete u'.complete u.norm_le u'.norm_le ∅

  obtain ⟨B₁, b₁, -, hb₁, hLb₁⟩ := bc (spMap φK₀) u.A
  obtain ⟨B₂, b₂, -, hb₂, hLb₂⟩ := bc (spMap φK₀') u'.A
  have hpa : IsGrpPullback P₀.A u.A.A
      (spMap (algebraMap (FractionRing W₀) (PadicAlgCl p)) ≫ spMap φK₀) a :=
    ha.congr (by rw [spComp, hcp₀]) rfl
  have hpa' : IsGrpPullback P₀.A u'.A.A
      (spMap (algebraMap (FractionRing W₀) (PadicAlgCl p)) ≫ spMap φK₀') a' :=
    ha'.congr (by rw [spComp, hcp₀']) rfl
  obtain ⟨c₁, hc₁b, hc₁h, hc₁, hc₁L⟩ := GlobalTheory.T.polarisedAbelianPoint_lifts_through_intermediate_pullback (spMap φK₀)
    (spMap (algebraMap (FractionRing W₀) (PadicAlgCl p))) u.A B₁ P₀ b₁ a hb₁ hpa
  obtain ⟨c₂, hc₂b, hc₂h, hc₂, hc₂L⟩ := GlobalTheory.T.polarisedAbelianPoint_lifts_through_intermediate_pullback (spMap φK₀')
    (spMap (algebraMap (FractionRing W₀) (PadicAlgCl p))) u'.A B₂ P₀ b₂ a' hb₂ hpa'
  have hLc₁ := hc₁L hLa hLb₁
  have hLc₂ := hc₂L hLa' hLb₂

  obtain ⟨s, hs⟩ := GlobalTheory.T.polarisedAbelian_iso_descends_from_algebraicExtension (FractionRing W₀) (PadicAlgCl p) (algebraMap _ _) hW₀alg B₁ B₂ P₀ c₁ c₂
    hc₁ hc₂ hLc₁ hLc₂

  obtain ⟨W, _, _, _, _, hWc, hWn, hsW, -, ⟨α₀, αK, hαK, hαmax, hαcp⟩, -⟩ :=
    GlobalTheory.T.exists_common_complete_dvr_padicAlgClosure_unitBalls p W₀ W₀ hW₀c hW₀c hW₀n hW₀n s
  have hcomm : (αK.comp φK₀).comp (algebraMap u.V (FractionRing u.V)) =
      (algebraMap W (FractionRing W)).comp (α₀.comp φ₀) := by
    ext v
    have h1 := RingHom.congr_fun hφK₀ v
    have h2 := RingHom.congr_fun hαK (φ₀ v)
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [h1, h2]
  have hcomm' : (αK.comp φK₀').comp (algebraMap u'.V (FractionRing u'.V)) =
      (algebraMap W (FractionRing W)).comp (α₀.comp φ₀') := by
    ext v
    have h1 := RingHom.congr_fun hφK₀' v
    have h2 := RingHom.congr_fun hαK (φ₀' v)
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [h1, h2]
  have hmax : (IsLocalRing.maximalIdeal u.V).map (α₀.comp φ₀) ≤ IsLocalRing.maximalIdeal W := by
    rw [← Ideal.map_map]
    exact (Ideal.map_mono hmax₀).trans hαmax
  have hmax' : (IsLocalRing.maximalIdeal u'.V).map (α₀.comp φ₀') ≤ IsLocalRing.maximalIdeal W := by
    rw [← Ideal.map_map]
    exact (Ideal.map_mono hmax₀').trans hαmax
  have hF : (algebraMap (FractionRing W) (PadicAlgCl p)).comp (αK.comp φK₀) =
      algebraMap (FractionRing u.V) (PadicAlgCl p) := by
    rw [← RingHom.comp_assoc, hαcp, hcp₀]
  have hF' : (algebraMap (FractionRing W) (PadicAlgCl p)).comp (αK.comp φK₀') =
      algebraMap (FractionRing u'.V) (PadicAlgCl p) := by
    rw [← RingHom.comp_assoc, hαcp, hcp₀']

  obtain ⟨C, ψ₁, hgC, hψ₁, hLψ₁⟩ := bc (spMap (αK.comp φK₀)) u.A
  have hψ₁' : IsGrpPullback C.A u.A.A (spMap αK ≫ spMap φK₀) ψ₁ := hψ₁.congr (spComp _ _).symm rfl
  obtain ⟨χ, hχb, -, hχ, hχL⟩ := GlobalTheory.T.polarisedAbelianPoint_lifts_through_intermediate_pullback (spMap φK₀) (spMap αK) u.A B₁ C b₁ ψ₁ hb₁ hψ₁'
  have hLχ := hχL hLψ₁ hLb₁
  obtain ⟨χ₂, hχ₂, hLχ₂, hd⟩ :=
    hs (FractionRing W) αK (algebraMap (FractionRing W) (PadicAlgCl p)) hαcp hsW C χ hχ hLχ
  have hψ₂ : IsGrpPullback C.A u'.A.A (spMap (αK.comp φK₀')) (χ₂ ≫ b₂) :=
    (hχ₂.comp hb₂).congr (spComp _ _) rfl
  have hLψ₂ : LBIso C.L (u'.A.L.pull (χ₂ ≫ b₂)) := lbcomp u'.A.isLB B₂.isLB C.isLB hLb₂ hLχ₂
  have hgC' : C.g = u'.A.g := GlobalTheory.T.polarisedAbelian_relDim_eq_of_grpPullback_field (FractionRing W) _ (spMap (αK.comp φK₀')) u'.A C (χ₂ ≫ b₂) hψ₂

  obtain ⟨D₁, hD₁, G₁, _, _, U₁, hG₁, htor₁⟩ :=
    GlobalTheory.T.uniformisation_moves_along_dvr_injection_given_fibre u.V W u.complete hWc (α₀.comp φ₀) (αK.comp φK₀) hcomm hmax u.D u.A u.G u.U C ψ₁ hψ₁ hLψ₁
      hgC (PadicAlgCl p) hF
  obtain ⟨D₂, hD₂, G₂, _, _, U₂, hG₂, htor₂⟩ :=
    GlobalTheory.T.uniformisation_moves_along_dvr_injection_given_fibre u'.V W u'.complete hWc (α₀.comp φ₀') (αK.comp φK₀') hcomm' hmax' u'.D u'.A u'.G u'.U C
      (χ₂ ≫ b₂) hψ₂ hLψ₂ hgC' (PadicAlgCl p) hF'
  haveI : CharZero (PadicAlgCl p) :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[p] (PadicAlgCl p)).injective
  haveI : CharZero W :=
    RingHom.charZero ((algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W)))

  obtain ⟨ε, hεψ, hεt⟩ := GlobalTheory.TwoUnifTors.main W hWc C G₁ G₂ hG₁ hG₂ D₁ D₂ U₁ U₂
  have hv₁ : ∀ v : u.V, algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ v) =
      algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ ((α₀.comp φ₀) v)) := by
    intro v
    have h1 := RingHom.congr_fun hcomm v
    have h2 := RingHom.congr_fun hF (algebraMap u.V (FractionRing u.V) v)
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [← h2, h1]
  have hv₂ : ∀ v : u'.V, algebraMap (FractionRing u'.V) (PadicAlgCl p) (algebraMap u'.V _ v) =
      algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ ((α₀.comp φ₀') v)) := by
    intro v
    have h1 := RingHom.congr_fun hcomm' v
    have h2 := RingHom.congr_fun hF' (algebraMap u'.V (FractionRing u'.V) v)
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [← h2, h1]
  have hW1 : ∀ v : W, ‖algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ v)‖ ≤ 1 :=
    fun v => (hWn _).2 ⟨v, rfl⟩
  refine ⟨hD₁.xe.symm.trans (ε.trans hD₂.xe), ?_, ?_⟩
  · intro χ r
    obtain ⟨y, rfl⟩ := hD₁.xe.surjective χ
    rw [psiNorm_iff, psiNorm_iff]
    have e1 := GlobalTheory.T.psiCoordinate_norm_invariant_degData_pullback p u.V W (α₀.comp φ₀) hv₁ hW1 u.D.toPre D₁.toPre hD₁ y r
    have e2 := GlobalTheory.T.psiCoordinate_norm_invariant_degData_pullback p u'.V W (α₀.comp φ₀') hv₂ hW1 u'.D.toPre D₂.toPre hD₂ (ε y) r
    obtain ⟨⟨r₁, hr₁⟩, n₁⟩ := GlobalTheory.T.psiCoordinate_norm_chart_eq_coordinate_norm_padicDVR p W hWn D₁ y
    obtain ⟨⟨r₂, hr₂⟩, n₂⟩ := GlobalTheory.T.psiCoordinate_norm_chart_eq_coordinate_norm_padicDVR p W hWn D₂ (ε y)
    have e3 : PsiNormAt p D₁.toPre y r ↔ PsiNormAt p D₂.toPre (ε y) r := by
      rw [n₁ r₁ hr₁ r, n₂ r₂ hr₂ r, unit_norm p W hWn (hεψ y r₁ r₂ hr₁ hr₂)]
    simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    exact e1.trans (e3.trans e2.symm)
  · intro m pk pk' x x' w hm hx hx' hw hwx hwx'
    obtain ⟨q₁, x₁, hq₁, hx₁ψ, hx₁⟩ := htor₁ m hm pk x hx
    obtain ⟨q₂, x₂, hq₂, hx₂ψ, hx₂⟩ := htor₂ m hm pk' x' hx'

    have hsq : c₁ ≫ B₁.A.hom =
        (P₀.A.hom ≫ spMap (algebraMap (FractionRing W) (PadicAlgCl p))) ≫ spMap αK := by
      rw [hc₁h, Category.assoc, spComp, hαcp]
    obtain ⟨d, hdχ, hdh⟩ : ∃ d : P₀.A.left ⟶ C.A.left, d ≫ χ = c₁ ∧
        d ≫ C.A.hom = P₀.A.hom ≫ spMap (algebraMap (FractionRing W) (PadicAlgCl p)) :=
      ⟨hχ.1.lift _ _ hsq, hχ.1.lift_fst _ _ _, hχ.1.lift_snd _ _ _⟩
    have hdχ₂ : d ≫ χ₂ = c₂ := hd d hdχ hdh
    have hT : (TFK (R := W) (PadicAlgCl p)).hom = spMap (algebraMap (FractionRing W) (PadicAlgCl p)) := rfl
    have hbase : (w ≫ d) ≫ C.A.hom = (TFK (R := W) (PadicAlgCl p)).hom := by
      rw [Category.assoc, hdh, ← Category.assoc, hw, Category.id_comp, hT]
    have k₁ : x₁.left = w ≫ d := by
      apply hψ₁.1.hom_ext
      · rw [hx₁ψ, ← hχb, Category.assoc, reassoc_of% hdχ, hc₁b, hwx]
      · rw [Over.w x₁, hbase]
    have k₂ : x₂.left = w ≫ d := by
      apply hψ₂.1.hom_ext
      · rw [hx₂ψ, Category.assoc, reassoc_of% hdχ₂, hc₂b, hwx']
      · rw [Over.w x₂, hbase]
    have hxx : x₂ = x₁ := Over.OverMorphism.ext (k₂.trans k₁.symm)
    rw [hxx] at hx₂
    have hc := hεt (PadicAlgCl p) m q₁ q₂ x₁ hm hx₁ hx₂
    unfold CongMod at hc ⊢
    obtain ⟨z, hz⟩ := hc
    refine ⟨hD₂.xe z, ?_⟩
    rw [← hq₂, hz, map_add (f := _), map_nsmul, ← hq₁]
    simp

end GlobalTheory.UnifTorsK
end
end
