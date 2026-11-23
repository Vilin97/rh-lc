module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalDomain
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientDataOfNonzeroSection
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompareUniformisationDataPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationChartValueFormsCorrespond
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericSquare
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfLevel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCpPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNzOfPolAt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelOfExpT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroOnClosedFibreCompleteLocal
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfExpansionDvdStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientDataOfNonzeroSectionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_coefficientData_of_nonzero_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left), GlobalTheory.LN.Cmp φ U U' F → GlobalTheory.LN.CDvr V → Function.Injective φ → (maximalIdeal V).comap φ = maximalIdeal R → GlobalTheory.LN.Under U' U₀.toUnifPre → ∃ (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), q ≠ 0 ∧ U.ExpT (𝟙_ _) 1 σ f ∧ (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) ∧ GlobalTheory.PsiRing.FibNZ (𝟙_ _ ⊗ D.P.A).hom (g 0) ∧ ∀ α, α ≠ 0 → ∃ a ∈ maximalIdeal R, ∃ h : GlobalTheory.UU.SecBT D (𝟙_ _) 1 α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom a (g α) h := by
  first | exact @GlobalTheory.Mum.exists_coefData_of_ne_zero | exact GlobalTheory.Mum.exists_coefData_of_ne_zero | (intros; apply GlobalTheory.Mum.exists_coefData_of_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSettingOfEvenOn

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitSetting

open GlobalTheory.UU GlobalTheory.LN



theorem exists_setting_of_evenOn (laws : Laws) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (P : CP G) (hS : IsSemiAbelian G) (hE : EvenOn P)
    (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) [IsMonHom gen.hom]
    (hA : LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))))
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) (φ : R →+* V) (hφ : Function.Injective φ)
    (hI : maximalIdeal R ≤ (maximalIdeal V).comap φ) :
    ∃ (A' : PolAV (Sp (FractionRing V))) (s : HidaSetting V A' ((Over.pullback (spMap φ)).obj G)) (w : _),
      IsCPMap s.P P (spMap φ) (pullback.fst G.hom (spMap φ)) pullback.condition w := by
  obtain ⟨X, _, _, _, Q₀, P₀, hlev, hev⟩ := hE
  have hG' : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := IsSemiAbelian.pullback _ G hS
  obtain ⟨ψ, sq'⟩ := ClosedPol.exists_generic_square φ hφ
  obtain ⟨A', gen', hgen', hA'⟩ := ClosedPol.exists_fibre_pull laws sq' P.L.isLB A gen hA
  obtain ⟨P', wP, hP', H⟩ := exists_cp_pull _ _ (spMap φ) G ((Over.pullback (spMap φ)).obj G) _ _
    (toBase_mul_pullback G (spMap φ)) P
  rw [← hP'] at hA'
  obtain ⟨P₀', w₀, H₀⟩ := exists_isLevelCP (maximalIdeal V) 0 P'
  have le : maximalIdeal R ^ (0 + 1) ≤ (maximalIdeal V ^ (0 + 1)).comap φ := by
    rw [zero_add, pow_one, pow_one]; exact hI
  let b : R ⧸ maximalIdeal R ^ (0 + 1) →+* V ⧸ maximalIdeal V ^ (0 + 1) := Ideal.quotientMap _ φ le
  have sq : spMap b ≫ thick R (maximalIdeal R) 0 = thick V (maximalIdeal V) 0 ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]
  obtain ⟨wl, hl⟩ := hlev
  obtain ⟨F, pF, w₃, k₃⟩ := ClosedPol.exists_fourth (G := G) (G' := (Over.pullback (spMap φ)).obj G)
    (H := thickObj R (maximalIdeal R) 0 G)
    (H' := thickObj V (maximalIdeal V) 0 ((Over.pullback (spMap φ)).obj G)) (P := P) (P' := P')
    (N := P₀) (N' := P₀') sq (isGrpPullback_pullback G (spMap φ))
    (isGrpPullback_pullback G (thick R (maximalIdeal R) 0))
    (isGrpPullback_pullback _ (thick V (maximalIdeal V) 0)) H hl H₀
  have := hS.smooth
  have := hS.geomConnected
  have : Smooth (thickObj R (maximalIdeal R) 0 G).hom := by
    show Smooth (pullback.snd _ _); infer_instance
  have : GeometricallyConnected (thickObj R (maximalIdeal R) 0 G).hom := by
    show GeometricallyConnected (pullback.snd _ _); infer_instance
  obtain ⟨D₀⟩ := TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max 0) _ P₀ Q₀ hev
  obtain ⟨Q₀', D₀', -, -, -⟩ := ClosedPol.exists_desc_pull pF Q₀ D₀ k₃
  have ev := UniformizationSetting.exists_even_of_desc D₀'
  obtain ⟨wA, hwA⟩ := hA'
  exact ⟨A', ⟨hV, hG', gen', hgen', P', wA, hwA, _, Q₀', P₀', ⟨w₀, H₀⟩, ev⟩, wP, H⟩

end GlobalTheory.Mum.TraitSetting
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRComparisonPreUniformised

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitCompare

open GlobalTheory.UU GlobalTheory.LN



theorem exists_cmp_under : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (_ : GlobalTheory.LN.Cmp φ U U' F), GlobalTheory.LN.CDvr V ∧ Function.Injective φ ∧ (maximalIdeal V).comap φ = maximalIdeal R ∧ GlobalTheory.LN.Under U' U₀.toUnifPre := by
  intro R _ _ _ hB D A G _ _ U hE
  obtain ⟨⟨hL, hL2, -, -, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have hEg := GlobalTheory.LN.ega_holds
  have hU := GlobalTheory.uniformisation_dvr_unconditional
  have := hB.1.1
  have := hB.2
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R (maximalIdeal R)
  have := hV.1
  have hBV : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hle : (maximalIdeal R).map φ ≤ maximalIdeal V := Ideal.map_le_iff_le_comap.2 hc.ge
  have := U.gen_hom
  obtain ⟨A', s, w, hw⟩ :=
    GlobalTheory.Mum.TraitSetting.exists_setting_of_evenOn hL U.P U.semi hE A U.gen ⟨U.wA, U.wA_gen⟩ hV φ hφ hc.ge
  obtain ⟨D', U₀, hLG, -, -⟩ := hU V A' _ s
  obtain ⟨U', hU'⟩ := (GlobalTheory.LN.PreForm.under_exists_and_expands hL hL2 V _ D' A' _ s.semi).1 U₀.toUnifPre
  have := s.semi.smooth
  obtain ⟨w', hw'⟩ := GlobalTheory.PrimeUnif.isCPMap_of_eq hL.globalFns s.gen s.P U'.P (hU'.2.1.trans hLG) hw
  obtain ⟨C, -⟩ := GlobalTheory.T.exists_compare_uniformisationData_pullback hL hL2 hEg R V _ _ hB.1 hBV (maximalIdeal.isMaximal V).ne_top φ hle D D'.toPre A A'
    G _ U U' _ (isGrpPullback_pullback G _) w' hw'
  exact ⟨V, _, _, _, φ, D', A', _, _, _, U', U₀, _, C, hV, hφ, hc, hU'⟩

end GlobalTheory.Mum.TraitCompare
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRComparisonPreUniformisedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_completeDVR_comparison_preUniformised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (_ : GlobalTheory.LN.Cmp φ U U' F), GlobalTheory.LN.CDvr V ∧ Function.Injective φ ∧ (maximalIdeal V).comap φ = maximalIdeal R ∧ GlobalTheory.LN.Under U' U₀.toUnifPre := by
  first | exact @GlobalTheory.Mum.TraitCompare.exists_cmp_under | exact GlobalTheory.Mum.TraitCompare.exists_cmp_under | (intros; apply GlobalTheory.Mum.TraitCompare.exists_cmp_under <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNonzeroLocusOfWeightZeroExpansion

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PreUTheta

theorem exists_mem_nonzeroLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (τ : U.SecGT (𝟙_ _) 1) (g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α), U.ExpT (𝟙_ _) 1 τ g → GlobalTheory.PsiRing.FibNZ (𝟙_ _ ⊗ D.P.A).hom (g 0) → (∀ α, α ≠ 0 → ∃ a ∈ maximalIdeal R, ∃ h : GlobalTheory.UU.SecBT D (𝟙_ _) 1 α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom a (g α) h) → ∃ θ : LB.Sec U.P.L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = closedPoint R := by
  intro R _ _ _ D A G _ _ U τ g hE hnz hmul
  obtain ⟨z₀, hz₀, hn₀⟩ := hnz (closedPoint R)
  have hx : D.P.A.hom ((snd (𝟙_ (Over (Sp R))) D.P.A).left z₀) = closedPoint R :=
    (congrArg (fun q => q z₀) (Over.w (snd (𝟙_ (Over (Sp R))) D.P.A))).trans hz₀
  obtain ⟨y', hy'⟩ := GlobalTheory.ThetaUnit.exists_thick_pt le_rfl 0 D.P.A _ hx
  obtain ⟨y, rfl⟩ := (U.gt 0).q_surj.surj y'
  have hpG : (U.gt 0).pG.left y = (snd (𝟙_ (Over (Sp R))) D.P.A).left z₀ := hy'
  let rG : (thickObj R (maximalIdeal R) 0 G).left ⟶ (𝟙_ (Over (Sp R)) ⊗ G).left :=
    (lift (toUnit _) (fstG (maximalIdeal R) 0 G)).left
  let rB : (thickObj R (maximalIdeal R) 0 G).left ⟶ (𝟙_ (Over (Sp R)) ⊗ D.P.A).left :=
    (lift (toUnit _) (U.gt 0).pG).left
  have h₁ : rG ≫ (snd _ G).left = (fstG (maximalIdeal R) 0 G).left := by
    rw [← Over.comp_left, lift_snd]
  have h₂ : rB ≫ (snd _ D.P.A).left = (U.gt 0).pG.left := by
    rw [← Over.comp_left, lift_snd]
  have h₃ : rB ≫ (fst _ D.P.A).left = rG ≫ (fst _ G).left := by
    rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
  have hinj : ∀ a b : (𝟙_ (Over (Sp R)) ⊗ D.P.A).left,
      (snd (𝟙_ (Over (Sp R))) D.P.A).left a = (snd (𝟙_ (Over (Sp R))) D.P.A).left b → a = b := by
    intro a b hab
    have e := GlobalTheory.PsiExpansion.snd_lift_unit D.P.A
    have key : ∀ c, (lift (toUnit D.P.A) (𝟙 D.P.A)).left ((snd (𝟙_ (Over (Sp R))) D.P.A).left c) = c :=
      fun c => by rw [← Scheme.Hom.comp_apply, e]; rfl
    rw [← key a, ← key b, hab]
  have hrB : rB y = z₀ := hinj _ _ ((congrArg (fun q => q y) h₂).trans hpG)
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' D.P.isLB y
  obtain ⟨JG, hJG⟩ := GlobalTheory.ConstFam.exists_good' U.P.L.isLB y
  obtain ⟨s, hs⟩ := hE 0
  obtain ⟨H₁, H₂⟩ := hs _ (𝟙 _) rG rB (by rw [Category.id_comp]; exact h₁) (by rw [Category.id_comp]; exact h₂) h₃
    y JG J hJG hJ
  have hu : IsUnit (sval (g 0) rB y J) :=
    (GlobalTheory.Ex.OneGen.isUnit_sval_iff (g 0) rB y hJ).2 (by rw [hrB]; exact hn₀)
  have hc' : rB ≫ (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom =
      (thickObj R (maximalIdeal R) 0 G).hom ≫ spMap (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) :=
    Over.w (lift (toUnit _) (U.gt 0).pG)
  rw [Finset.sum_eq_single 0 (fun α _ hα => by
    obtain ⟨a, ha, h, hh⟩ := hmul α hα
    rw [GlobalTheory.IndivisibleSection.sval_of_secIsMul hh _ y hJ, hc', cst_comp,
      Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha), GlobalTheory.GermDiv.cst_zero, zero_mul, zero_mul])
    (fun h => absurd (H₁ 0 h) hu.ne_zero)] at H₂
  have hτ : IsUnit (sval τ rG y JG) :=
    isUnit_of_mul_isUnit_right (H₂ ▸ hu.mul (Units.isUnit _))
  obtain ⟨σ, hσ⟩ := GlobalTheory.PsiExpansion.exists_sameG U.P.L.isLB τ
  rw [hσ _ rG y JG hJG, h₁] at hτ
  have hm := (GlobalTheory.Ex.OneGen.isUnit_sval_iff σ _ y hJG).1 hτ
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.secOfH0 σ, _, GlobalTheory.ThetaClosed.nonzeroLocus_firstPower_section_subset σ hm, ?_⟩
  have hc : (fstG (maximalIdeal R) 0 G).left ≫ G.hom = (U.gt 0).pG.left ≫ D.P.A.hom :=
    (Over.w (fstG (maximalIdeal R) 0 G)).trans (Over.w (U.gt 0).pG).symm
  exact (congrArg (fun q => q y) hc).trans ((congrArg D.P.A.hom hpG).trans hx)

end GlobalTheory.PreUTheta
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNonzeroLocusOfWeightZeroExpansionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_mem_nonzeroLocus_of_weightZero_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (τ : U.SecGT (𝟙_ _) 1) (g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α), U.ExpT (𝟙_ _) 1 τ g → GlobalTheory.PsiRing.FibNZ (𝟙_ _ ⊗ D.P.A).hom (g 0) → (∀ α, α ≠ 0 → ∃ a ∈ maximalIdeal R, ∃ h : GlobalTheory.UU.SecBT D (𝟙_ _) 1 α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom a (g α) h) → ∃ θ : LB.Sec U.P.L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = closedPoint R := by
  first | exact @GlobalTheory.PreUTheta.exists_mem_nonzeroLocus | exact GlobalTheory.PreUTheta.exists_mem_nonzeroLocus | (intros; apply GlobalTheory.PreUTheta.exists_mem_nonzeroLocus <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisedFibrewiseNonvanishingSection

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem thetaNZ_of_preU : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → GlobalTheory.LN.ThetaNZ G U.P.L.L := by
  intro R _ _ _ hB D A G _ _ U hE
  obtain ⟨V, _, _, _, φ, D', A', G', _, _, U', U₀, F, C, hV, hφ, hc, hU⟩ := GlobalTheory.T.exists_completeDVR_comparison_preUniformised R hB D A G U hE
  obtain ⟨σ, f, g, q, hq, hf, hfg, hg0, hgm⟩ := GlobalTheory.T.exists_coefficientData_of_nonzero_section R hB D A G U V φ D' A' G' U' U₀ F C hV hφ hc hU
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_section_quotient_of_expansion_dvd R hB D A G U σ f g q hq hf hfg
  have := U.semi.smooth
  exact GlobalTheory.UnifNormal.thetaNZ_of_closedPoint G _ (GlobalTheory.T.exists_mem_nonzeroLocus_of_weightZero_expansion R D A G U τ g hτ hg0 hgm)

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisedFibrewiseNonvanishingSectionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.preUniformised_fibrewise_nonvanishing_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → GlobalTheory.LN.ThetaNZ G U.P.L.L := by
  first | exact @GlobalTheory.Mum.thetaNZ_of_preU | exact GlobalTheory.Mum.thetaNZ_of_preU | (intros; apply GlobalTheory.Mum.thetaNZ_of_preU <;> assumption)
end
end
