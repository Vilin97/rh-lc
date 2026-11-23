module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLineBundleSectionsGenerateIdealSheaf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimClosureOfCoheightField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberZeroSmallImage
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinateDivisorMultiplicitySumStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DimOfIsArithVar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerCharacteristicDimensionZeroStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionsGenerateIdealProjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericPointNonvanishingCoordinateSection
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepClassDecompositionStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.NumberTheory.Height.NumberField
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjSpace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoheightEqOneOfDimClosure
import Mathlib.Tactic.Basify
import Mathlib.Algebra.Azumaya.Basic

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericPointNonvanishingCoordinateSectionStatement

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup


theorem _root_.GlobalTheory.T.generic_point_nonvanishing_coordinate_section : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f] (k : Fin (m + 1)) (l : Bk n k), (X ⟨k, l⟩ : Pol n) ∉ ptIdeal (f (genericPoint Z)) → genericPoint Z ∈ Out.nonzeroLocus (pullFormSec (f ≫ prB n k) (X l) (isHomogeneous_X ℤ l)) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.VertGen.genericPoint_mem_nonzeroLocus | exact GlobalTheory.CompanionTheory.MixZ.VertGen.genericPoint_mem_nonzeroLocus | (intros; apply GlobalTheory.CompanionTheory.MixZ.VertGen.genericPoint_mem_nonzeroLocus <;> assumption)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.O1ClassPullbackNaturality

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MixZ

def chartPullPullO {R : Type} [CommRing R] {N : ℕ} {S T : Scheme.{0}} (r : T ⟶ S) (φ : S ⟶ PSpace R N) :
    ChartPull (pullO (r ≫ φ) 1) (pullO φ 1) r where
  idx i := i
  le _ _ h := h
  g y i j hi hj := by
    have hle : (pullO (r ≫ φ) 1).U i ⊓ (pullO (r ≫ φ) 1).U j ≤
        r ⁻¹ᵁ ((pullO φ 1).U i ⊓ (pullO φ 1).U j) := fun _ h => h
    have hm : r y ∈ (pullO φ 1).U i ⊓ (pullO φ 1).U j := ⟨hi, hj⟩
    have ev : (((pullO φ 1).g i j : Γ(S, (pullO φ 1).U i ⊓ (pullO φ 1).U j)ˣ) :
        Γ(S, (pullO φ 1).U i ⊓ (pullO φ 1).U j)) = pullRatio φ _ i inf_le_left j :=
      (Units.val_pow_eq_pow_val _ _).trans (pow_one _)
    have ev' : (((pullO (r ≫ φ) 1).g i j : Γ(T, (pullO (r ≫ φ) 1).U i ⊓ (pullO (r ≫ φ) 1).U j)ˣ) :
        Γ(T, (pullO (r ≫ φ) 1).U i ⊓ (pullO (r ≫ φ) 1).U j)) = pullRatio (r ≫ φ) _ i inf_le_left j :=
      (Units.val_pow_eq_pow_val _ _).trans (pow_one _)
    have e : (pullO (r ≫ φ) 1).g i j = res hle (pullU r _ ((pullO φ 1).g i j)) := by
      apply Units.ext
      refine ev'.trans (Eq.trans ?_ (congrArg (r.appLE _ _ hle).hom ev).symm)
      exact (appLE_pullRatio (hi := inf_le_left) r hle).symm
    rw [e, gm_res (𝟙 T) y hle ⟨hi, hj⟩, gm_pull (𝟙 T) r y _ hm, Category.id_comp]

theorem cls_pullO_comp {R : Type} [CommRing R] {N : ℕ} {S T : Scheme.{0}} (r : T ⟶ S) (φ : S ⟶ PSpace R N) :
    cls (pullO (r ≫ φ) 1) (isLB_pullO _ 1) = CechPic.pull r (cls (pullO φ 1) (isLB_pullO _ 1)) := by
  rw [← cls_pull (isLB_pullO φ 1) r (pull_isLB (isLB_pullO φ 1) r)]
  exact (cls_eq_iff _ _).2 (LBIso.chartPull (chartPullPullO r φ)
    (chartPullPull (pullO φ 1) r) (PolBaseChange.lbIso_refl (isLB_pullO φ 1)))

end GlobalTheory.CompanionTheory.MixZ
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.O1ClassPullbackNaturalityStatement

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup


theorem _root_.GlobalTheory.T.cls_pullO_one_comp_eq_pull : ∀ {R : Type} [CommRing R] {N : ℕ} {S T : Scheme.{0}} (r : T ⟶ S) (φ : S ⟶ PSpace R N), cls (pullO (r ≫ φ) 1) (isLB_pullO _ 1) = CechPic.pull r (cls (pullO φ 1) (isLB_pullO _ 1)) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.cls_pullO_comp | exact GlobalTheory.CompanionTheory.MixZ.cls_pullO_comp | (intros; apply GlobalTheory.CompanionTheory.MixZ.cls_pullO_comp <;> assumption)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VertEq

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MixZ.Vert

theorem key (p : ℕ) [Fact p.Prime] {m : ℕ} {n : Fin (m + 1) → ℕ} (a : Fin (m + 1) → ℤ) (d : ℕ) :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f] [Algebra (ZMod p) Γ(Z, ⊤)],
      topologicalKrullDim Z = d → ∀ (L : LB Z) (hL : L.IsLB),
      cls L hL = ∑ k, a k • cls (pullO (f ≫ prB n k) 1) (isLB_pullO _ 1) →
      topSelfIntersection (ZMod p) L d = geoNum d (ptIdeal (f (genericPoint Z))) (fun _ => a) := by
  induction d with
  | zero =>
    intro Z _ f _ _ hd L hL _
    rw [topSelf_zero]
    exact GlobalTheory.T.euler_characteristic_dimension_zero m n Z f p hd _
  | succ d ih =>
    intro Z _ f _ _ hd L hL hc
    have hp : IsProjOver (strHom (ZMod p) (X := Z)) :=
      VertProj.isProjOver_strHom_zmod ℤ _ (mpStr ℤ m n) _ (isArithVar_mpStr m n) Z f p
    have hf := algebraMap_eq_strHom (ZMod p) Z
    have : AlgebraicGeometry.IsNoetherian Z := isNoetherian_of_isProjOver hp
    have hDV := diffVanish_chiPic_of_isProjOver hf (structureModule Z) hp (d := d + 1)
      (by rw [QCoh.suppDim_structureModule, hd])
    have red : ∀ w : Z, Order.coheight w = 1 →
        interNumRed (ZMod p) (⟨closure {w}, isClosed_closure⟩ : Closeds Z) (fun _ : Fin d => L) =
          geoNum d (ptIdeal (f w)) (fun _ => a) := by
      intro w hw
      let C : Closeds Z := ⟨closure {w}, isClosed_closure⟩
      have hirr : IsIrreducible (C : Set Z) := isIrreducible_singleton.closure
      haveI := isIntegral_red hirr
      letI : Algebra (ZMod p) Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) :=
        algebraΓOfHom (redι C ≫ strHom (ZMod p) Z)
      have hfZ : ∀ r : ZMod p, (redι C).appTop (algebraMap (ZMod p) Γ(Z, ⊤) r) =
          algebraMap (ZMod p) Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) r := fun r => by
        rw [hf r]; rfl
      have hdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal C).subscheme = d := by
        rw [topologicalKrullDim_red]
        exact VdmRec.CutSec.dim_closure_of_coheight (isArithVar_mpStr m n) f hd hw
      have hcl : cls (L.pull (redι C)) (pull_isLB hL _) =
          ∑ k, a k • cls (pullO ((redι C ≫ f) ≫ prB n k) 1) (isLB_pullO _ 1) := by

        rw [cls_pull hL, hc, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_zsmul, Category.assoc, GlobalTheory.T.cls_pullO_one_comp_eq_pull (redι C) (f ≫ prB n k)]
      have e := ih _ (redι C ≫ f) hdim _ (pull_isLB hL _) hcl
      rw [interNumRed_def, interNumSub_def, interNumOn_def,
        interNum_pushforward_of_isClosedImmersion hfZ _ (fun _ => hL)]
      rw [topSelf_def] at e
      refine e.trans ?_
      rw [Scheme.Hom.comp_apply, PullVanish.redι_genericPoint w]
    have hrel := (isMultiProjPrime_ptIdeal m n (f (genericPoint Z))).2.2
    have e := hDV.interNum_update_of_cls_eq_sum (ι := Fin (d + 1)) (L := fun _ => L) (by simp) (fun _ => hL) 0
      (Finset.univ) (P := fun k => pullO (f ≫ prB n k) 1) (fun k => isLB_pullO _ 1) a hL hc
    have upd : ∀ N : LB Z, Function.update (fun _ : Fin (d + 1) => L) 0 N = Fin.cons N (fun _ : Fin d => L) := by
      intro N
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · simp [Function.update_of_ne (Fin.succ_ne_zero i)]
    simp only [upd] at e
    have e0 : (Fin.cons L (fun _ : Fin d => L) : Fin (d + 1) → LB Z) = fun _ => L := by
      funext i
      refine Fin.cases rfl (fun _ => rfl) i
    rw [e0] at e
    rw [topSelf_def, e, geoNum, dite_eq_left hrel]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine congrArg (a k * ·) ?_
    have hl := (hrel k).choose_spec
    have hs := GlobalTheory.T.generic_point_nonvanishing_coordinate_section m n Z f k _ hl
    rw [GlobalTheory.CompanionTheory.Ar.IntersectionMultiplicitySection.interNum_cons_eq_finsum_mult (ZMod p) Z hp d (by rw [hd]) _ (isLB_pullO _ 1)
      (fun _ => L) (fun _ => hL) _ hs]
    refine Eq.trans (finsum_congr fun w => ?_) (GlobalTheory.T.coordinate_divisor_multiplicity_sum m n Z f k _ hs (fun W => geoNum d W (fun _ => a)))
    by_cases hw : (divOfSec (isLB_pullO _ 1) _ hs).mult w = 0
    · rw [hw, zero_mul, zero_mul]
    · rw [red w (CartierDiv.coheight_eq_one_of_mult_ne_zero hw)]

theorem vertEq : VertEq := by
  intro m n M A hA X i _ Z _ j _ p _ _ d hd
  refine key p A.a d Z (j ≫ i) hd _ (pull_isLB (pull_isLB M.isLB _) _) ?_

  rw [cls_pull (pull_isLB M.isLB _), cls_pull M.isLB, GlobalTheory.T.hermRep_class_decomposition m n M A hA, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, map_zsmul, Category.assoc, GlobalTheory.T.cls_pullO_one_comp_eq_pull, GlobalTheory.T.cls_pullO_one_comp_eq_pull]

end GlobalTheory.CompanionTheory.MixZ.Vert
end
end
end
