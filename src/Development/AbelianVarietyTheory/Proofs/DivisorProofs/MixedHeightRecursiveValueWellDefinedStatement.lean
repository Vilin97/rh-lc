module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveDegreeIndependentOfSectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArithStatement
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbientStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanIntegralPullMulDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchRestrictedEqZeroOfNoComplexPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithAmbientVerticalOrArithmeticVarietyStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductionIndependentOfSectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductiveRhsSymmIsometryInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightUniqueRestrictClosedSubschemeStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoClosedImmersionsSameGenericPoint

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
open Limits

namespace GlobalTheory

theorem range_closedImmersion_eq_closure_genericPoint {X Y : Scheme.{0}} [IsIntegral Y] (i : Y ⟶ X)
    [IsClosedImmersion i] : Set.range i = closure {i (genericPoint Y)} := by
  have hc : IsClosedMap i := i.isClosedEmbedding.isClosedMap
  have h1 : Set.range i = i '' closure {genericPoint Y} := by
    rw [(genericPoint_spec Y).def, Set.image_univ]
  rw [h1]
  apply le_antisymm
  · exact image_closure_subset_closure_image i.continuous |>.trans (by rw [Set.image_singleton])
  · rw [← Set.image_singleton]
    exact closure_minimal (Set.image_mono subset_closure) (hc _ isClosed_closure)

theorem iso_of_closedImmersion_genericPoint_eq :
    ∀ (X Y Y' : Scheme.{0}) [IsIntegral Y] [IsIntegral Y'] (i : Y ⟶ X) (i' : Y' ⟶ X)
      [IsClosedImmersion i] [IsClosedImmersion i'], i (genericPoint Y) = i' (genericPoint Y') →
      ∃ g : Y' ⟶ Y, IsIso g ∧ g ≫ i = i' ∧ g (genericPoint Y') = genericPoint Y := by
  intro X Y Y' _ _ i i' _ _ h
  have hr : Set.range i = Set.range i' := by
    rw [range_closedImmersion_eq_closure_genericPoint, range_closedImmersion_eq_closure_genericPoint, h]
  have hs : Function.Surjective (pullback.snd i i') := by
    intro y'
    obtain ⟨y, hy⟩ : i' y' ∈ Set.range i := hr ▸ ⟨y', rfl⟩
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := i) (g := i') y y' hy
    exact ⟨z, hz⟩
  have hf : Function.Surjective (pullback.fst i i') := by
    intro y
    obtain ⟨y', hy⟩ : i y ∈ Set.range i' := hr ▸ ⟨y, rfl⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i) (g := i') y y' hy.symm
    exact ⟨z, hz⟩
  haveI : Surjective (pullback.snd i i') := ⟨hs⟩
  haveI : Surjective (pullback.fst i i') := ⟨hf⟩
  haveI : IsIso (pullback.snd i i') := isIso_of_isClosedImmersion_of_surjective _
  haveI : IsIso (pullback.fst i i') := isIso_of_isClosedImmersion_of_surjective _
  refine ⟨inv (pullback.snd i i') ≫ pullback.fst i i', inferInstance, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  · apply i.isClosedEmbedding.injective
    have e := congrArg (fun f : Y' ⟶ X => f (genericPoint Y')) (show (inv (pullback.snd i i') ≫ pullback.fst i i') ≫ i = i' by
      rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc])
    rw [Scheme.Hom.comp_apply] at e
    rw [e, h]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoClosedImmersionsSameGenericPointStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.exists_iso_closedImmersions_same_genericPoint : ∀ (X Y Y' : Scheme.{0}) [IsIntegral Y] [IsIntegral Y'] (i : Y ⟶ X) (i' : Y' ⟶ X) [IsClosedImmersion i] [IsClosedImmersion i'], i (genericPoint Y) = i' (genericPoint Y') → ∃ g : Y' ⟶ Y, IsIso g ∧ g ≫ i = i' ∧ g (genericPoint Y') = genericPoint Y := by
  first | exact @GlobalTheory.iso_of_closedImmersion_genericPoint_eq | exact GlobalTheory.iso_of_closedImmersion_genericPoint_eq | (intros; apply GlobalTheory.iso_of_closedImmersion_genericPoint_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveHeightFormulaRhsTransportIso

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.MixHt
open GlobalTheory.TrueGeo.SmallSec GlobalTheory.FrameGlue.Pull GlobalTheory.MultPull GlobalTheory.Points

variable {k : Type} [CommRing k]

theorem isEmpty_cxPts_of_map {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (g : Y ⟶ X) (hg : g ≫ p = q)
    (h : ∀ σ : k →+* ℂ, IsEmpty (CxPts p σ)) (σ : k →+* ℂ) : IsEmpty (CxPts q σ) :=

  isEmpty_iff.2 fun y => isEmpty_iff.1 (h σ) (PtsOver.map g hg (spMap σ) y)

theorem mixArch_pull_iso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k)
    (hp : IsAmb p) (hq : IsAmb q) (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X) [IsIso g]
    (e : ℕ) (hX : topologicalKrullDim X = (e + 1 : ℕ)) (L : Fin e → HermLB p) (M : HermLB p)
    (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r) :
    mixArch (fun a => (L a).pull g hg) (M.pull g hg)
      (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) =
      mixArch L M hr := by
  have hY : topologicalKrullDim Y = (e + 1 : ℕ) :=
    (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso g)).isHomeomorph).trans hX
  have hg' : inv g ≫ q = p := by rw [← hg, IsIso.inv_hom_id_assoc]
  by_cases hp0 : ∀ σ : k →+* ℂ, IsEmpty (CxPts p σ)
  · rw [(GlobalTheory.T.mixedArch_restricted_eq_zero_of_no_complexPoints k X p hp0 e L M).1 r hr]
    exact (GlobalTheory.T.mixedArch_restricted_eq_zero_of_no_complexPoints k Y q (isEmpty_cxPts_of_map g hg hp0) e _ _).1 _ _
  by_cases hq0 : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)
  · exact absurd (isEmpty_cxPts_of_map (inv g) hg' hq0) hp0
  obtain ⟨e₁, he₁, hXa⟩ := (GlobalTheory.T.projArithAmbient_vertical_or_arithmeticVariety k X p hp (e + 1) hX).resolve_left fun ⟨_, _, _, h⟩ => hp0 h
  obtain ⟨e₂, he₂, hYa⟩ := (GlobalTheory.T.projArithAmbient_vertical_or_arithmeticVariety k Y q hq (e + 1) hY).resolve_left fun ⟨_, _, _, h⟩ => hq0 h
  obtain rfl : e₁ = e := by omega
  obtain rfl : e₂ = e₁ := by omega
  unfold mixArch
  congr 2
  funext n
  have h₁ : (comb (fun a => (L a).pull g hg) n).archInt (M.pull g hg) e₂
      (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) =
      ((comb L n).pull g hg).archInt (M.pull g hg) e₂
      (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) := by
    simp only [HermLB.archInt, (isometric_comb_pull L n g hg).chernInt_eq]
  rw [h₁, GlobalTheory.T.archimedeanIntegral_pull_mul_degree k X Y p q e₂ hXa hYa g hg hη (by rw [Published.residueDegree_of_isClosedImmersion]; exact one_ne_zero),
    Published.residueDegree_of_isClosedImmersion, Nat.cast_one, one_mul]

theorem mult_pull_iso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) ⤳ genericPoint X) [IsIso g]
    (M : HermLB p) {r : M.B.ι → X.functionFieldˣ} (hr : IsRatSec M.B r) (y : Y) :
    ((M.pull g hg).div (MultPull.isRatSec_pull_map g hη hr)).mult y = (M.div hr).mult (g y) := by
  change (divOfRatSec (LB.isLB_pull M.isLB g) (MultPull.isRatSec_pull_map g hη hr)).mult y =
    (divOfRatSec M.isLB hr).mult (g y)
  obtain ⟨c, hc⟩ := exists_chart (LB.isLB_pull M.isLB g) y
  have hc' : g y ∈ M.B.U (c PUnit.unit) := Set.mem_iInter.1 hc PUnit.unit
  rw [((presents_divOfRatSec _ _).isEqn c y hc).mult_eq,
    ((presents_divOfRatSec M.isLB hr).isEqn _ _ hc').mult_eq]
  exact ord_fnMap g hη y _

theorem transport : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), IsIso g → ∀ e : ℕ, topologicalKrullDim X = (e + 1 : ℕ) → ∀ (h : X → ℝ) (L : Fin e → HermLB p) (M : HermLB p) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), recVal (fun w => h (g w)) (fun a => (L a).pull g hg) (M.pull g hg) (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) = recVal h L M hr := by
  intro k _ X Y _ _ _ _ p q hp hq g hg hη _ e hX h L M r hr
  unfold recVal
  rw [mixArch_pull_iso p q hp hq g hg hη e hX L M r hr]
  congr 1
  refine (finsum_congr fun z => ?_).trans
    (finsum_comp_equiv (Scheme.homeoOfIso (asIso g)).toEquiv (f := fun x => ((M.div hr).mult x : ℝ) * h x))
  exact congrArg (fun n : ℤ => (n : ℝ) * h (g z)) (mult_pull_iso g hg _ M hr z)

end GlobalTheory.MixHt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveHeightFormulaRhsTransportIsoStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.inductive_height_formula_rhs_transport_iso : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), IsIso g → ∀ e : ℕ, topologicalKrullDim X = (e + 1 : ℕ) → ∀ (h : X → ℝ) (L : Fin e → HermLB p) (M : HermLB p) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), recVal (fun w => h (g w)) (fun a => (L a).pull g hg) (M.pull g hg) (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) = recVal h L M hr := by
  exact @GlobalTheory.MixHt.transport
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightRecursiveValueWellDefined

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.StepVal

variable {k : Type} [CommRing k]

theorem isometric_pull_pull' {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    {s : Z ⟶ Sp k} (L : HermLB p) (f : Y ⟶ X) (hf : f ≫ p = q) (g : Z ⟶ Y) (hg : g ≫ q = s) (c : Z ⟶ X)
    (hc : c ≫ p = s) (e : g ≫ f = c) : ((L.pull f hf).pull g hg).Isometric (L.pull c hc) := by
  subst e
  have R := L.refines_pull_pull f hf g hg hc
  exact HermLB.isometric_of_chart _ R.le (fun x => R.g Z (𝟙 Z) x) fun σ c y hy =>
    ((R.φ σ c y hy).trans (add_zero _)).symm

theorem recVal_congr {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} {e : ℕ}
    {h h' : Y → ℝ} (H : ∀ z : Y, Order.coheight z = 1 → h z = h' z) (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : recVal h L M hr = recVal h' L M hr := by
  unfold recVal
  congr 1
  refine finsum_congr fun z => ?_
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  · rw [H z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)]

theorem dim_of_genericPoint {X Y : Scheme.{0}} [IsIntegral Y] {p : X ⟶ Sp k} (hp : IsAmb p) (i : Y ⟶ X)
    [IsClosedImmersion i] {x : X} {d : ℕ} (hx : HasDim x d) (hg : i (genericPoint Y) = x) :
    topologicalKrullDim Y = d := by
  have H := (GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hp).2.2.2.2
  rw [← H.2 Y d, ← H.1 Y i (genericPoint Y) d, hg]
  exact hx

theorem recVal_indep_section (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ) {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) (hY : topologicalKrullDim Y = (m + 1 : ℕ)) {T}
    (hT : IsMix q m T) (L : Fin m → HermLB q) (N : HermLB q) {r r' : N.B.ι → Y.functionFieldˣ} (hr : IsRatSec N.B r)
    (hr' : IsRatSec N.B r') : recVal (T m L) L N hr = recVal (T m L) L N hr' := by
  cases m with
  | zero =>
    have H : ∀ z : Y, Order.coheight z = 1 → T 0 L z = Real.log (Nat.card (Y.residueField z)) := fun z hz =>
      hT.zero L z (((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq 0 hY).1 z).1 hz)
    rw [recVal_congr H, recVal_congr H]
    exact GlobalTheory.T.arithmetic_curve_degree_independent_of_section k Y q hq hY N L r hr r' hr'
  | succ e => exact GlobalTheory.T.mixedHeightInduction_independent_of_section hInt hRec k Y q hq e hY T hT N L r hr r' hr'

theorem recVal_indep (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ) {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) (hY : topologicalKrullDim Y = (m + 1 : ℕ)) {T}
    (hT : IsMix q m T) (L L' : Fin m → HermLB q) (hL : ∀ a, (L a).Isometric (L' a)) (M M' : HermLB q)
    (hM : M.Isometric M') {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) {r' : M'.B.ι → Y.functionFieldˣ}
    (hr' : IsRatSec M'.B r') : recVal (T m L) L M hr = recVal (T m L') L' M' hr' := by
  have H := GlobalTheory.T.mixedHeight_inductive_rhs_symm_isometry_invariant hInt k Y q hq m hY T hT M r hr
  obtain ⟨r₃, hr₃, e₃⟩ := H.2.2 L' M' hM
  rw [H.1 L L' hL, ← e₃]
  exact recVal_indep_section hInt hRec m hq hY hT L' M' hr₃ hr'

end GlobalTheory.MixHt.StepVal

namespace GlobalTheory.MixHt.StepVal

variable {k : Type} [CommRing k]

theorem recVal_eq_of_same (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ)
    (hall : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T)
    {X : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsAmb p) {T} (hT : IsMix p m T) {x : X} (hx : HasDim x (m + 1))
    (M : HermLB p) (L : Fin m → HermLB p) {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k}
    (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ p = q) (hg : i (genericPoint Y) = x)
    (M' M'' : HermLB q) (L' L'' : Fin m → HermLB q) (hM' : (M.pull i hi).Isometric M')
    (hM'' : (M.pull i hi).Isometric M'') (hL' : ∀ a, ((L a).pull i hi).Isometric (L' a))
    (hL'' : ∀ a, ((L a).pull i hi).Isometric (L'' a)) {r' : M'.B.ι → Y.functionFieldˣ} (hr' : IsRatSec M'.B r')
    {r'' : M''.B.ι → Y.functionFieldˣ} (hr'' : IsRatSec M''.B r'') :
    recVal (fun z => T m L (i z)) L' M' hr' = recVal (fun z => T m L (i z)) L'' M'' hr'' := by
  have hq : IsAmb q := by subst hi; exact hp.sub i
  have hY := dim_of_genericPoint hp i hx hg
  obtain ⟨T', hT'⟩ := hall k Y q hq
  have E : ∀ N : Fin m → HermLB q, (∀ a, ((L a).pull i hi).Isometric (N a)) → ∀ z : Y, Order.coheight z = 1 →
      T m L (i z) = T' m N z := fun N hN z hz =>
    GlobalTheory.T.mixedHeight_unique_restrict_closedSubscheme k X Y p q hp i hi m m T T' hT hT' m le_rfl le_rfl L N hN z
      (((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq m hY).1 z).1 hz)
  rw [recVal_congr (E L' hL'), recVal_congr (E L'' hL'')]
  exact recVal_indep hInt hRec m hq hY hT' L' L'' (fun a => (hL' a).symm.trans (hL'' a)) M' M''
    (hM'.symm.trans hM'') hr' hr''

theorem recVal_eq_of_two (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ)
    (hall : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T)
    {X : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsAmb p) {T} (hT : IsMix p m T) {x : X} (hx : HasDim x (m + 1))
    (M : HermLB p) (L : Fin m → HermLB p)
    {Y₁ : Scheme.{0}} [IsIntegral Y₁] [IsLocallyNoetherian Y₁] {q₁ : Y₁ ⟶ Sp k}
    (i₁ : Y₁ ⟶ X) [IsClosedImmersion i₁] (hi₁ : i₁ ≫ p = q₁) (hg₁ : i₁ (genericPoint Y₁) = x)
    (M₁ : HermLB q₁) (L₁ : Fin m → HermLB q₁) (hM₁ : (M.pull i₁ hi₁).Isometric M₁)
    (hL₁ : ∀ a, ((L a).pull i₁ hi₁).Isometric (L₁ a)) {r₁ : M₁.B.ι → Y₁.functionFieldˣ} (hr₁ : IsRatSec M₁.B r₁)
    {Y₂ : Scheme.{0}} [IsIntegral Y₂] [IsLocallyNoetherian Y₂] {q₂ : Y₂ ⟶ Sp k}
    (i₂ : Y₂ ⟶ X) [IsClosedImmersion i₂] (hi₂ : i₂ ≫ p = q₂) (hg₂ : i₂ (genericPoint Y₂) = x)
    (M₂ : HermLB q₂) (L₂ : Fin m → HermLB q₂) (hM₂ : (M.pull i₂ hi₂).Isometric M₂)
    (hL₂ : ∀ a, ((L a).pull i₂ hi₂).Isometric (L₂ a)) {r₂ : M₂.B.ι → Y₂.functionFieldˣ} (hr₂ : IsRatSec M₂.B r₂) :
    recVal (fun z => T m L (i₁ z)) L₁ M₁ hr₁ = recVal (fun z => T m L (i₂ z)) L₂ M₂ hr₂ := by
  obtain ⟨g, hiso, hgi, hη⟩ := GlobalTheory.T.exists_iso_closedImmersions_same_genericPoint X Y₁ Y₂ i₁ i₂ (hg₁.trans hg₂.symm)
  have hgq : g ≫ q₁ = q₂ := by rw [← hi₁, ← hi₂, ← Category.assoc, hgi]
  have hq₁ : IsAmb q₁ := by subst hi₁; exact hp.sub i₁
  have hq₂ : IsAmb q₂ := by subst hi₂; exact hp.sub i₂
  have hY₁ := dim_of_genericPoint hp i₁ hx hg₁
  have tr := GlobalTheory.T.inductive_height_formula_rhs_transport_iso k Y₁ Y₂ q₁ q₂ hq₁ hq₂ g hgq hη hiso m hY₁ (fun z => T m L (i₁ z)) L₁ M₁ r₁ hr₁
  rw [← tr]
  have hfun : (fun w => T m L (i₁ (g w))) = fun w => T m L (i₂ w) := by
    funext w
    rw [← hgi]
    simp
  rw [hfun]
  refine recVal_eq_of_same hInt hRec m hall hp hT hx M L i₂ hi₂ hg₂ _ _ _ _ ?_ hM₂ (fun a => ?_) hL₂ _ hr₂
  · exact (isometric_pull_pull' M i₁ hi₁ g hgq i₂ hi₂ hgi).symm.trans (hM₁.pull g hgq)
  · exact (isometric_pull_pull' (L a) i₁ hi₁ g hgq i₂ hi₂ hgi).symm.trans ((hL₁ a).pull g hgq)

theorem step_val : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k),
    IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ T,
    IsMix p m T → ∀ (x : X), HasDim x (m + 1) → ∀ (M : HermLB p) (L : Fin m → HermLB p), ∃ v : ℝ,
    ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ p = q), i (genericPoint Y) = x → ∀ (M' : HermLB q) (L' : Fin m → HermLB q),
    (M.pull i hi).Isometric M' → (∀ a, ((L a).pull i hi).Isometric (L' a)) →
    ∀ (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r), v = recVal (fun z => T m L (i z)) L' M' hr := by
  intro hInt hRec m hall k _ X p hp T hT x hx M L
  classical
  by_cases H : ∃ v : ℝ, ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (q : Y ⟶ Sp k)
      (i : Y ⟶ X) (_ : IsClosedImmersion i) (hi : i ≫ p = q) (_ : i (genericPoint Y) = x) (M' : HermLB q)
      (L' : Fin m → HermLB q) (_ : (M.pull i hi).Isometric M') (_ : ∀ a, ((L a).pull i hi).Isometric (L' a))
      (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r), v = recVal (fun z => T m L (i z)) L' M' hr
  · obtain ⟨v, Y₁, _, _, q₁, i₁, _, hi₁, hg₁, M₁, L₁, hM₁, hL₁, r₁, hr₁, rfl⟩ := H
    exact ⟨_, fun Y _ _ q i _ hi hg M' L' hM hL r hr =>
      recVal_eq_of_two hInt hRec m hall hp hT hx M L i₁ hi₁ hg₁ M₁ L₁ hM₁ hL₁ hr₁ i hi hg M' L' hM hL hr⟩
  · exact ⟨0, fun Y _ _ q i _ hi hg M' L' hM hL r hr =>
      absurd ⟨_, Y, ‹_›, ‹_›, q, i, ‹_›, hi, hg, M', L', hM, hL, r, hr, rfl⟩ H⟩

end GlobalTheory.MixHt.StepVal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightRecursiveValueWellDefinedStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.mixedHeightRecursiveValue_well_defined : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ T, IsMix p m T → ∀ (x : X), HasDim x (m + 1) → ∀ (M : HermLB p) (L : Fin m → HermLB p), ∃ v : ℝ, ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ p = q), i (genericPoint Y) = x → ∀ (M' : HermLB q) (L' : Fin m → HermLB q), (M.pull i hi).Isometric M' → (∀ a, ((L a).pull i hi).Isometric (L' a)) → ∀ (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r), v = recVal (fun z => T m L (i z)) L' M' hr := by
  first | exact @GlobalTheory.MixHt.StepVal.step_val | exact GlobalTheory.MixHt.StepVal.step_val | (intros; apply GlobalTheory.MixHt.StepVal.step_val <;> assumption)
end
end
