module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartSingleton
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimClosureOfCoheightField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionCycleFormulaProjective
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaArithmeticCurveRationalFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithAmbientVerticalOrArithmeticVarietyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalDivisorDegreeZeroFiniteFieldCurve

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PrincDegZero

theorem log_card_eq (κ : Type) [Field κ] [Finite κ] (V : Type) [AddCommGroup V] [Module κ V] :
    Real.log (Nat.card V) = Module.finrank κ V * Real.log (Nat.card κ) := by
  by_cases h : Module.Finite κ V
  · have : Finite V := Module.finite_of_finite κ
    rw [Module.natCard_eq_pow_finrank (K := κ)]
    push_cast
    rw [Real.log_pow]
  · rw [Module.finrank_of_not_finite h]
    have : Infinite V := by
      by_contra h'
      have := not_infinite_iff_finite.1 h'
      exact h (Module.Finite.of_finite)
    simp [Nat.card_eq_zero_of_infinite]

theorem log_card_residueField {κ : Type} [Field κ] [Finite κ] {Y : Scheme.{0}} [IsIntegral Y] [Algebra κ Γ(Y, ⊤)]
    [LocallyOfFiniteType (strHom κ (X := Y))] (hd : topologicalKrullDim Y = (0 + 1 : ℕ)) {z : Y}
    (hz : Order.coheight z = 1) :
    Real.log (Nat.card (Y.residueField z)) =
      (interNumRed κ (⟨closure {z}, isClosed_closure⟩ : Closeds Y) (Fin.elim0 : Fin 0 → LB Y) : ℝ) *
        Real.log (Nat.card κ) := by
  have hdim := VdmRec.CutSec.dim_closure_of_coheight_field (strHom κ Y) hd hz
  obtain ⟨W, j, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
  have hrange : Set.range j = closure {j (genericPoint W)} := by
    rw [← Set.image_singleton, j.isClosedEmbedding.closure_image_eq, (genericPoint_spec _).def, Set.image_univ]
  letI := algebraΓAlong κ j
  have hW : topologicalKrullDim W = (0 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange).symm.trans hdim
  rw [InterModel.interNumRed_eq_interNumOn _ j _ hrange,
    interNumOn_eq_interNum_pull (appTop_algebraMap_along κ j) (fun i => i.elim0), interNum_of_isEmpty]
  have hu (w : W) : w = genericPoint W := by
    have := Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (IrreducibleCloseds W) ≤ 0
      from hW.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ W, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec W)
  have hZ : ({genericPoint W} : Set W) = Set.univ := Set.eq_univ_of_forall hu
  have hc : IsClosed ({genericPoint W} : Set W) := hZ ▸ isClosed_univ
  have := isClosed_singleton_iff_isClosedImmersion.1 hc
  have : Surjective (W.fromSpecResidueField (genericPoint W)) :=
    ⟨fun w => ⟨IsLocalRing.closedPoint _, (hu _).trans (hu w).symm⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (W.fromSpecResidueField (genericPoint W))
  have : IsAffine W := .of_isIso (inv (W.fromSpecResidueField (genericPoint W)))
  have : IsIso (W.fromSpecResidueField (genericPoint W)).appTop := inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))
  have b₁ : Function.Bijective (j.residueFieldMap (genericPoint W)) := by
    refine ⟨RingHom.injective _, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := W.residue_surjective _ a
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective _ a
    exact ⟨Y.residue _ b, by rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩
  have b₂ : Function.Bijective ((W.fromSpecResidueField (genericPoint W)).appTop ≫
      (Scheme.ΓSpecIso (W.residueField (genericPoint W))).hom) := ConcreteCategory.bijective_of_isIso _
  have e : Γ(W, ⊤) ≃ Y.residueField (j (genericPoint W)) :=
    (Equiv.ofBijective _ b₂).trans (Equiv.ofBijective _ b₁).symm
  rw [← Nat.card_congr e, chi_structureModule_of_isAffine, log_card_eq κ]
  push_cast
  ring

end GlobalTheory.PrincDegZero

namespace GlobalTheory.PrincDegZero

theorem finsum_ord_mul_log_card_eq_zero : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → topologicalKrullDim Y = (1 : ℕ) → ∀ (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) Γ(Y, ⊤)] (f : Y.functionField), f ≠ 0 → ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Y.residueField z)) = 0 := by
  intro k _ Y _ _ q hA hd l _ _ f hf
  have : Module.Finite ℤ k := hA.finite
  have : AlgebraicGeometry.IsNoetherian Y := hA.isNoetherian
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨hpr, H, hH⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hA.isProjOver
  have hp : IsProjOver (strHom (ZMod l) (X := Y)) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom (ZMod l) Y ≫ spMap (Int.castRingHom (ZMod l)) = q ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom (ZMod l) Y ≫ spMap (Int.castRingHom (ZMod l))) := by rw [e]; infer_instance
    have : IsProper (strHom (ZMod l) (X := Y)) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod l)))
    exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨this, H, hH⟩
  have : IsProper (strHom (ZMod l) (X := Y)) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have hd' : topologicalKrullDim Y = (0 + 1 : ℕ) := hd
  let r : (LB.triv Y).ι → Y.functionFieldˣ := fun _ => Units.mk0 f hf
  have hr : IsRatSec (LB.triv Y) r := fun _ _ h => by simp [r]
  have hM := LB.isLB_triv Y
  have key := GlobalTheory.ratSec_cycle_formula (ZMod l) Y hp 0 hd.le (LB.triv Y) hM Fin.elim0 (fun i => i.elim0) r hr
  rw [interNum_eq_zero_of_cls_eq_zero (ZMod l) _ (isLB_cons hM fun i => i.elim0) 0 (cls_triv _)] at key
  have hm (z : Y) : (divOfRatSec hM hr).mult z = Scheme.ord f z :=
    ((presents_divOfRatSec hM hr).isEqn PUnit.unit z trivial).mult_eq
  have hfin : Function.HasFiniteSupport fun w => (divOfRatSec hM hr).mult w *
      interNumRed (ZMod l) (⟨closure {w}, isClosed_closure⟩ : Closeds _) (Fin.elim0 : Fin 0 → LB Y) :=
    (CartierDiv.finite_support_mult _).subset (Function.support_mul_subset_left _ _)
  have em := (AddMonoidHom.mulRight (Real.log (Nat.card (ZMod l)))).comp (Int.castAddHom ℝ) |>.map_finsum hfin
  rw [← key] at em
  simp only [map_zero] at em
  refine (finsum_congr fun z => ?_).trans em.symm
  change (Scheme.ord f z : ℝ) * _ = (((divOfRatSec hM hr).mult z * _ : ℤ) : ℝ) * _
  rw [hm]
  by_cases hz : Scheme.ord f z = 0
  · simp [hz]
  have hc : Order.coheight z = 1 := by
    by_contra h
    exact hz (Scheme.ord_eq_zero_of_coheight_neq_one h f)
  rw [Int.cast_mul, mul_assoc, log_card_residueField (κ := ZMod l) hd' hc]

end GlobalTheory.PrincDegZero
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalDivisorDegreeZeroFiniteFieldCurveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.principalDivisor_degree_zero_finiteField_curve : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → topologicalKrullDim Y = (1 : ℕ) → ∀ (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) Γ(Y, ⊤)] (f : Y.functionField), f ≠ 0 → ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Y.residueField z)) = 0 := by
  first | exact @GlobalTheory.PrincDegZero.finsum_ord_mul_log_card_eq_zero | exact GlobalTheory.PrincDegZero.finsum_ord_mul_log_card_eq_zero | (intros; apply GlobalTheory.PrincDegZero.finsum_ord_mul_log_card_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveDegreeIndependentOfSection

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveIndep

variable {Y : Scheme.{0}} [IsIntegral Y] {L : LB Y}

theorem exists_ratio (hL : L.IsLB) {r r' : L.ι → Y.functionFieldˣ} (hr : IsRatSec L r)
    (hr' : IsRatSec L r') : ∃ f : Y.functionFieldˣ, ∀ i, genericPoint Y ∈ L.U i → r' i = r i * f := by
  obtain ⟨i₀, h₀⟩ := exists_chart hL (genericPoint Y)
  refine ⟨(r i₀)⁻¹ * r' i₀, fun i hi => Units.ext ?_⟩
  have e := hr i i₀ ⟨hi, h₀⟩
  have e' := hr' i i₀ ⟨hi, h₀⟩
  have h0 : (r i₀ : Y.functionField) ≠ 0 := (r i₀).ne_zero
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [e', e]
  field_simp

theorem div_eq_add_principal (hL : L.IsLB) {r r' : L.ι → Y.functionFieldˣ} (hr : IsRatSec L r)
    (hr' : IsRatSec L r') (f : Y.functionFieldˣ) (hf : ∀ i, genericPoint Y ∈ L.U i → r' i = r i * f) :
    divOfRatSec hL hr' = divOfRatSec hL hr + CartierDiv.principal f :=
  (presents_divOfRatSec hL hr').unique ⟨hL, hr', fun i x hx => by
    rw [hf i (gen_mem hx)]
    exact ((presents_divOfRatSec hL hr).add_principal f).isEqn i x hx⟩

theorem mult_eq_add_ord [IsLocallyNoetherian Y] (hL : L.IsLB) {r r' : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) (hr' : IsRatSec L r') (f : Y.functionFieldˣ)
    (hf : ∀ i, genericPoint Y ∈ L.U i → r' i = r i * f) (z : Y) :
    (divOfRatSec hL hr').mult z = (divOfRatSec hL hr).mult z + Scheme.ord (f : Y.functionField) z := by
  rw [div_eq_add_principal hL hr hr' f hf, CartierDiv.mult_add,
    (CartierDiv.isEqn_principal f z).mult_eq]

end GlobalTheory.CurveIndep

namespace GlobalTheory.CurveIndep


open Classical in
theorem mixArch_zero {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}
    (L : Fin 0 → HermLB q) (N : HermLB q) {r : N.B.ι → Y.functionFieldˣ} (hr : IsRatSec N.B r) :
    mixArch L N hr = (HermLB.triv q).archInt N 0 hr := by
  have h (n : Fin 0 → ℤ) : (comb L n).archInt N 0 hr = (HermLB.triv q).archInt N 0 hr := by
    have e : comb L n = HermLB.triv q := by simp [comb]
    rw [e]
  have e (S : Finset (Fin 0)) : S.card = 0 := by simp [Subsingleton.elim S ∅]
  simp [mixArch, FibreProj.pol, h, e]

theorem archInt_eq_zero {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (hq : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) (L M : HermLB q) (e : ℕ)
    {r : M.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) : L.archInt M e hr = 0 := by
  unfold HermLB.archInt
  refine finsum_eq_zero_of_forall_eq_zero fun σ => ?_
  haveI := hq σ
  simp [Weight.chernInt, MeasureTheory.integral_of_isEmpty]

theorem main : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → topologicalKrullDim Y = (0 + 1 : ℕ) → ∀ (N : HermLB q) (L : Fin 0 → HermLB q) (r : N.B.ι → Y.functionFieldˣ) (hr : IsRatSec N.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'), recVal (fun z => Real.log (Nat.card (Y.residueField z))) L N hr = recVal (fun z => Real.log (Nat.card (Y.residueField z))) L N hr' := by
  intro k _ Y _ _ q hA hd N L r hr r' hr'
  obtain ⟨f, hf⟩ := exists_ratio N.isLB hr hr'
  have := hA.isNoetherian
  set c : Y → ℝ := fun z => Real.log (Nat.card (Y.residueField z)) with hc
  have hfin (D : CartierDiv Y) : (Function.support fun z => (D.mult z : ℝ) * c z).Finite :=
    (CartierDiv.finite_support_mult D).subset fun z hz h0 => hz (by simp [h0])
  have hord (z : Y) : Scheme.ord (f : Y.functionField) z = (CartierDiv.principal f).mult z :=
    ((CartierDiv.isEqn_principal f z).mult_eq).symm
  have hsum : ∑ᶠ z, ((N.div hr').mult z : ℝ) * c z =
      ∑ᶠ z, ((N.div hr).mult z : ℝ) * c z + ∑ᶠ z, (Scheme.ord (f : Y.functionField) z : ℝ) * c z := by
    simp_rw [hord]
    rw [← finsum_add_distrib (hfin _) (hfin _)]
    refine finsum_congr fun z => ?_
    rw [HermLB.div, HermLB.div, mult_eq_add_ord N.isLB hr hr' f hf z, hord]
    push_cast
    ring
  unfold recVal
  rw [hsum, mixArch_zero, mixArch_zero]
  rcases GlobalTheory.T.projArithAmbient_vertical_or_arithmeticVariety k Y q hA (0 + 1) hd with ⟨l, hl, ⟨alg⟩, hemp⟩ | ⟨e, he, hq⟩
  · have h0 : ∑ᶠ z, (Scheme.ord (f : Y.functionField) z : ℝ) * c z = 0 :=
      @GlobalTheory.T.principalDivisor_degree_zero_finiteField_curve k _ Y _ _ q hA hd l hl alg (f : Y.functionField) f.ne_zero
    rw [h0, archInt_eq_zero hemp, archInt_eq_zero hemp]
    ring
  · obtain rfl : e = 0 := by omega
    have := hq.finite_emb
    rw [GlobalTheory.ArchDimZero.main k Y q hq N (HermLB.triv q) r hr,
      GlobalTheory.ArchDimZero.main k Y q hq N (HermLB.triv q) r' hr',
      GlobalTheory.T.productFormula_arithmeticCurve_rationalFunction k Y q hq (f : Y.functionField) f.ne_zero]
    have hlog (σ : k →+* ℂ) (y : CxPts q σ) : logNorm (N.φ σ) r' y =
        Real.log ‖ratVal (f : Y.functionField) y‖ + logNorm (N.φ σ) r y := by
      have hy := GlobalTheory.TwistTop.under_eq_genericPoint hq y
      have hreg (g : Y.functionField) : RegAt (under y) g := by
        rw [hy]; exact regAt_genericPoint g
      have hunit (g : Y.functionFieldˣ) : UnitAt (under y) (g : Y.functionField) := by
        rw [hy]; exact unitAt_genericPoint g.ne_zero
      have hi : genericPoint Y ∈ N.B.U (pick (N.φ σ).isLB y) :=
        gen_mem (mem_ptsIn.1 (mem_pick (N.φ σ).isLB y))
      simp only [logNorm]
      rw [hf _ hi, Units.val_mul, ratVal_mul (hreg _) (hreg _), norm_mul,
        Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero (hunit _)))
          (norm_ne_zero_iff.2 (ratVal_ne_zero (hunit f)))]
      ring
    have hσ (σ : k →+* ℂ) : ∑ᶠ y : CxPts q σ, logNorm (N.φ σ) r' y =
        ∑ᶠ y : CxPts q σ, Real.log ‖ratVal (f : Y.functionField) y‖ + ∑ᶠ y : CxPts q σ, logNorm (N.φ σ) r y := by
      have := GlobalTheory.ArchDimZero.finite_cxPts hq σ
      simp_rw [hlog σ]
      exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)
    simp_rw [hσ]
    rw [finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
    ring

end GlobalTheory.CurveIndep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveDegreeIndependentOfSectionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.arithmetic_curve_degree_independent_of_section : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → topologicalKrullDim Y = (0 + 1 : ℕ) → ∀ (N : HermLB q) (L : Fin 0 → HermLB q) (r : N.B.ι → Y.functionFieldˣ) (hr : IsRatSec N.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'), recVal (fun z => Real.log (Nat.card (Y.residueField z))) L N hr = recVal (fun z => Real.log (Nat.card (Y.residueField z))) L N hr' := by
  first | exact @GlobalTheory.CurveIndep.main | exact GlobalTheory.CurveIndep.main | (intros; apply GlobalTheory.CurveIndep.main <;> assumption)
end
end
