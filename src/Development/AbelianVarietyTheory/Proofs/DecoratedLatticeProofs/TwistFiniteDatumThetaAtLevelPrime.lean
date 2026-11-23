module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTrans
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValDetSubOneLt
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColCond
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiOneEqOneIffColumnConditionStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLevelPrimePhiOneEqOneIffColumnsStatement
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColCond
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCoordinateVectorsChainSpaceSelfDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PutInSplitPlacesDatumProductOnHalf

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasResOfValSubLt

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseFn

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2.DetSpec

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable [StarRing E] {n : ℕ}

variable {hc : Formalism.BasicNotions.CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem fn_eq {p : DecoF E n ST SG Q} {k : GL (Fin n) (AfE F E)} (h : IsPtOf hc k p) (hN : p.deco.1.N = Formalism.L2.Col.stdLat E n) (P : ST)
    (r : Fin n) (hr : r.1 + 1 = n) (c : 𝓞 E)
    (hrow : ∀ i, HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r i)) (if i = r then Ideal.Quotient.mk P.1.asIdeal c else 0))
    (x : Fin n → 𝓞 E) : p.deco.1.f P (fun i => (x i : E)) = Ideal.Quotient.mk P.1.asIdeal (c * x r) := by
  refine HasRes.unique (h.f P _ (hN ▸ (Formalism.L2.Col.mem_stdLat _).2 fun i => ⟨x i, rfl⟩) r hr) ?_
  choose ρ hρ hv using hrow
  refine ⟨∑ i, ρ i * x i, ?_, ?_⟩

  · simp only [map_sum, map_mul, hρ, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

  · simp only [Col2.pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, adAt_inclE]
    rw [← Finset.sum_sub_distrib]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    show Valued.v (_ * algebraMap E (P.1.adicCompletion E) (algebraMap (𝓞 E) E (x i)) - _) < 1
    rw [← _root_.sub_mul, map_mul, valued_algebraMap]
    exact (mul_le_of_le_one_right' (P.1.valuation_le_one (x i))).trans_lt (hv i)

end Loc

end GlobalTheory.BaseFn

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChartDecorationLevelPrimeFunctionalEqConjMul

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

namespace GlobalTheory.PhiOneVal

theorem base_deco_fn : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) (u : B.Word) (a : I.ι)
    (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ i, i ≤ B.R.m → ∀ (β : Ch i) (P : (B.primes X).vT u)
    (x : Formalism.L2.Col.Sp B.fields.E (B.R.N i)), x ∈ Formalism.L2.Col.stdLat B.fields.E (B.R.N i) → ∀ r : Fin (B.R.N i), r.1 + 1 = B.R.N i →
    ∀ c : 𝓞 B.fields.E, algebraMap (𝓞 B.fields.E) B.fields.E c = x r →
      (A.p0 i β).1.1.deco.1.f P x = Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u) * c) := by
  intro B X I l Z u a Ch A hA i hi β P x hx r hr c hc
  choose y hy using (Formalism.L2.Col.mem_stdLat x).1 hx
  have hxy : x = fun j => (y j : B.fields.E) := funext fun j => (hy j).symm
  have hyc : y r = c := NumberField.RingOfIntegers.coe_injective ((hy r).trans hc.symm)
  rw [hxy, ← hyc]
  exact GlobalTheory.BaseFn.fn_eq (hA.base i hi β).1 (hA.base i hi β).2 P r hr _ (fun j => (hA.reads i hi).k_T β P r j hr) y

end GlobalTheory.PhiOneVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChartDecorationLevelPrimeFunctionalEqConjMulStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

theorem _root_.GlobalTheory.T.baseChartDecoration_levelPrimeFunctional_eq_conj_mul : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ i, i ≤ B.R.m → ∀ (β : Ch i) (P : (B.primes X).vT u)
    (x : Formalism.L2.Col.Sp B.fields.E (B.R.N i)), x ∈ Formalism.L2.Col.stdLat B.fields.E (B.R.N i) → ∀ r : Fin (B.R.N i), r.1 + 1 = B.R.N i →
    ∀ c : 𝓞 B.fields.E, algebraMap (𝓞 B.fields.E) B.fields.E c = x r →
      (A.p0 i β).1.1.deco.1.f P x = Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u) * c) := by
  first | exact @GlobalTheory.PhiOneVal.base_deco_fn | exact GlobalTheory.PhiOneVal.base_deco_fn | (intros; apply GlobalTheory.PhiOneVal.base_deco_fn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartBasePointsLevelDatumEqLocalProd

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section

namespace GlobalTheory.PhiOneVal


open Classical in
theorem phiT_base_eq_prod : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ J : List ι, Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ j (hj : j + 1 ≤ B.R.m) (α : Ch j) (γ : Ch (j + 1))
      (z : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E),
      B.embLL (Formalism.L2.Col.phiT _ (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1
          (toHom _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) z)) =
        (J.map fun i => phiOne (Q j i) (Q (j + 1) i) (rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z))))).prod := by
  intro B X I _ _ l Z u a Ch A hA k _ _ _ _ ι p β Q L hS J hJ j hj α γ z
  have hj0 : j ≤ B.R.m := Nat.le_of_succ_le hj
  obtain ⟨⟨e, he⟩, hS2⟩ := hS
  obtain ⟨hLj, hSj⟩ := hS2 j hj0
  obtain ⟨hLj', hSj'⟩ := hS2 (j + 1) hj
  have hG := GlobalTheory.T.phi_one_eq_one_iff_column_condition B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 (B.fields.conjO (X.piT u))
    (A.p0 j α).1.1.deco.2 (A.p0 (j + 1) γ).1.1.deco.2 (hA.base j hj0 α).2 (hA.base (j + 1) hj γ).2
    (fun P x hx r hr c hc => GlobalTheory.T.baseChartDecoration_levelPrimeFunctional_eq_conj_mul I l Z u a Ch A hA j hj0 α P x hx r hr c hc)
    (fun P x hx r hr c hc => GlobalTheory.T.baseChartDecoration_levelPrimeFunctional_eq_conj_mul I l Z u a Ch A hA (j + 1) hj γ P x hx r hr c hc)
    (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)
  have hLoc : ∀ i, (Maps (Q j i) (Q (j + 1) i) (GlobalTheory.FinPl.rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z)))) ↔
      ColCond (e i).1 (B.fields.conjO (X.piT u)) (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)) :=
    fun i => GlobalTheory.T.maps_rd_iff_colCond_toHom (p i) (e i).1 (he i) _ _ (β j i) (β (j + 1) i) (Q j i) (Q (j + 1) i) (L j) (L (j + 1)) _ hLj hLj'
      (hSj i).1 (hSj' i).1 (hSj i).2 (hSj' i).2 z
  have key : (∀ P : (B.primes X).vT u, ColCond P.1 (B.fields.conjO (X.piT u))
      (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)) ↔
      ∀ i ∈ J, Maps (Q j i) (Q (j + 1) i) (GlobalTheory.FinPl.rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z)))) := by
    refine ⟨fun h i _ => (hLoc i).2 (h (e i)), fun h P => ?_⟩
    obtain ⟨i, rfl⟩ := e.surjective P
    exact (hLoc i).1 (h i (hJ.all i))
  have hprod : ∀ (J' : List ι) (c : ι → Prop), (J'.map fun i => (if c i then (1 : ℂ) else 0)).prod =
      if ∀ i ∈ J', c i then 1 else 0 := by
    intro J' c
    induction J' with
    | nil => simp
    | cons i J' ih =>
      rw [List.map_cons, List.prod_cons, ih]
      by_cases h : c i <;> simp [h]
  have hv : ∀ x, Formalism.L2.Col.phiT B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 x = 1 ∨
      Formalism.L2.Col.phiT B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 x = 0 := by
    intro x
    unfold Formalism.L2.Col.phiT
    split_ifs <;> simp
  simp only [phiOne]
  rw [hprod]
  split_ifs with hc
  · rw [hG.2 (key.2 hc), map_one]
  · rcases hv (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z) with h1 | h0
    · exact absurd (key.1 (hG.1 h1)) hc
    · rw [h0, map_zero]

end GlobalTheory.PhiOneVal

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartBasePointsLevelDatumEqLocalProdStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chartBasePoints_levelDatum_eq_local_prod : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ J : List ι, Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ j (hj : j + 1 ≤ B.R.m) (α : Ch j) (γ : Ch (j + 1))
      (z : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E),
      B.embLL (Formalism.L2.Col.phiT _ (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1
          (toHom _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) z)) =
        (J.map fun i => phiOne (Q j i) (Q (j + 1) i) (rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z))))).prod := by
  first | exact @GlobalTheory.PhiOneVal.phiT_base_eq_prod | exact GlobalTheory.PhiOneVal.phiT_base_eq_prod | (intros; apply GlobalTheory.PhiOneVal.phiT_base_eq_prod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCoordinateVectorsChainSpaceSelfDualStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_coordinate_vectors_chain_space_selfDual : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (j : ℕ), j ≤ B.R.m →
    ∀ L : Lat ((I.rec7 l Z).sp.X j), (∀ z, z ∈ L ↔ z ∈ intVec (I.rec7 l Z) _) → IsSelfDualC ((I.rec7 l Z).sp.X j) L := by
  first | exact @GlobalTheory.AdForm.intVec_isSelfDualC | exact GlobalTheory.AdForm.intVec_isSelfDualC | (intros; apply GlobalTheory.AdForm.intVec_isSelfDualC <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PutInSplitPlacesDatumProductOnHalfStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.putInSplitPlaces_datum_product_on_half : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt D k) (J : List ι), Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T),
    IsSelfDualC S LS → IsSelfDualC T LT → (∀ z, z ∈ LS ↔ z ∈ intVec D S.rank) → (∀ z, z ∈ LT ↔ z ∈ intVec D T.rank) →
    ∀ (Pset : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e Pset →
    (∃ eq : ι ≃ Pset, ∀ i, Formalism.L2.NTheta.IsIdemAt (p i).e (eq i).1) →
    ∀ (Ψ : ι → Matrix n n' k → ℂ) (f f' : WO S T → ℂ), IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (stdHom S T) f →
    OverAll ψ α β LS LT Ψ J f f' →
    IsRatDatum ψ S T e (fun γ => (J.map fun i => Ψ i (rd (α i) (β i) (γ.map (incA D)))).prod) f f' := by
  first | exact @GlobalTheory.FinPl.PutIn.ratDatum_of_overAll | exact GlobalTheory.FinPl.PutIn.ratDatum_of_overAll | (intros; apply GlobalTheory.FinPl.PutIn.ratDatum_of_overAll <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistFiniteDatumThetaAtLevelPrime

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem twVec' : TwVec' := by
  intro B X I hOk hPins l Z u a Ch A hA ψ θ x vac c₀ hX k _ _ _ _ ι p β Q hStd J hPl j hj α γ cT hReps e he
  have hjm : j ≤ B.R.m := Nat.le_of_succ_le hj
  have hL0 : ∀ z, z ∈ (x j).L ↔ z ∈ intVec (I.rec7 l Z) _ := (hX.xs j hjm).2.2
  have hL1 : ∀ z, z ∈ (x (j + 1)).L ↔ z ∈ intVec (I.rec7 l Z) _ := (hX.xs (j + 1) hj).2.2
  have hvac := hX.vc j (by omega)
  have hS0 : ((x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) = intVec (I.rec7 l Z) _ := by ext z; exact hL0 z
  have hS1 : ((x (j + 1)).L : Set (Fin ((I.rec7 l Z).sp.X (j + 1)).rank → (I.rec7 l Z).host.E)) = intVec (I.rec7 l Z) _ := by ext z; exact hL1 z
  have hV : Vac ψ _ _ (x j).L (x (j + 1)).L (fun v => ∃ i, v = (p i).v) (vac j) := by
    refine ⟨hvac.2.theta, ?_⟩
    have hle : latO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) ((x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) ((x (j + 1)).L : Set (Fin ((I.rec7 l Z).sp.X (j + 1)).rank → (I.rec7 l Z).host.E)) (fun v => ∃ i, v = (p i).v) ≤ stdHom _ _ := by
      rw [hS0, hS1]
      apply AddSubgroup.closure_mono
      rintro w ⟨a, ha, -, rest⟩
      exact ⟨a, ha, fun _ h => absurd trivial h, rest⟩
    exact ⟨fun u hu => hvac.2.lat.1 u (hle hu), fun e' he' u hu hh => hvac.2.lat.2 e' he' u (hle hu) hh⟩
  have hO := hReps.2 (vac j) hV
  obtain ⟨eq, heq⟩ := hStd.1
  have hF := GlobalTheory.T.putInSplitPlaces_datum_product_on_half (I.rec7 l Z) k ι p J hPl _ _ ψ hX.std _ _ (β j) (β (j + 1)) (x j).L (x (j + 1)).L
    (GlobalTheory.T.integral_coordinate_vectors_chain_space_selfDual I hOk l Z j hjm _ hL0) (GlobalTheory.T.integral_coordinate_vectors_chain_space_selfDual I hOk l Z (j + 1) hj _ hL1) hL0 hL1 _ e he ⟨eq, heq⟩ _ (vac j) _ hvac.2.theta hvac.2.lat hO
  have hval := GlobalTheory.T.chartBasePoints_levelDatum_eq_local_prod I hOk hPins l Z u a Ch A hA k ι p β Q _ hStd J hPl j hj α γ
  convert hF using 2 with z
  exact hval z

end GlobalTheory.AdForm

end
end
end
