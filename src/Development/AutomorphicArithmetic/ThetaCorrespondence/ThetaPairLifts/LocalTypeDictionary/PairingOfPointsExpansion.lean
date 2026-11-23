module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSummandEmbeddingHom
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMeasDefOfIsTermVol
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedKernelExpansionSumLevelInvariantStatement
public import Development.AutomorphicArithmetic.LocalEmbeddings.JetsGrid
public import Development.AutomorphicArithmetic.LocalEmbeddings.JetsTest
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridRowLevelZeroInfUnitaryEqDatumLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.VertexPairPointsTransformationLaw
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
public import Development.AutomorphicArithmetic.LocalEmbeddings.JetsChain
public import Development.AutomorphicArithmetic.LocalEmbeddings.JetsGlue

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CastMulUnitaryAdelicGroupOfEq

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowLaw

section Gen
variable {Gg Γg : Type} [Group Gg] [Group Γg] {Wg : Type} [NormedAddCommGroup Wg] [InnerProductSpace ℂ Wg]

theorem adForms_law (ι : Γg →* Gg) (ρ : Γg →* Module.End ℂ Wg) (J : Subgroup Gg) (χ : J →* ℂˣ) {F : Gg → Wg}
    (hF : F ∈ Bridge.AdForms ι ρ J χ) (h : Gg) (k : J) : F (h * k) = (χ k : ℂ) • F h := by
  have e := hF 1 h k
  rwa [map_one, one_mul, map_one, Module.End.one_apply] at e

end Gen

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
  {G : GridData R.toLevCh sc} {W : G.Weil} {U : Set T}

theorem cast_mul_unitaryAdelicGroup_of_eq {X Y : LSp D} (h : X = Y) (a b : GA D X.sp) :
    cast (congrArg (fun X : LSp D => GA D X.sp) h) (a * b) =
      cast (congrArg (fun X : LSp D => GA D X.sp) h) a * cast (congrArg (fun X : LSp D => GA D X.sp) h) b := by
  subst h; rfl

theorem toXf_mul (y k : FinPt G (.grid 0 D.R.m)) : toXf (y * k) = toXf y * toXf k := by
  unfold toXf
  rw [← map_mul, Subgroup.coe_mul]
  exact congrArg _ (cast_mul_unitaryAdelicGroup_of_eq (colY_m R.toLevCh) _ _)

theorem formC_apply (S : SumChoice W U) (t : T) (u : (R.HX t).H) (y : FinPt G (.grid 0 D.R.m)) :
    S.formC t u y = S.co ((R.HX t).e u (toXf y)) := rfl

theorem formC_mul (S : SumChoice W U) (hHX : R.models_HX) (t : T) (u : (R.HX t).H) (y k : FinPt G (.grid 0 D.R.m))
    (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) :
    S.formC t u (y * k) = (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • S.formC t u y := by
  have h : ∀ F, F ∈ LinearMap.range (R.HX t).e → F ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ
      (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ := fun F hF => (hHX t).2.1 ▸ hF
  have e : (R.HX t).e u (toXf y * toXf k) =
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • (R.HX t).e u (toXf y) :=
    adForms_law (Bridge.ratF D.sp.X') _ _ _ (h _ (LinearMap.mem_range_self (R.HX t).e u)) (toXf y) ⟨toXf k, hk⟩
  calc S.formC t u (y * k) = S.co ((R.HX t).e u (toXf (y * k))) := formC_apply S t u (y * k)
    _ = S.co ((R.HX t).e u (toXf y * toXf k)) := congrArg (fun z => S.co ((R.HX t).e u z)) (toXf_mul y k)
    _ = S.co ((((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • (R.HX t).e u (toXf y)) := congrArg S.co e
    _ = (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • S.co ((R.HX t).e u (toXf y)) := S.co.map_smul _ _
    _ = _ := congrArg _ (formC_apply S t u y).symm

end GlobalTheory.FirstRowLaw

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBottomLevelLeFormLevelLargeDepth

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowLevel

theorem finE_cast_mem {D : D7} (X Y : LSp D) (e : X = Y) (K : Subgroup (GL (Fin X.sp.rank) (Lev.EAf D)))
    (K' : Subgroup (GL (Fin Y.sp.rank) (Lev.EAf D))) (h : HEq K K') (g : GA D X.sp) (hg : Lev.finE X.sp g ∈ K) :
    Lev.finE Y.sp (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) g) ∈ K' := by
  subst e
  cases h
  exact hg

theorem toXf_mem_of_is {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) {μ₀ : T} (hL : L.Is μ₀) (t : T) (k : FinPt G (.grid 0 D.R.m))
    (hk : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _)) :
    toXf k ∈ (levEnv D.sp.X' L.βX (L.datXt t)).J := by

  have hU : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _) ⊓ UA D.sp.cm (G.V (.grid 0 D.R.m)).gram :=
    ⟨hk, GlobalTheory.LevSplit.finE_mem_UA _ _⟩
  have hX := finE_cast_mem (columnBlock L D.R.m) ⟨D.sp.X', L.ΛX⟩ (colY_m L) _ _
    (GlobalTheory.T.gridRowLevel_zero_inf_unitary_eq_datumLevel W S hL t (Nat.zero_le _)) k.1 hU
  exact hX

theorem levRow_zero_le : Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
      toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J := by
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _
  exact fun t k hk => toXf_mem_of_is ch.W ch.S.toGridChoice hS.core.lev t k hk

end GlobalTheory.FirstRowLevel

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBottomLevelLeFormLevelLargeDepthStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.gridBottomLevel_le_formLevel_largeDepth : Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
      toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J := by
  first | exact @GlobalTheory.FirstRowLevel.levRow_zero_le | exact GlobalTheory.FirstRowLevel.levRow_zero_le | (intros; apply GlobalTheory.FirstRowLevel.levRow_zero_le <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FirstRowInvariantUnderTwist

section

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FirstRowLaw
section Gen
variable {Gg Γg : Type} [Group Gg] [Group Γg] {Wg : Type} [NormedAddCommGroup Wg] [InnerProductSpace ℂ Wg]
end Gen
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
  {G : GridData R.toLevCh sc} {W : G.Weil} {U : Set T}
theorem first_row_invariant_under_twist : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (u : (R.HX t).H) (v : VV ℂ (wt ch.G (.top 0))) (x : ∀ j, FinPt ch.G (.top j)) (y : ∀ i, FinPt ch.G (.grid i D.R.m))
      (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x (Function.update y 0 (y 0 * k)) v (ch.S.formC t u (y 0 * k)) =
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x y v (ch.S.formC t u (y 0)) := by
  intro hP hS
  obtain ⟨a, h1⟩ := GlobalTheory.T.gridBottomLevel_le_formLevel_largeDepth
  obtain ⟨b, h2⟩ := _root_.GlobalTheory.T.vertex_pair_points_transformation_law hP hS
  refine ⟨max a b, fun ε CF hC => ?_⟩
  obtain ⟨x₁, h1⟩ := h1 ε CF (le_of_max_le_left hC)
  obtain ⟨x₂, h2⟩ := h2 ε CF (le_of_max_le_right hC)
  refine ⟨max x₁ x₂, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc => ?_⟩
  intro t a β hβ τ hτ u v x y k hk0
  have hk := h1 D large₂ e (le_of_max_le_left hx) Γ Pl0 T A Ks R F s ch hi hsc t k hk0
  have hC := h2 D large₂ e (le_of_max_le_right hx) Γ Pl0 T A Ks R F s ch hi hsc t a β hβ τ hτ x y k hk0 hk v
  rw [formC_mul ch.S s.core.models.HX t u (y 0) k hk]
  exact hC _
end GlobalTheory.FirstRowLaw
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PairingOfPointsExpansion

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
section
open GlobalTheory.DefStep GlobalTheory.JetsOne GlobalTheory.ExpansionInvariance
private theorem last_functional_compatible {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T} (hL : L.Is μ0) (Λ : Module.Dual ℂ (VV ℂ (wt G (.top D.R.m))))
    (Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))) :
    ∃ (c : ℂ) (s : GA D (G.V (.grid D.R.m D.R.m)) →* GA D (G.V (.top D.R.m))), (∀ h, stabilizerEmbedding G.sp.topDec h = s h) ∧
      LastOK (realAct W.θ S.N.fr (.top D.R.m)) Λ (realAct W.θ S.N.fr (.grid D.R.m D.R.m)) Λ' s (finEmb G.sp.topDec)
        (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid D.R.m D.R.m))
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hdef := GlobalTheory.TopIntegral.isDefinite_last G
  haveI : CompactSpace (GinfC (G.V (.grid D.R.m D.R.m))) := isCompact_iff_compactSpace.1 (Eqv.isCompact_GinfC hdef.1 hdef.2)
  obtain ⟨κ₀, k1, k2⟩ := exists_haar _ hdef
  obtain ⟨c, hc⟩ := GlobalTheory.TopIntegral.real_average W.θ_is S.N Λ Λ' κ₀
  obtain ⟨s, h1, h2, h3⟩ := GlobalTheory.TopIntegral.exists_orthogonal_summand_embedding_hom G.sp.topDec
  refine ⟨c, s, h2, hdef, posDef_grid hL le_rfl, fun g hg => realAct_fin _ _ _ hg, fun g hg => realAct_fin _ _ _ hg, h1, h3,
    fun z => (h2 _).symm.trans (GlobalTheory.RealType.Emb_fin _ z), fun k hk => h2 k ▸ GlobalTheory.RealType.Emb_mem_inf _ hk,
    fun u u' => ?_, fun κ a1 a2 u u' => ?_⟩
  · simp only [← h2]
    exact (GlobalTheory.TopIntegral.continuous_integrand W.θ_is S.N Λ Λ' u u').comp continuous_subtype_val
  · obtain rfl : κ = κ₀ := Measure.isHaarMeasure_eq_of_isProbabilityMeasure κ κ₀
    simp only [← h2]
    exact hc u u'
private theorem pairing_of_points_expansion {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (c : ℂ) (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0)))
    (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))) (X : ∀ j, FinPt G (.top j))
    (Y : ∀ i, FinPt G (.grid i D.R.m)) :
    c * pairPts S τ X Y (Ψ (X 0)) (F (Y 0)) = τ.sum fun d a => a *
      GlobalTheory.JetsOne.pairP (V := fun j => G.V (.top j)) (V' := fun j => G.V (.grid j D.R.m)) (Mo := fun j => VV ℂ (wt G (.top j)))
        (Mo' := fun j => VV ℂ (wt G (.grid j D.R.m))) (colComp S d) (fun x => rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ (Ψ x))
        (rowComp S d) (fun x => rhoVr (tauE D) (wt G (.grid 0 D.R.m)) (S.N.fr (.grid 0 D.R.m))⁻¹
          (funOf (listedWt G (.grid 0 D.R.m)) (F x))) D.R.m
        (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) X Y := by
  rw [pairPts, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  refine (mul_left_comm c (τ d) _).trans (congrArg (τ d * ·) ?_)
  exact (congrArg₂ (fun a b => (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) a b)
    (ptV_eq_chainTo (V := fun j => G.V (.top j)) (Mo := fun j => VV ℂ (wt G (.top j))) (colComp S d)
      (fun x => rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ (Ψ x)) X D.R.m)
    (ptV_eq_chainTo (V := fun j => G.V (.grid j D.R.m)) (Mo := fun j => VV ℂ (wt G (.grid j D.R.m))) (rowComp S d)
      (fun x => rhoVr (tauE D) (wt G (.grid 0 D.R.m)) (S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt G (.grid 0 D.R.m)) (F x)))
      Y D.R.m)).symm
end
theorem _root_.GlobalTheory.T.twisted_pairing_identity : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun ch => ∀ P : PolCol ch.G × PolRow ch.G, ∃ κ : ℂ, ∀ t a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M τ, IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ch.S.IsExpansion t (ch.Phi a) β τ → ∀ y, defTot t ch.S.toGridChoice M (Finsupp.single P 1) τ (colFn ch a) (formTop ch t y) = κ * ch.S.classSum (ch.Phi a) β τ (psiC (ch.Psi a)) (ch.S.formC t y) := by
  intro hP hS
  obtain ⟨C0, H⟩ := Big.and hS (_root_.GlobalTheory.FirstRowLaw.first_row_invariant_under_twist hP hS)
  refine ⟨C0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc P => ?_⟩
  obtain ⟨hOK, h0⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch hi hsc
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨Λ0, hΛ0⟩ := GlobalTheory.JetsOne.col_real ch
  obtain ⟨Λ0', hΛ0'⟩ := GlobalTheory.JetsOne.form_real ch s.core.models.cX
  obtain ⟨Λ, rfl, hΛ⟩ := GlobalTheory.JetsOne.col_chain ch.S.toGridChoice hL P Λ0
  obtain ⟨Λ', rfl, hΛ'⟩ := GlobalTheory.JetsOne.row_chain ch.S.toGridChoice hL P Λ0'
  obtain ⟨c, σ, hσ, hlast⟩ := last_functional_compatible ch.S.toGridChoice hL (Λ D.R.m) (Λ' D.R.m)
  refine ⟨c, fun t a β hβ M τ hM hτ y => ?_⟩
  have hv := (hOK t a).vec β τ hτ
  obtain ⟨v1, v2⟩ := TermVolDef.isMeasDef_of_isTermVol ch.S.toGridChoice hL t _ β M hM
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.T.normalisedKernelExpansionSum_levelInvariant ch.S.toGridChoice hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hi.guard t)
    (Set.mem_univ t) hβ hτ hv (psiC (ch.Psi a)) (ch.S.formC t y)
  have hK0 : ∀ h : 0 < D.R.m, ch.S.levTop t (ch.Phi a) β 0 h = ch.G.Kplus := fun _ => rfl
  have key := GlobalTheory.JetsOne.glue (V := fun j => ch.G.V (.top j)) (V' := fun j => ch.G.V (.grid j D.R.m)) τ
    (fun d hd => hΛ t (Set.mem_univ t) d (hv d hd).1) (hΛ0 a) (GlobalTheory.JetsOne.col_left ch a)
    (fun d hd => GlobalTheory.JetsOne.col_near _ P d (hv d hd).1 (GlobalTheory.JetsOne.col_fix ch a (v1 0 hm).2.1))
    (fun d hd => hΛ' t (Set.mem_univ t) d (hv d hd).2) (hΛ0' t y) (GlobalTheory.JetsOne.form_aut s ch t y).1
    (fun d hd => GlobalTheory.JetsOne.row_near _ P d (hv d hd).2 (GlobalTheory.JetsOne.form_aut s ch t y).2) hlast
    (fun n hn => posDef_top ch.G hn.le) (fun n hn => posDef_grid hL hn)
    (fun j => M.ν (.top j)) (fun j => M.fd (.top j)) (ch.S.levTop t (ch.Phi a) β) (fun n hn => (v1 n hn).2)
    (fun j => M.ν (.grid j D.R.m)) (fun j => M.fd (.grid j D.R.m)) (ch.S.levRow t) (fun n hn => (v2 n hn).2)
    (fun X Y => c * GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ X Y (psiC (ch.Psi a) (X 0)) (ch.S.formC t y (Y 0)))
    (pairing_of_points_expansion ch.S.toGridChoice τ c _ _)
    (fun X Y j hj k hk => by
      rcases j with _ | j
      · have := i2 (GlobalTheory.JetsOne.psiC_right ch a) X Y k hk
        beta_reduce
        rw [Function.update_self, this]
      · exact congrArg _ (i1 X Y _ j.succ_pos hj k hk))
    (fun X Y j hj k hk => by
      rcases j with _ | j
      · have := h0 t a β hβ τ hτ y (psiC (ch.Psi a) (X 0)) X Y k hk
        beta_reduce
        rw [Function.update_self, this]
      · exact congrArg _ (i3 X Y _ j.succ_pos hj k hk))
    (fun X Y k h1 hk => congrArg _ (i4 X Y k h1 hk))
  rw [defTot, Finsupp.sum_single_index (by simp)]
  simp only [one_mul, GlobalTheory.JetsOne.defPer_eq, hσ]
  refine key.trans ?_
  rw [GridChoice.classSum, mul_finsum]
  exact finsum_congr fun c' => mul_left_comm _ _ _
end
end
end
