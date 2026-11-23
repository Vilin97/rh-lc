module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridStandardVacuumScalarEqProdLocalPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatHatStabOfHatL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdlVal
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminantIdeleAtSplitPlaceMovedGridNode
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenLevelInner
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdlVal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminantIdeleAtSplitPlaceMovedGridNodeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

theorem _root_.GlobalTheory.T.determinantIdeleAtSplitPlace_moved_gridNode : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)) (w : Pl D.host.E),
    (∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) →
    detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) =
      GlobalTheory.LFun.locIdele D.host.F w (gdet (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩)
        (S.B.β (j + 1) D.R.m) w (finG (G.V (.grid (j + 1) D.R.m)) k))) := by
  first | exact @GlobalTheory.RowDetLocal.detIdl_moved_eq_locIdele | exact GlobalTheory.RowDetLocal.detIdl_moved_eq_locIdele | (intros; apply GlobalTheory.RowDetLocal.detIdl_moved_eq_locIdele <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathEdgeFactorProdIntegralVertex

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

noncomputable section
namespace GlobalTheory.OppositeEdges

theorem oppositePath_prod_mulSingle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Γ : Grid k) (j : ℕ) :
    j + 1 < Γ.m → ∀ (κ : GL (Fin (Γ.rank (j + 1, Γ.m))) k), κ ∈ GlobalTheory.SplitWeil.KO k _ →
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (j + 1, Γ.m) κ))).prod =
      ((Γ.chi (Γ.m - (j + 1)) (gdet κ) : ℂˣ) : ℂ) * (((Γ.chi (Γ.m - j) (gdet κ))⁻¹ : ℂˣ) : ℂ) := by
  intro hj κ hκ
  set g : Γ.VertexGroup := Pi.mulSingle (j + 1, Γ.m) κ with hg
  have hap : ∀ z, apow (1 : kˣ) z = 1 := fun z => apow_of_valuation_eq_one (by simp) z
  have hK : ∀ Y, g Y ∈ GlobalTheory.SplitWeil.KO k _ := by
    intro Y
    by_cases hY : Y = (j + 1, Γ.m)
    · subst hY; simpa [hg] using hκ
    · rw [hg, Pi.mulSingle_eq_of_ne hY]; exact one_mem _
  have ha : ∀ Y, ∀ z : ℂ, apow (gdet (Assignment.one.read (g Y))) z = 1 := fun Y z =>
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO (hK Y))) z

  have hfar : ∀ b : Edge, b.src ≠ (j + 1, Γ.m) → b.tgt ≠ (j + 1, Γ.m) → Γ.edgeFactor .one g b = 1 := by
    intro b h1 h2
    simp [Grid.edgeFactor, hg, Pi.mulSingle_eq_of_ne h1, Pi.mulSingle_eq_of_ne h2, hap]
  have htheta : (((List.range Γ.m).reverse.map (Edge.theta Γ.m)).map (Γ.edgeFactor .one g)).prod = 1 := by
    refine List.prod_eq_one fun c hc => ?_
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
    apply hfar <;> simp [Edge.src, Edge.tgt] <;> omega
  have hex : (((List.range Γ.m).map (Edge.ex · Γ.m)).map (Γ.edgeFactor .one g)).prod =
      ∏ i ∈ Finset.range Γ.m, Γ.edgeFactor .one g (.ex i Γ.m) := by
    rw [List.map_map, Finset.prod_eq_multiset_prod]; rfl
  have hne : j ≠ j + 1 := by omega
  have hrest : ∀ i ∈ Finset.range Γ.m, i ≠ j ∧ i ≠ j + 1 → Γ.edgeFactor .one g (.ex i Γ.m) = 1 := by
    intro i _ hi
    apply hfar <;> simp [Edge.src, Edge.tgt] <;> omega
  rw [oppositePath, List.map_append, List.prod_append, htheta, mul_one, hex,
    Finset.prod_eq_mul j (j + 1) hne hrest (by simp; omega) (by simp; omega)]
  have hκa : ∀ z : ℂ, apow (gdet (Assignment.one.read κ)) z = 1 := fun z =>
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO hκ)) z
  have hj1 : (j + 1 + 1, Γ.m) ≠ (j + 1, Γ.m) := by simp
  have hj0 : (j, Γ.m) ≠ (j + 1, Γ.m) := by simp
  simp only [Grid.edgeFactor, Edge.src, Edge.tgt, ha, mul_one, hg, Pi.mulSingle_eq_of_ne hj1,
    Pi.mulSingle_eq_of_ne hj0, Pi.mulSingle_eq_same, hκa, map_one, hap, Units.val_one, inv_one, one_mul]
  simp only [Grid.kappa, Grid.blockChar, MonoidHom.div_apply, Units.val_div_eq_div_val,
    Units.val_inv_eq_inv_val, Nat.add_sub_cancel]
  have h1 := Units.ne_zero (Γ.chi (Γ.m - (j + 1)) (gdet κ))
  have h2 := Units.ne_zero (Γ.chi (Γ.m - j) (gdet κ))
  have h3 := Units.ne_zero ((Γ.eta ^ ((Γ.rank (j + 1, Γ.m) + 1) % 2)) (gdet κ))
  field_simp

end GlobalTheory.OppositeEdges
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathEdgeFactorProdIntegralVertexStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

theorem _root_.GlobalTheory.T.oppositePath_edgeFactor_prod_integral_vertex : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Γ : Grid k) (j : ℕ),
    j + 1 < Γ.m → ∀ (κ : GL (Fin (Γ.rank (j + 1, Γ.m))) k), κ ∈ GlobalTheory.SplitWeil.KO k _ →
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (j + 1, Γ.m) κ))).prod =
      ((Γ.chi (Γ.m - (j + 1)) (gdet κ) : ℂˣ) : ℂ) * (((Γ.chi (Γ.m - j) (gdet κ))⁻¹ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.OppositeEdges.oppositePath_prod_mulSingle | exact GlobalTheory.OppositeEdges.oppositePath_prod_mulSingle | (intros; apply GlobalTheory.OppositeEdges.oppositePath_prod_mulSingle <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceScalarsMulEqOppositePathEdgeFactors

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

noncomputable section

namespace GlobalTheory.RowVacScalar



theorem splitScal_mul_eq_oppositePath : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ w ∈ locPl G t, (∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) →
    GlobalTheory.RowVacScalar.splitScal G (.chi j D.R.m) w (G.toPair (.chi j D.R.m) 1 (moved S j k)).1
                 (G.toPair (.chi j D.R.m) 1 (moved S j k)).2 *
      GlobalTheory.RowVacScalar.splitScal G (.chi (j + 1) D.R.m) w (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).1
        (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2 =
    ((oppositePath D.R.m).map ((locGrid G t w).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m)
      (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
        (finG (G.V (.grid (j + 1) D.R.m)) k))))).prod := by
  intro D T L sc G W U S t ht j hj k hk w hw hs
  have hK : inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
      (finG (G.V (.grid (j + 1) D.R.m)) k) ∈ GlobalTheory.SplitWeil.KO (Kw w) _ := by
    have h1 := hk
    simp only [GridChoice.levRow, prodLev, Subgroup.mem_inf, Subgroup.mem_iInf] at h1
    have h2 := h1.1 ⟨w, hw⟩
    rw [Subgroup.mem_comap] at h2
    rwa [GlobalTheory.LastRowLat.givenLevel_inner G t w (j + 1, D.R.m) (by simp) (by simp; have := D.R.two_le_m; omega)] at h2
  have he : idemAt w * idemAt w = idemAt w := (Classical.epsilon_spec hs).1.1
  have d1 : ∀ V : HSp D, detIdl (idemAt w) V 1 = 1 := fun V => by
    unfold detIdl; split_ifs <;> simp
  have dneg : detIdl (idemAt w) (negSp (G.V (.grid (j + 1) D.R.m))) (negGA _ (moved S j k)) =
      detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) := by
    refine Units.ext ?_
    rw [detIdl_val he, detIdl_val he, mt_negGA]
  have hpar : Odd (G.pS (.chi (j + 1) D.R.m)).rank ↔ Odd (G.pT (.chi j D.R.m)).rank := by
    have r0 := (rank_vertex G t w (X := (j, D.R.m)) ⟨by omega, le_rfl⟩).symm
    have r2 := (rank_vertex G t w (X := (j + 1 + 1, D.R.m)) ⟨by omega, le_rfl⟩).symm
    change Odd (G.V (.grid (j + 1 + 1) D.R.m)).rank ↔ Odd (G.V (.grid j D.R.m)).rank
    rw [r0, r2]
    simp only [Grid.rank, locGrid]
    rw [show D.R.r + D.R.m * D.R.t + (j + 1 + 1) * sLen D = (D.R.r + D.R.m * D.R.t + j * sLen D) + 2 * sLen D by ring]
    rw [Nat.odd_add]
    exact ⟨fun h => h.2 (even_two_mul _), fun h => ⟨fun _ => even_two_mul _, fun _ => h⟩⟩
  have key : ∀ (a b η : (AE D)ˣ →* Circle) (n n' : ℕ), (Odd n ↔ Odd n') → ∀ x,
      (Formalism.IndefR.Lift.attChr a η n x)⁻¹ * Formalism.IndefR.Lift.attChr b η n' x = (a x)⁻¹ * b x := by
    intro a b η n n' h x
    unfold Formalism.IndefR.Lift.attChr
    by_cases hn : Odd n
    · rw [if_pos hn, if_pos (h.1 hn), MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_rev, inv_inv,
        mul_comm (η x), mul_mul_mul_comm, mul_inv_cancel, mul_one]
    · rw [if_neg hn, if_neg (fun h' => hn (h.2 h'))]
  have hχ : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ y, ((G.ch.chi i (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) =
      (((G.ch.chiH i).loc w y : ℂˣ) : ℂ) := fun i h1 h2 y => by
    have := congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq (G.ch.chi_eq i h1 h2) w)
    simpa [GlobalTheory.LFun.locChar] using this
  refine Eq.trans ?_ (GlobalTheory.T.oppositePath_edgeFactor_prod_integral_vertex (locGrid G t w) j hj _ hK).symm
  simp only [splitScal, GridData.toPair, splitFacO, map_one, d1, inv_one, one_mul, mul_one]
  have eqS : detIdl (idemAt w) (G.pS (Pair.chi j D.R.m)) ((negGA (G.V (Node.grid (j + 1) D.R.m))) (moved S j k)) =
      detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) := dneg
  have eqT : detIdl (idemAt w) (G.pT (Pair.chi (j + 1) D.R.m)) (moved S j k) =
      detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) := rfl
  rw [eqS, eqT, GlobalTheory.T.determinantIdeleAtSplitPlace_moved_gridNode S t j hj k w hs, ← Circle.coe_mul]
  rw [GridData.chrT, GridData.chrS]
  rw [key (G.chr (Pair.chi j D.R.m)) (G.chr (Pair.chi (j + 1) D.R.m)) L.eta _ _ hpar.symm]
  rw [Circle.coe_mul, Circle.coe_inv]
  dsimp only [GridData.chr]
  rw [hχ _ (by omega) (by omega), hχ _ (by omega) (by omega)]
  simp only [locGrid, Units.val_inv_eq_inv_val]
  exact mul_comm _ _

end GlobalTheory.RowVacScalar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceScalarsMulEqOppositePathEdgeFactorsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

theorem _root_.GlobalTheory.T.splitPlaceScalars_mul_eq_oppositePath_edgeFactors : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ w ∈ locPl G t, (∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) →
    GlobalTheory.RowVacScalar.splitScal G (.chi j D.R.m) w (G.toPair (.chi j D.R.m) 1 (moved S j k)).1
                 (G.toPair (.chi j D.R.m) 1 (moved S j k)).2 *
      GlobalTheory.RowVacScalar.splitScal G (.chi (j + 1) D.R.m) w (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).1
        (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2 =
    ((oppositePath D.R.m).map ((locGrid G t w).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m)
      (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
        (finG (G.V (.grid (j + 1) D.R.m)) k))))).prod := by
  first | exact @GlobalTheory.RowVacScalar.splitScal_mul_eq_oppositePath | exact GlobalTheory.RowVacScalar.splitScal_mul_eq_oppositePath | (intros; apply GlobalTheory.RowVacScalar.splitScal_mul_eq_oppositePath <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumScalarsEqProductEdgeFactorsRow

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVacScalar

private theorem map_mt_one_eq_one {D : D7} (V : HSp D) : (Formalism.L2.Theta.mt V 1).map (finPart D) = 1 := by
  rw [Formalism.L2.Theta.mt, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem scalars_eq_edgeFactors : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ (c₁ c₂ : ℂ),
    W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) →
    W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) =
      c₂ • S.Z.vac (.chi (j + 1) D.R.m) →
    c₁ * c₂ = ∏ w : locPl G t, ((oppositePath D.R.m).map ((locGrid G t w.1).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m)
      (inBasis (rank_vertex G t w.1 (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w.1
        (finG (G.V (.grid (j + 1) D.R.m)) k))))).prod := by
  intro D T L sc G W U S μ₀ hL t ht j hj k hk c₁ c₂ h₁ h₂
  obtain ⟨hA, hB, hC, hD⟩ := GlobalTheory.RowMovedLat.moved_pair_stab S ht j hj k hk
  have e₁ := GlobalTheory.RowVacScalar.vacScalar_eq_prod S hL t j hj.le _ hA ?g₁ hB ?l₁ c₁ h₁
  have e₂ := GlobalTheory.RowVacScalar.vacScalar_eq_prod S hL t (j + 1) hj _ ?g₂ hC ?l₂ hD c₂ h₂
  · rw [e₁, e₂, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    exact GlobalTheory.T.splitPlaceScalars_mul_eq_oppositePath_edgeFactors S ht j hj k hk w.1 w.2 ⟨_, GlobalTheory.RowVacScalar.isIdemAt_idemAt hL G t w.2⟩
  case g₁ =>
    dsimp only [GridData.toPair]
    exact one_mem _
  case l₁ =>
    intro y
    dsimp only [GridData.toPair]
    rw [map_mt_one_eq_one, Matrix.one_mulVec]
  case g₂ =>
    dsimp only [GridData.toPair]
    rw [map_one]
    exact one_mem _
  case l₂ =>
    intro y
    dsimp only [GridData.toPair]
    rw [map_one, map_mt_one_eq_one, Matrix.one_mulVec]

end GlobalTheory.RowVacScalar
end
end
end
