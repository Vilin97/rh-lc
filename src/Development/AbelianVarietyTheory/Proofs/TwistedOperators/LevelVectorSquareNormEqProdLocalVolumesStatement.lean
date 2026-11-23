module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppInd
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSqProductDatumThetaConjugateHalfStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesDisjointTwistPlaces

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerZeroUpperBlockIndicatorSqSumEqCard

section

@[expose] public section

open Classical

namespace GlobalTheory.LevelVecNorm

theorem finsum_indicator_one_eq_ncard' {α : Type} (s : Set α) :
    (∑ᶠ x, s.indicator (fun _ => (1:ℝ)) x) = (s.ncard : ℝ) := by
  by_cases hs : s.Finite
  · rw [← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card s hs]
    simp
  · have hsupp : Function.support (s.indicator (fun _ => (1:ℝ))) = s := by
      ext x; by_cases hx : x ∈ s <;> simp [hx]
    rw [finsum_of_infinite_support (by rw [hsupp]; exact hs), Set.Infinite.ncard hs]
    simp

theorem suppInd_sq_sum_eq_card : ∀ {k : Type} [CommRing k] {b a : ℕ} (r t : ℕ), b = r + t → a = r → ∀ H : Subgroup (GL (Fin r) k),
    ∑ᶠ z : Matrix (Fin b) (Fin a) k, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = (Nat.card H : ℝ) := by
  intro k _ b a r t hb ha H
  subst hb; subst a
  let f : GL (Fin r) k → Matrix (Fin (r + t)) (Fin r) k := fun g i j =>
    if h : i.val < r then (g : Matrix (Fin r) (Fin r) k) ⟨i.val, h⟩ j else 0
  have htop : ∀ g, Formalism.IndefR.Datum.topL r (f g) = (g : Matrix (Fin r) (Fin r) k) := by
    intro g; ext i j
    simp [Formalism.IndefR.Datum.topL, f, i.isLt, j.isLt, show i.val < r + t by omega]
  have hlow : ∀ g, Formalism.IndefR.Datum.LowZero r (f g) := by
    intro g i j hi _
    simp [f, show ¬ i.val < r by omega]
  have hinj : Function.Injective f := by
    intro g g' h
    apply Units.ext
    rw [← htop g, ← htop g', h]
  let S : Set (Matrix (Fin (r + t)) (Fin r) k) :=
    {z | Formalism.IndefR.Datum.LowZero r z ∧ ∃ g ∈ H, ((g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = Formalism.IndefR.Datum.topL r z}
  have hS : S = f '' (H : Set (GL (Fin r) k)) := by
    ext z
    constructor
    · rintro ⟨hz, g, hg, hgz⟩
      refine ⟨g, hg, ?_⟩
      ext i j
      by_cases hi : i.val < r
      · have := congrFun (congrFun hgz ⟨i.val, hi⟩) j
        simp only [Formalism.IndefR.Datum.topL, j.isLt, show i.val < r + t by omega] at this
        simpa [f, hi] using this
      · simp [f, hi, hz i j (by omega) j.isLt]
    · rintro ⟨g, hg, rfl⟩
      exact ⟨hlow g, g, hg, (htop g).symm⟩
  have hfun : ∀ z, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = S.indicator (fun _ => (1:ℝ)) z := by
    intro z
    unfold GlobalTheory.LevelVecNorm.suppInd
    by_cases hz : z ∈ S
    · have hz' := hz
      simp only [S, Set.mem_ofPred_eq] at hz'
      rw [if_pos hz', Set.indicator_of_mem hz]; norm_num
    · have hz' := hz
      simp only [S, Set.mem_ofPred_eq] at hz'
      rw [if_neg hz', Set.indicator_of_notMem hz]; norm_num
  simp_rw [hfun]
  rw [finsum_indicator_one_eq_ncard', hS, Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq]
  rfl

end GlobalTheory.LevelVecNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerZeroUpperBlockIndicatorSqSumEqCardStatement

section

@[expose] public section

open Classical


theorem _root_.GlobalTheory.T.lowerZeroUpperBlockIndicator_sq_sum_eq_card : ∀ {k : Type} [CommRing k] {b a : ℕ} (r t : ℕ), b = r + t → a = r → ∀ H : Subgroup (GL (Fin r) k),
  ∑ᶠ z : Matrix (Fin b) (Fin a) k, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = (Nat.card H : ℝ) := by
  first | exact @GlobalTheory.LevelVecNorm.suppInd_sq_sum_eq_card | exact GlobalTheory.LevelVecNorm.suppInd_sq_sum_eq_card | (intros; apply GlobalTheory.LevelVecNorm.suppInd_sq_sum_eq_card <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormFiniteThetaDatumEqIndicatorProduct

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.LevelVecNorm.NormFac

variable {E : Type} [Field E] [NumberField E]

instance finKP (PP : Pl E) : Finite (kP PP) := PP.asIdeal.finiteQuotientOfFreeOfNeBot PP.ne_bot

theorem norm_char_fin {G : Type} [Group G] [Finite G] (f : G →* ℂˣ) (g : G) : ‖((f g : ℂˣ) : ℂ)‖ = 1 := by
  refine Complex.norm_eq_one_of_pow_eq_one (n := Nat.card G) ?_ Nat.card_pos.ne'
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

theorem mem_blockTri_blkOf {κ : Type} [CommRing κ] {r t : ℕ} (g : GL (Fin r) κ) : g ∈ blockTri (blkOf r t) := by
  rw [mem_blockTri]
  intro i j h
  simp [blkOf, i.2, j.2] at h

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] {r : ℕ} (hr : r ≤ r) (g : GL (Fin r) κ) : upperLeftBlock hr g = g := by
  have hm : g ∈ blockTri (blk2 r) := by
    rw [mem_blockTri]
    intro i j h
    simp [blk2, i.2, j.2] at h
  ext i j
  rw [upper_block_val_submatrix hr hm]
  rfl

theorem exists_GL_iff {κ : Type} [CommRing κ] {r : ℕ} (M : Matrix (Fin r) (Fin r) κ) :
    (∃ g : GL (Fin r) κ, (g : Matrix (Fin r) (Fin r) κ) = M) ↔ IsUnit M.det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  exact ⟨fun ⟨g, hg⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨g, hg⟩⟩

theorem locH_of_mem (Pg : Finset (Pl E)) {r : ℕ} (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) {PP : Pl E}
    (h : PP ∈ Pg) : locH Pg Hl PP = Hl ⟨PP, h⟩ := dif_pos h

theorem locH_of_not (Pg : Finset (Pl E)) {r : ℕ} (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) {PP : Pl E}
    (h : PP ∉ Pg) : locH Pg Hl PP = ⊤ := dif_neg h

theorem norm_omegaQ {D : D7} {a b : ℕ} (Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    ‖omegaQ Q r ξ k y‖ = if ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det then 1 else 0 := by
  unfold omegaQ
  split
  · rename_i h
    simp only [norm_prod, norm_zpow, norm_char_fin, _root_.one_zpow, Finset.prod_const_one]
  · rename_i h
    rw [norm_zero]

theorem norm_omegaG {D : D7} {b r t : ℕ} (hr : r ≤ r) (Pg : Finset (Pl D.host.E))
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) (cl : ∀ PP : ↥Pg, Hl PP →* ℂˣ)
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin r) (kP PP)) :
    ‖omegaG (Lev.datY r r t 0 hr Pg ∅ (LevelP.ofLocal Hl cl) χ ξ Lev.Frm.B) m y‖ =
      if ∀ PP (h : PP ∈ Pg), LowZero r (y PP) ∧
          ∃ g ∈ Hl ⟨PP, h⟩, ((g : GL (Fin r) (kP PP)) : Matrix (Fin r) (Fin r) (kP PP)) = topL r (y PP) then 1 else 0 := by
  by_cases hc : ∀ PP (h : PP ∈ Pg), LowZero r (y PP) ∧
      ∃ g ∈ Hl ⟨PP, h⟩, ((g : GL (Fin r) (kP PP)) : Matrix (Fin r) (Fin r) (kP PP)) = topL r (y PP)
  · rw [if_pos hc]
    unfold omegaG
    split
    · simp only [norm_mul, norm_prod, norm_inv, norm_char_fin, Finset.prod_const_one, inv_one, mul_one]
    · rename_i h
      exfalso
      apply h
      refine ⟨fun PP hP => (hc PP hP).1, fun PP => (hc PP.1 PP.2).2.choose,
        fun PP => (hc PP.1 PP.2).2.choose_spec.2, fun PP => mem_blockTri_blkOf _, ?_⟩
      show (fun PP : ↥Pg => upperLeftBlock hr ((hc PP.1 PP.2).2.choose)) ∈ Subgroup.pi Set.univ Hl
      intro PP _
      simp only [restrictedBlock_self_apply]
      exact (hc PP.1 PP.2).2.choose_spec.1
  · rw [if_neg hc]
    unfold omegaG
    split
    · rename_i h
      exfalso
      obtain ⟨hlow, g, hg1, -, hg3⟩ := h
      apply hc
      intro PP hP
      have h3 : (fun PP : ↥Pg => upperLeftBlock hr (g PP)) ∈ Subgroup.pi Set.univ Hl := hg3
      have h4 := h3 ⟨PP, hP⟩ (Set.mem_univ _)
      simp only [restrictedBlock_self_apply] at h4
      exact ⟨hlow PP hP, g ⟨PP, hP⟩, h4, hg1 ⟨PP, hP⟩⟩
    · rw [norm_zero]

theorem norm_omegaG_mul_omegaQ {D : D7} {b a r t : ℕ} (hr : r ≤ a) (har : a = r) (Pg Q : Finset (Pl D.host.E))
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) (cl : ∀ PP : ↥Pg, Hl PP →* ℂˣ)
    (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    ‖omegaG (Lev.datY a r t 0 hr Pg ∅ (LevelP.ofLocal Hl cl) (fun _ _ => 1) (fun _ => 1) Lev.Frm.B) m y *
        omegaQ Q a m (-1) y‖ = ∏ PP ∈ Pg ∪ Q, suppInd r (locH Pg Hl PP) (y PP) := by
  subst a
  rw [norm_mul, norm_omegaG, norm_omegaQ, ite_zero_mul_ite_zero, mul_one]
  unfold suppInd
  rw [Finset.prod_ite_zero, Finset.prod_const_one]
  by_cases hc : ∀ PP ∈ Pg ∪ Q, LowZero r (y PP) ∧
      ∃ g ∈ locH Pg Hl PP, ((g : GL (Fin r) (kP PP)) : Matrix (Fin r) (Fin r) (kP PP)) = topL r (y PP)
  · rw [if_pos hc, if_pos]
    refine ⟨fun PP hP => ?_, fun PP hP => ?_⟩
    · have h1 := hc PP (Finset.mem_union_left _ hP)
      rwa [locH_of_mem Pg Hl hP] at h1
    · have h1 := hc PP (Finset.mem_union_right _ hP)
      refine ⟨h1.1, ?_⟩
      obtain ⟨g, -, hg⟩ := h1.2
      exact (exists_GL_iff _).1 ⟨g, hg⟩
  · rw [if_neg hc, if_neg]
    rintro ⟨hA, hB⟩
    apply hc
    intro PP hP
    by_cases hg : PP ∈ Pg
    · rw [locH_of_mem Pg Hl hg]
      exact hA PP hg
    · rw [locH_of_not Pg Hl hg]
      have hq : PP ∈ Q := (Finset.mem_union.1 hP).resolve_left hg
      obtain ⟨g, hg'⟩ := (exists_GL_iff _).2 (hB PP hq).2
      exact ⟨(hB PP hq).1, g, Subgroup.mem_top _, hg'⟩

end GlobalTheory.LevelVecNorm.NormFac

namespace GlobalTheory.LevelVecNorm

theorem normFac : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)),
  ‖omegaG (R.datWp i (LevelP.ofLocal Hl cl)) m y * omegaQ (R.Q t) (Wc D i).rank m (-1) y‖ = ∏ PP ∈ R.Pg ∪ R.Q t, GlobalTheory.LevelVecNorm.suppInd D.R.r (GlobalTheory.LevelVecNorm.locH R.Pg Hl PP) (y PP) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t Hl cl m y
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  exact NormFac.norm_omegaG_mul_omegaQ (le_of_eq hW.symm) hW R.Pg (R.Q t) Hl cl m y

end GlobalTheory.LevelVecNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormFiniteThetaDatumEqIndicatorProductStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical


theorem _root_.GlobalTheory.T.norm_finiteThetaDatum_eq_indicator_product : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)),
  ‖omegaG (R.datWp i (LevelP.ofLocal Hl cl)) m y * omegaQ (R.Q t) (Wc D i).rank m (-1) y‖ = ∏ PP ∈ R.Pg ∪ R.Q t, GlobalTheory.LevelVecNorm.suppInd D.R.r (GlobalTheory.LevelVecNorm.locH R.Pg Hl PP) (y PP) := by
  first | exact @GlobalTheory.LevelVecNorm.normFac | exact GlobalTheory.LevelVecNorm.normFac | (intros; apply GlobalTheory.LevelVecNorm.normFac <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesDisjointTwistPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical


theorem _root_.GlobalTheory.T.disjoint_Pg_Q_of_core : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Disjoint R.Pg (R.Q t) := by
  first | exact @GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces | exact GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces | (intros; apply GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorSquareNormEqProdLocalVolumes

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.LevelVecNorm

theorem levelVector_squareNorm_eq_prod_localVolumes_alt : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ), P = LevelP.ofLocal Hl cl → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → nrm2 μ 𝓧 f = (∏ PP ∈ R.Pg.attach, (Nat.card (Hl PP) : ℝ) * ((Nat.card (kP PP.1) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹) * ∏ PP ∈ R.Q t, (Nat.card (GL (Fin D.R.r) (kP PP)) : ℝ) * ((Nat.card (kP PP) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹ := by
  intro hLIS D G _ _ Pl0 T A Ks _ _ _ R F hPM i t σ s P cμ cη m ω BW f₀ f c io hL Hl cl hP μ 𝓧 hμ
  have hL' := hL
  obtain ⟨hcore, -, -, -, -, -, -, hlev, -⟩ := hL'
  obtain ⟨-, e, he, hth⟩ := hlev
  subst hP
  have h1 := GlobalTheory.T.normSq_productDatumTheta_conjugateHalf R F hPM i t σ s (LevelP.ofLocal Hl cl) cμ cη m ω BW f₀ f c io hL e he
    (fun y => omegaG (R.datWp i (LevelP.ofLocal Hl cl)) m y * omegaQ (R.Q t) (Wc D i).rank m (-1) y)
    (fun PP z => GlobalTheory.LevelVecNorm.suppInd D.R.r (GlobalTheory.LevelVecNorm.locH R.Pg Hl PP) z)
    (GlobalTheory.T.norm_finiteThetaDatum_eq_indicator_product R i t Hl cl m) f hth μ 𝓧 hμ
  rw [h1]
  have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hexp : (Vc D i).rank * (Wc D i).rank = D.R.r ^ 2 + D.R.r * D.R.t := by rw [hV, hW]; ring
  simp_rw [fun PP => GlobalTheory.T.lowerZeroUpperBlockIndicator_sq_sum_eq_card (k := kP PP) D.R.r D.R.t hV hW (GlobalTheory.LevelVecNorm.locH R.Pg Hl PP), hexp]
  rw [Finset.prod_union (GlobalTheory.T.disjoint_Pg_Q_of_core R F hcore t)]
  congr 1
  · rw [← Finset.prod_attach R.Pg]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [div_eq_mul_inv]
    congr 3
    simp [GlobalTheory.LevelVecNorm.locH, PP.2]
  · refine Finset.prod_congr rfl fun PP hPP => ?_
    have hn : PP ∉ R.Pg := fun h => Finset.disjoint_left.1 (GlobalTheory.T.disjoint_Pg_Q_of_core R F hcore t) h hPP
    rw [div_eq_mul_inv]
    congr 2
    simp only [GlobalTheory.LevelVecNorm.locH, dif_neg hn]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv

end GlobalTheory.LevelVecNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorSquareNormEqProdLocalVolumesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)


theorem _root_.GlobalTheory.T.levelVector_squareNorm_eq_prod_localVolumes : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ), P = LevelP.ofLocal Hl cl → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → nrm2 μ 𝓧 f = (∏ PP ∈ R.Pg.attach, (Nat.card (Hl PP) : ℝ) * ((Nat.card (kP PP.1) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹) * ∏ PP ∈ R.Q t, (Nat.card (GL (Fin D.R.r) (kP PP)) : ℝ) * ((Nat.card (kP PP) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹ := by
  first | exact @GlobalTheory.LevelVecNorm.levelVector_squareNorm_eq_prod_localVolumes_alt | exact GlobalTheory.LevelVecNorm.levelVector_squareNorm_eq_prod_localVolumes_alt | (intros; apply GlobalTheory.LevelVecNorm.levelVector_squareNorm_eq_prod_localVolumes_alt <;> assumption)
end
end
