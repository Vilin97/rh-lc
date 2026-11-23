module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllPositiveModelFiniteDimensionalCompactType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPerfectPairingCoefficientSpaceTensorModelStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSizesNR
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHCTypeWConj
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairwiseFlatMapBand
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylKTypeTensorEqContragredientTranslatesSpanStatement
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightBaseParEqNegLowestKType

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal.BaseWeights

theorem mem_tparBlock {c x : ℚ} {n : ℕ} (h : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block c n) : x ∈ TPar.block c n := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
  exact Finset.mem_image.2 ⟨a, Finset.mem_range.2 (List.mem_range.1 ha), rfl⟩

theorem basePar_sublist {S : Sizes} (P : Entries S) : P.basePar.Sublist P.orderList := by
  have h1 : ∀ l : List (Fin (S.k - 1)),
      (l.map fun i => (P.v i : ℚ)).Sublist (l.flatMap fun i => [(P.v i : ℚ), P.u i]) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append]
      exact (ih.cons _).cons₂ _
  unfold Entries.basePar Entries.orderList
  exact List.Sublist.append ((h1 _).trans (List.sublist_append_right _ _)) (List.Sublist.refl _)

theorem base_mem_Dpar (D : D7) (C : ℝ) (τ : D.what₂.Tau) :
    ∀ x ∈ (rowEntries D C τ).basePar, ∃ s, (x, s) ∈ (Ptw D).Dpar D.R.m τ := by
  have hodd : ¬ Odd D.R.m := Nat.not_odd_iff_even.2 D.R.m_even
  obtain ⟨hv, hb, he⟩ := GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)
  intro x hx
  simp only [Entries.basePar, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.mem_finRange,
    true_and] at hx
  unfold TPar.Dpar
  rcases hx with ⟨i, rfl⟩ | ⟨j, h | h⟩
  · refine ⟨true, Finset.mem_image.2 ⟨((Ptw D).v τ i, true), ?_, ?_⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    · simp only [hodd, if_false, add_zero]
      exact Prod.ext (hv i) rfl
  · refine ⟨decide ((j : ℕ) ≤ D.R.m ∨ Even ((j : ℕ) - D.R.m)), Finset.mem_image.2 ⟨(-(Ptw D).b τ j, decide ((j : ℕ) ≤ D.R.m ∨ Even ((j : ℕ) - D.R.m))), ?_, ?_⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
    · simp only [hodd, if_false, add_zero]
      refine Prod.ext ?_ rfl
      rw [h]
      show -(D.hc τ).b j = _
      rw [hb j]; rfl
  · refine ⟨true, Finset.mem_image.2 ⟨(x, true), ?_, ?_⟩⟩
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, j.2⟩, ?_⟩)
      refine Finset.mem_image.2 ⟨x, ?_, rfl⟩
      have hx' := mem_tparBlock h
      have : (-(Ptw D).e τ j) = -(((rowEntries D C τ).e j : ℤ) : ℚ) := by
        show -(D.hc τ).e j = _
        rw [he j]; rfl
      rw [this]
      exact hx'
    · simp only [hodd, if_false, add_zero]

end GlobalTheory.RowReal.BaseWeights

namespace GlobalTheory.RowReal

open GlobalTheory.RowReal.BaseWeights

theorem hw_basePar_eq_neg_lowK : ∀ (D : D7) (C : ℝ)
    (M : Formalism.IndefR.Mult.DSModel D.sp.X' (Formalism.IndefR.Mult.parB (Ptw D) D.R.m)) (τ : D.what₂.Tau)
    (i : Fin D.sp.X'.rank),
    (hw (rowEntries D C τ).basePar i : ℝ) = -(Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Fin.rev i) := by
  intro D C M τ i
  have hlen : (rowEntries D C τ).basePar.length = D.sp.X'.rank := by
    rw [length_base, D.sp.X'_rank]
    simp [Sizes.nC, rowSizes, Ranks.rankX', Ranks.r]
  have hε : M.ε τ = Formalism.MainNotions.S.allPos _ := funext fun a => GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) M τ a
  obtain ⟨hanti, q, hq, hS⟩ := M.enum τ
  have hqa : StrictAnti q := fun a b h => by
    have := hanti h
    rw [hq, hq] at this
    exact_mod_cast this
  have hinj : Function.Injective fun a => -q a := fun a b h => hqa.injective (neg_injective h)
  have hE : (Finset.univ.image fun a => -q a).card = D.sp.X'.rank := by
    rw [Finset.card_image_of_injective _ hinj]; simp
  have hpw := (rowEntries_good D C τ).order.sublist (basePar_sublist (rowEntries D C τ))
  let f : Fin D.sp.X'.rank → ℚ := fun j => (rowEntries D C τ).basePar[(j : ℕ)]'(by rw [hlen]; exact j.2)
  have hf : StrictAnti f := fun a b hab => List.pairwise_iff_getElem.1 hpw _ _ _ _ hab
  have hfm : ∀ j, f j ∈ Finset.univ.image fun a => -q a := by
    intro j
    obtain ⟨s, hs⟩ := base_mem_Dpar D C τ _ (List.getElem_mem (by rw [hlen]; exact j.2))
    have h2 : (-(f j), s) ∈ Formalism.IndefR.Mult.parB (Ptw D) D.R.m τ := Finset.mem_image.2 ⟨_, hs, rfl⟩
    rw [hS] at h2
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h2
    refine Finset.mem_image.2 ⟨a, Finset.mem_univ _, ?_⟩
    have h3 := congrArg Prod.fst ha
    simp only at h3
    rw [h3, neg_neg]
  let g : Fin D.sp.X'.rank → ℚ := fun j => -q j.rev
  have hg : StrictAnti g := fun a b hab => by
    simp only [g, neg_lt_neg_iff]
    exact hqa (Fin.rev_lt_rev.2 hab)
  have hgm : ∀ j, g j ∈ Finset.univ.image fun a => -q a := fun j => Finset.mem_image.2 ⟨j.rev, Finset.mem_univ _, rfl⟩
  have hfg : f = g := (GlobalTheory.SignedHC.descEnum_unique hE hf hfm).symm.trans (GlobalTheory.SignedHC.descEnum_unique hE hg hgm)
  have hi : (i : ℕ) < (rowEntries D C τ).basePar.length := by rw [hlen]; exact i.2
  have key : (rowEntries D C τ).basePar[(i : ℕ)] = -q i.rev := congrFun hfg i
  have h1 := hw_base _ i hi
  have hl : (((rowEntries D C τ).basePar.length : ℕ) : ℚ) = (D.sp.X'.rank : ℚ) := by rw [hlen]
  rw [hl, key] at h1
  rw [hε, GlobalTheory.ConjTypeW.lowK_allPos, hq]
  have h4 : (hw (rowEntries D C τ).basePar i : ℝ) = (((hw (rowEntries D C τ).basePar i : ℤ) : ℚ) : ℝ) := by push_cast; rfl
  rw [h4, h1, Fin.val_rev]
  have h5 : (i : ℕ) + 1 ≤ D.sp.X'.rank := i.2
  rw [Nat.cast_sub h5]
  push_cast
  ring

end GlobalTheory.RowReal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightBaseParEqNegLowestKTypeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.highestWeight_basePar_eq_neg_lowestKType : ∀ (D : D7) (C : ℝ) (M : Formalism.IndefR.Mult.DSModel D.sp.X' (Formalism.IndefR.Mult.parB (Ptw D) D.R.m)) (τ : D.what₂.Tau) (i : Fin D.sp.X'.rank), (hw (rowEntries D C τ).basePar i : ℝ) = -(Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Fin.rev i) := by
  first | exact @GlobalTheory.RowReal.hw_basePar_eq_neg_lowK | exact GlobalTheory.RowReal.hw_basePar_eq_neg_lowK | (intros; apply GlobalTheory.RowReal.hw_basePar_eq_neg_lowK <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CastRealAll

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowReal
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefBase

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem rank_X (ch : Choice R) : (rowSizes D).nC (0 : Fin ((rowSizes D).m + 1)) = D.sp.X'.rank := by
  have h1 := rank_gridM ch.G (i := 0) (Nat.zero_le _)
  have h2 : (ch.G.V (.grid 0 D.R.m)) = (columnBlock R.toLevCh D.R.m).sp := rfl
  rw [h2, colY_m] at h1
  exact h1.symm

def xPt (ch : Choice R) (g : Gc D.what₂.Tau (rowSizes D)) : GA D D.sp.X' :=
  cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) ((kappa ch.W g).2 0)

theorem cast_realAll (θ : InfFam D) (n0 : ℕ) (hn : n0 = D.sp.X'.rank) (v : UG D.what₂.Tau n0) :
    ∀ (X : LSp D) (h : X = ⟨D.sp.X', R.toLevCh.ΛX⟩) (O : D.what₂.Tau → Matrix (Fin X.sp.rank) (Fin X.sp.rank) ℂ)
      (hO : HEq O (onb R.MX)) (e1 : n0 = X.sp.rank),
      cast (congrArg (fun X : LSp D => GA D X.sp) h)
        (realAll θ X.sp (fun τ => O τ * ((castU e1 (v τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) * (O τ)⁻¹)) =
      realAll θ D.sp.X' (fun τ => onb R.MX τ * ((castU hn (v τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) *
        (onb R.MX τ)⁻¹) := by
  intro X h
  subst h
  intro O hO e1
  cases eq_of_heq hO
  rfl

theorem xPt_eq (ch : Choice R) (hO : ch.W.Over R) (h0 : PosOnb ch.W (.grid 0 D.R.m)) (g : Gc D.what₂.Tau (rowSizes D)) :
    xPt ch g = realAll R.θ D.sp.X' (fun τ => GlobalTheory.DefLift.unfr R.MX τ
      ((castU (rank_X ch) (g.2 0 τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ)) := by
  unfold xPt
  have hk : ((kappa ch.W g).2 0 : GA D (columnBlock R.toLevCh D.R.m).sp) =
      realAll ch.W.θ (columnBlock R.toLevCh D.R.m).sp (fun τ => ch.W.onb (.grid 0 D.R.m) τ *
        ((castU (rank_gridM ch.G (i := 0) (Nat.zero_le _)).symm (g.2 0 τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) *
          (ch.W.onb (.grid 0 D.R.m) τ)⁻¹) := by
    exact vtxPt_eq h0 (colU ch.G 0 g)
  rw [hk]
  have e := cast_realAll (R := R) ch.W.θ _ (rank_X ch) (g.2 0) (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh)
    (ch.W.onb (.grid 0 D.R.m)) hO.onbX (rank_gridM ch.G (i := 0) (Nat.zero_le _)).symm
  refine e.trans ?_
  rw [hO.θ]
  congr 1
  funext τ
  unfold GlobalTheory.DefLift.unfr onb
  rw [Matrix.nonsing_inv_nonsing_inv _ (GlobalTheory.DefLift.fr_det R.MX τ)]

end GlobalTheory.CoefBase

namespace GlobalTheory.CoefBase

section Core

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} [DecidableEq D.what₂.Tau]

end Core

section Core2

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} [DecidableEq D.what₂.Tau]

theorem core (M : Formalism.IndefR.Mult.DSModel V S) (θ : InfFam D) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ)
    (hθ : IsInfFam θ) (hp : GlobalTheory.DefLift.AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr) (lam : D.what₂.Tau → ℕ → ℤ)
    (hl : ∀ τ (i : Fin V.rank), (lam τ i : ℝ) = -(Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Fin.rev i)) :
    ∃ A : c.W ≃ₗ[ℂ] weylSub V.rank lam, ∀ (u : UG D.what₂.Tau V.rank) (w : c.W),
      A (c.ρ (realAll θ V (fun τ => GlobalTheory.DefLift.unfr M τ (u τ))) w) = weylRep V.rank lam u (A w) := by
  have hε : ∀ τ, M.ε τ = Formalism.MainNotions.S.allPos V.rank := fun τ => funext fun a => hp τ a
  have m := fun τ => GlobalTheory.CompactModel.model_allPos D V S M τ (hε τ)
  haveI : ∀ τ, FiniteDimensional ℂ (M.H τ) := fun τ => (m τ).1
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_perfectPairing_coefficientSpace_tensorModel D V S M θ c pr hθ hp hc hpr
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.weyl_kTypeTensor_eq_contragredient_translatesSpan D.what₂.Tau V.rank M.H M.σ M.lam lam (fun τ => (M.enum τ).1) (fun τ => (m τ).2.2.1) (fun τ => (m τ).2.2.2)
    (fun τ i => by rw [hl τ i, hε τ])
  haveI : FiniteDimensional ℂ (⨂[ℂ] τ, M.H τ) := inferInstance
  haveI : FiniteDimensional ℂ (Module.Dual ℂ (weylSub V.rank lam)) := Module.Finite.equiv Φ.symm
  haveI : FiniteDimensional ℂ (weylSub V.rank lam) := (Module.finite_dual_iff ℂ).1 this
  let ev := Module.evalEquiv ℂ (weylSub V.rank lam)
  refine ⟨(E.trans Φ.dualMap).trans ev.symm, fun u w => ?_⟩
  apply ev.injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  ext φ
  rw [LinearEquiv.dualMap_apply, hE, LinearMap.comp_apply]
  have key : (PiTensorProduct.map fun τ => ((M.σ τ ((u τ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) :
      M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)) (Φ φ) = Φ ((weylRep V.rank lam).dual u⁻¹ φ) := (hΦ u⁻¹ φ).symm
  rw [key]
  obtain ⟨y, hy⟩ := ev.surjective (Φ.dualMap (E w))
  rw [← hy, LinearEquiv.symm_apply_apply]
  have h2 : E w (Φ ((weylRep V.rank lam).dual u⁻¹ φ)) = ev y ((weylRep V.rank lam).dual u⁻¹ φ) := by
    rw [hy]; rfl
  rw [h2]
  show ((weylRep V.rank lam).dual u⁻¹ φ) y = φ (weylRep V.rank lam u y)
  rw [Representation.dual_apply, inv_inv]
  rfl

end Core2

theorem weyl_cast {ι : Type} [Fintype ι] [DecidableEq ι] (n n' : ℕ) (h : n = n') (lam : ι → ℕ → ℤ) :
    ∃ e : weylSub (ι := ι) n lam ≃ₗ[ℂ] weylSub n' lam, ∀ u F,
      e (weylRep n lam u F) = weylRep n' lam (fun τ => castU h (u τ)) (e F) := by
  subst h
  exact ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem cast_inv : ∀ (X Y : LSp D) (h : X = Y) (a : GA D X.sp),
    cast (congrArg (fun X : LSp D => GA D X.sp) h) a⁻¹ = (cast (congrArg (fun X : LSp D => GA D X.sp) h) a)⁻¹ := by
  intro X Y h a
  subst h
  rfl

theorem xPt_inv (ch : Choice R) (g : Gc D.what₂.Tau (rowSizes D)) : xPt ch g⁻¹ = (xPt ch g)⁻¹ := by
  have hk : ((kappa ch.W g⁻¹).2 0 : GA D (columnBlock R.toLevCh D.R.m).sp) =
      ((kappa ch.W g).2 0 : GA D (columnBlock R.toLevCh D.R.m).sp)⁻¹ :=
    congrArg (fun x => x.2 0) (map_inv (kappa ch.W) g)
  exact (congrArg (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh))) hk).trans
    (cast_inv (columnBlock R.toLevCh D.R.m) _ (colY_m R.toLevCh) ((kappa ch.W g).2 0))

theorem coefBase [DecidableEq D.what₂.Tau] (ch : Choice R) (hθ : R.models_inf) (hc : R.models_cX) (hpr : R.models_prX)
    (hO : ch.W.Over R) (h0 : PosOnb ch.W (.grid 0 D.R.m)) :
    ∃ B : Module.Dual ℂ (weylSub ((rowSizes D).nC (0 : Fin ((rowSizes D).m + 1))) (baseWt (rowEntries D ch.sc.cGap))) ≃ₗ[ℂ]
        Module.Dual ℂ R.cX.W,
      ∀ g φ, B ((baseRep (rowEntries D ch.sc.cGap)).dual g φ) =
        B φ ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) ((kappa ch.W g).2 0))⁻¹ := by
  obtain ⟨A0, hA0⟩ := core R.MX R.θ R.cX R.prX hθ (GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) _) hc hpr
    (baseWt (rowEntries D ch.sc.cGap)) (fun τ i => GlobalTheory.T.highestWeight_basePar_eq_neg_lowestKType D ch.sc.cGap R.MX τ i)
  obtain ⟨e, he⟩ := weyl_cast (ι := D.what₂.Tau) _ _ (rank_X ch) (baseWt (rowEntries D ch.sc.cGap))
  refine ⟨(A0.trans e.symm).dualMap, fun g φ => ?_⟩
  ext w
  show ((baseRep (rowEntries D ch.sc.cGap)).dual g φ) (e.symm (A0 w)) = φ (e.symm (A0 (R.cX.ρ (xPt ch g)⁻¹ w)))
  rw [← xPt_inv, xPt_eq ch hO h0, hA0, Representation.dual_apply]
  have h1 := he (g⁻¹.2 0) (e.symm (A0 w))
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]
  rfl

end GlobalTheory.CoefBase
end
end
end
