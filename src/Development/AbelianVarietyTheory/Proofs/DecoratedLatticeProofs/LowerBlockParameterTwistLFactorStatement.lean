module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharTameAtOfFactorsThroughResidue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKCongr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SegmentsBoundsAndDoublingLFactorStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitProjectionUnderEqResidueCardEqAbsNorm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterTwistNextTargetChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftsCharOfResidueCharAtSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Mathlib.Algebra.Order.Star.Int
import ReciprocityTheory.Automorphisms.PlaceA
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharQuotientUnramifiedAtTwistPlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.ChainTw.QuotUnr

theorem loc_eq_of_isRes {D : D7} {H H' : Formalism.L2.Host.HChar D.host.E} {PP : Pl D.host.E} {a : (kP PP)ˣ →* ℂˣ}
    (h : IsRes H PP a) (h' : IsRes H' PP a) (x : (PP.adicCompletion D.host.E)ˣ) (hx : Formalism.L2.Host.IsUnitAt PP x) :
    H.loc PP x = H'.loc PP x := by
  have ht := GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes D H PP a h
  have ht' := GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes D H' PP a h'
  obtain ⟨b, hb⟩ := GlobalTheory.GaussModulus.exists_int_approx PP (x := (x : PP.adicCompletion D.host.E)) (le_of_eq hx) 1
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hbv : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E)) = 1 := by
    have hx1 : Valued.v (x : PP.adicCompletion D.host.E) = 1 := hx
    have e : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E)) = Valued.v (x : PP.adicCompletion D.host.E) :=
      Valuation.map_eq_of_sub_lt _ (by rw [Valuation.map_sub_swap, hx1]; exact lt_of_le_of_lt hb hlt)
    rw [e, hx1]
  have hbP : b ∉ PP.asIdeal := by
    intro hm
    have h1 : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E b) < 1 := (PP.valuation_lt_one_iff_mem b).2 hm
    have h2 : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E b) = 1 := by
      rw [← GlobalTheory.GaussModulus.valued_algebraMap]; exact hbv
    exact (ne_of_lt h1) h2
  have hb0 : (b : D.host.E) ≠ 0 := fun h0 => hbP (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  let kb : D.host.Eˣ := Units.mk0 _ hb0
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  letI : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  have hu0 : (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := fun h0 => hbP (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  let u : (kP PP)ˣ := Units.mk0 _ hu0
  have e1 := h b kb u rfl rfl
  have e2 := h' b kb u rfl rfl

  obtain ⟨y, hy⟩ : ∃ y : (PP.adicCompletion D.host.E)ˣ, y = x * (Formalism.L2.Host.atFin PP kb)⁻¹ := ⟨_, rfl⟩
  have hkv : Valued.v ((Formalism.L2.Host.atFin PP kb : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) = 1 := hbv
  have hyu : Formalism.L2.Host.IsUnitAt PP y := by
    show Valued.v ((y : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) = 1
    rw [hy, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hkv, inv_one, mul_one]
    exact hx
  have hy1 : Valued.v ((y : PP.adicCompletion D.host.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have hk0 : ((Formalism.L2.Host.atFin PP kb : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) =
        algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E) := rfl
    have e : (y : PP.adicCompletion D.host.E) - 1 =
        ((x : PP.adicCompletion D.host.E) - algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E)) *
          (algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E))⁻¹ := by
      have hne : algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E) ≠ 0 := by
        rw [← hk0]; exact Units.ne_zero _
      rw [hy, Units.val_mul, Units.val_inv_eq_inv_val, hk0, sub_mul, mul_inv_cancel₀ hne]
    rw [e, map_mul, map_inv₀, hbv, inv_one, mul_one]
    exact hb
  have hxy : x = Formalism.L2.Host.atFin PP kb * y := by rw [hy, mul_left_comm, mul_inv_cancel, mul_one]
  rw [hxy, map_mul, map_mul, ht y hyu hy1, ht' y hyu hy1, mul_one, mul_one]
  exact e1.symm.trans e2

end GlobalTheory.ChainTw.QuotUnr


open GlobalTheory.ChainTw.QuotUnr in
theorem GlobalTheory.ChainTw.quot_unrAt_twist : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ PP ∈ w.Q, ∀ i j : ℕ, 1 ≤ i → i ≤ D.R.m → 1 ≤ j → j ≤ D.R.m → GlobalTheory.LFun.UnrAt (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP := by
  intro D c w hw PP hPP i j hi1 him hj1 hjm
  have hPg : PP ∈ c.Pg := by classical rw [hw.union]; exact Finset.mem_union_right _ hPP
  obtain ⟨Hi, hci, hri⟩ := hw.com.res ⟨i - 1, by omega⟩
  obtain ⟨Hj, hcj, hrj⟩ := hw.com.res ⟨j - 1, by omega⟩
  simp only [Nat.sub_add_cancel hi1, Nat.sub_add_cancel hj1] at hci hri hcj hrj
  have ri := hri PP hPg
  have rj := hrj PP hPg
  rw [hw.chiQ i PP hPP] at ri
  rw [hw.chiQ j PP hPP] at rj
  intro x hx
  have li := DFunLike.congr_fun (GlobalTheory.LFun.locChar_eq_of_chrEq hci PP) x
  have lj := DFunLike.congr_fun (GlobalTheory.LFun.locChar_eq_of_chrEq hcj PP) x
  have split : GlobalTheory.LFun.locChar (c.μ i * (c.μ j)⁻¹) PP x =
      GlobalTheory.LFun.locChar (c.μ i) PP x * (GlobalTheory.LFun.locChar (c.μ j) PP x)⁻¹ := by
    simp only [GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
  rw [split, li, lj, loc_eq_of_isRes ri rj x hx, mul_inv_cancel]

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharQuotientUnramifiedAtTwistPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.hecke_char_quotient_unramified_at_twist_place : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ PP ∈ w.Q, ∀ i j : ℕ, 1 ≤ i → i ≤ D.R.m → 1 ≤ j → j ≤ D.R.m → GlobalTheory.LFun.UnrAt (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP := by
  first | exact @GlobalTheory.ChainTw.quot_unrAt_twist | exact GlobalTheory.ChainTw.quot_unrAt_twist | (intros; apply GlobalTheory.ChainTw.quot_unrAt_twist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeckeCharAtUniformizerIdeleEqValue

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocUnifVal

theorem valued_eq_of_unif {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (ϖ : (Fv D.host.F v)ˣ)
    (hϖ : ValuativeRel.valuation (Fv D.host.F v) (ϖ : Fv D.host.F v) = ValuativeRel.uniformizer (Fv D.host.F v)) :
    Valued.v (ϖ : Fv D.host.F v) = WithZero.exp (-1 : ℤ) := by
  haveI : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have key : ∀ a b : Fv D.host.F v, ValuativeRel.valuation (Fv D.host.F v) a ≤ ValuativeRel.valuation (Fv D.host.F v) b ↔
      Valued.v a ≤ Valued.v b := fun a b =>
    (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (Fv D.host.F v)) a b).symm.trans
      (Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ)))) a b)
  have hlt : Valued.v (ϖ : Fv D.host.F v) < 1 := by
    have h1 : ValuativeRel.valuation (Fv D.host.F v) (ϖ : Fv D.host.F v) < ValuativeRel.valuation (Fv D.host.F v) 1 := by
      rw [map_one, hϖ]; exact ValuativeRel.uniformizer_lt_one
    rw [← map_one (Valued.v : Valuation (Fv D.host.F v) _)]
    exact lt_of_not_ge fun h => (not_le.2 h1) ((key _ _).2 h)
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer D.host.F
  have hx : Valued.v (algebraMap D.host.F (Fv D.host.F v) π) = WithZero.exp (-1 : ℤ) := by
    rw [ReciprocityTheory.Aut.adic_valued_algebraMap, hπ]
  have hle : WithZero.exp (-1 : ℤ) ≤ Valued.v (ϖ : Fv D.host.F v) := by
    rw [← hx]
    refine (key _ _).1 ?_
    rw [hϖ, ValuativeRel.le_uniformizer_iff, ← map_one (ValuativeRel.valuation (Fv D.host.F v))]
    refine lt_of_not_ge fun h => ?_
    have := (key _ _).1 h
    rw [map_one, hx] at this
    exact absurd this (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
  have h0 : Valued.v (ϖ : Fv D.host.F v) ≠ 0 := (map_ne_zero _).2 ϖ.ne_zero
  rw [← WithZero.exp_log h0] at hlt hle ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [WithZero.exp_le_exp] at hle
  congr 1
  omega

theorem value_eq_val : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP → ∀ (x : (AE D)ˣ) (ϖ : (Fv D.host.F v)ˣ), IsLocUnif φ x ϖ → ∀ χ : (AE D)ˣ →* Circle, GlobalTheory.LFun.UnrAt (F := D.host.F) χ PP → Circle.toUnits (χ x) = GlobalTheory.LFun.val (F := D.host.F) χ PP := by
  intro D v φ PP hφ x ϖ hloc χ hχ
  obtain ⟨e, he, hx1, hx2, hx3⟩ := hloc
  have h : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v := (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hφ).1.symm
  have hAt : Formalism.L2.NTheta.IsIdemAt e PP := (((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ PP hφ).2.2 e he).1
  have hP : IsPrimeIdem PP e (e + cA D e) := Or.inl ⟨hAt, rfl⟩
  have hxe : e * ((x : AE D) - 1) = (x : AE D) - 1 := by linear_combination -hx1
  obtain ⟨y, hy, hxy⟩ := GlobalTheory.WeilAtPlace.exists_eq_locIdele (GlobalTheory.WeilAtPlace.isPrimeIdem_infPart hP)
    (GlobalTheory.LFun.finPart_of_isPrimeIdem hP) x hxe
  have hτ : GlobalTheory.AdelicU.splitPrime (GlobalTheory.SplitProjChart.emb φ) = PP := (GlobalTheory.ResLift.eq_splitPrime hφ).symm
  have hc : (y : PP.adicCompletion D.host.E) = GlobalTheory.LFun.complMap h (ϖ : Fv D.host.F v) := by
    have e1 : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (finPart D (x : AE D)) =
        GlobalTheory.AdelicU.compFin D.host.F D.host.E v (x : AE D) := by
      rw [GlobalTheory.FinPl.LatMem.compFin_eq_compAt]; rfl
    rw [hy, GlobalTheory.LFun.compAt_apply, GlobalTheory.LFun.finAdEquiv_apply h, e1,
      GlobalTheory.LFun.ConjPlace.toCompl_eq (GlobalTheory.AdelicU.isCMExt_host D) h hτ, GlobalTheory.SplitProjChart.splitProj_emb, ← hx2]
    rfl
  have hu : Formalism.L2.Host.IsUnifAt PP y := by
    unfold Formalism.L2.Host.IsUnifAt
    rw [hc, GlobalTheory.LFun.ConjPlace.valued_complMap (GlobalTheory.AdelicU.isCMExt_host D) h hτ]
    exact GlobalTheory.LocUnifVal.valued_eq_of_unif ϖ hx3
  have := hχ.locChar_eq_val hu
  rw [← this, hxy]
  rfl

end GlobalTheory.LocUnifVal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeckeCharAtUniformizerIdeleEqValueStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unramifiedHeckeChar_at_uniformizerIdele_eq_value : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP → ∀ (x : (AE D)ˣ) (ϖ : (Fv D.host.F v)ˣ), IsLocUnif φ x ϖ → ∀ χ : (AE D)ˣ →* Circle, GlobalTheory.LFun.UnrAt (F := D.host.F) χ PP → Circle.toUnits (χ x) = GlobalTheory.LFun.val (F := D.host.F) χ PP := by
  first | exact @GlobalTheory.LocUnifVal.value_eq_val | exact GlobalTheory.LocUnifVal.value_eq_val | (intros; apply GlobalTheory.LocUnifVal.value_eq_val <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterTwistLFactor

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.QParL

theorem seg_eq_segL : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP →
    ∀ (x : (AE D)ˣ) (ϖ : (Fv D.host.F v)ˣ), IsLocUnif φ x ϖ → ∀ z t, GlobalTheory.LFun.seg PP z t = GlobalTheory.ParHecke.segL ϖ z t := by
  intro D v φ PP hφ x ϖ hx z t
  obtain ⟨-, hq⟩ := GlobalTheory.PlaceProjAt.under_resCard D v φ PP hφ
  obtain ⟨e, -, -, -, hϖ⟩ := hx
  have hn := GlobalTheory.GLDoubling.nabs_unif hϖ
  unfold GlobalTheory.LFun.seg GlobalTheory.ParHecke.segL
  refine Multiset.map_congr rfl fun n _ => ?_
  congr 1
  ext
  rw [GlobalTheory.SmGL.val_absPow, hn, hq, GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), ← Complex.cpow_neg]
  congr 1
  ring

theorem qPar_succ {D : D7} (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) (k : ℕ) :
    qPar c PP x (k + 1) = (qPar c PP x k).map (· * (Circle.toUnits (c.chS (k + 1) x) * (Circle.toUnits (c.chT (k + 1) x))⁻¹)) +
      GlobalTheory.LFun.seg PP (Circle.toUnits (c.chS (k + 1) x)) D.R.t := rfl

theorem card_qPar {D : D7} (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) (k : ℕ) : (qPar c PP x k).card = k * D.R.t := by
  induction k with
  | zero => simp [qPar]
  | succ k ih => rw [qPar_succ, Multiset.card_add, Multiset.card_map, ih, GlobalTheory.LFun.card_seg]; ring

theorem seg_map_mul {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (z u : ℂˣ) (t : ℕ) :
    (GlobalTheory.LFun.seg w z t).map (· * u) = GlobalTheory.LFun.seg w (z * u) t := by
  simp only [GlobalTheory.LFun.seg, Multiset.map_map, Function.comp_def]
  exact Multiset.map_congr rfl fun i _ => mul_right_comm _ _ _

theorem sum_map_mul {ι : Type} (s : Finset ι) (f : ι → Multiset ℂˣ) (u : ℂˣ) :
    (∑ i ∈ s, f i).map (· * u) = ∑ i ∈ s, (f i).map (· * u) :=
  map_sum (Multiset.mapAddMonoidHom (· * u)) f s

theorem qPar_closed {D : D7} (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) (k : ℕ) :
    qPar c PP x k = ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.seg PP (Circle.toUnits ((c.μ i * c.eps k) x)) D.R.t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [qPar_succ, ih, sum_map_mul, Finset.sum_Icc_succ_top (by omega)]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [seg_map_mul, ← GlobalTheory.ChainOnto.ParClosed.eps_succ]
      congr 1
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
      ext
      simp only [Units.val_mul]
      ring
    · rw [GlobalTheory.ChainOnto.ParClosed.chS_succ]

theorem qPar_twist {D : D7} (c : Com D) (PP : Pl D.host.E) (x : (AE D)ˣ) (k : ℕ) :
    (qPar c PP x k).map (· * (Circle.toUnits (c.chT (k + 1) x))⁻¹) =
      ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.seg PP (Circle.toUnits ((c.μ i * (c.μ (k + 1))⁻¹) x)) D.R.t := by
  rw [qPar_closed, sum_map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [seg_map_mul, GlobalTheory.ChainOnto.ParClosed.chT_succ]
  congr 1
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
  rw [_root_.mul_inv_rev]
  group

theorem invNormFactor_eq (q t k : ℕ) :
    GlobalTheory.GLDoubling.invNormFactor q (k * t) ((t : ℂ) / 2) =
      ((∏ n ∈ Finset.Ioc t ((k + 1) * t), (1 - ((q : ℝ) ^ n)⁻¹) : ℝ) : ℂ) := by
  unfold GlobalTheory.GLDoubling.invNormFactor
  push_cast
  rw [show (k + 1) * t = t + k * t by ring]
  generalize k * t = m
  have h1 : Finset.Ioc t (t + m) = (Finset.Icc 1 m).map (addLeftEmbedding t) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_Icc, addLeftEmbedding_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨n - t, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩; constructor <;> omega
  rw [h1, Finset.prod_map]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : (2 * ((t : ℂ) / 2) + (i : ℂ)) = ((addLeftEmbedding t i : ℕ) : ℂ) := by
    simp only [addLeftEmbedding_apply]; push_cast; ring
  rw [this, Complex.cpow_neg, Complex.cpow_natCast]

end GlobalTheory.QParL

open GlobalTheory.QParL in
theorem GlobalTheory.ChainTw.qPar_twist_lFactor : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ k < D.R.m, ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ x ϖ, IsLocUnif φ x ϖ → (∀ z t, GlobalTheory.LFun.seg PP z t = GlobalTheory.ParHecke.segL ϖ z t) ∧ (qPar c PP x k).card = k * D.R.t ∧ ∀ α : Fin (k * D.R.t) → ℂˣ, Finset.univ.val.map α = (qPar c PP x k).map (· * (Circle.toUnits (c.chT (k + 1) x))⁻¹) → (∀ i, ‖(α i : ℂ)‖ ≤ (Ideal.absNorm PP.asIdeal : ℝ) ^ (((D.R.t : ℝ) - 1) / 2) ∧ ‖(α i : ℂ)‖⁻¹ ≤ (Ideal.absNorm PP.asIdeal : ℝ) ^ (((D.R.t : ℝ) - 1) / 2)) ∧ GlobalTheory.GLDoubling.lFactor (Ideal.absNorm PP.asIdeal) α ((D.R.t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.lFactor (Ideal.absNorm PP.asIdeal) α⁻¹ ((D.R.t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.invNormFactor (Ideal.absNorm PP.asIdeal) (k * D.R.t) ((D.R.t : ℂ) / 2) = blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ) := by
  intro D c w hw k hk PP hPP v φ hφ x ϖ hx
  refine ⟨seg_eq_segL D v φ PP hφ x ϖ hx, card_qPar c PP x k, fun α hα => ?_⟩
  rw [qPar_twist] at hα
  have hz : ∀ i ∈ Finset.Icc 1 k, Circle.toUnits ((c.μ i * (c.μ (k + 1))⁻¹) x) =
      GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) PP := fun i hi =>
    GlobalTheory.T.unramifiedHeckeChar_at_uniformizerIdele_eq_value D v φ PP hφ x ϖ hx _ (GlobalTheory.T.hecke_char_quotient_unramified_at_twist_place D c w hw PP hPP i (k + 1) (Finset.mem_Icc.1 hi).1
      (by have := (Finset.mem_Icc.1 hi).2; omega) (by omega) (by omega))
  have hα' : Finset.univ.val.map α = ∑ i ∈ Finset.Icc 1 k,
      GlobalTheory.LFun.seg PP (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) PP) D.R.t := by
    rw [hα]; exact Finset.sum_congr rfl fun i hi => by rw [hz i hi]
  obtain ⟨hb, hL⟩ := GlobalTheory.T.segments_bounds_and_doubling_lFactor PP k D.R.t (k * D.R.t)
    (fun i => GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) PP) (fun i => GlobalTheory.LFun.norm_val _ _) α hα'
  refine ⟨hb, ?_⟩
  rw [hL, invNormFactor_eq, blockL, zinv]

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterTwistLFactorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.lower_block_parameter_twist_L_factor : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ k < D.R.m, ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ x ϖ, IsLocUnif φ x ϖ → (∀ z t, GlobalTheory.LFun.seg PP z t = GlobalTheory.ParHecke.segL ϖ z t) ∧ (qPar c PP x k).card = k * D.R.t ∧ ∀ α : Fin (k * D.R.t) → ℂˣ, Finset.univ.val.map α = (qPar c PP x k).map (· * (Circle.toUnits (c.chT (k + 1) x))⁻¹) → (∀ i, ‖(α i : ℂ)‖ ≤ (Ideal.absNorm PP.asIdeal : ℝ) ^ (((D.R.t : ℝ) - 1) / 2) ∧ ‖(α i : ℂ)‖⁻¹ ≤ (Ideal.absNorm PP.asIdeal : ℝ) ^ (((D.R.t : ℝ) - 1) / 2)) ∧ GlobalTheory.GLDoubling.lFactor (Ideal.absNorm PP.asIdeal) α ((D.R.t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.lFactor (Ideal.absNorm PP.asIdeal) α⁻¹ ((D.R.t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.invNormFactor (Ideal.absNorm PP.asIdeal) (k * D.R.t) ((D.R.t : ℂ) / 2) = blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ) := by
  first | exact @GlobalTheory.ChainTw.qPar_twist_lFactor | exact GlobalTheory.ChainTw.qPar_twist_lFactor | (intros; apply GlobalTheory.ChainTw.qPar_twist_lFactor <;> assumption)
end
end
