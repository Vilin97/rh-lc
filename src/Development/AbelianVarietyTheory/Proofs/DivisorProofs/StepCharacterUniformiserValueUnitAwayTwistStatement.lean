module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsMulOfCondExp
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRamifiedPlacesHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSubOneMemPow

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

open Classical

namespace GlobalTheory.ValUnitLevel
open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing GlobalTheory.ChiUnit Formalism.L2.Host GlobalTheory.ValUnit

theorem isUnit_mk_pow {R : Type} [CommRing R] {P : Ideal R} (hP : P.IsMaximal) {a : R} (ha : a ∉ P) (n : ℕ) :
    IsUnit (Ideal.Quotient.mk (P ^ n) a) := by
  obtain ⟨y, i, hi, e⟩ := hP.exists_inv ha
  have hnil : IsNilpotent (Ideal.Quotient.mk (P ^ n) i) :=
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hi n⟩
  have h1 : Ideal.Quotient.mk (P ^ n) y * Ideal.Quotient.mk (P ^ n) a = 1 - Ideal.Quotient.mk (P ^ n) i := by
    rw [← map_mul, eq_sub_iff_add_eq, ← map_add (f := _), e, map_one]
  exact isUnit_of_mul_isUnit_right (h1 ▸ hnil.isUnit_one_sub)

theorem exists_pow_sub_one_mem_pow {L : Type} [Field L] [NumberField L] (S : Finset (HeightOneSpectrum (𝓞 L))) (a : 𝓞 L)
    (n : HeightOneSpectrum (𝓞 L) → ℕ) (ha : ∀ w ∈ S, a ∉ w.asIdeal) :
    ∃ M : ℕ, 0 < M ∧ ∀ w ∈ S, a ^ M - 1 ∈ w.asIdeal ^ n w := by
  have key : ∀ w ∈ S, ∃ m : ℕ, 0 < m ∧ Ideal.Quotient.mk (w.asIdeal ^ n w) a ^ m = 1 := fun w hw => by
    haveI : Finite (𝓞 L ⧸ w.asIdeal ^ n w) :=
      Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ w.ne_bot)
    obtain ⟨u, hu⟩ := isUnit_mk_pow w.isMaximal (ha w hw) (n w)
    obtain ⟨m, hm, e⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite u)
    exact ⟨m, hm, by rw [← hu]; simpa using congrArg Units.val e⟩
  choose! m hm e using key
  refine ⟨∏ w ∈ S, m w, Finset.prod_pos hm, fun w hw => ?_⟩
  rw [← Ideal.Quotient.eq, map_pow, map_one, ← Finset.mul_prod_erase _ _ hw, pow_mul, e w hw, one_pow]

theorem locK_eq_one_of_levelLe {L : Type} [Field L] [NumberField L] {χ : Formalism.L2.Host.HChar L} {w : HeightOneSpectrum (𝓞 L)}
    {n : ℕ} (h : χ.LevelLe w n) (k : Lˣ) (a : 𝓞 L) (hk : (k : L) = a) (ha0 : a ∉ w.asIdeal)
    (ha : a - 1 ∈ w.asIdeal ^ n) : χ.locK w k = 1 := by
  refine h _ ?_ ?_
  · unfold IsUnitAt
    rw [GlobalTheory.TypeValues.val_atFin w k a hk]
    exact w.intValuation_eq_one_iff.2 ha0
  · have h1 : ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1 =
        algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L (a - 1)) := by
      rw [map_sub, map_sub, map_one, map_one]
      congr 1
      show algebraMap L (w.adicCompletion L) (k : L) = _
      rw [hk]
    have h2 : Valued.v (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L (a - 1))) =
        w.valuation L (algebraMap (𝓞 L) L (a - 1)) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [h1, h2, w.valuation_of_algebraMap, w.intValuation_le_pow_iff_mem]
    exact ha

theorem unitOff_val : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (I : Type) [Fintype I]
    (φ : I → L →+* ℂ) (n : I → ℤ) (v : HeightOneSpectrum (𝓞 L)) (q : ℕ), χ.HasInf φ n → χ.UnrAt v →
    (q : 𝓞 L) ∈ v.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff q ((χ.val v : ℂˣ) : ℂ) := by
  intro L _ _ χ I _ φ n v q hinf hv hq
  have hfin := GlobalTheory.Mem.UnrAe.finite_ramified χ
  choose nl hnl using GlobalTheory.Mem.UnrAe.exists_levelLe χ
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · exact ⟨Units.ne_zero _, 1, by simpa using isIntegral_zero, by simpa using isIntegral_zero⟩
  obtain ⟨h, a, hh, ha0, ha⟩ := exists_pow_eq_span v
  have hav : a ∈ v.asIdeal := Ideal.pow_le_self hh.ne' (ha ▸ Ideal.mem_span_singleton_self a)
  have haw : ∀ w : HeightOneSpectrum (𝓞 L), w ≠ v → a ∉ w.asIdeal := fun w hw hm => by
    have h1 : v.asIdeal ^ h ≤ w.asIdeal := by rw [ha, Ideal.span_singleton_le_iff_mem]; exact hm
    have h2 : v.asIdeal ≤ w.asIdeal := fun x hx => w.isPrime.mem_of_pow_mem h (h1 (Ideal.pow_mem_pow hx h))
    exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h2).symm)
  obtain ⟨b, hb⟩ : a ∣ (q : 𝓞 L) ^ h := Ideal.mem_span_singleton.1 (ha ▸ Ideal.pow_mem_pow hq h)
  have hvS : v ∉ hfin.toFinset := by simpa using hv
  have hne : ∀ w ∈ hfin.toFinset, w ≠ v := fun w hw e => hvS (e ▸ hw)
  obtain ⟨M, hM, hM1⟩ := exists_pow_sub_one_mem_pow hfin.toFinset a nl fun w hw => haw w (hne w hw)
  have hc0 : a ^ M ≠ 0 := pow_ne_zero _ ha0
  have hk0 : ((a ^ M : 𝓞 L) : L) ≠ 0 := by exact_mod_cast hc0
  set k : Lˣ := Units.mk0 _ hk0 with hk
  have hord : ∀ w : HeightOneSpectrum (𝓞 L), ordF w k = -WithZero.log (w.intValuation (a ^ M)) := fun w => by
    show -WithZero.log (w.valuation L (algebraMap (𝓞 L) L (a ^ M))) = _
    rw [HeightOneSpectrum.valuation_of_algebraMap]
  have hp := GlobalTheory.TypeValues.productRule χ hfin.toFinset (fun w hw => by simpa using hw) k
  rw [Finset.prod_eq_one (fun w hw => locK_eq_one_of_levelLe (hnl w) k (a ^ M) rfl
      (fun hm => haw w (hne w hw) (w.isPrime.mem_of_pow_mem M hm)) (hM1 w hw)), mul_one,
    finprod_eq_single _ v (fun w hw => by
      rw [hord, HeightOneSpectrum.intValuation_eq_one_iff.2 (fun hm => haw w hw (w.isPrime.mem_of_pow_mem M hm))]
      simp), finprod_eq_if, if_pos hvS] at hp
  have hpos : 0 < ordF v k := by
    rw [hord]
    have h0 : v.intValuation (a ^ M) ≠ 0 := v.intValuation_ne_zero _ hc0
    have h3 := (v.intValuation_le_pow_iff_mem (a ^ M) 1).2 (by
      rw [pow_one]; exact Ideal.pow_mem_of_mem _ hav M hM)
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at h3
    push_cast at h3
    omega
  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le hpos.le
  rw [he, zpow_natCast] at hp
  refine unitOff_of_pow (k := e) (by omega) ?_
  have hp' := congrArg (Units.val : ℂˣ → ℂ) hp
  rw [Units.val_mul, Units.val_one, Units.val_pow_eq_pow_val, hinf] at hp'
  rw [eq_inv_of_mul_eq_one_right hp']
  refine unitOff_inv (unitOff_prod _ _ fun i _ => unitOff_zpow (unitOff_div_norm ?_) _)
  have hi : ∀ x : 𝓞 L, IsIntegral ℤ (φ i (algebraMap (𝓞 L) L x)) := fun x =>
    (RingOfIntegers.isIntegral_coe x).map (φ i).toIntAlgHom
  show UnitOff q (φ i (algebraMap (𝓞 L) L (a ^ M)))
  rw [map_pow, map_pow]
  refine unitOff_pow (unitOff_of_mul_eq (m := h) (hi a) (hi b) ?_ hq0.ne') M
  rw [← map_mul, ← map_mul, ← hb, map_pow, map_pow, map_natCast, map_natCast]

end GlobalTheory.ValUnitLevel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfUnitOffEmbedding

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

theorem GlobalTheory.Square.isAwayUnit_of_unitOff_embedding : ∀ {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (x : K) (q m : ℕ), 0 < q → q ∣ m →
    GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff q (σ x) → GlobalTheory.Square.IsAwayUnit m x := by
  intro K _ _ σ x q m hq hqm h
  obtain ⟨hx0, n, h1, h2⟩ := h
  have hx : x ≠ 0 := fun h0 => hx0 (by rw [h0, map_zero])
  have hinj : Function.Injective σ.toIntAlgHom := σ.injective
  have i1 : (q : K) ^ n * x ∈ integralClosure ℤ K := by
    rw [mem_integralClosure_iff, ← isIntegral_algHom_iff σ.toIntAlgHom hinj]
    simpa using h1
  have i2 : (q : K) ^ n * x⁻¹ ∈ integralClosure ℤ K := by
    rw [mem_integralClosure_iff, ← isIntegral_algHom_iff σ.toIntAlgHom hinj]
    simpa using h2
  set a : 𝓞 K := ⟨_, i1⟩ with ha_def
  set b : 𝓞 K := ⟨_, i2⟩ with hb_def
  have ha : algebraMap (𝓞 K) K a = (q : K) ^ n * x := rfl
  have hb : algebraMap (𝓞 K) K b = (q : K) ^ n * x⁻¹ := rfl
  obtain ⟨d, rfl⟩ := hqm
  refine GlobalTheory.Square.AwayClosure.of_integral (k := n) (l := n) (a := a * (d : 𝓞 K) ^ n)
    (b := b * (d : 𝓞 K) ^ n) hx ?_ ?_
  · rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_natCast, ha]
    push_cast
    ring
  · rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_natCast, hb]
    push_cast
    ring
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepCharacterUniformiserValueUnitAwayTwist

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

namespace GlobalTheory.TwistStepVal

theorem isAwayUnit_loc {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] (σ : K →+* ℂ)
    (χ : Formalism.L2.Host.HChar L) {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n : I → ℤ} (hinf : χ.HasInf φ n)
    {w : HeightOneSpectrum (𝓞 L)} (hw : χ.UnrAt w) (y : (w.adicCompletion L)ˣ) (hy : Formalism.L2.Host.IsUnifAt w y)
    {m : ℕ} (hm : Ideal.absNorm w.asIdeal ∣ m) {x : K} (hx : σ x = ((χ.loc w y : ℂˣ) : ℂ)) :
    GlobalTheory.Square.IsAwayUnit m x := by
  have hq : 0 < Ideal.absNorm w.asIdeal :=
    Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  refine GlobalTheory.Square.isAwayUnit_of_unitOff_embedding σ x _ m hq hm ?_
  rw [hx, Formalism.L2.Host.HChar.val_eq χ hw y hy]
  exact GlobalTheory.ValUnitLevel.unitOff_val L χ I φ n w _ hinf hw (Ideal.absNorm_mem _)

theorem step_val : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (W : G.Weil) (S : GridChoice W Set.univ) {μ₀ : T},
    Lc.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
      (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      (Lc.C.mu0 j).UnrAt (GlobalTheory.AdelicU.splitPrime τ) → (G.ch.chiH (D.R.m - i)).UnrAt (GlobalTheory.AdelicU.splitPrime τ) →
      GlobalTheory.AdelicU.splitPrime τ ∈ twPl G t →
      ∃ x : D.what₂.LL, D.what₂.embLL x = ((chrW (GlobalTheory.SqStep.chs G i j t).ν τ (unifAt v) : ℂˣ) : ℂ) ∧
        GlobalTheory.Square.IsAwayUnit (Qn G t) x := by
  intro D T Lc sc G W S μ₀ hL hN i j t v τ hμ hχ htw
  rw [GlobalTheory.SqStepArith.chrW_chs G hL]
  have hy : Formalism.L2.Host.IsUnifAt (GlobalTheory.AdelicU.splitPrime τ)
      (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom (unifAt v)) := by
    show Valued.v (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ) ((unifAt v : (Fv D.host.F v)ˣ) : Fv D.host.F v))
      = WithZero.exp (-1 : ℤ)
    rw [GlobalTheory.LFun.SplitTie.valued_complMap τ (GlobalTheory.AdelicU.splitPrime_under τ), GlobalTheory.ChrWUnif.valued_unifAt]
  generalize Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom (unifAt v) = y at hy ⊢
  have hm : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have e : ((nuH G t i j).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) =
      ((Lc.C.mu0 j).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) * ((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) *
        ((G.ch.chiH (D.R.m - i)).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ)⁻¹ := by
    simp [nuH, Formalism.L2.Host.HChar.loc, div_eq_mul_inv]
  obtain ⟨a, ha⟩ := hN.chars.mu0 j (GlobalTheory.AdelicU.splitPrime τ) y
  obtain ⟨b, hb⟩ := hN.chars.xi t (GlobalTheory.AdelicU.splitPrime τ) y
  obtain ⟨c, hc⟩ := hN.chars.chi (D.R.m - i) hm (Nat.sub_le _ _) (GlobalTheory.AdelicU.splitPrime τ) y
  have hQ : 0 < Qn G t := Finset.prod_pos fun w _ =>
    Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hdvd : Ideal.absNorm (GlobalTheory.AdelicU.splitPrime τ).asIdeal ∣ Qn G t :=
    Finset.dvd_prod_of_mem (fun w : HeightOneSpectrum (𝓞 D.host.E) => Ideal.absNorm w.asIdeal) htw
  refine ⟨a * b * c⁻¹, by rw [e, map_mul, map_mul, map_inv₀, ha, hb, hc], ?_⟩
  obtain ⟨n, -, hn⟩ := (Lc.C.isMu0 j).inf
  have ua := isAwayUnit_loc D.what₂.embLL _ hn hμ y hy hdvd ha
  have uc := isAwayUnit_loc D.what₂.embLL _ (G.ch.inf _ hm (Nat.sub_le _ _)) hχ y hy hdvd hc
  obtain ⟨k, hk, hξ⟩ := hL.xi_fin t
  have ub : GlobalTheory.Square.IsAwayUnit (Qn G t) b := by
    refine GlobalTheory.Square.AwayClosure.of_pow_eq_one _ hk (D.what₂.embLL.injective ?_)
    rw [map_pow, hb, map_one, ← Units.val_pow_eq_pow_val]
    have h1 : (Lc.xiH t ^ k).loc (GlobalTheory.AdelicU.splitPrime τ) y = 1 := by
      rw [show Lc.xiH t ^ k = 1 from hξ]; rfl
    rw [← Units.val_one, ← h1]
    simp [Formalism.L2.Host.HChar.loc]
  exact GlobalTheory.Square.AwayClosure.mul (GlobalTheory.Square.AwayClosure.mul ua ub) (GlobalTheory.Square.AwayClosure.inv hQ uc)

end GlobalTheory.TwistStepVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepCharacterUniformiserValueUnitAwayTwistStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)


theorem _root_.GlobalTheory.T.stepCharacter_uniformiserValue_unit_away_twist : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (W : G.Weil) (S : GridChoice W Set.univ) {μ₀ : T},
    Lc.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
      (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      (Lc.C.mu0 j).UnrAt (GlobalTheory.AdelicU.splitPrime τ) → (G.ch.chiH (D.R.m - i)).UnrAt (GlobalTheory.AdelicU.splitPrime τ) →
      GlobalTheory.AdelicU.splitPrime τ ∈ twPl G t →
      ∃ x : D.what₂.LL, D.what₂.embLL x = ((chrW (GlobalTheory.SqStep.chs G i j t).ν τ (unifAt v) : ℂˣ) : ℂ) ∧
        GlobalTheory.Square.IsAwayUnit (Qn G t) x := by
  first | exact @GlobalTheory.TwistStepVal.step_val | exact GlobalTheory.TwistStepVal.step_val | (intros; apply GlobalTheory.TwistStepVal.step_val <;> assumption)
end
end
