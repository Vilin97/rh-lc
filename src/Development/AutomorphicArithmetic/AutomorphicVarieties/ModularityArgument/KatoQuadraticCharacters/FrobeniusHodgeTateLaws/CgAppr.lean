module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiQuadAlt
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThNSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsThBActSgDDiamIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogDerivQExpansionMulPrimePowCongr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegralityStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerClassEqImpPowRatio
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerRootOfInvariantTInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeDiamondActionStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorHeckeTQEqUAddVTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorUpperULCommuteScaleOne
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalValueModPrimePowUniqueOddWeightStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsThBSuccCoeffCongStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombinationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeDiamondActionStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob
import Development.AbelianVarietyTheory.Definitions.Foundations.Mdl

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorHeckeTQEqUAddVTwistStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.thetaOperator_heckeT_q_eq_U_add_V_twist : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], Algebra.IsAlgebraic ℚ Ω → (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → 1 ≤ N → ∀ (n w d q : ℕ), Odd w → q.Prime → ¬ q ∣ N * l → ((q : Ω))⁻¹ ∈ A → (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ φ' : HahnSeries ℚ Ω, IsLat 1 φ → IsLat 1 φ' →
  IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
  IsThB X A N l n (X.act l (sgD N l (d * q) : Matrix (Fin 2) (Fin 2) ℤ) b) φ' →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l q b)) (hq ε q φ + ((q : Ω) ^ (w + 1)) • vq q φ') := by
  first | exact @GlobalTheory.HeckeTh.isThB_heckeT | exact GlobalTheory.HeckeTh.isThB_heckeT | (intros; apply GlobalTheory.HeckeTh.isThB_heckeT <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorUpperULCommuteScaleOneStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.thetaOperator_upperU_l_commute_scale_one : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ), Algebra.IsAlgebraic ℚ Ω → (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → 1 ≤ N → Odd w → (l : Ω) ∈ A.nonunits → d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsLat 1 φ →
  IsThB X A N l (n + 1) (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b)) (uq l φ) := by
  first | exact @GlobalTheory.ThHeckeU.isThB_act_heckeU | exact GlobalTheory.ThHeckeU.isThB_act_heckeU | (intros; apply GlobalTheory.ThHeckeU.isThB_act_heckeU <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalModPrimePowCommutesHeckeDiamond

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.ThNHecke

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem inv_natCast_mem (A : ValuationSubring Ω) {l q : ℕ} (hq : q.Prime) (hl : l.Prime) (hql : q ≠ l)
    (hlA : (l : Ω) ∈ A.nonunits) : ((q : Ω))⁻¹ ∈ A := by
  have hcop : Nat.Coprime q l := (Nat.coprime_primes hq hl).mpr hql
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have e : (u : Ω) * (q : Ω) + (v : Ω) * (l : Ω) = 1 := by exact_mod_cast congrArg (fun t : ℤ => (t : Ω)) huv
  have hu : A.valuation (u : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A u)
  have hv : A.valuation (v : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A v)
  have hqle : A.valuation (q : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A q)
  have hl1 : A.valuation (l : Ω) < 1 := (A.mem_nonunits_iff).mp hlA
  have hq1 : A.valuation (q : Ω) = 1 := by
    refine le_antisymm hqle (not_lt.mp fun hlt => ?_)
    have h1 : A.valuation ((u : Ω) * (q : Ω)) < 1 := by
      rw [map_mul]; exact (mul_le_mul' hu le_rfl).trans_lt (by rwa [one_mul])
    have h2 : A.valuation ((v : Ω) * (l : Ω)) < 1 := by
      rw [map_mul]; exact (mul_le_mul' hv le_rfl).trans_lt (by rwa [one_mul])
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [e, map_one] at h3
    exact lt_irrefl _ h3
  rw [← A.valuation_le_one_iff, map_inv₀, hq1, inv_one]

theorem op_mem_B [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (hj : ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) (N l w : ℕ) [Fact l.Prime]
    (hN : 1 ≤ N) (hlN : ¬ l ∣ N) (T : Letter) (hT : admitted N l T) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.op N l T b ∈ X.B N l w := by
  obtain ⟨φ, h1, h2⟩ := hj
  have hA := (GlobalTheory.T.modular_function_tower_integrality ε X ε.injective ⟨φ, h2, h1⟩ l).1
  have hNl : Nat.Coprime N l :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).mpr hlN)
  have hle : X.B N l w ≤ (X.B N l w).comap (X.op N l T) :=
    Submodule.span_le.mpr (fun x hx => Submodule.subset_span
      (StabHecke.op_BSet X hA N w (by omega) hNl T hT x hx))
  exact hle hb

theorem isThB_cong [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [hl : Fact l.Prime]
    (l2 : l ≠ 2) (hN : ¬ l ∣ N) (hN1 : 1 ≤ N) (hlA : (l : Ω) ∈ A.nonunits) (n : ℕ) (b : X.Fn l)
    (φ φ' : HahnSeries ℚ Ω) (h1 : IsThB X A N l n b φ) (h2 : IsThB X A N l n b φ') :
    ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨f, hfI, hfc, hfδ, hfD⟩ := h1
  obtain ⟨f', hf'I, hf'c, hf'δ, hf'D⟩ := h2
  obtain ⟨u, hu⟩ := GlobalTheory.Tower.cls_eq_pow X l n f f' (hfc.symm.trans hf'c)
  have hf0 : (f : X.K) ≠ 0 := f.ne_zero
  have hu0 : (u : X.K) ≠ 0 := u.ne_zero
  have hL : (u : X.K) ^ (l ^ n) = (f : X.K)⁻¹ * f' := by rw [hu]; field_simp
  have hT := GlobalTheory.TInv.sl_T_eq X N l n hl.out l2 hN hN1 (u : X.K) hu0 (by
      intro γ hγ; rw [hL, map_mul, map_inv₀, hfI γ hγ, hf'I γ hγ]) (by
      intro δ hδ hδ'
      obtain ⟨g, hgI, hg⟩ := hfδ δ hδ hδ'
      obtain ⟨g', hg'I, hg'⟩ := hf'δ δ hδ hδ'
      have hsf : X.sl (ofSL δ) (f : X.K) ≠ 0 := by
        intro h0; exact hf0 ((X.sl (ofSL δ)).injective (h0.trans (map_zero _).symm))
      have hg0 : g ≠ 0 := by
        intro h0; rw [h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hg; exact mul_ne_zero hf0 hsf hg
      refine ⟨g' / g, ?_, ?_⟩
      · intro γ hγ; rw [map_div₀, hgI γ hγ, hg'I γ hγ]
      · rw [div_pow, ← hg', ← hg, hu, map_mul, map_pow]; field_simp; ring)
  exact GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong X A l hlA n (f : X.K) (u : X.K) hf0 hu0 hT φ φ' hfD (by rw [← hu]; exact hf'D)

end GlobalTheory.ThNHecke


open GlobalTheory.ThNHecke in
theorem GlobalTheory.CyclotomicQExpansion.thN_hecke : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w d : ℕ), Odd w → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
  (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → ∀ r, CgA A l n ((thN X A N l n d (X.heckeT N l q b)).coeff r)
      ((hq ε q (thN X A N l n d b) + ((q : Ω) ^ (w + 1)) • vq q (thN X A N l n (d * q) b)).coeff r)) ∧
  (∀ r, CgA A l n ((thN X A N l n d (X.heckeU l b)).coeff r) ((uq l (thN X A N l (n + 1) d b)).coeff r)) ∧
  (∀ a : ℕ, a.Coprime N → ∀ r, CgA A l n ((thN X A N l n d (X.diam N l a b)).coeff r) ((thN X A N l n (d * a) b).coeff r)) := by
  intro Ω _ _ _ ε X A N l _ hj hl2 hlN hN hlA n w d hw hd b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have halg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hl : l.Prime := Fact.out
  have stab : ∀ T : Letter, admitted N l T → ∀ c : X.Fn l, c ∈ X.B N l w → X.op N l T c ∈ X.B N l w :=
    fun T hT c hc => op_mem_B ε X hj N l w (by omega) hlN T hT c hc
  have dB : ∀ e : ℕ, e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w →
      X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c ∈ X.B N l w :=
    fun e he c hc => stab (Letter.D e) he c hc
  have exL : ∀ (m e : ℕ), e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w →
      IsThB X A N l m (X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c) (thN X A N l m e c) ∧ IsLat 1 (thN X A N l m e c) :=
    fun m e he c hc => GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l hj hl2 hlN (by omega) hlA m w e hw he c hc
  have ex : ∀ (m e : ℕ), e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w →
      IsThB X A N l m (X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c) (thN X A N l m e c) :=
    fun m e he c hc => (exL m e he c hc).1
  have uniq : ∀ (m : ℕ) (c : X.Fn l), c ∈ X.B N l w → ∀ φ φ' : HahnSeries ℚ Ω,
      IsThB X A N l m c φ → IsThB X A N l m c φ' → ∀ r, CgA A l m (φ.coeff r) (φ'.coeff r) :=
    fun m c _ φ φ' h h' => isThB_cong X A N l hl2 hlN (by omega) hlA m c φ φ' h h'
  refine ⟨?_, ?_, ?_⟩
  · intro q hqP hqd r
    have hqN : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hqP).mpr (fun h => hqd (dvd_mul_of_dvd_left h l))
    have hql : q ≠ l := by
      rintro rfl; exact hqd (dvd_mul_left q N)
    have hqinv := inv_natCast_mem A hqP hl hql hlA
    have hTb : X.heckeT N l q b ∈ X.B N l w := stab (Letter.T q) ⟨hqP, hqd⟩ b hb
    have e1 := exL n d hd b hb
    have e2 := exL n (d * q) (Nat.Coprime.mul_left hd hqN) b hb
    have h2 : IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l q b))
        (hq ε q (thN X A N l n d b) + ((q : Ω) ^ (w + 1)) • vq q (thN X A N l n (d * q) b)) :=
      GlobalTheory.T.thetaOperator_heckeT_q_eq_U_add_V_twist Ω ε X A N l halg hj (by omega) n w d q hw hqP hqd hqinv hlA hl2 hlN hd b hb _ _ e1.2 e2.2 e1.1 e2.1
    exact uniq n _ (dB d hd _ hTb) _ _ (ex n d hd _ hTb) h2 r
  · intro r
    have hUb : X.heckeU l b ∈ X.B N l w := stab Letter.U trivial b hb
    have e1 := exL (n + 1) d hd b hb
    have h2 : IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b))
        (uq l (thN X A N l (n + 1) d b)) :=
      GlobalTheory.T.thetaOperator_upperU_l_commute_scale_one Ω ε X A N l n w d halg hj hl2 (by omega) hw hlA hd hlN b hb _ e1.2 e1.1
    exact uniq n _ (dB d hd _ hUb) _ _ (ex n d hd _ hUb) h2 r
  · intro a ha r
    have hDb : X.diam N l a b ∈ X.B N l w := stab (Letter.D a) ha b hb
    have h1 := (GlobalTheory.KZ.isThB_act_sgD_diam_iff Ω ε X A N l n w a d ha hd b hb _).mp (ex n d hd _ hDb)
    exact uniq n _ (dB (d * a) (Nat.Coprime.mul_left hd ha) b hb) _ _ h1 (ex n (d * a) (Nat.Coprime.mul_left hd ha) b hb) r
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalModPrimePowCommutesHeckeDiamondStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.cuspFunctionalModPrimePow_commutes_hecke_diamond : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w d : ℕ), Odd w → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
  (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → ∀ r, CgA A l n ((thN X A N l n d (X.heckeT N l q b)).coeff r)
      ((hq ε q (thN X A N l n d b) + ((q : Ω) ^ (w + 1)) • vq q (thN X A N l n (d * q) b)).coeff r)) ∧
  (∀ r, CgA A l n ((thN X A N l n d (X.heckeU l b)).coeff r) ((uq l (thN X A N l (n + 1) d b)).coeff r)) ∧
  (∀ a : ℕ, a.Coprime N → ∀ r, CgA A l n ((thN X A N l n d (X.diam N l a b)).coeff r) ((thN X A N l n (d * a) b).coeff r)) := by
  first | exact @GlobalTheory.CyclotomicQExpansion.thN_hecke | exact GlobalTheory.CyclotomicQExpansion.thN_hecke | (intros; apply GlobalTheory.CyclotomicQExpansion.thN_hecke <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.CgAppr

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct
open UpperTheory.V.Z.Kato.Joint

namespace UpperTheory.V.Z.Kato.Joint.ThetaOperator

variable {l : ℕ} [Fact l.Prime]

private theorem cg_trans {n : ℕ} {x y z : Qbar l} (h1 : Cg n x y) (h2 : Cg n y z) : Cg n x z := by
  unfold Cg at *
  have e : x - z = (x - y) + (y - z) := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

private theorem cg_symm {n : ℕ} {x y : Qbar l} (h1 : Cg n x y) : Cg n y x := by
  unfold Cg at *
  rwa [norm_sub_rev]

private theorem cg_lin {n : ℕ} {x y : Qbar l} (a c : Qbar l) (hc : ‖c‖ ≤ 1) (h1 : Cg n x y) :
    Cg n (a + c * x) (a + c * y) := by
  unfold Cg at *
  have e : a + c * x - (a + c * y) = c * (x - y) := by ring
  rw [e, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans h1

private theorem cg_j {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {j : Ω →+* Qbar l} (hj : ∀ x ∈ A, ‖j x‖ ≤ 1)
    {n : ℕ} {x y : Ω} (h : CgA A l n x y) : Cg n (j x) (j y) := by
  obtain ⟨z, hz, e⟩ := h
  unfold Cg
  rw [← map_sub, e, map_mul, map_pow, map_natCast, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hj z hz)

private theorem norm_appr_sub_le_norm_pow (n : ℕ) (c : ℤ_[l]) :
    ‖((c.appr n : ℕ) : Qbar l) - ((c : ℤ_[l]) : Qbar l)‖ ≤ ‖((l : Qbar l)) ^ n‖ := by
  have e : ((c.appr n : ℕ) : Qbar l) - ((c : ℤ_[l]) : Qbar l)
      = algebraMap ℚ_[l] (PadicAlgCl l) (((-(c - ((c.appr n : ℕ) : ℤ_[l])) : ℤ_[l]) : ℚ_[l])) := by
    simp
  have e2 : ((l : Qbar l)) ^ n = algebraMap ℚ_[l] (PadicAlgCl l) (((l : ℚ_[l])) ^ n) := by simp
  rw [e, e2, PadicAlgCl.norm_extends, PadicAlgCl.norm_extends, PadicInt.padic_norm_e_of_padicInt, norm_neg]
  have h := (PadicInt.norm_le_pow_iff_mem_span_pow _ n).2 (PadicInt.appr_spec n c)
  refine h.trans (le_of_eq ?_)
  rw [Padic.norm_p_pow]

private theorem cg_appr (n : ℕ) (c : ℤ_[l]) (x : Qbar l) (hx : ‖x‖ ≤ 1) :
    Cg n (((c.appr n : ℕ) : Qbar l) * x) (((c : ℤ_[l]) : Qbar l) * x) := by
  unfold Cg
  rw [← sub_mul, norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_appr_sub_le_norm_pow n c) (norm_nonneg _)).trans
    (by rw [mul_comm]; exact mul_le_of_le_one_left (norm_nonneg _) hx)

private theorem appr_zero' (n : ℕ) : (0 : ℤ_[l]).appr n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [PadicInt.appr]; simp [ih]

private theorem diam_cg {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (χ : ℕ → ℤ_[l]) (hS : Std A N w j) (n a : ℕ) (b : X.Fn l)
    (ha : a.Coprime N) (hb : InChi X N w χ b) (r : ℚ) :
    Cg n (j ((thN X A N l n 1 (X.diam N l a b)).coeff r))
      (((χ a : ℤ_[l]) : Qbar l) * j ((thN X A N l n 1 b).coeff r)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨hl, hl2, hlN, hN5, hw, hj⟩ := hS
  obtain ⟨hbB, hdiam⟩ := hb
  have hB1 : X.diam N l 1 b ∈ X.B N l w := by
    rw [hdiam 1 (Nat.coprime_one_left N)]
    exact Submodule.smul_mem _ _ hbB
  have hBa : X.diam N l a b ∈ X.B N l w := by
    rw [hdiam a ha]
    exact Submodule.smul_mem _ _ hbB
  have hψ := (GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w 1 hw
    (Nat.coprime_one_left N) b hbB).1
  have hθ := (GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w 1 hw
    (Nat.coprime_one_left N) (X.diam N l a b) hBa).1
  have hD : ∀ s : ℚ, (thN X A N l n 1 b).coeff s ∈ A := by
    obtain ⟨f, -, -, -, hd⟩ := hψ
    exact hd.1
  have hlin := GlobalTheory.T.theta_basis_linear_combination Ω ε X A N l n w (X.diam N l 1 b) (X.diam N l 1 b) hB1 hB1 (χ a) 0
    (thN X A N l n 1 b) (thN X A N l n 1 b) hψ hψ
  have e : X.act l (sgD N l 1) (X.diam N l a b) = χ a • X.diam N l 1 b + (0 : ℤ_[l]) • X.diam N l 1 b := by
    rw [zero_smul, add_zero, hdiam a ha, map_smul]
    rfl
  rw [e] at hθ
  have hmem : χ a • X.diam N l 1 b + (0 : ℤ_[l]) • X.diam N l 1 b ∈ X.B N l w :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hB1) (Submodule.smul_mem _ _ hB1)
  have hu := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w hw _ hmem _ _ hθ hlin r
  have h1 := cg_j hj hu
  rw [appr_zero'] at h1
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, Nat.cast_zero, zero_smul, add_zero,
    smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast] at h1
  exact cg_trans h1 (cg_appr n (χ a) _ (hj _ (hD r)))

end UpperTheory.V.Z.Kato.Joint.ThetaOperator

private theorem norm_natCast_pow_le_one {l : ℕ} [Fact l.Prime] (q k : ℕ) : ‖((q : Qbar l)) ^ k‖ ≤ 1 := by
  have e : ((q : Qbar l)) ^ k = algebraMap ℚ_[l] (PadicAlgCl l) (((q : ℤ) : ℚ_[l]) ^ k) := by simp
  rw [e, PadicAlgCl.norm_extends, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (Padic.norm_int_le_one _)

private theorem coeff_div_prime_eq_zero_of_not_dvd_of_isLat {Ω : Type} [Field Ω] (φ : HahnSeries ℚ Ω) (hL : IsLat 1 φ) {q i : ℕ}
    (hq : q.Prime) (hnd : ¬ q ∣ i) : φ.coeff ((i : ℚ) / q) = 0 := by
  by_contra h
  have hden := hL _ h
  rw [Nat.cast_one, one_mul] at hden
  have key : (((i : ℚ) / q).num : ℚ) = (i : ℚ) / q := Rat.coe_int_num_of_den_eq_one hden
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have h2 : (i : ℚ) = q * ((i : ℚ) / q).num := by rw [key]; field_simp
  have h3 : (i : ℤ) = q * ((i : ℚ) / q).num := by exact_mod_cast h2
  exact hnd (Int.natCast_dvd_natCast.mp ⟨_, h3⟩)

open UpperTheory.V.Z.Kato.Joint.ThetaOperator in
theorem UpperTheory.V.Z.Kato.Joint.thOp :
    UpperTheory.V.Z.Kato.Joint.ThOp := by
  intro l _ Ω _ _ _ ε X A N w j χ hS n T b hT hb i
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hS' := hS
  obtain ⟨hl, hl2, hlN, hN5, hw, hj⟩ := hS'
  have hψ : ∀ m, IsThB X A N l m (X.act l (sgD N l 1) b) (thN X A N l m 1 b) ∧ IsLat 1 (thN X A N l m 1 b) :=
    fun m => GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l X.j_hol hl2 hlN hN5 hl m w 1 hw (Nat.coprime_one_left N) b hb.1
  have hrel := GlobalTheory.T.cuspFunctionalModPrimePow_commutes_hecke_diamond Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w 1 hw (Nat.coprime_one_left N) b hb.1
  cases T with
  | T q =>
    obtain ⟨hqp, hqNl⟩ := hT
    have hqN : q.Coprime N :=
      Nat.Coprime.coprime_dvd_right (dvd_mul_right N l) ((Nat.Prime.coprime_iff_not_dvd hqp).2 hqNl)
    simp only [th, seqN, fop, Tower.op, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.EisM.To, GlobalTheory.EisM.Vo]
    have h1 := hrel.1 q hqp hqNl ((i : ℚ) / (1 : ℕ))
    rw [GlobalTheory.CyclotomicQExpansion.Api.hq_eq_uq_of_isAlgClosed hqp.pos (hψ n).2] at h1
    have h1' := cg_j hj h1
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, GlobalTheory.CyclotomicQExpansion.Api.coeff_uq hqp.pos,
      GlobalTheory.CyclotomicQExpansion.Api.coeff_vq hqp.pos, map_add, Nat.cast_one, div_one, Rat.den_natCast, if_true,
      one_mul, smul_eq_mul, nsmul_eq_mul, map_mul, map_pow, map_natCast] at h1'
    have hx : Cg n (j ((thN X A N l n q b).coeff ((i : ℚ) / q)))
        (((χ q : ℤ_[l]) : Qbar l) *
          (if q ∣ i then j ((thN X A N l n 1 b).coeff (((i / q : ℕ) : ℚ) / ((1 : ℕ) : ℚ))) else 0)) := by
      have ha := cg_j hj (hrel.2.2 q hqN ((i : ℚ) / q))
      have hc := cg_trans (cg_symm ha) (diam_cg X A N w j χ hS n q b hqN hb ((i : ℚ) / q))
      rw [one_mul] at hc
      split_ifs with hdiv
      · rwa [Nat.cast_one, div_one, Nat.cast_div hdiv (by exact_mod_cast hqp.ne_zero)]
      · rw [mul_zero]
        rwa [coeff_div_prime_eq_zero_of_not_dvd_of_isLat _ (hψ n).2 hqp hdiv, map_zero, mul_zero] at hc
    have key := cg_trans h1' (cg_lin _ _ (norm_natCast_pow_le_one q (w + 1)) hx)
    have hw2 : w + 2 - 1 = w + 1 := by omega
    simp only [Nat.cast_one, div_one, Nat.cast_mul, hw2]
    convert key using 2
    simp only [Nat.cast_one, div_one]
    ring
  | U =>
    show Cg n (j ((thN X A N l n 1 (X.heckeU l b)).coeff ((i : ℚ) / ((1 : ℕ) : ℚ))))
      (j ((thN X A N l n 1 b).coeff (((l * i : ℕ) : ℚ) / ((1 : ℕ) : ℚ))))
    have h2 := cg_j hj (hrel.2.1 ((i : ℚ) / (1 : ℕ)))
    simp only [GlobalTheory.CyclotomicQExpansion.Api.coeff_uq (Fact.out : l.Prime).pos, Nat.cast_one, div_one, Rat.den_natCast,
      if_true] at h2
    have h3 := cg_j hj (GlobalTheory.T.cgA_coeff_of_isThB_succ Ω ε X A N l hl2 hlN (by omega) hl n _ _ _ (hψ (n + 1)).1 (hψ n).1
      ((l : ℚ) * i))
    simp only [Nat.cast_one, div_one, Nat.cast_mul]
    exact cg_trans h2 h3
  | D d =>
    simp only [th, seqN, fop, Tower.op, LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply,
      smul_eq_mul]
    exact diam_cg X A N w j χ hS n d b hT hb _

end
end
end
