module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsGLExistsUnique
public import Formalism.LocalToGlobal.Columns.ChainTwAn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricTestFunctionsAgreeRationalPointsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralPositionOneEqFiniteSumStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistSupportPeriodicLevels
import Formalism.LocalToGlobal.Columns.ChainTwAn

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionMatrixBoundedRationalAutIntegral

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.TwBridge

theorem isGL_int_of_bdd {X : Fields} {Pr : Primes X} {R : Ranks} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ) (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∉ Pr.vGs)
    (hc : GlobalTheory.SymBridge.IsCompl P (qOf P) ι ϖ) (j c : ℕ) (a : AutY X R j) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin c) k)
    (hg : IsGL ι a g)
    (hb : ∀ x ∈ lamYat (Pr := Pr) (R := R) j P, a⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧
      ((qOf P : X.E) ^ j) • a x ∈ lamYat (Pr := Pr) (R := R) j P) :
    IntM (g⁻¹ : GL _ k).val ∧ IntM ((ϖ : k) ^ j • g.val) := by
  obtain ⟨e, -, he⟩ := hg
  have hb' : TwBdd (Pr := Pr) j P a := hb
  have hi : (g⁻¹ : GL _ k).val = GlobalTheory.SymBridge.toLoc ι e e a.symm.toLinearMap := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [he, Model.toLoc_mul, LinearEquiv.comp_symm, Model.toLoc_eq]
    simp
  refine ⟨fun r s => ?_, fun r s => ?_⟩
  · rw [hi]
    show ι (a.symm (Pi.single (e s) 1) (e r)) ∈ 𝒪[k]
    rw [hc.int]
    exact twAn_bdd_inv hP hb' (Pi.single (e s) 1) (fun l => twAn_single_int (e s) l) (e r)
  · rw [he, Matrix.smul_apply, hc.unif]
    show ι ((qOf P : ℕ) : X.E) ^ j • ι (a (Pi.single (e s) 1) (e r)) ∈ 𝒪[k]
    rw [smul_eq_mul, ← map_pow, ← map_mul, hc.int]
    exact twAn_bdd_q hP hb' (Pi.single (e s) 1) (fun l => twAn_single_int (e s) l) (e r)

end GlobalTheory.TwBridge
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionMatrixBoundedRationalAutIntegralStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.completionMatrix_boundedRationalAut_integral : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs →
    GlobalTheory.SymBridge.IsCompl P (qOf P) ι ϖ → ∀ (j c : ℕ) (a : AutY X R j) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin c) k),
    IsGL ι a g →
    (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, a⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧
      ((qOf P : X.E) ^ j) • a x ∈ lamYat (Pr := Pr) (R := R) j P) →
    IntM (g⁻¹ : GL _ k).val ∧ IntM ((ϖ : k) ^ j • g.val) := by
  first | exact @GlobalTheory.TwBridge.isGL_int_of_bdd | exact GlobalTheory.TwBridge.isGL_int_of_bdd | (intros; apply GlobalTheory.TwBridge.isGL_int_of_bdd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearWeilActionSupportAndPeriodIntegral

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.StepData

theorem om_support_period : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (ϖ : kˣ), valuation k (ϖ : k) < 1 → ∀ (i : ℕ)
    (μ : kˣ →* ℂˣ) (Φ : Matrix B A k → ℂ), (∀ x, Φ x ≠ 0 → IntM x) → (∀ x y, MaxM y → Φ (x + y) = Φ x) →
    ∀ (g : GL A k) (g' : GL B k), IntM (g⁻¹ : GL A k).val → IntM ((ϖ : k) ^ i • g.val) →
      IntM (g'⁻¹ : GL B k).val → IntM ((ϖ : k) ^ (i + 1) • g'.val) →
    (∀ x, om μ g g' Φ x ≠ 0 → ∀ r s, valuation k (x r s) ≤ valuation k (((ϖ ^ (i + 1))⁻¹ : kˣ) : k)) ∧
    (∀ x y, (∀ r s, valuation k (y r s) ≤ valuation k ((ϖ : k) ^ (i + 1))) → om μ g g' Φ (x + y) = om μ g g' Φ x) := by
  intro k _ _ _ _ A B _ _ _ _ ϖ hϖ i μ Φ hsupp hper g g' hg hgi hg' hg'i
  have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
  have hvp : valuation k ((ϖ : k) ^ (i + 1)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact pow_ne_zero _ hϖ0
  constructor
  · intro x hx r s
    have hΦ : Φ ((g'⁻¹ : GL B k).val * x * g.val) ≠ 0 := by
      intro h0; apply hx; simp only [om, h0, mul_zero]
    have hz := hsupp _ hΦ
    have hx' : (ϖ : k) ^ (i + 1) • x = ((ϖ : k) ^ (i + 1) • g'.val) * ((g'⁻¹ : GL B k).val * x * g.val) *
        (g⁻¹ : GL A k).val := by
      rw [Matrix.smul_mul, Matrix.smul_mul]
      congr 1
      simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    have hint : IntM ((ϖ : k) ^ (i + 1) • x) := by rw [hx']; exact (hg'i.mul hz).mul hg
    have h1 : valuation k ((ϖ : k) ^ (i + 1) * x r s) ≤ 1 := hint r s
    rw [map_mul] at h1
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀]
    calc valuation k (x r s) = (valuation k ((ϖ : k) ^ (i + 1)))⁻¹ * (valuation k ((ϖ : k) ^ (i + 1)) * valuation k (x r s)) := by
          rw [inv_mul_cancel_left₀ hvp]
      _ ≤ (valuation k ((ϖ : k) ^ (i + 1)))⁻¹ * 1 := by gcongr
      _ = _ := mul_one _
  · intro x y hy
    have hy' : IntM (((ϖ : k) ^ (i + 1))⁻¹ • y) := fun r s => by
      show valuation k (((ϖ : k) ^ (i + 1))⁻¹ * y r s) ≤ 1
      rw [map_mul, map_inv₀]
      calc _ ≤ (valuation k ((ϖ : k) ^ (i + 1)))⁻¹ * valuation k ((ϖ : k) ^ (i + 1)) := by gcongr; exact hy r s
        _ = 1 := inv_mul_cancel₀ hvp
    have hc : (ϖ : k) * (ϖ : k) ^ i * ((ϖ : k) ^ (i + 1))⁻¹ = 1 := by
      rw [pow_succ]; field_simp
    have heq : (g'⁻¹ : GL B k).val * y * g.val = (ϖ : k) • ((g'⁻¹ : GL B k).val * (((ϖ : k) ^ (i + 1))⁻¹ • y) * ((ϖ : k) ^ i • g.val)) := by
      rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul, hc, one_smul]
    have hM : IntM ((g'⁻¹ : GL B k).val * (((ϖ : k) ^ (i + 1))⁻¹ • y) * ((ϖ : k) ^ i • g.val)) :=
      (hg'.mul hy').mul hgi
    have hmax : MaxM ((g'⁻¹ : GL B k).val * y * g.val) := by
      rw [heq]
      intro r s
      rw [Matrix.smul_apply, smul_eq_mul, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hϖ (hM r s)
    simp only [om, Matrix.mul_add, Matrix.add_mul, hper _ _ hmax]

end GlobalTheory.StepData
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearWeilActionSupportAndPeriodIntegralStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.linearWeilAction_support_and_period_integral : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (ϖ : kˣ), valuation k (ϖ : k) < 1 → ∀ (i : ℕ)
    (μ : kˣ →* ℂˣ) (Φ : Matrix B A k → ℂ), (∀ x, Φ x ≠ 0 → IntM x) → (∀ x y, MaxM y → Φ (x + y) = Φ x) →
    ∀ (g : GL A k) (g' : GL B k), IntM (g⁻¹ : GL A k).val → IntM ((ϖ : k) ^ i • g.val) →
      IntM (g'⁻¹ : GL B k).val → IntM ((ϖ : k) ^ (i + 1) • g'.val) →
    (∀ x, om μ g g' Φ x ≠ 0 → ∀ r s, valuation k (x r s) ≤ valuation k (((ϖ ^ (i + 1))⁻¹ : kˣ) : k)) ∧
    (∀ x y, (∀ r s, valuation k (y r s) ≤ valuation k ((ϖ : k) ^ (i + 1))) → om μ g g' Φ (x + y) = om μ g g' Φ x) := by
  first | exact @GlobalTheory.StepData.om_support_period | exact GlobalTheory.StepData.om_support_period | (intros; apply GlobalTheory.StepData.om_support_period <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralTwistPrimeEqDeepFiniteSum

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwSumAgree

theorem sumAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → SumAgree Ch sel mu cst σ₀ P ι s W ν := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hok hAt
  have hPA := GlobalTheory.T.parahoric_test_functions_agree_rational_points X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hAt
  have hiL := GlobalTheory.Proof.TwistSupportPeriodicLevels.ofTwist_support_periodic_levels k s (Fin R.k ⊕ Fin (s + 1)) (Fin R.t)
    (Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2)) (XIx (Fin R.k) (Fin R.t)) W.δ W.tame W.η
    (fun j c h => GlobalTheory.StepData.plainFrame (stdOrd (Fin R.k) (Fin R.t) j c h)) (LatFrame.refl k _) (fun _ _ _ => rfl)
  intro j c h a b g g' hag hbg' ha hb hD
  have hm := hAt.steps
  refine ⟨j + 1, j + 1, fun A' B' hA hB e' e hoe' hoe x => ?_⟩
  obtain ⟨E', hE', hg⟩ := id hag
  obtain ⟨E, hE, hg'⟩ := id hbg'
  have hj : j < R.m := by omega
  have hom := GlobalTheory.TwBridge.Model.om_agree Ch sel mu cst σ₀ P ι s W hAt hok j (c + 1) (c + 1 + 1) hj E' E a b g g' hg hg'
    ((W.T s R).Phi j (c + 1) (by omega)) (PhiAt Ch mu cst.sharp j P.1)
    (fun y => hPA.1 j (c + 1) (by omega) E' E hE' hE y)
  obtain ⟨h1, h2⟩ := GlobalTheory.T.completionMatrix_boundedRationalAut_integral ι W.ϖ P.1 hAt.nmem hAt.compl j (c + 1 + 1) a g hag ha
  obtain ⟨h1', h2'⟩ := GlobalTheory.T.completionMatrix_boundedRationalAut_integral ι W.ϖ P.1 hAt.nmem hAt.compl (j + 1) (c + 1) b g' hbg' hb
  have hSP := GlobalTheory.T.linearWeilAction_support_and_period_integral W.ϖ ((W.unif W.ϖ).2 le_rfl) j ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega))
    (hiL.1 j (c + 1) (by omega)) (hiL.2.1 j (c + 1) (by omega)) g g' h1 h2 h1' h2'
  have hpsi : ∀ z, IntAt P.1 ((qOf P.1 : X.E) ^ (j + 1) * z) → (W.ψ (ι z) : ℂ) = σ₀ (cst.psi P z) :=
    fun z hz => hAt.psi z (twAn_qpow_mul (by omega) hz)
  have o1 : GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun z => (e' z).val) (R.N j)) E' := by
    rintro (z | z)
    · exact (hE' _).trans (hoe' z).symm
    · exact hE' _
  have o2 : GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun z => (e z).val) (R.N (j + 1))) E := by
    rintro (z | z)
    · exact (hE _).trans (hoe z).symm
    · exact hE _
  exact GlobalTheory.T.unfoldingIntegral_positionOne_eq_finite_sum X.E X.K k P.1 (qOf P.1) ι W.ϖ σ₀ W.ψ ν (cst.psi P) (j + 1) hAt.compl W.unif W.cond hν hpsi
    (XIx (Fin R.k) (Fin R.t) j) (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) (R.N j) (cOf R j) (R.N (j + 1)) (cOf R (j + 1))
    A' B' (by omega) (by unfold cOf; omega) (by unfold cOf; omega) hA hB e' e E' E o1 o2 _ _ _ hom hSP.1 hSP.2 x

end GlobalTheory.TwSumAgree
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralTwistPrimeEqDeepFiniteSumStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.unfoldingIntegral_twistPrime_eq_deep_finite_sum : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → SumAgree Ch sel mu cst σ₀ P ι s W ν := by
  first | exact @GlobalTheory.TwSumAgree.sumAgree | exact GlobalTheory.TwSumAgree.sumAgree | (intros; apply GlobalTheory.TwSumAgree.sumAgree <;> assumption)
end
end
