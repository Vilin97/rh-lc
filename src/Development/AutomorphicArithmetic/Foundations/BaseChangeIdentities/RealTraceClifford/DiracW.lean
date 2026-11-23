module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ExpansionTerms
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Conclusion2
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfMulSum
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifEx
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DiracHW
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.IrrCh
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.MultTrOnBot
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SpnAdj
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DominantRearrangementProperties
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.IrrCh
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SymOfMul

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DiracCh

section

@[expose] public section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

theorem UpperTheory.RealTr.diracCh :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      IsPair E1 E2 → LocF (kF E1 E2) → (∀ m (x : V), gelA E1 m x = GlobalTheory.Dec.gelfVal (infOf lam true) m • x) →
      (∀ m (x : V), gelA (barF E2) m x = GlobalTheory.Dec.gelfVal (infOf lam false) m • x) → ∀ ν x : Wt n, hwSp E1 E2 ν ≠ ⊥ → StrictAnti x → cf (chR n * alt (ν + rhoV n)) x ≠ 0 → LSq lam ≤ nsq x := by
  intro n lam V _ _ E1 E2 hP hL h1 h2 ν x hν hx hc
  have hGl : GlRel (kF E1 E2) := by
    intro a b c d
    have e : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
        (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
      simp only [kF, add_mul, mul_add]
      rw [hP.comm a b c d, hP.comm c d a b]
      abel
    rw [e, hP.gl1 a b c d, hP.gl2 a b c d]
    split_ifs <;> simp [kF] <;> abel
  have hU : UF (kF E1 E2) := ⟨hGl, hP.unitK⟩
  rw [hwSp_eq] at hν
  obtain ⟨-, S, c₀, d, hfd, hS, hch, hd, hal⟩ := irrCh n V (kF E1 E2) hU hL ν hν
  obtain ⟨J, _, _, c, η, hcl⟩ := clifEx n
  obtain ⟨S', hfd', hS', hch'⟩ := tenCh n V (kF E1 E2) hU S hfd hS J c η hcl c₀ hch
  have hU' : UF (dg (kF E1 E2) c) := (tenF n V J).2.2.2.2 (kF E1 E2) c η hU hcl
  have hm := mult n (Ten J V) (dg (kF E1 E2) c) hU' S' hfd' hS' 1 _
    ⟨fun a b => by simp, fun y hy => by simpa using hy⟩ hch' (x - rhoV n)
    (by simpa using hx)
  have key : alt (rhoV n) * (c₀ * ∑ j, ex (η j)) =
      ((2 : ℂ) ^ n * d) • (chR n * alt (ν + rhoV n)) := by
    rw [hcl.chr, mul_smul_comm, mul_smul_comm, ← mul_assoc, hal, smul_mul_assoc, smul_smul,
      mul_comm (alt (ν + rhoV n)) (chR n)]
  have hne : hw (dg (kF E1 E2) c) (x - rhoV n) ≠ ⊥ := by
    intro hb
    rw [hb, bot_inf_eq, trOn_bot, sub_add_cancel, key, ((cfBasic n).2.2.2.1 (chR n * alt (ν + rhoV n)) 0 _ x).2] at hm
    rcases mul_eq_zero.1 hm with h | h
    · exact mul_ne_zero (pow_ne_zero n two_ne_zero) hd h
    · exact hc h
  have hfin := diracHW n lam V E1 E2 hP hL h1 h2 J c η hcl (x - rhoV n) hne
  rwa [sub_add_cancel] at hfin
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.MSymm

section

@[expose] public section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

theorem UpperTheory.RealTr.mSymm :
    ∀ (n : ℕ) (x y : Wt n), cf (chR n * alt x) y = cf (chR n * alt y) x := by
  intro n x y
  obtain ⟨-, -, -, -, -, -, hA, -⟩ := cfBasic n
  obtain ⟨-, -, -, hS, hN, -⟩ := chRF n
  rw [mul_comm, hA, mul_comm, hA]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ (fun w => ?_)
  have hs : sg (Equiv.inv (Equiv.Perm (Fin n)) w) = sg w := by
    simp [sg, Equiv.Perm.sign_inv]
  rw [hs]
  congr 1
  have hc : cf (chR n) (x - y ∘ ⇑((Equiv.inv (Equiv.Perm (Fin n))) w))
      = cf (chR n) ((x - y ∘ ⇑((Equiv.inv (Equiv.Perm (Fin n))) w)) ∘ ⇑w) :=
    (hS w _).symm
  rw [hc, ← hN]
  congr 1
  ext i
  simp [Function.comp_def, sub_eq_add_neg, add_comm]
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DiracW

section

@[expose] public section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem uf_kF {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E1 E2 : Fin n → Fin n → Module.End ℂ V} (hP : IsPair E1 E2) : UF (kF E1 E2) := by
  refine ⟨?_, hP.unitK⟩
  intro a b c d
  have g1 := hP.gl1 a b c d
  have g2 := hP.gl2 a b c d
  have h3 := hP.comm a b c d
  have h4 := hP.comm c d a b
  have e : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [kF, add_mul, mul_add]
    rw [h3, h4]
    abel
  rw [e, g1, g2]
  split_ifs <;> (try simp only [kF]) <;> abel

theorem UpperTheory.RealTr.diracW :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      IsPair E1 E2 → LocF (kF E1 E2) → (∀ m (x : V), gelA E1 m x = GlobalTheory.Dec.gelfVal (infOf lam true) m • x) →
      (∀ m (x : V), gelA (barF E2) m x = GlobalTheory.Dec.gelfVal (infOf lam false) m • x) → ∀ ν : Wt n, hwSp E1 E2 ν ≠ ⊥ → LSq lam ≤ spinSq ν := by
  intro n lam V _ _ E1 E2 hP hL h1 h2 ν hν
  have hν' : hw (kF E1 E2) ν ≠ ⊥ := by rwa [hwSp_eq] at hν
  have hD : Dom ν := (irrCh n V (kF E1 E2) (uf_kF hP) hL ν hν').1
  have hR := rearr n
  have hx : StrictAnti (domC (ν - rhoV n) + rhoV n) := by
    intro a b hab
    exact add_lt_add_of_le_of_lt ((hR.2.1 (ν - rhoV n)).1 hab.le) (hR.2.2.1 hab)
  have hc : cf (chR n * alt (ν + rhoV n)) (domC (ν - rhoV n) + rhoV n) ≠ 0 := by
    rw [mSymm, aux₃ n ν hD]
    exact one_ne_zero
  exact diracCh n lam V E1 E2 hP hL h1 h2 ν _ hν hx hc
end
end
end
