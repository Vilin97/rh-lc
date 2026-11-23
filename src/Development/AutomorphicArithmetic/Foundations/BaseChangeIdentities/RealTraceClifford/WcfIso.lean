module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ChSymAnti
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DominantRearrangementProperties
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.IsoFacts
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.LapForm
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Sl2Core
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.TrOnZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ConeWeightsNotSecondType
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.AsymExp
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DominantRearrangementProperties
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll
import Formalism.RealPlaceAnalysis.QuotientSettingHolds

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.WcfForm

section

@[expose] public section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

theorem UpperTheory.RealTr.wcfForm :
    ∀ (n : ℕ) (c : FR n) (ν : Wt n), Antitone ν → Sym c → (∀ μ, cf c μ ≠ 0 → Maj μ ν) →
      (∀ x, cf (alt (rhoV n) * c) x ≠ 0 → nsq x = nsq (ν + rhoV n)) → alt (rhoV n) * c = cf c ν • alt (ν + rhoV n) := by
  intro n c ν hν hc hmaj hnsq
  obtain ⟨_, _, _, hlin, _, _, halt, hperm, hasym, hsym, _, hstrict, _⟩ := cfBasic n
  obtain ⟨hR1, -, hρ, -, -, hR6⟩ := rearr n
  set ρ := rhoV n with hρdef
  set lam : Wt n := ν + ρ with hlam
  have hlamS : StrictAnti lam := by
    intro a b hab
    show ν b + ρ b < ν a + ρ a
    linarith [hν hab.le, hρ hab]
  have hA : ASym (alt ρ * c) := by
    rw [mul_comm]
    exact (hsym c (alt ρ) hc).1 (hasym ρ)
  have hsg1 : sg (1 : Equiv.Perm (Fin n)) = 1 := by
    have e := hperm ρ 1
    simp only [Equiv.Perm.coe_one, Function.comp_id] at e
    have e2 : cf (alt ρ) ρ = cf (sg (1 : Equiv.Perm (Fin n)) • alt ρ) ρ := by rw [← e]
    rw [(hlin (alt ρ) (alt ρ) (sg (1 : Equiv.Perm (Fin n))) ρ).2, (hstrict ρ hρ).1] at e2
    simpa using e2.symm
  have hterm : ∀ (x : Wt n) (w : Equiv.Perm (Fin n)), Antitone x → cf c (x - ρ ∘ ⇑w) ≠ 0 →
      ∑ a, x a * x a ≤ ∑ a, x a * ν a + ∑ a, x a * ρ (w a) := by
    intro x w hx hne
    have h1 : ∑ a, x a * (x - ρ ∘ ⇑w) a ≤ ∑ a, x a * ν a := hmaj _ hne x hx
    have h2 : ∑ a, x a * (x - ρ ∘ ⇑w) a = ∑ a, x a * x a - ∑ a, x a * ρ (w a) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      simp [mul_sub]
    linarith
  have hsplit : ∀ x : Wt n, ∑ a, x a * lam a = ∑ a, x a * ν a + ∑ a, x a * ρ a := by
    intro x
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp [hlam, mul_add]
  have hone : ∀ x : Wt n, StrictAnti x → cf (alt ρ * c) x ≠ 0 → x = lam := by
    intro x hx hne0
    have hne := hne0
    rw [halt] at hne
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hcw : cf c (x - ρ ∘ ⇑w) ≠ 0 := right_ne_zero_of_mul hw
    have h3 := hterm x w hx.antitone hcw
    have h4 := (hR1 x ρ hx.antitone hρ.antitone w).1
    have h5 : nsq x ≤ ∑ a, x a * lam a := by
      have e1 := hsplit x
      have e2 : nsq x = ∑ a, x a * x a := by
        unfold nsq
        refine Finset.sum_congr rfl (fun a _ => ?_)
        ring
      linarith
    exact (hR6 x lam h5).2 (hnsq x hne0).ge
  have hcoef : cf (alt ρ * c) lam = cf c ν := by
    rw [halt, Finset.sum_eq_single 1]
    · have e : lam - ρ ∘ ⇑(1 : Equiv.Perm (Fin n)) = ν := by
        funext a
        simp [hlam]
      rw [e, hsg1, one_mul]
    · intro w _ hw1
      by_contra hne
      have hcw : cf c (lam - ρ ∘ ⇑w) ≠ 0 := right_ne_zero_of_mul hne
      have h3 := hterm lam w hlamS.antitone hcw
      have h4 := hR1 lam ρ hlamS.antitone hρ.antitone w
      have e1 : ∑ a, lam a * lam a = ∑ a, lam a * ν a + ∑ a, lam a * ρ a := hsplit lam
      exact hw1 (h4.2 hlamS hρ (le_antisymm h4.1 (by linarith)))
    · intro h
      exact absurd (Finset.mem_univ _) h
  obtain ⟨s, hs, hf⟩ := asymExp n _ hA
  have hsub : s ⊆ {lam} := fun x hx => Finset.mem_singleton.mpr (hone x (hs x hx).1 (hs x hx).2)
  rw [← hcoef]
  rcases Finset.subset_singleton_iff.mp hsub with h | h
  · rw [h, Finset.sum_empty] at hf
    have z := (hlin 0 0 0 lam).2
    rw [zero_smul, zero_mul] at z
    rw [hf, z, zero_smul]
  · rw [h, Finset.sum_singleton] at hf
    exact hf
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.WcfIso

section

@[expose] public section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

theorem UpperTheory.RealTr.wcfIso :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ B c (ν : Wt n), Cm F S B → IsCh F S B c → (∀ μ, μ ≠ ν → hw F μ ⊓ S = ⊥) →
      alt (rhoV n) * c = trOn (hw F ν ⊓ S) B • alt (ν + rhoV n) := by
  intro n V _ _ F hF S hfin hstb B c ν hcm hch hother
  have cfB := cfBasic n
  by_cases hS : hw F ν ⊓ S = ⊥
  · have hbot : S = ⊥ := by
      by_contra hne
      obtain ⟨x, hxS, hx0, μ, hμ⟩ := Formalism.REAL.kHiExist V n (fun _ => true) F S hfin
        (Formalism.REAL.glRel_kRel _ _ hF.gl) (fun a b _ => hF.unit a b) (fun a b _ => hstb a b) hne
      have hmem : x ∈ hw F μ ⊓ S := ⟨hμ, hxS⟩
      by_cases hμν : μ = ν
      · subst hμν
        rw [hS] at hmem
        exact hx0 ((Submodule.mem_bot ℂ).1 hmem)
      · rw [hother μ hμν] at hmem
        exact hx0 ((Submodule.mem_bot ℂ).1 hmem)
    have hc0 : ∀ μ, cf c μ = 0 := by
      intro μ
      rw [hch μ, hbot, inf_bot_eq, trOn_bot]
    have hz : ∀ x : Wt n, cf (0 : FR n) x = 0 := by
      intro x
      have h := (cfB.2.2.2.1 0 0 0 x).2
      simpa using h
    rw [hS, trOn_bot, zero_smul]
    apply cfB.2.2.1
    intro x
    rw [hz]
    by_contra hne
    obtain ⟨y, _, hy⟩ := cfB.2.2.2.2.2.1 _ _ x hne
    exact hy (hc0 _)
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    have hdom := hwDom n V F hF S hfin hstb ν x hx.2 hx0 hx.1
    have hanti := ((rearr n).2.2.2.2.1 ν hdom).1
    obtain ⟨hcas, hmaj, hweq⟩ := isoFacts n V F hF S hfin hstb ν hother
    obtain ⟨t, ht1, ht2⟩ := chLap n V F hF S hfin hstb B c _ hcm hch hcas
    have key := wcfForm n c ν hanti (chSym n V F hF S hfin hstb B c hcm hch)
      (fun μ hμ => hmaj μ (fun h => hμ (by rw [hch μ, h, trOn_bot])))
      (fun y hy => by
        have h := lapForm n c t _ ht1 ht2 y hy
        have h' : ((nsq y : ℝ) : ℂ) = ((nsq (ν + rhoV n) : ℝ) : ℂ) := by
          rw [h]
          push_cast
          ring
        exact_mod_cast h')
    rw [key, hch ν, hweq]
end
end
end
