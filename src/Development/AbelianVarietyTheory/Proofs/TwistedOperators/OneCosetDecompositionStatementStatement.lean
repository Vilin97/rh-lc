module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodGroupsReduceSplitPlaceFamilySucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepIntegrandVanishesOffBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLevelElementOffPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitriangularStabilizerOfPrincipalMoveStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OfMulTrivialAtPlacesSubset

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.CondCut

variable {D : D7}

theorem idOff_sub {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, Q v → P v) {a : AE D} (ha : a ∈ idOff D P) : a ∈ idOff D Q := by
  unfold GlobalTheory.FinPl.idOff at ha ⊢
  rw [Submodule.mem_iInf] at ha ⊢
  exact fun w => ha ⟨w.1, h w.1 w.2⟩

theorem idAt_sup {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, Q v → P v) {a : AE D} (ha : a ∈ idAt D Q) : a ∈ idAt D P := by
  unfold GlobalTheory.FinPl.idAt at ha ⊢
  obtain ⟨h0, hw⟩ := Ideal.mem_inf.1 ha
  refine Ideal.mem_inf.2 ⟨h0, ?_⟩
  rw [Submodule.mem_iInf] at hw ⊢
  exact fun w => hw ⟨w.1, fun hq => w.2 (h w.1 hq)⟩

theorem mt_mul_of_grpOff {W : HSp D} {Q : GlobalTheory.FinPl.Pl D → Prop} {b : GA D W} (hb : b ∈ grpOff W Q) {k : ℕ}
    (M : Matrix (Fin W.rank) (Fin k) (AE D)) (hM : ∀ i j, M i j ∈ idAt D Q) : mt W b * M = M := by
  have hb' := (GlobalTheory.FinPlLoc.mem_congGrp _ b).1 hb
  have key : (mt W b - 1) * M = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have h1 := (GlobalTheory.FinPlLoc.mem_idOff_iff Q _).1 (hb' i l)
    have h2 := (GlobalTheory.FinPlLoc.mem_idAt_iff Q _).1 (hM l j)
    rw [Matrix.sub_apply, ← h2]
    calc (mt W b i l - (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) i l) * (GlobalTheory.FinPlLoc.idem D Q * M l j)
        = (GlobalTheory.FinPlLoc.idem D Q * (mt W b i l - (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) i l)) * M l j := by ring
      _ = 0 := by rw [h1, zero_mul]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at key
  exact key

theorem mul_mem_idAt {Q : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} (A : Matrix (Fin m) (Fin n) (AE D))
    (B : Matrix (Fin n) (Fin k) (AE D)) (hB : ∀ i j, B i j ∈ idAt D Q) (i : Fin m) (j : Fin k) : (A * B) i j ∈ idAt D Q := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hB l j)

end GlobalTheory.AscFin.CondCut


open GlobalTheory.AscFin.CondCut in
theorem GlobalTheory.AscFin.Cond.of_mul_grpOff : ∀ {D : D7} {V₀ W W₀ : HSp D} {ρ σ : ℕ} (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (ψ : AddChar (AF D.host.F) ℂ) (P Q : GlobalTheory.FinPl.Pl D → Prop) (g₁ g₂ : GA D W), (∀ v, Q v → P v) → g₁ ∈ grpAt W Q → g₂ ∈ grpOff W Q → g₁ * g₂ = g₂ * g₁ → Cond dW p x y ψ P (g₁ * g₂) → Cond dW p x y ψ Q g₁ := by
  intro D V₀ W W₀ ρ σ dW p x y ψ P Q g₁ g₂ hQP _hg₁ hg₂ _hcomm H
  have hg₂i : g₂⁻¹ ∈ grpOff W Q := inv_mem hg₂
  have emt : ∀ {k : ℕ} (M : Matrix (Fin W.rank) (Fin k) (AE D)),
      mt W (g₁ * g₂)⁻¹ * M = mt W g₂⁻¹ * (mt W g₁⁻¹ * M) := by
    intro k M
    rw [_root_.mul_inv_rev]
    exact Matrix.mul_assoc _ _ _
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨u, a, ha, hoff⟩ := H.pt
    refine ⟨u, a, ha, fun i j => ?_⟩
    have h1 := idOff_sub hQP (hoff i j)
    have h2 : (((mt W g₂⁻¹ - 1) * (mt W g₁⁻¹ * (x * u.1.1)) : Matrix (Fin W.rank) (Fin ρ) (AE D))) i j ∈ idOff D Q := by
      rw [Matrix.mul_apply]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (by
        rw [Matrix.sub_apply]; exact (GlobalTheory.FinPlLoc.mem_congGrp _ _).1 hg₂i i l)
    have e : mt W g₁⁻¹ * (x * u.1.1) - x - a =
        (mt W (g₁ * g₂)⁻¹ * (x * u.1.1) - x - a) - (mt W g₂⁻¹ - 1) * (mt W g₁⁻¹ * (x * u.1.1)) := by
      rw [emt, Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e, Matrix.sub_apply]
    exact sub_mem h1 h2
  · intro N hN hlow hA
    refine H.shift N (fun i j => idAt_sup hQP (hN i j)) hlow ?_
    rw [emt, mt_mul_of_grpOff hg₂i _ (mul_mem_idAt _ _ (mul_mem_idAt _ _ hN))]
    exact hA
  · intro ξ hξ ξ' hξQ he
    refine H.iso ξ hξ ξ' (fun i j => idAt_sup hQP (hξQ i j)) ?_
    have hinc : ∀ i j, (dW.incX V₀ ξ) i j ∈ idAt D Q := mul_mem_idAt _ _ hξQ
    show mt W g₁ * mt W g₂ * dW.incX V₀ ξ = _
    rw [Matrix.mul_assoc, mt_mul_of_grpOff hg₂ _ hinc]
    exact he

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OfMulTrivialAtPlacesSubsetStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.of_mul_trivialAtPlaces_subset : ∀ {D : D7} {V₀ W W₀ : HSp D} {ρ σ : ℕ} (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (ψ : AddChar (AF D.host.F) ℂ) (P Q : GlobalTheory.FinPl.Pl D → Prop) (g₁ g₂ : GA D W), (∀ v, Q v → P v) → g₁ ∈ grpAt W Q → g₂ ∈ grpOff W Q → g₁ * g₂ = g₂ * g₁ → Cond dW p x y ψ P (g₁ * g₂) → Cond dW p x y ψ Q g₁ := by
  first | exact @GlobalTheory.AscFin.Cond.of_mul_grpOff | exact GlobalTheory.AscFin.Cond.of_mul_grpOff | (intros; apply GlobalTheory.AscFin.Cond.of_mul_grpOff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneCosetDecompositionStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.CosetFJ

variable {D : D7}

theorem coset_of_places {V₀ W W₀ : HSp D} {ρ σ : ℕ} (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (ψ : AddChar (AF D.host.F) ℂ) (K : Subgroup (GA D W))
    (S : Finset (GlobalTheory.FinPl.Pl D)) :
    (∀ v ∈ S, ∀ g ∈ grpAt W (· = v), Cond dW p x y ψ (· = v) g →
      ∃ r ∈ Rgrp W x, r ∈ grpAt W (· = v) ∧ ∃ k ∈ K, k ∈ grpAt W (· = v) ∧ g = r * k) →
    ∀ g ∈ grpAt W (· ∈ S), Cond dW p x y ψ (· ∈ S) g →
      ∃ r ∈ Rgrp W x, r ∈ grpAt W (· ∈ S) ∧ ∃ k ∈ K, k ∈ grpAt W (· ∈ S) ∧ g = r * k := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ g hg _
    have e : g = 1 := GlobalTheory.QRed.grpAt_eq_one (fun v => by simp) hg
    exact ⟨1, one_mem _, one_mem _, 1, one_mem _, one_mem _, by rw [e, one_mul]⟩
  | insert v s hv ih =>
    intro hloc g hg hc
    obtain ⟨g₁, hg₁, g₂, hg₂o, rfl⟩ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).1 g
    have mono : ∀ {P : GlobalTheory.FinPl.Pl D → Prop} {a : GA D W}, (∀ w, P w → w ∈ insert v s) → a ∈ grpAt W P →
        a ∈ grpAt W (· ∈ insert v s) := fun hP ha => GlobalTheory.DStepSuppSecond.grpAt_mono hP ha
    have hg₁' : g₁ ∈ grpAt W (· ∈ insert v s) := mono (fun w hw => by simp [hw]) hg₁
    have hg₂ : g₂ ∈ grpAt W (· ∈ insert v s) := by
      have := mul_mem (inv_mem hg₁') hg
      rwa [inv_mul_cancel_left] at this
    have hg₂s : g₂ ∈ grpAt W (· ∈ s) :=
      GlobalTheory.QRed.grpAt_of_off (fun w hw => by rcases Finset.mem_insert.1 hw with h | h; exacts [Or.inl h.symm, Or.inr h])
        hg₂ hg₂o
    have hcomm : g₁ * g₂ = g₂ * g₁ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).2.1 g₁ hg₁ g₂ hg₂o
    have hdisj : ∀ w, w = v → ¬ w ∈ s := fun w hw hws => hv (hw ▸ hws)
    have hg₁o : g₁ ∈ grpOff W (· ∈ s) := GlobalTheory.QRed.grpAt_off hdisj hg₁
    have hc₁ := GlobalTheory.T.of_mul_trivialAtPlaces_subset dW p x y ψ _ _ g₁ g₂ (fun w hw => by simp [hw]) hg₁ hg₂o hcomm hc
    have hc₂ := GlobalTheory.T.of_mul_trivialAtPlaces_subset dW p x y ψ _ _ g₂ g₁ (fun w hw => Finset.mem_insert_of_mem hw) hg₂s hg₁o hcomm.symm
      (hcomm ▸ hc)
    obtain ⟨r₁, hr₁, hr₁a, k₁, hk₁, hk₁a, e₁⟩ := hloc v (Finset.mem_insert_self v s) g₁ hg₁ hc₁
    obtain ⟨r₂, hr₂, hr₂a, k₂, hk₂, hk₂a, e₂⟩ :=
      ih (fun w hw => hloc w (Finset.mem_insert_of_mem hw)) g₂ hg₂s hc₂
    have hk₁r₂ : k₁ * r₂ = r₂ * k₁ := GlobalTheory.SeeSawLastValue.grpAt_comm hdisj hk₁a hr₂a
    refine ⟨r₁ * r₂, mul_mem hr₁ hr₂, mul_mem (mono (fun w hw => by simp [hw]) hr₁a)
      (mono (fun w hw => Finset.mem_insert_of_mem hw) hr₂a), k₁ * k₂, mul_mem hk₁ hk₂,
      mul_mem (mono (fun w hw => by simp [hw]) hk₁a) (mono (fun w hw => Finset.mem_insert_of_mem hw) hk₂a), ?_⟩
    rw [e₁, e₂]
    calc r₁ * k₁ * (r₂ * k₂) = r₁ * (k₁ * r₂) * k₂ := by simp only [mul_assoc]
      _ = r₁ * r₂ * (k₁ * k₂) := by rw [hk₁r₂]; simp only [mul_assoc]

theorem one_coset_decomposition_base : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ g ∈ grpAt _ (fun v => v ∈ G.pl.S0), Cond (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (fun v => v ∈ G.pl.S0) g → ∃ r ∈ Rgrp _ (xFB F σ h'), r ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ ∃ k ∈ lev G (.grid (2 * σ + 2) 0), k ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ g = r * k := by
  intro D hD T L μ0 hL sc G W M hM F _hF σ h h' g hg hc
  refine coset_of_places (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (lev G (.grid (2 * σ + 2) 0)) G.pl.S0 ?_ g hg hc
  intro v hv g hg hc
  obtain ⟨u, a, ha, hoff⟩ := hc.pt
  obtain ⟨k, hk, hka, hk'⟩ := GlobalTheory.T.exists_level_element_off_place D hD T L μ0 hL sc G W M hM F _hF σ h h' v hv g hg u a ha hoff
  obtain ⟨r, hr, hra, e⟩ := GlobalTheory.T.exists_unitriangularStabilizer_of_principal_move _ (xFB F σ h') (· = v) g k u hg hka hk'
  exact ⟨r, hr, hra, k⁻¹, inv_mem hk, inv_mem hka, e⟩

end GlobalTheory.CosetFJ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneCosetDecompositionStatementStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.one_coset_decomposition_statement : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ g ∈ grpAt _ (fun v => v ∈ G.pl.S0), Cond (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (fun v => v ∈ G.pl.S0) g → ∃ r ∈ Rgrp _ (xFB F σ h'), r ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ ∃ k ∈ lev G (.grid (2 * σ + 2) 0), k ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ g = r * k := by
  first | exact @GlobalTheory.CosetFJ.one_coset_decomposition_base | exact GlobalTheory.CosetFJ.one_coset_decomposition_base | (intros; apply GlobalTheory.CosetFJ.one_coset_decomposition_base <;> assumption)
end
end
