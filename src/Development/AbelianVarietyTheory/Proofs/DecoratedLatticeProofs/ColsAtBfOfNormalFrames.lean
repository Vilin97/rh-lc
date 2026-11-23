module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceMemLatticeCompletionIffParts
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjPartLineMultipleMemIff

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColsConj

theorem form_mulVec {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (A : Fin N → k)
    (G : Fin N → Fin N → k) (β : Matrix (Fin N) Y k) (m₁ : Y) (c₁ : k)
    (h1 : ∑ r, ∑ r', A r * G r r' * β r' m₁ = c₁) (h0 : ∀ m, m ≠ m₁ → ∑ r, ∑ r', A r * G r r' * β r' m = 0)
    (w : Y → k) : ∑ r, ∑ r', A r * G r r' * (β *ᵥ w) r' = c₁ * w m₁ := by
  have h : ∑ r, ∑ r', A r * G r r' * (β *ᵥ w) r' = ∑ m, (∑ r, ∑ r', A r * G r r' * β r' m) * w m := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (s := (Finset.univ : Finset Y))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset Y))]
    refine Finset.sum_congr rfl fun r' _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [h, Finset.sum_eq_single m₁ (fun m _ hm => by rw [h0 m hm, zero_mul]) (fun hm => absurd (Finset.mem_univ _) hm), h1]

theorem conj_part_mem_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (u u' : Fin S.rank → D.host.E) (m₁ : Y) (c₁ : k), IsSelfDualC S L → IntIn q S F L → valuation k c₁ = 1 → (∀ r, F.β r m₁ = c₁ * (ofSplit q).pr (u' r)) → (∑ r, ∑ r', star (u r) * S.gram r r' * u' r' = 1) → (∀ m, m ≠ m₁ → ∑ r, ∑ r', (ofSplit q).pr (star (u r)) * (ofSplit q).pr (S.gram r r') * F.β r' m = 0) → ∀ a : AE D, ((fun r => cA D q.e * (a * incA D (u r))) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ q.pr (cA D a) ∈ 𝒪[k]) := by
  intro D k _ _ _ _ q S L Y _ _ F u u' m₁ c₁ hL hI hc hb hd hp a
  have hpr : ∀ x : D.host.E, (ofSplit q).pr x = q.pr (incA D x) := fun _ => rfl
  simp only [hpr] at hb hp
  have hy : (fun r => cA D q.e * (a * incA D (u r))) =
      fun r => cA D (q.sec (q.pr (cA D a) * q.pr (incA D (star (u r))))) := by
    funext r
    rw [← RingHom.map_mul, q.sec_pr, RingHom.map_mul, RingHom.map_mul, GlobalTheory.LatVac.cA_cA,
      GlobalTheory.FinPl.FrameLat.cA_incA, star_star]
  have h1 : ∑ r, ∑ r', q.pr (incA D (star (u r))) * q.pr (incA D (S.gram r r')) * F.β r' m₁ = c₁ := by
    have h := congrArg (fun x => c₁ * q.pr (incA D x)) hd

    simp only [map_sum, RingHom.map_mul, RingHom.map_one, mul_one, Finset.mul_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
    rw [hb]; ring
  have key : ∀ w : Y → k, ∑ i, ∑ j, (F.β *ᵥ w) i * q.pr (cA D (incA D (S.gram i j))) *
      (q.pr (cA D a) * q.pr (incA D (star (u j)))) = q.pr (cA D a) * (c₁ * w m₁) := by
    intro w
    rw [← form_mulVec _ _ F.β m₁ c₁ h1 hp w, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GlobalTheory.FinPl.FrameLat.cA_incA, GlobalTheory.LatVac.gram_star]; ring
  rw [hy, GlobalTheory.FinPl.FrameLat.csec_mem_iff hL]
  constructor
  · intro h
    have hw : ∀ i, (Pi.single m₁ (1 : k) : Y → k) i ∈ 𝒪[k] := fun i => by
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h2 := h _ ((hI _).1 hw)
    rw [key, Pi.single_eq_same, mul_one] at h2
    rw [Valuation.mem_integer_iff] at h2 ⊢
    rwa [map_mul, hc, mul_one] at h2
  · intro ha x hx
    have hxe : x = F.β *ᵥ (F.γ *ᵥ x) := by rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
    have hw : ∀ i, (F.γ *ᵥ x) i ∈ 𝒪[k] := (hI _).2 (by rw [← hxe]; exact hx)
    rw [hxe, key]
    exact mul_mem ha (mul_mem ((Valuation.mem_integer_iff _ _).2 hc.le) (hw m₁))

end GlobalTheory.ColsConj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjPartLineMultipleMemIffStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlace_conjPart_lineMultiple_mem_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (u u' : Fin S.rank → D.host.E) (m₁ : Y) (c₁ : k), IsSelfDualC S L → IntIn q S F L → valuation k c₁ = 1 → (∀ r, F.β r m₁ = c₁ * (ofSplit q).pr (u' r)) → (∑ r, ∑ r', star (u r) * S.gram r r' * u' r' = 1) → (∀ m, m ≠ m₁ → ∑ r, ∑ r', (ofSplit q).pr (star (u r)) * (ofSplit q).pr (S.gram r r') * F.β r' m = 0) → ∀ a : AE D, ((fun r => cA D q.e * (a * incA D (u r))) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ q.pr (cA D a) ∈ 𝒪[k]) := by
  first | exact @GlobalTheory.ColsConj.conj_part_mem_iff | exact GlobalTheory.ColsConj.conj_part_mem_iff | (intros; apply GlobalTheory.ColsConj.conj_part_mem_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIntegralAdeleIffBothComponents

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SplitInt

theorem intAt_iff_pr (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (a : AE D) (ha : a ∈ GlobalTheory.FinPl.idAt D (· = q.v)) :
    (a ∈ GlobalTheory.FinPl.intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k]) := by
  have he := GlobalTheory.UpMem.finPart_e_int q
  rw [q.int_iff, q.int_iff, q.sec_pr, q.sec_pr, map_mul, map_mul]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨GlobalTheory.FinPl.FrameLat.mul_mem_intAE he h,
      GlobalTheory.FinPl.FrameLat.mul_mem_intAE he (GlobalTheory.IdemSupport.finPart_cA_mem h)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨ha, ?_⟩
    have hsum : a = q.e * a + cA D (q.e * cA D a) := by
      rw [map_mul, Formalism.L2.Theta.cA_cA, ← add_mul]
      exact ((GlobalTheory.FinPl.FrameLat.idem_iff q a).1 ha).symm
    have h3 : finPart D (cA D (q.e * cA D a)) ∈ intAE D := by
      apply GlobalTheory.IdemSupport.finPart_cA_mem
      rw [map_mul]; exact h2
    rw [hsum, (finPart D).map_add, (finPart D).map_mul]
    exact add_mem h1 h3

end GlobalTheory.SplitInt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIntegralAdeleIffBothComponentsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlace_integralAdele_iff_both_components : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (a : AE D), a ∈ GlobalTheory.FinPl.idAt D (· = q.v) → (a ∈ GlobalTheory.FinPl.intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k]) := by
  first | exact @GlobalTheory.SplitInt.intAt_iff_pr | exact GlobalTheory.SplitInt.intAt_iff_pr | (intros; apply GlobalTheory.SplitInt.intAt_iff_pr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceMemLatticeCompletionIffPartsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlace_mem_latticeCompletion_iff_parts : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (y : Fin S.rank → AE D), (∀ r, y r ∈ GlobalTheory.FinPl.idAt D (· = q.v)) → (y ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ (fun r => q.e * y r) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ∧ (fun r => cA D q.e * y r) ∈ GlobalTheory.FinPl.latV S L (· = q.v)) := by
  first | exact @GlobalTheory.FinPl.SplitParts.mem_latV_iff_parts | exact GlobalTheory.FinPl.SplitParts.mem_latV_iff_parts | (intros; apply GlobalTheory.FinPl.SplitParts.mem_latV_iff_parts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceWPartFrameColumnMultipleMemIff

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColsWPart

theorem wpart_mem_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (u : Fin S.rank → D.host.E) (m₀ : Y) (c₀ : k), IntIn q S F L → valuation k c₀ = 1 → (∀ r, F.β r m₀ = c₀ * (ofSplit q).pr (u r)) → ∀ a : AE D, ((fun r => q.e * (a * incA D (u r))) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ q.pr a ∈ 𝒪[k]) := by
  intro D k _ _ _ _ q S L Y _ _ F u m₀ c₀ hI hc hcol a
  have hc0 : c₀ ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact zero_ne_one hc
  have heq : (fun i => q.sec ((F.β *ᵥ Pi.single m₀ (q.pr a / c₀)) i)) = fun r => q.e * (a * incA D (u r)) := by
    funext r
    have h1 : (F.β *ᵥ Pi.single m₀ (q.pr a / c₀)) r = F.β r m₀ * (q.pr a / c₀) := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h1, hcol r, ← q.sec_pr, map_mul q.pr]
    congr 1
    show c₀ * q.pr (incA D (u r)) * (q.pr a / c₀) = q.pr a * q.pr (incA D (u r))
    field_simp
  rw [← heq, ← hI (Pi.single m₀ (q.pr a / c₀))]
  have hdiv : q.pr a / c₀ ∈ 𝒪[k] ↔ q.pr a ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, map_div₀, hc, div_one]
  constructor
  · intro h
    have := h m₀
    rw [Pi.single_eq_same] at this
    exact hdiv.1 this
  · intro h i
    by_cases hi : i = m₀
    · subst hi; rw [Pi.single_eq_same]; exact hdiv.2 h
    · rw [Pi.single_eq_of_ne hi]; exact zero_mem _

end GlobalTheory.ColsWPart
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceWPartFrameColumnMultipleMemIffStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlace_wPart_frameColumnMultiple_mem_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (u : Fin S.rank → D.host.E) (m₀ : Y) (c₀ : k), IntIn q S F L → valuation k c₀ = 1 → (∀ r, F.β r m₀ = c₀ * (ofSplit q).pr (u r)) → ∀ a : AE D, ((fun r => q.e * (a * incA D (u r))) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ q.pr a ∈ 𝒪[k]) := by
  first | exact @GlobalTheory.ColsWPart.wpart_mem_iff | exact GlobalTheory.ColsWPart.wpart_mem_iff | (intros; apply GlobalTheory.ColsWPart.wpart_mem_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColsAtBfOfNormalFrames

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColsBFSplit

theorem xi_unit {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (hU : q.UnitAA) : valuation k ((ofSplit q).xi) = 1 := by
  have hpe : q.pr q.e = 1 := by
    have h := q.pr_sec 1
    rwa [show q.sec 1 = q.e by simpa using q.sec_pr 1] at h
  have hpce : q.pr (cA D q.e) = 0 := by
    have h : q.pr (q.e * cA D q.e) = 0 := by rw [q.split.2.1, map_zero]
    rwa [map_mul, hpe, one_mul] at h
  have heI := GlobalTheory.FinPl.LatIndHalf.e_mem_idAt q
  have heInt : q.e ∈ GlobalTheory.FinPl.intAt D (· = q.v) :=
    (GlobalTheory.T.splitPlace_integralAdele_iff_both_components D k q q.e heI).2 ⟨by rw [hpe]; exact one_mem _, by rw [hpce]; exact zero_mem _⟩
  obtain ⟨h1, h2⟩ := hU.1 q.e heInt
  have a1 := ((GlobalTheory.T.splitPlace_integralAdele_iff_both_components D k q _ h1.1).1 h1).1
  have a2 := ((GlobalTheory.T.splitPlace_integralAdele_iff_both_components D k q _ h2.1).1 h2).1
  rw [map_mul, hpe, mul_one] at a1 a2
  have hne : q.pr (incA D D.host.xi0) ≠ 0 := by
    intro h0
    have : q.pr (incA D D.host.xi0⁻¹) * q.pr (incA D D.host.xi0) = 1 := by
      rw [← map_mul, ← map_mul, inv_mul_cancel₀ (GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero (D := D)), map_one, map_one]
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have hinv : q.pr (incA D D.host.xi0⁻¹) = (q.pr (incA D D.host.xi0))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ (GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero (D := D)), map_one, map_one]
  rw [hinv] at a2
  have b1 := (Valuation.mem_integer_iff _ _).1 a1
  have b2 := (Valuation.mem_integer_iff _ _).1 a2
  rw [map_inv₀] at b2
  change valuation k (q.pr (incA D D.host.xi0)) = 1
  have hv0 : valuation k (q.pr (incA D D.host.xi0)) ≠ 0 := by simpa using hne
  exact le_antisymm b1 ((inv_le_one₀ (zero_lt_iff.2 hv0)).1 b2)

theorem line_crit {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {S : HSp D} {L : GlobalTheory.FinPl.Lat S} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k S.rank Y) (u u' : Fin S.rank → D.host.E) (m₀ m₁ : Y) (c₀ c₁ : k) (hL : IsSelfDualC S L)
    (hI : IntIn q S F L) (h0 : valuation k c₀ = 1) (h1 : valuation k c₁ = 1)
    (hc0 : ∀ r, F.β r m₀ = c₀ * (ofSplit q).pr (u r)) (hc1 : ∀ r, F.β r m₁ = c₁ * (ofSplit q).pr (u' r))
    (hd : ∑ r, ∑ r', star (u r) * S.gram r r' * u' r' = 1)
    (hp : ∀ m, m ≠ m₁ → ∑ r, ∑ r', (ofSplit q).pr (star (u r)) * (ofSplit q).pr (S.gram r r') * F.β r' m = 0)
    (a : AE D) (ha : a ∈ GlobalTheory.FinPl.idAt D (· = q.v)) :
    (fun r => a * incA D (u r)) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = q.v) := by
  rw [GlobalTheory.T.splitPlace_mem_latticeCompletion_iff_parts D k q S L _ (fun r => Ideal.mul_mem_right _ _ ha), GlobalTheory.T.splitPlace_wPart_frameColumnMultiple_mem_iff D k q S L Y F u m₀ c₀ hI h0 hc0 a,
    GlobalTheory.T.splitPlace_conjPart_lineMultiple_mem_iff D k q S L Y F u u' m₁ c₁ hL hI h1 hc1 hd hp a, GlobalTheory.T.splitPlace_integralAdele_iff_both_components D k q a ha]

end GlobalTheory.ColsBFSplit

end
end
end
