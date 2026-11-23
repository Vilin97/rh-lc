module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HolomorphicLowestType
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSLowK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockCoefficientEqConstMulLowestKTypeCoefficientStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarmonicFockVectorsKilledByLoweringAdaptedBasisStatement
public import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Formalism.LocalToGlobal.IndefiniteReal.ConjLemmas
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftDatumIsNonzeroFockVacuumStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPairingLowestWeightSchurPolarisationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramNegTransposeDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MixedLaplacianKillsProductOfMinorsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsInnerEqFockInnerProductMulNorm

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesModelHolomorphicPositiveSignsFirst

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

open Formalism.IndefR.FWT GlobalTheory.HolDict

namespace GlobalTheory.HolLabel

theorem eq_self_of_strictMono {n : ℕ} {F K : Fin n → Fin n} (hK : StrictMono K) (hF : StrictMono F)
    (hFK : ∀ x, F (K x) = x) (x : Fin n) : K x = x :=
  le_antisymm ((hF.le_apply (x := K x)).trans_eq (hFK x)) hK.le_apply

theorem holShape_signs_first : ∀ (D : D7) (σ : D.what₂.LL →+* ℂ), (∀ ρ, Formalism.IndefR.Links.labE σ (Formalism.IndefR.Links.lab σ ρ) = tauE D ρ) → ∀ (i : Fin D.R.m) (M : DSModel (Wc D i) (Formalism.IndefR.Links.parAt (Wc D i) σ)), GlobalTheory.HolDict.HolShape M ∧ (∃ wt, GlobalTheory.HolDict.WtIs M wt) ∧ ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < pW D i ρ) := by
  intro D σ hσ i M
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 = (Wc D i).rank :=
    fun τ => GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
  have hp : ∀ ρ, Formalism.IndefR.Links.parAt (Wc D i) σ ρ =
      Formalism.L2.NTheta.holPar _ _ (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) := fun ρ => by
    unfold Formalism.IndefR.Links.parAt; rw [if_pos (hσ ρ)]
  have ho : ∀ ρ, Odd (((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2) := fun ρ => by
    rw [hpq ρ, hrk]; exact Formalism.L2.NTheta.odd_r _
  have hentL : ∀ ρ (c : Fin ((Wc D i).sig (tauE D ρ)).1),
      Formalism.L2.NTheta.holEnt _ _ (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) (Sum.inl c) =
        Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) (c : ℕ) := fun ρ c => by
    unfold Formalism.IndefR.Links.kapAt
    rw [Formalism.L2.NTheta.holEnt_kapW _ _ _ (ho ρ)]
    rfl
  have hentR : ∀ ρ (c : Fin ((Wc D i).sig (tauE D ρ)).2),
      Formalism.L2.NTheta.holEnt _ _ (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) (Sum.inr c) =
        Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) (((Wc D i).sig (tauE D ρ)).1 + (c : ℕ)) := fun ρ c => by
    unfold Formalism.IndefR.Links.kapAt
    rw [Formalism.L2.NTheta.holEnt_kapW _ _ _ (ho ρ)]
    rfl
  have heps : ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < pW D i ρ) := by
    intro ρ
    obtain ⟨hanti, f, hf, hS⟩ := M.enum ρ
    rw [hp ρ] at hS
    have hpqρ := hpq ρ
    have hL := hentL ρ
    have hR := hentR ρ
    have hlt : ∀ m n : ℕ, m < n → n < (Wc D i).rank → Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) n < Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) m := by
      intro m n hmn hn
      have h1 := Formalism.L2.NTheta.lamAt_add_add_le (D.hc (Formalism.IndefR.Links.lab σ ρ)) (n - m) m (by omega)
      rw [show m + (n - m) = n by omega] at h1
      have h2 : (1 : ℚ) ≤ ((n - m : ℕ) : ℚ) := by exact_mod_cast (by omega : 1 ≤ n - m)
      linarith
    have mem1 : ∀ a : Fin (Wc D i).rank, ∃ n : Fin (Wc D i).rank,
        f a = Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) n ∧ M.ε ρ a = decide ((n : ℕ) < ((Wc D i).sig (tauE D ρ)).1) := by
      intro a
      have hm : (f a, M.ε ρ a) ∈ Formalism.L2.NTheta.holPar ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) := by
        rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
      obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hm
      rcases x with c | c
      · simp only [hL, Sum.elim_inl, Prod.mk.injEq] at hx
        exact ⟨⟨c, by omega⟩, hx.1.symm, by rw [← hx.2]; exact (decide_eq_true c.2).symm⟩
      · simp only [hR, Sum.elim_inr, Prod.mk.injEq] at hx
        exact ⟨⟨((Wc D i).sig (tauE D ρ)).1 + c, by omega⟩, hx.1.symm, by rw [← hx.2]; exact (decide_eq_false (by simp)).symm⟩
    have mem2 : ∀ n : Fin (Wc D i).rank, ∃ a : Fin (Wc D i).rank,
        f a = Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) n ∧ M.ε ρ a = decide ((n : ℕ) < ((Wc D i).sig (tauE D ρ)).1) := by
      intro n
      have hm : ∀ x, (Formalism.L2.NTheta.holEnt ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) x,
          Sum.elim (fun _ => true) (fun _ => false) x) ∈ Finset.univ.image (fun a => (f a, M.ε ρ a)) := fun x => by
        rw [← hS]; unfold Formalism.L2.NTheta.holPar; exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
      by_cases hn : (n : ℕ) < ((Wc D i).sig (tauE D ρ)).1
      · obtain ⟨a, -, ha⟩ := Finset.mem_image.1 (hm (Sum.inl ⟨n, hn⟩))
        simp only [hL, Sum.elim_inl, Prod.mk.injEq] at ha
        exact ⟨a, ha.1, by rw [ha.2]; exact (decide_eq_true hn).symm⟩
      · obtain ⟨a, -, ha⟩ := Finset.mem_image.1 (hm (Sum.inr ⟨n - ((Wc D i).sig (tauE D ρ)).1, by omega⟩))
        simp only [hR, Sum.elim_inr, Prod.mk.injEq] at ha
        rw [show ((Wc D i).sig (tauE D ρ)).1 + (n - ((Wc D i).sig (tauE D ρ)).1) = n by omega] at ha
        exact ⟨a, ha.1, by rw [ha.2]; exact (decide_eq_false hn).symm⟩
    choose F hF1 hF2 using mem1
    choose K hK1 hK2 using mem2
    have fanti : ∀ a b : Fin (Wc D i).rank, a < b → f b < f a := fun a b hab => by
      have h1 := hanti hab
      rw [hf, hf] at h1
      exact_mod_cast h1
    have hFm : StrictMono F := fun a b hab => by
      have h1 := fanti a b hab
      rw [hF1 a, hF1 b] at h1
      by_contra hc
      rcases (not_lt.1 hc).lt_or_eq with hc | hc
      · exact lt_asymm h1 (hlt _ _ hc (F a).2)
      · rw [hc] at h1; exact lt_irrefl _ h1
    have hKm : StrictMono K := fun n m hnm => by
      have h1 := hlt _ _ hnm m.2
      rw [← hK1 n, ← hK1 m] at h1
      by_contra hc
      rcases (not_lt.1 hc).lt_or_eq with hc | hc
      · exact lt_asymm h1 (fanti _ _ hc)
      · rw [hc] at h1; exact lt_irrefl _ h1
    have hFK : ∀ n, F (K n) = n := fun n => by
      have h1 : Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) (F (K n)) = Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) n := by rw [← hF1, hK1]
      rcases lt_trichotomy (F (K n)) n with hc | hc | hc
      · exact absurd h1 (hlt _ _ hc n.2).ne'
      · exact hc
      · exact absurd h1 (hlt _ _ hc (F (K n)).2).ne
    intro a
    have h1 := hK2 a
    rw [eq_self_of_strictMono hKm hFm hFK a] at h1
    exact h1
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam (M.lam ρ) := fun ρ => by
    have he := M.enum ρ
    refine ⟨he.1, fun a => ?_⟩
    obtain ⟨-, f, hf, hS⟩ := he
    rw [hp ρ] at hS
    have hm : (f a, M.ε ρ a) ∈ Formalism.L2.NTheta.holPar _ _ (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hm
    have hx1 := congrArg Prod.fst hx
    have hn : (((Wc D i).rank : ℕ) : ℝ) = (((Wc D i).sig (tauE D ρ)).1 : ℝ) + ((Wc D i).sig (tauE D ρ)).2 := by
      rw [← hpq ρ]; push_cast; rfl
    dsimp only at hx1
    rw [hf a, ← hx1, hn]
    rcases x with c | c
    · refine ⟨Formalism.IndefR.Links.kapAt (Wc D i) σ ρ (Sum.inl c) - ((Wc D i).sig (tauE D ρ)).2 - (c : ℕ), ?_⟩
      simp only [Formalism.L2.NTheta.holEnt, Sum.elim_inl]
      push_cast
      ring
    · refine ⟨Formalism.IndefR.Links.kapAt (Wc D i) σ ρ (Sum.inr c) - (c : ℕ), ?_⟩
      simp only [Formalism.L2.NTheta.holEnt, Sum.elim_inr]
      push_cast
      ring
  refine ⟨fun ρ => ⟨hc ρ, _, (Nat.le_add_right _ _).trans (hpq ρ).le, heps ρ⟩, ?_, heps⟩
  choose w hw using fun ρ a => Formalism.QuantumDeterminants.low_k_integrable_holds _ (M.ε ρ) _ (hc ρ).2 a
  exact ⟨fun ρ c => w ρ (revNeg (M.ε ρ) (arr (nNeg (M.ε ρ)) c)), fun ρ c => (hw ρ _).symm⟩

end GlobalTheory.HolLabel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesModelHolomorphicPositiveSignsFirstStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

theorem _root_.GlobalTheory.T.discreteSeriesModel_holomorphic_positiveSignsFirst : ∀ (D : D7) (σ : D.what₂.LL →+* ℂ), (∀ ρ, Formalism.IndefR.Links.labE σ (Formalism.IndefR.Links.lab σ ρ) = tauE D ρ) → ∀ (i : Fin D.R.m) (M : DSModel (Wc D i) (Formalism.IndefR.Links.parAt (Wc D i) σ)), GlobalTheory.HolDict.HolShape M ∧ (∃ wt, GlobalTheory.HolDict.WtIs M wt) ∧ ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < pW D i ρ) := by
  first | exact @GlobalTheory.HolLabel.holShape_signs_first | exact GlobalTheory.HolLabel.holShape_signs_first | (intros; apply GlobalTheory.HolLabel.holShape_signs_first <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LabelAtRealPlaceEqEmbeddingOverReflexField

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.LabAtRealPlace

theorem sigmaOf_sqrt (D : D7) (τ : D.what₂.Tau) :
    D.host.sigmaOf ((D.eTau τ).1 : D.R.GG) D.host.sqrtMinusD = D.host.sqrtMinusD := by
  have h1 : D.host.galE (D.host.sigmaOf ((D.eTau τ).1 : D.R.GG)) ∈
      D.R.Psi := by
    rw [show D.host.galE (D.host.sigmaOf ((D.eTau τ).1 : D.R.GG)) = (D.eTau τ).1 from D.host.gal.apply_symm_apply _]
    exact (D.eTau τ).2
  exact (D.host.galE_mem_Psi_iff _).1 h1

theorem labE_sqrt (D : D7) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (h : IsEmbOverK D σ s) (τ ρ : D.what₂.Tau) :
    Formalism.IndefR.Links.labE σ τ D.host.sqrtMinusD = tauE D ρ D.host.sqrtMinusD := by
  have hm : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have e1 : Formalism.IndefR.Links.labE σ τ D.host.sqrtMinusD = σ (D.embE D.host.sqrtMinusD) := by
    show σ (D.embE (D.host.sigmaOf ((D.eTau τ).1 : D.R.GG) D.host.sqrtMinusD)) = _
    rw [sigmaOf_sqrt]
  have e2 : Formalism.IndefR.Conj.labE D.what₂.embLL ρ D.host.sqrtMinusD = D.what₂.embLL (D.embE D.host.sqrtMinusD) := by
    show D.what₂.embLL (D.embE (D.host.sigmaOf ((D.eTau ρ).1 : D.R.GG) D.host.sqrtMinusD)) = _
    rw [sigmaOf_sqrt]
  rw [e1, h.2 _ hm, ← e2, Formalism.IndefR.Conj.labE_base]

theorem labE_lab (D : D7) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (h : IsEmbOverK D σ s) (ρ : D.what₂.Tau) :
    Formalism.IndefR.Links.labE σ (Formalism.IndefR.Links.lab σ ρ) = tauE D ρ := by
  have hex : ∃ τ, Formalism.IndefR.Links.labE σ τ = tauE D ρ ∨
      Formalism.IndefR.Links.labE σ τ = (starRingEnd ℂ).comp (tauE D ρ) := by
    obtain ⟨B, hB⟩ := Formalism.IndefR.Conj.labExists σ
    have h' := hB (B.perm.symm ρ)
    rw [Formalism.IndefR.Conj.ArchLab.emb, Equiv.apply_symm_apply] at h'
    refine ⟨B.perm.symm ρ, ?_⟩
    split_ifs at h'
    exacts [Or.inl h', Or.inr h']
  rw [Formalism.IndefR.Links.lab, dite_eq_left hex]
  refine hex.choose_spec.resolve_right fun h' => ?_
  have h2 := labE_sqrt D σ s h hex.choose ρ
  rw [h', RingHom.comp_apply] at h2
  obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h2
  have h3 : (tauE D ρ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
    rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD_sq D.host, map_neg, map_natCast]
  rw [hx] at h3
  have h4 : x ^ 2 = -(D.host.d : ℝ) := by exact_mod_cast h3
  have h5 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  nlinarith [sq_nonneg x]

theorem main : ∀ (D : D7) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), IsEmbOverK D σ s → ∀ ρ, Formalism.IndefR.Links.labE σ (Formalism.IndefR.Links.lab σ ρ) = tauE D ρ := fun D σ s h ρ => labE_lab D σ s h ρ

end GlobalTheory.LabAtRealPlace
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LabelAtRealPlaceEqEmbeddingOverReflexFieldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

theorem _root_.GlobalTheory.T.labelAtRealPlace_eq_embedding_over_reflexField : ∀ (D : D7) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), IsEmbOverK D σ s → ∀ ρ, Formalism.IndefR.Links.labE σ (Formalism.IndefR.Links.lab σ ρ) = tauE D ρ := by
  first | exact @GlobalTheory.LabAtRealPlace.main | exact GlobalTheory.LabAtRealPlace.main | (intros; apply GlobalTheory.LabAtRealPlace.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JointHarmonicsLowestKTypeCoefficientReal

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

noncomputable section

namespace GlobalTheory.FockCoefReal

theorem l2_self_eq_setIntegral_norm_sq {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓧 : Set X) (f : X → ℂ) :
    l2 μ 𝓧 f f = ((∫ w in 𝓧, ‖f w‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  show (∫ w in 𝓧, f w * starRingEnd ℂ (f w) ∂μ) = _
  rw [← integral_complex_ofReal]
  congr 1
  funext w
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem fockIp_eq_fock {ι : Type} (P Q : MvPolynomial ι ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp P Q = Formalism.E.fock P Q := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp, Formalism.E.fock, Formalism.A.mfact, starRingEnd_apply]



theorem fock_coef_real : GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts.HarmonicModule → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → ∀ g : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) ρ)) → ∀ (e e' : ∀ ρ, lowT (R.MW i σ) ρ) (w w' : c.W), l2 μ 𝓧 (ω (1, realElt R.θ (Wc D i) g) (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e) w))) (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e') w')) = Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) * (∏ ρ, ⟪((e' ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ), (R.MW i σ).rep ρ (g ρ) ((e ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ) * ⟪w', w⟫_ℂ * l2 μ 𝓧 f f := by
  intro _ D G _ _ Pl0 T A Ks _ _ _ R F _ i t σ s P cμ cη m ω BW f₀ f c io hL μ 𝓧 hcv g hg e e' w w'
  obtain ⟨hf0, hfth, hcartV, hvac⟩ := GlobalTheory.T.thetaLiftDatum_isNonzeroFockVacuum R F i t σ s P cμ cη m ω BW f₀ f c io hL μ 𝓧 hcv
  obtain ⟨hCore, -, hEmb, -, -, hW, hBW, -, hPt, hc, hIo⟩ := hL
  have hm := hCore.models
  have hθ : IsInfFam R.θ := hm.inf
  have hlab := GlobalTheory.T.labelAtRealPlace_eq_embedding_over_reflexField D σ s hEmb
  obtain ⟨hHol, hWt, hε⟩ := GlobalTheory.T.discreteSeriesModel_holomorphic_positiveSignsFirst D σ hlab i (R.MW i σ)
  let pt := pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) BW f
  have hpt : ptAt R i σ BW f = ⇑pt := rfl
  have hptTh : ∀ Q, IsThetaFunO R.ψ (Vc D i) (Wc D i) (pt Q) := hPt
  have hpq : ∀ τ, pW D i τ + qW D i τ ≤ (Vc D i).rank := fun τ => by
    have e1 := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
    have e2 := Formalism.IndefR.FWT.rank_Wc i
    have e3 := r_le_V i
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.qW] at e1
    simp only [pW, qW]
    omega
  have hpW : ∀ τ, pW D i τ ≤ (Wc D i).rank := fun τ => by
    have e1 := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.qW] at e1
    simp only [pW]
    omega
  have hharm := fun τ => GlobalTheory.T.mixed_laplacian_kills_product_of_minors D (Wc D i).rank (Vc D i).rank (pW D i) (qW D i) (aPlAt D i σ) (aMiAt D i σ) hpq τ
  have hkill := GlobalTheory.T.harmonicFockVectors_killed_by_lowering_adaptedBasis D R.ψ R.θ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hθ hW _ (R.MW i σ) (D.sp.V_sig _) (D.sp.W_sig _)
    (R.BV i) (hm.BV i) (pW D i) hε BW hBW f hfth hvac (deltaAtEmb D i σ) hharm
  have hee := GlobalTheory.T.fockCoefficient_eq_const_mul_lowestKTypeCoefficient D R.ψ R.θ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hθ hW _ (R.MW i σ) hHol hWt μ 𝓧 hcv c hc pt hptTh
    (deltaAtEmb D i σ) io hIo hkill
  have hww := GlobalTheory.T.thetaLiftPairing_lowestWeight_schur_polarisation D R.ψ R.θ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hθ hW _ (R.MW i σ) μ 𝓧 hcv c hc pt hptTh
    (deltaAtEmb D i σ) io hIo hee g hg e e' w w'
  have hip := GlobalTheory.FockIsometry.ipO_pureTensorO D R.ψ R.θ (Vc D i) (Wc D i) hW.std hθ (fun _ => 1) (R.BV i)
    (cart (R.MW i σ)) BW (fun _ => (Vc D i).rank) (pW D i) (fun _ => le_rfl) hpW hcartV
    (fun ρ => GlobalTheory.FrameEquiv.isCartanInv_cart_model (R.MW i σ) ρ) (hm.BV i) hBW f hfth hvac μ 𝓧 hcv
    (deltaAtEmb D i σ) (deltaAtEmb D i σ)
  have hΔ : l2 μ 𝓧 (pt (deltaAtEmb D i σ)) (pt (deltaAtEmb D i σ)) =
      Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) * l2 μ 𝓧 f f := by
    rw [l2_self_eq_setIntegral_norm_sq μ 𝓧 f, ← fockIp_eq_fock]
    exact hip
  rw [hpt, hww, hΔ]
  ring

end GlobalTheory.FockCoefReal

end
end
end
