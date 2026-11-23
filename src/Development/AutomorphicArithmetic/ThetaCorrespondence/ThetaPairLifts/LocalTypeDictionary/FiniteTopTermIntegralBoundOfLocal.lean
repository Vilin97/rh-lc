module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumEqualSignKernelLossesBounded
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Imports
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ImportsBis
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ImportsTer
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.KerStd
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LatMove
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.MatLat
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.RatMove
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DivisorDecompositionOfLocalFactors

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.divisor_decomposition_of_local_factors : ∃ C1 : ℝ, 0 < C1 ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ (ch : Choice R) (CF : ℝ), ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.NormSum.Inp D →
      DictAt ch → ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ →
      ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 →
      d.P = locPl ch.G t → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ch.S.Z.IsRatAt d x y →
      ∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away ch.G t w →
      ∀ (a : ℝ) (v : VV ℂ (wt ch.G p.small)), InLat _ w a (latAt ch.S.toGridChoice p.small x) v →
        InLat _ w (a + (vw w ((l : ℕ) : D.what₂.LL) : ℝ) * C1 *
            GlobalTheory.SumSize.TopInt.kerLoss ch.G δ C1 large₂.sc.b p.small p.big l (padicValNat l k))
          (latAt ch.S.toGridChoice p.big y) (ch.S.Z.kkMap 1 d x y v) := by
  refine ⟨1, one_pos, ?_⟩
  intro D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch CF _ _ _ _ hI hDict S δ hL t p hp k d hk hd hz hP x y hR w l hl hw hA a v hv
  have hn := DefPair.nodes hp
  obtain ⟨k', hk', hd', hle, hsp⟩ := UpperTheory.WildA.depth large₂ hS.size d hP w l hl hw hA k hk hd
  obtain ⟨r, U, hU, e, hx⟩ := UpperTheory.WildA.toStd ch.S.toGridChoice p.small hn.1 l hl x
  obtain ⟨r', U', hU', e', hy⟩ := UpperTheory.WildA.toStd ch.S.toGridChoice p.big hn.2 l hl y
  have hmv := UpperTheory.WildA.move ch.S.Z hS.core.lev t p hp d x r y r' U U' hU hU'
  have hR' : ch.S.Z.IsRatAt d (r * x) (r' * y) := by
    intro i j
    have := UpperTheory.WildA.ratMove D _ _ _ _ _ _ hmv (fun i j => by
      have := hR i j
      rwa [Normal.kkIn, LinearMap.toMatrix_apply] at this) i j
    rwa [Normal.kkIn, LinearMap.toMatrix_apply]
  have h1 := UpperTheory.WildA.kerStd D large₂ Γ Pl0 T A Ks R F hS ch hI hDict S δ hL t p hp k' d hk' hd' hz hP _ _ hR' w l hl hw hsp hx hy
    large₂.sc.b
  have h2 := (UpperTheory.WildA.latMove D _ w a _ U v).2 hv
  rw [← e] at h2
  have h3 := UpperTheory.WildA.matLat D _ _ w l hl hw _ _ hx hy _ _ h1 a _ h2
  have h4 := LinearMap.congr_fun hmv v
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h4
  rw [h4, e'] at h3
  refine GlobalTheory.SumSize.TopInt.inLat_mono ((UpperTheory.WildA.latMove D _ w _ _ U' _).1 h3) ?_
  rw [mul_one]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (GlobalTheory.SumSize.TopInt.kerLoss_mono _ _ _ _ _ _ _ hle)
    (by exact_mod_cast GlobalTheory.SumSize.TopInt.vw_natCast_nonneg w l))
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteTopTermIntegralBoundOfLocal

section

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SumSize.TopInt
theorem finite_top_term_integral_bound_of_local (hPL : ∃ C1 : ℝ, 0 < C1 ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ (ch : Choice R) (CF : ℝ), ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.NormSum.Inp D →
      DictAt ch → ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ →
      ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 →
      d.P = locPl ch.G t → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ch.S.Z.IsRatAt d x y →
      ∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away ch.G t w →
      ∀ (a : ℝ) (v : VV ℂ (wt ch.G p.small)), InLat _ w a (latAt ch.S.toGridChoice p.small x) v →
        InLat _ w (a + (vw w ((l : ℕ) : D.what₂.LL) : ℝ) * C1 *
            GlobalTheory.SumSize.TopInt.kerLoss ch.G δ C1 large₂.sc.b p.small p.big l (padicValNat l k))
          (latAt ch.S.toGridChoice p.big y) (ch.S.Z.kkMap 1 d x y v)) (hSL : ∀ C1 : ℝ, 0 < C1 → ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ C0 : ℝ, ∀ ε C : ℝ, C0 ≤ C → ∃ x₀ : ℝ,
      ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
      ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → GlobalTheory.NormSum.Inp D →
      ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ →
        Loss (GlobalTheory.SumSize.TopInt.topDl ch.G δ C1 large₂.sc.b) (bOne ch.G C large₂.sc.b)) :
    _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → FinTopK := by
  intro hP hI hD hE
  obtain ⟨C1, hC1, hPL⟩ := hPL
  obtain ⟨CF1, hS⟩ := hSL C1 hC1
  obtain ⟨CF2, hD⟩ := hD
  obtain ⟨CF3, hE⟩ := hE
  refine ⟨max CF1 (max CF2 CF3), fun CF hCF => ?_⟩
  obtain ⟨C01, hS⟩ := hS CF (le_of_max_le_left hCF)
  obtain ⟨C02, hD⟩ := hD CF (le_trans (le_max_left _ _) (le_of_max_le_right hCF))
  obtain ⟨C03, hE⟩ := hE CF (le_trans (le_max_right _ _) (le_of_max_le_right hCF))
  refine ⟨max C01 (max C02 C03), fun ε C hC => ?_⟩
  obtain ⟨x1, hS⟩ := hS ε C (le_of_max_le_left hC)
  obtain ⟨x2, hD⟩ := hD ε C (le_trans (le_max_left _ _) (le_of_max_le_right hC))
  obtain ⟨x3, hE⟩ := hE ε C (le_trans (le_max_right _ _) (le_of_max_le_right hC))
  refine ⟨max x1 (max x2 x3), fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hs ch hch hsc hfo => ?_⟩
  have dict : DictAt ch :=
    hD D large₂ he (le_trans (le_max_left _ _) (le_of_max_le_right hx)) Γ Pl0 T A Ks R F hs ch hch hsc hfo
  have dep : DepthAt ch :=
    hE D large₂ he (le_trans (le_max_right _ _) (le_of_max_le_right hx)) Γ Pl0 T A Ks R F hs ch hch hsc hfo
  obtain ⟨S, δ, hL⟩ := (GlobalTheory.NormSum.letters_and_sizes D (hI D).g1).1
  have loss := hS D large₂ he (le_of_max_le_left hx) Γ Pl0 T A Ks R F hs ch hch hsc hfo (hI D) S δ hL
  refine ⟨topDl ch.G δ C1 large₂.sc.b, loss, ?_⟩
  intro t w hw Φ β d hocc c j a v hv
  obtain ⟨hβ, τ, hτ, hd⟩ := hocc
  have hτ' := hτ
  obtain ⟨hk, ⟨e, -, h1, -⟩, h3⟩ := hτ'
  have hrat := (hfo.isRatAt hβ hτ hd c).1 j
  have key := hPL D large₂ Γ Pl0 T A Ks R F hs ch CF hch hsc hfo hP (hI D) dict S δ hL t (.top t j)
    (show (j : ℕ) + 1 ≤ D.R.m from j.2) _ (d.1 j) hk ((h3 d hd).1 j) ((h1 d hd).1 j).2.2 ((h1 d hd).1 j).1 _ _ hrat
    w (primeUnder w) (primeUnder_prime w) (primeUnder_mem w) hw a v hv
  refine inLat_mono key ?_
  have hdep := (dep t Φ β hβ).2 w (primeUnder w) (primeUnder_prime w) (primeUnder_mem w) hw
  have := le_topDl ch.G hL.2.1 hC1.le large₂.sc.b w j.2 hdep
  linarith
theorem finite_top_term_integral_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → FinTopK :=
  _root_.GlobalTheory.SumSize.TopInt.finite_top_term_integral_bound_of_local _root_.GlobalTheory.T.divisor_decomposition_of_local_factors GlobalTheory.T.sum_equalSign_kernel_losses_bounded
end GlobalTheory.SumSize.TopInt
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.sum_size_finite_top_term_integral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → FinTopK := by
  first | exact @_root_.GlobalTheory.SumSize.TopInt.finite_top_term_integral_bound | exact _root_.GlobalTheory.SumSize.TopInt.finite_top_term_integral_bound | (intros; apply _root_.GlobalTheory.SumSize.TopInt.finite_top_term_integral_bound <;> assumption)
end
end
end
