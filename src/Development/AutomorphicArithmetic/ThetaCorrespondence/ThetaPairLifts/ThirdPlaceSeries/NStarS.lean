module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowDef
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersFamilyConstStatement
public import Development.AutomorphicArithmetic.ResidueCharacters.NumCost
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
public import Development.AutomorphicArithmetic.ResidueCharacters.LenUnitInvariantsLe
public import Development.AutomorphicArithmetic.ResidueCharacters.LocAll
import Development.AutomorphicArithmetic.ResidueCharacters.NumParameters
public import Development.AutomorphicArithmetic.ResidueCharacters.NumRow
public import Development.AutomorphicArithmetic.ResidueCharacters.PlaceTypeConj
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclusionSplitOfHub
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.ResidueCharacters.ExistsUnion

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowGlue

section

@[expose] public section



section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
variable {D : D7}
end UpperTheory.N
theorem UpperTheory.N.starSF_of_rowC_alt (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) : _root_.UpperTheory.N.RowCAlt A B → _root_.UpperTheory.N.StarSelfDualCondition := by
  intro h eps Fm
  obtain ⟨x0, h0⟩ := h Fm
  obtain ⟨C0, x1, hC0, hpar⟩ := GlobalTheory.T.admissible_parameters_family_const Fm
  refine ⟨18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1, max 3 (max x0 x1),
    fun x hxx hx i HW F Cm X C₂ hS k hTw hs h2 π hπ => ?_⟩
  have h3 : 3 ≤ x := (le_max_left _ _).trans hxx
  have hb := h0 x (((le_max_left _ _).trans (le_max_right _ _)).trans hxx) hx i HW F Cm X C₂ hS k hTw hs h2 π hπ
  obtain ⟨-, -, -, hn, ht, -⟩ := hpar x (((le_max_right _ _).trans (le_max_right _ _)).trans hxx) hx i
  have hlog : 1 ≤ Real.log (Fm.L x i).sc.x := by
    rw [Fm.L_x x i hx, Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hc : UpperTheory.N.costC (Fm.L x i) A B ((Fm.D x i).nd.l k) ≤
      midF (Fm.L x i) (18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1) :=
    UpperTheory.N.Num.cost_le (Fm.L x i) (Fm.params x hx i) hA hB hC0 hlog hn ht hs le_rfl
  unfold Bd at hb ⊢
  linarith
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfSetup

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
theorem UpperTheory.N.n_at_bounds_of_setup (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ) (S : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂) :
    UpperTheory.N.RowAt L X.ρ 6000 30000 := by
  intro i hTw hs h2 π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hgk : ∀ k, D.nd.l i ≠ D.host.g k := fun k e =>
    UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond k) (e ▸ hs)
  have hg : D.nd.l i ∉ TwistedPlaces.gset D := by
    simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hgk 0, hgk 1⟩
  have hL : EmbeddingTypes.hypL i := ⟨by have := hl.two_le; omega, Or.inr hs, fun h => absurd hs h, hgk 0, hgk 1⟩
  have hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1 :=
    D.host.QS_split _ hl h2 (Nat.dvd_of_mem_primeFactors hs)
  obtain ⟨dc, -, h⟩ := _root_.UpperTheory.N.conclusion_split_alt hP D L P nch HW F Cm X C₂ S i hg D.host.condN
    (UpperTheory.N.cycAt_of i fun e => absurd e h2) hL (UpperTheory.N.decl_split D i h2 hj) (UpperTheory.N.locAll hP D HW F Cm (D.nd.l i))
  obtain ⟨hB, hW, hz⟩ := h π hπ
  have hs1 : 1 ≤ D.nd.s0 i := by rw [D.nd.restNLevelExponent_of_odd i h2]; exact le_max_left _ _
  have hh := UpperTheory.N.h0_le D i dc.col (fun e => absurd e h2) hs1 (fun u hu => (dc.cover u).1 (Or.inr hu))
  have hb := UpperTheory.N.Num.one_le_b L
  have hbB : L.sc.b ≤ RowSmall.hB L := (UpperTheory.N.Num.hB_bounds L P).1
  have hf : (⌊2 * L.sc.b⌋₊ : ℝ) ≤ 2 * L.sc.b := Nat.floor_le (by linarith)
  refine UpperTheory.N.bound_smallPrime_of_splitBound_cyclotomic L P X.ρ S.kill S.sha i hTw hs π hπ dc _ _ _ ?_ ?_ ?_ hW (by exact_mod_cast hh) hz hB
  · have : (Formalism.MainNotions.N.hN L : ℝ) ≤ RowSmall.hB L := Nat.floor_le (by
      show 0 ≤ RowSmall.hB L
      linarith)
    linarith
  · unfold GlobalTheory.HubX.hOf
    push_cast
    linarith
  · linarith
theorem UpperTheory.N.exists_nonneg_c_constants_of_prints : Hypotheses₂ → ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.RowCAlt A B :=
  fun hP => ⟨6000, 30000, by norm_num, by norm_num, fun Fm => ⟨0, fun x _ hx i HW F Cm X C₂ S =>
    _root_.UpperTheory.N.n_at_bounds_of_setup hP _ _ (Fm.params x hx i) _ HW F Cm X C₂ S⟩⟩
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NStarS

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
theorem UpperTheory.N.starSF_of_prints (hP : Hypotheses₂) : _root_.UpperTheory.N.StarSelfDualCondition := by
  obtain ⟨A, B, hA, hB, h⟩ := _root_.UpperTheory.N.exists_nonneg_c_constants_of_prints hP
  exact _root_.UpperTheory.N.starSF_of_rowC_alt A B hA hB h
end
end
end
