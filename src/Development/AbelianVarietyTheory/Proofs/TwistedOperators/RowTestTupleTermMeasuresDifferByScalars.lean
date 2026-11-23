module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridVertexMeasureEqOfSameNormalisation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridRowLevelZeroInfUnitaryEqDatumLevelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagGenDiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSumRowCol
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestLastColumnLevelIffGridVertexLevelVolumeOn

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLevelUnit

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem levJ_grid_succ (G : GridData L sc) (t : T) (i n : ℕ) (hn : n ≠ 0) :
    levJ G t (.grid (i + 1) n) = G.levMax (.grid (i + 1) n) := by
  cases n with
  | zero => exact absurd rfl hn
  | succ n => rfl

theorem levJ_grid_zero (G : GridData L sc) (t : T) (n : ℕ) (hn : n ≠ 0) :
    HEq (levJ G t (.grid 0 n)) (levCol L t (n - 1)) := by
  cases n with
  | zero => exact absurd rfl hn
  | succ n => exact HEq.rfl

theorem levRow_iff_levJ : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t i (hi : i ≤ D.R.m) (k : FinPt ch.G (.grid i D.R.m)), finG (ch.G.V (.grid i D.R.m)) k ∈ ch.S.toGridChoice.levRow t i hi ↔ finG (ch.G.V (.grid i D.R.m)) k ∈ levJ ch.G t (.grid i D.R.m) :=
  ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s ch _ _ t i hi k => by
    have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
    have hU : finG (ch.G.V (.grid i D.R.m)) k ∈ UA D.sp.cm (ch.G.V (.grid i D.R.m)).gram := GlobalTheory.LevSplit.finE_mem_UA _ _
    suffices e : ch.S.toGridChoice.levRow t i hi ⊓ UA D.sp.cm (ch.G.V (.grid i D.R.m)).gram = levJ ch.G t (.grid i D.R.m) by
      rw [← e]; exact ⟨fun h => ⟨h, hU⟩, fun h => h.1⟩
    clear hU k
    cases i with
    | zero =>
      apply eq_of_heq
      exact (GlobalTheory.T.gridRowLevel_zero_inf_unitary_eq_datumLevel ch.W ch.S.toGridChoice s.core.lev t hi).trans
        ((levJ_grid_zero ch.G t D.R.m hm).trans (levCol_top _ t (j := D.R.m - 1) (by omega))).symm
    | succ i =>
      rw [levJ_grid_succ ch.G t i D.R.m hm]
      exact GlobalTheory.FunObj.GridChoice.levRow_succ_inf_UA ch.W ch.S.toGridChoice t i hi⟩⟩

end GlobalTheory.RowLevelUnit
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestLastColumnLevelIffGridVertexLevelVolumeOnStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowTest_lastColumn_level_iff_gridVertexLevelVolumeOne : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t i (hi : i ≤ D.R.m) (k : FinPt ch.G (.grid i D.R.m)), finG (ch.G.V (.grid i D.R.m)) k ∈ ch.S.toGridChoice.levRow t i hi ↔ finG (ch.G.V (.grid i D.R.m)) k ∈ levJ ch.G t (.grid i D.R.m) := by
  first | exact @GlobalTheory.RowLevelUnit.levRow_iff_levJ | exact GlobalTheory.RowLevelUnit.levRow_iff_levJ | (intros; apply GlobalTheory.RowLevelUnit.levRow_iff_levJ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.Divisors.MiddleNotMem

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.FunObj.UnfModel
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj

section Alg
variable {k : Type*} [Field k] {n n' n'' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  [Fintype n''] [DecidableEq n'']

theorem symPr_zero (C : Subgroup (GL (n ⊕ Fin 0) k)) : symPr C = C.comap (embX 0) := by
  have h : ∀ p, N k n 0 p = ⊥ := fun p => (Subgroup.eq_bot_iff_forall _).2 fun g hg => Units.ext (by
    ext (r | r) (s | s)
    · exact RootEx.Model.mem_N_iff.1 hg _ _ le_rfl
    all_goals first | exact r.elim0 | exact s.elim0)
  ext g
  show (∃ u ∈ symN k n 0, u * embX 0 g ∈ C) ↔ _
  simp [symN, h]
end Alg

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {G : Grid (k := k)} (hs : 1 ≤ G.s) [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)



end GlobalTheory.FunObj.UnfModel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestTopLevelLastIffGridVertexLevelVolumeOne

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastLevUnit

open GlobalTheory.FunObj.UnfModel GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx ValuativeRel

section Loc
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem symPr_of_eq_zero {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ} (hc : c = 0) (C : Subgroup (GL (n ⊕ Fin c) k)) :
    symPr C = C.comap (embX c) := by
  subst hc; exact symPr_zero C

theorem embX_frame_int {a c b : ℕ} (h : a + c = b) (z : GL (Fin a) k) :
    (∀ i j : Fin b, (embX c z).val ((frame h).symm i) ((frame h).symm j) ∈ 𝒪[k]) ↔ ∀ i j, z.val i j ∈ 𝒪[k] := by
  constructor
  · intro H i j
    have := H (frame h (.inl i)) (frame h (.inl j))
    simpa [embX] using this
  · intro H i j
    generalize (frame h).symm i = r
    generalize (frame h).symm j = s
    rcases r with r | r <;> rcases s with s | s <;> simp only [embX, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
    · exact H r s
    · exact zero_mem _
    · exact zero_mem _
    · rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _

theorem embX_mem_frame_KO {a c b : ℕ} (h : a + c = b) (x : GL (Fin a) k) :
    embX c x ∈ (KO k (Fin b)).map (frameGL (k := k) h).toMonoidHom ↔ x ∈ KO k (Fin a) := by
  rw [Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap, mem_KO_iff, mem_KO_iff, ← map_inv, ← map_inv]
  exact and_congr (embX_frame_int h x) (embX_frame_int h x⁻¹)

theorem symPr_conjLevel_last {Γ : Grid k} (hs : 1 ≤ Γ.s) (J : Γ.Level) (g : Γ.VertexGroup) {j : ℕ} (hj : j < Γ.m)
    (hlast : j + 1 = Γ.m) (hJ : J (Γ.m, j) = KO k _) (hg : g (Γ.m, j) = 1) :
    symPr (conjLevel hs J g hj) = KO k (Fin (topRank Γ j)) := by
  rw [symPr_of_eq_zero (by omega), conjLevel, hJ, hg]
  ext x
  rw [Subgroup.mem_comap, map_one]
  have e : Subgroup.map (MulEquiv.toMonoidHom (1 : MulAut (GL (Fin (Γ.rank (Γ.m, j))) k))) (KO k (Fin (Γ.rank (Γ.m, j)))) =
      KO k _ := Subgroup.map_id _
  rw [e]
  exact embX_mem_frame_KO _ x

end Loc
end GlobalTheory.LastLevUnit

namespace GlobalTheory.LastLevUnit

open GlobalTheory.FunObj.UnfModel GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx ValuativeRel GlobalTheory.FunObj.LevRowSucc

theorem elt_last {k : Type*} [Field k] {Γ : Grid k} {hs : 1 ≤ Γ.s} {J : Γ.Level} (ρ : Reps hs J) (β : Cosets hs J) {j : ℕ}
    (hj : j + 2 = Γ.m) : ρ.elt β (Γ.m, j + 1) = 1 := by
  rw [Reps.elt, onColumn_apply]
  dsimp only
  rw [dite_eq_right (by omega)]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem givenLevel_pos (G : GridData L sc) (t : T) (w : Pl D.host.E) :
    ∀ X : ℕ × ℕ, X.1 ≠ 0 → X.2 ≠ 0 → givenLevel G t w X = KO (Kw w) (Fin ((locGrid G t w).rank X))
  | (0, _), h, _ => absurd rfl h
  | (_ + 1, 0), _, h => absurd rfl h
  | (_ + 1, _ + 1), _, _ => rfl

theorem levTop_last_inf_UA {G : GridData L sc} (W : G.Weil) {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (β : CosFam G t) (j : ℕ) (h : j + 1 < D.R.m) (hj : j + 2 = D.R.m) :
    S.levTop t Φ β (j + 1) h ⊓ UA D.sp.cm (G.V (.top (j + 1))).gram = G.levMax (.top (j + 1)) := by
  rw [GridData.levMax]
  exact prodLev_inf_UA (S.βp_is (j + 1) h.le) (G.isV (X := .top (j + 1)) h.le fun _ e => by cases e).sd (locPl G t) _ _
    fun w => symPr_conjLevel_last one_le_sLen (givenLevel G t w.1) ((repsAt G t w.1).elt (β w)) h (by show j + 1 + 1 = D.R.m; omega)
      (givenLevel_pos G t w.1 _ (by show D.R.m ≠ 0; omega) (by show j + 1 ≠ 0; omega)) (elt_last _ _ hj)

theorem levTop_inf_UA_levJ {G : GridData L sc} (W : G.Weil) {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (β : CosFam G t) : ∀ n (h : n < D.R.m), n + 1 = D.R.m → 2 ≤ D.R.m →
    S.levTop t Φ β n h ⊓ UA D.sp.cm (G.V (.top n)).gram = levJ G t (.top n)
  | 0, _, h1, h2 => absurd h1 (by omega)
  | j + 1, h, h1, _ => levTop_last_inf_UA W S t Φ β j h (by omega)

theorem levTop_iff_levJ : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t Φ β (h : D.R.m - 1 < D.R.m), 2 ≤ D.R.m → ∀ (k : FinPt ch.G (.top (D.R.m - 1))),
    finG (ch.G.V (.top (D.R.m - 1))) k ∈ ch.S.toGridChoice.levTop t Φ β (D.R.m - 1) h ↔
      finG (ch.G.V (.top (D.R.m - 1))) k ∈ levJ ch.G t (.top (D.R.m - 1)) :=
  ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s ch _ _ t Φ β h hm k => by
    have hU : finG (ch.G.V (.top (D.R.m - 1))) k ∈ UA D.sp.cm (ch.G.V (.top (D.R.m - 1))).gram := GlobalTheory.LevSplit.finE_mem_UA _ _
    rw [← levTop_inf_UA_levJ ch.W ch.S.toGridChoice t Φ β (D.R.m - 1) h (by omega) hm]
    exact ⟨fun h' => ⟨h', hU⟩, fun h' => h'.1⟩⟩⟩

end GlobalTheory.LastLevUnit
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestTopLevelLastIffGridVertexLevelVolumeOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.rowTest_topLevel_last_iff_gridVertexLevelVolumeOne : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t Φ β (h : D.R.m - 1 < D.R.m), 2 ≤ D.R.m → ∀ (k : FinPt ch.G (.top (D.R.m - 1))),
    finG (ch.G.V (.top (D.R.m - 1))) k ∈ ch.S.toGridChoice.levTop t Φ β (D.R.m - 1) h ↔
      finG (ch.G.V (.top (D.R.m - 1))) k ∈ levJ ch.G t (.top (D.R.m - 1)) := by
  first | exact @GlobalTheory.LastLevUnit.levTop_iff_levJ | exact GlobalTheory.LastLevUnit.levTop_iff_levJ | (intros; apply GlobalTheory.LastLevUnit.levTop_iff_levJ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestTupleTermMeasuresDifferByScalars

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.TermScales

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem finE_toFin' (V : HSp D) (g : GA D V) : Lev.finE V (GlobalTheory.AutMult.toFin V g : GA D V) = Lev.finE V g := by
  conv_rhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
  have hx : Lev.finE V (GlobalTheory.AutMult.toInf V g : GA D V) = 1 := by
    simp only [Lev.finE, MonoidHom.comp_apply]
    rw [show finHom V (GlobalTheory.AutMult.toInf V g : GA D V) = 1 from (GlobalTheory.AutMult.toInf V g).2, map_one]
  rw [map_mul, hx, one_mul]

theorem isAt_congr (M : Vol G) (X : Node) {K K' : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))}
    (hK : ∀ k : FinPt G X, finG (G.V X) k ∈ K ↔ finG (G.V X) k ∈ K') (h : M.IsAt X K) : M.IsAt X K' := by
  have hK' : ∀ g : GA D (G.V X), Lev.finE (G.V X) g ∈ K ↔ Lev.finE (G.V X) g ∈ K' := by
    intro g
    rw [← finE_toFin' (G.V X) g]
    exact hK (GlobalTheory.AutMult.toFin (G.V X) g)
  unfold Vol.IsAt at h ⊢
  split_ifs at h ⊢
  · simpa only [IsMeasDef, Lev.IsMeasLevDef, Lev.IsMeasLevW, hK'] using h
  · simpa only [Lev.IsMeasFD, Lev.IsMeasLev, Lev.IsMeasLevW, hK'] using h

theorem isHaar_of_isAt (M : Vol G) (X : Node) {K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))} (h : M.IsAt X K) :
    (M.ν X).IsHaarMeasure := by
  unfold Vol.IsAt at h
  split_ifs at h
  · exact h.1.1
  · exact h.1.1

end GlobalTheory.TermScales


open GlobalTheory.TermScales in
theorem GlobalTheory.TermScales.exists_scales : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t Φ β (M M' : Vol ch.G), M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' →
    ∃ x : Node → ℝ≥0, Scales M M' x ∧
      ∀ X : Node, DefNode D.R.m X → X ≠ .top D.R.m → (∀ j ∈ idx D, X ≠ .top j) → x X = 1 := by
  refine big_mono ?_ (Big.and GlobalTheory.T.rowTest_lastColumn_level_iff_gridVertexLevelVolumeOne GlobalTheory.T.rowTest_topLevel_last_iff_gridVertexLevelVolumeOne)
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch hch
  obtain ⟨hrow, htop⟩ := hch
  intro t Φ β M M' hM hM'
  have hdef : ∀ X : Node, DefNode D.R.m X → X ≠ .top D.R.m → Node.InRange D.R.m X := by
    intro X hX _
    rcases X with ⟨i, j⟩ | i | j
    · exact ⟨hX.1, hX.2.le⟩
    · exact hX.elim
    · exact hX
  have hM'at : ∀ X : Node, DefNode D.R.m X → X ≠ .top D.R.m → ∃ K, M'.IsAt X K := by
    intro X hX hne
    rcases X with ⟨i, j⟩ | i | j
    · obtain ⟨hi, rfl⟩ := hX
      exact ⟨_, hM'.2 i hi⟩
    · exact hX.elim
    · have hj : j < D.R.m := lt_of_le_of_ne hX (fun e => hne (by rw [e]))
      exact ⟨_, hM'.1 j hj⟩
  have key : ∀ X : Node, ∃ c : ℝ≥0, (DefNode D.R.m X → X ≠ .top D.R.m → M.ν X = c • M'.ν X) ∧
      (DefNode D.R.m X → X ≠ .top D.R.m → (∀ j ∈ idx D, X ≠ .top j) → c = 1) := by
    intro X
    by_cases hX : DefNode D.R.m X ∧ X ≠ .top D.R.m ∧ ∀ j ∈ idx D, X ≠ .top j
    · obtain ⟨hd, hne, hidx⟩ := hX
      refine ⟨1, fun _ _ => ?_, fun _ _ _ => rfl⟩
      rw [one_smul]
      have hMX := hM.vtx X (hdef X hd hne)
      rcases X with ⟨i, j⟩ | i | j
      · obtain ⟨hi, rfl⟩ := hd
        exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ hMX (isAt_congr M' _ (hrow t i hi) (hM'.2 i hi))
      · exact hd.elim
      · have hj : j < D.R.m := lt_of_le_of_ne hd (fun e => hne (by rw [e]))
        have hj' : j ∉ idx D := fun hm => hidx j hm rfl
        simp only [idx, List.mem_range'_1] at hj'
        rcases Nat.eq_zero_or_pos j with rfl | hpos
        · exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ hMX (hM'.1 0 hj)
        · have e : j = D.R.m - 1 := by omega
          have h2 : 2 ≤ D.R.m := by omega
          subst e
          exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ hMX (isAt_congr M' _ (htop t Φ β hj h2) (hM'.1 _ hj))
    · by_cases hX' : DefNode D.R.m X ∧ X ≠ .top D.R.m
      · obtain ⟨hd, hne⟩ := hX'
        obtain ⟨i1, i2, i3, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (ch.G.V X)
        obtain ⟨K', hK'⟩ := hM'at X hd hne
        haveI := isHaar_of_isAt M X (hM.vtx X (hdef X hd hne))
        haveI := isHaar_of_isAt M' X hK'
        exact ⟨Measure.haarScalarFactor (M.ν X) (M'.ν X), fun _ _ => Measure.isMulLeftInvariant_eq_smul _ _,
          fun h1 h2 h3 => (hX ⟨h1, h2, h3⟩).elim⟩
      · exact ⟨1, fun h1 h2 => (hX' ⟨h1, h2⟩).elim, fun h1 h2 _ => (hX' ⟨h1, h2⟩).elim⟩
  choose x hx using key
  exact ⟨x, fun X h1 h2 => (hx X).1 h1 h2, fun X h1 h2 h3 => (hx X).2 h1 h2 h3⟩
end
end
end
