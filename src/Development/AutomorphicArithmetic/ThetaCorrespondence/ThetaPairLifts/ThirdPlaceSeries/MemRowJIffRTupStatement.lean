module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedBy
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPatOne
public import Formalism.LocalToGlobal.Divisibility.DefGroup
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRedIffIsPat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelGeneratedByLocalUnipotentsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIdentityOffFreePositionsRightBlockIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsConjPlOfIdemSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotOfPlacedByStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColLevelMatchFamStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralAdaptedElementProperty

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZeroMem

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem h0_eq (D : D7) : 0 + 2 * D.R.rS + 2 = D.R.m := by
  obtain ⟨q, hq⟩ := D.R.m_even
  have := D.R.two_le_m
  unfold Ranks.rS
  omega




end GlobalTheory.LevZeroMem

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateSymmetricUnipotentPattern

section

@[expose] public section

namespace GlobalTheory.SymResCount

open Formalism.L2.DIV

theorem mem_unipSym_iff {K : Type} [CommRing K] {r : ℕ} (ρ κ : ℕ) (g : GL (Fin r) K) :
    g ∈ unipSym K r ρ κ ↔ ∀ a b : Fin r, ¬ (a.val < b.val ∧ ¬ (ρ ≤ a.val ∧ a.val < ρ + κ ∧ b.val = ρ + κ)) →
      (g : Matrix (Fin r) (Fin r) K) a b = (1 : Matrix (Fin r) (Fin r) K) a b := by
  constructor
  · rintro ⟨⟨hl, hd⟩, hc⟩ a b hab
    by_cases e : a = b
    · subst e; rw [hd a, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne e]
      have hne : a.val ≠ b.val := fun h => e (Fin.ext h)
      by_cases h1 : b.val < a.val
      · exact hl (show b.val < a.val from h1)
      · exact hc a b (by omega) (by omega) (by omega)
  · intro h
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j h0 h1 h2 => ?_⟩
    · have hij' : j.val < i.val := hij
      rw [h i j (by omega), Matrix.one_apply_ne (fun e => by rw [e] at hij'; omega)]
    · rw [h i i (by omega), Matrix.one_apply_eq]
    · rw [h i j (by omega), Matrix.one_apply_ne (fun e => by rw [e] at h1; omega)]

def permFn (ρ κ i : ℕ) : ℕ := if i < κ then ρ + i else if i < κ + ρ then i - κ else i

def permInv (ρ κ a : ℕ) : ℕ := if a < ρ then κ + a else if a < ρ + κ then a - ρ else a

def perm (r ρ κ : ℕ) (hr : κ + ρ ≤ r) : Fin r ≃ Fin r where
  toFun i := ⟨permFn ρ κ i.val, by unfold permFn; split_ifs <;> omega⟩
  invFun a := ⟨permInv ρ κ a.val, by unfold permInv; split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext; simp only; unfold permFn permInv; split_ifs <;> omega
  right_inv a := by
    apply Fin.ext; simp only; unfold permFn permInv; split_ifs <;> omega

theorem perm_val {r ρ κ : ℕ} (hr : κ + ρ ≤ r) (i : Fin r) : (perm r ρ κ hr i).val = permFn ρ κ i.val := rfl

theorem freePos_iff (ρ κ i j : ℕ) :
    GlobalTheory.SymRes.FreePos ρ κ i j ↔ (permFn ρ κ i < permFn ρ κ j ∧
      ¬ (ρ ≤ permFn ρ κ i ∧ permFn ρ κ i < ρ + κ ∧ permFn ρ κ j = ρ + κ)) := by
  unfold GlobalTheory.SymRes.FreePos permFn; split_ifs <;> omega

def reidx {K : Type} [CommRing K] (r ρ κ : ℕ) (hr : κ + ρ ≤ r) : GL (Fin r) K ≃* GL (Fin r) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K (perm r ρ κ hr)).toMulEquiv

theorem reidx_apply {K : Type} [CommRing K] {r ρ κ : ℕ} (hr : κ + ρ ≤ r) (g : GL (Fin r) K) (i j : Fin r) :
    ((reidx r ρ κ hr g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) (perm r ρ κ hr i) (perm r ρ κ hr j) =
      (g : Matrix (Fin r) (Fin r) K) i j := by
  simp [reidx, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

theorem reidx_mem_iff {K : Type} [CommRing K] {r ρ κ : ℕ} (hr : κ + ρ ≤ r) (g : GL (Fin r) K) :
    reidx r ρ κ hr g ∈ unipSym K r ρ κ ↔ GlobalTheory.SymRes.IsPat ρ κ g := by
  rw [mem_unipSym_iff]
  constructor
  · intro h i j hf
    have := h (perm r ρ κ hr i) (perm r ρ κ hr j) (by rw [perm_val, perm_val, ← freePos_iff]; exact hf)
    rw [reidx_apply] at this
    rw [this]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne (fun e' => e ((perm r ρ κ hr).injective e'))]
  · intro h a b hab
    obtain ⟨i, rfl⟩ := (perm r ρ κ hr).surjective a
    obtain ⟨j, rfl⟩ := (perm r ρ κ hr).surjective b
    rw [reidx_apply, h i j (by rw [freePos_iff, ← perm_val hr, ← perm_val hr]; exact hab)]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne (fun e' => e ((perm r ρ κ hr).injective e'))]

end GlobalTheory.SymResCount

namespace GlobalTheory.SymResCount
open Formalism.L2.DIV

theorem conj_pat_onto : ∀ (K : Type) [CommRing K] [Finite K] (r ρ κ : ℕ), r = κ + (2 * ρ + 1) →
    ∀ m : GL (Fin r) K, (∀ g : GL (Fin r) K, GlobalTheory.SymRes.IsPat ρ κ g → m * g * m⁻¹ ∈ Formalism.L2.DIV.unipSym K r ρ κ) →
    ∀ g : GL (Fin r) K, m * g * m⁻¹ ∈ Formalism.L2.DIV.unipSym K r ρ κ → GlobalTheory.SymRes.IsPat ρ κ g := by
  intro K _ _ r ρ κ hr m hm g hg
  have hr' : κ + ρ ≤ r := by omega
  haveI : Finite (GL (Fin r) K) := Finite.of_injective (fun u : GL (Fin r) K => (u : Matrix (Fin r) (Fin r) K)) Units.val_injective
  set S : Set (GL (Fin r) K) := {g | GlobalTheory.SymRes.IsPat ρ κ g} with hS
  set U : Set (GL (Fin r) K) := (unipSym K r ρ κ : Set (GL (Fin r) K)) with hU
  have hSU : (reidx (K := K) r ρ κ hr') '' S = U := by
    ext h
    constructor
    · rintro ⟨x, hx, rfl⟩; exact (reidx_mem_iff hr' x).2 hx
    · intro hh
      refine ⟨(reidx r ρ κ hr').symm h, (reidx_mem_iff hr' _).1 (by rw [MulEquiv.apply_symm_apply]; exact hh), by simp⟩
  have hinj : Function.Injective (fun x : GL (Fin r) K => m * x * m⁻¹) := fun x y h =>
    mul_left_cancel (mul_right_cancel h)
  have hc : (fun x : GL (Fin r) K => m * x * m⁻¹) '' S = U := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro _ ⟨x, hx, rfl⟩; exact hm x hx
    · rw [Set.ncard_image_of_injective S hinj, ← hSU, Set.ncard_image_of_injective S (reidx r ρ κ hr').injective]
    · exact Set.toFinite U
  have hg' : m * g * m⁻¹ ∈ U := hg
  rw [← hc] at hg'
  obtain ⟨x, hx, he⟩ := hg'
  have : x = g := hinj he
  rw [← this]; exact hx

end GlobalTheory.SymResCount
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemRowJIffRTup

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.LevZeroMem
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem conj_mem_K_two_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) {v : VCom f.c} (G : (_root_.GlobalTheory.BaseChain.com_z W).Pg → GLoc v)
    (hBot : GlobalTheory.LevZero.Bot (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) G)
    (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hBl : B.lev = f.c.B 0 D.R.rS h0) (hAd : B.Adapted (W.S.tr u).wt) (hTr : _root_.GlobalTheory.MiTop.LevTraceAlt f B)
    (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (W.S.tr u) a₀) (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = f.g.b 0)
    (hs : s = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧
      finE (D.sp.Y 0) κ ∈ St (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0))) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset))
    (hone : ∀ k ∈ levS (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W),
      (∀ PP ∈ (_root_.GlobalTheory.BaseChain.com_z W).Pg, redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) PP (finE (D.sp.Y 0) k) = 1) →
      (iotaX W.S.X W.Q.instEq (s * k * s⁻¹)).2 ∈ W.S.X.K2) :
    ∀ k ∈ levS (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W), (iotaX W.S.X W.Q.instEq (s * k * s⁻¹)).2 ∈ W.S.X.K2 := by
  have hemb : ∀ b, embA B.d B.o b = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o b : GA D (D.sp.Y 0)) := fun b =>
    by
      have h1 := congr_arg_heq (fun L : BesLev D D.R.rS => (embA L.d L.o : GA D L.A →* GA D L.V)) hBl
      have h2 : embA B.d B.o = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o : GA D (D.sp.X 0) →* GA D (D.sp.Y 0)) :=
        eq_of_heq h1
      exact DFunLike.congr_fun h2 b
  have hfl : flagN B.d = (flagN (f.c.bes 0 D.R.rS h0).d : Subgroup (GA D (D.sp.Y 0))) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => flagN L.d) hBl)
  refine GlobalTheory.T.indexZeroLevel_generated_by_local_unipotents (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) G h0 hBot
    (fun k : GA D (D.sp.Y 0) => (iotaX W.S.X W.Q.instEq (s * k * s⁻¹)).2 ∈ W.S.X.K2) ?_ ?_ ?_ hone
  · intro (k : GA D (D.sp.Y 0)) _ (k' : GA D (D.sp.Y 0)) _ q q'
    show (iotaX W.S.X W.Q.instEq (s * (k * k') * s⁻¹)).2 ∈ W.S.X.K2
    have e : s * (k * k') * s⁻¹ = (s * k * s⁻¹) * (s * k' * s⁻¹) := by group
    rw [e, map_mul, Prod.snd_mul]
    exact W.S.Y.hK.2.1 _ q _ q'
  · intro PP (n : GA D (D.sp.Y 0)) q hn _ _ hk
    have hn' : n ∈ flagN B.d := by rw [hfl]; exact hn
    have e : s * (t⁻¹ * n * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        (embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      rw [hs]; group
    have hk' : t⁻¹ * n * t ∈ levS (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) := by rw [ht]; exact hk
    have hKs := ((hSt (s * (t⁻¹ * n * t) * s⁻¹)).1 ⟨GlobalTheory.MemMatch.conj_mem_GfC W.S.X W.Q.instEq s _ hk'.1, by
      rw [map_mul, map_mul, map_inv, GlobalTheory.FrameConj.conj_mem_St_iff]; exact parLev_St hk'.2.1⟩).2
    have hN := ((B.tieN _).1 (GlobalTheory.CharLaws.embA_conj_mem B.d B.o (a₀ * a) hn')).2
    have goal : (iotaX W.S.X W.Q.instEq (s * (t⁻¹ * n * t) * s⁻¹)).2 ∈ W.S.X.K2 := by
      rw [e] at hKs ⊢
      generalize embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹ = n' at hN hKs ⊢
      rw [map_mul, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply] at hKs ⊢
      generalize iotaX W.S.X W.Q.instEq n' = y at hN hKs ⊢
      change (W.S.X.xu u)⁻¹ * y.2 * W.S.X.xu u ∈ _ at hKs ⊢
      refine Formalism.L2.SG.Pf.unipotent_conj_mem_level hN ?_
      have := Formalism.L2.SG.Pf.unitaryCongruence.K_mul _ (Formalism.L2.SG.Pf.unitaryCongruence.K_mul _ (W.S.X.xu_K u) hKs)
        (Formalism.L2.SG.Pf.unitaryCongruence.K_inv _ (W.S.X.xu_K u))
      rwa [show W.S.X.xu u * ((W.S.X.xu u)⁻¹ * y.2 * W.S.X.xu u) * (W.S.X.xu u)⁻¹ = y.2 by group] at this
    subst ht
    exact goal
  · intro b hb hk
    rw [← hemb b] at hk
    have h1 := (_root_.GlobalTheory.T.level_trace_adapted_translate_alt W hPk u f B hTr hAd a₀ hH0 b hb).1.1 hk
    have hab : a * b * a⁻¹ = b := by rw [← Subgroup.mem_center_iff.1 hac b]; group
    have e : s * (t⁻¹ * embA B.d B.o b * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        embA B.d B.o (a₀ * b * a₀⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      have : a₀ * b * a₀⁻¹ = (a₀ * a) * b * (a₀ * a)⁻¹ := by
        conv_lhs => rw [← hab]
        group
      rw [this, map_mul _ _ (a₀ * a)⁻¹, map_mul _ (a₀ * a) b, map_inv, hs]; group
    rw [← e] at h1
    rw [← hemb b]
    subst ht
    exact h1.2

theorem mem_K_two_iff_of_family_character (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) {v : VCom f.c} (G : (_root_.GlobalTheory.BaseChain.com_z W).Pg → GLoc v)
    (hBot : GlobalTheory.LevZero.Bot (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) G)
    (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hBl : B.lev = f.c.B 0 D.R.rS h0) (hAd : B.Adapted (W.S.tr u).wt) (hTr : _root_.GlobalTheory.MiTop.LevTraceAlt f B)
    (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (W.S.tr u) a₀) (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = f.g.b 0)
    (hs : s = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧
      finE (D.sp.Y 0) κ ∈ St (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0))) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset))
    (κ : GA D (D.sp.Y 0)) (hκ : κ ∈ GfC (D.sp.Y 0))
    (hκS : finE (D.sp.Y 0) κ ∈ St (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0))) :
    (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.K2 ↔
      rTup (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0)) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈
        (_root_.GlobalTheory.LevZero.datZero_alt W).P.H := by
  obtain ⟨hr, ξ, hL⟩ := hBot.mem.lev
  obtain ⟨N, hN, -⟩ := hBot.mem.base
  have hrk : (D.sp.Y 0).rank = D.R.rankY 0 := hBot.mem.rank
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by rw [hrk]; simp [Formalism.BasicNotions.Ranks.rankY]
  have hr' : D.R.r ≤ (D.sp.Y 0).rank := hr
  have hLb : _root_.GlobalTheory.LevZero.datZero_alt W = (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr' (_root_.GlobalTheory.BaseChain.com_z W).Pg ∅
      (_root_.GlobalTheory.BaseChain.com_z W).P (_root_.GlobalTheory.BaseChain.com_z W).chi ξ Frm.B) := hL
  have hlift : Lev.LiftsExist (D.sp.Y 0) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) :=
    GlobalTheory.ChainOnto.FlagAct.liftsExist_stage hBot.com hBot.mem
  obtain ⟨m, hm⟩ := GlobalTheory.MemMatch.exists_read W.S.X W.Q.instEq (_root_.GlobalTheory.BaseChain.com_z W).Pg hBot.typ hBot.com.split
    (fun PP => ⟨_, (hBot.loc PP).idem⟩) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) N hN s hSt
  have hin := _root_.GlobalTheory.LevZeroMem.conj_mem_K_two_alt W hPk f B G hBot h0 hBl hAd hTr a₀ hH0 a hac t s ht hs hSt (fun k hk h1 =>
    (hm k hk.1 (parLev_St hk.2.1)).2 fun PP => by rw [h1 PP.1 PP.2, mul_one, mul_inv_cancel]; exact one_mem _)
  have hpat : ∀ g : ∀ PP : (_root_.GlobalTheory.BaseChain.com_z W).Pg, GL (Fin D.R.r) (kP PP.1),
      g ∈ (_root_.GlobalTheory.BaseChain.com_z W).P.H ↔ ∀ PP, GlobalTheory.SymRes.IsPat D.R.rS D.R.k (g PP) :=
    fun g => (hBot.grp g).trans (forall_congr' fun PP => GlobalTheory.LevZero.exists_red_iff_isPat (G PP) PP.1 (hBot.loc PP).idem (g PP))
  rw [hLb] at hlift hin ⊢
  have hlev : ∀ k ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) k ∈ St (F := D.host.F) (E := D.host.E) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) →
      (fun PP : (_root_.GlobalTheory.BaseChain.com_z W).Pg => upperLeftBlock hr' (redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) PP.1 (finE (D.sp.Y 0) k))) ∈ (_root_.GlobalTheory.BaseChain.com_z W).P.H →
      k ∈ levS (D.sp.Y 0) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr' (_root_.GlobalTheory.BaseChain.com_z W).Pg ∅
        (_root_.GlobalTheory.BaseChain.com_z W).P (_root_.GlobalTheory.BaseChain.com_z W).chi ξ Frm.B) := by
    intro k hk hS hP
    refine ⟨hk, ?_⟩
    show finE (D.sp.Y 0) k ∈ lev _ _ _ _
    rw [mem_lev, mem_parLev]
    exact ⟨⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hS, fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ hn _,
      fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩, hP⟩
  obtain ⟨k₀, rfl⟩ : ∃ k₀, κ = s * k₀ * s⁻¹ := ⟨s⁻¹ * κ * s, by group⟩
  have hk₀ : k₀ ∈ GfC (D.sp.Y 0) := by
    have := GlobalTheory.MemMatch.conj_mem_GfC W.S.X W.Q.instEq s⁻¹ _ hκ
    rwa [show s⁻¹ * (s * k₀ * s⁻¹) * s⁻¹⁻¹ = k₀ by group] at this
  have hfe : finE (D.sp.Y 0) (s * k₀ * s⁻¹) =
      finE (D.sp.Y 0) s * finE (D.sp.Y 0) k₀ * (finE (D.sp.Y 0) s)⁻¹ := by rw [map_mul, map_mul, map_inv]
  rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff] at hκS
  rw [hfe, GlobalTheory.FrameConj.rTup_conj]
  refine ⟨fun hK => ?_, fun hP => hin k₀ (hlev k₀ hk₀ hκS hP)⟩
  refine (hpat _).2 fun PP => (GlobalTheory.MemMatch.isIdentityOffFreePositions_rightBlock_iff _ _ hr' hn _).2 ?_
  haveI : Finite (kP PP.1) := Ideal.finiteQuotientOfFreeOfNeBot PP.1.asIdeal PP.1.ne_bot
  have hrr : (D.sp.Y 0).rank = D.R.k + (2 * D.R.rS + 1) := by
    have := le_antisymm hn hr'
    have h0' := h0
    unfold Ranks.r at this
    omega
  refine GlobalTheory.SymResCount.conj_pat_onto (kP PP.1) _ D.R.rS D.R.k hrr (m PP) (fun g hg => ?_) _ ((hm k₀ hk₀ hκS).1 hK PP)
  let g0 : ∀ Q : (_root_.GlobalTheory.BaseChain.com_z W).Pg, GL (Fin D.R.r) (kP Q.1) := Function.update (fun _ => 1) PP (upperLeftBlock hr' g)
  have hg0 : g0 ∈ (_root_.GlobalTheory.BaseChain.com_z W).P.H := (hpat _).2 fun Q => by
    by_cases hQ : Q = PP
    · subst hQ
      simp only [g0, Function.update_self]
      exact (GlobalTheory.MemMatch.isIdentityOffFreePositions_rightBlock_iff _ _ hr' hn _).2 hg
    · simp only [g0, Function.update_of_ne hQ]
      exact GlobalTheory.SymRes.isPat_one _ _
  obtain ⟨k, hk, hkp, hkr⟩ := hlift g0
  have hkr' : (fun PP : (_root_.GlobalTheory.BaseChain.com_z W).Pg => upperLeftBlock hr' (redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) PP.1 (finE (D.sp.Y 0) k))) = g0 := hkr
  have h1 := (hm k hk (parLev_St hkp)).1 (hin k (hlev k hk (parLev_St hkp) (hkr' ▸ hg0))) PP
  have h2 : redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) PP.1 (finE (D.sp.Y 0) k) = g :=
    GlobalTheory.MemMatch.reductionBlock_injective_of_eq hr' hn _ _ ((congrFun hkr' PP).trans (Function.update_self _ _ _))
  rwa [h2] at h1

theorem mem_rowJ_iff_rTup_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → (κ ∈ rowJ W.S.X W.Q.instEq ↔ Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H) := by
  intro D L hT Gi Gl Kc Yd cX ex W hPk u f B hPl a₀ hH0 a _ hac hStab κ hκ hκS
  obtain ⟨k, _, _, _, _, ι, v, o, n, G, pl, hc, hv, hvt, hsh, hpin, hread, hbt⟩ := hPl
  have hBot := _root_.GlobalTheory.T.bessel_local_type_data_alt W hPk u f B k ι v o n G pl ⟨hc, hv, hvt, hsh, hpin, hread, hbt⟩
  have h0 := h0_eq D
  have hκ1 : (iotaX W.S.X W.Q.instEq κ).1 = 1 := (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff W.S.X W.Q.instEq κ).2 hκ
  show (iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.K2 ↔ _
  exact (and_iff_right hκ1).trans (_root_.GlobalTheory.LevZeroMem.mem_K_two_iff_of_family_character W hPk f B _ hBot h0 (hbt.lev h0) hbt.adapted hbt.trace a₀ hH0 a hac _ _ rfl rfl
    hStab κ hκ hκS)
end GlobalTheory.LevZeroMem
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemRowJIffRTupStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.central_adapted_element_property_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → (κ ∈ rowJ W.S.X W.Q.instEq ↔ Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H) := by
  first | exact @_root_.GlobalTheory.LevZeroMem.mem_rowJ_iff_rTup_alt | exact _root_.GlobalTheory.LevZeroMem.mem_rowJ_iff_rTup_alt | (intros; apply _root_.GlobalTheory.LevZeroMem.mem_rowJ_iff_rTup_alt <;> assumption)
end
end
end
