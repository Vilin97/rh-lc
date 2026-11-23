module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFreeSeriesKernelServedPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceIdempotentCmEmbeddingCompat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalModuleLocalisingToLattices
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.ExtEmbEquivComp
import Mathlib.RingTheory.Algebraic.Cardinality
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ServedPlaceLevelsClassesComparisonMapsStatement
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Tactic.Linter.Style
public import Formalism.LocalToGlobal.GroupLattices.ClassLocalOfEq

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalModuleLocalisingToLatticesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_global_module_localising_to_lattices : ∀ {D : D7} {H : Formalism.L2.Herm.HermColsCh D} (Gs : Formalism.L2.Herm.SymmetricGroupCompatibility D H) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)) (n : ℕ)
    (L : ∀ q : Fin (D.gat u v hg).P.nV, Submodule ((D.gat u v hg).P.W q) (Fin n → (D.gat u v hg).P.Qq q)),
    (∀ q, G.IsLattice ((D.gat u v hg).P.W q) (L q)) →
    ∃ Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E), ∀ q,
      L q = Submodule.span ((D.gat u v hg).P.W q) {y | ∃ x ∈ Λ, y = fun i => GlobalTheory.Mem.Top.KerOne.iw0 Gs u v hg q (x i)} := by
  first | exact @GlobalTheory.Mem.Top.KerGlob.exists_global_lattice | exact GlobalTheory.Mem.Top.KerGlob.exists_global_lattice | (intros; apply GlobalTheory.Mem.Top.KerGlob.exists_global_lattice <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalCoefficientFieldEmbeddingKernelPlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KerIK

open Cardinal

theorem kf_hom_of_isRec {sc : Scale} {D : D7} {Gt : GatTies D} {c : LatCmp D} {H : Formalism.L2.Herm.Herm0 D}
    {F : ∀ u, Formalism.L2.Forms.Forms0 D u} (h : IsRecG sc D Gt c H F) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)) [Fact (D.what₂.places.resChar v).Prime] :
    Nonempty ((D.gat u v hg).Kf →+* ℂ_[D.what₂.places.resChar v]) := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, eq⟩ := h
  cases eq
  exact ⟨iK u v hg⟩

theorem mk_LL_le (D : D7) : #D.what₂.LL ≤ ℵ₀ := by
  have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ D.what₂.LL
  rwa [Cardinal.mkRat, max_self] at this

theorem exists_iK : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ iK : ((w.D Z).gat u v hg).Kf →+* ℂ_[(w.D Z).what₂.places.resChar v],
        ∀ (x : (w.D Z).what₂.LL) (hx : (w.D Z).what₂.embLL x ∈ algebraicClosure ℚ ℂ),
          iK (t.cmp.embW u v hg x) = E.lam v ⟨(w.D Z).what₂.embLL x, hx⟩ := by
  intro K B f T w _ _ _ Z t Wt nch _ Y _ _ O _ _ E _ u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  obtain ⟨i0⟩ := kf_hom_of_isRec t.isRec u v hg
  have hC : ℵ₀ < #ℂ_[(w.D Z).what₂.places.resChar v] :=
    Cardinal.aleph0_lt_continuum.trans_le (continuum_le_cardinal_of_nontriviallyNormedField _)
  obtain ⟨σ, hσ⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.extEmb_equiv_comp (i0.comp (t.cmp.embW u v hg)) (E.iL v)
    (mk_LL_le (w.D Z)) hC rfl
  refine ⟨σ.toRingHom.comp i0, fun x hx => ?_⟩
  have h1 := hσ x
  have h2 := E.iL_lam v x
  simp only [RingHom.comp_apply] at h1
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [h1, h2, lamV, dite_eq_left hx]

end GlobalTheory.KerIK
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalCoefficientFieldEmbeddingKernelPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_localCoefficientField_embedding_kernelPlace : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ iK : ((w.D Z).gat u v hg).Kf →+* ℂ_[(w.D Z).what₂.places.resChar v],
        ∀ (x : (w.D Z).what₂.LL) (hx : (w.D Z).what₂.embLL x ∈ algebraicClosure ℚ ℂ),
          iK (t.cmp.embW u v hg x) = E.lam v ⟨(w.D Z).what₂.embLL x, hx⟩ := by
  first | exact @GlobalTheory.KerIK.exists_iK | exact GlobalTheory.KerIK.exists_iK | (intros; apply GlobalTheory.KerIK.exists_iK <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEmbeddingAtOrbitPositionEqInduced

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.KerOne

theorem splitPlace_embedding_at_orbitPosition_eq_induced : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (q : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' q)) (x : (w.D Z).host.E),
        ((w.D Z).gat u v hg).P.ι q ((((w.D Z).gat u v hg).P.σ q ^ s.val) (GlobalTheory.Mem.Top.KerOne.iw0 t.full.1.g u v hg q x)) =
          t.cmp.embW u v hg (tauLL (w.D Z) (t.Gt.gat_pos u v hg ⟨q, s⟩) (if s.val % 2 = 1 then (w.D Z).host.conj x else x)) := by
  intro K B f T w _ _ _ Z t _ _ _ _ _ _ _ _ _ _ _ u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  intro q s x
  have h := (t.g.cmp.tie u v hg).pos_emb q s x
  have key : ∀ (X : Formalism.L2.Herm.Herm0 (w.D Z)) (Bm : GL (Fin (w.D Z).R.k) (w.D Z).host.E), X = t.full.1.to0 →
      (Formalism.L2.G.Cmp.locAt X u v hg Bm).iw q x = iw0 t.full.1.g u v hg q x := by
    rintro X Bm rfl; rfl
  rw [key _ _ t.herm_eq] at h
  rw [← h]
  have h3 : Formalism.L2.Forms.sigD (w.D Z) x = (w.D Z).host.conj x := Formalism.BasicNotions.bridge_star_holds (w.D Z).R (w.D Z).host x
  rw [h3]
  show _ = (t.cmp.embW u v hg) (Formalism.L2.G.Cmp.tEL (w.D Z) _ _)
  congr 2
  by_cases hs : s.val % 2 = 1
  · have : ¬ Even s.val := by rw [Nat.not_even_iff_odd, Nat.odd_iff]; exact hs
    simp [hs, this]
  · have : Even s.val := by rw [Nat.even_iff]; omega
    simp [hs, this]

end GlobalTheory.Mem.Top.KerOne
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEmbeddingAtOrbitPositionEqInducedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlace_embedding_at_orbitPosition_eq_induced_alt : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (q : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' q)) (x : (w.D Z).host.E),
        ((w.D Z).gat u v hg).P.ι q ((((w.D Z).gat u v hg).P.σ q ^ s.val) (GlobalTheory.Mem.Top.KerOne.iw0 t.full.1.g u v hg q x)) =
          t.cmp.embW u v hg (tauLL (w.D Z) (t.Gt.gat_pos u v hg ⟨q, s⟩) (if s.val % 2 = 1 then (w.D Z).host.conj x else x)) := by
  first | exact @GlobalTheory.Mem.Top.KerOne.splitPlace_embedding_at_orbitPosition_eq_induced | exact GlobalTheory.Mem.Top.KerOne.splitPlace_embedding_at_orbitPosition_eq_induced | (intros; apply GlobalTheory.Mem.Top.KerOne.splitPlace_embedding_at_orbitPosition_eq_induced <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesServedPlaceEqLocalOrbitPairs

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.KerOne

theorem stepZeroClasses_servedPlace_eq_localOrbitPairs_alt : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ cls0 : ((w.D Z).gat u v hg).comp → ((w.D Z).gat u v hg).P.Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls 0,
        (∀ (a a' : ((w.D Z).gat u v hg).comp) (L L' : ((w.D Z).gat u v hg).P.Tup), ((w.D Z).gat u v hg).P.IsLatTup L →
          ((w.D Z).gat u v hg).P.IsLatTup L' →
          (cls0 a L = cls0 a' L' ↔ a = a' ∧ ∃ γ : (((w.D Z).gat u v hg).lev a).Γ, L' = (((w.D Z).gat u v hg).lev a).smul γ L)) ∧
        ∀ x, ∃ a L, ((w.D Z).gat u v hg).P.IsLatTup L ∧ cls0 a L = x := by
  intro K B f T w _ _ _ Z t Wt nch _ Y _ _ O _ _ E _ u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  have e : ((w.D Z).mem u).C.cls 0 ≃ ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls 0 := TC.eCls0 w.I w.l u ((w.D Z).what₂.muAt v)
  obtain ⟨W, Qq, O', Kf, _, _, _, _, _, _, _, _, _, _, n', ι, σ, j, w0, hS, nV, r, m, lam0, dom, hk, I, ψ, e', hH, heq⟩ :=
    t.g.gat u v hg
  obtain ⟨c⟩ := Formalism.L2.G.TwTie0.class_local_of_eq (w.D Z) t.g.herm.lev0 u e hS nV r m lam0 dom hk I ψ e' hH ((w.D Z).gat u v hg) heq
  exact ⟨c.cls, c.cls_iff, c.cls_surj⟩

end GlobalTheory.Mem.Top.KerOne
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesServedPlaceEqLocalOrbitPairsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepZeroClasses_servedPlace_eq_localOrbitPairs : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ cls0 : ((w.D Z).gat u v hg).comp → ((w.D Z).gat u v hg).P.Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls 0,
        (∀ (a a' : ((w.D Z).gat u v hg).comp) (L L' : ((w.D Z).gat u v hg).P.Tup), ((w.D Z).gat u v hg).P.IsLatTup L →
          ((w.D Z).gat u v hg).P.IsLatTup L' →
          (cls0 a L = cls0 a' L' ↔ a = a' ∧ ∃ γ : (((w.D Z).gat u v hg).lev a).Γ, L' = (((w.D Z).gat u v hg).lev a).smul γ L)) ∧
        ∀ x, ∃ a L, ((w.D Z).gat u v hg).P.IsLatTup L ∧ cls0 a L = x := by
  first | exact @GlobalTheory.Mem.Top.KerOne.stepZeroClasses_servedPlace_eq_localOrbitPairs_alt | exact GlobalTheory.Mem.Top.KerOne.stepZeroClasses_servedPlace_eq_localOrbitPairs_alt | (intros; apply GlobalTheory.Mem.Top.KerOne.stepZeroClasses_servedPlace_eq_localOrbitPairs_alt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsKernelDataAtServedPlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.KerOne

theorem kerData_at_served : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ (Lv : G.Levels (Fl u v hg)) (KD : Formalism.L2.G.Cmp.KerData (w.D Z) t.cmp (w.tw Z) u v hg Lv),
        KD.lam = E.lam v ∧
        ThAtServed (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) E ∧
        Formalism.L2.Herm.SymmetricKernelCompatibleAtPlace t.full.1.base.toHermColsCh t.full.1.g u v hg (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) ∧
        Formalism.L2.Herm.GIwPos u v hg (Formalism.L2.G.Cmp.kerAtP_of t.Gt KD) := by
  intro K B f T w hO hF hP Z t Wt nch hn Y hMu hQp O hStd hUnf E hE Fl hFl hw u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  obtain ⟨iK, hiK⟩ := GlobalTheory.T.exists_localCoefficientField_embedding_kernelPlace w hO hF hP Z t Wt nch hn Y hMu hQp O hStd hUnf E hE u v hg
  have hpos := GlobalTheory.T.splitPlace_embedding_at_orbitPosition_eq_induced_alt w hO hF hP Z t Wt nch hn Y hMu hQp O hStd hUnf E hE u v hg
  obtain ⟨cls0, h0iff, h0surj⟩ := GlobalTheory.T.stepZeroClasses_servedPlace_eq_localOrbitPairs w hO hF hP Z t Wt nch hn Y hMu hQp O hStd hUnf E hE u v hg
  obtain ⟨Lv, clsS, up, hSiff, hSsurj, hInt⟩ := GlobalTheory.T.served_place_levels_classes_comparison_maps w hO hF hP Z t Wt nch hn Y hMu hQp O hStd hUnf E hE Fl hFl hw u v hg
  classical
  let Gs := t.full.1.g
  let iwJ : ∀ j (q : Fin ((Fl u v hg).Pj j).nV), (w.D Z).host.E →+* ((Fl u v hg).Pj j).Qq q := fun j =>
    match j with
    | 0 => fun q => iw0 Gs u v hg q
    | _ + 1 => fun q => iw0 Gs u v hg q
  let globJ : ∀ j, Lv.comp j → ((Fl u v hg).Pj j).Tup →
      Submodule (𝓞 (w.D Z).host.E) (Fin (((Fl u v hg).Pj j).m + 1) → (w.D Z).host.E) := fun j =>
    match j with
    | 0 => fun _ L => if hL : ((Fl u v hg).Pj 0).IsLatTup L then
        Classical.choose (GlobalTheory.T.exists_global_module_localising_to_lattices Gs u v hg (((Fl u v hg).Pj 0).m + 1) L hL) else ⊥
    | j + 1 => fun _ L => if hL : ((Fl u v hg).Pj (j + 1)).IsLatTup L then
        Classical.choose (GlobalTheory.T.exists_global_module_localising_to_lattices Gs u v hg (((Fl u v hg).Pj (j + 1)).m + 1) L hL) else ⊥
  let clsJ : ∀ j, Lv.comp j → ((Fl u v hg).Pj j).Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls j := fun j =>
    match j with
    | 0 => fun a L => cls0 a L
    | j + 1 => fun a L => clsS j a L
  let KD0 : Formalism.L2.G.Cmp.KerData (w.D Z) t.cmp (w.tw Z) u v hg Lv :=
    { fl_t := (hFl u v hg).1
      fl_m := (hFl u v hg).2
      lam := E.lam v
      iK := iK
      iLL_lam := hiK
      iw := iwJ
      glob := globJ
      glob_loc := by
        intro j _ a L hL q
        cases j with
        | zero =>
          have h := Classical.choose_spec (GlobalTheory.T.exists_global_module_localising_to_lattices Gs u v hg (((Fl u v hg).Pj 0).m + 1) L hL) q
          simp only [globJ, iwJ, dif_pos hL]
          exact h
        | succ j =>
          have h := Classical.choose_spec (GlobalTheory.T.exists_global_module_localising_to_lattices Gs u v hg (((Fl u v hg).Pj (j + 1)).m + 1) L hL) q
          simp only [globJ, iwJ, dif_pos hL]
          exact h
      cls := clsJ
      cls_iff := by
        intro j hj a a' L L' hL hL'
        cases j with
        | zero => exact h0iff a a' L L' hL hL'
        | succ j => exact hSiff j hj a a' L L' hL hL'
      cls_surj := by
        intro j hj x
        cases j with
        | zero => exact h0surj x
        | succ j => exact hSsurj j hj x
      Th := fun _ _ _ => 0
      up := up
      intS := hInt }
  obtain ⟨Th, hTh⟩ := GlobalTheory.T.exists_freeSeries_kernel_servedPlace t.Gt KD0 E rfl
  refine ⟨Lv, { KD0 with Th := Th }, rfl, hTh, ?_, ?_⟩
  · intro q x
    exact splitPlaceIdempotent_cmEmbedding_compat Gs u v hg q x
  · intro q s x
    exact hpos q s x

end GlobalTheory.Mem.Top.KerOne
end
end
