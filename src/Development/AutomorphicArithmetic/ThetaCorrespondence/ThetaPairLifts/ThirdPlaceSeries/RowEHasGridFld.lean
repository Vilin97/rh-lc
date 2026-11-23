module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingsFormsExistList
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithAtProperty
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartSel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvPSizeRowsDlog
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThreePrimesOneModLeRpow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DsigEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationComapLtOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridFieldHasLattices

section

@[expose] public section

open Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.ChiGrid

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow

section Transfer

variable {D : Formalism.BasicNotions.D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

theorem fieldHas_of_same {G G₀ : GridData Lc sc} {K : Type} [Field K] {e : K →+* ℂ} (hv : G.pl.v0 = G₀.pl.v0)
    (hch : ∀ a : Fin D.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) (h : FieldHas G₀ e) : FieldHas G e := by
  have hS : G.pl.S0 = G₀.pl.S0 := by
    delta Places.S0
    rw [hv]
  have hd : ∀ v, G.pl.depth sc v = G₀.pl.depth sc v := fun v => by
    delta Places.depth
    rw [hv]
  refine ⟨fun i h1 h2 => ?_, fun v hv' => ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
    have := hch ⟨a, by omega⟩
    simp only at this
    rw [this]
    exact h.values _ h1 h2
  · rw [hd]
    exact h.roots v (hS ▸ hv')

theorem lamOf_of_same {G G₀ : GridData Lc sc} (hw : G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0)
    (hch : ∀ a : Fin D.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) : lamOf G = lamOf G₀ := by
  delta lamOf
  rw [hw]
  congr 1
  funext a
  exact hch a

end Transfer

variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
  {Kc : Formalism.MainNotions.G.Consts} {Y : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem gridFit_of_parts {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} (hs : TwistedPlaceChoiceLiesOverPair D ex.nch)
    (hc : ∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (ex.nch.twI w) (ex.nch.Q w))
    (hp : ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (ex.nch.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (ex.nch.twI w) (ex.nch.Q w) (ex.nch.k' w) (ex.nch.psi' w ^ a) (twEps D (ex.nch.twI w)))
    (h1 : Formalism.L2.Host.ValLL0 D p.R.C) (h2 : FieldHas G (Formalism.L2.Host.embLL0 D))
    (h3 : Formalism.L2.Host.PsiChoiceCompatible D p.R.C ex.nch p.Tp) (h4 : GlobalTheory.LamTie.IsLamTieFull D.ntw (lamOf G)) : GridFit p G :=
  ⟨h1, h2, hs, hc, hp, h3, h4⟩

end GlobalTheory.Mem.LiteralAutomorphy.GridRow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistsAtLinked

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy.TwAtLink

open GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems (Twisted SamePair SameBelow LiesUnder TwistedPlaceSettings)

theorem cond_powers {D : D7} {C : NChoice D} {I : TwIn D} (h : DQ.GoodAllAt D C I) :
    (∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (C.twI w) (C.Q w)) ∧
    ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (C.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (C.twI w) (C.Q w) (C.k' w) (C.psi' w ^ a) (twEps D (C.twI w)) := by
  classical
  refine ⟨fun w hw => ?_, I.N0, fun w hw a ha => ?_⟩
  · have h1 := ((h w hw).2 1 (by simp)).1
    exact ⟨fun P hP => (h1.1 P hP).1, (Finset.disjoint_union_right.1 h1.2.1).1,
      GlobalTheory.AntiRam.ramExactly_conj D _ _ _ h1.2.2.2.2.1 h1.2.2.2.2.2.2.1⟩
  · have e : ∃ b : ℤ, b.natAbs = a.natAbs ∧ BlochKatoReduction.Gen.psiAt (C.sd w) (C.psi' w ^ b) = C.psi' w ^ a := by
      cases C.sd w
      · exact ⟨-a, Int.natAbs_neg a, by simp [BlochKatoReduction.Gen.psiAt]⟩
      · exact ⟨a, rfl, by simp [BlochKatoReduction.Gen.psiAt]⟩
    obtain ⟨b, hb, e⟩ := e
    have hc : Nat.Coprime b.natAbs (D.ntw.l (C.twI w)) := by
      rw [hb]
      simpa using Int.isCoprime_iff_nat_coprime.1 ha
    exact e ▸ ((h w hw).2 b hc).2.2.2.2.1

theorem twI_eq {D : D7} {C : NChoice D} {xd : ThData D} (h : GoodO D C xd) {w w' : D.what₂.places.Pl}
    (hw : Twisted D w) (hw' : Twisted D w') (e : C.Q w = C.Q w') (hne : C.Q w ≠ ∅) : C.twI w = C.twI w' := by
  by_contra hn
  have := h.sep w w' hw hw' hn
  rw [← e] at this
  exact hne (disjoint_self.1 this)

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}

end GlobalTheory.Mem.LiteralAutomorphy.TwAtLink

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistsAtLinked

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Mem.LiteralAutomorphy.TwAtLink
open GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems (Twisted SamePair SameBelow LiesUnder TwistedPlaceSettings)
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
theorem Q_eq_alt (q : WPt p.s K) {w w' : (q.w.D q.Z).what₂.places.Pl} (hw : Twisted (q.w.D q.Z) w)
    (hw' : Twisted (q.w.D q.Z) w') (h : SamePair (q.w.D q.Z) w w') :
    q.O.ex.nch.Q w = q.O.ex.nch.Q w' ∧ q.O.ex.nch.k' w = q.O.ex.nch.k' w' := by
  have key : ∀ v v', Twisted (q.w.D q.Z) v → Twisted (q.w.D q.Z) v' → SameBelow (q.w.D q.Z) v v' →
      q.O.ex.nch.Q v = q.O.ex.nch.Q v' ∧ q.O.ex.nch.k' v = q.O.ex.nch.k' v' := by
    intro v v' hv hv' hs
    have m : ∀ u, Twisted (q.w.D q.Z) u → u ∈ q.x.Wt := fun u hu => by
      by_contra hn
      exact hu (q.x.what₂.mu.off u hn)
    have a := q.x.n.Q v (m v hv)
    have a' := q.x.n.Q v' (m v' hv')
    have c := q.x.coh.same v v' fun x hx => hs ⟨x, hx⟩
    exact ⟨a.1.trans (c.1.trans a'.1.symm), a.2.trans (c.2.1.trans a'.2.symm)⟩
  rcases h with h | h
  · exact key w w' hw hw' h
  · have k := key _ w' ((GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj w).2 hw) hw' h
    have c := q.core_data_of_point.a.all.choice.conj w hw
    exact ⟨(congrArg (fun t : TwPack _ => t.2.1) c).symm.trans k.1, (congrArg (fun t : TwPack _ => t.2.2.1) c).symm.trans k.2⟩
theorem twists_at_linked_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Q : V4.Slot), RowE Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) fun _ D O _ _ => (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → D.ntw.l (O.ex.nch.twI w) = D.what₂.places.resChar w ∧ (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) w ∨ GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) (D.what₂.places.conj w))) ∧ (∀ w w', GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w' → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.SamePair D w w' → O.ex.nch.Q w = O.ex.nch.Q w' ∧ O.ex.nch.k' w = O.ex.nch.k' w' ∧ (O.ex.nch.Q w ≠ ∅ → O.ex.nch.twI w = O.ex.nch.twI w')) ∧ (∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (O.ex.nch.twI w) (O.ex.nch.Q w)) ∧ ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (O.ex.nch.twI w) : ℤ) → BlochKatoReduction.Gen.partC N0 (O.ex.nch.twI w) (O.ex.nch.Q w) (O.ex.nch.k' w) (O.ex.nch.psi' w ^ a) (twEps D (O.ex.nch.twI w)) := by
  intro hL p Q
  refine RowE.of_all fun κ K β c b _ _ hl => ?_
  obtain ⟨q, b', -, he⟩ := hl
  have h1 := congrArg (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c =>
    (fun (D : D7) (O : Obj D) => (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → D.ntw.l (O.ex.nch.twI w) = D.what₂.places.resChar w ∧ (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) w ∨ GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (O.ex.nch.twI w) (D.what₂.places.conj w))) ∧ (∀ w w', GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w' → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.SamePair D w w' → O.ex.nch.Q w = O.ex.nch.Q w' ∧ O.ex.nch.k' w = O.ex.nch.k' w' ∧ (O.ex.nch.Q w ≠ ∅ → O.ex.nch.twI w = O.ex.nch.twI w')) ∧ (∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (O.ex.nch.twI w) (O.ex.nch.Q w)) ∧ ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (O.ex.nch.twI w) : ℤ) → BlochKatoReduction.Gen.partC N0 (O.ex.nch.twI w) (O.ex.nch.Q w) (O.ex.nch.k' w) (O.ex.nch.psi' w ^ a) (twEps D (O.ex.nch.twI w))) s.1 s.2.1) he
  refine cast h1.symm ?_
  obtain ⟨I, -, hI, -⟩ := q.x.good.tw
  exact ⟨fun w hw => ⟨q.O.ex.nch.twI_l w, GlobalTheory.TwistGoodCompare.atPlace_of_tie q.B.coeffGaloisSubfield_isGalois q.O.ex.nch_tie w hw⟩,
    fun w w' hw hw' h => ⟨(_root_.GlobalTheory.Mem.LiteralAutomorphy.TwAtLink.Q_eq_alt q hw hw' h).1, (_root_.GlobalTheory.Mem.LiteralAutomorphy.TwAtLink.Q_eq_alt q hw hw' h).2, twI_eq q.x.good hw hw' (_root_.GlobalTheory.Mem.LiteralAutomorphy.TwAtLink.Q_eq_alt q hw hw' h).1⟩, cond_powers hI⟩
end GlobalTheory.Mem.LiteralAutomorphy.TwAtLink
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEHasGridFld

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.ChiGrid
namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow
section Transfer
variable {D : Formalism.BasicNotions.D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
end Transfer
variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
  {Kc : Formalism.MainNotions.G.Consts} {Y : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
theorem hasGrid_of_full_field_lamTie (p : PtAt ex Csz) (CF : ℝ) (hp : p.CompatibilityConditions)
    (hs : TwistedPlaceChoiceLiesOverPair D ex.nch)
    (hc : ∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (ex.nch.twI w) (ex.nch.Q w))
    (hpw : ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (ex.nch.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (ex.nch.twI w) (ex.nch.Q w) (ex.nch.k' w) (ex.nch.psi' w ^ a) (twEps D (ex.nch.twI w)))
    (G : Grid p CF) (h2 : FieldHas G (Formalism.L2.Host.embLL0 D)) (h4 : GlobalTheory.LamTie.IsLamTieFull D.ntw (lamOf G))
    (hF : Full p.R.toRealDat G) : HasGrid (@Fld) p CF := by
  have hfit := gridFit_of_parts hs hc hpw hp.real.valLL0 h2 hp.real.psiChoice h4
  obtain ⟨W, M, ρ, ξ, cv, rm, S, rp, n, e, c, hIs, hOK, hSq⟩ := hF
  exact ⟨G, W, hIs.weil, hfit, n, ⟨M, ρ, ξ, cv, rm, S, rp, e, c⟩, ⟨hIs, hp.eSer, hOK, hSq⟩⟩
end GlobalTheory.Mem.LiteralAutomorphy.GridRow
namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow
theorem rowE_hasGrid_fld_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (CF : ℝ) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL CF K B f T w Z Wt p0 t nch n xd c)) → RowE (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ)) fun _ D O c b => ∀ t : b.Comparison₂, (b.part t).pt.CompatibilityConditions → GlobalTheory.BigTop.Fun.HasGrid @GlobalTheory.BigTop.Fun.Fld (b.part t).pt CF := by
  intro hL CF N S Γ hN
  refine ((_root_.GlobalTheory.Mem.LiteralAutomorphy.TwAtLink.twists_at_linked_alt hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ).s)).and
    ((_root_.GlobalTheory.Mem.LiteralAutomorphy.GridRow.rowE_pinned_grid_alt hL CF N S Γ hN).and (_root_.GlobalTheory.Mem.LiteralAutomorphy.GridRow.rowE_full_grid_alt hL CF N S Γ))).imp fun κ K β c b _ _ _ H t ht => ?_
  obtain ⟨hw1, hw2, hcond, hpow⟩ := H.1
  obtain ⟨G₀, hF₀, hT₀⟩ := H.2.1 t ht
  obtain ⟨G, hv, hw, hch, hFull⟩ := H.2.2 t ht G₀
  exact _root_.GlobalTheory.Mem.LiteralAutomorphy.GridRow.hasGrid_of_full_field_lamTie _ CF ht ⟨hw1, fun w w' a b c => (hw2 w w' a b c).2.2⟩ hcond hpow G (fieldHas_of_same hv hch hF₀)
    (lamOf_of_same hw hch ▸ hT₀) hFull
end GlobalTheory.Mem.LiteralAutomorphy.GridRow
end
end
end
