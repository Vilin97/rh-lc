module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AutomorphicArithmetic.CharacterBoxes.Supply
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddLargeBaseCoreSlot
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RecExGOfRecAtG
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowLower
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DsPPosAndLower
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LayeredAutomorphicDataExistsOfTwoPassesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesEqMassesOfUnfold
public import Development.AutomorphicArithmetic.CharacterBoxes.ObjCTrue

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsClassSelOfRowL

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem isSel_of_sAnd {Bd : BdT} {Q R : V4.Slot} {Lk : LkT Bd} {E : Par → BdP Bd} {𝒜 : FamClass} {σ : RawSel Bd 𝒜}
    (s : IsSel (sAnd Q R) Lk E 𝒜 σ) : IsSel Q Lk E 𝒜 σ := by
  intro eps Fm hc
  obtain ⟨κ, h1, h2, h3⟩ := s Fm hc
  refine ⟨κ, h1, h2, fun x hx i => ⟨?_, (h3 x hx i).2⟩⟩
  obtain ⟨K, β, b, a0, a1, a2, a3⟩ := (h3 x hx i).1
  exact ⟨K, β, b, a0, a1.1, a2, a3⟩

end GlobalTheory.Fc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddLargeBaseCoreSlotStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.secondG_sAnd_of_largeBase : ∀ (KP : GroupRetwisting.BaseP) (Q Q' R : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.LargeBaseConditionG KP Q R → GroupRetwisting.SecondG KP Q Q' → GroupRetwisting.SecondG KP Q (sAnd Q' R) := by
  first | exact @GlobalTheory.Mem.Top.GroupRetwisting.SecondG.sAnd_of_largeBase | exact GlobalTheory.Mem.Top.GroupRetwisting.SecondG.sAnd_of_largeBase | (intros; apply GlobalTheory.Mem.Top.GroupRetwisting.SecondG.sAnd_of_largeBase <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwGoodOneSetDiv

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.EX.DQ NumberField IsDedekindDomain

namespace GlobalTheory.EX.DQ



theorem twGoodOne_setDiv (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
    (N0 : D.ntw.Tw → ℕ) (S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b))
    (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k : ℕ) (p : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ)
    (H : TwGoodOne D ⟨twEOf O.xd, N0, S⟩ i b Q k p) :
    TwGoodOne (setDiv D N h) ⟨twEOf (O.tr N h).xd, N0, S⟩ i b Q k p := by
  unfold TwGoodOne at H ⊢
  have e1 : AvRec (setDiv D N h) = AvRec D := rfl
  have e2 : twEps (setDiv D N h) i = twEps D i := rfl
  rw [e1, e2]
  unfold IntegralHeckeForms.GoodTw at H ⊢
  obtain ⟨h1, ⟨eB, h2, h3, h4⟩, h5, h6, h7, h8⟩ := H
  exact ⟨h1, ⟨eB, h2, h3, h4⟩, fun j hj c => ⟨(h5 j hj c).1, (h5 j hj c).2⟩, h6, h7, h8⟩

theorem qd_setDiv : ∀ (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ),
    QD D O → QD (setDiv D N h) (O.tr N h) := by
  rintro D O N h ⟨h1, ⟨hc, N0, S, hS⟩, h3⟩
  refine ⟨h1, ⟨hc, N0, S, fun w hw => ⟨(hS w hw).1, fun a ha => ?_⟩⟩, h3⟩
  exact twGoodOne_setDiv D O N h N0 S _ _ _ _ _ ((hS w hw).2 a ha)

end GlobalTheory.EX.DQ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayeredDataOfGoodScaleContexts

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem recExP_of_recAtG : StandardLattice.SiegelMassRatioCM → ∀ (Q' : V4.Slot) (QO : Par → ∀ D : D7, Obj D → Prop), RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) → (EvP fun κ K => ∀ β : BPt K, β.Is Q' → QO κ β.D β.O) → RecExP (fun κ => DQ.withQD (fun D O => κ.Pos → QO κ D O)) := by
  intro hconds Q' QO h hq
  obtain ⟨ε0, hε0, h⟩ := h
  obtain ⟨ε1, hε1, hq⟩ := hq
  refine ⟨min ε0 ε1, lt_min hε0 hε1, fun eps C8 C5 c6 Cb he he0 he52 hC8 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb he (he0.trans (min_le_left _ _)) he52 hC8
  obtain ⟨K1, hq⟩ := hq eps C8 C5 c6 Cb he (he0.trans (min_le_right _ _)) he52 hC8
  refine ⟨K0.sup K1, fun C hstd hC hL => ?_⟩
  obtain ⟨c1, h⟩ := h C hstd hC (large_of_sup hL).1
  obtain ⟨c1', hq⟩ := hq C hstd hC (large_of_sup hL).2
  refine ⟨max (max c1 c1') 0, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hcD)
  obtain ⟨c2q, hq⟩ := hq cD (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hcD)
  obtain ⟨c2', hlow⟩ := GlobalTheory.EX.WinLow.window_lower hconds eps C he he52 hstd cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max (max c2 c2q) c2', fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hch)
  have hq := hq ch (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hch)
  obtain ⟨x1, hlow⟩ := hlow ch (le_trans (le_max_right _ _) hch)
  obtain ⟨x2, hint⟩ := exists_du_nat eps he he52
  have hq' : ∃ x3 : ℝ, Par.Pos ⟨eps, C, cD, ch, C5, c6, Cb⟩ → ∀ K : Ctx, Par.Of ⟨eps, C, cD, ch, C5, c6, Cb⟩ K → x3 ≤ K.s.x →
      ∀ β : BPt K, β.Is Q' → QO ⟨eps, C, cD, ch, C5, c6, Cb⟩ β.D β.O := by
    by_cases hp : Par.Pos ⟨eps, C, cD, ch, C5, c6, Cb⟩
    · obtain ⟨x3, h3⟩ := hq hp
      exact ⟨x3, fun _ => h3⟩
    · exact ⟨0, fun hp' => absurd hp' hp⟩
  obtain ⟨x3, hq'⟩ := hq'
  refine ⟨1, max (max x0 x3) (max x1 x2), one_pos, fun s P a b c hs hx d3 => ?_⟩
  have hok := d3.ok
  have hx0 : x0 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx3 : x3 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : x1 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : x2 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨du, hpos, hdu⟩ := hint s C cD ch P _ a b c hs hx2 hok
  obtain ⟨hD, hDle⟩ := GlobalTheory.Mem.Top.DsLow.DsP_pos_and_lower P
  refine ⟨du, DsP P, hpos, hD, fun u => ?_, fun Lv h1 h2 h3 => ?_⟩
  · rw [one_mul]
    exact hlow s P _ a b c du (DsP P) hs hx1 hok hdu hDle u
  · let K : Ctx := ⟨s, C, cD, ch, P, _, a, b, c, hstd, hok, Lv, fun u => by rw [h1]; exact hdu u, h2, h3⟩
    obtain ⟨D, Y, g1, g2, g3, g4, ⟨X, f, T, co, hQ, he⟩, u1, u2, u3⟩ := h K rfl rfl rfl hs hx0 d3
    refine ⟨D, Y, g1, g2, g3, g4, fun p p1 p2 p3 p4 => ⟨fun hp => ?_, ?_⟩⟩
    · obtain ⟨rfl, he⟩ := Sigma.mk.inj he
      exact hq' hp K ⟨rfl, rfl, rfl, hs, d3⟩ hx3
        ⟨X, f, T, co, Y, eq_of_heq he, p, p1, p2, p3, p4, ⟨C5, c6, Cb, d3⟩, g2, g3, u1, u2⟩ hQ
    · exact DQ.qd_setDiv D (Y.obj p) (nPrime p.L) p.ht ⟨u1, u2, u3⟩

end GlobalTheory.Fc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayeredDataOfGoodScaleContextsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.existsLayeredData_of_goodScaleContexts : StandardLattice.SiegelMassRatioCM → ∀ (Q' : V4.Slot) (QO : Par → ∀ D : D7, Obj D → Prop), RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) → (EvP fun κ K => ∀ β : BPt K, β.Is Q' → QO κ β.D β.O) → RecExP (fun κ => DQ.withQD (fun D O => κ.Pos → QO κ D O)) := by
  first | exact @GlobalTheory.Fc.recExP_of_recAtG | exact GlobalTheory.Fc.recExP_of_recAtG | (intros; apply GlobalTheory.Fc.recExP_of_recAtG <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberTopFinalContextParameters

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem memberTop_final_contextParameters :
    StandardLattice.SiegelMassRatioCM → (∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) →
    ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot) (QO : Par → ∀ D : D7, Obj D → Prop),
      GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' →
      (EvP fun κ K => ∀ β : BPt K, β.Is Q' → QO κ β.D β.O) →
      RecExP (fun κ => DQ.withQD (fun D O => κ.Pos → QO κ D O)) :=
  fun hAll hU KP Q Q' QO hB hF hE hS hEv =>
    GlobalTheory.T.existsLayeredData_of_goodScaleContexts hAll Q' QO
      (GlobalTheory.T.layeredAutomorphicData_exists_of_twoPasses (GlobalTheory.Mem.VolMass.volumes_eq_masses_of_unfold hU) KP Q Q' hB hF hE hS)
      hEv

end GlobalTheory.Fc
end
end

-- Source module: Development.AutomorphicArithmetic.CharacterBoxes.ClassSel

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace UpperTheory.Top

theorem classSel : StandardLattice.SiegelMassRatioCM → (∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) → ∀ (KP : ∀ B : Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Bd : BdT) (Lk : LkT Bd) (H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop) (cT : ℝ → ℝ → ℝ), (DC.MinkDiv → GroupRetwisting.BaseCond KP ∧ GroupRetwisting.FirstG KP Q ∧ GroupRetwisting.ExportF KP Q ∧ GroupRetwisting.SecondG KP Q Q') → ExBL KP Q Q' Lk → RowL KP Q Q' Lk H → ∃ (𝒜 : FamClass) (σ : RawSel Bd 𝒜), (DC.MinkDiv → ExD 𝒜 cT) ∧ (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → DQ.Duty7 Fm ∧ DQ.MtStableF Fm) ∧ IsSel Q' Lk (fun _ _ _ _ _ => True) 𝒜 σ ∧ H 𝒜 σ := by
  intro h1 h2 KP Q Q' Bd Lk H cT hc hx hr
  obtain ⟨R, r, hx', hr'⟩ := RowL.elim hx hr
  obtain ⟨E, hE, hH⟩ := Row.elim hx' hr'
  have hs : IsSel (sAnd Q' R) Lk (fun _ _ _ _ _ => True) (cls (sAnd Q' R) Lk E) (pick (sAnd Q' R) Lk E) :=
    IsSel.mono (fun _ _ _ _ _ _ => trivial) (pick_isSel (sAnd Q' R) Lk E)
  refine ⟨cls (sAnd Q' R) Lk E, pick (sAnd Q' R) Lk E, ?_, fun _ _ h => sevenDuties_of_class h,
    @isSel_of_sAnd Bd Q' R Lk _ (cls (sAnd Q' R) Lk E) (pick (sAnd Q' R) Lk E) hs, hH⟩
  refine recS (QOf (sAnd Q' R) Lk E) cT fun hm => ?_
  obtain ⟨a, b, c, d⟩ := hc hm
  have d' := GlobalTheory.T.secondG_sAnd_of_largeBase KP Q Q' R a (evG_of_ev r) d
  have h := memberTop_final_contextParameters h1 h2 KP Q (sAnd Q' R) (QOf (sAnd Q' R) Lk E) a b c d' hE
  have e : ∀ κ : Par, (fun D O => κ.Pos → QOf (sAnd Q' R) Lk E κ D O) = QOf (sAnd Q' R) Lk E κ :=
    fun κ => funext fun _ => funext fun _ => propext ⟨fun h' h0 => h' h0 h0, fun h' _ => h'⟩
  simpa only [e] using h

end UpperTheory.Top
end
end
