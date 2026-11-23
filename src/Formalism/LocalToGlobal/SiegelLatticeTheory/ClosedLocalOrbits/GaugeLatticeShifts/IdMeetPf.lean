module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DistinctWordsDistinctParameters
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetKey
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetKeyPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiTrivOut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOpInhab
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolColPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolEqPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolFundPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolGcPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SigmaFiniteOfFcG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NinfConjIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HaarOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdBlocks
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolIndexPf

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetOnePf

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

section Gen

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem nlam_iff_of_rel {Λ : Submodule (𝓞 D.host.E) (VS D).V} {p q : GCar X u u F0 F0 Λ Λ}
    (h : GRel X u u F0 F0 Λ Λ p q) : p.1.2 ∈ NLam Λ (lf D F0) ↔ q.1.2 ∈ NLam Λ (lf D F0) := by
  obtain ⟨n, hn, n', hn', hq⟩ := h
  let H := NLamSub Λ (lf D F0)
  rw [hq]
  constructor
  · intro hp
    exact H.mul_mem (H.mul_mem hn hp) hn'
  · intro hq'
    have e : p.1.2 = n⁻¹ * (n * p.1.2 * n') * n'⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hn) hq') (H.inv_mem hn')

theorem nlam_out_iff {Λ : Submodule (𝓞 D.host.E) (VS D).V} (p : GCar X u u F0 F0 Λ Λ) :
    (Quot.out (Quot.mk (GRel X u u F0 F0 Λ Λ) p)).1.2 ∈ NLam Λ (lf D F0) ↔ p.1.2 ∈ NLam Λ (lf D F0) := by
  have key : ∀ a b : GCar X u u F0 F0 Λ Λ, Relation.EqvGen (GRel X u u F0 F0 Λ Λ) a b →
      (a.1.2 ∈ NLam Λ (lf D F0) ↔ b.1.2 ∈ NLam Λ (lf D F0)) := by
    intro a b hab
    induction hab with
    | rel a b h => exact nlam_iff_of_rel h
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  exact key _ _ (Quot.eqvGen_exact (Quot.out_eq (Quot.mk (GRel X u u F0 F0 Λ Λ) p)))

theorem isId_of_lin {t : GTerm X u u F0 F0 what₂ what₂} (h : t.lin ∈ NLam t.lam (lf D F0)) : t.isId := by
  unfold GTerm.isId Formalism.L2.SG.FourParts.termIsId Formalism.L2.SG.FourParts.IsIdT
  refine ⟨t.frame, ⟨t.rep.2.2.2.2, rfl⟩, ?_⟩
  unfold Formalism.L2.SG.FourParts.IsIdF
  have hi : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hf : mapLF t.lin (lf D F0) = _ := dif_pos hi
  rw [show t.frame = mapLF t.lin (lf D F0) from rfl, hf]
  refine ⟨t.lin, h, fun a => rfl, ?_⟩
  have hz : (mapFlag t.lin hi (lf D F0).fl).z = t.lin (lf D F0).fl.z := rfl
  show t.lin (lf D F0).fl.z - (mapFlag t.lin hi (lf D F0).fl).z ∈ _
  rw [hz, sub_self]
  exact zero_mem _

end Gen

theorem idMeetOneC_of (hK : IdMeetKeyC) : IdMeetOneC := by
  intro D X Y u hneat _
  refine ⟨fun ρ ρ' t hid hm => (hK D X Y u hneat ρ ρ' t hid hm).1, ?_, ?_⟩
  · intro ρ t t' hid hid' hm hm'
    have h1 := (hK D X Y u hneat ρ ρ t hid hm).2
    have h2 := (hK D X Y u hneat ρ ρ t' hid' hm').2
    obtain ⟨hl, hl', -⟩ := hm
    obtain ⟨hr, hr', -⟩ := hm'
    obtain ⟨lam, mem, lam', mem', cls⟩ := t
    obtain ⟨lam₂, mem₂, lam₂', mem₂', cls₂⟩ := t'
    simp only at hl hl' hr hr'
    subst hl hl' hr hr'
    have h1' : (Quot.out cls).1.2 ∈ Formalism.L2.SG.Pf.NLamSub ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) := h1
    have h2' : (Quot.out cls₂).1.2 ∈ Formalism.L2.SG.Pf.NLamSub ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) := h2
    have hrel : GRel X u u (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) (Quot.out cls) (Quot.out cls₂) :=
      ⟨(Quot.out cls₂).1.2 * ((Quot.out cls).1.2)⁻¹,
        Subgroup.mul_mem _ h2' (Subgroup.inv_mem _ h1'), 1, Formalism.L2.SG.Pf.nlam_one _ _, by group⟩
    have hs := Quot.sound hrel
    have hc : cls = cls₂ := (Quot.out_eq cls).symm.trans (hs.trans (Quot.out_eq cls₂))
    subst hc
    rfl
  · intro ρ
    have hΛ := (Y.cs u).lam_mem ρ
    let t : GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) :=
      idGTerm X ((Y.cs u).lamOf ρ) hΛ ((Y.rowsOK u).1 _ hΛ)
    have hlin : t.lin ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) :=
      (nlam_out_iff _).2 (Formalism.L2.SG.Pf.nlam_one _ _)
    refine ⟨t, isId_of_lin hlin, rfl, rfl, ?_⟩
    exact (Formalism.L2.SG.Pf.nilradical_conj_level' D X Y u ρ t.pt t.lin hlin t.rep.2.1).1

end Formalism.L2.SG.Pf.IdMeet
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetPhasePf

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full

theorem idMeetPhaseC_of (hK : IdMeetKeyC) : IdMeetPhaseC := by
  intro D X Y u hneat _ ρ t hid hmeet
  obtain ⟨-, hlin⟩ := hK D X Y u hneat ρ ρ t hid hmeet
  have hR : RatLink X t.pt t.lin := t.rep.2.1
  have hN : t.pt.1 ∈ X.NinfU u := Formalism.L2.SG.Pf.nLamNinf_holds D X u _ t.pt t.lin hR hlin
  have hNf : t.pt.2 ∈ X.NfinU u := Formalism.L2.SG.Pf.nLamNfin_holds D X u _ t.pt t.lin hR hlin
  obtain ⟨h1, hmul, hinv⟩ := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  obtain ⟨-, hchi, -⟩ := Formalism.L2.SG.Pf.nilradical_conj_level' D X Y u ρ t.pt t.lin hlin hR
  have hprod := Formalism.L2.SG.Pf.psiProd_all D X u t.pt (ratLink_mem X hR) hN hNf
  refine ⟨hinv _ hN, ?_⟩
  have hψ1 : X.psiInfU u 1 = 1 := by
    have h11 := (hmul 1 h1 1 h1).2
    rw [mul_one] at h11
    have hn := Formalism.L2.SG.RealObj.InfCut.norm_psiInfU X u 1
    have h0 : X.psiInfU u 1 ≠ 0 := by
      intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
    exact mul_left_cancel₀ h0 (h11.symm.trans (mul_one _).symm)
  have hinvψ : X.psiInfU u t.pt.1⁻¹ * X.psiInfU u t.pt.1 = 1 := by
    rw [← (hmul _ (hinv _ hN) _ hN).2, inv_mul_cancel, hψ1]
  have hconj : starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) = X.psiInfU u t.pt.1 := by
    have hn := Formalism.L2.SG.RealObj.InfCut.norm_psiInfU X u t.pt.1⁻¹
    have hz : starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) = (X.psiInfU u t.pt.1⁻¹)⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]; simp
    rw [hz, inv_eq_of_mul_eq_one_right hinvψ]
  show X.chi2 ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)) *
    starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) = 1
  rw [hchi, hconj, mul_comm]
  exact hprod

end Formalism.L2.SG.Pf.IdMeet
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolHinfPf

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full

theorem hinfConjC_holds : HinfConjC := by
  intro D X u h hh Ω hΩ
  obtain ⟨h1, hmul, hinvN⟩ := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  let N : Subgroup X.B.I.Ginf :=
    Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.subOf (X.NinfU u) h1 (fun x hx y hy => (hmul x hx y hy).1) hinvN
  have hNc : IsClosed (N : Set X.B.I.Ginf) := Formalism.L2.SG.Pf.Vanish2.ninf_closed X.B.I X.eR (X.zR u)
  have hH : IsHaarOnSet X.B.I (N : Set X.B.I.Ginf) (X.muN u) := X.muN_haar u
  have hHa := Formalism.L2.SG.Pf.haarOnSet_isHaar_inst X.B.I N hNc (X.muN u) hH
  obtain ⟨_, h0, hc, hl⟩ := hH
  have hfin : IsFiniteMeasureOnCompacts (X.muN u) := ⟨hHa.2.1⟩
  have hconj : ∀ g ∈ Hinf X u, ∀ n ∈ X.NinfU u, g * n * g⁻¹ ∈ X.NinfU u := fun g hg n hn => by
    have hi : g⁻¹ ∈ Hinf X u := (Hinf X u).inv_mem hg
    have hfix : ∀ v, ∀ x ∈ fixSet X u, (uMat (g⁻¹ v)).mulVec (rv X.B.I v x) = rv X.B.I v x := hi
    have := Formalism.L2.SG.CovariantRepresentation.ninf_conj X u g⁻¹ (fun v a => hfix v _ (Or.inl (Or.inl ⟨a, rfl⟩)))
      (fun v => hfix v _ (Or.inr rfl)) hn
    simpa using this
  have hcont : ∀ g : X.B.I.Ginf, Continuous fun s : X.B.I.Ginf => g * s * g⁻¹ := fun g =>
    (continuous_const.mul continuous_id).mul continuous_const

  obtain ⟨K0, hK0c, hK0n⟩ := exists_compact_mem_nhds (1 : X.B.I.Ginf)
  have hK0pos : 0 < X.muN u K0 := by
    have hpos := hHa.2.2 (interior K0) isOpen_interior ⟨1, mem_interior_iff_mem_nhds.2 hK0n, h1⟩
    exact lt_of_lt_of_le hpos (measure_mono interior_subset)
  let K : Set X.B.I.Ginf :=
    (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2 * p.1⁻¹) '' ((Hinf X u : Set X.B.I.Ginf) ×ˢ K0)
  have hKc : IsCompact K :=
    ((Formalism.L2.SG.Pf.hinf_compact X u).prod hK0c).image
      ((continuous_fst.mul continuous_snd).mul continuous_fst.inv)
  have hK0K : K0 ⊆ K := fun k hk => ⟨(1, k), ⟨(Hinf X u).one_mem, hk⟩, by simp⟩
  have hKpos : 0 < X.muN u K := lt_of_lt_of_le hK0pos (measure_mono hK0K)
  have hKfin : X.muN u K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKinv : ∀ g ∈ Hinf X u, (fun s => g * s * g⁻¹) ⁻¹' K = K := by
    intro g hg
    ext x
    constructor
    · rintro ⟨⟨a, k⟩, ⟨ha, hk⟩, hx⟩
      refine ⟨(g⁻¹ * a, k), ⟨(Hinf X u).mul_mem ((Hinf X u).inv_mem hg) ha, hk⟩, ?_⟩
      have hx' : a * k * a⁻¹ = g * x * g⁻¹ := hx
      show g⁻¹ * a * k * (g⁻¹ * a)⁻¹ = x
      calc g⁻¹ * a * k * (g⁻¹ * a)⁻¹ = g⁻¹ * (a * k * a⁻¹) * g := by group
        _ = x := by rw [hx']; group
    · rintro ⟨⟨a, k⟩, ⟨ha, hk⟩, hx⟩
      refine ⟨(g * a, k), ⟨(Hinf X u).mul_mem hg ha, hk⟩, ?_⟩
      have hx' : a * k * a⁻¹ = x := hx
      show g * a * k * (g * a)⁻¹ = g * x * g⁻¹
      calc g * a * k * (g * a)⁻¹ = g * (a * k * a⁻¹) * g⁻¹ := by group
        _ = g * x * g⁻¹ := by rw [hx']

  have key : ∀ g ∈ Hinf X u, (X.muN u).map (fun s => g * s * g⁻¹) = X.muN u := by
    intro g hg
    have hm : Measurable fun s : X.B.I.Ginf => g * s * g⁻¹ := (hcont g).measurable
    have hpre : ∀ S : Set X.B.I.Ginf, (fun s => g * s * g⁻¹) ⁻¹' S = (fun s => g⁻¹ * s * g⁻¹⁻¹) '' S := by
      intro S
      exact (congrFun (Set.image_eq_preimage_of_inverse (f := fun s => g⁻¹ * s * g⁻¹⁻¹)
        (g := fun s => g * s * g⁻¹) (fun s => by show g * (g⁻¹ * s * g⁻¹⁻¹) * g⁻¹ = s; group)
        (fun s => by show g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s; group)) S).symm
    have hν0 : (X.muN u).map (fun s => g * s * g⁻¹) ≠ 0 := by
      intro hz
      apply h0
      have := congrArg (fun m : Measure X.B.I.Ginf => m Set.univ) hz
      simp only [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this
      exact Measure.measure_univ_eq_zero.1 this
    have hνc : (X.muN u).map (fun s => g * s * g⁻¹) (N : Set X.B.I.Ginf)ᶜ = 0 := by
      rw [Measure.map_apply hm hNc.measurableSet.compl]
      exact measure_mono_null (t := (N : Set X.B.I.Ginf)ᶜ) (fun ⦃s⦄ hs hsN => hs (hconj g hg s hsN)) hc
    have hνi : ∀ t ∈ N, ((X.muN u).map (fun s => g * s * g⁻¹)).map (fun x => t * x) =
        (X.muN u).map (fun s => g * s * g⁻¹) := by
      intro t ht
      have ht' : g⁻¹ * t * g⁻¹⁻¹ ∈ X.NinfU u := hconj g⁻¹ ((Hinf X u).inv_mem hg) t ht
      rw [Measure.map_map (measurable_const_mul t) hm]
      have e : (fun x => t * x) ∘ (fun s => g * s * g⁻¹) =
          (fun s => g * s * g⁻¹) ∘ (fun x => (g⁻¹ * t * g⁻¹⁻¹) * x) := by
        funext s
        show t * (g * s * g⁻¹) = g * (g⁻¹ * t * g⁻¹⁻¹ * s) * g⁻¹
        group
      rw [e, ← Measure.map_map hm (measurable_const_mul _), hl _ ht']
    have hνf : IsFiniteMeasureOnCompacts ((X.muN u).map (fun s => g * s * g⁻¹)) := ⟨fun C hC => by
      rw [Measure.map_apply hm hC.isClosed.measurableSet, hpre]
      exact (hC.image (hcont _)).measure_lt_top⟩
    obtain ⟨c, _, hceq⟩ := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.haar_unique N hNc (X.muN u)
      ((X.muN u).map (fun s => g * s * g⁻¹)) h0 hc hl hfin hνc hνi hνf
    have hK' : (X.muN u).map (fun s => g * s * g⁻¹) K = X.muN u K := by
      rw [Measure.map_apply hm hKc.isClosed.measurableSet, hKinv g hg]
    rw [hceq, Measure.smul_apply, smul_eq_mul] at hK'
    have hc1 : c = 1 := (ENNReal.mul_left_inj hKpos.ne' hKfin).1 (hK'.trans (one_mul _).symm)
    rw [hceq, hc1, one_smul]
  have hinv' : h⁻¹ ∈ Hinf X u := (Hinf X u).inv_mem hh
  have e : (fun s => h * s * h⁻¹) '' Ω = (fun s => h⁻¹ * s * h⁻¹⁻¹) ⁻¹' Ω :=
    congrFun (Set.image_eq_preimage_of_inverse (f := fun s => h * s * h⁻¹) (g := fun s => h⁻¹ * s * h⁻¹⁻¹)
      (fun s => by show h⁻¹ * (h * s * h⁻¹) * h⁻¹⁻¹ = s; group)
      (fun s => by show h * (h⁻¹ * s * h⁻¹⁻¹) * h⁻¹ = s; group)) Ω
  rw [e, ← Measure.map_apply (hcont _).measurable hΩ, key _ hinv']

end Formalism.L2.SG.Pf.IdMeet
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolPf

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

theorem roinf_eq_nocol {D : D7} {X : HidaSetting D} (Y : Full X) {u : D.what₂.Word} (ρ : (Y.cs u).Cl)
    (t : GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)) (hl : t.lam = (Y.cs u).lamOf ρ)
    (hl' : t.lam' = (Y.cs u).lamOf ρ) (hγ : t.lin ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u))) :
    ROinf t = Formalism.L2.SG.TermOp.KExpCut.NOcol (X.Fu u) (Y.cs u) ρ := by
  ext y
  unfold ROinf ROset Formalism.L2.SG.TermOp.KExpCut.NOcol
  rw [hl, hl']
  constructor
  · rintro ⟨x, n, hx, hy, hn, -⟩
    exact ⟨x, n, hx, hy, hn⟩
  · rintro ⟨x, n, hx, hy, hn⟩
    refine ⟨x, n, hx, hy, hn, ?_⟩
    let H := NLamSub ((Y.cs u).lamOf ρ) (lf D (X.Fu u))
    exact H.mul_mem (H.mul_mem (H.inv_mem hγ) hn) hγ

theorem idMeetVolC_of (hK : IdMeetKeyC) (hV : VolColC) : IdMeetVolC := by
  intro D X Y u hN hF ρ t ht hm
  obtain ⟨-, hlin⟩ := hK D X Y u hN ρ ρ t ht hm
  have hR := roinf_eq_nocol Y ρ t hm.1.symm hm.2.1.symm hlin
  have hex : ∃ Ω, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROinf t) Ω := hF t
  unfold FundOf
  rw [dite_eq_left hex]
  apply hV D X Y u ρ
  rw [← hR]
  exact hex.choose_spec

end Formalism.L2.SG.Pf.IdMeet
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetPf

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.IdMeet

theorem volColC_holds : VolColC :=
  volColC_of noinfEqC_holds nocolEqC_holds gcCountC_holds fundMeasEqC_holds indexVolC_holds indexTransferC_holds
    conjUC_holds gcFundC_holds gcConjC_holds hinfConjC_holds

theorem idMeetOneC_holds : IdMeetOneC := idMeetOneC_of idMeetKeyC_holds

theorem idMeetPhaseC_holds : IdMeetPhaseC := idMeetPhaseC_of idMeetKeyC_holds

theorem idMeetVolC_holds : IdMeetVolC := idMeetVolC_of idMeetKeyC_holds volColC_holds

end Formalism.L2.SG.Pf
end
end
end
