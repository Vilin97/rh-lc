module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTuplesOfLaws
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationExtendsByNewTuplesKeepingLawsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictToBase
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOneOfChrEq
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalFixedPointAtPlace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwLevPow

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwLevPow

theorem val_pow {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (a : ℕ) (v) :
    (χ ^ a).val v = χ.val v ^ a :=
  GlobalTheory.ConjExt.locK_pow χ a v _

theorem twLev_pow : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (χ : Formalism.L2.Host.HChar D.host.E) (xi : (AE D)ˣ →* Circle) (Q : Finset (Pl D.host.E)) (xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ),
      GlobalTheory.BigOn.Exp.TwConj.TwLev R χ xi Q xiR → ∀ a b : ℕ, (χ ^ a) ^ b = χ →
      GlobalTheory.BigOn.Exp.TwConj.TwLev R (χ ^ a) (xi ^ a) Q (fun PP => xiR PP ^ a) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC χ xi Q xiR h a b hab

  have hQ0 : ∀ PP, PP ∉ R.Q A.μ0 := fun PP hPP =>
    ((hC.lev.Q_ram A.μ0 PP).2 (Or.inl hPP)) (by rw [hC.lev.xi_base]; intro x _; rfl)
  refine
    { xi := GlobalTheory.ConjExt.chrEq_pow h.xi a
      xi_fin := ?_
      xi_triv := GlobalTheory.ConjExt.trivOn_pow h.xi_triv a
      xi_tame := fun v x h1 h2 => by
        rw [GlobalTheory.ConjExt.loc_pow, h.xi_tame v x h1 h2, one_pow]
      Q_pl := h.Q_pl
      Q_off := h.Q_off
      Q_de := h.Q_de
      Q_ram := fun PP => Iff.trans
        (not_congr ⟨fun hu => hab ▸ GlobalTheory.ConjExt.unrAt_pow hu b, fun hu => GlobalTheory.ConjExt.unrAt_pow hu a⟩) (h.Q_ram PP)
      xiR := fun PP hP c k u h1 h2 => by
        show (xiR PP ^ a) u = (χ ^ a).locK PP k
        rw [GlobalTheory.ConjExt.locK_pow, MonoidHom.pow_apply, h.xiR PP hP c k u h1 h2]
      roots := h.roots
      muVal := ?_
      half := h.half
      guard := h.guard }
  · obtain ⟨n, hn, ho⟩ := h.xi_fin
    refine ⟨n, hn, ?_⟩
    show (χ ^ a) ^ n = 1
    rw [← pow_mul, mul_comm, pow_mul, show χ ^ n = 1 from ho, one_pow]
  · intro i P hP
    obtain ⟨x, hx⟩ := h.muVal i P hP
    have hP0 : Bridge.SplitOff (R.pl P) ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q A.μ0 : Set (Pl D.host.E))) := by
      refine ⟨hP.1, fun hm => ?_, fun Q' hQ' => ?_⟩
      · rcases hm with hm | hm
        · exact hP.2.1 (Or.inl hm)
        · exact hQ0 _ hm
      · rcases hQ' with hQ' | hQ'
        · exact hP.2.2 Q' (Or.inl hQ')
        · exact absurd hQ' (hQ0 _)
    obtain ⟨g, c0R, c0L, ht⟩ := hC.fam.tie
    have hy := hC.fam.muVal i A.μ0 P ((ht.ok A.μ0 P).2 hP0)
    rw [hC.lev.xi_base, mul_one] at hy
    set y : D.what₂.LLˣ := A.muVal i A.μ0 P
    refine ⟨y * (y⁻¹ * x) ^ a, ?_⟩
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mul, map_mul, map_pow, map_mul, Units.val_inv_eq_inv_val,
      map_inv₀, hx, hy, Formalism.L2.Host.HChar.val_mul, Formalism.L2.Host.HChar.val_mul, val_pow]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    rw [inv_mul_cancel_left₀ (Units.ne_zero _)]

end GlobalTheory.TwLevPow
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistConjugateTuplesSameRealisationExtension

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj


open Classical in
theorem hasTuples_of_conj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    Formalism.IndefR.Links.HostHyp D → GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∀ (ψ ψ' : Twist D Circle) (t : T0) (τ : ℂ ≃+* ℂ), IsTupOf R B ψ t → ConjChar τ ψ ψ' → FixDat B τ →
      GlobalTheory.BigOn.Exp.TwConj.HasTuples T R κ v₀ O ph j B ψ ψ' := by
  intro hDS hCW h1 h2 h3 D G _ _ Pl0 T0 A T _ R F κ v₀ O ph j B hH hL ψ ψ' t τ ht hc hf
  have hC := hL.1
  obtain ⟨n, hn⟩ := GlobalTheory.ConjExt.exists_conj_pow hC.lev t
  obtain ⟨a, -, ha, b, hb⟩ := hn τ
  have hxi' : B.de.chi * ψ'.chi = R.xi t ^ a := by
    refine MonoidHom.ext fun x => Circle.ext ?_
    rw [ha x, ht.1]
    simp only [MonoidHom.mul_apply, Circle.coe_mul, map_mul, hf.1, hc.2]
  have hQ' : R.Q t = B.de.Q ∪ ψ'.Q := by rw [hc.1, ht.2]
  by_cases hχ : R.xiH t ^ a = R.xiH t
  · have e : R.xi t ^ a = R.xi t :=
      GlobalTheory.ChrEqUnique.idc_unique D _ _ _ (GlobalTheory.ConjExt.chrEq_pow (hC.lev.xi t) a) (by rw [hχ]; exact hC.lev.xi t)
    exact hasTuples_of_laws hL Ext.refl ht ⟨by rw [hxi', e], hQ'⟩
  · have h0 : R.xiH t ≠ 1 := fun h => hχ (by rw [h, one_pow])
    have h0a : R.xiH t ^ a ≠ 1 := fun h => h0 (by rw [← hb, h, one_pow])
    have hlev := twLev_of_core hC hL.2.2.2.2.1 t
    have hleva := GlobalTheory.TwLevPow.twLev_pow R F hC _ _ _ _ hlev a b hb
    obtain ⟨A0, R0, F0, v0, O0, hL0, hE0, hxi0, htr⟩ := GlobalTheory.BaseRestrict.restrict_to_base T R F κ v₀ O ph j B hL
    have hT0 := htr _ _ _ _ hlev
    have hT0a := htr _ _ _ _ hleva
    obtain ⟨T', A', R', F', v', O', hL', hE', htup⟩ := GlobalTheory.T.realisation_extends_by_newTuples_keeping_laws h1 h2 h3 hDS hCW T R0 F0 κ v0 O0 ph j B hH hL0 Bool
      (fun b => if b then R.xiH t ^ a else R.xiH t) (fun b => if b then R.xi t ^ a else R.xi t) (fun _ => R.Q t)
      (fun b => if b then (fun PP => R.xiR t PP ^ a) else R.xiR t)
      (fun b => by cases b <;> assumption)
      (fun x y hxy => by
        cases x <;> cases y
        · rfl
        · exact absurd hxy.symm hχ
        · exact absurd hxy hχ
        · rfl)
      (fun b t0 => by rw [hxi0]; cases b; exacts [h0, h0a])
      (fun p hp => by
        obtain ⟨𝔭, h𝔭, h𝔭'⟩ := hT0.Q_de p hp
        exact ⟨𝔭, h𝔭, fun _ => h𝔭'⟩)
    obtain ⟨s, hs1, hs2⟩ := htup false
    obtain ⟨s', hs1', hs2'⟩ := htup true
    exact hasTuples_of_laws hL' (hE0.trans hE') (t := s) (t' := s')
      ⟨hs1.trans ht.1, hs2.trans ht.2⟩ ⟨hs1'.trans hxi'.symm, hs2'.trans hQ'⟩

end GlobalTheory.BigOn.Exp.TwConj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistConjugateTuplesSameRealisationExtensionStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twist_conjugate_tuples_same_realisation_extension : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    Formalism.IndefR.Links.HostHyp D → GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∀ (ψ ψ' : Twist D Circle) (t : T0) (τ : ℂ ≃+* ℂ), IsTupOf R B ψ t → ConjChar τ ψ ψ' → FixDat B τ →
      GlobalTheory.BigOn.Exp.TwConj.HasTuples T R κ v₀ O ph j B ψ ψ' := by
  first | exact @GlobalTheory.BigOn.Exp.TwConj.hasTuples_of_conj | exact GlobalTheory.BigOn.Exp.TwConj.hasTuples_of_conj | (intros; apply GlobalTheory.BigOn.Exp.TwConj.hasTuples_of_conj <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocalTupleAtPlace

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)
namespace GlobalTheory.PlaceTup
theorem has_local_tuples_at_place_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ ψ' : Twist D Circle, ψ'.Good → ConjChar τ (twVia Z.ρ ι) ψ' →
  GlobalTheory.BigOn.Exp.TwConj.HasTuples X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j (baseOf Z c w j) (twVia Z.ρ ι) ψ' := by
  intro hDS hCW _ hP D X X0 Y S YS Z c w j H ι hι τ hτ ψ' hψ' hC
  have hC0 := X.char
  have hL : GlobalTheory.BigOn.Exp.TwConj.Laws X.core X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j (baseOf Z c w j) :=
    ⟨⟨hC0.lev, hC0.grp, hC0.fam, hC0.models, hC0.chain, hC0.thP⟩, X.finT, ⟨X.geo.fw⟩,
      GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC0.lev hC0.fam hC0.models hC0.thP, X.guard, X.geo.pins j,
      by
        convert X.geo.phase j X.unif using 2
        all_goals (rename_i k; rw [X.phs k]; try simp),
      GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin hC0.lev Z.good Z.pin (c.twI w) j (c.sd w)⟩
  exact GlobalTheory.T.twist_conjugate_tuples_same_realisation_extension hDS hCW hP.decay hP.what₂.art hP.ray X.core X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j
    (baseOf Z c w j) X.host hL (twVia Z.ρ ι) ψ' (Y.tupT (D.what₂.muTw w)) τ (H.tup ι hι) hC
    (_root_.GlobalTheory.PlaceFix.fixed_at_place_of_local_alt hP D X X0 Y S YS Z c w j H τ hτ).2
end GlobalTheory.PlaceTup
end
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.GlobalTheory.T.exists_local_tuple_of_discrete_series_read : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ ψ' : Twist D Circle, ψ'.Good → ConjChar τ (twVia Z.ρ ι) ψ' →
  GlobalTheory.BigOn.Exp.TwConj.HasTuples X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j (baseOf Z c w j) (twVia Z.ρ ι) ψ' := by
  first | exact @_root_.GlobalTheory.PlaceTup.has_local_tuples_at_place_alt | exact _root_.GlobalTheory.PlaceTup.has_local_tuples_at_place_alt | (intros; apply _root_.GlobalTheory.PlaceTup.has_local_tuples_at_place_alt <;> assumption)
end
end
end
end
