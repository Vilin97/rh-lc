module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AvgLevel
public import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLevelGroupFaceLevelIffFlagGroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterSpaceCoordsIffLevelActsByCharStatement
import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincipalLevelFormOfFaceLevelMultiplicity

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.MultLevelP

theorem multT_mono {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (hJ : J' ⊆ J) (hχ : ∀ k ∈ J', χ' k = χ k) :
    MultT θ M J χ ≤ MultT θ M J' χ' := by
  unfold MultT Mult
  exact Submodule.map_mono (Submodule.span_mono fun T hT =>
    ⟨hT.aut, hT.cusp, fun v k hk g => by rw [hχ k hk]; exact hT.lev v k (hJ hk) g, hT.equiv, hT.cont⟩)

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}

theorem levS_flag1_sub (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) : levS V β (flag1L L) ⊆ levS V β L := by
  rintro κ ⟨hκ, hp, hr⟩
  have e : Formalism.L2.DIV.rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hr
  refine ⟨hκ, hp, ?_⟩
  show Formalism.L2.DIV.rTup β L (finE V κ) ∈ L.P.H
  rw [e]
  exact L.P.H.one_mem

theorem levChi_flag1 (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {κ : GA D V} (hκ : κ ∈ levS V β (flag1L L)) :
    levChi V β (flag1L L) κ = levChi V β L κ := by
  obtain ⟨-, -, hr⟩ := hκ
  have e : Formalism.L2.DIV.rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hr
  have h1 : Formalism.L2.DIV.rTup β L (finE V κ) ∈ L.P.H := e ▸ L.P.H.one_mem
  have h := levFn_withP (β := β) (L := L) L.P (finE V κ)
  change Formalism.L2.DIV.levFn β L (finE V κ) = _ at h
  have e1 : (⟨_, h1⟩ : L.P.H) = 1 := Subtype.ext e
  unfold levChi
  rw [levFn_flag1, h, Formalism.L2.DIV.extendOne_of_mem _ h1, e1, map_one, one_mul]

end GlobalTheory.MultLevelP



theorem GlobalTheory.MultLevelP.exists_form_of_mult : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (Tm : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)), Tm ∈ Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) → ∃ Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ, (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) ∧ R.cX.toMap R.prX Fn = Tm := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB b t Tm hTm
  have hθ := hB.models.inf
  have hc := hB.models.cX
  have hpr := hB.models.prX
  have hp := GlobalTheory.DefiniteMult.allPlus_parB (V := D.sp.X') _ (Nat.sub_le _ _) R.MX
  have hT0 : Tm ∈ MultT R.θ R.MX (levS _ R.βX (flag1L (datXP R t (R.levR F b))))
      (levChi _ R.βX (flag1L (datXP R t (R.levR F b)))) :=
    GlobalTheory.MultLevelP.multT_mono R.θ R.MX (GlobalTheory.MultLevelP.levS_flag1_sub (β := R.βX) (datXP R t (R.levR F b)))
      (fun k hk => GlobalTheory.MultLevelP.levChi_flag1 (datXP R t (R.levR F b)) hk) hTm
  have e : flag1L (datXP R t (R.levR F b)) = flag1L (R.datXt t) := rfl
  have hT1 : Tm ∈ MultT R.θ R.MX (levS _ R.βX (flag1L (R.datXt t))) (levChi _ R.βX (flag1L (R.datXt t))) := by
    rw [← e]; exact hT0
  have X := GlobalTheory.DefiniteMult.exists_form (D := D) (V := D.sp.X') (M := R.MX) (θ := R.θ) (c := R.cX) (pr := R.prX) (β := R.βX) (L := R.datXt t) hθ hp hc hpr hT1
  obtain ⟨Fn, hFn, hmap⟩ := X
  refine ⟨Fn, hFn, ?_, hmap⟩
  rintro ⟨q, hqQ⟩ hq h
  obtain ⟨κ, hκκ⟩ := GlobalTheory.DefiniteMult.exists_fin_lift (D := D) D.sp.X' q
  have hκ := hκκ.1
  have hκq := hκκ.2
  obtain ⟨g, hg⟩ := (finHom D.sp.X').rangeRestrict_surjective h
  subst hg
  have hqQ' : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q := by rw [hκq]; exact hqQ
  have eQ : (⟨_, hqQ'⟩ : (levEnv D.sp.X' R.βX (R.datXt t)).Q) = ⟨q, hqQ⟩ := Subtype.ext hκq
  have hq' : (R.B.R t).act_tie.red ⟨_, hqQ'⟩ ∈ (F.lvl b).P :=
    (congrArg (fun x => (R.B.R t).act_tie.red x ∈ (F.lvl b).P) eQ).mpr hq
  have key : ∀ (x y : (levEnv D.sp.X' R.βX (R.datXt t)).Q), x = y → ∀ (hx : (R.B.R t).act_tie.red x ∈ (F.lvl b).P)
      (hy : (R.B.R t).act_tie.red y ∈ (F.lvl b).P),
      ((levEnv D.sp.X' R.βX (R.datXt t)).ch x : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hx⟩ : D.what₂.LLˣ) : D.what₂.LL) =
        ((levEnv D.sp.X' R.βX (R.datXt t)).ch y : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hy⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
    rintro x _ rfl hx hy
    rfl
  have hbr := GlobalTheory.T.mem_level_group_face_level_iff_flag_group D G Pl0 T A Ks R F hB.grp.red_R b t κ hκ
  have hκS : κ ∈ levS _ R.βX (datXP R t (R.levR F b)) := hbr.1.2 ⟨hqQ', hq'⟩
  have hχ := hbr.2 hqQ' hq'
  have hM := (mem_multT _ _ _ _ _).1 hTm
  have hlev : ∀ x g', Tm x (g' * κ) = levChi _ R.βX (datXP R t (R.levR F b)) κ * Tm x g' := by
    intro x g'
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := (GlobalTheory.mult_value_left_cont_level R.θ R.MX _ _ _ hM v).2.2 κ hκS g'
      rw [map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]
      exact congrArg (r * ·) this
    | add x y hx hy => rw [map_add (f := _), Pi.add_apply, Pi.add_apply, hx, hy, mul_add]
  have hb := (GlobalTheory.DefiniteMult.pair_bijective hθ hp hc hpr).1
  have hext : R.cX.ext Fn (g * κ) = levChi _ R.βX (datXP R t (R.levR F b)) κ • R.cX.ext Fn g := by
    refine hb (LinearMap.ext fun x => ?_)
    have a1 : R.prX (R.cX.ext Fn (g * κ)) x = Tm x (g * κ) := congrFun (LinearMap.congr_fun hmap x) (g * κ)
    have a2 : R.prX (R.cX.ext Fn g) x = Tm x g := congrFun (LinearMap.congr_fun hmap x) g
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, a1, a2, hlev]
  change R.cX.ρ (g * κ)⁻¹ (Fn ((finHom D.sp.X').rangeRestrict (g * κ))) =
    levChi _ R.βX (datXP R t (R.levR F b)) κ • R.cX.ρ g⁻¹ (Fn ((finHom D.sp.X').rangeRestrict g)) at hext
  rw [GlobalTheory.DefiniteMult.rho_right_inv R.cX.ρ g (hc.1 _ (inv_mem hκ)), map_mul] at hext
  have inj : Function.Injective (R.cX.ρ g⁻¹) := fun a a' haa => by
    have := congrArg (R.cX.ρ g) haa
    rwa [GlobalTheory.DefiniteEnd.rho_inv_cancel, GlobalTheory.DefiniteEnd.rho_inv_cancel] at this
  calc Fn ((finHom D.sp.X').rangeRestrict g * q) = Fn ((finHom D.sp.X').rangeRestrict g * (finHom D.sp.X').rangeRestrict κ) :=
      congrArg (fun x => Fn ((finHom D.sp.X').rangeRestrict g * x)) hκq.symm
    _ = levChi _ R.βX (datXP R t (R.levR F b)) κ • Fn ((finHom D.sp.X').rangeRestrict g) :=
      inj (hext.trans ((R.cX.ρ g⁻¹).map_smul _ _).symm)
    _ = _ := congrArg (fun c : ℂ => c • Fn ((finHom D.sp.X').rangeRestrict g)) (hχ.trans (key _ _ eQ hq' hq))

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincipalLevelFormOfFaceLevelMultiplicityStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.exists_principalLevelForm_of_faceLevelMultiplicity : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (Tm : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)), Tm ∈ Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) → ∃ Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ, (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) ∧ R.cX.toMap R.prX Fn = Tm := by
  first | exact @GlobalTheory.MultLevelP.exists_form_of_mult | exact GlobalTheory.MultLevelP.exists_form_of_mult | (intros; apply GlobalTheory.MultLevelP.exists_form_of_mult <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalLevelFormMemFaceLevelMultiplicity

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.DefiniteMult

theorem toMap_mem_levP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (Fn : Bridge.Gf D.sp.X' → R.cX.W), Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ → (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) → R.cX.toMap R.prX Fn ∈ Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB b t Fn hFn hP
  have h := GlobalTheory.DefiniteEnd.isMultMap_toMap hB.models.inf D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) R.MX hB.models.cX
    hB.models.prX hFn
  refine (mem_multT R.θ R.MX _ _ _).2 (Submodule.subset_span ⟨h.aut, h.cusp, fun v k hk g => ?_, h.equiv, h.cont⟩)
  have hkC : k ∈ GfC D.sp.X' := hk.1
  obtain ⟨hiff, hchi⟩ := GlobalTheory.T.mem_level_group_face_level_iff_flag_group D G Pl0 T A Ks R F hB.grp.red_R b t k hkC
  have hh := hiff.1 hk
  obtain ⟨hq, hp⟩ := hh
  have hc := hchi hq hp
  have hd := hP ⟨_, hq⟩ hp ((finHom D.sp.X').rangeRestrict g)
  have e : Fn ((finHom D.sp.X').rangeRestrict (g * k)) =
      levChi _ R.βX (datXP R t (R.levR F b)) k • Fn ((finHom D.sp.X').rangeRestrict g) :=
    (congrArg Fn (map_mul _ g k)).trans (hd.trans (congrArg (· • Fn ((finHom D.sp.X').rangeRestrict g)) hc.symm))
  have e2 : R.cX.ext Fn (g * k) = levChi _ R.βX (datXP R t (R.levR F b)) k • R.cX.ext Fn g :=
    ((congrArg (R.cX.ρ (g * k)⁻¹) e).trans
      (LinearMap.congr_fun (rho_right_inv R.cX.ρ g (hB.models.cX.1 _ (inv_mem hkC))) _)).trans (map_smul _ _ _)
  exact (congrArg (fun w => R.prX w (PiTensorProduct.tprod ℂ v)) e2).trans (LinearMap.congr_fun (map_smul R.prX _ _) _)

end GlobalTheory.DefiniteMult

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalLevelFormMemFaceLevelMultiplicityStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.principalLevelForm_mem_faceLevelMultiplicity : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (Fn : Bridge.Gf D.sp.X' → R.cX.W), Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ → (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) → R.cX.toMap R.prX Fn ∈ Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) := by
  first | exact @GlobalTheory.DefiniteMult.toMap_mem_levP | exact GlobalTheory.DefiniteMult.toMap_mem_levP | (intros; apply GlobalTheory.DefiniteMult.toMap_mem_levP <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalLevelFormMemSpanAdelicRationalForms

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.TopSpan

theorem mem_of_avg {K : Type} [Field K] (σ : K →+* ℂ) {V : Type} [AddCommGroup V] [Module K V] {G : Type} [Group G]
    (r : Representation K G V) (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ) {M : Type} [AddCommGroup M] [Module ℂ M]
    (j : V →ₛₗ[σ] M) (T : P → M →ₗ[ℂ] M) (hT : ∀ p v, T p (j v) = j (r p v))
    (S : Submodule ℂ M) (hS : ∀ v, (∀ h : P, r h v = ((ψ h : Kˣ) : K) • v) → j v ∈ S)
    (Fn : M) (hF : Fn ∈ Submodule.span ℂ (Set.range j)) (hFn : ∀ p, T p Fn = σ ((ψ p : Kˣ) : K) • Fn) : Fn ∈ S := by
  let Pj : M →ₗ[ℂ] M := (Nat.card P : ℂ)⁻¹ • ∑ p : P, σ ((ψ p⁻¹ : Kˣ) : K) • T p
  have hPj : ∀ x, Pj x = (Nat.card P : ℂ)⁻¹ • ∑ p : P, σ ((ψ p⁻¹ : Kˣ) : K) • T p x := by
    intro x
    simp only [Pj, LinearMap.smul_apply, LinearMap.sum_apply]
  have hcard : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hfix : Pj Fn = Fn := by
    have hterm : ∀ p : P, σ ((ψ p⁻¹ : Kˣ) : K) • T p Fn = Fn := by
      intro p
      rw [hFn, smul_smul, ← map_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, map_one, one_smul]
    rw [hPj, Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hmap : ∀ v, Pj (j v) ∈ S := by
    intro v
    have e : Pj (j v) = j ((Nat.card P : K)⁻¹ • ∑ p : P, ((ψ p⁻¹ : Kˣ) : K) • r p v) := by

      rw [hPj, map_smulₛₗ, map_sum, map_inv₀, map_natCast]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_smulₛₗ, hT]
    rw [e]
    exact hS _ (avg_level K V G r P ψ v)
  have hle : Submodule.span ℂ (Set.range j) ≤ S.comap Pj :=
    Submodule.span_le.2 (by rintro _ ⟨v, rfl⟩; exact hmap v)
  have hPF : Pj Fn ∈ S := hle hF
  rwa [hfix] at hPF

theorem exists_rowForm (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P : Subgroup G)
    (ψ : P →* D.what₂.LLˣ) (t : T) (f : A.fam.amb.FR t) (hlv : ∀ h : P, (A.fam.R t).r h f = ((ψ h : D.what₂.LLˣ) : D.what₂.LL) • f) :
    ∃ x, rowForm A P ψ t x = f :=
  (GlobalTheory.T.levelCharacterSpace_coords_iff_level_acts_by_char _ _ _ (A.fam.R t).r P ψ f).2 hlv

theorem jR_mem_span (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) (g : A.fam.amb.FR t)
    (hg : ∀ h : (F.lvl b).P, (A.fam.R t).r h g = (((F.lvl b).ψ h : D.what₂.LLˣ) : D.what₂.LL) • g)
    (Y : Bridge.Gf D.sp.X' → R.cX.W) (hY : Y = R.B.jR t g) :
    Y ∈ Submodule.span ℂ (Set.range fun x => R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)) := by
  obtain ⟨x, hx⟩ := exists_rowForm D G Pl0 T A (F.lvl b).P (F.lvl b).ψ t g hg
  subst hY
  subst hx
  exact Submodule.subset_span ⟨x, rfl⟩



theorem proj_span : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) (Fn : Bridge.Gf D.sp.X' → R.cX.W), Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ → (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) → Fn ∈ Submodule.span ℂ (Set.range fun x => R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)) := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F b t Fn hF hQ
  have hB := Bridge.ClassPres.extBij_holds (R.B.R t).pres
  have hF0 : Fn ∈ Submodule.span ℂ (Set.range (R.B.R t).pres.extL) := by rw [hB.2]; exact hF
  have hF' : Fn ∈ Submodule.span ℂ (Set.range (R.B.jR t)) := hF0
  obtain ⟨κ, hκ⟩ : ∃ κ : (F.lvl b).P → (levEnv D.sp.X' R.βX (R.datXt t)).Q,
      ∀ p, (R.B.R t).act_tie.red (κ p) = (p : G) :=
    ⟨fun p => ((R.B.R t).act_tie.red_surj (p : G)).choose,
      fun p => ((R.B.R t).act_tie.red_surj (p : G)).choose_spec⟩
  obtain ⟨gl, gl_apply⟩ : ∃ gl : (F.lvl b).P → (Bridge.Gf D.sp.X' → R.cX.W) →ₗ[ℂ] (Bridge.Gf D.sp.X' → R.cX.W),
      ∀ p H, gl p H = Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch (κ p) H :=
    ⟨fun p => { toFun := fun H => Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch (κ p) H
                map_add' := by intro H H'; funext h; simp only [Bridge.g0Act, Pi.add_apply, smul_add]
                map_smul' := by intro c H; funext h; simp only [Bridge.g0Act, Pi.smul_apply, RingHom.id_apply]; rw [smul_comm] },
      fun _ _ => rfl⟩
  have hact : ∀ (p : (F.lvl b).P) (f : A.fam.amb.FR t), gl p (R.B.jR t f) = R.B.jR t ((A.fam.R t).r p f) := by
    intro p f
    have e : (R.B.R t).pres.extL (A.leftGroupActionRight t (p : G) f) =
        Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch (κ p) ((R.B.R t).pres.extL f) :=
      (R.B.R t).act_tie.act_eq (p : G) (κ p) (hκ p) f
    exact (gl_apply p _).trans e.symm
  have hg : ∀ p : (F.lvl b).P, gl p Fn = D.what₂.embLL (((F.lvl b).ψ p : D.what₂.LLˣ) : D.what₂.LL) • Fn := by
    intro p
    have hq : (R.B.R t).act_tie.red (κ p) ∈ (F.lvl b).P := by rw [hκ p]; exact p.2
    rw [gl_apply]
    funext h
    simp only [Bridge.g0Act, Pi.smul_apply]
    rw [hQ (κ p) hq h]
    have hp : (⟨_, hq⟩ : (F.lvl b).P) = p := Subtype.ext (hκ p)
    rw [hp, smul_smul, ← mul_assoc, Units.inv_mul, one_mul]
  exact mem_of_avg D.what₂.embLL (A.fam.R t).r (F.lvl b).P (F.lvl b).ψ (R.B.jR t) gl hact _
    (fun v hv => jR_mem_span D G Pl0 T A Ks R F b t v hv _ rfl) Fn hF' hg

end GlobalTheory.TopSpan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalLevelFormMemSpanAdelicRationalFormsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.principalLevelForm_mem_span_adelicRationalForms : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) (Fn : Bridge.Gf D.sp.X' → R.cX.W), Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ → (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) → Fn ∈ Submodule.span ℂ (Set.range fun x => R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)) := by
  first | exact @GlobalTheory.TopSpan.proj_span | exact GlobalTheory.TopSpan.proj_span | (intros; apply GlobalTheory.TopSpan.proj_span <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLevelFormsSpanDefiniteMultiplicitySpace

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.TopSpan

theorem span_range_map_mem {M N ι : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (f : M →ₗ[ℂ] N)
    (g : ι → M) {y : M} (hy : y ∈ Submodule.span ℂ (Set.range g)) : f y ∈ Submodule.span ℂ (Set.range fun i => f (g i)) := by
  have h := Submodule.mem_map_of_mem (f := f) hy
  rwa [Submodule.map_span, ← Set.range_comp] at h



theorem topSpan : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → A.fam.Ok 1 → TopMultH R → ∀ (b : Bool) (t : T), Submodule.span ℂ (Set.range fun x => R.cX.toMap R.prX ((R.HX t).e (R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)))) = Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB hPr hOk hTop b t
  have hjX : ∀ x, (R.HX t).e (R.jX t x) = R.B.jR t x := hB.models.jX t
  simp only [hjX]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hmem : R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x) ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ
        (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ :=
      Bridge.ClassPres.extMem_holds (R.B.R t).pres _
    have hlv := (GlobalTheory.T.levelCharacterSpace_coords_iff_level_acts_by_char _ _ _ (A.fam.R t).r (F.lvl b).P (F.lvl b).ψ (rowForm A (F.lvl b).P (F.lvl b).ψ t x)).1 ⟨x, rfl⟩
    exact GlobalTheory.T.principalLevelForm_mem_faceLevelMultiplicity D G Pl0 T A Ks R F hB b t _ hmem (GlobalTheory.TopSpan.jR_level D G Pl0 T A Ks R F b t _ hlv)
  · intro Tm hT
    obtain ⟨Fn, hF, hQ, rfl⟩ := GlobalTheory.T.exists_principalLevelForm_of_faceLevelMultiplicity D G Pl0 T A Ks R F hB b t Tm hT
    exact span_range_map_mem (R.cX.toMap R.prX) (fun x => R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x))
      (GlobalTheory.T.principalLevelForm_mem_span_adelicRationalForms D G Pl0 T A Ks R F b t Fn hF hQ)

end GlobalTheory.TopSpan
end
end
