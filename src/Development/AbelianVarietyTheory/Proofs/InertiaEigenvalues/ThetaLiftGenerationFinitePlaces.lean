module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardLiftLevelActsByInverseCharacter
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnDownwardThetaLiftIntegrandStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelAveragesThetaPairZeroWithoutCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLevelTypeMemSpanAveragesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLevelTypeMemSpanTranslatesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenLevelFixingThetaFunction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardLiftLevelActsByInverseCharacterStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

theorem _root_.GlobalTheory.T.downwardLift_level_acts_by_inverse_character : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t), ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ωP i t (κ, 1) f) l g = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ * downInt R i t y f l g := by
  first | exact @GlobalTheory.DownLift.TypeLaw.downInt_level | exact GlobalTheory.DownLift.TypeLaw.downInt_level | (intros; apply GlobalTheory.DownLift.TypeLaw.downInt_level <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelAveragesThetaPairZeroWithoutCharacterStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

theorem _root_.GlobalTheory.T.level_averages_theta_pair_zero_without_character : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), NoChi R i t y → ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ κ : G → GA D (Vc D i), GlobalTheory.DownLift.GenFinite.IsLifts R i t κ → ∀ f : WO (Vc D i) (Wc D i) → ℂ, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (GlobalTheory.DownLift.GenFinite.avgW R i t PP a tr ε κ f) l g = 0 := by
  first | exact @GlobalTheory.DownLift.GenFinite.avgLaw | exact GlobalTheory.DownLift.GenFinite.avgLaw | (intros; apply GlobalTheory.DownLift.GenFinite.avgLaw <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionMemSpanLevelTypeDifferences

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite.TypeSpan

variable {D : D7} {V W : HSp D}

theorem levChi_mul' {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {k k' : GA D V}
    (hk : k ∈ levG V β L) (hk' : k' ∈ levG V β L) :
    levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  have e := (Formalism.L2.DIV.levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩
  have e' : Formalism.L2.DIV.levFn β L (finE V k * finE V k') =
      Formalism.L2.DIV.levFn β L (finE V k) * Formalism.L2.DIV.levFn β L (finE V k') := e
  unfold levChi
  rw [map_mul, e', Units.val_mul]

theorem levChi_ne_zero (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (k : GA D V) :
    levChi V β L k ≠ 0 := by
  unfold levChi
  exact Units.ne_zero _

theorem eventually_levChi_one (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    ∀ᶠ κ in nhds (1 : GA D V), levChi V β L κ = 1 := by
  classical
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hh
  obtain ⟨-, -, h3⟩ := hh
  unfold levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one β L _ fun PP hP => h3 PP (by rcases hP with h | h <;> simp [h]), Units.val_one]

end GlobalTheory.DownLift.GenFinite.TypeSpan

namespace GlobalTheory.DownLift.GenFinite

open GlobalTheory.DownLift.GenFinite.TypeSpan

theorem typeSpan : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → f ∈ Submodule.span ℂ ({φ | GlobalTheory.DownLift.GenFinite.TypeVec R i t φ} ∪ GlobalTheory.DownLift.GenFinite.TypeDiff R i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ hP i t f hf
  classical
  have hW := (hP i t).datum
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (Vc D i).gram
  obtain ⟨U, U', hUo, -, hfix⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D R.ψ hW.std (Vc D i) (Wc D i) (R.ωP i t)
    (GlobalTheory.Ker.isWeak_of_datum hW) hW.om_cont f hf
  set J := levG (Vc D i) (R.βV i) (R.datVt i t) with hJ
  set lam := levChi (Vc D i) (R.βV i) (R.datVt i t) with hlam
  set om := R.ωP i t with hom
  have hmul : ∀ a b : GA D (Vc D i), om (a * b, 1) = om (a, 1) * om (b, 1) := fun a b => by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hone : om (1, 1) = 1 := by rw [← Prod.one_eq_mk, map_one]
  have hlm : ∀ {a b : GA D (Vc D i)}, a ∈ J → b ∈ J → lam (a * b) = lam a * lam b := fun ha hb => levChi_mul' ha hb
  have hlne : ∀ a : GA D (Vc D i), lam a ≠ 0 := fun a => levChi_ne_zero _ _ a
  have hlam1 : lam 1 = 1 := by
    have e := hlm (one_mem J) (one_mem J)
    rw [mul_one] at e
    have h0 := hlne 1
    have e' : lam 1 * 1 = lam 1 * lam 1 := by rw [mul_one]; exact e
    exact (mul_left_cancel₀ h0 e').symm

  let N : Subgroup J :=
    { carrier := {κ | om ((κ : GA D (Vc D i)), 1) f = f ∧ lam κ = 1}
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨?_, ?_⟩
        · show om ((a : GA D (Vc D i)) * b, 1) f = f
          rw [hmul, Module.End.mul_apply, hb1, ha1]
        · show lam ((a : GA D (Vc D i)) * b) = 1
          rw [hlm a.2 b.2, ha2, hb2, one_mul]
      one_mem' := by
        refine ⟨?_, ?_⟩
        · show om (1, 1) f = f
          rw [hone]; rfl
        · exact hlam1
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        refine ⟨?_, ?_⟩
        · show om ((a : GA D (Vc D i))⁻¹, 1) f = f
          conv_lhs => rw [← ha1]
          rw [← Module.End.mul_apply, ← hmul, inv_mul_cancel, hone]; rfl
        · show lam ((a : GA D (Vc D i))⁻¹) = 1
          have e := hlm (inv_mem a.2) a.2
          rw [inv_mul_cancel, hlam1, ha2, mul_one] at e
          exact e.symm }
  have hNo : IsOpen (N : Set J) := by
    refine Subgroup.isOpen_of_mem_nhds N (g := 1) ?_
    have h1 : {x : GA D (Vc D i) | x ∈ U ∧ lam x = 1} ∈ nhds (1 : GA D (Vc D i)) :=
      Filter.inter_mem (hUo.mem_nhds U.one_mem) (eventually_levChi_one _ _)
    have h2 := (continuous_subtype_val (p := fun x => x ∈ J)).continuousAt (x := (1 : J)).preimage_mem_nhds h1
    exact Filter.mem_of_superset h2 fun κ hκ => ⟨hfix _ hκ.1 κ.2.1 1 U'.one_mem (one_mem _), hκ.2⟩
  haveI : CompactSpace J := isCompact_iff_compactSpace.mp (GlobalTheory.ParahoricCompact.isCompact_levG _ _ _)
  haveI : Finite (J ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  letI : Fintype (J ⧸ N) := Fintype.ofFinite _

  let Fv : J → (WO (Vc D i) (Wc D i) → ℂ) := fun κ => lam κ • om ((κ : GA D (Vc D i)), 1) f
  have hFvN : ∀ (a n : J), n ∈ N → Fv (a * n) = Fv a := by
    rintro a n ⟨hn1, hn2⟩
    show lam ((a : GA D (Vc D i)) * n) • om ((a : GA D (Vc D i)) * n, 1) f = lam a • om ((a : GA D (Vc D i)), 1) f
    rw [hlm a.2 n.2, hn2, mul_one, hmul, Module.End.mul_apply, hn1]
  let Fb : J ⧸ N → (WO (Vc D i) (Wc D i) → ℂ) := fun q => Fv q.out
  have hFb : ∀ κ : J, Fb (κ : J ⧸ N) = Fv κ := by
    intro κ
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N κ
    show Fv (κ : J ⧸ N).out = Fv κ
    rw [hn]
    exact hFvN κ n n.2
  have hFbTh : ∀ q, IsThetaFunO R.ψ (Vc D i) (Wc D i) (Fb q) := fun q =>
    theta_smul _ (hW.om_pres _ _ hf)

  have hact : ∀ (κ' : J) (q : J ⧸ N), om ((κ' : GA D (Vc D i)), 1) (Fb q) = (lam κ')⁻¹ • Fb (κ' • q) := by
    intro κ' q
    induction q using QuotientGroup.induction_on with
    | H κ =>
      rw [MulAction.Quotient.smul_mk, hFb, hFb]
      show om ((κ' : GA D (Vc D i)), 1) (lam κ • om ((κ : GA D (Vc D i)), 1) f) =
        (lam κ')⁻¹ • (lam ((κ' : GA D (Vc D i)) * κ) • om ((κ' : GA D (Vc D i)) * κ, 1) f)
      rw [map_smul, hmul, Module.End.mul_apply, hlm κ'.2 κ.2, smul_smul, ← mul_assoc,
        inv_mul_cancel₀ (hlne _), one_mul]
  set c : ℂ := ((Fintype.card (J ⧸ N) : ℕ) : ℂ)⁻¹ with hc
  set fJ := c • ∑ q, Fb q with hfJ
  have hfJv : TypeVec R i t fJ := by
    refine ⟨theta_smul _ (theta_sum Finset.univ Fb f hf fun q _ => hFbTh q), fun κ hκ => ?_⟩
    show om (κ, 1) fJ = (lam κ)⁻¹ • fJ
    have e : om (κ, 1) (∑ q, Fb q) = (lam κ)⁻¹ • ∑ q, Fb q := by

      rw [map_sum]
      have := fun q => hact ⟨κ, hκ⟩ q
      simp only [] at this
      rw [Finset.sum_congr rfl fun q _ => this q, ← Finset.smul_sum]
      congr 1
      exact Equiv.sum_comp (MulAction.toPerm (⟨κ, hκ⟩ : J)) Fb
    rw [hfJ, map_smul, e, smul_comm]
  have hdiff : ∀ q, f - Fb q ∈ Submodule.span ℂ ({φ | TypeVec R i t φ} ∪ TypeDiff R i t) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H κ =>
      rw [hFb]
      have e : f - Fv κ = (-lam κ) • (om ((κ : GA D (Vc D i)), 1) f - (lam κ)⁻¹ • f) := by
        show f - lam κ • om ((κ : GA D (Vc D i)), 1) f = _
        rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ (hlne _)]
        simp only [neg_smul, one_smul]
        abel
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨κ, κ.2, f, hf, rfl⟩))
  have hcard : ((Fintype.card (J ⧸ N) : ℕ) : ℂ) ≠ 0 := by
    have : 0 < Fintype.card (J ⧸ N) := Fintype.card_pos
    exact_mod_cast this.ne'
  have hsplit : f = fJ + c • ∑ q, (f - Fb q) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      hc, inv_mul_cancel₀ hcard, one_smul, hfJ]
    abel
  rw [hsplit]
  exact Submodule.add_mem _ (Submodule.subset_span (Or.inl hfJv))
    (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => hdiff q))

end GlobalTheory.DownLift.GenFinite

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionMemSpanLevelTypeDifferencesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

theorem _root_.GlobalTheory.T.thetaFunction_mem_span_levelType_differences : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → f ∈ Submodule.span ℂ ({φ | GlobalTheory.DownLift.GenFinite.TypeVec R i t φ} ∪ GlobalTheory.DownLift.GenFinite.TypeDiff R i t) := by
  first | exact @GlobalTheory.DownLift.GenFinite.typeSpan | exact GlobalTheory.DownLift.GenFinite.typeSpan | (intros; apply GlobalTheory.DownLift.GenFinite.typeSpan <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationFinitePlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem downInt_transl (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (g g' : GA D (Wc D i)) :
    downInt R i t y (R.ωP i t (1, g') f) l g = downInt R i t y f l (g * g') := by
  have e : ∀ h : GA D (Vc D i), thetaKO (R.ωP i t) h g (R.ωP i t (1, g') f) = thetaKO (R.ωP i t) h (g * g') f := by
    intro h
    have hm : ((h, g) : GA D (Vc D i) × GA D (Wc D i)) * (1, g') = (h, g * g') := by
      rw [Prod.mk_mul_mk, mul_one]
    show R.ωP i t (h, g) (R.ωP i t (1, g') f) 0 = R.ωP i t (h, g * g') f 0
    rw [← hm, map_mul, Module.End.mul_apply]
  simp only [downInt, e]

theorem downInt_add (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f f' : WO (Vc D i) (Wc D i) → ℂ)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i))
    (hf : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t))
    (hf' : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f' * l (R.extV i t y h)) (R.fdV i t) (R.νV i t)) :
    downInt R i t y (f + f') l g = downInt R i t y f l g + downInt R i t y f' l g := by
  unfold downInt
  rw [← integral_add hf hf']
  congr 1
  funext h
  simp [thetaKO, map_add, add_mul]

theorem downInt_smul (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (c : ℂ) (f : WO (Vc D i) (Wc D i) → ℂ)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) :
    downInt R i t y (c • f) l g = c * downInt R i t y f l g := by
  unfold downInt
  rw [← integral_const_mul]
  congr 1
  funext h
  simp [thetaKO, map_smul, mul_assoc]

end GlobalTheory.DownLift.GenFinite

namespace GlobalTheory.DownLift.GenFinite

theorem genFin : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GenFin R i t := by
  intro hH D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y hNC hvan
  rintro ⟨f, l, g, hf, hne⟩
  apply hne
  have hθ : ∀ (p : GA D (Vc D i) × GA D (Wc D i)) (φ : WO (Vc D i) (Wc D i) → ℂ),
      IsThetaFunO R.ψ (Vc D i) (Wc D i) φ → IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.ωP i t p φ) :=
    fun p φ hφ => (hP i t).datum.om_pres p φ hφ
  let Pr : (WO (Vc D i) (Wc D i) → ℂ) → Prop := fun φ =>
    IsThetaFunO R.ψ (Vc D i) (Wc D i) φ ∧ ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y φ l g = 0
  have hint := GlobalTheory.T.integrableOn_downwardThetaLift_integrand D G Pl0 T A Ks R F hG hP i t y
  have hadd : ∀ φ φ', Pr φ → Pr φ' → Pr (φ + φ') := by
    intro φ φ' h1 h2
    refine ⟨theta_add h1.1 h2.1, fun l g => ?_⟩
    rw [downInt_add R i t y φ φ' l g (hint φ l g h1.1) (hint φ' l g h2.1), h1.2 l g, h2.2 l g, add_zero]
  have hsmul : ∀ (c : ℂ) φ, Pr φ → Pr (c • φ) := by
    intro c φ h1
    exact ⟨theta_smul c h1.1, fun l g => by rw [downInt_smul, h1.2 l g, mul_zero]⟩
  have hzero : Pr 0 :=
    ⟨by simpa using theta_smul (0 : ℂ) hf,
      fun l g => by simpa using downInt_smul R i t y 0 f l g⟩
  have hspan : ∀ s : Set (WO (Vc D i) (Wc D i) → ℂ), (∀ φ ∈ s, Pr φ) → ∀ φ ∈ Submodule.span ℂ s, Pr φ := by
    intro s hs φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hs x hx
    | zero => exact hzero
    | add x y' _ _ hx hy => exact hadd x y' hx hy
    | smul c x _ hx => exact hsmul c x hx
  have hGen : ∀ φ ∈ Gen R i t, Pr φ := by
    rintro φ ⟨g', f', hf', rfl⟩
    exact ⟨hθ _ _ hf'.1, fun l g => by rw [downInt_transl]; exact hvan f' hf' l (g * g')⟩
  have hAvg : ∀ φ ∈ AvgIm R i t, Pr φ := by
    rintro φ ⟨PP, a, ha, tr, ε, hε, κ, hκ, f', hf', rfl⟩
    refine ⟨?_, fun l g => GlobalTheory.T.level_averages_theta_pair_zero_without_character D G Pl0 T A Ks R F hG hP i t y hNC PP a ha tr ε hε κ hκ f' hf' l g⟩
    unfold avgW
    exact theta_sum _ _ f' hf' fun k _ => theta_smul _ (hθ _ _ hf')
  have hType : ∀ φ, TypeVec R i t φ → Pr φ := by
    intro φ hφ
    refine hspan _ ?_ φ (GlobalTheory.T.thetaFunction_levelType_mem_span_averages D G Pl0 T A Ks R F hG hP i t φ hφ)
    rintro x (hx | hx)
    · exact hspan _ hGen x (GlobalTheory.T.thetaFunction_levelType_mem_span_translates hH D G Pl0 T A Ks R F hG hP i t x hx.1 hx.2)
    · exact hAvg x hx
  have hDiff : ∀ φ ∈ TypeDiff R i t, Pr φ := by
    rintro φ ⟨κ, hκ, f', hf', rfl⟩
    refine ⟨theta_sub (hθ _ _ hf') (theta_smul _ hf'), fun l g => ?_⟩
    have e : R.ωP i t (κ, 1) f' - (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • f' =
        R.ωP i t (κ, 1) f' + (-(levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹) • f' := by
      rw [neg_smul, sub_eq_add_neg]
    rw [e, downInt_add R i t y _ _ l g (hint _ l g (hθ _ _ hf'))
      (hint _ l g (theta_smul _ hf')), downInt_smul,
      GlobalTheory.T.downwardLift_level_acts_by_inverse_character D G Pl0 T A Ks R F hG hP i t y f' hf' κ hκ l g]
    ring
  refine (hspan _ ?_ f (GlobalTheory.T.thetaFunction_mem_span_levelType_differences D G Pl0 T A Ks R F hG hP i t f hf)).2 l g
  rintro x (hx | hx)
  · exact hType x hx
  · exact hDiff x hx

end GlobalTheory.DownLift.GenFinite
end
end
end
