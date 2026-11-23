module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDividingLabelsIffClassZeroStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotTwistSumZeroFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumIOfSumFMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermNonzeroIndexMemMaximalIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermNonzeroIndexMemMaximalIdealStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTwistWeightWellDefinedLatticeStatement
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Definitions.Divisors.IsMemberPOfIsMember

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.Poinc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GSep.MemberModel

variable {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {L : Type} [AddCommGroup L] {mo : L → V} {hL : I → L → L}

theorem terms_sum (𝔪 : GMem X₁ z₁ act V ev L mo hL) {x₀ : X₁.S.Gam} {C : Type} {lab : C → X₁.S.Gam}
    {T : L → C → V} (h : 𝔪.Terms x₀ lab T) (c : C) :
    SumF (maximalIdeal V) (FractionRing V)
      (fun χ => algebraMap V (FractionRing V) (T (𝔪.e₈.symm χ) c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)
      (𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩) := by
  obtain ⟨x, fr, th, w₀, s, g', w, -, -, hth, -, hs, hc, hT⟩ := h
  have := (hc c).2.2 1 le_rfl (w c) (fun z J _ => (pow_one _).symm) (hc c).2.1 th s _ hs (hth (lab c))
  convert this using 2 with χ
  rw [hT, AddEquiv.apply_symm_apply]

section
open GlobalTheory.UPoinc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

end

section
open GlobalTheory.UPoinc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

end

end GlobalTheory.GSep.MemberModel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberIndexZeroTermEqThetaRatioMod

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep.ConstTerm

theorem sub_mem_of_sumI {V Ix : Type} [CommRing V] {I : Ideal V} {y : Ix → V} {v : V} (h : SumI I y v) (i₀ : Ix)
    (hy : ∀ j, j ≠ i₀ → y j ∈ I) : v - y i₀ ∈ I := by
  classical
  obtain ⟨N, -, -, -, hS⟩ := h
  obtain ⟨S, hS⟩ := hS 1
  have h1 := Submodule.smul_mono (le_refl (I ^ 1)) (le_top : N ≤ ⊤) (hS (insert i₀ S) (Finset.subset_insert _ _))
  rw [pow_one, smul_eq_mul, Ideal.mul_top, ← Finset.add_sum_erase _ _ (Finset.mem_insert_self i₀ S)] at h1
  have h2 : ∑ j ∈ (insert i₀ S).erase i₀, y j ∈ I :=
    Submodule.sum_mem _ fun j hj => hy j (Finset.ne_of_mem_erase hj)
  have := add_mem h1 h2
  convert this using 1
  ring

theorem const_term_sub_mem : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C) (r : X₁.M.Z.presheaf.stalk z₁), X₁.M.stalkHom z₁ r = X₁.S.th (lab c) / X₁.S.th x₀ → ev1 r - T 0 c ∈ maximalIdeal V1 := by
  intro I X₁ z₁ act x₀ hd V _ _ _ ev X _ t δ 𝔪 C lab hlab T hT c r hr
  haveI : IsNoetherianRing V := 𝔪.cn.1
  haveI : IsLocalHom ev := 𝔪.loc
  have hθ : 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := GlobalTheory.GSep.TwistModel.yK_th_ne_zero 𝔪 hd
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hd' := hd.of_specializes
    (ξ := (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) (sp _)
  have hs : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have e := RatModel.val_mul hs (hd'.2 (lab c)) (𝔪.reg _ (X₁.S.th_mem x₀))
  rw [div_mul_cancel₀ _ hd.1, ← hr, GlobalTheory.GSep.TwistModel.val_stalkHom] at e
  have e' : 𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩ =
      algebraMap V (FractionRing V) (ev r) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    rw [𝔪.yK_eq, 𝔪.yK_eq]
    exact e
  have hS := GlobalTheory.GSep.MemberModel.terms_sum 𝔪 hT c
  rw [e'] at hS
  have hI := GlobalTheory.Poinc.TwistSum₂.sumI_of_sumF_mul (fun χ => T (𝔪.e₈.symm χ) c) (ev r) _ hθ hS
  have := sub_mem_of_sumI hI 0 fun j hj =>
    GlobalTheory.T.thetaMember_term_nonzero_index_mem_maximalIdeal I X₁ z₁ act x₀ hd V ev X t δ 𝔪 C lab hlab T hT c _ (𝔪.e₈.symm.map_ne_zero_iff.2 hj)
  simpa only [map_zero] using this

end GlobalTheory.GSep.ConstTerm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberIndexZeroTermEqThetaRatioModStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.thetaMember_index_zero_term_eq_theta_ratio_mod : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C) (r : X₁.M.Z.presheaf.stalk z₁), X₁.M.stalkHom z₁ r = X₁.S.th (lab c) / X₁.S.th x₀ → ev1 r - T 0 c ∈ maximalIdeal V1 := by
  first | exact @GlobalTheory.GSep.ConstTerm.const_term_sub_mem | exact GlobalTheory.GSep.ConstTerm.const_term_sub_mem | (intros; apply GlobalTheory.GSep.ConstTerm.const_term_sub_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumZetaPowerResidueDividingLabel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.GSep.TwistResid

theorem twist_resid : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), lab c ∈ X₁.S.supI X₁.M z₁ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ (sg : ℤˣ) (e : ℕ), GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ e → ∀ s u : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) → X₁.M.stalkHom z₁ u = X₁.S.th (lab c + τ) / X₁.S.th (lab c) → ev1 (s * u) - 1 ∈ maximalIdeal V1 := by
  classical
  intro I X₁ z₁ act x₀ hx₀ V _ _ _ ev Y _ t δ 𝔪 C lab hlab T hT c hc τ hτ sg e hTw s u hs hu
  have hcd : X₁.M.Div X₁.S.th (lab c) z₁ := hc
  have hqO : X₁.S.th (lab c) / X₁.S.th x₀ ∈ X₁.M.O z₁ := hx₀.2 (lab c)
  let r := (X₁.M.stalkEquiv z₁).symm ⟨_, hqO⟩
  have hr : X₁.M.stalkHom z₁ r = X₁.S.th (lab c) / X₁.S.th x₀ := by
    rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
  have hrU : IsUnit r := ((RatModel.isUnit_O_iff (⟨_, hqO⟩ : X₁.M.O z₁)).2
    ⟨div_ne_zero hcd.1 hx₀.1, by rw [inv_div]; exact hcd.2 x₀⟩).map (X₁.M.stalkEquiv z₁).symm
  obtain ⟨zt, hzt⟩ : ∃ zt : X₁.M.Z.presheaf.stalk z₁,
      X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) := by
    obtain ⟨s', hs'⟩ := (X₁.M.stalkEquiv z₁).surjective
      ⟨algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)), Subalgebra.algebraMap_mem _ _⟩
    exact ⟨s', by rw [← RatModel.coe_stalkEquiv, hs']⟩
  obtain ⟨wt, hwt⟩ := GlobalTheory.T.thetaMember_twist_weight_wellDefined_lattice I X₁ z₁ act x₀ hx₀ V ev Y t δ 𝔪 sg τ hτ
  let wt' : Y → ZMod (X₁.S.r * X₁.S.N) := fun mu => if mu = 0 then 0 else wt mu
  have hwt' : ∀ a mu, 𝔪.YY a mu → wt' mu = (sg : ℤ) • eStd X₁.S.g _ τ a := by
    intro a mu h
    by_cases h0 : mu = 0
    · subst h0
      have ha : a ∈ X₁.S.HH X₁.M z₁ := (GlobalTheory.T.mem_dividingLabels_iff_class_zero I X₁ z₁ act x₀ hx₀ V ev Y t δ 𝔪 a).2 h
      have h1 : eStd X₁.S.g _ τ a = 0 := hτ a ha
      simp only [wt', if_pos rfl, h1, smul_zero]
    · simp only [wt', if_neg h0]
      exact hwt a mu h
  have hh : X₁.M.stalkHom z₁ (s * u * r) = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) * X₁.S.th (lab c + τ) / X₁.S.th x₀ := by
    rw [map_mul, map_mul, hs, hu, hr]
    field_simp [hcd.1, hx₀.1]
  obtain ⟨N, -, -, -, hN⟩ := hTw zt (s * u * r) hzt hh wt' hwt'
  obtain ⟨S, hS⟩ := hN 1
  have h1 := hS (insert 0 S) (Finset.subset_insert _ _)
  have hle : maximalIdeal V ^ 1 • N ≤ (maximalIdeal V : Submodule V V) :=
    Submodule.smul_le.2 fun a ha b _ => by
      rw [smul_eq_mul]; exact Ideal.mul_mem_right b _ (by simpa using ha)
  have h2 := hle h1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_insert_self 0 S)] at h2
  have h3 : ∑ mu ∈ (insert 0 S).erase 0, ev zt ^ (wt' mu).val * T mu c ∈ maximalIdeal V :=
    Ideal.sum_mem _ fun mu hmu => Ideal.mul_mem_left _ _
      (GlobalTheory.T.thetaMember_term_nonzero_index_mem_maximalIdeal I X₁ z₁ act x₀ hx₀ V ev Y t δ 𝔪 C lab hlab T hT c mu (Finset.ne_of_mem_erase hmu))
  have h0 : ev zt ^ (wt' 0).val * T 0 c = T 0 c := by simp [wt']
  rw [h0] at h2
  have h4 : ev (s * u * r) - T 0 c ∈ maximalIdeal V := by
    have := Ideal.add_mem _ h2 h3
    simpa [sub_add_eq_sub_sub, sub_add_cancel] using this
  have h5 := GlobalTheory.T.thetaMember_index_zero_term_eq_theta_ratio_mod I X₁ z₁ act x₀ hx₀ V ev Y t δ 𝔪 C lab hlab T hT c r hr
  have h6 : (ev (s * u) - 1) * ev r ∈ maximalIdeal V := by
    have := Ideal.sub_mem _ h4 h5
    rw [map_mul] at this
    convert this using 1; ring
  exact (Ideal.mul_unit_mem_iff_mem _ (hrU.map ev)).1 h6

end GlobalTheory.GSep.TwistResid
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumZetaPowerResidueDividingLabelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.twistedSum_zeta_power_residue_dividing_label : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), lab c ∈ X₁.S.supI X₁.M z₁ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ (sg : ℤˣ) (e : ℕ), GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ e → ∀ s u : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) → X₁.M.stalkHom z₁ u = X₁.S.th (lab c + τ) / X₁.S.th (lab c) → ev1 (s * u) - 1 ∈ maximalIdeal V1 := by
  first | exact @GlobalTheory.GSep.TwistResid.twist_resid | exact GlobalTheory.GSep.TwistResid.twist_resid | (intros; apply GlobalTheory.GSep.TwistResid.twist_resid <;> assumption)
end
end
