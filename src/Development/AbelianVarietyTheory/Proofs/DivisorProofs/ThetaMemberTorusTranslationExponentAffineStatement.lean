module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFCompEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentsAffineTwoMembersStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsFrameExponentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrExp
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermsCoefficientsUnique
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.YKThNeZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermsCoefficientsUniqueStatement

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
open GlobalTheory.UT.CoefBasic


theorem _root_.GlobalTheory.T.thetaMember_terms_coefficients_unique : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (b : X₁.S.Gam)
  (x x₂ : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (fr₂ : ∀ a, FrAt (x₂ a))
  (th th₂ : SecA 𝔪.A (FractionRing V) 1) (w₀ w₀₂ : W0 𝔪.U.toUnifPre) (s s₂ : Fam 𝔪.D.toPre (FractionRing V) 1)
  (g' g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
  (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
  (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
  (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
  𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g' o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g' w (x b) (fr b) →
  (∀ a, (x₂ a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
  (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
  (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀₂.IsGen →
  𝔪.U.ExpandsF (FractionRing V) 1 w₀₂ th₂ s₂ →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) → w₂.IsGen → 𝔪.Over' w₀₂ g₂ w₂ (x₂ b) (fr₂ b) →
  ∀ χ, coef s g' w χ = coef s₂ g₂ w₂ χ := by
  first | exact @GlobalTheory.GSep.TermsUniq.coef_eq | exact GlobalTheory.GSep.TermsUniq.coef_eq | (intros; apply GlobalTheory.GSep.TermsUniq.coef_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationExponentOfFrameExponent

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
open GlobalTheory.UT.CoefBasic
open GlobalTheory.GSep GlobalTheory.GSep.TransTerms

namespace GlobalTheory.GSep.TransTerms

theorem transExp_of_frExp : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ), ∀ a ∈ X₁.S.HH X₁.M z₁, ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ e : ℕ, GlobalTheory.GSep.TransTerms.FrExp 𝔪 a τ e → GlobalTheory.GSep.TransTerms.TransExp 𝔪 x₀ a τ e := by
  have huniq := GlobalTheory.T.thetaMember_terms_coefficients_unique
  intro I X₁ z₁ act x₀ hdiv V _ _ _ ev Y _ t δ 𝔪 a _ τ _ e hF
  obtain ⟨-, x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, htor, hw, hov, htr⟩ := hF
  intro χ hχ C lab T hT c hc C' lab' T' hT' c' hc' mu
  letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (FractionRing V)
  set g₀ := GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ) with hg₀def
  have hg₀ : IsTor χ g₀ := (GlobalTheory.UT.isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ)
  have hadd : g'.IsAdd g₀ (g' + g₀) := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl
  have hb : (g' + g₀).b = g'.b := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  set c₀ : FractionRing V := 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) with hc₀def
  have hc₀ : c₀ ≠ 0 :=
    ((((X₁.S.prim.isUnit (by have := X₁.S.r_pos; have := X₁.S.N_ge; positivity)).pow e).map
      (algebraMap X₁.o₁ X₁.S.R)).map 𝔪.yK).ne_zero
  obtain ⟨w₁, hw₁, hv₁⟩ := GlobalTheory.UT.TorsionValue.exists_frm_scale w hw (inv_ne_zero hc₀)
  obtain ⟨w'', hw'', hv''⟩ : ∃ w'' : Frm 𝔪.D.toPre (FractionRing V) 1 (g' + g₀).b, w''.IsGen ∧
      ∀ z J, val w'' (𝟙 _) z J = val w₁ (𝟙 _) z J := by
    rw [hb]; exact ⟨w₁, hw₁, fun _ _ => rfl⟩
  have hvs : ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w'' (𝟙 _) z J).val = cstH z c₀⁻¹ * (val w (𝟙 _) z J).val :=
    fun z J hJ => by rw [hv'' z J, hv₁ z J hJ, GlobalTheory.UT.CoefBasic.cst_eq]
  have hvw : ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w (𝟙 _) z J).val = cstH (R := V) z c₀ * (val w'' (𝟙 _) z J).val :=
    fun z J hJ => by rw [hvs z J hJ, ← _root_.mul_assoc, ← map_mul, mul_inv_cancel₀ hc₀, map_one, _root_.one_mul]
  have hov'' := htr χ hχ g₀ hg₀ (g' + g₀) hadd w'' hw'' hvw
  have htor'' : ∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' + g₀) o ∧ o.IsZero := by
    obtain ⟨o, ho, hoz⟩ := htor
    refine ⟨0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (GlobalTheory.TorusExt.isZero_iff_eq _).2 rfl⟩
    rw [smul_add, ← (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho, (GlobalTheory.TorusExt.isZero_iff_eq _).1 hoz, zero_add, hg₀def,
      ← map_nsmul, ← ofMul_pow, hχ.1, ofMul_one, map_zero]
  obtain ⟨x₁, fr₁, th₁, w₀₁, s₁, G₁, W₁, hx₁, hfr₁, hth₁, hw₀₁, hs₁, hc₁, hT₁⟩ := hT
  obtain ⟨x₂, fr₂, th₂, w₀₂, s₂, G₂, W₂, hx₂, hfr₂, hth₂, hw₀₂, hs₂, hc₂, hT₂⟩ := hT'
  obtain ⟨ht₁, hW₁, ho₁⟩ := hc₁ c
  obtain ⟨ht₂, hW₂, ho₂⟩ := hc₂ c'
  rw [hc] at ho₁
  rw [hc'] at ho₂
  have u₁ := huniq I X₁ z₁ act V ev Y t δ 𝔪 a x x₁ fr fr₁ th th₁ w₀ w₀₁ s s₁ g' (G₁ c) w (W₁ c)
    hx hfr hth hw₀ hs htor hw hov hx₁ hfr₁ hth₁ hw₀₁ hs₁ ht₁ hW₁ ho₁ (𝔪.e₈ mu)
  have u₂ := huniq I X₁ z₁ act V ev Y t δ 𝔪 (a + τ) x x₂ fr fr₂ th th₂ w₀ w₀₂ s s₂ (g' + g₀) (G₂ c') w'' (W₂ c')
    hx hfr hth hw₀ hs htor'' hw'' hov'' hx₂ hfr₂ hth₂ hw₀₂ hs₂ ht₂ hW₂ ho₂ (𝔪.e₈ mu)
  have co := GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd hw hvs s (𝔪.e₈ mu)
  have hθ := GlobalTheory.GSep.GMem.yK_th_ne_zero I X₁ z₁ act V ev Y t δ 𝔪 x₀ hdiv
  apply mul_right_cancel₀ hθ
  rw [_root_.mul_assoc, _root_.mul_assoc, hT₁ mu c, hT₂ mu c', ← u₁, ← u₂, co]
  field_simp

end GlobalTheory.GSep.TransTerms
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationExponentOfFrameExponentStatement

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
open GlobalTheory.UT.CoefBasic


theorem _root_.GlobalTheory.T.translationExponent_of_frameExponent : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ), ∀ a ∈ X₁.S.HH X₁.M z₁, ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ e : ℕ, GlobalTheory.GSep.TransTerms.FrExp 𝔪 a τ e → GlobalTheory.GSep.TransTerms.TransExp 𝔪 x₀ a τ e := by
  first | exact @GlobalTheory.GSep.TransTerms.transExp_of_frExp | exact GlobalTheory.GSep.TransTerms.transExp_of_frExp | (intros; apply GlobalTheory.GSep.TransTerms.transExp_of_frExp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorusTranslationExponentAffine

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
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep.TransTerms

theorem trans_exp_affine : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ F1 F2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.TransExp 𝔪1 x₀ a τ (F1 a)) ∧ (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.TransExp 𝔪2 x₀ a τ (F2 a)) ∧ ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((F1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((F2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  classical
  intro I X₁ z₁ act x₀ hd V1 _ _ _ ev1 Y1 _ t1 δ1 𝔪1 V2 _ _ _ ev2 Y2 _ t2 δ2 𝔪2 τ hτ
  let E1 : X₁.S.Gam → ℕ := fun a => if ha : a ∈ X₁.S.HH X₁.M z₁ then
    Classical.choose (GlobalTheory.T.thetaMember_exists_frame_exponent I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 a ha τ hτ) else 0
  let E2 : X₁.S.Gam → ℕ := fun a => if ha : a ∈ X₁.S.HH X₁.M z₁ then
    Classical.choose (GlobalTheory.T.thetaMember_exists_frame_exponent I X₁ z₁ act x₀ hd V2 ev2 Y2 t2 δ2 𝔪2 a ha τ hτ) else 0
  have h1 : ∀ a ∈ X₁.S.HH X₁.M z₁, FrExp 𝔪1 a τ (E1 a) := fun a ha => by
    simp only [E1, dif_pos ha]
    exact Classical.choose_spec (GlobalTheory.T.thetaMember_exists_frame_exponent I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 a ha τ hτ)
  have h2 : ∀ a ∈ X₁.S.HH X₁.M z₁, FrExp 𝔪2 a τ (E2 a) := fun a ha => by
    simp only [E2, dif_pos ha]
    exact Classical.choose_spec (GlobalTheory.T.thetaMember_exists_frame_exponent I X₁ z₁ act x₀ hd V2 ev2 Y2 t2 δ2 𝔪2 a ha τ hτ)
  exact ⟨E1, E2, fun a ha => GlobalTheory.T.translationExponent_of_frameExponent I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 a ha τ hτ _ (h1 a ha),
    fun a ha => GlobalTheory.T.translationExponent_of_frameExponent I X₁ z₁ act x₀ hd V2 ev2 Y2 t2 δ2 𝔪2 a ha τ hτ _ (h2 a ha),
    GlobalTheory.T.frameExponents_affine_two_members I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 V2 ev2 Y2 t2 δ2 𝔪2 τ hτ E1 E2 h1 h2⟩

end GlobalTheory.GSep.TransTerms
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorusTranslationExponentAffineStatement

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


theorem _root_.GlobalTheory.T.thetaMember_torus_translation_exponent_affine : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ F1 F2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.TransExp 𝔪1 x₀ a τ (F1 a)) ∧ (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.TransExp 𝔪2 x₀ a τ (F2 a)) ∧ ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((F1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((F2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  first | exact @GlobalTheory.GSep.TransTerms.trans_exp_affine | exact GlobalTheory.GSep.TransTerms.trans_exp_affine | (intros; apply GlobalTheory.GSep.TransTerms.trans_exp_affine <;> assumption)
end
end
