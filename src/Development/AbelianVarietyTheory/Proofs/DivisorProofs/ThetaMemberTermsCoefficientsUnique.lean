module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantNeZeroUniformisedMember
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EigenEquationTranslationKernelGenericFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIndepCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorsionFrameUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationGenericFramesScaleByConstantStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionEqOfValuesAtLabelTorsion

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

noncomputable section
namespace GlobalTheory.GSep.GMem

theorem sec_eq_of_valAt : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th th₂ : SecA 𝔪.A (FractionRing V) 1),
  (∀ a, (fr a).IsGen) → (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) →
  (∀ a, ValAt th₂ (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → th₂ = th := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 x fr th th₂ _ h₁ h₂
  obtain ⟨b, hb⟩ := GlobalTheory.GSep.GMem.exists_th_ne_zero I X₁ z₁ act V ev Y t δ 𝔪
  set y := 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ with hy
  have ht : (show GlobalTheory.TorsionExt.AbSec 𝔪.A (FractionRing V) 1 from th) ≠ 0 := by
    intro h0
    have hz : ValAt (show GlobalTheory.TorsionExt.AbSec 𝔪.A (FractionRing V) 1 from th) (x b) (fr b) 0 := by
      rw [h0]; exact GlobalTheory.TermsMove.valAt_zero (x b) (fr b)
    exact hb (GlobalTheory.TermsMove.valAt_unique (h₁ b) hz)
  obtain ⟨c, hc⟩ := GlobalTheory.TermsMove.exists_eq_smul ht (show GlobalTheory.TorsionExt.AbSec 𝔪.A (FractionRing V) 1 from th₂)
  have hz0 : ValAt (0 : GlobalTheory.TorsionExt.AbSec 𝔪.A (FractionRing V) 1) (x b) (fr b) 0 :=
    GlobalTheory.TermsMove.valAt_zero (x b) (fr b)
  have hl := GlobalTheory.TermsMove.valAt_lin (h₁ b) hz0 c
  rw [add_zero, add_zero, ← hc] at hl
  have e := GlobalTheory.TermsMove.valAt_unique (h₂ b) hl
  have c1 : c = 1 := by
    have : (c - 1) * y = 0 := by rw [sub_mul, ← e]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hb
  rw [c1, one_smul] at hc
  exact hc

end GlobalTheory.GSep.GMem
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionEqOfValuesAtLabelTorsionStatement

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


theorem _root_.GlobalTheory.T.section_eq_of_values_at_label_torsion : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th th₂ : SecA 𝔪.A (FractionRing V) 1),
  (∀ a, (fr a).IsGen) → (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) →
  (∀ a, ValAt th₂ (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → th₂ = th := by
  first | exact @GlobalTheory.GSep.GMem.sec_eq_of_valAt | exact GlobalTheory.GSep.GMem.sec_eq_of_valAt | (intros; apply GlobalTheory.GSep.GMem.sec_eq_of_valAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExpansionTermsEq

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

namespace GlobalTheory.GSep.ExpUnique

theorem expandsF_unique {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I) {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
    (w : W0 U) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s s₂ : Fam D.toPre F k)
    (h : U.ExpandsF F k w t s) (h₂ : U.ExpandsF F k w t s₂) : s = s₂ := by
  obtain ⟨σ, hσ, hG⟩ := h
  obtain ⟨σ₂, hσ₂, hG₂⟩ := h₂
  have hf : ∀ j, σ.f j = σ₂.f j := by
    refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.sec_ext_val U.LG.isLB (fun y J hJ => ?_)
    choose J₁ hJ₁ using fun χ : _ ⟶ A.A.left => exists_chart A.isLB (χ y)
    have e₁ := GlobalTheory.Jets.sval_of_isoRelM hσ (𝟙 _) y hJ hJ₁
    have e₂ := GlobalTheory.Jets.sval_of_isoRelM hσ₂ (𝟙 _) y hJ hJ₁
    exact e₁.trans e₂.symm
  obtain rfl : σ = σ₂ := by
    rcases σ with ⟨a, _⟩
    rcases σ₂ with ⟨b, _⟩
    obtain rfl : a = b := funext hf
    rfl
  exact GlobalTheory.expandsG_unique R I hR D A G U k F σ s s₂ hG hG₂

end GlobalTheory.GSep.ExpUnique

theorem GlobalTheory.GSep.ExpUnique.coef_eq_of_expandsF : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (k : ℕ) (th : SecA 𝔪.A (FractionRing V) k) (s s₂ : Fam 𝔪.D.toPre (FractionRing V) k),
  w₀.IsGen → 1 ≤ k → 𝔪.U.ExpandsF (FractionRing V) k w₀ th s → 𝔪.U.ExpandsF (FractionRing V) k w₀ th s₂ →
  ∀ (g : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) k g.b), w.IsGen → ∀ χ, coef s₂ g w χ = coef s g w χ := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 w₀ k th s s₂ _ _ hs hs₂ g w _ χ
  rw [GlobalTheory.GSep.ExpUnique.expandsF_unique (GlobalTheory.TorRef.admissibleBase_of_completeNormalLocalCharZero 𝔪.cn) 𝔪.U.toUnifPre (FractionRing V) k w₀ th
    s s₂ hs hs₂]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExpansionTermsEqStatement

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


theorem _root_.GlobalTheory.T.thetaMember_expansion_terms_eq : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (k : ℕ) (th : SecA 𝔪.A (FractionRing V) k) (s s₂ : Fam 𝔪.D.toPre (FractionRing V) k),
  w₀.IsGen → 1 ≤ k → 𝔪.U.ExpandsF (FractionRing V) k w₀ th s → 𝔪.U.ExpandsF (FractionRing V) k w₀ th s₂ →
  ∀ (g : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) k g.b), w.IsGen → ∀ χ, coef s₂ g w χ = coef s g w χ := by
  first | exact @GlobalTheory.GSep.ExpUnique.coef_eq_of_expandsF | exact GlobalTheory.GSep.ExpUnique.coef_eq_of_expandsF | (intros; apply GlobalTheory.GSep.ExpUnique.coef_eq_of_expandsF <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorsionPointsEqSameValues

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

namespace GlobalTheory.GSep.TorsUniq

theorem same_point : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (fr : FrAt x)
  (g g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
  w₀.IsGen → fr.IsGen →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g w x fr →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) → w₂.IsGen → 𝔪.Over' w₀ g₂ w₂ x fr →
  g₂.b = g.b ∧ ∀ χ z J, Good 𝔪.D.toPre.P.L z J → val (g₂.s χ) (𝟙 _) z J = val (g.s χ) (𝟙 _) z J := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 w₀ x fr g g₂ w w₂ hw₀ hfr hg hw ho hg₂ hw₂ ho₂
  have hn : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (lt_of_lt_of_le two_pos X₁.S.N_ge)
  obtain ⟨e, -⟩ := GlobalTheory.Poinc.Sep.LiesUniq.eq_of_liesOver V 𝔪.cn 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ _ hn g g₂ w w₂ x fr hg hg₂ hw hw₂ hfr ho ho₂
  subst e
  exact ⟨rfl, fun _ _ _ _ => rfl⟩

end GlobalTheory.GSep.TorsUniq
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorsionPointsEqSameValuesStatement

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


theorem _root_.GlobalTheory.T.thetaMember_torsion_points_eq_same_values : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (fr : FrAt x)
  (g g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
  w₀.IsGen → fr.IsGen →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g w x fr →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) → w₂.IsGen → 𝔪.Over' w₀ g₂ w₂ x fr →
  g₂.b = g.b ∧ ∀ χ z J, Good 𝔪.D.toPre.P.L z J → val (g₂.s χ) (𝟙 _) z J = val (g.s χ) (𝟙 _) z J := by
  first | exact @GlobalTheory.GSep.TorsUniq.same_point | exact GlobalTheory.GSep.TorsUniq.same_point | (intros; apply GlobalTheory.GSep.TorsUniq.same_point <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermsCoefficientsUnique

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

noncomputable section
namespace GlobalTheory.GSep.TermsUniq

section Reformulated
variable {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {V : Type} [CommRing V] [IsDomain V]
  [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {Y : Type} [AddCommGroup Y] {t : Y → V} {δ : I → Y → Y}

theorem hom_eq_of_comp (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) {u v : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A}
    (h : u.left ≫ 𝔪.φ = v.left ≫ 𝔪.φ) : u = v :=
  Over.OverMorphism.ext (𝔪.cart.1.hom_ext h ((Over.w u).trans (Over.w v).symm))

theorem frame_val_eq (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) {x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A}
    {a : X₁.S.Gam} (fr fr₂ : FrAt x)
    (h : ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl x.left z (J (x.left ≫ 𝔪.φ)) (J' x.left) * val fr (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J)
    (h₂ : ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl x.left z (J (x.left ≫ 𝔪.φ)) (J' x.left) * val fr₂ (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) :
    ∀ z J', Good 𝔪.A.L z J' → val fr₂ (𝟙 _) z J' = val fr (𝟙 _) z J' := by
  intro z J' hJ'
  obtain ⟨J, hJ⟩ := exists_good' X₁.ρ.P.isLB z
  exact mul_left_cancel ((h₂ z J J' hJ hJ').trans (h z J J' hJ hJ').symm)
end Reformulated

section Gen
variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem valAt_congr {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {k : ℕ} {th : SecA A F k}
    {x : TFK (R := R) F ⟶ A.A} {e e' : FrAt x} {c : F} (h : ValAt th x e c)
    (he : ∀ z J, Good A.L z J → val e' (𝟙 _) z J = val e (𝟙 _) z J) : ValAt th x e' c := by
  intro z J hJ
  rw [h z J hJ]
  congr 2
  have := he z J hJ
  simp only [Geo.Tor.val, powFrame] at this ⊢
  exact (map_zpow _ _ _).trans ((congrArg (· ^ (k : ℤ)) this.symm).trans (map_zpow _ _ _).symm)

variable {D : DegPre R}

theorem coef_congr {k : ℕ} {g g₂ : GtPtF D F} {w : Frm D F k g.b} {w₂ : Frm D F k g₂.b} (hw : w.IsGen)
    (hb : g₂.b = g.b) (hs : ∀ χ z J, Good D.P.L z J → val (g₂.s χ) (𝟙 _) z J = val (g.s χ) (𝟙 _) z J)
    (hv : ∀ z J, Good D.P.L z J → val w₂ (𝟙 _) z J = val w (𝟙 _) z J) (s : Fam D F k) (χ : D.X) :
    coef s g₂ w₂ χ = coef s g w χ := by
  refine coef_eq fun z J hJ => ?_
  have a := isCoef_coef g hw χ s z J hJ
  have e : lift (𝟙 (TF (R := R) F)) g₂.b = lift (𝟙 (TF (R := R) F)) g.b := by rw [hb]
  rw [hs χ z J hJ, hv z J hJ, e]
  exact a

theorem coef_smul {k : ℕ} {g : GtPtF D F} {w : Frm D F k g.b} (hw : w.IsGen) (u : F) (s : Fam D F k) (χ : D.X) :
    coef (u • s) g w χ = u * coef s g w χ := by
  have hlin := ((coef_basic R D F k g).2.2 w hw).2.1
  have e0 := hlin 0 0 1 χ
  simp only [_root_.one_smul, _root_.add_zero, _root_.one_mul] at e0
  have h0 : coef (0 : Fam D F k) g w χ = 0 := by linear_combination (-1 : F) * e0
  have e := hlin s 0 u χ
  rw [_root_.add_zero, h0, _root_.add_zero] at e
  exact e
end Gen

section Transport
variable {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {V : Type} [CommRing V] [IsDomain V]
  [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {Y : Type} [AddCommGroup Y] {t : Y → V} {δ : I → Y → Y}

theorem over_transport (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) {w₀ w₀₂ : W0 𝔪.U.toUnifPre}
    {g : GtPtF 𝔪.D.toPre (FractionRing V)} {w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g.b}
    {x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A} {fr fr₂ : FrAt x} {u : FractionRing V}
    (hO : 𝔪.Over' w₀₂ g w x fr₂) (hw : w.IsGen)
    (hD : ∀ (k : ℕ) (th : SecA 𝔪.A (FractionRing V) k) (s : Fam 𝔪.D.toPre (FractionRing V) k),
      𝔪.U.ExpandsF (FractionRing V) k w₀ th s → 𝔪.U.ExpandsF (FractionRing V) k w₀₂ th (u ^ k • s))
    (hfr : ∀ z J, Good 𝔪.A.L z J → val fr₂ (𝟙 _) z J = val fr (𝟙 _) z J)
    (hv : ∀ z J, Good 𝔪.D.toPre.P.L z J →
      (val w' (𝟙 _) z J).val = cst (FractionRing V) z u * (val w (𝟙 _) z J).val) :
    𝔪.Over' w₀ g w' x fr := by
  intro k hk wk' hwk' hwk'g th s' v hexp hval
  obtain ⟨wk, hwkg, hwk⟩ := TorsionValue.exists_frm_pow w hw k
  have H := hO k hk wk hwk hwkg th (u ^ k • s') v (hD k th s' hexp) (valAt_congr hval fun z J hJ => hfr z J hJ)
  have hcv : ∀ z J, Good 𝔪.D.toPre.P.L z J →
      (val wk' (𝟙 _) z J).val = cst (FractionRing V) z (u ^ k) * (val wk (𝟙 _) z J).val := by
    intro z J hJ
    rw [hwk' z J hJ, hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hv z J hJ, mul_pow, cst_eq, cst_eq,
      map_pow]
  have e : coef (u ^ k • s') g wk = coef s' g wk' := funext fun χ => by
    rw [coef_smul hwkg, TorsionValue.coef_scale hwkg hcv s' χ]
  rw [e] at H
  exact H
end Transport

theorem coef_eq : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (b : X₁.S.Gam)
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
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 b x x₂ fr fr₂ th th₂ w₀ w₀₂ s s₂ g' g₂ w w₂ hx hfr hth hw₀ hs hg hw hO hx₂ hfr₂
    hth₂ hw₀₂ hs₂ hg₂ hw₂ hO₂ χ
  obtain rfl : x = x₂ := (funext fun a => hom_eq_of_comp 𝔪 ((hx₂ a).trans (hx a).symm)).symm
  have efr : ∀ a z J', Good 𝔪.A.L z J' → val (fr₂ a) (𝟙 _) z J' = val (fr a) (𝟙 _) z J' :=
    fun a => frame_val_eq 𝔪 (a := a) (fr a) (fr₂ a) (hfr a).2 (hfr₂ a).2
  have hth₂' : ∀ a, ValAt th₂ (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) :=
    fun a => valAt_congr (hth₂ a) fun z J hJ => (efr a z J hJ).symm
  obtain rfl : th = th₂ := Eq.symm <| GlobalTheory.T.section_eq_of_values_at_label_torsion I X₁ z₁ act V ev Y t δ 𝔪 x fr th th₂ (fun a => (hfr a).1) hth hth₂'
  obtain ⟨u, hu, hD⟩ := GlobalTheory.T.uniformisation_generic_frames_scale_by_constant I X₁ z₁ act V ev Y t δ 𝔪 w₀ w₀₂ hw₀ hw₀₂
  obtain ⟨w₂', hw₂'g, hv₂'⟩ := TorsionValue.exists_frm_scale w₂ hw₂ hu
  have hO₂' : 𝔪.Over' w₀ g₂ w₂' (x b) (fr b) := over_transport 𝔪 hO₂ hw₂ hD (efr b) hv₂'
  obtain ⟨hb, hsv⟩ := GlobalTheory.T.thetaMember_torsion_points_eq_same_values I X₁ z₁ act V ev Y t δ 𝔪 w₀ (x b) (fr b) g' g₂ w w₂' hw₀ (hfr b).1 hg hw hO hg₂ hw₂'g hO₂'
  have hwv := GlobalTheory.T.thetaMember_torsion_frame_unique I X₁ z₁ act V ev Y t δ 𝔪 w₀ (x b) (fr b) g' g₂ w w₂' hw₀ (hfr b).1 hg hw hO hg₂ hw₂'g hO₂' hb hsv
  have e1 : coef s g₂ w₂' χ = coef s g' w χ := coef_congr hw hb hsv hwv s χ
  have e2 : coef s₂ g₂ w₂ χ = coef (u ^ 1 • s) g₂ w₂ χ :=
    GlobalTheory.T.thetaMember_expansion_terms_eq I X₁ z₁ act V ev Y t δ 𝔪 w₀₂ 1 th (u ^ 1 • s) s₂ hw₀₂ le_rfl (hD 1 th s hs) hs₂ g₂ w₂ hw₂ χ
  rw [e2, pow_one, coef_smul hw₂, ← TorsionValue.coef_scale hw₂ hv₂' s χ, e1]

end GlobalTheory.GSep.TermsUniq
end
end
end
