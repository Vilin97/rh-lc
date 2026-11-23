module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionFieldStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfCommonGenericFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelAutActsOnRaisedModelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMonoStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushforwardPolarisationBundleInvertibleOnModelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbedStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMapStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalModelAboveFiniteCoverStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelFiniteOverModuliModelDescends
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OpenImmersionCompStructureEqGeneric
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingOfUnitBall

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelLevelOneDescends

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.RaisedDescends

theorem map_nsmul_eq_pow {A Q : Type*} [AddMonoid A] [Group Q] (f : A → Q) (hf : ∀ a c, f (a + c) = f a * f c)
    (m : ℕ) (a : A) : f (m • a) = f a ^ m := by
  induction m with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [zero_nsmul, pow_zero]
    exact left_eq_mul.mp h
  | succ m ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem mono_spMap_of_isDedFrac {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) :
    Mono (spMap β) := by
  letI := β.toAlgebra
  have := h.2.2
  have : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O) (S := F)
  infer_instance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isDedFrac_of_isInc (l : Level H) (S A : ℕ) (hS : 0 < S) (hA : l.A = A) (h1 : A = 1) (β : RZ H S A →+* KA l)
    (hβ : IsInc (RZ H S A).subtype (KA l).val.toRingHom β) : IsDedFrac β := by
  subst hA
  exact (GlobalTheory.T.cmModelCoefficientSubring_dedekind_compatible_embedding E H l S 0 hS (by rw [h1, pow_zero])).2.2 β hβ

theorem Cpt_j_over {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F}
    (C : Cpt c t β) : C.j ≫ C.s = c ≫ spMap β := by
  rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

theorem levComp_comp {D : Datum H} {l l' : Level H} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    {b : Base l B} {b' : Base l' B'} {b'' : Base l' B''} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}
    {s'' : S'' ⟶ Sp B''} {o'' : Obj D l' b'' s''} {o' : Obj D l' b' s'} {o : Obj D l b s} {r : S' ⟶ S} {g : S'' ⟶ S'}
    (m : ObjMap o'' o' g) {ν : SABMap o'.t o.t r} (h : LevComp o' o r ν) (ν' : SABMap o''.t o.t (g ≫ r))
    (e : ν'.φ = m.toSABMap.φ ≫ ν.φ) : LevComp o'' o (g ≫ r) ν' := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · have h1 := h.1 a
    rw [← map_nsmul_eq_pow _ o'.eta_add] at h1
    rw [← map_nsmul_eq_pow _ o''.eta_add, e, ← Category.assoc, m.eta, Category.assoc, h1, Category.assoc]
  · have h1 := h.2 a
    rw [← map_nsmul_eq_pow _ o'.etaA_add] at h1
    rw [← map_nsmul_eq_pow _ o''.etaA_add, e, ← Category.assoc, m.etaA, Category.assoc, h1, Category.assoc]

theorem descends_of_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), 0 < n → l₀.Dvd l → l.A = 1 → IsDedFrac β → Raises B Y → Y.Descends := by
  intro h1 h2 h3 E _ _ _ H D Xo n N T hN l₀ B l c O _ β Y hn hd hA hβ hR
  obtain ⟨b, r, ν, hb, hlev, ⟨a⟩⟩ := hR
  obtain ⟨k, r₁, ν₁, hr₁, hk, hlev₁, hfin, -⟩ := GlobalTheory.T.exists_finite_etale_surjective_levelMap E H D Xo hN l₀ l hd
  have hS : 0 < n * l₀.M := Nat.mul_pos hn (lt_of_lt_of_le (by norm_num) l₀.three_le)
  have hD₀ : IsDedFrac B.β := isDedFrac_of_isInc l₀ _ 1 hS B.A_one rfl _ B.β_inc
  have hD₁ : IsDedFrac (k.comp B.β) :=
    isDedFrac_of_isInc l _ 1 hS hA rfl _ fun x => (hk (B.β x)).trans (B.β_inc x)
  have hsm : Smooth (Xo l).s := by
    have := (Xo l).smooth
    exact SmoothOfRelativeDimension.smooth D.dim _
  obtain ⟨C', ⟨a'⟩⟩ := GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ _ _ B.β _ _ _ (Xo l).s (Xo l).univ.t (k.comp B.β) B.C (RingHom.id _) k r₁ hr₁ ν₁
    hD₀ hD₁ (RingHom.comp_id _)
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm).2.1 hfin
  have hbβ : β.comp b = (IntermediateField.inclusion c.le).toRingHom.comp (k.comp B.β) := by
    refine RingHom.ext fun x => Subtype.ext ?_
    exact (hb x).trans ((hk (B.β x)).trans (B.β_inc x)).symm
  have hred : IsReduced ((Xo l).XF c) :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ (pullback.snd _ _) inferInstance).1
  obtain ⟨ν₂, hν₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν₁ Y.m0.toSABMap
  have hover : r ≫ (Xo l₀).s = (pullback.fst _ _ ≫ r₁) ≫ (Xo l₀).s := by
    have := mono_spMap_of_isDedFrac hD₀
    rw [← cancel_mono (spMap B.β), Category.assoc, ← Cpt_j_over B.C, ← Category.assoc, ← a.j_comm, Category.assoc,
      a.π_over, ← Category.assoc, Cpt_j_over, Category.assoc, ← spMap_comp, hbβ, spMap_comp, spMap_comp,
      Category.assoc, Category.assoc, reassoc_of% hr₁, pullback.condition_assoc]
  obtain ⟨e₁, e₂⟩ := GlobalTheory.LevUniq.map_to_univ_unique h1 h2 h3 E H D l₀ l (Xo l₀) _ _ _ _ Y.oF r _ ν ν₂ hred hover hlev
    (levComp_comp Y.m0 hlev₁ ν₂ hν₂)
  obtain ⟨h, mu', hh, -, -, hj, hφ, hf⟩ := GlobalTheory.Models.Cpt.Above.exists_lift E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    B.C C' (ofModel Y) (RingHom.id _) b (IntermediateField.inclusion c.le).toRingHom r₁ ν₁ a' (pullback.fst _ _)
    Y.m0.toSABMap a.π a.mu a.π_over hβ hbβ pullback.condition
    (by rw [a.j_comm, e₁, Category.assoc]) (by rw [a.φ_comm, e₂, hν₂, Category.assoc])
  exact GlobalTheory.descends_of_above E H D l (Xo l) c O β Y _ (k.comp B.β) C' b ⟨h, hh, hf a.fin, mu', hj, hφ⟩ hD₁ hβ hbβ

end GlobalTheory.RaisedDescends

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelLevelOneDescendsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.raised_model_level_one_descends : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), 0 < n → l₀.Dvd l → l.A = 1 → IsDedFrac β → Raises B Y → Y.Descends := by
  first | exact @GlobalTheory.RaisedDescends.descends_of_raises | exact GlobalTheory.RaisedDescends.descends_of_raises | (intros; apply GlobalTheory.RaisedDescends.descends_of_raises <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelStructureConditionsAndSplitFibres

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem System.levelStructureConditions_and_splitFibres : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW (i : Idx H p), (S.Y p W hp hW i).LevelStructureConditions p ∧ (S.Y p W hp hW i).SplitFibres := by
  intro hext L1 L2 L3 E _ _ _ H D Xo hpq hlev S p W hp hW i
  obtain ⟨l₀, h, hR⟩ := S.raises p W hp hW i
  have hdvd : l₀.Dvd i.l := ((GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp).2.1 i.l l₀ h).1
  obtain ⟨hded, hunit, -⟩ := (GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H i.l i.c).2.2.2 p W hp hW
  have hgood : Good (S.Y p W hp hW i).t := by
    obtain ⟨b, r, ν, -, -, ⟨A⟩⟩ := hR
    exact good_pullback L3.gtBaseChange E H _ _ _ _ A.π A.mu (S.B (S.ch p) l₀ h.1).good
  refine ⟨⟨?_, fun hA => ?_, ?_, ?_, ?_, ?_⟩, hgood.2.1⟩
  · exact GlobalTheory.T.levelAut_acts_on_raised_model L1 L2 L3 E H D Xo _ _ _ hpq l₀ _ i.l i.c _ _ _ hdvd hded hR
  · exact GlobalTheory.T.raised_model_level_one_descends L1 L2 L3 E H D Xo _ _ _ hlev l₀ _ i.l i.c _ _ _ (S.aux _).1.pos hdvd hA hded hR
  · exact GlobalTheory.T.pushforward_polarisationBundle_invertible_on_model L1 L2 L3 E H D i.l _ _ _ _ _ _ (S.Y p W hp hW i).oF _ _ (ofModel (S.Y p W hp hW i)) hded
      hgood.2.2
  · obtain ⟨U, hU, hσ⟩ := GlobalTheory.torsion_section_extends_abLocus E H D i.l _ i.c _ _ (S.Y p W hp hW i) hded hgood.1
    exact ⟨U, hU, fun a n hn => ⟨hσ _ n (hunit n hn), hσ _ n (hunit n hn)⟩⟩
  · intro V K _ _ _ _ _ _ _
    exact GlobalTheory.goodRedExt_of_isDiscreteValuationRing hext E H D i.l _ i.c _ _ _ V K
  · intro V C _ _ _ _ _ _ _ hV _
    exact GlobalTheory.GoodRedUnitBall.goodRedExt_unitBall hext E H D Xo _ _ _ l₀ _ i.l i.c _ _ _ hR V C hV

end GlobalTheory.Models
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelStructureConditionsAndSplitFibresStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.localModel_oneModel_and_splitFibres : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW (i : Idx H p), (S.Y p W hp hW i).LevelStructureConditions p ∧ (S.Y p W hp hW i).SplitFibres := by
  first | exact @GlobalTheory.Models.System.levelStructureConditions_and_splitFibres | exact GlobalTheory.Models.System.levelStructureConditions_and_splitFibres | (intros; apply GlobalTheory.Models.System.levelStructureConditions_and_splitFibres <;> assumption)
end
end
