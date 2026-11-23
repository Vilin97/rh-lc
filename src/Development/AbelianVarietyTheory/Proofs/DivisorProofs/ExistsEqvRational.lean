module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantBijectionsFamiliesSectionsDifferBySca
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonScalingDescendsToFractionFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecTw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjugateEquivariantBijectionTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueFieldExtensionStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantBijectionsFamiliesSectionsDifferByScaStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.equivariant_bijections_families_sections_differ_by_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ lab E E', Eqv D.toPre A F N lab E → Eqv D.toPre A F N lab E' → ∃ c : Fˣ, ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  first | exact @GlobalTheory.Mum.eqv_eq_smul | exact GlobalTheory.Mum.eqv_eq_smul | (intros; apply GlobalTheory.Mum.eqv_eq_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjugateEquivariantBijectionTwistStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_galoisConjugate_equivariantBijection_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E, Eqv D.toPre A (Kb R) N lab E → (∀ τ : Kb R →ₐ[FractionRing R] Kb R, LabExt τ lab lab) → ∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ E', Eqv D.toPre A (Kb R) N lab E' ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre N) s, F₀.Over s → SecTw σ (E s) (E' s) := by
  first | exact @GlobalTheory.Mum.exists_eqv_conj | exact GlobalTheory.Mum.exists_eqv_conj | (intros; apply GlobalTheory.Mum.exists_eqv_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilySectionEquivarianceSmulOfNeZero

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum.ScaleEqv

theorem eqv_scale : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) lab E, Eqv D A F N lab E → ∀ c : Fˣ, ∃ E', Eqv D A F N lab E' ∧ ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  intro R _ _ D A F _ _ N lab E h c
  let gg : F →+* Γ((TFK (R := R) F ⊗ A.A).left, ⊤) :=
    (fst (TFK (R := R) F) A.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  have hgg : ∀ u : F, gg u = (fst (TFK (R := R) F) A.A).left.appTop.hom (fnF F u) := fun _ => rfl
  have inv1 : ∀ (W : (TFK (R := R) F ⊗ A.A).left.Opens) (u : Fˣ), resTop W (gg u.val) * resTop W (gg (u⁻¹).val) = 1 := by
    intro W u
    simp only [resTop]
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  let S : F → SecK A.L (snd (TFK (R := R) F) A.A).left N → SecK A.L (snd (TFK (R := R) F) A.A).left N :=
    fun u t => DVR.SecOps.secScale (gg u) t
  have Sf : ∀ u t j, (S u t).f j = resTop _ (gg u) * t.f j := fun _ _ _ => rfl
  have SS : ∀ (u : Fˣ) t, S u.val (S (u⁻¹).val t) = t := by
    intro u t
    apply DVR.SecOps.sec_ext
    intro j
    rw [Sf, Sf, ← _root_.mul_assoc, inv1, _root_.one_mul]
  have SS' : ∀ (u : Fˣ) t, S (u⁻¹).val (S u.val t) = t := by
    intro u t
    have := SS u⁻¹ t
    rwa [inv_inv] at this
  refine ⟨fun s => S c.val (E s), ⟨?_, ?_, ?_, h.onto, h.frame, h.lift, ?_⟩, fun s j => rfl⟩
  · constructor
    · intro s t hst
      apply h.bij.1
      have := congrArg (S (c⁻¹).val) hst
      simpa only [SS'] using this
    · intro t
      obtain ⟨s, hs⟩ := h.bij.2 (S (c⁻¹).val t)
      exact ⟨s, by simp only [hs, SS]⟩
  · intro s s' s'' hs j
    simp only [Sf]
    rw [h.add s s' s'' hs j, mul_add]
  · intro u s s' hs j
    simp only [Sf]
    rw [h.smul u s s' hs j, mul_left_comm]
  · intro p w θ s s' hw hθ hph j
    have key := h.act p w θ s s' hw hθ hph j
    have e : (translT A.A θ.pt).left ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R) F) A.A).left := by
      rw [← Over.comp_left, translT, lift_fst]
    have hψ : ∀ (W : (TFK (R := R) F ⊗ A.A).left.Opens),
        ((translT A.A θ.pt).left.app W).hom (resTop W (gg c.val)) =
          resTop ((translT A.A θ.pt).left ⁻¹ᵁ W) (gg c.val) := by
      intro W
      simp only [resTop]
      rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
      congr 1
      rw [hgg]
      have hT : ((translT A.A θ.pt).left.appTop).hom (((fst (TFK (R := R) F) A.A).left.appTop).hom (fnF F c.val)) =
          ((fst (TFK (R := R) F) A.A).left.appTop).hom (fnF F c.val) := by
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e]
      exact hT
    erw [Sf, Sf]
    erw [map_mul, map_mul, map_mul, hψ, key, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res, mul_left_comm]

end GlobalTheory.Mum.ScaleEqv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilySectionEquivarianceSmulOfNeZeroStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.thetaFamilySectionEquivariance_smul_of_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) lab E, Eqv D A F N lab E → ∀ c : Fˣ, ∃ E', Eqv D A F N lab E' ∧ ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  first | exact @GlobalTheory.Mum.ScaleEqv.eqv_scale | exact GlobalTheory.Mum.ScaleEqv.eqv_scale | (intros; apply GlobalTheory.Mum.ScaleEqv.eqv_scale <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqvRational

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_eqv_rational : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E, Eqv D.toPre A (Kb R) N lab E → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, LabExt σ lab lab) → ∃ (Φ : IntFam (maximalIdeal R) D.toPre N → H0 A.L N) (E₀ : _), Eqv D.toPre A (Kb R) N lab E₀ ∧ ∀ F₀ s, F₀.Over s → Agree A.L (E₀ s) (Φ F₀) := by
  intro R _ _ _ hB D A N hN lab E hE hlab
  have hc0 : CharZero R := hB.2
  choose E' hE' hT using fun σ => GlobalTheory.T.exists_galoisConjugate_equivariantBijection_twist R hB D A N hN lab E hE hlab σ
  choose c hc using fun σ => GlobalTheory.T.equivariant_bijections_families_sections_differ_by_scalar R (maximalIdeal R) D A (Kb R) N hN lab E (E' σ) hE (hE' σ)
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.exists_common_scaling_descends_to_fractionField R hB A N {q : IntFam (maximalIdeal R) D.toPre N × Fam D.toPre (Kb R) N // q.1.Over q.2}
    (fun i => E i.1.2) c (fun σ i => ⟨E' σ i.1.2, hT σ i.1.1 i.1.2 i.2, hc σ i.1.2⟩)
  obtain ⟨E₀, hE₀, hE₀f⟩ := GlobalTheory.T.thetaFamilySectionEquivariance_smul_of_ne_zero R D.toPre A (Kb R) N lab E hE c₀
  choose Φ hΦ using hc₀
  have hex := fun F₀ => GlobalTheory.T.existsUnique_fieldExtension R (maximalIdeal R) D.toPre N F₀ (Kb R)
  refine ⟨fun F₀ => Φ ⟨(F₀, (hex F₀).exists.choose), (hex F₀).exists.choose_spec⟩, E₀, hE₀, fun F₀ s hs => ?_⟩
  obtain rfl : (hex F₀).exists.choose = s := (hex F₀).unique (hex F₀).exists.choose_spec hs
  exact hΦ _ (E₀ _) (hE₀f _)

end GlobalTheory.Mum
end
end
