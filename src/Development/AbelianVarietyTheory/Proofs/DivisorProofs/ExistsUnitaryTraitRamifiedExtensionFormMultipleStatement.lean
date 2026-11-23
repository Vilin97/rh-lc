module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLatStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionMonoBase

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcExt

theorem exists_ramified_ext (T : CDVR) {Ω : Type} [Field Ω] [Algebra T.Fr Ω] [Algebra.IsAlgebraic T.Fr Ω] [IsAlgClosed Ω]
    (M : IntermediateField T.Fr Ω) [FiniteDimensional T.Fr M] (N : ℕ) (hN : 0 < N) (ϖ₀ : T.V) (h₀ : Irreducible ϖ₀) :
    ∃ (T' : CDVR) (g : T.V →+* T'.V) (κ : M →+* T'.Fr) (e : ℕ) (ϖ : T'.V),
      Function.Injective g ∧ IsLocalHom g ∧ Irreducible ϖ ∧
      (∀ v, κ (algebraMap T.Fr M (algebraMap T.V T.Fr v)) = algebraMap T'.V T'.Fr (g v)) ∧
      N ∣ e ∧ Associated (g ϖ₀) (ϖ ^ e) := by
  haveI : CharZero T.Fr := algebraRat.charZero _
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap T.Fr Ω (algebraMap T.V T.Fr ϖ₀)) hN
  let A := IntermediateField.adjoin T.Fr ({α} : Set Ω)
  have : FiniteDimensional T.Fr A := IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  let L : IntermediateField T.Fr Ω := M ⊔ A
  have : FiniteDimensional T.Fr L := inferInstance
  obtain ⟨W, _, _, _, _, _, _, _, hc, -, hinj, hloc, -, -⟩ := GlobalTheory.SS.exists_complete_dvr_finite_extension T.V T.Fr L
  have : CharZero W := charZero_of_injective_algebraMap hinj
  let T' : CDVR := { V := W }
  let ψ : L ≃+* FractionRing W := (FractionRing.algEquiv W L).symm.toRingEquiv
  have hψ : ∀ w : W, ψ (algebraMap W L w) = algebraMap W (FractionRing W) w := fun w =>
    (FractionRing.algEquiv W L).symm.commutes w
  let κ : M →+* FractionRing W := ψ.toRingHom.comp (IntermediateField.inclusion (le_sup_left : M ≤ L)).toRingHom
  have hκ : ∀ v, κ (algebraMap T.Fr M (algebraMap T.V T.Fr v)) = algebraMap W (FractionRing W) (algebraMap T.V W v) := by
    intro v
    have h1 : algebraMap T.Fr L (algebraMap T.V T.Fr v) = algebraMap W L (algebraMap T.V W v) :=
      (RingHom.congr_fun hc v).symm
    rw [← hψ, ← h1]
    rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hg0 : algebraMap T.V W ϖ₀ ≠ 0 := fun h => h₀.ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg0 hϖ
  have hαL : α ∈ L := (le_sup_right : A ≤ L) (IntermediateField.mem_adjoin_simple_self T.Fr α)
  let b : FractionRing W := ψ ⟨α, hαL⟩
  have hb : b ^ N = algebraMap W (FractionRing W) (algebraMap T.V W ϖ₀) := by
    have h1 : (⟨α, hαL⟩ : L) ^ N = algebraMap W L (algebraMap T.V W ϖ₀) := by
      apply Subtype.ext
      have h2 := RingHom.congr_fun hc ϖ₀
      refine hα.trans ?_
      exact (congrArg (L.val) h2.symm)
    rw [← hψ, ← h1, map_pow]
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow hN.ne'] at hb
    exact hg0 ((IsFractionRing.injective W (FractionRing W)) (by rw [← hb, map_zero]))
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := W) b
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [← hxy, map_zero, zero_div])
  obtain ⟨m, v₁, hv₁⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  obtain ⟨n, v₂, hv₂⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hW : x ^ N = algebraMap T.V W ϖ₀ * y ^ N := by
    apply IsFractionRing.injective W (FractionRing W)
    have hy' : algebraMap W (FractionRing W) y ≠ 0 := by
      simpa using hy0
    rw [map_pow, map_mul, map_pow, ← hb, ← hxy, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hy')]
  have he : m * N = e + n * N := by
    rw [hv₁, hv₂, hu, mul_pow, mul_pow, ← pow_mul, ← pow_mul] at hW
    have : ((v₁ ^ N : Wˣ) : W) * ϖ ^ (m * N) = ((u * v₂ ^ N : Wˣ) : W) * ϖ ^ (e + n * N) := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hW, pow_add]
      ring
    exact IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ _ _ _ _ this
  refine ⟨T', algebraMap T.V W, κ, e, ϖ, hinj, hloc, hϖ, hκ, ?_, ?_⟩
  · have : N ∣ e + n * N := ⟨m, by rw [← he, mul_comm]⟩
    exact (Nat.dvd_add_left (Dvd.intro_left n rfl)).1 this
  · exact ⟨u⁻¹, by
      show algebraMap T.V W ϖ₀ * ((u⁻¹ : Wˣ) : W) = ϖ ^ e
      rw [hu, mul_comm (u : W), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩

section Level

open GlobalTheory.TorusExt GlobalTheory.QkNumberField GlobalTheory.ArcPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end Level

section Level2

open GlobalTheory.TorusExt GlobalTheory.QkNumberField GlobalTheory.ArcPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}


end Level2
section Main

open GlobalTheory.TorusExt GlobalTheory.QkNumberField GlobalTheory.ArcPull


end Main

end GlobalTheory.ArcExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitRamifiedExtensionFormMultiple

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.UPoinc

theorem mumBase_of_cdvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] : GlobalTheory.Mum.Base V :=
  ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩

theorem uTrait_ramExt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (T : GlobalTheory.UPoinc.UTrait Xo c) (n : ℕ), 0 < n →
    ∃ (T₂ : GlobalTheory.UPoinc.UTrait Xo c) (g : T.V →+* T₂.V) (gK : FractionRing T.V →+* FractionRing T₂.V)
      (e : T.P.D.toPre.X ≃ₗ[𝓞 E] T₂.P.D.toPre.X) (q : ℕ), Function.Injective g ∧ IsLocalHom g ∧
      (∀ a, gK (algebraMap T.V _ a) = algebraMap T₂.V _ (g a)) ∧ T₂.y = spMap gK ≫ T.y ∧ 0 < q ∧
      ∀ a b, T₂.be (e a) (e b) = ((n * q : ℕ) : ℤ) * T.be a b := by
  intro E _ _ _ H Dw l Xo c T n hn
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  haveI : IsAdicComplete (maximalIdeal T.V) T.V := T.cdvr.2.1
  haveI : CharZero T.V := T.cdvr.2.2
  let T0 : Formalism.L2.Pj.CDVR := { V := T.V }
  obtain ⟨T₁, g₁, κ, e₁, ϖ₁, hg₁, hl₁, hϖ₁, hκ, hne₁, hass₁⟩ :=
    GlobalTheory.ArcExt.exists_ramified_ext T0 (Ω := AlgebraicClosure T0.Fr) ⊥ n hn T.ϖ T.irr
  let gK₁ : FractionRing T.V →+* FractionRing T₁.V :=
    κ.comp (algebraMap T0.Fr (⊥ : IntermediateField T0.Fr (AlgebraicClosure T0.Fr)))
  have hgK₁ : ∀ a, gK₁ (algebraMap T.V _ a) = algebraMap T₁.V _ (g₁ a) := hκ
  haveI : IsAdicComplete (maximalIdeal T₁.V) T₁.V := T₁.cpl
  have hB₁ : GlobalTheory.Mum.Base T₁.V := mumBase_of_cdvr T₁.V
  obtain ⟨T₂, f, fK, hf, hfl, -, hfK, hy⟩ :=
    GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c T₁.V hB₁ inferInstance (spMap gK₁ ≫ T.y)
  haveI : IsDiscreteValuationRing T₂.V := T₂.cdvr.1
  haveI : IsAdicComplete (maximalIdeal T₂.V) T₂.V := T₂.cdvr.2.1
  haveI : CharZero T₂.V := T₂.cdvr.2.2

  have hfϖ0 : f ϖ₁ ≠ 0 := fun h => hϖ₁.ne_zero (hf (by rw [h, map_zero]))
  obtain ⟨e₂, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfϖ0 T₂.irr
  have he₂ : 0 < e₂ := by
    rcases Nat.eq_zero_or_pos e₂ with h | h
    · exfalso
      rw [h, pow_zero, mul_one] at hu
      exact hϖ₁.not_isUnit ((isUnit_map_iff f ϖ₁).1 (hu ▸ u.isUnit))
    · exact h
  have he₁ : 0 < e₁ := by
    rcases Nat.eq_zero_or_pos e₁ with h | h
    · exfalso
      rw [h, pow_zero] at hass₁
      exact T.irr.not_isUnit ((isUnit_map_iff g₁ T.ϖ).1 (associated_one_iff_isUnit.1 hass₁))
    · exact h
  have hassf : Associated (f ϖ₁) (T₂.ϖ ^ e₂) := ⟨u⁻¹, by rw [hu, mul_comm (u : T₂.V), mul_assoc, Units.mul_inv, mul_one]⟩
  have hass : Associated ((f.comp g₁) T.ϖ) (T₂.ϖ ^ (e₁ * e₂)) := by
    have h1 : Associated (f (g₁ T.ϖ)) (f ϖ₁ ^ e₁) := by
      rw [← map_pow]; exact hass₁.map f
    rw [mul_comm, pow_mul]
    exact h1.trans (hassf.pow_pow)
  have hyc : spMap (fK.comp gK₁) ≫ T.y = spMap (RingHom.id (FractionRing T₂.V)) ≫ T₂.y := by
    have hid : spMap (RingHom.id (FractionRing T₂.V)) = 𝟙 _ := by
      show Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [hy, hid, Category.id_comp, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp]; rfl
  have hcomp : ∀ a, (fK.comp gK₁) (algebraMap T.V _ a) = algebraMap T₂.V _ ((f.comp g₁) a) := fun a => by
    simp only [RingHom.comp_apply]
    rw [hgK₁, hfK]
  obtain ⟨e, he⟩ := GlobalTheory.T.traitsOfModuliPoint_have_isomorphic_proportional_lattices E H Dw l Xo c T T₂ T₂.V (f.comp g₁) (RingHom.id T₂.V) (fK.comp gK₁)
    (RingHom.id _) (mumBase_of_cdvr T₂.V) inferInstance (hf.comp hg₁) Function.injective_id inferInstance
    inferInstance hcomp (fun _ => rfl) hyc T₂.ϖ (e₁ * e₂) 1 T₂.irr hass (by rw [pow_one]; rfl)
  obtain ⟨k, hk⟩ := hne₁
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk; omega
    · exact h
  refine ⟨T₂, f.comp g₁, fK.comp gK₁, e, k * e₂, hf.comp hg₁, inferInstance, hcomp, ?_, Nat.mul_pos hk0 he₂,
    fun a b => ?_⟩
  · rw [hy, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp]; rfl
  · have h := he a b
    rw [Nat.cast_one, one_mul] at h
    rw [← h, hk, mul_assoc]

end GlobalTheory.UPoinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitRamifiedExtensionFormMultipleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_unitaryTrait_ramifiedExtension_form_multiple : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (T : GlobalTheory.UPoinc.UTrait Xo c) (n : ℕ), 0 < n →
    ∃ (T₂ : GlobalTheory.UPoinc.UTrait Xo c) (g : T.V →+* T₂.V) (gK : FractionRing T.V →+* FractionRing T₂.V)
      (e : T.P.D.toPre.X ≃ₗ[𝓞 E] T₂.P.D.toPre.X) (q : ℕ), Function.Injective g ∧ IsLocalHom g ∧
      (∀ a, gK (algebraMap T.V _ a) = algebraMap T₂.V _ (g a)) ∧ T₂.y = spMap gK ≫ T.y ∧ 0 < q ∧
      ∀ a b, T₂.be (e a) (e b) = ((n * q : ℕ) : ℤ) * T.be a b := by
  first | exact @GlobalTheory.UPoinc.uTrait_ramExt | exact GlobalTheory.UPoinc.uTrait_ramExt | (intros; apply GlobalTheory.UPoinc.uTrait_ramExt <;> assumption)
end
end
