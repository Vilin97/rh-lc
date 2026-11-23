module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtR
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalEvenCharacterLeadingTermsMemMaximalIdealStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicIntegralReadingOfTrivialisationsStatement
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTranslatedMembersLeadingTimesIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicUnitMultipleFractionRing

section

@[expose] public section

namespace GlobalTheory
namespace EvenCubicNorm

open Finset

theorem eq_zero_of_even_cubic {ι X G : Type*} [AddCommGroup X] [AddCommGroup G]
    (b : Module.Basis ι ℤ X) (f : X → G) (hev : ∀ a, f (-a) = f a)
    (hcub : ∀ a a' c, f (a + a' + c) + f a + f a' + f c = f (a + a') + f (a + c) + f (a' + c))
    (h1 : ∀ i, f (b i) = 0) (h2 : ∀ i j, i ≠ j → f (b i + b j) = 0) : ∀ a, f a = 0 := by
  have hext : ∀ g : X →+ G, (∀ i, g (b i) = 0) → ∀ a, g a = 0 := by
    intro g hg a
    have : g.toIntLinearMap = 0 := b.ext (fun i => by simpa using hg i)
    simpa using LinearMap.congr_fun this a
  have h0 : f 0 = 0 := by simpa using hcub 0 0 0
  let B : X → X →+ G := fun c =>
    { toFun := fun a => f (a + c) - f a - f c
      map_zero' := by simp [h0]
      map_add' := by
        intro a a'
        have h := hcub a a' c
        have e : f (a + a' + c) - f (a + a') - f c - (f (a + c) - f a - f c + (f (a' + c) - f a' - f c))
            = (f (a + a' + c) + f a + f a' + f c) - (f (a + a') + f (a + c) + f (a' + c)) := by abel
        rw [← sub_eq_zero, e, h, sub_self] }
  have hBapp : ∀ c a, B c a = f (a + c) - f a - f c := fun _ _ => rfl
  have hdiag : ∀ i, B (b i) (b i) = 0 := by
    intro i
    have h := (B (b i)).map_add (b i) (-(b i))
    rw [add_neg_cancel, map_zero, hBapp (b i) (-(b i)), neg_add_cancel, hev, h0, h1] at h
    simpa using h.symm
  have hA : ∀ j a, B (b j) a = 0 := by
    intro j
    apply hext
    intro i
    by_cases hij : i = j
    · subst hij; exact hdiag i
    · rw [hBapp, h2 i j hij, h1, h1]; simp
  have hAll : ∀ a c, B c a = 0 := by
    intro a c
    have h := hext (B a) (fun j => by rw [hBapp, add_comm (b j) a, ← hA j a, hBapp]; abel) c
    rw [hBapp] at h ⊢
    rw [add_comm c a] at h
    rw [← h]; abel
  let F : X →+ G :=
    { toFun := f
      map_zero' := h0
      map_add' := by
        intro a c
        have h := hAll a c
        rw [hBapp, sub_sub, sub_eq_zero] at h
        exact h }
  intro a
  exact hext F h1 a

section Quadratic

variable {M : Type*} [CommGroup M] {ι : Type*} [Fintype ι]

def prodPow (z : ι → ι → M) (e : ι → ι → ℤ) : M := ∏ i, ∏ j, z i j ^ e i j

theorem prodPow_add (z : ι → ι → M) (e e' : ι → ι → ℤ) :
    prodPow z e * prodPow z e' = prodPow z (fun i j => e i j + e' i j) := by
  simp only [prodPow, zpow_add, Finset.prod_mul_distrib]

theorem prodPow_single [DecidableEq ι] (z : ι → ι → M) (k l : ι) :
    prodPow z (fun i j => if i = k ∧ j = l then 1 else 0) = z k l := by
  unfold prodPow
  rw [Finset.prod_eq_single k, Finset.prod_eq_single l]
  · simp
  · intro j _ hj; simp [hj]
  · simp
  · intro i _ hi
    apply Finset.prod_eq_one
    intro j _; simp [hi]
  · simp

end Quadratic

theorem indicator_sum_mul {ι : Type*} [DecidableEq ι] (i j k l : ι) (hkl : k ≠ l) :
    (((if i = k then 1 else 0) + (if i = l then 1 else 0)) * ((if j = k then 1 else 0) + (if j = l then 1 else 0)) : ℤ) =
      (if i = k ∧ j = k then 1 else 0) + (if i = l ∧ j = l then 1 else 0) +
        (if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0) := by
  by_cases hik : i = k <;> by_cases hil : i = l <;> by_cases hjk : j = k <;> by_cases hjl : j = l <;>
    simp_all

theorem exists_even_cubic_unit_multiple (R : Type) [CommRing R] [IsDomain R] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (κ₀ : X → (FractionRing R)ˣ)
    (hev : ∀ a, ∃ u : Rˣ, ((κ₀ (-a) : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R))
    (hcub : ∀ a a' b, ∃ u : Rˣ, ((κ₀ (a + a' + b) * κ₀ a * κ₀ a' * κ₀ b : (FractionRing R)ˣ) : FractionRing R) = ((κ₀ (a + a') * κ₀ (a + b) * κ₀ (a' + b) : (FractionRing R)ˣ) : FractionRing R) * algebraMap R (FractionRing R) (u : R)) :
    ∃ κ : X → (FractionRing R)ˣ, (∀ a, κ (-a) = κ a) ∧
      (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) ∧
      ∀ a, ∃ u : Rˣ, ((κ a : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R) := by
  classical
  set K := FractionRing R
  let φ : Rˣ →* Kˣ := Units.map (algebraMap R K).toMonoidHom
  have hφ : ∀ u : Rˣ, ((φ u : Kˣ) : K) = algebraMap R K (u : R) := fun u => rfl
  let H : Subgroup Kˣ := φ.range
  let ψ : Kˣ → Additive (Kˣ ⧸ H) := fun x => Additive.ofMul (QuotientGroup.mk x)
  have ψmul : ∀ x y, ψ (x * y) = ψ x + ψ y := fun x y => rfl
  have ψφ : ∀ x u, ψ (x * φ u) = ψ x := by
    intro x u
    rw [ψmul]
    have : ψ (φ u) = 0 := by
      show Additive.ofMul (QuotientGroup.mk (φ u) : Kˣ ⧸ H) = 0
      rw [(QuotientGroup.eq_one_iff (φ u)).mpr (MonoidHom.mem_range.mpr ⟨u, rfl⟩)]; rfl
    rw [this, add_zero]
  have ψeq : ∀ x y, ψ x = ψ y → ∃ u : Rˣ, y = x * φ u := by
    intro x y h
    have h' : (QuotientGroup.mk x : Kˣ ⧸ H) = QuotientGroup.mk y := h
    obtain ⟨u, hu⟩ := QuotientGroup.eq.mp h'
    exact ⟨u, by rw [hu]; group⟩
  let b := (Module.Free.chooseBasis ℤ X).reindex (Fintype.equivFin _)
  set r := Fintype.card (Module.Free.ChooseBasisIndex ℤ X)
  let n : Fin r → X → ℤ := fun i a => b.repr a i
  let z : Fin r → Fin r → Kˣ := fun i j =>
    if i = j then κ₀ (b i) else if i < j then κ₀ (b i + b j) * (κ₀ (b i))⁻¹ * (κ₀ (b j))⁻¹ else 1
  let E : X → Fin r → Fin r → ℤ := fun a i j => n i a * n j a
  let κ : X → Kˣ := fun a => prodPow z (E a)
  have hκ : ∀ a, κ a = prodPow z (E a) := fun _ => rfl
  have κev : ∀ a, κ (-a) = κ a := by
    intro a; simp only [hκ]; congr 1; funext i j; simp [E, n]
  have κcub : ∀ a a' c, κ (a + a' + c) * κ a * κ a' * κ c = κ (a + a') * κ (a + c) * κ (a' + c) := by
    intro a a' c
    simp only [hκ, prodPow_add]
    congr 1; funext i j; simp only [E, n, map_add (f := _), Finsupp.add_apply]; ring
  have nb : ∀ i k, n i (b k) = if i = k then 1 else 0 := by
    intro i k; simp [n, Finsupp.single_apply, eq_comm]
  have κb : ∀ k, κ (b k) = κ₀ (b k) := by
    intro k
    have : E (b k) = fun i j => if i = k ∧ j = k then 1 else 0 := by
      funext i j; simp only [E, nb]; split_ifs <;> simp_all
    rw [hκ, this, prodPow_single]; simp [z]
  have κbb : ∀ k l, k < l → κ (b k + b l) = κ₀ (b k + b l) := by
    intro k l hkl
    have hne : k ≠ l := ne_of_lt hkl
    have hsplit : prodPow z (E (b k + b l)) =
        prodPow z (fun i j => if i = k ∧ j = k then 1 else 0) * prodPow z (fun i j => if i = l ∧ j = l then 1 else 0) *
        prodPow z (fun i j => if i = k ∧ j = l then 1 else 0) * prodPow z (fun i j => if i = l ∧ j = k then 1 else 0) := by
      simp only [prodPow_add]
      congr 1; funext i j; simp only [E, n, map_add (f := _), Finsupp.add_apply]
      have h1 := nb i k; have h2 := nb i l; have h3 := nb j k; have h4 := nb j l
      simp only [n] at h1 h2 h3 h4
      rw [h1, h2, h3, h4]
      exact indicator_sum_mul i j k l hne
    rw [hκ, hsplit, prodPow_single, prodPow_single, prodPow_single, prodPow_single]
    have hzk : z k k = κ₀ (b k) := by simp only [z]; exact if_pos trivial
    have hzl : z l l = κ₀ (b l) := by simp only [z]; exact if_pos trivial
    have hzkl : z k l = κ₀ (b k + b l) * (κ₀ (b k))⁻¹ * (κ₀ (b l))⁻¹ := by
      simp only [z]; rw [if_neg hne, if_pos hkl]
    have hzlk : z l k = 1 := by simp only [z]; rw [if_neg hne.symm, if_neg (not_lt_of_gt hkl)]
    rw [hzk, hzl, hzkl, hzlk, mul_one, mul_comm (κ₀ (b k) * κ₀ (b l)), mul_assoc, mul_assoc,
      ← mul_assoc (κ₀ (b k))⁻¹, ← mul_inv, inv_mul_cancel, mul_one]
  have κbb' : ∀ k l, k ≠ l → κ (b k + b l) = κ₀ (b k + b l) := by
    intro k l hkl
    rcases lt_or_gt_of_ne hkl with h | h
    · exact κbb k l h
    · rw [add_comm]; exact κbb l k h

  have κ₀ev : ∀ a, ψ (κ₀ (-a)) = ψ (κ₀ a) := by
    intro a
    obtain ⟨u, hu⟩ := hev a
    have : κ₀ (-a) = κ₀ a * φ u := Units.ext (by rw [Units.val_mul, hφ]; exact hu)
    rw [this, ψφ]
  have κ₀cub : ∀ a a' c, ψ (κ₀ (a + a' + c)) + ψ (κ₀ a) + ψ (κ₀ a') + ψ (κ₀ c) =
      ψ (κ₀ (a + a')) + ψ (κ₀ (a + c)) + ψ (κ₀ (a' + c)) := by
    intro a a' c
    obtain ⟨u, hu⟩ := hcub a a' c
    have : κ₀ (a + a' + c) * κ₀ a * κ₀ a' * κ₀ c = κ₀ (a + a') * κ₀ (a + c) * κ₀ (a' + c) * φ u :=
      Units.ext (by rw [Units.val_mul _ (φ u), hφ]; exact hu)
    have h := congrArg ψ this
    rw [ψφ] at h
    simpa only [ψmul] using h
  let f : X → Additive (Kˣ ⧸ H) := fun a => ψ (κ (a)) - ψ (κ₀ a)
  have hf : ∀ a, f a = 0 := by
    refine EvenCubicNorm.eq_zero_of_even_cubic b f ?_ ?_ ?_ ?_
    · intro a; simp only [f]; rw [κev, κ₀ev]
    · intro a a' c
      have h1 := κ₀cub a a' c
      have h2 := congrArg ψ (κcub a a' c)
      simp only [ψmul] at h2
      simp only [f]
      have e : ψ (κ (a + a' + c)) - ψ (κ₀ (a + a' + c)) + (ψ (κ a) - ψ (κ₀ a)) + (ψ (κ a') - ψ (κ₀ a')) +
            (ψ (κ c) - ψ (κ₀ c)) - (ψ (κ (a + a')) - ψ (κ₀ (a + a')) + (ψ (κ (a + c)) - ψ (κ₀ (a + c))) +
            (ψ (κ (a' + c)) - ψ (κ₀ (a' + c)))) =
          (ψ (κ (a + a' + c)) + ψ (κ a) + ψ (κ a') + ψ (κ c) - (ψ (κ (a + a')) + ψ (κ (a + c)) + ψ (κ (a' + c)))) -
          (ψ (κ₀ (a + a' + c)) + ψ (κ₀ a) + ψ (κ₀ a') + ψ (κ₀ c) -
            (ψ (κ₀ (a + a')) + ψ (κ₀ (a + c)) + ψ (κ₀ (a' + c)))) := by abel
      rw [← sub_eq_zero, e, h1, h2, sub_self, sub_self, sub_self]
    · intro i; simp only [f]; rw [κb, sub_self]
    · intro i j hij; simp only [f]; rw [κbb' i j hij, sub_self]
  refine ⟨κ, κev, κcub, fun a => ?_⟩
  have h := hf a
  simp only [f, sub_eq_zero] at h
  obtain ⟨u, hu⟩ := ψeq _ _ h.symm
  exact ⟨u, by rw [hu, Units.val_mul, hφ]⟩

end EvenCubicNorm
end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicUnitMultipleFractionRingStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_even_cubic_unit_multiple_fractionRing : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (κ₀ : X → (FractionRing R)ˣ), (∀ a, ∃ u : Rˣ, ((κ₀ (-a) : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R)) → (∀ a a' b, ∃ u : Rˣ, ((κ₀ (a + a' + b) * κ₀ a * κ₀ a' * κ₀ b : (FractionRing R)ˣ) : FractionRing R) = ((κ₀ (a + a') * κ₀ (a + b) * κ₀ (a' + b) : (FractionRing R)ˣ) : FractionRing R) * algebraMap R (FractionRing R) (u : R)) → ∃ κ : X → (FractionRing R)ˣ, (∀ a, κ (-a) = κ a) ∧ (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) ∧ ∀ a, ∃ u : Rˣ, ((κ a : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R) := by
  first | exact @GlobalTheory.EvenCubicNorm.exists_even_cubic_unit_multiple | exact GlobalTheory.EvenCubicNorm.exists_even_cubic_unit_multiple | (intros; apply GlobalTheory.EvenCubicNorm.exists_even_cubic_unit_multiple <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaFamilyPrescribedLeadingTerm

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ThFam

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem gs_scal_one {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (y : Y) : gs (𝟙 Y) y ⊤ (scal p 1) = 1 := by
  have h : scal p (1 : R) = 1 := by simp [scal]
  rw [h, gs_eq _ y ⊤ trivial, map_one, map_one]

theorem secScal_generic (D : DegData R (maximalIdeal R)) (k : ℕ) (α : D.toPre.X) (b : D.toPre.SecB k α) :
    GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k)
      (GlobalTheory.FieldBaseChange.genericTerm D k α b) (D.toPre.famφB α) (DegPre.famε k) b
      (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) := by
  refine (GlobalTheory.FieldBaseChange.secScal_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_
  exact (GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).symm.trans
    ((_root_.one_mul _).symm.trans (congrArg (· * _) (gs_scal_one _ y).symm))

theorem lead_units {X : Type} [AddCommGroup X] (κ κ' : X → (FractionRing R)ˣ) (u : X → Rˣ)
    (hu : ∀ a, ((κ' a : (FractionRing R)ˣ) : FractionRing R) = (κ a : FractionRing R) * algebraMap R (FractionRing R) (u a : R))
    (k : ℕ) (α mu : X) :
    ((lead κ k α mu : (FractionRing R)ˣ) : FractionRing R) = (lead κ' k α mu : FractionRing R) *
      algebraMap R (FractionRing R) (((u mu ^ k * (u (mu + α) * (u mu)⁻¹ * (u α)⁻¹))⁻¹ : Rˣ) : R) := by
  have e : ∀ x : Rˣ, algebraMap R (FractionRing R) ((x⁻¹ : Rˣ) : R) = (algebraMap R (FractionRing R) (x : R))⁻¹ :=
    fun x => map_units_inv (algebraMap R (FractionRing R) : R →* FractionRing R) x
  have ne : ∀ x : Rˣ, algebraMap R (FractionRing R) (x : R) ≠ 0 := fun x =>
    (x.isUnit.map (algebraMap R (FractionRing R))).ne_zero
  have h₁ := ne (u mu); have h₂ := ne (u (mu + α)); have h₃ := ne (u α)
  have h₄ := (κ mu).ne_zero; have h₅ := (κ (mu + α)).ne_zero; have h₆ := (κ α).ne_zero
  simp only [lead, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hu, e, map_mul, map_pow]
  field_simp
  ring

theorem core (hR : Base R) (D : DegData R (maximalIdeal R)) (κ : D.toPre.X → (FractionRing R)ˣ)
    (hκ : Reads D.toPre κ) (κ' : D.toPre.X → (FractionRing R)ˣ)
    (hu : ∀ a, ∃ u : Rˣ, ((κ' a : (FractionRing R)ˣ) : FractionRing R) =
      (κ a : FractionRing R) * algebraMap R (FractionRing R) (u : R))
    (k : ℕ) (hk : 1 ≤ k) (α : D.toPre.X)
    (h1 : ∀ mu, mu ≠ 0 → ∃ s ∈ maximalIdeal R,
      ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s)
    (h2 : ∀ n : ℕ, {mu | ¬ ∃ s ∈ maximalIdeal R ^ n,
      ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s}.Finite)
    (b : D.toPre.SecB k α) : ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead α b := by
  classical
  choose u hu using hu
  have inj := IsFractionRing.injective R (FractionRing R)
  have h1' : ∀ mu, ∃ s : R, mu ≠ 0 → s ∈ maximalIdeal R ∧
      ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s := fun mu => by
    by_cases h : mu = 0
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨s, hs, e⟩ := h1 mu h
      exact ⟨s, fun _ => ⟨hs, e⟩⟩
  choose s hs using h1'
  let w : D.toPre.X → R := fun mu => (((u mu ^ k * (u (mu + α) * (u mu)⁻¹ * (u α)⁻¹))⁻¹ : Rˣ) : R)
  let r : D.toPre.X → R := fun mu => s mu * w mu
  have hr : ∀ mu, mu ≠ 0 → algebraMap R (FractionRing R) (r mu) =
      ((lead κ k α mu : (FractionRing R)ˣ) : FractionRing R) ∧ r mu ∈ maximalIdeal R := fun mu h =>
    ⟨by rw [lead_units κ κ' u hu k α mu, (hs mu h).2, map_mul], Ideal.mul_mem_right _ _ (hs mu h).1⟩
  have key : ∀ mu, mu ≠ 0 → ∀ e : ℕ, r mu ∉ maximalIdeal R ^ (e + 1) → ¬ ∃ s' ∈ maximalIdeal R ^ (e + 1),
      ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s' := by
    rintro mu h e hn ⟨s', hs'm, hs'e⟩
    have : s mu = s' := inj ((hs mu h).2.symm.trans hs'e)
    exact hn (Ideal.mul_mem_right _ _ (this ▸ hs'm))
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  have hcls : ∀ a c : D.toPre.X, α + k • a = α + k • c → a = c := fun a c h => by
    have h' : (k : ℤ) • a = (k : ℤ) • c := by simpa using add_left_cancel h
    exact smul_right_injective D.toPre.X (show (k : ℤ) ≠ 0 by omega) h'
  obtain ⟨F, hFα, hF0⟩ := ReciprocityTheory.ChartRestriction.G.DVR.UUA.exists_fam_rep (F := FractionRing R) hG D.tau_bimult k α hcls
    (GlobalTheory.FieldBaseChange.genericTerm D k α b)
  have hb : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α)
      (D.toPre.famφB α) (DegPre.famε k) b (DegPre.prB D.toPre (FractionRing R)).left
      (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) := by
    rw [hFα]; exact secScal_generic D k α b
  have hex : ∀ β : D.toPre.X, ∃ g : D.toPre.SecB k β, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) β)
      (DegPre.famε k) (F.s β) (D.toPre.famφB β) (DegPre.famε k) g (DegPre.prB D.toPre (FractionRing R)).left
      (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) ∧ (β ≠ α → VanMod (maximalIdeal R) g 0 ∧
        ∀ e : ℕ, ¬ VanMod (maximalIdeal R) g e → ∃ mu, α + k • mu = β ∧ ¬ ∃ s' ∈ maximalIdeal R ^ (e + 1),
          ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s') := by
    intro β
    by_cases hβ : β = α
    · subst hβ
      exact ⟨b, hb, fun h => absurd rfl h⟩
    by_cases hc : ∃ mu, α + k • mu = β
    · obtain ⟨mu, rfl⟩ := hc
      have hmu : mu ≠ 0 := by
        rintro rfl
        exact hβ (by simp)
      obtain ⟨f, hf1, hf2⟩ := GlobalTheory.T.thetaFamily_translatedMembers_leading_times_integral R hR D κ hκ k hk α b F hb mu (r mu) (hr mu hmu).1
      refine ⟨f, hf1, fun _ => ⟨hf2 0 (by simpa using (hr mu hmu).2), fun e he => ⟨mu, rfl, ?_⟩⟩⟩
      exact key mu hmu e (fun h => he (hf2 e h))
    · push_neg at hc
      refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secZero, ?_, fun _ => ⟨fun j => map_zero _, fun e he => absurd (fun j => map_zero _) he⟩⟩
      refine (GlobalTheory.FieldBaseChange.secScal_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_
      rw [ReciprocityTheory.ChartRestriction.G.DVR.UUA.sval_zero_of (fun j => rfl) _ y J (hJ.mem _ _),
        ReciprocityTheory.ChartRestriction.G.DVR.UUA.sval_zero_of (hF0 β hc) _ y J (hJ.mem _ _), mul_zero]
  choose g hg using hex
  refine ⟨⟨F, Function.update g α b, fun β => ?_, fun e => ?_⟩, Function.update_self α b g, fun β hβ => ?_⟩
  · by_cases h : β = α
    · subst h
      rw [Function.update_self]
      exact hb
    · rw [Function.update_of_ne h]
      exact (hg β).1
  · refine (((h2 (e + 1)).image (fun mu => α + k • mu)).insert α).subset fun β hβ => ?_
    by_cases h : β = α
    · exact Or.inl h
    · right
      have hβ' : ¬ VanMod (maximalIdeal R) (g β) e := by
        have := hβ
        simp only [Set.mem_setOf_eq] at this
        rwa [Function.update_of_ne h] at this
      obtain ⟨mu, hmu, hn⟩ := ((hg β).2 h).2 e hβ'
      exact ⟨mu, hn, hmu⟩
  · show VanMod (maximalIdeal R) (Function.update g α b β) 0
    rw [Function.update_of_ne hβ]
    exact ((hg β).2 hβ).1

theorem exists_intFam_lead : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)), (∀ α : D.toPre.X, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ b : D.toPre.SecB k α,
      ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead α b) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ b : D.toPre.SecB k 0, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead 0 b := by
  intro R _ _ _ hR D
  haveI := hR.1.1
  haveI := hR.1.2.2.1
  obtain ⟨κ, hκ, hev, hcub, hpos, htend⟩ := GlobalTheory.T.exists_even_cubic_integral_reading_of_trivialisations R hR D
  obtain ⟨κ', hev', hcub', hu⟩ := GlobalTheory.T.exists_even_cubic_unit_multiple_fractionRing R D.toPre.X κ hev hcub
  have hu0 := hu
  choose u hu' using hu0
  have hpos' : ∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, ((κ' a : (FractionRing R)ˣ) : FractionRing R) =
      algebraMap R (FractionRing R) s := fun a ha => by
    obtain ⟨s, hs, e⟩ := hpos a ha
    exact ⟨s * u a, Ideal.mul_mem_right _ _ hs, by rw [hu' a, e, map_mul]⟩
  have h0 : κ' 0 = 1 := by
    have := hcub' 0 0 0
    simp only [add_zero] at this
    exact mul_eq_left.1 this
  refine ⟨fun α => ?_, fun k hk b => ?_⟩
  · obtain ⟨k₁, H⟩ := GlobalTheory.T.cubical_even_character_leading_terms_mem_maximalIdeal R D.toPre.X κ' hev' hcub' hpos' α
    exact ⟨max k₁ 1, fun k hk b => core hR D κ hκ κ' hu k (le_of_max_le_right hk) α
      (H k (le_of_max_le_left hk)).1 (H k (le_of_max_le_left hk)).2 b⟩
  · have hl : ∀ mu, lead κ' k 0 mu = κ' mu ^ k := fun mu => by
      simp [lead, h0]
    refine core hR D κ hκ κ' hu k hk 0 (fun mu hmu => ?_) (fun n => ?_) b
    · obtain ⟨s, hs, e⟩ := hpos' mu hmu
      exact ⟨s ^ k, Ideal.pow_mem_of_mem _ hs k (by omega), by rw [hl, Units.val_pow_eq_pow_val, e, map_pow]⟩
    · refine (htend n).subset fun mu hmu h => hmu ?_
      obtain ⟨s, hs, e⟩ := h
      refine ⟨(s * u mu) ^ k, Ideal.pow_mem_of_mem _ (Ideal.mul_mem_right _ _ hs) k (by omega), ?_⟩
      rw [hl, Units.val_pow_eq_pow_val, hu' mu, e, ← map_mul, ← map_pow]

end GlobalTheory.ThFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaFamilyPrescribedLeadingTermStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_integralThetaFamily_prescribed_leadingTerm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), (∀ α : D.toPre.X, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ b : D.toPre.SecB k α, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead α b) ∧ ∀ k : ℕ, 1 ≤ k → ∀ b : D.toPre.SecB k 0, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead 0 b := by
  first | exact @GlobalTheory.ThFam.exists_intFam_lead | exact GlobalTheory.ThFam.exists_intFam_lead | (intros; apply GlobalTheory.ThFam.exists_intFam_lead <;> assumption)
end
end
