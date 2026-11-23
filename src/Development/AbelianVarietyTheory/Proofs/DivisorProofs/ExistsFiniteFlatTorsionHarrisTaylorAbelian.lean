module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.Subsingleton
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyDegreeKilledByPrimeToPHarrisTaylorStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyOfDegreeIntActionHarrisTaylor
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormallyUnramifiedOfCompOfEtaleOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqMulOfRankAtStalk
import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelsOfChain
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeIdealMulEqSpanNumberField

section

@[expose] public section

open scoped NumberField

namespace GlobalTheory.IdealPrincipalCoprime

theorem natCast_prime_not_isUnit (F : Type) [Field F] [NumberField F] {p : ℕ} (hp : p.Prime) :
    ¬ IsUnit (p : 𝓞 F) := by
  intro h
  have h1 := h.map (Algebra.norm ℤ (S := 𝓞 F))
  rw [← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap,
    isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h1
  exact hp.ne_one h1

theorem exists_mul_eq_span_coprime : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime →
    ∀ (w : Ideal (𝓞 F)), w ≠ ⊥ → ∃ (g e : 𝓞 F) (𝔟 : Ideal (𝓞 F)), g ≠ 0 ∧ e ∈ w ∧ 1 - e ∈ 𝔟 ∧
      w * 𝔟 = Ideal.span {g} ∧ 𝔟 ⊔ Ideal.span {(p : 𝓞 F)} = ⊤ := by
  intro F _ _ p hp w hw
  set N : Ideal (𝓞 F) := Ideal.span {(p : 𝓞 F)} * w with hN
  have hp0 : (p : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hN0 : N ≠ ⊥ := by
    rw [hN, Ne, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]
    exact ⟨hp0, hw⟩
  obtain ⟨g, hg⟩ := IsDedekindDomain.exists_sup_span_eq (I := w * N) (J := w) Ideal.mul_le_left
    (mul_ne_zero hw hN0)
  have hgw : Ideal.span {g} ≤ w := hg ▸ le_sup_right
  obtain ⟨𝔟, h𝔟⟩ := Ideal.dvd_iff_le.mpr hgw
  have hsup : N ⊔ 𝔟 = ⊤ := by
    apply mul_left_cancel₀ (show w ≠ 0 from hw)
    rw [Ideal.mul_sup, ← h𝔟, hg, Ideal.mul_top]
  have hNp : N ≤ Ideal.span {(p : 𝓞 F)} := Ideal.mul_le_left
  have hNw : N ≤ w := Ideal.mul_le_right
  have hbp : 𝔟 ⊔ Ideal.span {(p : 𝓞 F)} = ⊤ := by
    have h : N ⊔ 𝔟 ≤ 𝔟 ⊔ Ideal.span {(p : 𝓞 F)} := sup_le (le_sup_of_le_right hNp) le_sup_left
    rw [hsup] at h; exact eq_top_iff.mpr h
  have hwb : w ⊔ 𝔟 = ⊤ := by
    have h : N ⊔ 𝔟 ≤ w ⊔ 𝔟 := sup_le (le_sup_of_le_left hNw) le_sup_right
    rw [hsup] at h; exact eq_top_iff.mpr h
  have h1 : (1 : 𝓞 F) ∈ w ⊔ 𝔟 := by rw [hwb]; exact Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  refine ⟨g, e, 𝔟, ?_, he, ?_, h𝔟.symm, hbp⟩
  · intro hg0
    have hb0 : 𝔟 = ⊥ := by
      have : w * 𝔟 = ⊥ := by rw [← h𝔟, hg0, Ideal.span_singleton_eq_bot.mpr rfl]
      rcases Ideal.mul_eq_bot.mp this with h | h
      · exact absurd h hw
      · exact h
    rw [hb0, bot_sup_eq] at hbp
    exact natCast_prime_not_isUnit F hp (Ideal.span_singleton_eq_top.mp hbp)
  · rw [← hef, add_sub_cancel_left]; exact hf

end GlobalTheory.IdealPrincipalCoprime
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeIdealMulEqSpanNumberFieldStatement

section

@[expose] public section

open scoped NumberField

theorem _root_.GlobalTheory.T.exists_coprime_ideal_mul_eq_span_numberField : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ (w : Ideal (𝓞 F)), w ≠ ⊥ → ∃ (g e : 𝓞 F) (𝔟 : Ideal (𝓞 F)), g ≠ 0 ∧ e ∈ w ∧ 1 - e ∈ 𝔟 ∧ w * 𝔟 = Ideal.span {g} ∧ 𝔟 ⊔ Ideal.span {(p : 𝓞 F)} = ⊤ := by
  first | (exact @GlobalTheory.IdealPrincipalCoprime.exists_mul_eq_span_coprime) | (exact GlobalTheory.IdealPrincipalCoprime.exists_mul_eq_span_coprime) | (intros; apply GlobalTheory.IdealPrincipalCoprime.exists_mul_eq_span_coprime  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyOfDegreeIntActionHarrisTaylorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isIsogenyOfDegree_intAction_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (c : 𝓞 D.F), c ≠ 0 → GlobalTheory.IwLevel.IsIsogDeg (o.act.act (algebraMap (𝓞 D.F) D.O c)) ((Algebra.norm ℤ c).natAbs ^ (D.m * D.n)) := by
  first | (exact @GlobalTheory.HTTors.isIsogDeg_intAct) | (exact GlobalTheory.HTTors.isIsogDeg_intAct) | (intros; apply GlobalTheory.HTTors.isIsogDeg_intAct  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyOfDegreeTorsionCoprimeIdealsProduct

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IwLevel.CoprimeTors

theorem isIsogDeg_of_coprime : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [CommRing O]
    (ρ : ReciprocityTheory.ChartRestriction.G.Out.RingAct A O) (𝔞 𝔟 : Ideal O), 𝔞 ⊔ 𝔟 = ⊤ →
    ∀ (K₁ K₂ K₃ : Over S) (i₁ : K₁ ⟶ A) (i₂ : K₂ ⟶ A) (i₃ : K₃ ⟶ A), Mono i₁ → Mono i₂ → Mono i₃ →
    (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₁ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔞 x) →
    (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₂ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔟 x) →
    (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₃ x ↔ GlobalTheory.IwLevel.KilledBy ρ (𝔞 * 𝔟) x) →
    ∀ (d e : ℕ), 0 < e → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₃) (d * e) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₂) e →
    GlobalTheory.IwLevel.IsIsogDeg (toUnit K₁) d := by
  intro S A _ _ O _ ρ 𝔞 𝔟 hab K₁ K₂ K₃ i₁ i₂ i₃ _ _ _ h₁ h₂ h₃ d e he hK₃ hK₂
  have h1mem : (1 : O) ∈ 𝔞 ⊔ 𝔟 := hab ▸ Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1mem
  have k₁ : ∀ a ∈ 𝔞, i₁ ≫ ρ.act a = 1 := fun a ha => (h₁ K₁ i₁).1 ⟨𝟙 _, Category.id_comp _⟩ a ha
  have k₂ : ∀ a ∈ 𝔟, i₂ ≫ ρ.act a = 1 := fun a ha => (h₂ K₂ i₂).1 ⟨𝟙 _, Category.id_comp _⟩ a ha
  have k₃ : ∀ a ∈ 𝔞 * 𝔟, i₃ ≫ ρ.act a = 1 := fun a ha => (h₃ K₃ i₃).1 ⟨𝟙 _, Category.id_comp _⟩ a ha
  have hadd : ∀ {T : Over S} (x : T ⟶ A) (a b : O),
      x ≫ ρ.act (a + b) = (x ≫ ρ.act a) * (x ≫ ρ.act b) := fun x a b => by
    rw [ρ.map_add]; exact MonObj.comp_mul x _ _
  have hone : ∀ {T : Over S} (x : T ⟶ A), x ≫ ρ.act 1 = x := fun x => by
    rw [ρ.map_one, Category.comp_id]
  have e₁ : i₁ ≫ ρ.act v = i₁ := by
    have := hadd i₁ v u
    rw [add_comm v u, huv, hone, k₁ u hu, _root_.mul_one] at this
    exact this.symm
  have e₂ : i₂ ≫ ρ.act u = i₂ := by
    have := hadd i₂ u v
    rw [huv, hone, k₂ v hv, _root_.mul_one] at this
    exact this.symm
  have hm : GlobalTheory.IwLevel.KilledBy ρ (𝔞 * 𝔟) ((fst K₁ K₂ ≫ i₁) * (snd K₁ K₂ ≫ i₂)) := fun c hc => by
    have := ρ.hom c
    have hc₁ : c ∈ 𝔞 := Ideal.mul_le_left (I := 𝔞) (J := 𝔟) hc
    have hc₂ : c ∈ 𝔟 := Ideal.mul_le_right (I := 𝔞) (J := 𝔟) hc
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, k₁ c hc₁, k₂ c hc₂, MonObj.comp_one,
      MonObj.comp_one, _root_.mul_one]
  obtain ⟨m, hm'⟩ := (h₃ _ _).2 hm
  have hg₁ : GlobalTheory.IwLevel.KilledBy ρ 𝔞 (i₃ ≫ ρ.act v) := fun a ha => by
    rw [Category.assoc, ← ρ.map_mul]; exact k₃ _ (Ideal.mul_mem_mul ha hv)
  have hg₂ : GlobalTheory.IwLevel.KilledBy ρ 𝔟 (i₃ ≫ ρ.act u) := fun b hb => by
    rw [Category.assoc, ← ρ.map_mul, mul_comm]; exact k₃ _ (Ideal.mul_mem_mul hu hb)
  obtain ⟨g₁, hg₁'⟩ := (h₁ _ _).2 hg₁
  obtain ⟨g₂, hg₂'⟩ := (h₂ _ _).2 hg₂
  have iso : IsIso m := by
    refine ⟨⟨lift g₁ g₂, ?_, ?_⟩⟩
    · have hr := ρ.hom v
      have hs := ρ.hom u
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, Category.id_comp, ← cancel_mono i₁, Category.assoc, hg₁',
          ← Category.assoc, hm', MonObj.mul_comp, Category.assoc, Category.assoc, e₁, k₂ v hv,
          MonObj.comp_one, _root_.mul_one]
      · rw [Category.assoc, lift_snd, Category.id_comp, ← cancel_mono i₂, Category.assoc, hg₂',
          ← Category.assoc, hm', MonObj.mul_comp, Category.assoc, Category.assoc, e₂, k₁ u hu,
          MonObj.comp_one, _root_.one_mul]
    · rw [← cancel_mono i₃, Category.assoc, hm', MonObj.comp_mul, ← Category.assoc, lift_fst,
        ← Category.assoc, lift_snd, hg₁', hg₂', ← hadd, add_comm, huv, hone, Category.id_comp]
  have hP : GlobalTheory.IwLevel.IsIsogDeg (toUnit (K₁ ⊗ K₂)) (d * e) := by
    rw [toUnit_unique (toUnit (K₁ ⊗ K₂)) (m ≫ toUnit K₃), ← _root_.one_mul (d * e)]
    exact (GlobalTheory.IwLevel.IsIsogDeg.of_isIso m).comp hK₃
  have hpb : IsPullback (fst K₁ K₂) (snd K₁ K₂) (toUnit K₁) (toUnit K₂) :=
    ⟨⟨toUnit_unique _ _⟩, ⟨PullbackCone.IsLimit.mk _ (fun c ↦ lift c.fst c.snd) (fun _ ↦ lift_fst _ _)
      (fun _ ↦ lift_snd _ _) fun c m h₁ h₂ ↦ by ext <;> simp [h₁, h₂]⟩⟩
  have hfst : GlobalTheory.IwLevel.IsIsogDeg (fst K₁ K₂) e := hK₂.of_isPullback (hpb.flip.map (Over.forget S))
  have hcomp : fst K₁ K₂ ≫ toUnit K₁ = toUnit (K₁ ⊗ K₂) := toUnit_unique _ _
  have := hfst.fin; have := hfst.flat; have := hfst.surj
  have := hP.fin; have := hP.flat; have := hP.surj

  obtain ⟨t, -⟩ := (h₂ K₁ (1 : K₁ ⟶ A)).2 fun b _ => by have := ρ.hom b; exact MonObj.one_comp _
  let s : K₁ ⟶ K₁ ⊗ K₂ := lift (𝟙 K₁) t
  have hs : s ≫ fst K₁ K₂ = 𝟙 K₁ := lift_fst _ _
  have hsep : IsSeparated (fst K₁ K₂).left := inferInstance
  have : IsFinite (s.left ≫ (fst K₁ K₂).left) := by
    rw [← Over.comp_left, hs, Over.id_left]; infer_instance
  have : IsFinite s.left := IsFinite.of_comp s.left (fst K₁ K₂).left
  have hsu : s ≫ toUnit (K₁ ⊗ K₂) = toUnit K₁ := toUnit_unique _ _
  have hfin : IsFinite (toUnit K₁).left := by rw [← hsu, Over.comp_left]; infer_instance
  have : Flat ((fst K₁ K₂).left ≫ (toUnit K₁).left) := by rw [← Over.comp_left, hcomp]; infer_instance
  have hflat : Flat (toUnit K₁).left := flat_of_comp_of_flat_of_surjective (fst K₁ K₂).left _
  have : Surjective ((fst K₁ K₂).left ≫ (toUnit K₁).left) := by
    rw [← Over.comp_left, hcomp]; infer_instance
  have hsurj : Surjective (toUnit K₁).left := Surjective.of_comp (fst K₁ K₂).left _
  refine ⟨hfin, hflat, hsurj, fun y => ?_⟩
  have h := GlobalTheory.FinrankComp.finrank_comp_of_const (fst K₁ K₂).left (toUnit K₁).left e hfst.rank y
  rw [← Over.comp_left, hcomp, hP.rank, mul_comm d e] at h
  exact (Nat.eq_of_mul_eq_mul_left he h).symm

end GlobalTheory.IwLevel.CoprimeTors
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyOfDegreeTorsionCoprimeIdealsProductStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isIsogenyOfDegree_torsion_coprime_ideals_product : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [CommRing O] (ρ : ReciprocityTheory.ChartRestriction.G.Out.RingAct A O) (𝔞 𝔟 : Ideal O), 𝔞 ⊔ 𝔟 = ⊤ → ∀ (K₁ K₂ K₃ : Over S) (i₁ : K₁ ⟶ A) (i₂ : K₂ ⟶ A) (i₃ : K₃ ⟶ A), Mono i₁ → Mono i₂ → Mono i₃ → (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₁ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔞 x) → (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₂ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔟 x) → (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₃ x ↔ GlobalTheory.IwLevel.KilledBy ρ (𝔞 * 𝔟) x) → ∀ (d e : ℕ), 0 < e → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₃) (d * e) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₂) e → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₁) d := by
  first | (exact @GlobalTheory.IwLevel.CoprimeTors.isIsogDeg_of_coprime) | (exact GlobalTheory.IwLevel.CoprimeTors.isIsogDeg_of_coprime) | (intros; apply GlobalTheory.IwLevel.CoprimeTors.isIsogDeg_of_coprime  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFlatTorsionHarrisTaylorAbelian

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTTors

open GlobalTheory.IwLevel GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S : Scheme.{0}} {s : S ⟶ Sp R}

def actF (o : Obj b N s) : Out.RingAct o.A (𝓞 D.F) :=
  ⟨fun c => o.act.act (algebraMap (𝓞 D.F) D.O c), fun _ => o.act.hom _,
   by rw [map_one]; exact o.act.one,
   fun _ _ => by rw [map_mul]; exact o.act.mul _ _,
   fun _ _ => by rw [map_add (f := _)]; exact o.act.add _ _⟩

theorem killedBy_map (o : Obj b N s) (w : Ideal (𝓞 D.F)) {T : Over S} (x : T ⟶ o.A) :
    KilledBy (htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x ↔ KilledBy (actF o) w x := by
  rw [Ideal.map, killedBy_span]
  exact Set.forall_mem_image

theorem inSub_ker {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] {T : Over S} (x : T ⟶ A) :
    InSub (pullback.fst f η[B]) x ↔ x ≫ f = 1 := by
  refine ⟨?_, fun h => ⟨KerGrp.lift f x h, KerGrp.lift_fst _ _ _⟩⟩
  rintro ⟨y, rfl⟩
  rw [Category.assoc, KerGrp.fst_comp, MonObj.comp_one]

theorem comp_lift_eq_one {A : Over S} [GrpObj A] {T : Over S} (x : T ⟶ A) (a c : A ⟶ A) :
    x ≫ lift a c = 1 ↔ x ≫ a = 1 ∧ x ≫ c = 1 := by
  constructor
  · intro h
    have h1 := congrArg (· ≫ fst A A) h
    have h2 := congrArg (· ≫ snd A A) h
    simp only [Category.assoc, lift_fst, lift_snd, MonObj.one_comp] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, h1, MonObj.one_comp]
    · rw [Category.assoc, lift_snd, h2, MonObj.one_comp]

theorem killedBy_pair {A : Over S} [GrpObj A] [IsCommMonObj A] (ρ : Out.RingAct A (𝓞 D.F)) (g e : 𝓞 D.F)
    {T : Over S} (x : T ⟶ A) :
    KilledBy ρ (Ideal.span {g, e}) x ↔ x ≫ lift (ρ.act g) (ρ.act e) = 1 := by
  rw [killedBy_span, comp_lift_eq_one]
  simp

theorem htTorsion : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (w : Ideal (𝓞 D.F)), w ≠ ⊥ → ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ o.A), IsMonHom i ∧ Mono i ∧ GlobalTheory.IwLevel.IsIsogDeg (toUnit K) ((Ideal.absNorm w ^ D.m) ^ D.n) ∧ ∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x := by
  intro p _ D R _ b N S s o w hw
  obtain ⟨g, e, 𝔟, hg0, he, hf, hmul, hp⟩ := GlobalTheory.T.exists_coprime_ideal_mul_eq_span_numberField D.F p (Fact.out) w hw
  have hI2 := fun c hc => GlobalTheory.T.isIsogenyOfDegree_intAction_harrisTaylor p D R b N S s o c hc
  let ρ := actF o
  have hρ : ∀ c, IsMonHom (ρ.act c) := ρ.hom

  have hgw : g ∈ w * 𝔟 := by rw [hmul]; exact Ideal.mem_span_singleton_self g
  have hgw1 : g ∈ w := Ideal.mul_le_left (I := w) (J := 𝔟) hgw
  have hgw2 : g ∈ 𝔟 := Ideal.mul_le_right (I := w) (J := 𝔟) hgw
  have hw' : w = Ideal.span {g, e} := by
    apply le_antisymm
    · intro a ha
      have hsplit : a = a * (1 - e) + a * e := by ring
      rw [hsplit]
      refine add_mem ?_ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      have h1 : a * (1 - e) ∈ w * 𝔟 := Ideal.mul_mem_mul ha hf
      rw [hmul, Ideal.mem_span_singleton'] at h1
      obtain ⟨t, ht⟩ := h1
      rw [← ht]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.span_le.2 (Set.insert_subset_iff.2 ⟨hgw1, Set.singleton_subset_iff.2 he⟩)
  have h𝔟' : 𝔟 = Ideal.span {g, 1 - e} := by
    apply le_antisymm
    · intro a ha
      have hsplit : a = e * a + a * (1 - e) := by ring
      rw [hsplit]
      refine add_mem ?_ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      have h1 : e * a ∈ w * 𝔟 := Ideal.mul_mem_mul he ha
      rw [hmul, Ideal.mem_span_singleton'] at h1
      obtain ⟨t, ht⟩ := h1
      rw [← ht]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.span_le.2 (Set.insert_subset_iff.2 ⟨hgw2, Set.singleton_subset_iff.2 hf⟩)
  have hcop : w ⊔ 𝔟 = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : 𝓞 D.F) = e + (1 - e) := by ring
    rw [h1]
    exact Submodule.add_mem_sup he hf
  have h𝔟0 : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at hmul
    exact hg0 hmul

  let f₁ : o.A ⟶ o.A ⊗ o.A := lift (ρ.act g) (ρ.act e)
  let f₂ : o.A ⟶ o.A ⊗ o.A := lift (ρ.act g) (ρ.act (1 - e))
  letI := KerGrp.grp f₁
  have h₁ : ∀ (T : Over S) (x : T ⟶ o.A), InSub (pullback.fst f₁ η[o.A ⊗ o.A]) x ↔ KilledBy ρ w x := by
    intro T x; rw [inSub_ker, hw', killedBy_pair]
  have h₂ : ∀ (T : Over S) (x : T ⟶ o.A), InSub (pullback.fst f₂ η[o.A ⊗ o.A]) x ↔ KilledBy ρ 𝔟 x := by
    intro T x; rw [inSub_ker, h𝔟', killedBy_pair]
  have h₃ : ∀ (T : Over S) (x : T ⟶ o.A), InSub (pullback.fst (ρ.act g) η[o.A]) x ↔ KilledBy ρ (w * 𝔟) x := by
    intro T x; rw [inSub_ker, hmul, killedBy_span]; simp
  have d₃ : IsIsogDeg (toUnit (ker (ρ.act g)))
      (Ideal.absNorm w ^ (D.m * D.n) * Ideal.absNorm 𝔟 ^ (D.m * D.n)) := by
    rw [← mul_pow, ← map_mul, hmul, Ideal.absNorm_span_singleton]
    exact (hI2 g hg0).ker
  have d₂ : IsIsogDeg (toUnit (ker f₂)) (Ideal.absNorm 𝔟 ^ (D.m * D.n)) :=
    GlobalTheory.T.isIsogenyDegree_killedBy_primeToP_harrisTaylor p D R b N S s o hI2 𝔟 hp _ (pullback.fst f₂ η[o.A ⊗ o.A]) inferInstance
      (fun T x => by rw [h₂, killedBy_map])
  have hpos : 0 < Ideal.absNorm 𝔟 ^ (D.m * D.n) :=
    pow_pos (Nat.pos_of_ne_zero (fun h => h𝔟0 (Ideal.absNorm_eq_zero_iff.1 h))) _
  have d₁ := GlobalTheory.T.isIsogenyOfDegree_torsion_coprime_ideals_product S o.A (𝓞 D.F) ρ w 𝔟 hcop _ _ _ (pullback.fst f₁ η[o.A ⊗ o.A])
    (pullback.fst f₂ η[o.A ⊗ o.A]) (pullback.fst (ρ.act g) η[o.A]) inferInstance inferInstance inferInstance
    h₁ h₂ h₃ _ _ hpos d₃ d₂
  refine ⟨ker f₁, KerGrp.grp f₁, pullback.fst f₁ η[o.A ⊗ o.A], KerGrp.isMonHom_fst f₁, inferInstance,
    by rw [← pow_mul]; exact d₁, fun T x => by rw [h₁, killedBy_map]⟩

end GlobalTheory.HTTors
end
end
end
