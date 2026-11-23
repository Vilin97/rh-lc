module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqOneAddOfSq

section

@[expose] public section

set_option autoImplicit false

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

namespace GlobalTheory.AnPer

theorem dpExp_eq_one_add_of_sq {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type}
    [CommRing C] {J : Ideal C} (δ : DividedPowers J) (ρ : Hol W →+* C) {x : C} (hx : x ∈ J)
    (hx2 : x * x = 0) : dpExp δ x = 1 + x := by
  have hv : ∀ n, 2 ≤ n → δ.dpow n x = 0 := by
    intro n hn
    have hu : IsUnit ((n.factorial : ℕ) : C) := by
      have h1 : IsUnit ((n.factorial : ℕ) : Hol W) := by
        rw [← map_natCast (algebraMap ℂ (Hol W))]
        exact (IsUnit.mk0 _ (by exact_mod_cast (Nat.factorial_ne_zero n))).map _
      simpa using h1.map ρ
    have hp : x ^ n = 0 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add, sq, hx2, zero_mul]
    have := δ.factorial_mul_dpow_eq_pow hx (n := n)
    rw [hp] at this
    exact (hu.mul_right_eq_zero).1 this
  rw [dpExp_eq_sum_range_of_vanish δ x 2 hv]
  simp [Finset.sum_range_succ, δ.dpow_zero hx, δ.dpow_one hx]

theorem step_exp {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type} [CommRing C]
    {J : Ideal C} {ρ ρ' : Hol W →+* C} (s : Step J ρ ρ') (e l : Hol W)
    (he : ∀ a, dw a e = dw a l * e) :
    ρ' l - ρ l ∈ J ∧ (ρ' l - ρ l) * (ρ' l - ρ l) = 0 ∧ ρ' e = ρ e * (1 + (ρ' l - ρ l)) := by
  obtain ⟨n, h1, h2, h3⟩ := s
  have hx : ρ' l - ρ l = ∑ a, ρ (dw a l) * n a := by rw [h3 l]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hx]; exact J.sum_mem fun a _ ↦ J.mul_mem_left _ (h1 a)
  · rw [hx, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ ?_
    rw [mul_mul_mul_comm, h2, mul_zero]
  · rw [hx, h3 e, mul_add, mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [he, map_mul]; ring

theorem close_exp : ∀ {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type} [CommRing C]
    (J : Ideal C) (δ : DividedPowers J), IsNilDP δ → ∀ (ρ₁ ρ₂ : Hol W →+* C) (e l : Hol W),
    (∀ a, dw a e = dw a l * e) → Close J ρ₁ ρ₂ → ρ₂ e = ρ₁ e * dpExp δ (ρ₂ l - ρ₁ l) := by
  intro I _ g W C _ J δ hδ ρ₁ ρ₂ e l he hc
  induction hc with
  | refl => rw [sub_self, dpExp_zero, mul_one]
  | @tail ρ ρ' hc' s ih =>
    obtain ⟨hxJ, hx2, hρ'⟩ := step_exp s e l he
    have hyJ : ρ l - ρ₁ l ∈ J := Close.sub_mem hc' l
    rw [show ρ' l - ρ₁ l = (ρ l - ρ₁ l) + (ρ' l - ρ l) by ring,
      hδ.dpExp_add_eq_mul hyJ hxJ, dpExp_eq_one_add_of_sq δ ρ₁ hxJ hx2, hρ', ih, mul_assoc]

end GlobalTheory.AnPer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCocycleCohomologous

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem log_cocycle_cohomologous : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (a lg : Λ → ∀ k, Hol (K.W k)) (β : Λ → Λ → Hol F.V), (∀ l k, IsUnit (a l k)) → (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) → (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') → (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (β l m)) → (∀ l m k, lg (l + m) k = lg l k + lg m k) → ∀ (e : ∀ T : K.Obj, (T.C)ˣ) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C), (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J) → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ (ℓ T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) → ∃ c : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ = (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg) := by

  intro I _ g Λ _ F K a lg β ha hdw hsh hlgsh hlgadd e uu ℓ huu hℓ
  have hnil : ∀ T : K.Obj, IsNilDP T.δ := fun T ↦ by letI := T.ratAlg; exact isPDNilpotent_of_rat _ T.nil
  have hdp : ∀ {T T' : K.Obj} (ψ : T ⟶ T'), DividedPowers.IsDPMorphism T.δ T'.δ (ψ.φ : T.C →+* T'.C) := fun {T T'} ψ ↦ by
    letI := T'.ratAlg; exact isDPMorphism_of_rat T.δ T'.δ (ψ.φ : T.C →+* T'.C) ψ.mem
  have hw : ∀ (T T' : K.Obj) (φ : T ⟶ T'), ∃ n ∈ T'.J, dpExp T'.δ n =
      uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) * (((e T')⁻¹ : (T'.C)ˣ) : T'.C) := by
    intro T T' φ
    have hm : uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) * (((e T')⁻¹ : (T'.C)ˣ) : T'.C) - 1 ∈ T'.J := by
      have := T'.J.mul_mem_right (((e T')⁻¹ : (T'.C)ˣ) : T'.C) (huu T T' φ)
      convert this using 1
      rw [sub_mul, Units.mul_inv]
    obtain ⟨x, hx, hx'⟩ := (GlobalTheory.Cris.ExpBij.dpExp_bijOn T'.C T'.J T'.δ (hnil T')).surjOn hm
    exact ⟨x, hx, hx'⟩
  choose n hnJ hn using hw
  refine ⟨fun T T' φ ↦ (n T T' φ - T'.ρ (lg φ.deg T'.k) : T'.C), ?_⟩
  intro T T' T'' φ ψ
  obtain ⟨hℓJ, hℓe⟩ := hℓ T T' T'' φ ψ
  have hce := close_exp T''.J T''.δ (hnil T'') _ _ (a φ.deg T'.k) (lg φ.deg T'.k) (hdw φ.deg T'.k) ψ.close
  have hxJ := ψ.close.sub_mem (lg φ.deg T'.k)
  simp only [RingHom.comp_apply, AlgHom.coe_toRingHom] at hce hxJ
  have hnat : ∀ c ∈ T'.J, ψ.φ (dpExp T'.δ c) = dpExp T''.δ (ψ.φ c) := fun c hc ↦
    (dpExp_add_and_natural _ _ _ _ T'.δ T''.δ (hnil T')).2 _ (hdp ψ) c hc
  have hadd := (dpExp_add_and_natural _ _ _ _ T''.δ T''.δ (hnil T'')).1
  have hQ : ψ.φ (((e T')⁻¹ : (T'.C)ˣ) : T'.C) * ψ.φ (e T' : T'.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have haa : T''.ρ (a (φ ≫ ψ).deg T''.k) = T''.ρ (Charts.sh (Charts.Hom.le ψ) (a φ.deg T'.k)) * T''.ρ (a ψ.deg T''.k) := by
    rw [Charts.comp_deg, hsh _ _ _ _ (Charts.Hom.le ψ), map_mul]
  have hn1 := hn T T'' (φ ≫ ψ)
  have hn2 := hn T T' φ
  have hn3 := hn T' T'' ψ
  rw [Charts.comp_φ, haa] at hn1
  set x := ψ.φ (T'.ρ (lg φ.deg T'.k)) - T''.ρ (Charts.sh (Charts.Hom.le ψ) (lg φ.deg T'.k)) with hx
  have key : dpExp T''.δ (ℓ T T' T'' φ ψ + n T T'' (φ ≫ ψ) + x) = dpExp T''.δ (ψ.φ (n T T' φ) + n T' T'' ψ) := by
    rw [hadd _ (T''.J.add_mem hℓJ (hnJ _ _ _)) _ hxJ, hadd _ hℓJ _ (hnJ _ _ _),
      hadd _ (ψ.mem _ (hnJ _ _ _)) _ (hnJ _ _ _), ← hnat _ (hnJ _ _ _), hn1, hn2, hn3]
    simp only [map_mul]
    linear_combination (ψ.φ (φ.φ (e T : T.C)) * T''.ρ (Charts.sh (Charts.Hom.le ψ) (a φ.deg T'.k)) * T''.ρ (a ψ.deg T''.k) *
        (((e T'')⁻¹ : (T''.C)ˣ) : T''.C) * dpExp T''.δ x) * hℓe
      - (ψ.φ (uu T T' φ) * ψ.φ (φ.φ (e T : T.C)) * ψ.φ (((e T')⁻¹ : (T'.C)ˣ) : T'.C) * uu T' T'' ψ * ψ.φ (e T' : T'.C) *
        T''.ρ (a ψ.deg T''.k) * (((e T'')⁻¹ : (T''.C)ˣ) : T''.C)) * hce
      - (ψ.φ (uu T T' φ) * uu T' T'' ψ * ψ.φ (φ.φ (e T : T.C)) * T''.ρ (Charts.sh (Charts.Hom.le ψ) (a φ.deg T'.k)) *
        T''.ρ (a ψ.deg T''.k) * (((e T'')⁻¹ : (T''.C)ˣ) : T''.C) * dpExp T''.δ x) * hQ
  have hinj := (GlobalTheory.Cris.ExpBij.dpExp_bijOn T''.C T''.J T''.δ (hnil T'')).injOn
    (T''.J.add_mem (T''.J.add_mem hℓJ (hnJ _ _ _)) hxJ) (T''.J.add_mem (ψ.mem _ (hnJ _ _ _)) (hnJ _ _ _)) key
  have hb : T''.ρ (Charts.sh (Charts.Hom.le ψ) (lg φ.deg T'.k)) = T''.ρ (lg φ.deg T''.k) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg) := by
    rw [hlgsh _ _ _ _ (Charts.Hom.le ψ), T''.ρ.map_add, T''.ρ_cst]
  show ℓ T T' T'' φ ψ = (ψ.φ (n T T' φ - T'.ρ (lg φ.deg T'.k)) - (n T T'' (φ ≫ ψ) - T''.ρ (lg (φ ≫ ψ).deg T''.k)) +
    (n T' T'' ψ - T''.ρ (lg ψ.deg T''.k))) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg)
  rw [Charts.comp_deg, hlgadd, map_sub, T''.ρ.map_add]
  rw [hx, hb] at hinj
  linear_combination hinj

end GlobalTheory.AnPer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCocycleCohomologousStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.log_cocycle_cohomologous_alt : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (a lg : Λ → ∀ k, Hol (K.W k)) (β : Λ → Λ → Hol F.V), (∀ l k, IsUnit (a l k)) → (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) → (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') → (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (β l m)) → (∀ l m k, lg (l + m) k = lg l k + lg m k) → ∀ (e : ∀ T : K.Obj, (T.C)ˣ) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C), (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J) → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ (ℓ T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) → ∃ c : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ = (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg) := by
  first | exact @GlobalTheory.AnPer.log_cocycle_cohomologous | exact GlobalTheory.AnPer.log_cocycle_cohomologous | (intros; apply GlobalTheory.AnPer.log_cocycle_cohomologous <;> assumption)
end
end
