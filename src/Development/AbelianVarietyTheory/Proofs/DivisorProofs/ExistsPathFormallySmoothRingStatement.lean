module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.RingHom.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivCompM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoublingJetSuccOfLift
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsRingHomModXPowSuccLiftStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoublingJetSuccOfLiftStatement

section

@[expose] public section

open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.exists_doublingJet_succ_of_lift : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [Algebra ℚ R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → ∀ n : ℕ, 2 ≤ n → ∀ φ ψ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsJet π ε m β δ n φ → GlobalTheory.Nef.PathJet.IsRingHomMod π β (n + 1) ψ → (∀ f, (PowerSeries.X : PowerSeries R) ^ n ∣ ψ f - φ f) → ∃ ψ' : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsJet π ε m β δ (n + 1) ψ' ∧ ∀ f, (PowerSeries.X : PowerSeries R) ^ n ∣ ψ' f - φ f := by
  first | exact @GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift | exact GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift | (intros; apply GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomLimitOfDoublingJets

section

@[expose] public section

open GlobalTheory.Nef

namespace GlobalTheory.Nef.PathJet

open PowerSeries

theorem limit_of_jets (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A)
    (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R) (φ : ℕ → A → PowerSeries R)
    (hφ : ∀ n, IsJet π ε m β δ (n + 2) (φ n))
    (hc : ∀ n f, (X : PowerSeries R) ^ (n + 2) ∣ φ (n + 1) f - φ n f) :
    ∃ γ : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β ∧
      PowerSeries.constantCoeff.comp γ = β.comp ε ∧ (∀ f, PowerSeries.coeff 1 (γ f) = δ f) ∧
      (PowerSeries.rescale 2).comp γ = γ.comp m := by

  have hdv : ∀ (n : ℕ) (p q : PowerSeries R), (X : PowerSeries R) ^ n ∣ p - q →
      ∀ k, k < n → coeff k p = coeff k q := by
    intro n p q h k hk
    have := (PowerSeries.X_pow_dvd_iff.mp h) k hk
    rwa [map_sub, sub_eq_zero] at this

  have hstab : ∀ f k j, k ≤ j + 1 → coeff k (φ j f) = coeff k (φ k f) := by
    intro f k j hkj
    rcases Nat.lt_or_ge j k with h | h
    · have hk : k = j + 1 := by omega
      subst hk
      exact (hdv _ _ _ (hc j f) (j + 1) (by omega)).symm
    · induction j, h using Nat.le_induction with
      | base => rfl
      | succ j hj ih =>
        rw [hdv _ _ _ (hc j f) k (by omega)]
        exact ih (by omega)
  let g : A → PowerSeries R := fun f => PowerSeries.mk fun k => coeff k (φ k f)
  have hg : ∀ f k j, k ≤ j + 1 → coeff k (g f) = coeff k (φ j f) := by
    intro f k j hkj
    simp only [g, PowerSeries.coeff_mk]
    exact (hstab f k j hkj).symm
  have gmul : ∀ f h, g (f * h) = g f * g h := by
    intro f h; ext k
    rw [hg _ k k (by omega), hdv _ _ _ ((hφ k).1.1 f h) k (by omega), coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [hg f x.1 k (by omega), hg h x.2 k (by omega)]
  have gadd : ∀ f h, g (f + h) = g f + g h := by
    intro f h; ext k
    rw [hg _ k k (by omega), hdv _ _ _ ((hφ k).1.2.1 f h) k (by omega), map_add (f := _), map_add (f := _),
      hg f k k (by omega), hg h k k (by omega)]
  have gone : g 1 = 1 := by
    ext k
    rw [hg _ k k (by omega), hdv _ _ _ (hφ k).1.2.2.1 k (by omega)]
  have gzero : g 0 = 0 := by
    have := gadd 0 0
    rw [add_zero] at this
    linear_combination -this
  let γ : A →+* PowerSeries R :=
    { toFun := g, map_one' := gone, map_mul' := gmul, map_zero' := gzero, map_add' := gadd }
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · ext b k
    show coeff k (g (π b)) = coeff k (C (β b))
    rw [hg _ k k (by omega), hdv _ _ _ ((hφ k).1.2.2.2 b) k (by omega)]
  · ext f
    show constantCoeff (g f) = β (ε f)
    rw [← coeff_zero_eq_constantCoeff_apply, hg f 0 0 (by omega), coeff_zero_eq_constantCoeff_apply,
      (hφ 0).2.2.1 f]
  · intro f
    show coeff 1 (g f) = δ f
    rw [hg f 1 0 (by omega), (hφ 0).2.2.2 f]
  · ext f k
    show coeff k (rescale 2 (g f)) = coeff k (g (m f))
    rw [coeff_rescale, hg f k k (by omega), hg (m f) k k (by omega),
      hdv _ _ _ ((hφ k).2.1 f) k (by omega), coeff_rescale]

end GlobalTheory.Nef.PathJet
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomLimitOfDoublingJetsStatement

section

@[expose] public section

open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.exists_ringHom_limit_of_doublingJets : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ∀ φ : ℕ → A → PowerSeries R, (∀ n, GlobalTheory.Nef.PathJet.IsJet π ε m β δ (n + 2) (φ n)) → (∀ n f, (PowerSeries.X : PowerSeries R) ^ (n + 2) ∣ φ (n + 1) f - φ n f) → ∃ γ : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β ∧ PowerSeries.constantCoeff.comp γ = β.comp ε ∧ (∀ f, PowerSeries.coeff 1 (γ f) = δ f) ∧ (PowerSeries.rescale 2).comp γ = γ.comp m := by
  first | exact @GlobalTheory.Nef.PathJet.limit_of_jets | exact GlobalTheory.Nef.PathJet.limit_of_jets | (intros; apply GlobalTheory.Nef.PathJet.limit_of_jets <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDoublingJetOfOrderTwoFirstOrder

section

@[expose] public section

open GlobalTheory.Nef

namespace GlobalTheory.Nef.PathJet

open PowerSeries

theorem firstOrder_isJet : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → GlobalTheory.Nef.PathJet.IsJet π ε m β δ 2 (fun f => PowerSeries.C (β (ε f)) + PowerSeries.C (δ f) * PowerSeries.X) := by
  intro A B R _ _ _ π ε m β δ hεπ hmπ hεm hm2 hδ hδπ
  have hεπ' : ∀ b, ε (π b) = b := fun b => by rw [← RingHom.comp_apply, hεπ, RingHom.id_apply]
  have hεm' : ∀ f, ε (m f) = ε f := fun f => by rw [← RingHom.comp_apply, hεm]
  have hδ1 : δ 1 = 0 := by
    have h := hδ 1 1
    simp only [mul_one, map_one, one_mul] at h
    have : δ 1 + δ 1 = δ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  have hdm : ∀ f, δ (m f) = 2 * δ f :=
    deriv_comp_m π ε m β δ hεπ hmπ hm2 hδ hδπ
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro f g
    refine ⟨C (-(δ f * δ g)), ?_⟩
    beta_reduce
    rw [hδ, map_mul, map_mul]
    simp only [map_add (f := _), map_mul, map_neg]
    ring
  · intro f g
    simp [map_add (f := _)]
    exact ⟨0, by ring⟩
  · simp [hδ1]
  · intro b
    simp [hεπ', hδπ]
  · intro f
    refine ⟨0, ?_⟩
    beta_reduce
    rw [hεm', hdm]
    have hrC : ∀ x : R, rescale (2 : R) (C x) = C x := by
      intro x; ext n; rw [coeff_rescale, coeff_C]; split_ifs with h <;> simp [h]
    simp only [map_add (f := _), map_mul, rescale_X, hrC]
    ring
  · intro f
    simp
  · intro f
    simp [coeff_C, coeff_C_mul, coeff_X]

end GlobalTheory.Nef.PathJet
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDoublingJetOfOrderTwoFirstOrderStatement

section

@[expose] public section

open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.isDoublingJetOfOrder_two_firstOrder : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → GlobalTheory.Nef.PathJet.IsJet π ε m β δ 2 (fun f => PowerSeries.C (β (ε f)) + PowerSeries.C (δ f) * PowerSeries.X) := by
  first | exact @GlobalTheory.Nef.PathJet.firstOrder_isJet | exact GlobalTheory.Nef.PathJet.firstOrder_isJet | (intros; apply GlobalTheory.Nef.PathJet.firstOrder_isJet <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPathFormallySmoothRing

section

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem exists_path_ring : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [Algebra ℚ R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), π.FormallySmooth → ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → ∃ γ : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β ∧ PowerSeries.constantCoeff.comp γ = β.comp ε ∧ (∀ f, PowerSeries.coeff 1 (γ f) = δ f) ∧ (PowerSeries.rescale 2).comp γ = γ.comp m := by
  intro A B R _ _ _ _ π ε m β δ hsm hεπ hmπ hεm hm2 hδ hδπ
  have step : ∀ n : ℕ, ∀ φ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsJet π ε m β δ (n + 2) φ →
      ∃ ψ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsJet π ε m β δ (n + 2 + 1) ψ ∧
        ∀ f, (PowerSeries.X : PowerSeries R) ^ (n + 2) ∣ ψ f - φ f := by
    intro n φ hφ
    obtain ⟨ψ, hψ, hψφ⟩ := GlobalTheory.T.exists_isRingHomModXPow_succ_lift A B R π β hsm (n + 2) (by omega) φ hφ.1
    exact GlobalTheory.T.exists_doublingJet_succ_of_lift A B R π ε m β δ hεπ hmπ hεm hm2 hδ hδπ (n + 2) (by omega) φ ψ hφ hψ hψφ
  choose F hF hFφ using step
  let seq : (n : ℕ) → {φ : A → PowerSeries R // GlobalTheory.Nef.PathJet.IsJet π ε m β δ (n + 2) φ} :=
    fun n => Nat.rec ⟨_, GlobalTheory.T.isDoublingJetOfOrder_two_firstOrder A B R π ε m β δ hεπ hmπ hεm hm2 hδ hδπ⟩
      (fun k s => ⟨F k s.1 s.2, hF k s.1 s.2⟩) n
  exact GlobalTheory.T.exists_ringHom_limit_of_doublingJets A B R π ε m β δ (fun n => (seq n).1) (fun n => (seq n).2)
    (fun n f => hFφ n (seq n).1 (seq n).2 f)

end GlobalTheory.Nef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPathFormallySmoothRingStatement

section

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.exists_path_formallySmooth_ring : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [Algebra ℚ R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), π.FormallySmooth → ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → ∃ γ : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β ∧ PowerSeries.constantCoeff.comp γ = β.comp ε ∧ (∀ f, PowerSeries.coeff 1 (γ f) = δ f) ∧ (PowerSeries.rescale 2).comp γ = γ.comp m := by
  first | exact @GlobalTheory.Nef.exists_path_ring | exact GlobalTheory.Nef.exists_path_ring | (intros; apply GlobalTheory.Nef.exists_path_ring <;> assumption)
end
end
