module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.LocalRingCardinality.SpanPowerMembership.Primes
import Formalism.LocalToGlobal.NormalizedHeckeFactors.ChiDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaWildOfTrivialTameCharactersStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldOverPlaceAlgClosureStatement
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameKummerInertiaSurjective
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSubOneLtOfRed
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.GaloisValuations.GlobalA

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityLiftFromResidueField

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.TameLift

theorem valuation_sub_lt_of_redThrough_eq {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {g : ℕ} [Fact g.Prime]
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) {x y : Ω} (hx : x ∈ A) (hy : y ∈ A)
    (h : redThrough A κ x = redThrough A κ y) : A.valuation (x - y) < 1 := by
  unfold redThrough at h
  rw [dite_eq_left hx, dite_eq_left hy] at h
  have h1 := κ.injective h
  have h2 : (⟨x, hx⟩ : A) - ⟨y, hy⟩ ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h1, sub_self]
  have := (A.valuation_lt_one_iff _).1 h2
  simpa using this

theorem exists_lift : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime],
    ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (m : ℕ), 0 < m → ¬ g ∣ m →
    ∀ c : Formalism.CyclotomicNorms.Fbar g, c ^ m = 1 → ∃ μ : Ω, μ ^ m = 1 ∧ redThrough A κ μ = c := by
  intro E Ω _ _ _ _ _ A v hA g hg hgv κ m hm hgm c hc
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : NeZero ((m : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hm.ne'⟩
  have : NeZero m := ⟨hm.ne'⟩

  have hvg : A.valuation (g : Ω) < 1 := by
    have := (hA (g : 𝓞 E)).2 hgv
    simpa using this

  have hvm : ¬ A.valuation (m : Ω) < 1 := by
    intro hlt
    have hcop : Nat.Coprime m g :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hg.out).mpr hgm)
    obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have e : ((u : Ω) * (m : Ω)) + (w : Ω) * (g : Ω) = 1 := by
      have := congrArg (fun z : ℤ => (z : Ω)) huw
      push_cast at this
      exact this
    have hu : A.valuation (u : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A u)
    have hw : A.valuation (w : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A w)
    have h1 : A.valuation ((u : Ω) * (m : Ω)) < 1 := by
      rw [Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le' hu) hlt
    have h2 : A.valuation ((w : Ω) * (g : Ω)) < 1 := by
      rw [Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le' hw) hvg
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [e, Valuation.map_one] at h3
    exact lt_irrefl _ h3
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hζA : ζ ∈ A := mem_of_pow_eq_one A hm hζ.pow_eq_one
  have hr : IsPrimitiveRoot (redThrough A κ ζ) m := by
    refine IsPrimitiveRoot.mk_of_lt _ hm ?_ ?_
    · rw [← redThrough_pow A κ hζA, hζ.pow_eq_one, redThrough_one]
    · intro l hl hlm hrl
      rw [← redThrough_pow A κ hζA, ← redThrough_one A κ] at hrl
      have hv := valuation_sub_lt_of_redThrough_eq A κ (pow_mem hζA l) (one_mem A) hrl
      have heq : ζ ^ l = 1 := eq_of_pow_eq_one A hvm
        (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) (one_pow _) hv
      exact hζ.pow_ne_one_of_pos_of_lt hl.ne' hlm heq
  obtain ⟨i, -, hi⟩ := hr.eq_pow_of_pow_eq_one hc
  refine ⟨ζ ^ i, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · rw [redThrough_pow A κ hζA, hi]

end GlobalTheory.TameLift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityLiftFromResidueFieldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

theorem _root_.GlobalTheory.T.exists_rootOfUnity_lift_from_residueField : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (m : ℕ), 0 < m → ¬ g ∣ m → ∀ c : Formalism.CyclotomicNorms.Fbar g, c ^ m = 1 → ∃ μ : Ω, μ ^ m = 1 ∧ redThrough A κ μ = c := by
  first | exact @GlobalTheory.TameLift.exists_lift | exact GlobalTheory.TameLift.exists_lift | (intros; apply GlobalTheory.TameLift.exists_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameKummerInertiaSurjectiveStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

theorem _root_.GlobalTheory.T.tame_kummer_inertia_surjective : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ (m : ℕ), 0 < m → ¬ g ∣ m → ∀ Y μ : Ω, Y ^ m = ((g : ℕ) : Ω) → μ ^ m = 1 → ∃ σ ∈ Ine (F := E) A, σ Y = μ * Y := by
  first | exact @GlobalTheory.TameKummerInertia.tame_kummer_surj | exact GlobalTheory.TameKummerInertia.tame_kummer_surj | (intros; apply GlobalTheory.TameKummerInertia.tame_kummer_surj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoupledTameInertiaGenerator

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
noncomputable section

open GlobalTheory.TameCoupledEx in
theorem GlobalTheory.TameCoupledEx.exists_coupled_of (hK : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → Nonempty (IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g)) (hL : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (m : ℕ), 0 < m → ¬ g ∣ m → ∀ c : Formalism.CyclotomicNorms.Fbar g, c ^ m = 1 → ∃ μ : Ω, μ ^ m = 1 ∧ redThrough A κ μ = c) (hS : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ (m : ℕ), 0 < m → ¬ g ∣ m → ∀ Y μ : Ω, Y ^ m = ((g : ℕ) : Ω) → μ ^ m = 1 → ∃ σ ∈ Ine (F := E) A, σ Y = μ * Y) (hW : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ τ ∈ Ine (F := E) A, (∀ d, 0 < d → ∃ y : Ω, y ^ (g ^ d - 1) = ((g : ℕ) : Ω) ∧ A.valuation (τ y / y - 1) < 1) → ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ ζ : ℕ → Formalism.CyclotomicNorms.Fbar g, IsGenSys ζ → ∃ κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g, ∃ σ ∈ Ine (F := E) A, TameGenAt A σ ∧ TameCoupled A κ σ ζ := by
  intro E Ω _ _ _ _ _ A v hA g _ hg hg2 ζ hζ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsGalois E Ω := {}
  have hgp : g.Prime := Fact.out
  have hgv : A.valuation ((g : ℕ) : Ω) < 1 := val_g_lt A v hA hg
  have hg0 : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hgp.ne_zero
  obtain ⟨κ⟩ := hK E Ω A v hA g hg
  let D : ℕ → ℕ := fun n => (n + 1).factorial
  have hDpos : ∀ n, 0 < D n := fun n => Nat.factorial_pos _
  have hNpos : ∀ d, 0 < d → 0 < g ^ d - 1 := fun d hd => pow_sub_one_pos hgp hd
  have hgN : ∀ d, 0 < d → ¬ g ∣ g ^ d - 1 := fun d hd => not_dvd_pow_sub_one hgp hd
  have hroot : ∀ n, ∃ r : Ω, r ^ (g ^ D n - 1) = ((g : ℕ) : Ω) := fun n =>
    IsAlgClosed.exists_pow_nat_eq _ (hNpos _ (hDpos n))
  choose r hr using hroot
  have hDdvd : ∀ n, D n ∣ D (n + 1) := fun n => Nat.factorial_dvd_factorial (by omega)
  have hdD : ∀ d, 0 < d → d ∣ D d := fun d hd => Nat.dvd_factorial hd (by omega)
  have hmem : ∀ (σ : G E Ω) {N : ℕ} {y : Ω}, 0 < N → y ^ N = ((g : ℕ) : Ω) → σ y / y ∈ A :=
    fun σ N y hN hy => tameQuot_mem A σ hN hg0 hy
  have hcl : ∀ (x : Ω) (P : Ω → Prop), IsClosed {τ : G E Ω | P (τ x)} := fun x P =>
    ReciprocityTheory.Gal.isClosed_setOf_apply x P
  let T : ℕ → Set (G E Ω) := fun n =>
    (Ine (F := E) A : Set (G E Ω)) ∩ {σ | redThrough A κ (σ (r n) / r n) = ζ (D n)}
  obtain ⟨σ, hσ⟩ : (⋂ n, T n).Nonempty := by
    refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T ?_ ?_ ?_ ?_
    · rintro n σ ⟨hI, hv⟩
      refine ⟨hI, ?_⟩
      show redThrough A κ (σ (r n) / r n) = ζ (D n)
      have hv' : redThrough A κ (σ (r (n + 1)) / r (n + 1)) = ζ (D (n + 1)) := hv
      rw [ratio_descent hgp hgv hI (hDpos n) (hDdvd n) (hr n) (hr (n + 1)),
        redThrough_pow A κ (hmem σ (hNpos _ (hDpos _)) (hr (n + 1))), hv']
      exact (hζ (D n) (hDpos n)).2 (D (n + 1)) (hDdvd n) (hDpos (n + 1))
    · intro n
      have hc : ζ (D n) ^ (g ^ D n - 1) = 1 := by
        rw [← (hζ _ (hDpos n)).1]; exact pow_orderOf_eq_one _
      obtain ⟨μ, hμ, hμc⟩ := hL E Ω A v hA g hg κ _ (hNpos _ (hDpos n)) (hgN _ (hDpos n)) _ hc
      obtain ⟨σ, hσI, hσr⟩ := hS E Ω A v hA g hg hg2 _ (hNpos _ (hDpos n)) (hgN _ (hDpos n)) (r n) μ (hr n) hμ
      refine ⟨σ, hσI, ?_⟩
      show redThrough A κ (σ (r n) / r n) = ζ (D n)
      have hr0 : r n ≠ 0 := ne_zero_of_pow_eq hgp (hNpos _ (hDpos n)) (hr n)
      rw [hσr, mul_div_cancel_right₀ _ hr0, hμc]
    · exact ((ReciprocityTheory.Gal.isClosed_Ine A).inter (hcl (r 0) (fun t => redThrough A κ (t / r 0) = ζ (D 0)))).isCompact
    · intro n
      exact (ReciprocityTheory.Gal.isClosed_Ine A).inter (hcl (r n) (fun t => redThrough A κ (t / r n) = ζ (D n)))
  simp only [Set.mem_iInter] at hσ
  have hσI : σ ∈ Ine (F := E) A := (hσ 0).1
  have hσv : ∀ n, redThrough A κ (σ (r n) / r n) = ζ (D n) := fun n => (hσ n).2
  refine ⟨κ, σ, hσI, ⟨hσI, ?_⟩, ?_⟩
  · intro τ hτ
    have hτI : τ ∈ Ine (F := E) A := hτ
    let Z : Set (G E Ω) := closure (Subgroup.zpowers σ : Set (G E Ω))
    have hZI : Z ⊆ Ine (F := E) A := closure_minimal (fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx; exact zpow_mem hσI k) (ReciprocityTheory.Gal.isClosed_Ine A)
    let U : ℕ → Set (G E Ω) := fun n =>
      Z ∩ {h | redThrough A κ (h (r n) / r n) = redThrough A κ (τ (r n) / r n)}
    obtain ⟨h, hh⟩ : (⋂ n, U n).Nonempty := by
      refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed U ?_ ?_ ?_ ?_
      · rintro n x ⟨hxZ, hx⟩
        refine ⟨hxZ, ?_⟩
        show redThrough A κ (x (r n) / r n) = redThrough A κ (τ (r n) / r n)
        have hx' : redThrough A κ (x (r (n + 1)) / r (n + 1)) = redThrough A κ (τ (r (n + 1)) / r (n + 1)) := hx
        rw [ratio_descent hgp hgv (hZI hxZ) (hDpos n) (hDdvd n) (hr n) (hr (n + 1)),
          ratio_descent hgp hgv hτI (hDpos n) (hDdvd n) (hr n) (hr (n + 1)),
          redThrough_pow A κ (hmem x (hNpos _ (hDpos _)) (hr (n + 1))),
          redThrough_pow A κ (hmem τ (hNpos _ (hDpos _)) (hr (n + 1))), hx']
      · intro n
        have hN := hNpos _ (hDpos n)
        haveI : NeZero (g ^ D n - 1) := ⟨hN.ne'⟩
        have hprim : IsPrimitiveRoot (ζ (D n)) (g ^ D n - 1) := (hζ _ (hDpos n)).1 ▸ IsPrimitiveRoot.orderOf _
        have hc : (redThrough A κ (τ (r n) / r n)) ^ (g ^ D n - 1) = 1 := by
          rw [← redThrough_pow A κ (hmem τ hN (hr n)), tameQuot_pow τ hg0 (hr n), redThrough_one]
        obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one hc
        refine ⟨σ ^ j, subset_closure (Subgroup.mem_zpowers_iff.2 ⟨(j : ℤ), by simp⟩), ?_⟩
        show redThrough A κ ((σ ^ j) (r n) / r n) = _
        rw [ratio_pow hgp hgv hσI hN (hgN _ (hDpos n)) (hr n), redThrough_pow A κ (hmem σ hN (hr n)), hσv n, hj]
      · exact (isClosed_closure.inter (hcl (r 0)
          (fun t => redThrough A κ (t / r 0) = redThrough A κ (τ (r 0) / r 0)))).isCompact
      · intro n
        exact isClosed_closure.inter (hcl (r n)
          (fun t => redThrough A κ (t / r n) = redThrough A κ (τ (r n) / r n)))
    simp only [Set.mem_iInter] at hh
    have hhZ : h ∈ Z := (hh 0).1
    have hhI := hZI hhZ
    have hhv : ∀ n, redThrough A κ (h (r n) / r n) = redThrough A κ (τ (r n) / r n) := fun n => (hh n).2
    have hρI : h⁻¹ * τ ∈ Ine (F := E) A := mul_mem (inv_mem hhI) hτI
    have hρW : ∀ y : Ω, y ≠ 0 → A.valuation ((h⁻¹ * τ) y / y - 1) < 1 := by
      refine hW E Ω A v hA g hg _ hρI ?_
      intro d hd
      have hN := hNpos _ (hDpos d)
      refine ⟨r d ^ ((g ^ D d - 1) / (g ^ d - 1)), root_down (hdD d hd) (hr d), ?_⟩
      apply val_sub_one_lt_of_red κ (hmem _ (hNpos _ hd) (root_down (hdD d hd) (hr d)))
      rw [ratio_descent hgp hgv hρI hd (hdD d hd) (root_down (hdD d hd) (hr d)) (hr d),
        redThrough_pow A κ (hmem _ hN (hr d))]
      have e1 : (h * (h⁻¹ * τ)) (r d) / r d = (h (r d) / r d) * ((h⁻¹ * τ) (r d) / r d) :=
        ratio_mul hgp hgv hhI _ hN (hgN _ (hDpos d)) (hr d)
      rw [mul_inv_cancel_left] at e1
      have e2 := congrArg (redThrough A κ) e1
      rw [redThrough_mul A κ (hmem h hN (hr d)) (hmem _ hN (hr d)), ← hhv d] at e2
      have hne : redThrough A κ (h (r d) / r d) ≠ 0 := by
        intro h0
        have : (redThrough A κ (h (r d) / r d)) ^ (g ^ D d - 1) = 1 := by
          rw [← redThrough_pow A κ (hmem h hN (hr d)), tameQuot_pow h hg0 (hr d), redThrough_one]
        rw [h0, zero_pow hN.ne'] at this
        exact zero_ne_one this
      have e3 : redThrough A κ ((h⁻¹ * τ) (r d) / r d) = 1 :=
        (mul_eq_left₀ hne).1 e2.symm
      rw [e3, one_pow]
    set C : Subgroup (G E Ω) :=
      Subgroup.closure (insert σ {σ' : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ' y / y - 1) < 1}) with hC
    have h1 : h ∈ C.topologicalClosure := by
      refine closure_mono ?_ hhZ
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact zpow_mem (Subgroup.subset_closure (Set.mem_insert _ _) : σ ∈ C) k
    have h2 : h⁻¹ * τ ∈ C := Subgroup.subset_closure (Set.mem_insert_of_mem _ hρW)
    have h3 := C.topologicalClosure.mul_mem h1 (C.le_topologicalClosure h2)
    rw [mul_inv_cancel_left] at h3
    exact h3
  · intro d hd y hy
    rw [ratio_descent hgp hgv hσI hd (hdD d hd) hy (hr d),
      redThrough_pow A κ (hmem σ (hNpos _ (hDpos d)) (hr d)), hσv d]
    exact (hζ d hd).2 (D d) (hdD d hd) (hDpos d)

theorem GlobalTheory.TameCoupledEx.exists_coupled_tame_generator : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ ζ : ℕ → Formalism.CyclotomicNorms.Fbar g, IsGenSys ζ → ∃ κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g, ∃ σ ∈ Ine (F := E) A, TameGenAt A σ ∧ TameCoupled A κ σ ζ :=
  GlobalTheory.TameCoupledEx.exists_coupled_of GlobalTheory.T.residue_field_over_place_alg_closure GlobalTheory.T.exists_rootOfUnity_lift_from_residueField GlobalTheory.T.tame_kummer_inertia_surjective GlobalTheory.T.inertia_wild_of_trivial_tame_characters
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoupledTameInertiaGeneratorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

theorem _root_.GlobalTheory.T.exists_coupled_tame_inertia_generator : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ ζ : ℕ → Formalism.CyclotomicNorms.Fbar g, IsGenSys ζ → ∃ κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g, ∃ σ ∈ Ine (F := E) A, TameGenAt A σ ∧ TameCoupled A κ σ ζ := by
  first | exact @GlobalTheory.TameCoupledEx.exists_coupled_tame_generator | exact GlobalTheory.TameCoupledEx.exists_coupled_tame_generator | (intros; apply GlobalTheory.TameCoupledEx.exists_coupled_tame_generator <;> assumption)
end
end
