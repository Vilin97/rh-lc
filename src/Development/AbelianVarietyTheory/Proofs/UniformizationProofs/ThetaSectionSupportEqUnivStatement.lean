module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.Finiteness.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Ring.Int.Field
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.SimpleModule.Basic
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOneDimStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleSectionsTorusTorsionWeightSpacesStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionFamilyNeZeroIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaExpansionSupportNotInPrimeIndexSubgroup
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSupportPairIffDegreeTwoSumDiff

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPrimeHomZmodOfNeTop

section

@[expose] public section

namespace GlobalTheory

theorem exists_prime_hom_zmod_of_ne_top (X : Type) [AddCommGroup X] [Module.Finite ℤ X]
    (Λ : AddSubgroup X) (h : Λ ≠ ⊤) :
    ∃ l : ℕ, l.Prime ∧ ∃ f : X →+ ZMod l, f ≠ 0 ∧ ∀ x ∈ Λ, f x = 0 := by
  have h1 : (AddSubgroup.toIntSubmodule Λ) ≠ ⊤ := by
    intro h'
    apply h
    ext x
    have : x ∈ AddSubgroup.toIntSubmodule Λ := by rw [h']; trivial
    exact ⟨fun _ => trivial, fun _ => this⟩
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (AddSubgroup.toIntSubmodule Λ)).resolve_left h1
  have hs : IsSimpleModule ℤ (X ⧸ M) := isSimpleModule_iff_isCoatom.mpr hM
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
  obtain ⟨n, hn⟩ := (IsPrincipalIdealRing.principal I).principal
  have hn' : I = Ideal.span {((n.natAbs : ℕ) : ℤ)} := by
    rw [Int.span_natAbs]; exact hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hb : I = ⊥ := by simpa using hn
    exact Ring.ne_bot_of_isMaximal_of_not_isField hI Int.not_isField hb
  have hp : (n.natAbs).Prime := by
    have := hI.isPrime
    rw [hn'] at this
    have h2 := (Ideal.span_singleton_prime (by simpa using hn0)).mp this
    exact Nat.prime_iff_prime_int.mpr h2
  let g : (ℤ ⧸ I) ≃+* ZMod n.natAbs :=
    (Ideal.quotEquivOfEq hn').trans (Int.quotientSpanNatEquivZMod n.natAbs)
  refine ⟨n.natAbs, hp, g.toAddMonoidHom.comp (e.toLinearMap.toAddMonoidHom.comp M.mkQ.toAddMonoidHom), ?_, ?_⟩
  · intro h0
    apply hM.1
    rw [eq_top_iff]
    intro x _
    have hx : g (e (M.mkQ x)) = 0 := DFunLike.congr_fun h0 x
    rw [map_eq_zero_iff _ g.injective, map_eq_zero_iff _ e.injective] at hx
    exact (Submodule.Quotient.mk_eq_zero M).mp hx
  · intro x hx
    have : M.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero M).mpr (hle hx)
    change g (e (M.mkQ x)) = 0
    rw [this, map_zero, map_zero]

theorem support_subgroup_odd_index :
    ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (S S₂ : Set X), S.Nonempty → (∀ a b, (a ∈ S ∧ b ∈ S) ↔ (a + b ∈ S₂ ∧ a - b ∈ S₂)) → (∀ x : X, ∃ z : X, x + (z + z) ∈ S₂) → S₂ = S ∧ ∃ Λ : AddSubgroup X, (Λ : Set X) = S ∧ (Λ = ⊤ ∨ ∃ l : ℕ, l.Prime ∧ Odd l ∧ ∃ f : X →+ ZMod l, f ≠ 0 ∧ ∀ x ∈ Λ, f x = 0) := by
  intro X _ _ S S₂ ⟨a, ha⟩ h hd
  have h02 : (0 : X) ∈ S₂ := by simpa using ((h a a).mp ⟨ha, ha⟩).2
  have h0 : (0 : X) ∈ S := ((h 0 0).mpr ⟨by simpa using h02, by simpa using h02⟩).1
  have heq : S₂ = S := by
    ext x
    have := h x 0
    simp only [add_zero, sub_zero, and_self, h0, and_true] at this
    exact this.symm
  subst heq
  refine ⟨rfl, ?_⟩
  let Λ : AddSubgroup X :=
    { carrier := S₂
      zero_mem' := h0
      add_mem' := fun {a b} ha hb => ((h a b).mp ⟨ha, hb⟩).1
      neg_mem' := fun {b} hb => by simpa using ((h 0 b).mp ⟨h0, hb⟩).2 }
  refine ⟨Λ, rfl, ?_⟩
  by_cases ht : Λ = ⊤
  · exact Or.inl ht
  · right
    obtain ⟨l, hl, f, hf, hΛ⟩ := exists_prime_hom_zmod_of_ne_top X Λ ht
    refine ⟨l, hl, ?_, f, hf, hΛ⟩
    refine hl.odd_of_ne_two ?_
    rintro rfl
    apply hf
    ext x
    obtain ⟨z, hz⟩ := hd x
    have h1 := hΛ _ hz
    have h2 : f z + f z = 0 := CharTwo.add_self_eq_zero _
    rw [map_add (f := _), map_add (f := _), h2, add_zero] at h1
    simpa using h1

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaExpansionSupportNotInPrimeIndexSubgroupStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.thetaExpansion_support_not_in_primeIndex_subgroup : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (l : ℕ), l.Prime → ∀ g : D.X →+ ZMod l, (∀ α, (∃ j, (f α).f j ≠ 0) → g α = 0) → g = 0) := by
  first | exact @GlobalTheory.UU.PrimeIndex.hom_zmod_eq_zero_of_support | exact GlobalTheory.UU.PrimeIndex.hom_zmod_eq_zero_of_support | (intros; apply GlobalTheory.UU.PrimeIndex.hom_zmod_eq_zero_of_support <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSupportPairIffDegreeTwoSumDiffStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.thetaSupport_pair_iff_degreeTwo_sum_diff : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ a b : D.X, ((∃ j, (f a).f j ≠ 0) ∧ ∃ j, (f b).f j ≠ 0) ↔ (U.Supp (Kbar V) 2 (a + b) ∧ U.Supp (Kbar V) 2 (a - b))) := by
  first | exact @GlobalTheory.UU.SuppRel.supp_rel | exact GlobalTheory.UU.SuppRel.supp_rel | (intros; apply GlobalTheory.UU.SuppRel.supp_rel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSectionSupportEqUniv

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.UU

theorem theta_support_eq_univ : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∀ α, ∃ j, (f α).f j ≠ 0) ∧ ∀ α, U.Supp (Kbar V) 2 α) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U θ f hθ
  have hrel := GlobalTheory.T.thetaSupport_pair_iff_degreeTwo_sum_diff h1 h2 V hV D A G U θ f hθ
  have hodd := GlobalTheory.T.thetaExpansion_support_not_in_primeIndex_subgroup h1 h2 V hV D A G U θ f hθ
  have hw := GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces h1 h2 V hV D A G U
  have hpull := GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1
  obtain ⟨th, hth, -⟩ := hpull.1 θ
  obtain ⟨s₀, hs₀, -⟩ := hpull.2 f
  have hone := (GlobalTheory.T.expF_of_theta_degree_one h1 h2 V hV D A G U θ f hθ th s₀ hth hs₀).2.2
  have hne : ({α | ∃ j, (f α).f j ≠ 0} : Set D.X).Nonempty := by
    obtain ⟨mu, t, s, hts, j, hj⟩ := (hw 1 le_rfl).2.1 0
    obtain ⟨c, hc⟩ := hone t s hts
    refine ⟨0 + 1 • mu, (_root_.GlobalTheory.pullB_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ _).1 ⟨j, fun h0 => hj ?_⟩⟩
    rw [hc, h0, mul_zero]
  obtain ⟨hS, Λ, hΛ, hc⟩ := GlobalTheory.support_subgroup_odd_index D.X {α | ∃ j, (f α).f j ≠ 0}
    {α | U.Supp (Kbar V) 2 α} hne hrel (fun x => by
      obtain ⟨mu, hmu⟩ := (hw 2 (by norm_num)).2.1 x
      exact ⟨mu, by rw [← two_nsmul]; exact hmu⟩)
  have htop : Λ = ⊤ := by
    rcases hc with h | ⟨l, hl, -, g, hg, hgΛ⟩
    · exact h
    · refine absurd (hodd l hl g fun α hα => hgΛ α ?_) hg
      have : α ∈ (Λ : Set D.X) := by rw [hΛ]; exact hα
      exact this
  have hall : ∀ α, α ∈ ({α | ∃ j, (f α).f j ≠ 0} : Set D.X) := fun α => by
    rw [← hΛ, htop]; trivial
  refine ⟨hall, fun α => ?_⟩
  have : α ∈ ({α | U.Supp (Kbar V) 2 α} : Set D.X) := by rw [hS]; exact hall α
  exact this

end GlobalTheory.UU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSectionSupportEqUnivStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.thetaSection_support_eq_univ : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∀ α, ∃ j, (f α).f j ≠ 0) ∧ ∀ α, U.Supp (Kbar V) 2 α) := by
  first | exact @GlobalTheory.UU.theta_support_eq_univ | exact GlobalTheory.UU.theta_support_eq_univ | (intros; apply GlobalTheory.UU.theta_support_eq_univ <;> assumption)
end
end
