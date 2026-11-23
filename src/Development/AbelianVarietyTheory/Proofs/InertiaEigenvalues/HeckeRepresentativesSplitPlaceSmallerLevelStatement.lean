module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSublevelFiniteIndexMorePlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAntiStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotentsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDoubleCosetOfSmallerLevelSameLocal

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isDC_of_smaller_level_same_local {G : Type} [Group G] (J J' Lc : Subgroup G) (x : G) (A : Finset G)
    (hJJ : J' ≤ J) (hLc : J ⊓ Lc ≤ J')
    (hdec : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ y ∈ Lc, Commute k₂ y)
    (hx : x ∈ Lc) (hA : ∀ a ∈ A, a ∈ Lc) (hDC : Bridge.IsDC J x A) : Bridge.IsDC J' x A := by
  obtain ⟨h1, h2⟩ := hDC
  refine ⟨fun a ha => ?_, fun g hg => ?_⟩
  · obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩, rfl⟩ := h1 a ha
    obtain ⟨k₁, hk₁J, k₂, hk₂J, hk₁L, rfl, hk₂c⟩ := hdec k hk
    obtain ⟨k₁', hk₁'J, k₂', hk₂'J, hk₁'L, rfl, -⟩ := hdec k' hk'
    have e : k₁ * k₂ * x * (k₁' * k₂') = k₁ * x * k₁' * (k₂ * k₂') := by
      have c1 : k₂ * x = x * k₂ := (hk₂c x hx).eq
      have c2 : k₂ * k₁' = k₁' * k₂ := (hk₂c k₁' hk₁'L).eq
      calc k₁ * k₂ * x * (k₁' * k₂') = k₁ * (k₂ * x) * k₁' * k₂' := by group
        _ = k₁ * x * (k₂ * k₁') * k₂' := by rw [c1]; group
        _ = k₁ * x * (k₁' * k₂) * k₂' := by rw [c2]
        _ = k₁ * x * k₁' * (k₂ * k₂') := by group
    have haL := hA _ ha
    have hprodL : k₂ * k₂' ∈ Lc := by
      have : k₂ * k₂' = (k₁ * x * k₁')⁻¹ * (k₁ * k₂ * x * (k₁' * k₂')) := by rw [e]; group
      rw [this]
      exact Lc.mul_mem (Lc.inv_mem (Lc.mul_mem (Lc.mul_mem hk₁L hx) hk₁'L)) haL
    have hprod : k₂ * k₂' ∈ J' := hLc ⟨J.mul_mem hk₂J hk₂'J, hprodL⟩
    have hk₁ : k₁ ∈ J' := hLc ⟨hk₁J, hk₁L⟩
    have hk₁' : k₁' ∈ J' := hLc ⟨hk₁'J, hk₁'L⟩
    refine ⟨⟨k₁, hk₁⟩, ⟨k₁' * (k₂ * k₂'), J'.mul_mem hk₁' hprod⟩, ?_⟩
    simp only
    rw [e]; group
  · obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩, rfl⟩ := hg
    obtain ⟨k₁, hk₁J, k₂, hk₂J, hk₁L, rfl, hk₂c⟩ := hdec k (hJJ hk)
    have hk₁ : k₁ ∈ J' := hLc ⟨hk₁J, hk₁L⟩
    have hk₂ : k₂ ∈ J' := by
      have : k₂ = k₁⁻¹ * (k₁ * k₂) := by group
      rw [this]; exact J'.mul_mem (J'.inv_mem hk₁) hk
    obtain ⟨a, ⟨haA, haJ⟩, -⟩ := h2 (k₁ * x) ⟨⟨k₁, hk₁J⟩, 1, by simp⟩
    have haL : a⁻¹ * (k₁ * x) ∈ Lc := Lc.mul_mem (Lc.inv_mem (hA a haA)) (Lc.mul_mem hk₁L hx)
    have haJ' : a⁻¹ * (k₁ * x) ∈ J' := hLc ⟨haJ, haL⟩
    have c1 : k₂ * x = x * k₂ := (hk₂c x hx).eq
    refine ⟨a, ⟨haA, ?_⟩, ?_⟩
    · have : a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * (k₁ * x) * (k₂ * k') := by
        calc a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * k₁ * (k₂ * x) * k' := by group
          _ = a⁻¹ * (k₁ * x) * (k₂ * k') := by rw [c1]; group
      rw [this]
      exact J'.mul_mem haJ' (J'.mul_mem hk₂ hk')
    · rintro b ⟨hbA, hbJ'⟩
      have hgJ : ∃ m₁ m₂ : J, k₁ * k₂ * x * k' = (m₁ : G) * x * m₂ :=
        ⟨⟨k₁ * k₂, hJJ hk⟩, ⟨k', hJJ hk'⟩, rfl⟩
      obtain ⟨c, -, hc⟩ := h2 _ hgJ
      have haJg : a⁻¹ * (k₁ * k₂ * x * k') ∈ J := by
        have : a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * (k₁ * x) * (k₂ * k') := by
          calc a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * k₁ * (k₂ * x) * k' := by group
            _ = a⁻¹ * (k₁ * x) * (k₂ * k') := by rw [c1]; group
        rw [this]; exact J.mul_mem haJ (J.mul_mem hk₂J (hJJ hk'))
      rw [hc b ⟨hbA, hJJ hbJ'⟩, hc a ⟨haA, haJg⟩]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDoubleCosetOfSmallerLevelSameLocalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isDoubleCoset_of_smaller_level_same_local : ∀ {G : Type} [Group G] (J J' Lc : Subgroup G) (x : G) (A : Finset G), J' ≤ J → J ⊓ Lc ≤ J' → (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ y ∈ Lc, Commute k₂ y) → x ∈ Lc → (∀ a ∈ A, a ∈ Lc) → Bridge.IsDC J x A → Bridge.IsDC J' x A := by
  first | exact @GlobalTheory.isDC_of_smaller_level_same_local | exact GlobalTheory.isDC_of_smaller_level_same_local | (intros; apply GlobalTheory.isDC_of_smaller_level_same_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeRepresentativesSplitPlaceSmallerLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallerLevelHecke
open Formalism.IndefR.Lev Formalism.L2.NTheta GlobalTheory.SplitHeckeAdj

theorem local_group_two {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L L' : LevDat D.host.E ℂ V.rank) (hβ : IsBaseFrame V β Λ 1)
    (P : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D) (he : IsIdemAt e P)
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    (hoff' : ∀ PP, PP ∈ L'.Pg ∨ PP ∈ L'.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) :
    ∃ Lc : Subgroup (Bridge.Gf V), (∀ g, SuppAt e V g → fin V g ∈ Lc) ∧
      (∀ g, SuppAt e V g → fin V g⁻¹ ∈ Lc) ∧
      (∀ k ∈ (levEnv V β L).J, ∃ k₁ ∈ (levEnv V β L).J, ∃ k₂ ∈ (levEnv V β L).J,
        k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ l ∈ Lc, Commute k₂ l) ∧
      (levEnv V β L).J ⊓ Lc ≤ (levEnv V β L').J := by
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have h01 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e _ hP
  have hff := h01.1
  have hcf := h01.2.1
  have h02 := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 _ hff hcf).1
  refine h02.elim fun L₀ hL₀ => ?_
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have h03 := (GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ 1 (flag1L L) hβ).2 P e _ hP h1 hoff
  have hK' := ((GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ 1 (flag1L L') hβ).2 P e _ hP h1 hoff').1
  have hK := h03.1
  have hχ := h03.2.1
  have hsp := h03.2.2
  have hL : ∀ g, g ∈ L₀ ↔ SuppAt e V g := hL₀
  have h04 := (GlobalTheory.T.involution_spherical_hecke_anti V P e he).1
  have h05 := transport_local (fin V) (GfC V) (levG V β (flag1L L)) L₀ (levEnv V β L).J (SuppAt e V)
    (SuppF V (1 - (e + cA D e))) (KsphC V ∅) (fun k => ((levEnv V β L).χ k : ℂ)) (levChi V β (flag1L L))
    (fin_lift V) (fun g g' => fin_inj V) (fun g => mem_J V β L) (fun g hg => hg.1) hL (fun g => supp_fin V he)
    (fun g g' => commute_compl V _ hff hcf) (fun g => chi_eq V β L) hK hχ hsp h04
  refine ⟨L₀.map (fin V), fun g hg => ⟨g, (hL g).2 hg, rfl⟩,
    fun g hg => ⟨g⁻¹, L₀.inv_mem ((hL g).2 hg), rfl⟩, h05.1, ?_⟩
  rintro _ ⟨hj, g, hg, rfl⟩
  have a := (hL g).1 hg
  have b := supp_fin V he a
  exact (mem_J V β L' b).2 ((hK' g a).2 ((hK g a).1 ((mem_J V β L b).1 hj)))

theorem isDC_smaller_level : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → ∀ (Pl0 : Type) (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ), (∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ≠ pl i.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i.1)) → i.2 ≤ V.rank → ∀ (x : Bridge.Gf V) (A : Finset (Bridge.Gf V)), isTEnv V pl ok i x → (∀ a ∈ A, isLocEnv V pl ok i a) → Bridge.IsDC (levEnv V β L).J x A → Bridge.IsDC (levEnv V β { L with Q := Q', xq := xq }).J x A := by
  intro D V β Λ hSD L Q' xq hQ Pl0 pl ok i hoff hi x A hx hA hDC
  have hle := (GlobalTheory.T.parahoricSublevel_finiteIndex_more_places D V β Λ hSD L Q' xq hQ).1
  obtain ⟨cc, hβ⟩ := hSD
  rw [one_pow] at hβ
  obtain ⟨α, ⟨e, ϖ, he, -, -, hα⟩, hxα⟩ := hx hi
  obtain ⟨Lc, l1, l2, l3, l4⟩ := local_group_two V β Λ L { L with Q := Q', xq := xq } hβ (pl i.1) e he
    (fun PP h => hoff PP (h.imp_right fun h' => hQ h')) hoff
  have e1 : x = fin V α⁻¹ := Subtype.ext hxα
  refine GlobalTheory.T.isDoubleCoset_of_smaller_level_same_local _ _ Lc x A hle l4 l3 ?_ (fun a ha => ?_) hDC
  · rw [e1]
    exact l2 α hα.2.1
  · obtain ⟨g, hg, rfl⟩ := loc_supp V (hA a ha) he
    exact l1 g hg

end GlobalTheory.SmallerLevelHecke
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeRepresentativesSplitPlaceSmallerLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hecke_representatives_split_place_smaller_level : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → ∀ (Pl0 : Type) (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ), (∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ≠ pl i.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i.1)) → i.2 ≤ V.rank → ∀ (x : Bridge.Gf V) (A : Finset (Bridge.Gf V)), isTEnv V pl ok i x → (∀ a ∈ A, isLocEnv V pl ok i a) → Bridge.IsDC (levEnv V β L).J x A → Bridge.IsDC (levEnv V β { L with Q := Q', xq := xq }).J x A := by
  first | exact @GlobalTheory.SmallerLevelHecke.isDC_smaller_level | exact GlobalTheory.SmallerLevelHecke.isDC_smaller_level | (intros; apply GlobalTheory.SmallerLevelHecke.isDC_smaller_level <;> assumption)
end
end
