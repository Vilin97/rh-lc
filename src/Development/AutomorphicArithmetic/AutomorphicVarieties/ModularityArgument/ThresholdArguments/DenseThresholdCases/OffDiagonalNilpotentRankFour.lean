module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DeformationSpaceLocalCharactersContinuous
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NnDefs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ExistsGen
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsPinningElementsOfLocAb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsPlaceOverLLocDegMulCardEq
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.RingTheory.Ideal.Height
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.NonemptyLocalWeilDataDecompositionGroupOfMemPlac
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Basify

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsMemPinsInsertKerOfPadicCharacter

section

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.Ws

theorem UpperTheory.exists_mem_pins_insert_ker_of_padic_character :
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (I : Subgroup G), IsClosed (I : Set G) → ∀ ε : G →* ℤ_[l]ˣ, Continuous ε → ∃ s ∈ I, Pins l I (insert s {g | g ∈ I ∧ ε g = 1}) := by
  intro l _ hl G _ _ _ _ I hI ε hε
  have hclo : ∀ K : Subgroup G, IsClosed (K : Set G) →
      IsClosed ((K.map ε : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    intro K hK
    rw [Subgroup.coe_map]
    exact (hK.isCompact.image hε).isClosed
  obtain ⟨γ, hγ, hV⟩ := UpperTheory.V.Kum.existsGen l (I.map ε) (hclo I hI) (Or.inl hl)
  obtain ⟨s, hsI, rfl⟩ := Subgroup.mem_map.mp hγ
  refine ⟨s, hsI, ?_⟩
  intro R _ _ _ _ _ ψ hψ _ hS g hg
  have hK : IsClosed ((ψ.ker ⊓ I : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact (isClosed_ker_of_adicCont ψ hψ).inter hI
  have hsK : s ∈ ψ.ker ⊓ I :=
    Subgroup.mem_inf.mpr ⟨MonoidHom.mem_ker.mpr (hS s (Set.mem_insert _ _)), hsI⟩
  have hle : I.map ε ≤ (ψ.ker ⊓ I).map ε := by
    refine hV.trans (Subgroup.topologicalClosure_minimal _ ?_ (hclo _ hK))
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_map_of_mem _ hsK
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_map_of_mem ε hg))
  have hk' := Subgroup.mem_inf.mp hk
  have h1 : ψ (g * k⁻¹) = 1 :=
    hS _ (Set.mem_insert_of_mem _ ⟨I.mul_mem hg (I.inv_mem hk'.2), by simp [hkg]⟩)
  have hk1 : ψ k = 1 := MonoidHom.mem_ker.mp hk'.1
  simpa [hk1] using h1
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.KrullDimQuotientLeCardOfRadicalParameters

section

@[expose] public section

open IsLocalRing

theorem UpperTheory.krullDim_quotient_le_card_of_radical_parameters :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (q : Ideal B) (κ : Type) [Finite κ] (x : κ → B), (∀ k, x k ∈ maximalIdeal B) → (∀ p : Ideal B, p.IsPrime → q ≤ p → (∀ k, x k ∈ p) → maximalIdeal B ≤ p) → ringKrullDim (B ⧸ q) ≤ Nat.card κ := by
  intro B _ _ _ q κ _ x hx h
  classical
  by_cases hq : q = ⊤
  · subst hq
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  haveI : Nontrivial (B ⧸ q) := Ideal.Quotient.nontrivial_iff.mpr hq
  haveI : IsLocalRing (B ⧸ q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk q) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let s : Set (B ⧸ q) := Set.range (fun k => Ideal.Quotient.mk q (x k))
  have hs : s.Finite := Set.finite_range _
  have hmin : maximalIdeal (B ⧸ q) ∈ (Ideal.span s).minimalPrimes := by
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      exact map_nonunit (Ideal.Quotient.mk q) _ (hx k)
    · rintro P ⟨hP, hsP⟩ _
      have h1 : maximalIdeal B ≤ P.comap (Ideal.Quotient.mk q) := by
        refine h _ (Ideal.comap_isPrime _ _) ?_ ?_
        · intro a ha
          rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
          exact P.zero_mem
        · intro k
          exact hsP (Ideal.subset_span ⟨k, rfl⟩)
      intro y hy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply h1
      rw [mem_maximalIdeal] at hy ⊢
      exact fun hu => hy (hu.map _)
  have h2 := Ideal.height_le_card_of_mem_minimalPrimes_span hs hmin
  have h3 : s.ncard ≤ Nat.card κ := by
    rw [← Set.ncard_univ, show s = (fun k => Ideal.Quotient.mk q (x k)) '' Set.univ from Set.image_univ.symm]
    exact Set.ncard_image_le Set.finite_univ
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  have h4 : (maximalIdeal (B ⧸ q)).height ≤ (Nat.card κ : ℕ∞) := h2.trans (by exact_mod_cast h3)
  exact_mod_cast h4
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OffDiagonalNilpotentRankFour

section

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
theorem UpperTheory.V.Ws.off_diagonal_nilpotent_rank_four :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (ι : PadicAlgCl l ≃+* ℂ) (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B), T.PotentialModularityTower ι X J → ∀ (v : T.ι) (i j : Fin 4), i ≠ j → ∀ (q : Ideal X.B), q.IsPrime → J ≤ q → (maximalIdeal c'.O).map (algebraMap c'.O X.B) ≤ q →
      (∀ s ∈ T.U1 v, X.ψ v i s - X.ψ v j s ∈ q) → ∀ dv : ℕ, dv * Nat.card T.ι = T.d → ringKrullDim (X.B ⧸ q) + dv ≤ (2 * T.d + 1 : ℕ) := by
  classical
  intro _ Ω _ _ _ l _ c D T hFit _ ι c' h X J hPM v i j hij q hq hJ hϖ hU dv hdv
  have hOk := hFit.1
  have hl2 : l ≠ 2 := by
    rcases hFit.2 with h | h
    · exact h.1.1.l_odd
    · exact h.1.1.l_odd
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : IsGalois T.F Ω := IsAlgClosure.isGalois T.F Ω
  haveI : Nonempty T.ι := ⟨v⟩
  have hg : 0 < Nat.card T.ι := Nat.card_pos
  haveI hcD : ∀ u, CompactSpace (Dec (F := T.F) (T.pl u)) := fun u =>
    isCompact_iff_compactSpace.1 (isClosed_Dec (T.pl u)).isCompact
  let I : ∀ u, Subgroup (Dec (F := T.F) (T.pl u)) := fun u => (Ine (F := T.F) (T.pl u)).subgroupOf _
  have hs : ∀ u, ∃ s : Fin dv → Dec (F := T.F) (T.pl u), (∀ k, s k ∈ I u) ∧ Pins l (I u) (Set.range s) := fun u => by
    obtain ⟨w, hw, hlw, hd⟩ := UpperTheory.exists_place_over_l_locDeg_mul_card_eq D T u
    obtain ⟨A⟩ := UpperTheory.nonempty_localWeilData_decompositionGroup_of_mem_place l (T.pl u) w hw hlw
    obtain rfl : locDeg w = dv := Nat.eq_of_mul_eq_mul_right hg (hd.trans hdv.symm)
    exact UpperTheory.exists_pinning_elements_of_locAb l _ _ _ A
  choose s hsI hsP using hs
  obtain ⟨s0, hs0, hP0⟩ := UpperTheory.exists_mem_pins_insert_ker_of_padic_character l hl2 _ (I v) ((isClosed_Ine (T.pl v)).preimage continuous_subtype_val)
    ((cycZ T.F Ω l).comp (Dec (F := T.F) (T.pl v)).subtype) ((continuous_cycZ T.F Ω l).comp continuous_subtype_val)
  obtain ⟨a, ha, ha'⟩ : ∃ a : Fin 4, (a = j ∨ j = i.rev) ∧ ∀ m : Fin 4, m = a ∨ m = a.rev ∨ m = i ∨ m = i.rev :=
    (by decide : ∀ i j : Fin 4, i ≠ j → ∃ a : Fin 4, (a = j ∨ j = i.rev) ∧
      ∀ m : Fin 4, m = a ∨ m = a.rev ∨ m = i ∨ m = i.rev) i j hij
  let x : (T.ι × Fin dv) ⊕ ({u // u ≠ v} × Fin dv) ⊕ Unit → X.B :=
    Sum.elim (fun y => X.ψ y.1 a (s y.1 y.2) - 1)
      (Sum.elim (fun y => X.ψ y.1.1 i (s y.1.1 y.2) - 1) fun _ => X.ψ v i s0 - X.ψ v j s0)
  have hm : ∀ u m (t : Dec (F := T.F) (T.pl u)), t ∈ I u → X.ψ u m t - 1 ∈ maximalIdeal X.B := fun u m t ht => by
    obtain ⟨-, κ, hκ⟩ := UpperTheory.deformationSpace_local_characters_continuous D T hOk c' h X _ (residue X.B) (fun b hb => by
      rw [(residue_eq_zero_iff b).2 hb]; exact zero_mem _) (fun b hb => (residue_eq_zero_iff _).2 (map_nonunit _ b hb))
    have h1 := ((hκ u m).2.2 t ht).1
    rw [(hκ u m).1, maximalIdeal_eq_bot, Ideal.mem_bot, ← map_one (residue X.B), ← map_sub, residue_eq_zero_iff] at h1
    exact h1
  have hdim := UpperTheory.krullDim_quotient_le_card_of_radical_parameters X.B q _ x ?_ ?_
  · have hc : Nat.card ((T.ι × Fin dv) ⊕ ({u // u ≠ v} × Fin dv) ⊕ Unit) + dv = 2 * T.d + 1 := by
      have h1 : Nat.card {u // u ≠ v} + 1 = Nat.card T.ι := by
        rw [← Finite.card_option]
        exact Nat.card_congr (Equiv.optionSubtypeNe v)
      simp only [Nat.card_sum, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin dv), Fintype.card_fin, Nat.card_unique]
      rw [← hdv, ← h1]
      ring
    rw [← hc, Nat.cast_add]
    gcongr
  · rintro (y | y | y)
    · exact hm _ _ _ (hsI _ _)
    · exact hm _ _ _ (hsI _ _)
    · simpa [x] using sub_mem (hm v i s0 hs0) (hm v j s0 hs0)
  intro p hp hqp hx
  haveI : IsLocalRing (X.B ⧸ p) := IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk p) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨h0, κ, hκ⟩ := UpperTheory.deformationSpace_local_characters_continuous D T hOk c' h X _ (Ideal.Quotient.mk p) (fun b hb => map_nonunit _ b hb)
    (fun b hb => Ideal.Quotient.eq_zero_iff_mem.2 (hqp (hϖ (Ideal.mem_map_of_mem _ hb))))
  have h1 : ∀ u m (t : Dec (F := T.F) (T.pl u)), κ u m t = 1 ↔ X.ψ u m t - 1 ∈ p := fun u m t => by
    rw [← Units.val_eq_one, (hκ u m).1, ← Ideal.Quotient.eq, map_one]
  have hpin : ∀ u m, (∀ k, X.ψ u m (s u k) - 1 ∈ p) → ∀ t ∈ I u, κ u m t = 1 := fun u m hk =>
    hsP u _ h0 (κ u m) (hκ u m).2.1 (fun t ht => ((hκ u m).2.2 t ht).1) (by
      rintro _ ⟨k, rfl⟩; exact (h1 _ _ _).2 (hk k))
  have hA : ∀ u, ∀ t ∈ I u, κ u a t = 1 := fun u => hpin u a fun k => hx (.inl (u, k))
  have hE : ∀ t ∈ I v, κ v i t = κ v j t := by
    refine hP0.eq h0 _ _ (hκ v i).2.1 (hκ v j).2.1 (fun t ht => ((hκ v i).2.2 t ht).1)
      (fun t ht => ((hκ v j).2.2 t ht).1) fun t ht => Units.ext ?_
    rw [(hκ v i).1, (hκ v j).1, Ideal.Quotient.eq]
    rcases ht with rfl | ⟨ht, ht'⟩
    · exact hx (.inr (.inr ()))
    · exact hqp (hU t ⟨ht, ht', hOk.ineL _ (T.ovl v) _ ht⟩)
  have hI : ∀ u, ∀ t ∈ I u, κ u i t = 1 := fun u => by
    by_cases hu : u = v
    · subst hu
      intro t ht
      rcases ha with rfl | rfl
      · exact (hE t ht).trans (hA u t ht)
      · have h2 := (hκ u i).2.2 t ht
        refine Units.val_eq_one.1 (eq_one_of_pow h0 h2.1 two_ne_zero ?_)
        rw [← Units.val_pow_eq_pow_val, sq, Units.val_eq_one]
        rw [← hE t ht] at h2
        exact h2.2
    · exact hpin u i fun k => hx (.inr (.inl (⟨u, hu⟩, k)))
  have hall : ∀ u m, ∀ t ∈ I u, κ u m t = 1 := fun u m t ht => by
    rcases ha' m with rfl | rfl | rfl | rfl
    · exact hA u t ht
    · simpa [hA u t ht] using ((hκ u a).2.2 t ht).2
    · exact hI u t ht
    · simpa [hI u t ht] using ((hκ u i).2.2 t ht).2
  obtain ⟨n, hn⟩ := hPM.fin
  refine hp.le_of_pow_le (n := n) (hn.trans (sup_le (sup_le (hJ.trans hqp) (hϖ.trans hqp)) (Ideal.span_le.2 ?_)))
  rintro _ ⟨u, m, t, ht, rfl⟩
  exact (h1 u m ⟨t, Ine_le_Dec _ ht⟩).1 (hall u m _ ht)
end
end
end
