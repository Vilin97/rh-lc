module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormLeOfMemBoxSet
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormSpanEqProd
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlphaNOfVdZeroUnit
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsVecOfHermRep
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FinitePrimesOfMem
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LamGEqOneOfOrtho
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountLocF
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SumOrbitsEquivariant
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFibGEqProd
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsVecOfHermRep
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsIntegralAtLocF
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsLatticeOfFibReps
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsIntegralLatOfForall
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SumRegroup

section

@[expose] public section

open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.MassProductFormula

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open UnimodularLocalization GoodPrimeTerms GoodGenusOrbits LocalFactorEquality


open Classical in
theorem sum_regroup (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hLfull : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c)
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s')
    {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    {A : Submodule (𝓞 K) V'} (hAfull : Submodule.IsFullLattice K A) (hAi : Formalism.HermitianLatticesTheory.IsIntegralLat h' A)
    (Z : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (hZL : ∀ 𝔭 ∉ Z, vd h L 𝔭.1 = 0) (hZn : ∀ 𝔭 ∉ Z, vF 𝔭.1 n = 0)
    (hZA : ∀ 𝔭 ∉ Z, vd h' A 𝔭.1 = 0)
    (s : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Finset (Submodule (𝓞 K) V'))
    (hsr : ∀ 𝔭, IsLocReps S L 𝔭.1 (s 𝔭)) :
    ∑ Λ' ∈ s', (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) =
      c * ∏ 𝔭 ∈ Z, ∑ T ∈ s 𝔭, (fibLoc S L 𝔭.1 T : ℝ) * lamP h' T 𝔭.1 := by
  have hA := hAfull.toIsLattice
  have hZ1 : ∀ 𝔭 ∉ Z, fibLoc S L 𝔭.1 A = 1 := fun 𝔭 h𝔭 =>
    fibLoc_eq_one hK hF hs hd S hLfull hLi hAfull hAi 𝔭.2 hn (hZL 𝔭 h𝔭) (hZn 𝔭 h𝔭) (hZA 𝔭 h𝔭)
  have hex : ∀ τ : ↥Z → Submodule (𝓞 K) V', τ ∈ Fintype.piFinset (fun 𝔭 : ↥Z => s 𝔭.1) →
      ∃ M, Good F S L M ∧ (∀ 𝔭 : ↥Z, locF 𝔭.1.1 M = τ 𝔭) ∧
        ∀ 𝔭 ∉ Z, locF 𝔭.1 M = locF 𝔭.1 A := by
    intro τ hτ
    rw [Fintype.mem_piFinset] at hτ
    obtain ⟨M, hM, h1, h2⟩ := exists_patch hK hF S hLfull hAfull Z
      (fun 𝔭 => if H : 𝔭 ∈ Z then τ ⟨𝔭, H⟩ else ⊥)
      (fun 𝔭 h𝔭 => by
        simp only [dif_pos h𝔭]
        exact ⟨((hsr 𝔭).1 _ (hτ ⟨𝔭, h𝔭⟩)).1, ((hsr 𝔭).1 _ (hτ ⟨𝔭, h𝔭⟩)).2.2⟩)
      (fun 𝔭 h𝔭 => by rw [hZ1 𝔭 h𝔭]; exact one_ne_zero)
    exact ⟨M, hM, fun 𝔭 => by rw [h1 𝔭.1 𝔭.2, dif_pos 𝔭.2], h2⟩
  choose! M hMg hMZ hMA using hex
  rw [← Finset.prod_coe_sort Z (fun 𝔭 => ∑ T ∈ s 𝔭, (fibLoc S L 𝔭.1 T : ℝ) * lamP h' T 𝔭.1),
    Finset.prod_univ_sum, Finset.mul_sum]
  have e1 : ∀ τ ∈ Fintype.piFinset (fun 𝔭 : ↥Z => s 𝔭.1),
      c * ∏ 𝔭 : ↥Z, ((fibLoc S L 𝔭.1.1 (τ 𝔭) : ℝ) * lamP h' (τ 𝔭) 𝔭.1.1) =
        ∑ Λ' ∈ s'.filter (fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' (M τ) Λ'),
          (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) := by
    intro τ hτ
    rw [sum_genus hK hF hs hd S hLfull hLi hc hs' hA hAi Z hZ1 hZA (hMg τ hτ) (hMA τ hτ),
      ← Finset.prod_coe_sort Z]
    congr 1
    refine Finset.prod_congr rfl fun 𝔭 _ => ?_
    rw [hMZ τ hτ 𝔭]
  rw [Finset.sum_congr rfl e1]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Λ' hΛ' => ?_
  by_cases hg : Good F S L Λ'
  · have hloc : ∀ 𝔭 : ↥Z, ∃! T₀, T₀ ∈ s 𝔭.1 ∧
        ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g T₀ = locF 𝔭.1.1 Λ' := fun 𝔭 =>
      (hsr 𝔭.1).2 _ (LocF.locF_idem _ _)
        (isIntegralAt_locF 𝔭.1.2.isPrime hF (hg.integral hF hLfull.toIsLattice hLi))
        (by rw [fibLoc_locF]; exact hg.2 𝔭.1)
    choose τ₀ hτ₀ hu using hloc
    have hmem : τ₀ ∈ Fintype.piFinset (fun 𝔭 : ↥Z => s 𝔭.1) :=
      Fintype.mem_piFinset.mpr fun 𝔭 => (hτ₀ 𝔭).1
    rw [Finset.sum_eq_single τ₀, if_pos]
    · rw [sameGenus_iff hK hF]
      intro 𝔭
      by_cases h𝔭 : 𝔭 ∈ Z
      · have := (hτ₀ ⟨𝔭, h𝔭⟩).2
        rw [hMZ τ₀ hmem ⟨𝔭, h𝔭⟩]
        exact this
      · exact good_orbit hK hF hs hd S hLfull hLi 𝔭.2 hn (hZL 𝔭 h𝔭) (hZn 𝔭 h𝔭)
          ((hMg τ₀ hmem).2 𝔭) (hg.2 𝔭)
    · intro τ hτ hne
      rw [if_neg]
      intro hsg
      apply hne
      funext 𝔭
      apply hu 𝔭
      refine ⟨Fintype.mem_piFinset.mp hτ 𝔭, ?_⟩
      have := (sameGenus_iff hK hF _ _).mp hsg 𝔭.1
      rwa [hMZ τ hτ 𝔭] at this
    · intro hc'
      exact absurd hmem hc'
  · have hlat := isFullLattice_of_fibReps S hs' hΛ'
    have : ∃ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, fibLoc S L 𝔭.1 Λ' = 0 := by
      by_contra hcon
      push Not at hcon
      exact hg ⟨hlat.toIsLattice, hcon⟩
    obtain ⟨𝔭, h𝔭⟩ := this
    rw [card_fibG_eq_zero hK hF hs hd S hLfull hLi hlat 𝔭 h𝔭]
    simp

theorem repMass_eq_prod_psi' (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hLfull : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c) :
    repMass h L (h S.x₀ S.x₀) =
      c * ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 := by
  classical
  have hL : Submodule.IsLattice K L := hLfull.toIsLattice
  obtain ⟨s', hs'⟩ := exists_fibReps hK hs hd S hL hLi
  rw [repMass_eq_sum_fib hK hs hd S hL hLi hs']
  by_cases H : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, ∃ T, fibLoc S L 𝔭.1 T ≠ 0
  · obtain ⟨n, hn⟩ := exists_norm_eq hF hs S hLi H
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact S.hx₀ (by rw [hn]; simp)
    have hAfull := StabilizerLattices.isFullLattice_cut S hLfull
    have hAi := isIntegralLat_cut S hLi
    have f1 := finite_vd_ne_zero hK hF hs hd hLfull hLi
    have f2 := finite_vF_ne_zero hn0
    have f3 := finite_vd_ne_zero hK hF (S.isSymm hs) (S.isTotPosDef hd) hAfull hAi
    set Z : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
      f1.toFinset ∪ f2.toFinset ∪ f3.toFinset with hZ
    have hZL : ∀ 𝔭 ∉ Z, vd h L 𝔭.1 = 0 := by
      intro 𝔭 h𝔭
      by_contra h0
      exact h𝔭 (by simp only [hZ, Finset.mem_union, Set.Finite.mem_toFinset]; exact Or.inl (Or.inl h0))
    have hZn : ∀ 𝔭 ∉ Z, vF 𝔭.1 n = 0 := by
      intro 𝔭 h𝔭
      by_contra h0
      exact h𝔭 (by simp only [hZ, Finset.mem_union, Set.Finite.mem_toFinset]; exact Or.inl (Or.inr h0))
    have hZA : ∀ 𝔭 ∉ Z, vd h' (S.cut L) 𝔭.1 = 0 := by
      intro 𝔭 h𝔭
      by_contra h0
      exact h𝔭 (by simp only [hZ, Finset.mem_union, Set.Finite.mem_toFinset]; exact Or.inr h0)
    choose T hT using H
    obtain ⟨M₀, hM₀, -, -⟩ := exists_patch hK hF S hLfull hAfull Z (fun 𝔭 => locF 𝔭.1 (T 𝔭))
      (fun 𝔭 _ => ⟨LocF.locF_idem _ _, by rw [fibLoc_locF]; exact hT 𝔭⟩)
      (fun 𝔭 h𝔭 => by
        rw [fibLoc_eq_one hK hF hs hd S hLfull hLi hAfull hAi 𝔭.2 hn (hZL 𝔭 h𝔭) (hZn 𝔭 h𝔭) (hZA 𝔭 h𝔭)]
        exact one_ne_zero)
    have hex := fun 𝔭 => exists_locReps hK hF hs hd S hLfull hLi hM₀ 𝔭
    rw [sum_regroup hK hF hs hd S hLfull hLi hc hs' hn hAfull hAi Z hZL hZn hZA
      (fun 𝔭 => (hex 𝔭).choose) (fun 𝔭 => (hex 𝔭).choose_spec)]
    congr 1
    rw [tprod_eq_prod (s := Z) (fun 𝔭 h𝔭 =>
      psiP_eq_one' hK hF hs hd S hLfull hLi 𝔭.2 hn (hZL 𝔭 h𝔭) (hZn 𝔭 h𝔭))]
    exact Finset.prod_congr rfl fun 𝔭 _ => (psiP_eq S L 𝔭.1 (hex 𝔭)).symm
  · push Not at H
    obtain ⟨𝔭, H⟩ := H
    rw [tprod_of_exists_eq_zero ⟨𝔭, psiP_eq_zero S L 𝔭.1 H⟩, mul_zero]
    refine Finset.sum_eq_zero fun Λ' hΛ' => ?_
    rw [card_fibG_eq_zero hK hF hs hd S hLfull hLi (isFullLattice_of_fibReps S hs' hΛ') 𝔭 (H Λ')]
    simp

end Formalism.HermitianLattices.Ext.L3.MassProductFormula
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RepMassEqProdPsi

section

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem repMass_eq_prod_psi (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c) :
    repMass h L (h S.x₀ S.x₀) = c * ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 :=
  MassProductFormula.repMass_eq_prod_psi' hK hF hs hd S (by first | exact hL | exact hL.toIsLattice) hLi hc

end Formalism.HermitianLattices.Ext.L3
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FactorIdentity

section

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Step

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V V' : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

theorem alphaStd_succ (𝔭 : Ideal (𝓞 F)) {m : ℕ} (hm : 1 ≤ m) :
    alphaStd K 𝔭 m = alphaStd K 𝔭 (m - 1) * A5.eFac K m 𝔭 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  unfold alphaStd A5.eFac
  rw [Finset.prod_Icc_succ_top (by omega)]
  simp

theorem factor_identity (q aS e aL aN : ℝ) (m a b : ℕ) (hm : 1 ≤ m) (hq : q ≠ 0) (he : e ≠ 0)
    (hL : aL ≠ 0) :
    q ^ ((m - 1) * (a + b)) * aS * aN / aL =
      (q ^ a) ^ (m - 1) * (aS * e * q ^ (m * b) / aL) * (q ^ b)⁻¹ * (aN / e) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

theorem tprod_localPsi_eq (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V} (hLfull : Submodule.IsFullLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn0 : n ≠ 0)
    (hn : h S.x₀ S.x₀ = algebraMap F K (n : F)) :
    ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 =
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * lamG F h L * (normD h L)⁻¹ *
        singS F h L n := by
  classical
  set U : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
    (finite_vd_ne_zero (F := F) hK hF hs hd hLfull hLi).toFinset ∪ (A5.finite_primes_of_mem hn0).toFinset
    with hU
  have hU1 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ U → vd h L 𝔭.1 = 0 := by
    intro 𝔭 h𝔭
    rw [hU, Finset.mem_union, not_or, Set.Finite.mem_toFinset] at h𝔭
    exact not_not.mp h𝔭.1
  have hU2 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ U → n ∉ 𝔭.1 := by
    intro 𝔭 h𝔭
    rw [hU, Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at h𝔭
    exact h𝔭.2
  have hU3 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ U → vF 𝔭.1 n = 0 := by
    intro 𝔭 h𝔭
    by_contra hne
    have := (A5.mem_pow_iff_le_vF 𝔭.2 hn0 1).mpr (Nat.one_le_iff_ne_zero.mpr hne)
    rw [pow_one] at this
    exact hU2 𝔭 h𝔭 this
  have hpt : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 =
      ((Ideal.absNorm 𝔭.1 : ℝ) ^ vF 𝔭.1 n) ^ (finrank K V - 1) * lamP h L 𝔭.1 *
        ((Ideal.absNorm 𝔭.1 : ℝ) ^ vd h L 𝔭.1)⁻¹ *
        (alphaN h L 𝔭.1 n / (1 - etaF K F 𝔭.1 ^ finrank K V *
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ)))) := by
    intro 𝔭
    rw [hLI K F hK hF V V' h h' S L 𝔭.1 n hs hd 𝔭.2 hn0 hn hLfull hLi]
    unfold lamP
    rw [alphaStd_succ 𝔭.1 hm]
    have hq : (Ideal.absNorm 𝔭.1 : ℝ) ≠ 0 := by
      have := A5.two_le_absNorm 𝔭.2
      positivity
    exact factor_identity _ _ _ _ _ _ _ _ hm hq (A5.eFac_pos 𝔭.2 hm).ne'
      (alphaL_pos hK hF hs hd hLfull hLi 𝔭.2).ne'
  have e1 : (Ideal.absNorm (Ideal.span {n}) : ℝ) =
      ∏ 𝔭 ∈ U, (Ideal.absNorm 𝔭.1 : ℝ) ^ vF 𝔭.1 n := by
    rw [absNorm_span_eq_prod n hn0]
    exact tprod_eq_prod fun 𝔭 h𝔭 => by rw [hU3 𝔭 h𝔭, pow_zero]
  have e2 : lamG F h L = ∏ 𝔭 ∈ U, lamP h L 𝔭.1 := by
    unfold lamG
    exact tprod_eq_prod fun 𝔭 h𝔭 => localMassFactor_of_valuation_eq_zero hK hF hs hd hLfull hLi 𝔭.2 (hU1 𝔭 h𝔭)
  have e3 : normD h L = ∏ 𝔭 ∈ U, (Ideal.absNorm 𝔭.1 : ℝ) ^ vd h L 𝔭.1 := by
    rw [normD_eq_prod hK hF hs hd hLfull hLi]
    exact tprod_eq_prod fun 𝔭 h𝔭 => by rw [hU1 𝔭 h𝔭, pow_zero]
  have h4 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ U →
      alphaN h L 𝔭.1 n / (1 - etaF K F 𝔭.1 ^ finrank K V *
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ))) = 1 := by
    intro 𝔭 h𝔭
    rw [alphaN_of_vd_zero_unit hK hF hs hd hLfull hLi 𝔭.2 (hU1 𝔭 h𝔭) hm (hU2 𝔭 h𝔭)]
    exact div_self (A5.eFac_pos 𝔭.2 hm).ne'
  have e4 : singS F h L n = ∏ 𝔭 ∈ U, alphaN h L 𝔭.1 n / (1 - etaF K F 𝔭.1 ^ finrank K V *
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ))) := by
    unfold singS
    exact tprod_eq_prod h4
  have e0 : ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 = ∏ 𝔭 ∈ U, psiP S L 𝔭.1 := by
    refine tprod_eq_prod fun 𝔭 h𝔭 => ?_
    rw [hpt 𝔭, hU3 𝔭 h𝔭, hU1 𝔭 h𝔭, h4 𝔭 h𝔭, localMassFactor_of_valuation_eq_zero hK hF hs hd hLfull hLi 𝔭.2 (hU1 𝔭 h𝔭)]
    simp
  rw [e0, e1, e2, e3, e4, ← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun 𝔭 _ => hpt 𝔭

theorem repMass_eq (hH : HermRepUnram) (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (hm : 2 ≤ finrank K V) {c : ℝ} (hc : MassConst K F (finrank K V - 1) c) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    repMass h L (algebraMap F K (n : F)) = c * lamG F h L * (normD h L)⁻¹ *
      ((Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * singS F h L n) := by
  have hn0 : n ≠ 0 := A5.ne_zero_of_mem_boxSet hn
  obtain ⟨x₀, hx₀⟩ := exists_vec_of_hermRep hH hK hs hd hm (algebraMap F K (n : F))
    ((hF _).mpr ⟨_, rfl⟩) (fun φ => (hn φ).1)
  have hne : h x₀ x₀ ≠ 0 := by
    rw [hx₀]
    intro e
    apply hn0
    apply RingOfIntegers.ext
    exact (algebraMap F K).injective (by rw [e]; simp)
  have h1 := repMass_eq_prod_psi (F := F) hK hF hs hd (vecSplitPerp h hne) hL hLi hc
  have h2 := tprod_localPsi_eq hLI hK hF hs hd (vecSplitPerp h hne) hL hLi (by omega) hn0 hx₀
  rw [h2] at h1
  have h3 : h (vecSplitPerp h hne).x₀ (vecSplitPerp h hne).x₀ = algebraMap F K (n : F) := hx₀
  rw [h3] at h1
  rw [h1]
  ring

end Formalism.HermitianLattices.Ext.L3.Step
end
end
end
