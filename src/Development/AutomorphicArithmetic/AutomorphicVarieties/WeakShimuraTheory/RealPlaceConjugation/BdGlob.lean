module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.CardGlobalCocyclesLeOfIwasawaRank
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.CcConj
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.KrFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.RankCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.Strict
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.EvenRt

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.residualCharacter_complexConjugation_eq_one :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (T : Tower D) (σ : G T.F Ω), IsCC σ → ∀ w ∈ [0, wPs, -wPs], T.rbU w σ = 1 := by
  intro Ω _ _ _ l _ c D hD T σ hσ w hw
  have hτ : IsCC (resQ T.F σ) := by
    unfold IsCC at *
    exact hσ
  have hconj := isConj_of_isComplexConjugation Ω (resQ T.F σ) D.cc hτ hD.isCC
  have hP : D.Psi (resQ T.F σ) = 1 := by
    obtain ⟨u, hu⟩ := isConj_iff.mp hconj
    rw [← hD.Psi_even, ← hu]
    simp only [map_mul, map_inv]
    rw [mul_comm, inv_mul_cancel_left]
  have hth : D.th (AlgEquiv.restrictScalars ℚ σ) = D.al (AlgEquiv.restrictScalars ℚ σ) := by
    have : D.th (resQ T.F σ) = (D.al * D.Psi) (resQ T.F σ) := by
      unfold Raw.th
      rfl
    rw [MonoidHom.mul_apply, hP, mul_one] at this
    exact this
  have hrt : (T.fr ∅).rt w σ = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · simp only [Fr.rt, Tower.fr, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_zero, Prod.snd_zero, zpow_zero, mul_one]
    · simp only [Fr.rt, Tower.fr, wPs, MonoidHom.coe_mk, OneHom.coe_mk, zpow_zero, one_mul, zpow_one,
        MonoidHom.coe_comp, Function.comp_apply]
      unfold chi
      cases T.pr <;> simp [lab, Raw.ps, hth]
    · simp only [Fr.rt, Tower.fr, wPs, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_neg, Prod.snd_neg, neg_zero, zpow_zero, one_mul, zpow_neg, zpow_one,
        MonoidHom.coe_comp, Function.comp_apply]
      unfold chi
      cases T.pr <;> simp [lab, Raw.ps, hth]
  show (Units.map _) ((T.fr ∅).rt w σ) = 1
  rw [hrt, map_one]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.StrResidueLeCocyclesVanishingOnInertiaKernel

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical Pointwise

theorem UpperTheory.V.Ws.str_residue_le_cocycles_vanishing_on_inertia_kernel :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (T : Tower D) (w : ℤ × ℤ), (T.fr ∅).Str (residue c.O) w ≤ cocOff (charRep (T.rbU w)) (ineOff T.F Ω 1 ∩ T.Kr) := by
  intro Ω _ _ _ l _ c D hG T w z hz
  rw [Fr.Str, Submodule.mem_inf] at hz
  obtain ⟨⟨hlc, hcoc, hN, -⟩, n, hn⟩ := hz
  have hK := residualKernel_properties D hG T
  refine ⟨hlc, ?_, ?_⟩
  · intro g h
    rw [hcoc]
    simp [charRep, Tower.rbU]
  · rintro g ⟨⟨A, -, hgA⟩, hgK⟩
    have hrb : D.rbar (resQ T.F g) = 1 := hK.2.2.2.2.1 g hgK
    have hrt : residue c.O ((T.fr ∅).rt w g : c.O) = 1 := by
      have := congrArg Units.val (hK.2.2.2.2.2.1 w g hrb)
      simpa [Tower.rbU] using this
    by_cases hA : A.valuation (l : Ω) < 1
    · obtain ⟨v, ⟨σ, hσ⟩, -⟩ := T.cover A hA
      have hσA : σ⁻¹ • A = T.pl v := by
        ext x
        rw [ValuationSubring.mem_inv_pointwise_smul_iff]
        exact hσ x
      have hgA' : g • A = A := MulAction.mem_stabilizer_iff.1 hgA.1
      have hdec : σ⁻¹ * g * σ ∈ (T.fr ∅).Gv v := by
        show (σ⁻¹ * g * σ) • T.pl v = T.pl v
        rw [← hσA, mul_smul, mul_smul, smul_inv_smul, hgA']
      have hconj : (T.fr ∅).rt w (σ⁻¹ * g * σ) = (T.fr ∅).rt w g := by
        rw [map_mul, map_mul, map_inv, mul_comm ((T.fr ∅).rt w σ)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
      have hz0 : z (σ⁻¹ * g * σ) = 0 := by
        rw [hn v _ hdec, hconj, hrt, one_mul, sub_self]
      have hz1 : z 1 = 0 := by
        have := hcoc 1 1
        simpa using this
      have e1 := hcoc (σ⁻¹ * g) σ
      have e2 := hcoc σ⁻¹ g
      have e3 := hcoc σ⁻¹ σ
      rw [inv_mul_cancel, hz1] at e3
      have hmul : residue c.O ((T.fr ∅).rt w (σ⁻¹ * g) : c.O) = residue c.O ((T.fr ∅).rt w σ⁻¹ : c.O) := by
        rw [map_mul, Units.val_mul, map_mul, hrt, mul_one]
      rw [hmul, e2, hz0] at e1
      have hu : IsUnit (residue c.O ((T.fr ∅).rt w σ⁻¹ : c.O)) := ((T.fr ∅).rt w σ⁻¹).isUnit.map _
      have key : residue c.O ((T.fr ∅).rt w σ⁻¹ : c.O) * z g = 0 := by
        linear_combination e3 - e1
      exact (mul_eq_zero.1 key).resolve_left hu.ne_zero
    · refine hN g ?_
      refine ⟨A, ?_, hgA, hrb⟩
      intro p hp
      rw [Finset.mem_insert] at hp
      rcases hp with rfl | hp
      · exact hA
      · simp at hp
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.BdGlob

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem isLocalHom_algebraMap_padicInt_coef_O {l : ℕ} [Fact l.Prime] (c : Coef l) :
    IsLocalHom (algebraMap ℤ_[l] c.O) := by
  haveI := c.fin
  apply RingHom.IsIntegral.isLocalHom
  · exact (Algebra.IsIntegral.of_finite ℤ_[l] c.O).isIntegral
  · intro a b h
    have h' := congrArg (fun x : c.O => (x : PadicAlgCl l)) h
    simp only [Subalgebra.coe_algebraMap] at h'
    have hinj : Function.Injective (algebraMap ℤ_[l] (PadicAlgCl l)) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)]
      exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp (fun a b h => Subtype.ext h)
    exact hinj h'

private theorem finite_residueField_coef {l : ℕ} [Fact l.Prime] (c : Coef l) :
    Finite (ResidueField c.O) := by
  haveI := c.fin
  haveI := isLocalHom_algebraMap_padicInt_coef_O c
  exact IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[l]) inferInstance

private theorem prime_nsmul_residueField_coef_eq_zero {l : ℕ} [Fact l.Prime] (c : Coef l) (m : ResidueField c.O) :
    l • m = 0 := by
  haveI := isLocalHom_algebraMap_padicInt_coef_O c
  have h0 : IsLocalRing.residue c.O (algebraMap ℤ_[l] c.O (l : ℤ_[l])) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2
      (fun hu => PadicInt.p_nonunit (isUnit_of_map_unit (algebraMap ℤ_[l] c.O) _ hu))
  have h1 : ((l : ResidueField c.O)) = 0 := by
    rw [map_natCast] at h0
    rw [← map_natCast (IsLocalRing.residue c.O)]
    exact h0
  rw [nsmul_eq_mul, h1, zero_mul]

theorem UpperTheory.V.Ws.rank_cocycleSpaces_le_of_towerIwasawaRank :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (T : Tower D) (r g : ℕ), (plDvd T.F (prodS D)).ncard ≤ g → XRk l 1 T.Kr r → (∀ w, Module.rank (ResidueField c.O) ((T.fr ∅).Str (residue c.O) w) ≤ (r + 1 : ℕ)) ∧ (∀ w ∈ [0, wPs, -wPs], Module.rank (ResidueField c.O) ((T.fr ∅).Zgl (residue c.O) w) ≤ (r + 2 + g : ℕ)) ∧ ∀ w, Module.rank (ResidueField c.O) ((T.fr ∅).Zgl (residue c.O) w) ≤ T.d + (r + 2 + g : ℕ) := by
  intro hP Ω _ _ _ l _ c D hD T r g hg hX
  obtain ⟨hN, hO, hI, hC, hK, hU, ⟨hS0, hSl⟩, hIne, -⟩ := residualKernel_properties D hD T
  haveI := finite_residueField_coef c
  have tor := prime_nsmul_residueField_coef_eq_zero c
  have triv : ∀ (w : ℤ × ℤ), ∀ σ ∈ T.Kr, ∀ m : ResidueField c.O, (charRep (T.rbU w)) σ m = m := by
    intro w σ hσ m
    simp [charRep, hU w σ (hK σ hσ)]
  have hinf : ∀ (w : ℤ × ℤ), ∀ σ ∈ ineOff (↥T.F) Ω (prodS D), ∀ m : ResidueField c.O,
      (charRep (T.rbU w)) σ m = m := by
    intro w σ hσ m
    simp [charRep, hU w σ (hIne σ hσ).2]
  have sub : ∀ (w : ℤ × ℤ), (T.fr ∅).Zgl (residue c.O) w ≤
      cocOff (charRep (T.rbU w)) (ineOff (↥T.F) Ω (prodS D)) := by
    intro w z hz
    obtain ⟨h1, h2, h3, -⟩ := hz
    refine ⟨h1, ?_, ?_⟩
    · intro a b
      rw [h2 a b]
      simp [charRep, Tower.rbU]
    · intro a ha
      exact h3 a (hIne a ha).1
  refine ⟨?_, ?_, ?_⟩
  · intro w
    have h := card_cocycles_vanishing_on_inertia_le_pow T.F Ω l (ResidueField c.O) (ResidueField c.O) tor (charRep (T.rbU w)) T.Kr r hI
      (triv w) hX
    refine le_trans (Submodule.rank_mono (str_residue_le_cocycles_vanishing_on_inertia_kernel D hD T w)) ?_
    haveI := h.1
    exact rank_le_of_card_le_pow_card_field _ _ _ h
  · intro w hw
    have h := (card_globalCocycles_le_of_iwasawaRank hP T.F Ω l _ _ tor (charRep (T.rbU w)) T.Kr (prodS D) r g hD.l_odd hS0 hSl hg
      (hinf w) hN hO hI (triv w) hC hX).2 T.realF
      (fun σ hσ m => by simp [charRep, residualCharacter_complexConjugation_eq_one D hD T σ hσ w hw])
    refine le_trans (Submodule.rank_mono (sub w)) ?_
    haveI := h.1
    exact rank_le_of_card_le_pow_card_field _ _ _ h
  · intro w
    have h := (card_globalCocycles_le_of_iwasawaRank hP T.F Ω l _ _ tor (charRep (T.rbU w)) T.Kr (prodS D) r g hD.l_odd hS0 hSl hg
      (hinf w) hN hO hI (triv w) hC hX).1
    refine le_trans (Submodule.rank_mono (sub w)) ?_
    haveI := h.1
    have h2 := rank_le_of_card_le_pow_card_field _ _ _ h
    refine le_trans h2 (le_of_eq ?_)
    simp only [Tower.d]
    push_cast
    ring
end
end
