module

public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaFixedIntegralOfSeparatingElementStatement
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerDeepAtOnePlaceUnitAtOtherStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFact

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaFixedRootsPerturbedPolynomial

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem eq_of_perturbed_pow_sub_one {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (y z u : R) (m : ℕ) (h : Polynomial ℤ)
    (hy : y ^ m - 1 = u * Polynomial.aeval y h) (hz : z ^ m - 1 = u * Polynomial.aeval z h)
    (hu : u ∈ IsLocalRing.maximalIdeal R) (hzy : z - y ∈ IsLocalRing.maximalIdeal R)
    (hm : (m : R) ∉ IsLocalRing.maximalIdeal R) : z = y := by
  by_contra hne
  have hne' : z - y ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨k, hk⟩ : z - y ∣ Polynomial.aeval z h - Polynomial.aeval y h := by
    have := Polynomial.sub_dvd_eval_sub z y (h.map (algebraMap ℤ R))
    simpa only [Polynomial.eval_map_algebraMap] using this
  have hS := Commute.geom_sum₂_mul (Commute.all z y) m
  have hS' : (∑ i ∈ Finset.range m, z ^ i * y ^ (m - 1 - i)) = u * k := by
    apply mul_right_cancel₀ hne'
    rw [hS]
    linear_combination hz - hy + u * hk
  have hu0 : IsLocalRing.residue R u = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hu
  have hzy0 : IsLocalRing.residue R z = IsLocalRing.residue R y := by
    have := (IsLocalRing.residue_eq_zero_iff _).mpr hzy
    rwa [map_sub, sub_eq_zero] at this
  have hm0 : (m : IsLocalRing.ResidueField R) ≠ 0 := by
    intro h0
    apply hm
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, h0]
  have hmpos : m ≠ 0 := by
    rintro rfl
    simp at hm0
  have hy1 : (IsLocalRing.residue R y) ^ m = 1 := by
    have := congrArg (IsLocalRing.residue R) hy
    rwa [map_sub, map_mul, hu0, zero_mul, map_pow, map_one, sub_eq_zero] at this
  have hy0 : IsLocalRing.residue R y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hmpos] at hy1
    exact zero_ne_one hy1
  have := congrArg (IsLocalRing.residue R) hS'

  simp only [map_sum, map_mul, map_pow, hu0, zero_mul, hzy0] at this
  rw [geom_sum₂_self] at this
  exact mul_ne_zero hm0 (pow_ne_zero _ hy0) this

theorem exists_roots_fixed_of_mem_Ine (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A' : ValuationSubring Ω) (σ : G E Ω)
    (hσ : σ ∈ Ine (F := E) A') (b e : Ω) (m : ℕ) (f : Polynomial ℤ) (he : IsIntegral ℤ e)
    (hσe : σ e = e) (hv : A'.valuation (1 - e) < 1) (hm : A'.valuation (m : Ω) = 1)
    (hf : f.Monic) (hfm : f.natDegree = m) (hb : Polynomial.aeval b f = 0) :
    ∃ ys : Multiset Ω, Multiset.card ys = m ∧ (∀ y ∈ ys, IsIntegral ℤ y ∧ σ y = y) ∧
      e * (b ^ m - 1) = (ys.map (fun y => b - y)).prod := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  set h : Polynomial ℤ := X ^ m - C 1 - f with hh
  have hdeg : h.degree < (m : WithBot ℕ) := by
    have h1 : (X ^ m - C 1 : Polynomial ℤ).Monic := Polynomial.monic_X_pow_sub_C 1 hm0
    have h2 : (X ^ m - C 1 : Polynomial ℤ).degree = m :=
      Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hm0) 1
    have h3 : f.degree = m := by rw [Polynomial.degree_eq_natDegree hf.ne_zero, hfm]
    rw [← h2]
    exact Polynomial.degree_sub_lt (h2.trans h3.symm) h1.ne_zero
      (by rw [h1.leadingCoeff, hf.leadingCoeff])
  let R := integralClosure ℤ Ω
  let e0 : R := ⟨e, he⟩
  let g0 : Polynomial R := f.map (algebraMap ℤ R) + C e0 * h.map (algebraMap ℤ R)
  have hf0 : (f.map (algebraMap ℤ R)).Monic := hf.map _
  have hf0d : (f.map (algebraMap ℤ R)).degree = m := by
    rw [hf.degree_map, Polynomial.degree_eq_natDegree hf.ne_zero, hfm]
  have hlt : (C e0 * h.map (algebraMap ℤ R)).degree < (f.map (algebraMap ℤ R)).degree := by
    rw [hf0d, ← Polynomial.smul_eq_C_mul]
    exact lt_of_le_of_lt ((Polynomial.degree_smul_le _ _).trans Polynomial.degree_map_le) hdeg
  have hg0 : g0.Monic := hf0.add_of_left hlt
  have hg0d : g0.degree = m := by
    rw [← hf0d]; exact Polynomial.degree_add_eq_left_of_degree_lt hlt
  have hev : ∀ y : Ω, Polynomial.aeval y g0 = Polynomial.aeval y f + e * Polynomial.aeval y h := by
    intro y
    simp only [g0, map_add (f := _), map_mul, Polynomial.aeval_map_algebraMap, Polynomial.aeval_C]
    rfl
  have hhev : ∀ y : Ω, Polynomial.aeval y h = y ^ m - 1 - Polynomial.aeval y f := by
    intro y
    simp [hh]
  let g : Polynomial Ω := g0.map (algebraMap R Ω)
  have hg : g.Monic := hg0.map _
  have hgd : g.natDegree = m := by
    rw [hg0.natDegree_map, Polynomial.natDegree_eq_of_degree_eq_some hg0d]
  have hcard : Multiset.card g.roots = g.natDegree := IsAlgClosed.card_roots_eq_natDegree
  refine ⟨g.roots, hcard.trans hgd, ?_, ?_⟩
  · intro y hy
    have hy0 : Polynomial.aeval y g0 = 0 := by
      have := (Polynomial.mem_roots hg.ne_zero).mp hy
      rwa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] at this
    have hyint : IsIntegral ℤ y := by
      have : IsIntegral R y := ⟨g0, hg0, hy0⟩
      exact isIntegral_trans y this
    refine ⟨hyint, ?_⟩
    have hyA : y ∈ A' := mem_of_isIntegral_int A' hyint
    have hσ' := mem_Ine.mp hσ
    have hzA : σ y ∈ A' := (apply_mem_iff_of_mem_Dec hσ'.1 y).mpr hyA
    have huA : 1 - e ∈ A' := (A'.valuation_le_one_iff _).mp hv.le
    have e1 : y ^ m - 1 = (1 - e) * Polynomial.aeval y h := by
      rw [hev] at hy0
      linear_combination hy0 - hhev y
    have e2 : (σ y) ^ m - 1 = (1 - e) * Polynomial.aeval (σ y) h := by
      have := congrArg σ e1
      rw [map_sub, map_pow, map_one, map_mul, map_sub, map_one, hσe] at this
      rw [this]
      congr 1
      exact (Polynomial.aeval_algHom_apply (σ : Ω →+* Ω).toIntAlgHom y h).symm
    have hae : ∀ x : A', ((Polynomial.aeval x h : A') : Ω) = Polynomial.aeval (x : Ω) h :=
      fun x => (Polynomial.aeval_algHom_apply A'.subtype.toIntAlgHom x h).symm
    have := eq_of_perturbed_pow_sub_one (R := A') ⟨y, hyA⟩ ⟨σ y, hzA⟩ ⟨1 - e, huA⟩ m h
      (Subtype.ext (by simpa [hae] using e1)) (Subtype.ext (by simpa [hae] using e2))
      ((A'.valuation_lt_one_iff _).mpr hv)
      ((A'.valuation_lt_one_iff _).mpr (hσ'.2 y ((A'.valuation_le_one_iff _).mpr hyA)))
      (fun hh' => by
        have := (A'.valuation_lt_one_iff _).mp hh'
        rw [show ((m : A') : Ω) = m from by simp, hm] at this
        exact lt_irrefl _ this)
    exact congrArg Subtype.val this
  · have := congrArg (Polynomial.eval b)
      (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hg hcard)
    rw [Polynomial.eval_multiset_prod, Multiset.map_map, Polynomial.eval_map_algebraMap, hev,
      hhev, hb] at this
    simp only [Function.comp_def, eval_sub, eval_X, eval_C] at this
    rw [this]; ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaFixedRootsPerturbedPolynomialStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_inertia_fixed_roots_perturbed_polynomial : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A' : ValuationSubring Ω) (σ : G E Ω), σ ∈ Ine (F := E) A' → ∀ (b e : Ω) (m : ℕ) (f : Polynomial ℤ), IsIntegral ℤ e → σ e = e → A'.valuation (1 - e) < 1 → A'.valuation (m : Ω) = 1 → f.Monic → f.natDegree = m → Polynomial.aeval b f = 0 → ∃ ys : Multiset Ω, Multiset.card ys = m ∧ (∀ y ∈ ys, IsIntegral ℤ y ∧ σ y = y) ∧ e * (b ^ m - 1) = (ys.map (fun y => b - y)).prod := by
  first | exact @GlobalTheory.exists_roots_fixed_of_mem_Ine | exact GlobalTheory.exists_roots_fixed_of_mem_Ine | (intros; apply GlobalTheory.exists_roots_fixed_of_mem_Ine <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFactStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.iwasawaDecomposition_fact : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (σ : G E Ω), σ ∈ Dec (F := E) A → ∀ t : Ω, A.valuation (σ t) = A.valuation t := by
  first | exact @GlobalTheory.Dec_valuation_apply_eq | exact GlobalTheory.Dec_valuation_apply_eq | (intros; apply GlobalTheory.Dec_valuation_apply_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaTwoPlacesOverSamePrimeTrivialMeet

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.InertiaTwoPlaces

open Polynomial

theorem fix_of_fix_integral {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (σ : G E Ω) (h : ∀ b : Ω, IsIntegral ℤ b → σ b = b) : σ = 1 := by
  ext x
  obtain ⟨s, t, hs, ht, hs1, e⟩ := ReciprocityTheory.Gal.exists_den E (⊤ : ValuationSubring Ω) (x := x)
    ((ValuationSubring.valuation_le_one_iff _ _).mpr trivial)
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs1
  have h2 : σ s * σ x = σ t := by rw [← map_mul, e]
  rw [h s hs, h t ht, ← e] at h2
  exact mul_left_cancel₀ hs0 h2

theorem eq_of_mem_Ine_of_mem_Ine : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)),
    IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → ∀ σ ∈ Ine (F := E) A,
    σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A := by
  intro E Ω _ _ _ _ _ A A' P hA hA' σ hσ hσ' hne
  by_contra hAA
  apply hne
  apply fix_of_fix_integral
  intro b hb
  by_contra hD
  have hD0 : σ b - b ≠ 0 := sub_ne_zero.mpr hD
  set f0 := minpoly ℤ b with hf0
  have hf0m : f0.Monic := minpoly.monic hb
  have hf0b : Polynomial.aeval b f0 = 0 := minpoly.aeval ℤ b
  set d := f0.natDegree with hd
  have hnat : ∀ n : ℕ, A'.valuation (n : Ω) ≤ 1 := fun n => ReciprocityTheory.Gal.valuation_natCast_le_one A' n
  obtain ⟨m, hdm, hmu⟩ : ∃ m : ℕ, d ≤ m ∧ A'.valuation (m : Ω) = 1 := by
    by_cases h1 : A'.valuation (d : Ω) = 1
    · exact ⟨d, le_rfl, h1⟩
    refine ⟨d + 1, Nat.le_succ d, ?_⟩
    by_contra h2
    have l1 : A'.valuation (d : Ω) < 1 := lt_of_le_of_ne (hnat d) h1
    have l2 : A'.valuation ((d + 1 : ℕ) : Ω) < 1 := lt_of_le_of_ne (hnat _) h2
    have : A'.valuation (((d + 1 : ℕ) : Ω) - (d : Ω)) < 1 := by
      rw [sub_eq_add_neg]
      exact Valuation.map_add_lt _ l2 (by rw [Valuation.map_neg]; exact l1)
    push_cast at this
    simp at this
  set f1 : Polynomial ℤ := Polynomial.X ^ (m - d) * f0 with hf1
  have hf1m : f1.Monic := (Polynomial.monic_X_pow _).mul hf0m
  have hf1d : f1.natDegree = m := by
    rw [hf1, (Polynomial.monic_X_pow _).natDegree_mul hf0m, Polynomial.natDegree_X_pow, ← hd]
    omega
  have hf1b : Polynomial.aeval b f1 = 0 := by simp [hf1, hf0b]
  have hσA : σ ∈ Dec (F := E) A := Ine_le_Dec A hσ
  have hbD : IsIntegral ℤ (σ b - b) :=
    (hb.map ((σ : Ω ≃ₐ[E] Ω).toAlgHom.restrictScalars ℤ)).sub hb
  have hc : IsIntegral ℤ ((σ b - b) ^ m) := hbD.pow m
  have hc0 : (σ b - b) ^ m ≠ 0 := pow_ne_zero _ hD0
  obtain ⟨e0, he0i, he0A, he0A'⟩ := GlobalTheory.T.exists_integer_deep_at_one_place_unit_at_other E Ω A A' P hA hA' (Ne.symm hAA) _ hc hc0
  obtain ⟨e, hei, hef, heA, heA'⟩ := GlobalTheory.T.exists_inertiaFixed_integral_of_separating_element E Ω A A' σ hσ' e0 _ he0i he0A he0A'
  obtain ⟨ys, hcard, hys, hprod⟩ := GlobalTheory.T.exists_inertia_fixed_roots_perturbed_polynomial E Ω A' σ hσ' b e m f1 hei hef heA' hmu hf1m hf1d hf1b
  have hbm : A.valuation (b ^ m - 1) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (ReciprocityTheory.Gal.mem_of_isIntegral_int A ((hb.pow m).sub isIntegral_one))
  have h1 : A.valuation (e * (b ^ m - 1)) < A.valuation (σ b - b) ^ m := by
    rw [Valuation.map_mul, ← Valuation.map_pow]
    calc A.valuation e * A.valuation (b ^ m - 1) ≤ A.valuation e * 1 := mul_le_mul_of_nonneg_left hbm zero_le'
      _ = A.valuation e := mul_one _
      _ < _ := heA
  have h2 : A.valuation (σ b - b) ^ m ≤ A.valuation ((ys.map (fun y => b - y)).prod) := by
    rw [map_multiset_prod, Multiset.map_map, ← hcard]
    rw [← Multiset.card_map (fun y => A.valuation (b - y)) ys]
    apply Multiset.pow_card_le_prod
    intro z hz
    rw [Multiset.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hyf := (hys y hy).2
    have e1 : σ b - b = σ (b - y) - (b - y) := by rw [map_sub, hyf]; ring
    rw [e1, sub_eq_add_neg]
    refine (Valuation.map_add _ _ _).trans ?_
    rw [Valuation.map_neg, GlobalTheory.T.iwasawaDecomposition_fact E Ω A σ hσA, max_self]
  rw [← hprod] at h2
  exact absurd h2 (not_le.mpr h1)

end GlobalTheory.InertiaTwoPlaces
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaTwoPlacesOverSamePrimeTrivialMeetStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.inertia_two_places_over_same_prime_trivial_meet : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → ∀ σ ∈ Ine (F := E) A, σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A := by
  first | exact @GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine | exact GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine | (intros; apply GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine <;> assumption)
end
end
