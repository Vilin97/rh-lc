module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LaurentCechNerveLevelSpecTensorPower
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MassFormulaConjugationAction
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagM3PadicGlobalStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FractionRingRingEquiv
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsMultiProjPrimeExtTo
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsometricFamilyIntersectionEqStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MassFormulaConjugationAction
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumTermDiscreteValuationStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumsVanishAtPlaces
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelGeometricGenericNumberStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootPowerSumMixedExpansionStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.UniformizerDivisorCycleNumberStatement
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DegreeEqCardToMultiset

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem degree_eq_card_toMultiset {α : Type} (d : α →₀ ℕ) :
    d.degree = Multiset.card (Finsupp.toMultiset d) := by
  rw [Finsupp.card_toMultiset]
  rfl

theorem ofFn_monoLines_perm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J J' : Type}
    (ℓ : J' → HermLine ι) (e : J → J') (μ : J →₀ ℕ) (m : J' →₀ ℕ) (d : ℕ)
    (hm : Finsupp.toMultiset m = (Finsupp.toMultiset μ).map e)
    (hd : (Finsupp.toMultiset m).toList.length = d) :
    ((Finsupp.toMultiset μ).map (ℓ ∘ e)).toList.Perm (List.ofFn (monoLines ℓ m d)) := by
  have h1 : List.ofFn (monoLines ℓ m d) = (Finsupp.toMultiset m).toList.map ℓ := by
    refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, hd]) fun n h₁ h₂ => ?_
    have hn : n < (Finsupp.toMultiset m).toList.length := by rwa [List.length_map] at h₂
    rw [List.getElem_ofFn, List.getElem_map]
    simp only [monoLines]
    rw [dite_eq_left hn]
    rfl
  rw [h1, ← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList, hm,
    Multiset.map_map]

theorem arMono_mapDomain_some {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N)
    (II : IntersectionSystem) (hII : IsIntersectionSystem II) (t : ℝ) (μ : Ψ × Fin N →₀ ℕ)
    (hμ : μ.degree = dimFl Ψ N + 1) :
    M.arMono II t (Finsupp.mapDomain some μ) =
      arList (II M.K M.ι) M.P (μ.toMultiset.map (M.x t)).toList / (M.δ : ℝ) := by
  classical
  have hms : Finsupp.toMultiset (Finsupp.mapDomain some μ) = (Finsupp.toMultiset μ).map some :=
    (Finsupp.toMultiset_map _ _).symm
  have hcard : Multiset.card (Finsupp.toMultiset μ) = dimFl Ψ N + 1 := by
    rw [← degree_eq_card_toMultiset, hμ]
  have hdeg : (Finsupp.mapDomain some μ).degree = dimFl Ψ N + 1 := by
    rw [degree_eq_card_toMultiset, hms, Multiset.card_map, hcard]
  have hnone : (Finsupp.mapDomain some μ) none = 0 :=
    Finsupp.mapDomain_notin_range _ _ (by simp)
  have hlen : (Finsupp.toMultiset (Finsupp.mapDomain some μ)).toList.length = dimFl Ψ N + 1 := by
    rw [Multiset.length_toList, hms, Multiset.card_map, hcard]
  have hperm := ofFn_monoLines_perm (M.line t) some μ (Finsupp.mapDomain some μ) (dimFl Ψ N + 1) hms hlen
  have hall : ∀ r ∈ (Finsupp.toMultiset (Finsupp.mapDomain some μ)).toList, IsSmoothHerm (M.line t r) := by
    intro r hr
    rw [Multiset.mem_toList, hms, Multiset.mem_map] at hr
    obtain ⟨r', -, rfl⟩ := hr
    exact M.x_smooth t r'
  have hsm : ∀ j, IsSmoothHerm (monoLines (M.line t) (Finsupp.mapDomain some μ) (dimFl Ψ N + 1) j) := by
    intro j
    have hj : (j : ℕ) < (Finsupp.toMultiset (Finsupp.mapDomain some μ)).toList.length := by
      rw [hlen]; exact j.2
    simp only [monoLines]
    rw [dite_eq_left hj]
    exact hall _ (List.get_mem _ _)
  have hmain := arNum_linear_arList_symm.2 M.K M.ι M.P (dimFl Ψ N) M.arith (II M.K M.ι) (hII M.K M.ι) _ _ hsm
    (by simpa [Function.comp_def, RootModel.line] using hperm)
  unfold RootModel.arMono
  rw [if_pos hdeg, hnone, pow_zero, mul_one]
  congr 1
  exact hmain.symm

theorem arFun_toA_eq_arNum : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (II : IntersectionSystem), IsIntersectionSystem II → ∀ (t : ℝ) (F : RP Ψ N), F.IsHomogeneous (dimFl Ψ N + 1) → M.arFun II t (toA F) = arNum (II M.K M.ι) M.P (M.x t) F / (M.δ : ℝ) := by
  intro Ψ _ _ N M II hII t F hF
  classical
  have hmono : ∀ μ ∈ F.support, M.arFun II t (toA (monomial μ (F.coeff μ))) =
      F.coeff μ * (arList (II M.K M.ι) M.P (μ.toMultiset.map (M.x t)).toList / (M.δ : ℝ)) := by
    intro μ hμ
    have hdeg : μ.degree = dimFl Ψ N + 1 := by
      have h := hF (MvPolynomial.mem_support_iff.1 hμ)
      rw [Finsupp.degree_eq_weight_one]
      exact h
    have h1 : toA (monomial μ (F.coeff μ)) =
        (F.coeff μ) • (basisMonomials (Option (Ψ × Fin N)) ℝ) (Finsupp.mapDomain some μ) := by
      simp [toA, MvPolynomial.rename_monomial, MvPolynomial.smul_monomial]
    rw [h1, map_smul, RootModel.arFun, Module.Basis.constr_basis, smul_eq_mul,
      arMono_mapDomain_some M II hII t μ hdeg]
  have hsum : toA F = ∑ μ ∈ F.support, toA (monomial μ (F.coeff μ)) := by
    unfold toA
    conv_lhs => rw [F.as_sum]

    rw [map_sum]

  rw [hsum, map_sum, Finset.sum_congr rfl hmono]
  unfold arNum
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [mul_div_assoc]

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumsVanishAtPlacesStatement

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.power_sums_vanish_at_places : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) → HasConstants ℤ A y → ∀ D : ℕ, IsArithVar (mCoordIdeal y) (D + 1) → ∀ (p : Nat.Primes) (N : ℕ) (x : Fin N → K → ℤ), (AtPlacesOver A Ω p fun O _ _ _ _ => PowerSumsVanish (pointIdeal O y) D x) → PowerSumsVanish (extTo (ZP p) (mCoordIdeal y)) D x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.powerSumsVanish_extTo_of_atPlacesOver | exact GlobalTheory.CompanionTheory.Ar.Num.powerSumsVanish_extTo_of_atPlacesOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.powerSumsVanish_extTo_of_atPlacesOver <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumHeightChangeModel

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.Prop6Model

theorem arNum_mixDiff {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι ℤ)) {σ : Type}
    (A A' : σ → HermLine ι) (F : MvPolynomial σ ℝ) :
    arNum I P (Sum.elim A A') (mixDiff F) = arNum I P A F - arNum I P A' F := by
  obtain ⟨hadd, hsmul, -, -, hren⟩ := arNum_linear_arList_symm.1 K ι I P (σ ⊕ σ) (Sum.elim A A')
  have h : mixDiff F = rename Sum.inl F + C (-1) * rename Sum.inr F := by
    simp [mixDiff, sub_eq_add_neg]
  rw [h, hadd, hsmul, hren, hren, Sum.elim_comp_inl, Sum.elim_comp_inr]
  ring

theorem le_dimFl_succ (Ψ : Type) [Fintype Ψ] (τ : Ψ) (N : ℕ) : N ≤ dimFl Ψ N + 1 := by
  have hc : 1 ≤ Fintype.card Ψ := Fintype.card_pos_iff.2 ⟨τ⟩
  have h1 : N * (N - 1) / 2 ≤ dimFl Ψ N := by
    unfold dimFl
    exact Nat.le_mul_of_pos_left _ hc
  have h2 : N ≤ N * (N - 1) / 2 + 1 := by
    rcases N with _ | _ | n
    · simp
    · simp
    · have h3 : (n + 1) * 2 ≤ (n + 1 + 1) * (n + 1 + 1 - 1) := by
        rw [Nat.add_sub_cancel]
        nlinarith
      have h4 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 h3
      omega
  omega

variable {Ψ : Type} {N : ℕ}

theorem liePs_isHomogeneous (j m : ℕ) (l : Ψ ⊕ Ψ) :
    (liePs j m l : MvPolynomial (Ψ × Fin N) ℝ).IsHomogeneous m := by
  cases l with
  | inl τ =>
    refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using (isHomogeneous_X ℝ (τ, i)).pow m
  | inr τ =>
    refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using ((isHomogeneous_X ℝ (τ, i)).neg).pow m

theorem bracket_isHomogeneous [Fintype Ψ] [DecidableEq Ψ] (j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (p k : ℕ) (τ : Ψ) :
    (bracket j φ p k τ : MvPolynomial (Ψ × Fin N) ℝ).IsHomogeneous (k - 1) := by
  unfold bracket
  have h := (isHomogeneous_C (Ψ × Fin N) (k : ℝ)).mul
    (IsHomogeneous.sum Finset.univ (fun τ' => C (co φ p k (Sum.inl τ) τ') * liePs j (k - 1) τ') (k - 1)
      fun τ' _ => by
        simpa using (isHomogeneous_C (Ψ × Fin N) (co φ p k (Sum.inl τ) τ')).mul
          (liePs_isHomogeneous (N := N) j (k - 1) τ'))
  simpa using h

end GlobalTheory.CompanionTheory.Ar.Num.Prop6Model

namespace GlobalTheory.CompanionTheory.Ar.Num


open Prop6Model in
theorem power_sum_height_model_change : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (R : SecondRoots M) (II : IntersectionSystem), IsIntersectionSystem II → ∀ (S : Finset Nat.Primes) (j : ℕ) (φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ)), R.IsChange S → R.LocalAtPlaces j S φ → ∀ t : ℝ, 0 < t → ∀ (τ : Ψ) (k : ℕ), 1 ≤ k → k ≤ N → ∀ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N + 1 - k) → M.arFun II t (toA (pk τ k * Q)) = R.model.arFun II t (toA (pk τ k * Q)) + ∑ p ∈ S, Real.log (p : ℕ) * M.geoFun (toA (bracket j (φ p) p k τ * Q)) := by
  intro Ψ _ _ N M R II hII S j φ hCh hLoc t ht τ k hk1 hkN Q hQ
  classical
  have hkd : k ≤ dimFl Ψ N + 1 := hkN.trans (le_dimFl_succ Ψ τ N)
  have hpk : (pk τ k : RP Ψ N).IsHomogeneous k := by
    refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using (isHomogeneous_X ℝ (τ, i)).pow k
  have hF : (pk τ k * Q : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1) := by
    have h := hpk.mul hQ
    rwa [Nat.add_sub_cancel' hkd] at h
  have hδ : (M.δ : ℝ) ≠ 0 := by exact_mod_cast M.δ_pos.ne'
  have e1 := arFun_toA_eq_arNum Ψ N M II hII t _ hF
  have e2 : R.model.arFun II t (toA (pk τ k * Q)) =
      arNum (II M.K M.ι) M.P (R.x t) (pk τ k * Q) / (M.δ : ℝ) :=
    arFun_toA_eq_arNum Ψ N R.model II hII t _ hF
  obtain ⟨Hs, hHs, hHs0, hexp⟩ := GlobalTheory.T.root_power_sum_mixed_expansion Ψ N (dimFl Ψ N) k hk1 hkd τ Q hQ
  obtain ⟨hvert, hiso⟩ := hCh
  have hlink := GlobalTheory.T.isometric_family_intersection_eq M.K M.ι M.P (dimFl Ψ N) M.arith (II M.K M.ι) (hII M.K M.ι) (Ψ × Fin N) S R.pairs
    hvert (M.x t) (R.x t) (fun i => M.x_smooth t i) (fun i => R.x_smooth t i) (hiso t ht) _ _ hexp
  obtain ⟨A, i1, i2, i3, i4, hinj, hconst, hloc⟩ := hLoc
  have hdiff : arNum (II M.K M.ι) M.P (M.x t) (pk τ k * Q) - arNum (II M.K M.ι) M.P (R.x t) (pk τ k * Q) =
      ∑ p ∈ S, Real.log (p : ℕ) * ((M.δ : ℝ) * M.geoFun (toA (bracket j (φ p) p k τ * Q))) := by
    rw [← arNum_mixDiff]
    refine Eq.trans hlink (Finset.sum_congr rfl fun p hp => ?_)
    congr 1
    obtain ⟨hirr, hmod, hv⟩ := zp_model M.K M.ι M.P (dimFl Ψ N) M.arith p
    have hm3 := GlobalTheory.T.flag_m3_padic_global M.K M.ι M.Ω M.y A hinj hconst (dimFl Ψ N) M.arith p Ψ N j (φ p) S R.pairs hvert
      (fun m _ hm O _ _ _ _ _ _ _ => (hloc p hp m hm O).1)
    have hz := GlobalTheory.T.power_sums_vanish_at_places M.K M.ι M.Ω M.y A hinj hconst (dimFl Ψ N) M.arith p N (fun i => R.xdeg (τ, i))
      (fun m _ hm O _ _ _ _ _ _ _ => (hloc p hp m hm O).2 τ)
    have hH : (bracket j (φ p) p k τ * Q : RP Ψ N).IsHomogeneous (dimFl Ψ N) := by
      have h := (bracket_isHomogeneous (N := N) j (φ p) p k τ).mul hQ
      have e : k - 1 + (dimFl Ψ N + 1 - k) = dimFl Ψ N := by omega
      rwa [e] at h
    have h1 := GlobalTheory.T.power_sum_term_discrete_valuation (ZP p) _ hirr M.K M.ι _ _ hmod p Ψ N j (φ p) k hk1 hkd τ Q Hs hQ hHs hHs0 _
      (hv _ S R.pairs hvert) hm3 hz
    have h2 := GlobalTheory.T.uniformizer_divisor_cycle_number (ZP p) _ hirr M.K M.ι _ _ hmod 1 1 (Ψ × Fin N) M.xdeg
      (bracket j (φ p) p k τ * Q) (dimFl Ψ N) hH [] (by simp)
    simp only [Units.val_one, one_mul, pow_one, Nat.cast_one] at h2
    have h3 := genNum_zp_eq_rat M.K M.ι M.P p (Ψ × Fin N) M.xdeg (bracket j (φ p) p k τ * Q) []
    have h4 := GlobalTheory.T.root_model_geometric_generic_number Ψ N M II hII _ hH
    refine h1.trans ?_
    refine Eq.trans h2 ?_
    rw [h3, h4]
    field_simp
  have hsum : ∑ p ∈ S, Real.log (p : ℕ) * ((M.δ : ℝ) * M.geoFun (toA (bracket j (φ p) p k τ * Q))) =
      (M.δ : ℝ) * ∑ p ∈ S, Real.log (p : ℕ) * M.geoFun (toA (bracket j (φ p) p k τ * Q)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e1, e2]
  rw [hsum] at hdiff
  field_simp
  linarith

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumHeightChangeModelStatement

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.power_sum_height_change_model : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (R : SecondRoots M) (II : IntersectionSystem), IsIntersectionSystem II → ∀ (S : Finset Nat.Primes) (j : ℕ) (φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ)), R.IsChange S → R.LocalAtPlaces j S φ → ∀ t : ℝ, 0 < t → ∀ (τ : Ψ) (k : ℕ), 1 ≤ k → k ≤ N → ∀ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N + 1 - k) → M.arFun II t (toA (pk τ k * Q)) = R.model.arFun II t (toA (pk τ k * Q)) + ∑ p ∈ S, Real.log (p : ℕ) * M.geoFun (toA (bracket j (φ p) p k τ * Q)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.power_sum_height_model_change | exact GlobalTheory.CompanionTheory.Ar.Num.power_sum_height_model_change | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.power_sum_height_model_change <;> assumption)
end
end
