module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemPass
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastRatCastAndExpRat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeExistsMultipleIntegralPrimeToLStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulPrimePowMemConductorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatMulIntegralMemCmLatticePrimeToStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationBoundOfMulSqIntegral

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

noncomputable section

namespace GlobalTheory.SizeSqIntegral

theorem sz_nat_val (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D : ℕ) :
    Sz l lam (-(padicValNat l D : ℝ)) (D : ℂ) := by
  have h := GlobalTheory.SizeRat.sz_ratCast l lam (D : ℚ) (-(padicValNat l D : ℝ)) (by
    rw [padicValRat.of_nat, Nat.padicValNat_def]; simp)
  simpa using h

theorem sz_zero_of_isIntegral (l : ℕ) [hl : Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (x : ℂ)
    (h : IsIntegral ℤ x) : Sz l lam 0 x :=
  GlobalTheory.SzRules.sz_of_isIntegral 1 x (fun hd => hl.out.one_lt.ne' (Nat.dvd_one.1 hd)) (by simpa using h)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D M : ℕ) (x : ℂ), 0 < D → IsIntegral ℤ ((D : ℂ) * x ^ 2) → Sz l lam (-(padicValNat l D : ℝ) / 2) ((D : ℂ) * x) ∧ Sz l lam (-(padicValNat l D : ℝ) / 2) ((M * l ^ padicValNat l D : ℕ) : ℂ) := by
  intro l hl lam D M x _ hx
  constructor
  · apply GlobalTheory.SzRules.sz_of_sq
    have h := GlobalTheory.SzRules.sz_mul (sz_nat_val l lam D) (sz_zero_of_isIntegral l lam _ hx)
    rw [add_zero] at h
    convert h using 1
    ring
  · have h1 := sz_nat_val l lam (l ^ padicValNat l D)
    rw [Nat.padicValNat_def, Nat.multiplicity_prime_pow] at h1
    have h2 : Sz l lam 0 (M : ℂ) := sz_zero_of_isIntegral l lam _ (by simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (M : ℤ))))
    have h := GlobalTheory.SzRules.sz_mul h2 h1
    rw [zero_add, ← Nat.cast_mul] at h
    refine GlobalTheory.SzRules.sz_mono ?_ h
    have : (0 : ℝ) ≤ (padicValNat l D : ℝ) := Nat.cast_nonneg _
    linarith

end GlobalTheory.SizeSqIntegral
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationBoundOfMulSqIntegralStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

theorem _root_.GlobalTheory.T.algebraicValuation_bound_of_mul_sq_integral : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D M : ℕ) (x : ℂ), 0 < D → IsIntegral ℤ ((D : ℂ) * x ^ 2) → Sz l lam (-(padicValNat l D : ℝ) / 2) ((D : ℂ) * x) ∧ Sz l lam (-(padicValNat l D : ℝ) / 2) ((M * l ^ padicValNat l D : ℕ) : ℂ) := by
  first | exact @GlobalTheory.SizeSqIntegral.main | exact GlobalTheory.SizeSqIntegral.main | (intros; apply GlobalTheory.SizeSqIntegral.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralDiscMulCoordsOfCmFieldIntegral

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam

theorem isIntegral_coord_of_isIntegral (E : Type) [Field E] [NumberField E] [IsCMField E] (θ : E) (D : ℕ)
    (x : Fin 2 → FR E) (_hD : 0 < D) (hθ : IsIntegral ℤ θ)
    (hr : (θ - IsCMField.complexConj E θ) ^ 2 = -(D : E))
    (hu : IsIntegral ℤ ((x 0 : E) * θ + (x 1 : E))) (j : Fin 2) :
    IsIntegral ℤ ((D : FR E) * x j ^ 2) ∧ IsIntegral ℤ ((D : FR E) * x j) := by
  have hc : ∀ y : E, IsIntegral ℤ y → IsIntegral ℤ (IsCMField.complexConj E y) := fun y hy =>
    map_isIntegral_int (IsCMField.complexConj E) hy
  have hfix : ∀ y : FR E, IsCMField.complexConj E (y : E) = y := fun y =>
    IsCMField.complexConj_apply_eq_self E y
  set r := θ - IsCMField.complexConj E θ with hrdef
  have hri : IsIntegral ℤ r := hθ.sub (hc _ hθ)
  have h0 : IsIntegral ℤ ((x 0 : E) * r) := by
    have := hu.sub (hc _ hu)
    rw [map_add (f := _), map_mul, hfix, hfix] at this
    have e : (x 0 : E) * r = (x 0 : E) * θ + (x 1 : E) -
        ((x 0 : E) * IsCMField.complexConj E θ + (x 1 : E)) := by rw [hrdef]; ring
    rw [e]; exact this
  have h1 : IsIntegral ℤ ((x 1 : E) * r) := by
    have := (hu.mul hri).sub (h0.mul hθ)
    have e : (x 1 : E) * r = ((x 0 : E) * θ + (x 1 : E)) * r - (x 0 : E) * r * θ := by ring
    rw [e]; exact this
  have hj : IsIntegral ℤ ((x j : E) * r) := by
    fin_cases j
    · exact h0
    · exact h1
  have hD' : (D : E) = -r ^ 2 := by rw [hr]; ring
  have hinj : Function.Injective (algebraMap (FR E) E) := (algebraMap (FR E) E).injective
  have hx : algebraMap (FR E) E (x j) = (x j : E) := rfl
  constructor
  · rw [← (isIntegral_algebraMap_iff (B := E)), map_mul, map_pow, map_natCast, hx, hD']
    have e : -r ^ 2 * (x j : E) ^ 2 = -((x j : E) * r * ((x j : E) * r)) := by ring
    rw [e]; exact (hj.mul hj).neg
  · rw [← (isIntegral_algebraMap_iff (B := E)), map_mul, map_natCast, hx, hD']
    have e : -r ^ 2 * (x j : E) = -((x j : E) * r * r) := by ring
    rw [e]; exact (hj.mul hri).neg

end GlobalTheory.HilbFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralDiscMulCoordsOfCmFieldIntegralStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

theorem _root_.GlobalTheory.T.isIntegral_disc_mul_coords_of_cmField_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (θ : E) (D : ℕ) (x : Fin 2 → FR E), 0 < D → IsIntegral ℤ θ → (θ - IsCMField.complexConj E θ) ^ 2 = -(D : E) → IsIntegral ℤ ((x 0 : E) * θ + (x 1 : E)) → ∀ j, IsIntegral ℤ ((D : FR E) * x j ^ 2) ∧ IsIntegral ℤ ((D : FR E) * x j) := by
  first | exact @GlobalTheory.HilbFam.isIntegral_coord_of_isIntegral | exact GlobalTheory.HilbFam.isIntegral_coord_of_isIntegral | (intros; apply GlobalTheory.HilbFam.isIntegral_coord_of_isIntegral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPassScaled

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.RoadE

open GlobalTheory.CMVal

variable {E : Type} [Field E] [NumberField E]

def passScaled (t : E) (c : Ideal (OF E)) (y : (Af E)ˣ) (N : ℕ) : Lat (FR E) where
  carrier := {x | ∃ y' ∈ lattice c y, (N : E) * y' = ptE t x}
  add_mem' := fun {x x'} ⟨a, ha, hxa⟩ ⟨b, hb, hxb⟩ => ⟨a + b, (latticeSub c y).add_mem ha hb, by
    have : ptE t (x + x') = ptE t x + ptE t x' := by simp only [ptE, Pi.add_apply, Subfield.coe_add]; ring
    rw [this, ← hxa, ← hxb]; ring⟩
  zero_mem' := ⟨0, (latticeSub c y).zero_mem, by simp [ptE]⟩
  smul_mem' := fun a x ⟨b, hb, hxb⟩ => ⟨algebraMap (OF E) E a * b, mul_mem_lattice (algebraMap_mem_orderC c a) hb, by
    rw [ptE_smul, ← hxb]; ring⟩

end GlobalTheory.RoadE

namespace GlobalTheory.RoadE
open GlobalTheory.CMVal

theorem passl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (y : (Af E)ˣ) (θ : E) (D M₀ : ℕ), IsBaseCond 𝔣 → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → OneOver l y → 0 < D → IsIntegral ℤ θ → (θ - IsCMField.complexConj E θ) ^ 2 = -(D : E) → ¬ l ∣ M₀ → ∃ (M M' : ℕ) (L : Lat (FR E)), ¬ l ∣ M ∧ ¬ l ∣ M' ∧ M₀ ∣ M' ∧ HasLevel (M' * l ^ (padicValNat l D + a0 𝔣 l)) L ∧ (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y' ∈ lattice (condQ 𝔣 Q) y, ((M * D : ℕ) : E) * y' = (x 0 : E) * θ + (x 1 : E)) ∧ (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb (FR E)), Sz l lam (-(padicValNat l D : ℝ) / 2) ((i (v j) : ℝ) : ℂ)) ∧ Sz l lam (-(padicValNat l D : ℝ) / 2) ((M' * l ^ (padicValNat l D + a0 𝔣 l) : ℕ) : ℂ) := by
  intro E _ _ _ l _ lam 𝔣 Q y θ D M₀ hf hQ hy hD hθ hθD hM₀
  have hl : l.Prime := Fact.out
  set c := condQ 𝔣 Q with hc
  obtain ⟨M, hMl, hMint⟩ := GlobalTheory.T.cmLattice_exists_multiple_integral_prime_to_l E l c y hl hy
  obtain ⟨M₁, hM₁l, hM₁c⟩ := GlobalTheory.T.exists_coprime_mul_prime_pow_mem_conductor E l 𝔣 Q hl hf hQ
  have hM₁0 : M₁ ≠ 0 := by rintro rfl; exact hM₁l (dvd_zero l)
  have hM0 : M ≠ 0 := by rintro rfl; exact hMl (dvd_zero l)
  have hR : 0 < M₁ * l ^ a0 𝔣 l := Nat.pos_of_ne_zero (mul_ne_zero hM₁0 (pow_ne_zero _ hl.ne_zero))
  obtain ⟨M₂, hM₂l, hM₂⟩ := GlobalTheory.T.nat_mul_integral_mem_cmLattice_prime_to E l c y (M₁ * l ^ a0 𝔣 l) hl hy hR hM₁c
  obtain ⟨D', hD'⟩ := (fun {p n : ℕ} => _root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat p n)) (p := l) (n := D)
  have hD'l : ¬ l ∣ D' := by
    rintro ⟨e, he⟩
    apply pow_succ_padicValNat_not_dvd (p := l) hD.ne'
    refine ⟨e, ?_⟩
    calc D = l ^ padicValNat l D * D' := hD'
      _ = l ^ (multiplicity l D + 1) * e := by rw [he, ← Nat.padicValNat_def, pow_succ]; ring
  have hnat : ∀ n : ℕ, IsIntegral ℤ (n : E) := fun n => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (n : ℤ)))
  have hDE : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  have hDF : (D : FR E) ≠ 0 := by exact_mod_cast hD.ne'
  have key : ∀ x ∈ passScaled θ c y (M * D), ∀ j,
      IsIntegral ℤ ((D : FR E) * ((D : FR E)⁻¹ * x j) ^ 2) ∧ IsIntegral ℤ (x j) := by
    rintro x ⟨y', hy', hxy⟩ j
    have hpt : (((D : FR E)⁻¹ * x 0 : FR E) : E) * θ + (((D : FR E)⁻¹ * x 1 : FR E) : E) = (M : E) * y' := by
      simp only [ptE] at hxy
      push_cast at hxy ⊢
      have h' : (M : E) * y' = (D : E)⁻¹ * (((x 0 : FR E) : E) * θ + ((x 1 : FR E) : E)) := by
        rw [← hxy]; field_simp
      rw [h']; ring
    have h := GlobalTheory.T.isIntegral_disc_mul_coords_of_cmField_integral E θ D (fun j => (D : FR E)⁻¹ * x j) hD hθ hθD (by rw [hpt]; exact hMint y' hy') j
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    simp only [mul_inv_cancel_left₀ hDF] at h2
    exact h2
  refine ⟨M, M₀ * M * D' * M₂ * M₁, passScaled θ c y (M * D), hMl, ?_, ⟨M * D' * M₂ * M₁, by ring⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    exacts [hM₀ h, hMl h, hD'l h, hM₂l h, hM₁l h]
  · refine ⟨fun w hw => ?_, fun x hx => ?_⟩
    · have hwj : ∀ j, IsIntegral ℤ ((w j : FR E) : E) := by
        intro j
        have hwj1 : w j ∈ (1 : Submodule (𝓞 (FR E)) (FR E)) := Submodule.mem_pi.1 hw j (Set.mem_univ j)
        obtain ⟨a, ha⟩ := Submodule.mem_one.1 hwj1
        rw [← ha]
        exact (RingOfIntegers.isIntegral_coe a).map (RingHom.toIntAlgHom (maximalRealSubfield E).subtype)
      have hP : IsIntegral ℤ ((M₀ : E) * (((w 0 : FR E) : E) * θ + ((w 1 : FR E) : E))) :=
        (hnat M₀).mul (((hwj 0).mul hθ).add (hwj 1))
      refine ⟨_, hM₂ _ hP, ?_⟩
      have e : (D : E) = (l : E) ^ padicValNat l D * D' := by exact_mod_cast hD'
      simp only [ptE, Pi.smul_apply, Algebra.smul_def, Subfield.coe_mul, map_natCast]
      push_cast
      linear_combination ((M : E) * M₂ * M₁ * (l : E) ^ a0 𝔣 l * M₀ * (((w 0 : FR E) : E) * θ + ((w 1 : FR E) : E))) * e
    · intro j _
      change x j ∈ (1 : Submodule (𝓞 (FR E)) (FR E))
      rw [Submodule.mem_one]
      exact ⟨⟨x j, (key x hx j).2⟩, rfl⟩
  · intro x; exact Iff.rfl
  · intro w hw j i
    have h1 := (key w hw j).1
    set f : FR E →ₐ[ℤ] ℂ := RingHom.toIntAlgHom (Complex.ofRealHom.comp i) with hf
    have h2 : IsIntegral ℤ ((D : ℂ) * (f ((D : FR E)⁻¹ * w j)) ^ 2) := by
      have := h1.map f
      simpa [map_mul, map_pow, map_natCast] using this
    have h3 := (GlobalTheory.T.algebraicValuation_bound_of_mul_sq_integral l lam D 0 (f ((D : FR E)⁻¹ * w j)) hD h2).1
    have h4 : (D : ℂ) * f ((D : FR E)⁻¹ * w j) = ((i (w j) : ℝ) : ℂ) := by
      rw [← map_natCast f D, ← map_mul, mul_inv_cancel_left₀ hDF]
      rfl
    rwa [h4] at h3
  · have h := (GlobalTheory.T.algebraicValuation_bound_of_mul_sq_integral l lam D (M₀ * M * D' * M₂ * M₁ * l ^ a0 𝔣 l) 0 hD (by simpa using (isIntegral_zero : IsIntegral ℤ (0 : ℂ)))).2
    rwa [show M₀ * M * D' * M₂ * M₁ * l ^ (padicValNat l D + a0 𝔣 l) =
      M₀ * M * D' * M₂ * M₁ * l ^ a0 𝔣 l * l ^ padicValNat l D by ring]

end GlobalTheory.RoadE
end
end
