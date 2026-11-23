module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffNormFormOfFamilyMemRangeIntegrallyClosed
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
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.Localization.Ideal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsIsFractionRingStalkImageOfGenericPointStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffNormFormOfFamilyMemRangeIntegrallyClosedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.coeff_normFormOfFamily_mem_range_integrallyClosed : ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L] [Algebra A K]
    [IsFractionRing A K] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L] {m : ℕ}
    (x : Fin m → L), (∀ i, IsIntegral A (x i)) →
    ∀ s, (GlobalTheory.NormSheaf.normForm K L x).coeff s ∈ (algebraMap A K).range := by
  first | exact @GlobalTheory.NormSheaf.IntegralCoeff.coeff_normForm_mem_range | exact GlobalTheory.NormSheaf.IntegralCoeff.coeff_normForm_mem_range | (intros; apply GlobalTheory.NormSheaf.IntegralCoeff.coeff_normForm_mem_range <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFormCoefficientIdealMapLocalizationAway

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheaf

theorem normForm_coeff_smul (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ}
    (y : Fin m → L) (c : K) (s : Fin m →₀ ℕ) :
    (normForm K L (fun i => algebraMap K L c * y i)).coeff s =
      c ^ Module.finrank K L * (normForm K L y).coeff s := by
  have hM : ∀ i, (Algebra.leftMulMatrix (Module.finBasis K L) (algebraMap K L c * y i)).map
      (MvPolynomial.C : K →+* MvPolynomial (Fin m) K) =
      (MvPolynomial.C c : MvPolynomial (Fin m) K) • (Algebra.leftMulMatrix (Module.finBasis K L) (y i)).map
        (MvPolynomial.C : K →+* MvPolynomial (Fin m) K) := by
    intro i
    rw [← Algebra.smul_def, map_smul]
    ext a b
    simp [Matrix.map_apply, Matrix.smul_apply, MvPolynomial.C_mul]
  have : normForm K L (fun i => algebraMap K L c * y i) =
      MvPolynomial.C (c ^ Module.finrank K L) * normForm K L y := by
    unfold normForm
    simp_rw [hM, smul_comm (MvPolynomial.X _ : MvPolynomial (Fin m) K) (MvPolynomial.C c), ← Finset.smul_sum,
      Matrix.det_smul, Fintype.card_fin, map_pow]
  rw [this, MvPolynomial.coeff_C_mul]

end GlobalTheory.NormSheaf

namespace GlobalTheory.NormSheaf

theorem normIdeal_map_away : ∀ (A K L B A' B' : Type) [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A K] [Algebra B L] [Algebra A' K] [Algebra B' L]
    [Algebra A A'] [Algebra B B'] [Algebra A B] (f : A) [IsLocalization.Away f A']
    [IsLocalization.Away (algebraMap A B f) B'],
    (algebraMap A' K).comp (algebraMap A A') = algebraMap A K →
    (algebraMap B' L).comp (algebraMap B B') = algebraMap B L →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp (algebraMap A B) →
    Function.Injective (algebraMap A' K) →
    (∀ {m : ℕ} (g : Fin m → B) s,
      (GlobalTheory.NormSheaf.normForm K L (fun i => algebraMap B L (g i))).coeff s ∈ (algebraMap A K).range) →
    ∀ J : Ideal B, (GlobalTheory.NormSheaf.normIdeal A K L B J).map (algebraMap A A') =
      GlobalTheory.NormSheaf.normIdeal A' K L B' (J.map (algebraMap B B')) := by
  intro A K L B A' B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f _ _ h1 h2 h3 hinj hcoef J
  have e1 : ∀ x : A, algebraMap A' K (algebraMap A A' x) = algebraMap A K x := fun x => by
    simpa using RingHom.congr_fun h1 x
  have e2 : ∀ x : B, algebraMap B' L (algebraMap B B' x) = algebraMap B L x := fun x => by
    simpa using RingHom.congr_fun h2 x
  have e3 : ∀ x : A, algebraMap K L (algebraMap A K x) = algebraMap B L (algebraMap A B x) := fun x => by
    simpa using RingHom.congr_fun h3 x
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    unfold normIdeal
    rw [Ideal.span_le]
    rintro a ⟨m, g, hg, s, hs⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    apply Ideal.subset_span
    refine ⟨m, fun i => algebraMap B B' (g i), fun i => Ideal.mem_map_of_mem _ (hg i), s, ?_⟩
    rw [e1, hs]
    simp only [e2]
  · unfold normIdeal
    rw [Ideal.span_le]
    rintro a' ⟨m, g', hg', s, hs⟩
    set b := algebraMap A B f with hb
    have hloc : ∀ i, ∃ (j : B) (n : ℕ), j ∈ J ∧ g' i * algebraMap B B' (b ^ n) = algebraMap B B' j := by
      intro i
      obtain ⟨⟨⟨j, hj⟩, ⟨_, n, rfl⟩⟩, h⟩ :=
        (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers b) B').1 (hg' i)
      exact ⟨j, n, hj, h⟩
    choose j n hj hn using hloc
    set N := ∑ i, n i
    have hN : ∀ i, g' i * algebraMap B B' (b ^ N) = algebraMap B B' (j i * b ^ (N - n i)) := by
      intro i
      have hle : n i ≤ N := Finset.single_le_sum (fun k _ => Nat.zero_le (n k)) (Finset.mem_univ i)
      rw [← Nat.add_sub_cancel' hle, pow_add, map_mul, ← mul_assoc, hn i, Nat.add_sub_cancel_left, map_mul]
    have hjJ : ∀ i, j i * b ^ (N - n i) ∈ J := fun i => J.mul_mem_right _ (hj i)
    set c := algebraMap A K f
    have himg : ∀ i, algebraMap B L (j i * b ^ (N - n i)) =
        algebraMap K L (c ^ N) * algebraMap B' L (g' i) := by
      intro i
      rw [← e2, ← hN i, map_mul, e2, map_pow, map_pow, hb, ← e3, mul_comm]
    obtain ⟨a, ha⟩ := hcoef (fun i => j i * b ^ (N - n i)) s
    have hcoef' : algebraMap A K a = (c ^ N) ^ Module.finrank K L * algebraMap A' K a' := by
      rw [ha, hs]
      simp only [himg]
      exact normForm_coeff_smul K L _ _ s
    have hmem : a ∈ normIdeal A K L B J := Ideal.subset_span ⟨m, _, hjJ, s, ha⟩
    have key : algebraMap A A' a = algebraMap A A' (f ^ (N * Module.finrank K L)) * a' := by
      apply hinj
      rw [map_mul, e1, e1, hcoef', map_pow, pow_mul]
    have hu : IsUnit (algebraMap A A' (f ^ (N * Module.finrank K L))) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit f).pow _
    rw [SetLike.mem_coe, ← Ideal.unit_mul_mem_iff_mem _ hu, ← key]
    exact Ideal.mem_map_of_mem _ hmem

end GlobalTheory.NormSheaf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFormCoefficientIdealMapLocalizationAwayStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.normFormCoefficientIdeal_map_localizationAway : ∀ (A K L B A' B' : Type) [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A K] [Algebra B L] [Algebra A' K] [Algebra B' L]
    [Algebra A A'] [Algebra B B'] [Algebra A B] (f : A) [IsLocalization.Away f A']
    [IsLocalization.Away (algebraMap A B f) B'],
    (algebraMap A' K).comp (algebraMap A A') = algebraMap A K →
    (algebraMap B' L).comp (algebraMap B B') = algebraMap B L →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp (algebraMap A B) →
    Function.Injective (algebraMap A' K) →
    (∀ {m : ℕ} (g : Fin m → B) s,
      (GlobalTheory.NormSheaf.normForm K L (fun i => algebraMap B L (g i))).coeff s ∈ (algebraMap A K).range) →
    ∀ J : Ideal B, (GlobalTheory.NormSheaf.normIdeal A K L B J).map (algebraMap A A') =
      GlobalTheory.NormSheaf.normIdeal A' K L B' (J.map (algebraMap B B')) := by
  first | exact @GlobalTheory.NormSheaf.normIdeal_map_away | exact GlobalTheory.NormSheaf.normIdeal_map_away | (intros; apply GlobalTheory.NormSheaf.normIdeal_map_away <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoeffIdealFamilyMapBasicOpen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

theorem isLocalization_away_of_eq_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (g : Γ(X, U)) (V : X.Opens) (hV : V = X.basicOpen g) (hle : V ≤ U) :
    letI := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra;
    IsLocalization.Away g Γ(X, V) := by
  subst hV
  exact hU.isLocalization_basicOpen g

theorem famIdeal_map_basicOpen : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y] [GlobalTheory.IsNormalScheme Z]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ Set.range π →
    (GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom =
      GlobalTheory.NormSheafDescent.famIdeal π hK hfd I (Z.affineBasicOpen f) := by
  intro Y Z π _ _ _ hK hfd I U f hU
  by_cases hD : genPt π ∈ Z.basicOpen f
  · have hζU : genPt π ∈ U.1 := Z.basicOpen_le f hD
    have hD' : genPt π ∈ (Z.affineBasicOpen f).1 := hD
    have hUD : ((Z.affineBasicOpen f : Z.affineOpens) : Set Z) ⊆ Set.range π :=
      fun x hx => hU (Z.basicOpen_le f hx)
    letI := fieldK π hK
    letI := algKL π
    obtain ⟨hdomA, hfrA⟩ := GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint Y Z π U.1 U.2 hU hζU
    obtain ⟨_, hfrA'⟩ := GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint Y Z π (Z.basicOpen f) (Z.affineBasicOpen f).2 hUD hD
    letI iA := algAK π U.1 hζU
    letI iB := algBL π U.1 hζU
    letI iA' := algAK π (Z.basicOpen f) hD
    letI iB' := algBL π (Z.basicOpen f) hD
    letI iAA' : Algebra Γ(Z, U) Γ(Z, Z.basicOpen f) :=
      (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom.toAlgebra
    have hleY : π ⁻¹ᵁ Z.basicOpen f ≤ π ⁻¹ᵁ U.1 := π.preimage_mono (Z.basicOpen_le f)
    letI iBB' : Algebra Γ(Y, π ⁻¹ᵁ U.1) Γ(Y, π ⁻¹ᵁ Z.basicOpen f) :=
      (Y.presheaf.map (homOfLE hleY).op).hom.toAlgebra
    letI iAB : Algebra Γ(Z, U) Γ(Y, π ⁻¹ᵁ U.1) := (π.app U.1).hom.toAlgebra
    haveI : IsLocalization.Away f Γ(Z, Z.basicOpen f) := U.2.isLocalization_basicOpen f
    haveI : IsLocalization.Away (algebraMap Γ(Z, U) Γ(Y, π ⁻¹ᵁ U.1) f) Γ(Y, π ⁻¹ᵁ Z.basicOpen f) :=
      isLocalization_away_of_eq_basicOpen (U.2.preimage π) (π.app U.1 f) _
        (Scheme.preimage_basicOpen π f) hleY
    have h1 : (algebraMap Γ(Z, Z.basicOpen f) (Z.presheaf.stalk (genPt π))).comp
        (algebraMap Γ(Z, U) Γ(Z, Z.basicOpen f)) = algebraMap Γ(Z, U) (Z.presheaf.stalk (genPt π)) := by
      ext a
      exact Z.presheaf.germ_res_apply (homOfLE (Z.basicOpen_le f)) (genPt π) hD a
    have h2 : (algebraMap Γ(Y, π ⁻¹ᵁ Z.basicOpen f) Y.functionField).comp
        (algebraMap Γ(Y, π ⁻¹ᵁ U.1) Γ(Y, π ⁻¹ᵁ Z.basicOpen f)) =
          algebraMap Γ(Y, π ⁻¹ᵁ U.1) Y.functionField := by
      ext a
      exact Y.presheaf.germ_res_apply (homOfLE hleY) (genericPoint Y) hD a
    have h3 : (algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField).comp
        (algebraMap Γ(Z, U) (Z.presheaf.stalk (genPt π))) =
          (algebraMap Γ(Y, π ⁻¹ᵁ U.1) Y.functionField).comp (algebraMap Γ(Z, U) Γ(Y, π ⁻¹ᵁ U.1)) := by
      ext a
      exact Scheme.Hom.germ_stalkMap_apply π U.1 (genericPoint Y) hζU a
    have h4 : Function.Injective (algebraMap Γ(Z, Z.basicOpen f) (Z.presheaf.stalk (genPt π))) :=
      IsFractionRing.injective _ _
    have h5 : ∀ {m : ℕ} (g : Fin m → Γ(Y, π ⁻¹ᵁ U.1)) s,
        (GlobalTheory.NormSheaf.normForm (Z.presheaf.stalk (genPt π)) Y.functionField
          (fun i => algebraMap Γ(Y, π ⁻¹ᵁ U.1) Y.functionField (g i))).coeff s ∈
            (algebraMap Γ(Z, U) (Z.presheaf.stalk (genPt π))).range := by
      intro m g s
      haveI : IsIntegrallyClosed Γ(Z, U) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen U.2
      letI iAL : Algebra Γ(Z, U) Y.functionField :=
        ((algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField).comp
          (algebraMap Γ(Z, U) (Z.presheaf.stalk (genPt π)))).toAlgebra
      haveI : IsScalarTower Γ(Z, U) (Z.presheaf.stalk (genPt π)) Y.functionField :=
        IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      have hfin : (π.app U.1).hom.Finite := π.finite_app U.1 U.2
      let φ : Γ(Y, π ⁻¹ᵁ U.1) →ₐ[Γ(Z, U)] Y.functionField :=
        { algebraMap Γ(Y, π ⁻¹ᵁ U.1) Y.functionField with
          commutes' := fun a => (congrArg (fun h => h a) h3).symm }
      refine GlobalTheory.T.coeff_normFormOfFamily_mem_range_integrallyClosed Γ(Z, U) (Z.presheaf.stalk (genPt π)) Y.functionField _ (fun i => ?_) s
      have hi : IsIntegral Γ(Z, U) (g i) := hfin.to_isIntegral (g i)
      exact hi.map φ
    have hJ : I.ideal ⟨π ⁻¹ᵁ (Z.affineBasicOpen f).1, (Z.affineBasicOpen f).2.preimage π⟩ =
        (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩).map
          (algebraMap Γ(Y, π ⁻¹ᵁ U.1) Γ(Y, π ⁻¹ᵁ Z.basicOpen f)) :=
      (I.map_ideal (U := ⟨π ⁻¹ᵁ (Z.affineBasicOpen f).1, (Z.affineBasicOpen f).2.preimage π⟩)
        (V := ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) hleY).symm
    simp only [famIdeal, dif_pos hζU, dif_pos hD']
    rw [hJ]
    exact GlobalTheory.T.normFormCoefficientIdeal_map_localizationAway Γ(Z, U) (Z.presheaf.stalk (genPt π)) Y.functionField Γ(Y, π ⁻¹ᵁ U.1)
      Γ(Z, Z.basicOpen f) Γ(Y, π ⁻¹ᵁ Z.basicOpen f) f h1 h2 h3 h4 h5 _
  · have hbot : Z.basicOpen f = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨y, rfl⟩ := hU (Z.basicOpen_le f hx)
      exact hD (((genericPoint_specializes y).map π.continuous).mem_open (Z.basicOpen f).isOpen hx)
    haveI : Subsingleton Γ(Z, Z.basicOpen f) :=
      CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty hbot)
    haveI : Subsingleton Γ(Z, (Z.affineBasicOpen f : Z.Opens)) := this
    ext x
    rw [Subsingleton.elim x 0]
    exact iff_of_true (Ideal.zero_mem _) (Ideal.zero_mem _)

end GlobalTheory.NormSheafDescent
end
end
