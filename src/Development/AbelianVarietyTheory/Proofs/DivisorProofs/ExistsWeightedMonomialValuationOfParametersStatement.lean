module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeGeneratorTopForm
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueCoordinatesOfLocalModelBelowPlace

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair


open IsLocalRing in
theorem exists_residue_coords_of_locModel : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (N r : ℕ) (V : Place c) (hC : V.Contains Q) (u : Fin r → V.ring),
    (∃ x : Fin N → L, TrBasis c x) →
    (∀ q ∈ IsLocalRing.maximalIdeal Q,
      (⟨q, hC _ q.2⟩ : V.ring) ∈ IsLocalRing.maximalIdeal V.ring) →
    (∀ P : MvPolynomial (Fin r) Q, (∃ α, P.coeff α ∉ IsLocalRing.maximalIdeal Q) →
      IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P)) →
    (∀ f : V.ring, ∃ P R : MvPolynomial (Fin r) Q,
      IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R) ∧
      f * MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R =
        MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P) →
    ∃ (j : ℕ) (s : Fin j → Q), r + j + 1 = N ∧
      ∀ P : MvPolynomial (Fin (r + j)) ℂ, P ≠ 0 →
        IsUnit (MvPolynomial.eval₂ V.const
          (Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring)) P) := by
  intro L _ c Q hQ
  letI := hQ.isLocalRing
  intro N r V hC u hx hm hunitP hloc
  classical
  let φ : Q →+* V.ring := Q.subtype.codRestrict V.ring fun q => hC _ q.2
  letI : Algebra ℂ V.ring := V.const.toAlgebra
  letI : Algebra ℂ L := c.toAlgebra
  letI : Algebra ℂ Q := (c.codRestrict Q hQ.const_mem).toAlgebra
  letI : Algebra Q V.ring := φ.toAlgebra
  haveI : IsScalarTower ℂ V.ring L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℂ Q V.ring := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  haveI : IsLocalHom (algebraMap Q V.ring) := ⟨fun q hq => by
    by_contra hq'
    have hqm : q ∈ maximalIdeal Q := (mem_maximalIdeal _).2 hq'
    exact (mem_maximalIdeal _).1 (hm q hqm) hq⟩
  haveI : Algebra.EssFiniteType ℂ V.ring := V.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ V.ring
  obtain ⟨x, hx⟩ := hx
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
  rw [Cardinal.mk_fin] at h2
  have h3 := trdeg_residueField_of_trdeg ℂ V.ring L h2.symm
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V.ring
  obtain ⟨hN, -⟩ := exists_basis_kaehler_of_trdeg ℂ L h2.symm ht
  let ub : Fin r → ResidueField V.ring := fun i => residue V.ring (u i)
  have key : ∀ P : MvPolynomial (Fin r) Q, residue V.ring (MvPolynomial.eval₂ φ u P) =
      MvPolynomial.aeval ub (P.map (residue Q)) := by
    intro P
    rw [MvPolynomial.eval₂_comp_left, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
  have hmem : ∀ Pb : MvPolynomial (Fin r) (ResidueField Q),
      MvPolynomial.aeval ub Pb ∈ Algebra.adjoin (ResidueField Q) (Set.range ub) := fun Pb => by
    rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨Pb, rfl⟩
  have hind : AlgebraicIndependent (ResidueField Q) ub := by
    rw [algebraicIndependent_iff]
    intro Pb hPb
    by_contra hne
    obtain ⟨P, rfl⟩ := MvPolynomial.map_surjective (residue Q) residue_surjective Pb
    obtain ⟨α, hα⟩ := MvPolynomial.ne_zero_iff.1 hne
    rw [MvPolynomial.coeff_map] at hα
    have hu := hunitP P ⟨α, fun h => hα ((residue_eq_zero_iff _).2 h)⟩
    rw [← residue_ne_zero_iff_isUnit] at hu
    exact hu ((key P).trans hPb)
  have halg : Algebra.IsAlgebraic (Algebra.adjoin (ResidueField Q) (Set.range ub))
      (ResidueField V.ring) := by
    constructor
    intro y
    obtain ⟨f, rfl⟩ := residue_surjective y
    obtain ⟨P, R, hR, hf⟩ := hloc f
    let a : Algebra.adjoin (ResidueField Q) (Set.range ub) := ⟨_, hmem (P.map (residue Q))⟩
    let b : Algebra.adjoin (ResidueField Q) (Set.range ub) := ⟨_, hmem (R.map (residue Q))⟩
    have hb : (b : ResidueField V.ring) ≠ 0 := by
      change MvPolynomial.aeval ub (R.map (residue Q)) ≠ 0
      rw [← key]; exact (residue_ne_zero_iff_isUnit _).2 hR
    have hb0 : b ≠ 0 := fun h => hb (by rw [h]; rfl)
    refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, fun h => hb0 ?_, ?_⟩
    · simpa using congrArg (fun p => p.coeff 1) h
    · have e := congrArg (residue V.ring) hf
      rw [map_mul, key, key] at e
      simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      change (b : ResidueField V.ring) * residue V.ring f - (a : ResidueField V.ring) = 0
      change residue V.ring f * (b : ResidueField V.ring) = (a : ResidueField V.ring) at e
      rw [mul_comm, e, sub_self]
  have hub : IsTranscendenceBasis (ResidueField Q) ub := hind.isTranscendenceBasis_iff_isAlgebraic.2 halg
  obtain ⟨T, hT⟩ := exists_isTranscendenceBasis ℂ (ResidueField Q)
  have hB := hT.sumElim_comp hub
  have hc : (r : Cardinal) + Cardinal.mk T = ((N - 1 : ℕ) : Cardinal) := by
    rw [← h3, ← hB.cardinalMk_eq_trdeg, Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id,
      Cardinal.mk_fin]
  haveI hfin : Finite T := Cardinal.lt_aleph0_iff_finite.1
    (lt_of_le_of_lt le_add_self (by rw [hc]; exact Cardinal.natCast_lt_aleph0))
  have hcard : r + Nat.card T = N - 1 := by
    rw [← Nat.cast_card (α := T)] at hc
    exact_mod_cast hc
  set j := Nat.card T with hj
  let e : Fin j ≃ T := (Finite.equivFin T).symm
  let s : Fin j → Q := fun i => Function.surjInv residue_surjective ((e i : ResidueField Q))
  have hs : ∀ i, residue Q (s i) = (e i : ResidueField Q) := fun i =>
    Function.surjInv_eq residue_surjective _
  let g : Fin (r + j) → Fin r ⊕ T := fun i => Sum.map id e (finSumFinEquiv.symm i)
  have hg : Function.Injective g :=
    (Sum.map_injective.2 ⟨Function.injective_id, e.injective⟩).comp finSumFinEquiv.symm.injective
  have hind2 := hB.1.comp g hg
  have hv : residue V.ring ∘ (Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring)) =
      Sum.elim ub (algebraMap (ResidueField Q) (ResidueField V.ring) ∘ Subtype.val) ∘ g := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [g, ub, Fin.append_left]
    · simp only [Function.comp_apply, Fin.append_right, g, finSumFinEquiv_symm_apply_natAdd,
        Sum.map_inr, Sum.elim_inr]
      rw [← hs, ResidueField.algebraMap_residue]
      rfl
  refine ⟨j, s, by omega, fun P hP => ?_⟩
  rw [← residue_ne_zero_iff_isUnit, MvPolynomial.eval₂_comp_left]
  change MvPolynomial.aeval (residue V.ring ∘ _) P ≠ 0
  rw [hv]
  exact fun h0 => hP (algebraicIndependent_iff.1 hind2 P h0)

end GlobalTheory.FieldPair
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueCoordinatesOfLocalModelBelowPlaceStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_residue_coordinates_of_localModel_below_place : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (N r : ℕ) (V : Place c) (hC : V.Contains Q) (u : Fin r → V.ring),
    (∃ x : Fin N → L, TrBasis c x) →
    (∀ q ∈ IsLocalRing.maximalIdeal Q,
      (⟨q, hC _ q.2⟩ : V.ring) ∈ IsLocalRing.maximalIdeal V.ring) →
    (∀ P : MvPolynomial (Fin r) Q, (∃ α, P.coeff α ∉ IsLocalRing.maximalIdeal Q) →
      IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P)) →
    (∀ f : V.ring, ∃ P R : MvPolynomial (Fin r) Q,
      IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R) ∧
      f * MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R =
        MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P) →
    ∃ (j : ℕ) (s : Fin j → Q), r + j + 1 = N ∧
      ∀ P : MvPolynomial (Fin (r + j)) ℂ, P ≠ 0 →
        IsUnit (MvPolynomial.eval₂ V.const
          (Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring)) P) := by
  first | exact @GlobalTheory.FieldPair.exists_residue_coords_of_locModel | exact GlobalTheory.FieldPair.exists_residue_coords_of_locModel | (intros; apply GlobalTheory.FieldPair.exists_residue_coords_of_locModel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialValuationOfParameters

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.MonoVal

theorem isQuasiRegularSeq_of_locModel : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (r : ℕ) (z : Fin (r + 1) → Q),
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) → ringKrullDim Q = r + 1 →
    IsNoetherianRing Q ∧ IsQuasiRegularSeq Q z := by
  intro L _ c Q hQ
  letI := hQ.isLocalRing
  intro r z hm hd
  letI := (c.codRestrict Q hQ.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
  haveI : IsNoetherianRing Q := Algebra.EssFiniteType.isNoetherianRing ℂ Q
  refine ⟨inferInstance, isQuasiRegularSeq_of_isRegular ?_⟩
  refine isRegular_of_ofList_eq_maximalIdeal ?_ ?_
  · rw [ofList_ofFn_eq_span_range, hm]
  · rw [List.length_ofFn, hd]
    norm_cast

def powCoeffMatrix {A : Type} [CommRing A] (n : ℕ) (t : A) (e : Fin n → ℕ) (w : Fin n → A) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  fun i j => Fin.cases (if j = 0 then 1 else 0)
    (fun i' => Fin.cases (w i' * ((e i' : A) * t ^ (e i' - 1)))
      (fun j' => if j' = i' then t ^ e i' else 0) j) i

theorem powCoeffMatrix_det {A : Type} [CommRing A] (n : ℕ) (t : A) (e : Fin n → ℕ)
    (w : Fin n → A) : (powCoeffMatrix n t e w).det = t ^ (∑ i, e i) := by
  rw [Matrix.det_of_lowerTriangular]
  · rw [Fin.prod_univ_succ]
    simp [powCoeffMatrix, Finset.prod_pow_eq_pow_sum]
  · intro i j hij
    change i < j at hij
    induction i using Fin.cases with
    | zero =>
      have : j ≠ 0 := (Fin.pos_iff_ne_zero.mp (lt_of_le_of_lt (Fin.zero_le _) hij))
      simp [powCoeffMatrix, this]
    | succ i' =>
      induction j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j' =>
        have : j' ≠ i' := by
          intro h; subst h; exact lt_irrefl _ hij
        simp [powCoeffMatrix, this]

theorem dForm_cons_pow_mul : ∀ {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) (n : ℕ) (t : A)
    (e : Fin n → ℕ) (w : Fin n → A),
    dForm α (Fin.cons t (fun i => t ^ e i * w i) : Fin (n + 1) → A) =
      t ^ (∑ i, e i) • dForm α (Fin.cons t w : Fin (n + 1) → A) := by
  intro k A _ _ α n t e w
  rw [← powCoeffMatrix_det n t e w]
  apply dForm_eq_det_smul
  intro i
  rw [Fin.sum_univ_succ]
  induction i using Fin.cases with
  | zero => simp [powCoeffMatrix]
  | succ i' =>
    simp only [powCoeffMatrix, Fin.cons_succ, Fin.cases_zero, Fin.cases_succ, Fin.cons_zero,
      ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    letI := α.toAlgebra
    change KaehlerDifferential.D k A (t ^ e i' * w i') = _
    rw [Derivation.leibniz, Derivation.leibniz_pow, add_comm]
    congr 1
    rw [mul_smul, mul_smul, ← Nat.cast_smul_eq_nsmul A]

theorem monomial_place : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q), letI := hQ.isLocalRing;
  ∀ (r N : ℕ) (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ),
  IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) → ringKrullDim Q = r + 1 → wt 0 = 1 → (∀ i, 1 ≤ wt i) →
  (∃ x : Fin N → L, TrBasis c x) →
  ∃ V : Place c, V.Contains Q ∧ (∀ q : Q, IsUnit q → V.ord q = 0) ∧ (∀ i, V.ord (z i) = wt i) ∧
    (∀ (d : ℕ) (q : Q), (q : L) ≠ 0 → q ∈ IsLocalRing.maximalIdeal Q ^ d → (d : ℤ) ≤ V.ord q) ∧
    ∀ y : Fin N → Q, IsFreeGen Q (dForm (c.codRestrict Q hQ.const_mem) y) →
      V.formOrd (dForm c (fun i => (y i : L))) + 1 ≤ ∑ i, (wt i : ℤ) := by
  intro L _ c Q hQ
  letI := hQ.isLocalRing
  intro r N z wt hm hdim hw0 hw1 hx
  obtain ⟨hN, hqr⟩ := isQuasiRegularSeq_of_locModel c Q hQ r z hm hdim
  obtain ⟨V, hC, u, hu, hirr, hmV, hunit, hloc⟩ := GlobalTheory.T.exists_weightedMonomialPlace_of_isLocModel c Q hQ r z wt hN hm.symm hqr hw0 hw1
  have ht0 : (z 0 : L) ≠ 0 := fun h => hirr.ne_zero (Subtype.ext h)
  have hordt : V.ord (z 0 : L) = 1 := by
    have h := V.ord_irreducible hirr
    exact h
  have h1m : (1 : Q) ∉ IsLocalRing.maximalIdeal Q := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal Q).ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have huu : ∀ i, IsUnit (u i) := fun i => by
    have h := hunit (MvPolynomial.X i) ⟨Finsupp.single i 1, by rw [MvPolynomial.coeff_X, if_pos rfl]; exact h1m⟩
    rw [MvPolynomial.eval₂_X] at h
    exact h
  have hu0 : ∀ i, (u i : L) ≠ 0 := fun i h => (huu i).ne_zero (Subtype.ext h)
  have hordu : ∀ i, V.ord (u i : L) = 0 := fun i => V.ord_eq_zero (huu i)
  have hordz : ∀ i, V.ord (z i : L) = wt i := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [hordt, hw0]; rfl
    · rw [← hu i, V.ord_mul (hu0 i) (pow_ne_zero _ ht0), V.ord_pow, hordu i, hordt]
      simp

  obtain ⟨φ, hφ⟩ : ∃ φ : Q →+* V.ring, φ = Q.subtype.codRestrict V.ring fun q => hC _ q.2 :=
    ⟨_, rfl⟩
  have hφL : ∀ q : Q, ((φ q : V.ring) : L) = q := fun q => by rw [hφ]; rfl
  refine ⟨V, hC, fun q hq => ?_, hordz, ?_, ?_⟩
  · have h := V.ord_eq_zero (hq.map φ)
    rwa [hφL] at h
  · intro d q hq0 hq
    have hmap : Ideal.map φ (IsLocalRing.maximalIdeal Q) ≤ Ideal.span {(⟨z 0, hC _ (z 0).2⟩ : V.ring)} := by
      rw [← hirr.maximalIdeal_eq, Ideal.map_le_iff_le_comap]
      intro q hq
      have h := hmV q hq
      rw [Ideal.mem_comap]
      convert h using 1
      exact Subtype.ext (hφL q)
    have h2 : φ q ∈ Ideal.span {(⟨z 0, hC _ (z 0).2⟩ : V.ring) ^ d} := by
      rw [← Ideal.span_singleton_pow]
      refine (Ideal.pow_right_mono hmap d) ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem φ hq
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h2
    have haL : (q : L) = (a : L) * (z 0 : L) ^ d := by
      rw [← hφL q, ← ha]
      rfl
    have ha0 : (a : L) ≠ 0 := fun h => hq0 (by rw [haL, h, zero_mul])
    rw [haL, V.ord_mul ha0 (pow_ne_zero _ ht0), V.ord_pow, hordt, mul_one]
    have := (V.ord_nonneg_iff ha0).2 a.2
    omega

  · intro y hy
    obtain ⟨xT, hxT⟩ := hx
    obtain ⟨j, s, hjN, hsu⟩ := GlobalTheory.T.exists_residue_coordinates_of_localModel_below_place c Q hQ N r V hC u ⟨xT, hxT⟩ hmV hunit hloc
    subst hjN
    obtain ⟨w, hw⟩ : ∃ w : Fin (r + j) → V.ring,
        w = Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring) := ⟨_, rfl⟩
    rw [← hw] at hsu
    have hG : IsFreeGen V.ring
        (dForm V.const (Fin.cons ⟨z 0, hC _ (z 0).2⟩ w : Fin (r + j + 1) → V.ring)) := by
      letI := V.const.toAlgebra
      letI := c.toAlgebra
      haveI : IsScalarTower ℂ V.ring L := IsScalarTower.of_algebraMap_eq' rfl
      haveI : Algebra.EssFiniteType ℂ V.ring := V.essFiniteType
      haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ V.ring
      obtain ⟨m, z', b, -, hb⟩ := exists_basis_kaehler_uniformiser ℂ hirr
      have h1 := trdeg_eq_of_basis_kaehler ℂ L b
      have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hxT
      rw [h1, Cardinal.mk_fin] at h2
      obtain rfl : r + j = m := by
        have : r + j + 1 = m + 1 := by exact_mod_cast h2
        omega
      exact isFreeGen_dForm_uniformiser_cons ℂ V.ring V.const (r + j) _ w V.essFiniteType hirr
        ⟨b⟩ hsu
    have e1 : dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L) =
        V.toRat (r + j + 1)
          (dForm V.const (Fin.cons ⟨z 0, hC _ (z 0).2⟩ w : Fin (r + j + 1) → V.ring)) := by
      have h := TopForm.formMap_dForm (D := r + j + 1) (α := V.const) (β := c) V.ring.subtype rfl
        (Fin.cons ⟨z 0, hC _ (z 0).2⟩ w : Fin (r + j + 1) → V.ring)
      refine Eq.trans ?_ h.symm
      congr 1
      funext i
      cases i using Fin.cases <;> rfl
    have hθ0 : dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L) ≠ 0 := by
      rw [e1]; exact V.toRat_ne_zero hG
    have hθ : V.formOrd
        (dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L)) = 0 := by
      rw [e1]; exact V.formOrd_toRat hG
    obtain ⟨a, ha⟩ := hy.2 (dForm (c.codRestrict Q hQ.const_mem)
      (Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) : Fin (r + j + 1) → Q))
    have e2 : dForm c (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) :
          Fin (r + j + 1) → Q) i : L)) = (a : L) • dForm c (fun i => (y i : L)) := by
      have h := congrArg (TopForm.formMap (r + j + 1) Q.subtype
        (α := c.codRestrict Q hQ.const_mem) (β := c) rfl) ha
      have f1 := TopForm.formMap_dForm (D := r + j + 1) (α := c.codRestrict Q hQ.const_mem) (β := c)
        Q.subtype rfl y
      have f2 := TopForm.formMap_dForm (D := r + j + 1) (α := c.codRestrict Q hQ.const_mem) (β := c)
        Q.subtype rfl (Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) : Fin (r + j + 1) → Q)
      rw [map_smulₛₗ] at h
      exact f2.symm.trans (h.symm.trans (congrArg (Q.subtype a • ·) f1))
    obtain ⟨e, he⟩ : ∃ e : Fin (r + j) → ℕ,
        e = Fin.append (fun i => wt i.succ) (fun _ : Fin j => 0) := ⟨_, rfl⟩
    have e3 : (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) :
          Fin (r + j + 1) → Q) i : L)) =
        (Fin.cons (z 0 : L) (fun i => (z 0 : L) ^ e i * (w i : L)) : Fin (r + j + 1) → L) := by
      funext i
      refine Fin.cases rfl (fun i => ?_) i
      simp only [Fin.cons_succ]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [he, hw, Fin.append_left]
        rw [← hu i, mul_comm]
      · simp only [he, hw, Fin.append_right, pow_zero, one_mul]
    have hsum : ∑ i, e i = ∑ i : Fin r, wt i.succ := by
      rw [he, Fin.sum_univ_add]
      simp
    have e4 : dForm c (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) :
          Fin (r + j + 1) → Q) i : L)) =
        (z 0 : L) ^ (∑ i : Fin r, wt i.succ) •
          dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L) := by
      rw [e3, dForm_cons_pow_mul, hsum]
    have hpow0 : ((z 0 : L) ^ (∑ i : Fin r, wt i.succ)) ≠ 0 := pow_ne_zero _ ht0
    have hne : dForm c (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) :
          Fin (r + j + 1) → Q) i : L)) ≠ 0 := by
      rw [e4]
      exact smul_ne_zero hpow0 hθ0
    have ha0 : (a : L) ≠ 0 := fun h => hne (by rw [e2, h, zero_smul])
    have hy0 : dForm c (fun i => (y i : L)) ≠ 0 := fun h => hne (by rw [e2, h, smul_zero])
    have o1 := V.formOrd_smul hxT hθ0 hpow0
    have o2 := V.formOrd_smul hxT hy0 ha0
    rw [← e4, hθ, V.ord_pow, hordt] at o1
    rw [← e2, o1] at o2
    have hnna := (V.ord_nonneg_iff ha0).2 (hC _ a.2)
    rw [Fin.sum_univ_succ, hw0]
    push_cast at o2 ⊢
    linarith

end GlobalTheory.MonoVal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialValuationOfParametersStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_weighted_monomial_valuation_of_parameters : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q), letI := hQ.isLocalRing;
  ∀ (r N : ℕ) (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ),
  IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) → ringKrullDim Q = r + 1 → wt 0 = 1 → (∀ i, 1 ≤ wt i) →
  (∃ x : Fin N → L, TrBasis c x) →
  ∃ V : Place c, V.Contains Q ∧ (∀ q : Q, IsUnit q → V.ord q = 0) ∧ (∀ i, V.ord (z i) = wt i) ∧
    (∀ (d : ℕ) (q : Q), (q : L) ≠ 0 → q ∈ IsLocalRing.maximalIdeal Q ^ d → (d : ℤ) ≤ V.ord q) ∧
    ∀ y : Fin N → Q, IsFreeGen Q (dForm (c.codRestrict Q hQ.const_mem) y) →
      V.formOrd (dForm c (fun i => (y i : L))) + 1 ≤ ∑ i, (wt i : ℤ) := by
  first | exact @GlobalTheory.MonoVal.monomial_place | exact GlobalTheory.MonoVal.monomial_place | (intros; apply GlobalTheory.MonoVal.monomial_place <;> assumption)
end
end
