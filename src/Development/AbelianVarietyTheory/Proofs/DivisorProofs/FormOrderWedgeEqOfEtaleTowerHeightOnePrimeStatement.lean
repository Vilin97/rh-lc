module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApi
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenWedgeFormOfFormallyEtaleMvPolynomial
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtalePolynomialPlaceToPlace

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.PolyPlaceEt

variable {k K : Type} [Field k] [Field K] {c : k →+* K}

def inclRing {Q : Subring K} {P : Place c} (h : P.Contains Q) : Q →+* P.ring :=
  Q.subtype.codRestrict P.ring fun q => h q q.2

theorem isUnit_of_ord_zero (P : Place c) (b : P.ring) (hb : (b : K) ≠ 0)
    (h : P.ord (b : K) = 0) : IsUnit b := by
  have h1 : (b : K)⁻¹ ∈ P.ring :=
    (P.ord_nonneg_iff (inv_ne_zero hb)).1 (by rw [P.ord_inv, h]; rfl)
  exact IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ hb))

theorem isLocalization_ring {Q : Subring K} {P : Place c} (h : P.IsPrimeOf Q) :
    letI := (inclRing h.1).toAlgebra
    IsLocalization ((IsUnit.submonoid P.ring).comap (inclRing h.1)) P.ring := by
  letI := (inclRing h.1).toAlgebra
  rw [isLocalization_iff]
  refine ⟨fun y => y.2, fun f => ?_, fun {a b} e => ⟨1, ?_⟩⟩
  · obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := h.2 f f.2
    exact ⟨⟨⟨a, ha⟩, ⟨⟨b, hb⟩, isUnit_of_ord_zero P ⟨b, h.1 b hb⟩ hb0 hbo⟩⟩, Subtype.ext e⟩
  · have : (a : K) = b := congrArg (fun z : P.ring => (z : K)) e
    rw [Subtype.ext this]

end PolyPlaceEt


open PolyPlaceEt in
theorem formallyEtale_polyPlace : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K)
    (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL) (P0 : Place cK)
    (j : K →+* L), IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T → P0.IsPrimeOf R →
    (∀ g : R, j (g : K) = (ι g : L)) → ∀ (hA : ∀ f ∈ P0.ring, j f ∈ P.ring)
    (hτ : ∀ i, (τ i : L) ∈ P.ring),
    (MvPolynomial.eval₂Hom (j.restrict P0.ring P.ring hA) (fun i => (⟨τ i, hτ i⟩ : P.ring))).FormallyEtale := by
  intro K L _ _ cK cL r R T ι ψ τ P P0 j hE hP hP0 hj hA hτ
  letI : Algebra R P0.ring := (inclRing hP0.1).toAlgebra
  letI : Algebra T P.ring := (inclRing hP.1).toAlgebra
  haveI h0 := isLocalization_ring hP0
  haveI h1 := isLocalization_ring hP
  letI : Algebra (MvPolynomial (Fin r) R) (MvPolynomial (Fin r) P0.ring) :=
    MvPolynomial.algebraMvPolynomial
  haveI := MvPolynomial.isLocalization (σ := Fin r) ((IsUnit.submonoid P0.ring).comap (inclRing hP0.1)) P0.ring
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) R) (MvPolynomial (Fin r) P0.ring) :=
    Algebra.FormallyEtale.of_isLocalization
      (((IsUnit.submonoid P0.ring).comap (inclRing hP0.1)).map MvPolynomial.C)
  have hc : ((algebraMap T P.ring).comp (MvPolynomial.eval₂Hom ι τ)).FormallyEtale :=
    RingHom.FormallyEtale.comp hE.etale (RingHom.formallyEtale_algebraMap.2
      (Algebra.FormallyEtale.of_isLocalization ((IsUnit.submonoid P.ring).comap (inclRing hP.1))))
  letI : Algebra (MvPolynomial (Fin r) R) P.ring :=
    ((algebraMap T P.ring).comp (MvPolynomial.eval₂Hom ι τ)).toAlgebra
  letI : Algebra (MvPolynomial (Fin r) P0.ring) P.ring :=
    (MvPolynomial.eval₂Hom (j.restrict P0.ring P.ring hA) (fun i => (⟨τ i, hτ i⟩ : P.ring))).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin r) R) (MvPolynomial (Fin r) P0.ring) P.ring := by
    apply IsScalarTower.of_algebraMap_eq'
    apply MvPolynomial.ringHom_ext
    · intro g
      change inclRing hP.1 (MvPolynomial.eval₂Hom ι τ (MvPolynomial.C g)) =
        MvPolynomial.eval₂Hom (j.restrict P0.ring P.ring hA) (fun i => (⟨τ i, hτ i⟩ : P.ring))
          (MvPolynomial.map (inclRing hP0.1) (MvPolynomial.C g))
      rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      apply Subtype.ext
      exact (hj g).symm
    · intro i
      change inclRing hP.1 (MvPolynomial.eval₂Hom ι τ (MvPolynomial.X i)) =
        MvPolynomial.eval₂Hom (j.restrict P0.ring P.ring hA) (fun i => (⟨τ i, hτ i⟩ : P.ring))
          (MvPolynomial.map (inclRing hP0.1) (MvPolynomial.X i))
      rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      rfl
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) R) P.ring := hc
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) P0.ring) P.ring :=
    Algebra.FormallyEtale.of_restrictScalars (R := MvPolynomial (Fin r) R)
  exact RingHom.formallyEtale_algebraMap.2 this

end GlobalTheory.FieldPair
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtalePolynomialPlaceToPlaceStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.formallyEtale_polynomialPlace_to_place : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K)
    (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL) (P0 : Place cK)
    (j : K →+* L), IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T → P0.IsPrimeOf R →
    (∀ g : R, j (g : K) = (ι g : L)) → ∀ (hA : ∀ f ∈ P0.ring, j f ∈ P.ring)
    (hτ : ∀ i, (τ i : L) ∈ P.ring),
    (MvPolynomial.eval₂Hom (j.restrict P0.ring P.ring hA) (fun i => (⟨τ i, hτ i⟩ : P.ring))).FormallyEtale := by
  first | exact @GlobalTheory.FieldPair.formallyEtale_polyPlace | exact GlobalTheory.FieldPair.formallyEtale_polyPlace | (intros; apply GlobalTheory.FieldPair.formallyEtale_polyPlace <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenWedgeFormOfFormallyEtaleMvPolynomialStatement

section

@[expose] public section

open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isFreeGen_wedgeForm_of_formallyEtale_mvPolynomial : ∀ {k A₀ A : Type} [CommRing k] [CommRing A₀] [CommRing A] (α : k →+* A₀) (β : k →+* A)
    (ρ : A₀ →+* A), ρ.comp α = β → ∀ {n r : ℕ} (z : Fin n → A₀) (b : Module.Basis (Fin n) A₀ (Omega α)),
    (∀ i, b i = dFun α (z i)) → ∀ (t : Fin r → A), (MvPolynomial.eval₂Hom ρ t).FormallyEtale →
    IsFreeGen A (dForm β (Fin.append t (fun i => ρ (z i)))) := by
  first | exact @GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial | exact GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial | (intros; apply GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerWedgeFormMapEqSmulOfBasis

section

@[expose] public section

open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.TopFormAppend

theorem dForm_append_eq_smul : ∀ {k K L : Type} [CommRing k] [CommRing K] [CommRing L] (cK : k →+* K) (cL : k →+* L)
    (j : K →+* L), j.comp cK = cL → ∀ {n r : ℕ} (x w : Fin n → K) (bK : Module.Basis (Fin n) K (Omega cK)),
    (∀ i, bK i = dFun cK (w i)) → ∀ f : K, dForm cK x = f • dForm cK w → ∀ t : Fin r → L,
    dForm cL (Fin.append t (fun i => j (x i))) = j f • dForm cL (Fin.append t (fun i => j (w i))) := by
  intro k K L _ _ _ cK cL j hc n r x w bK hbK f hf t
  let a : Matrix (Fin n) (Fin n) K := Matrix.of fun i l => bK.repr (dFun cK (x i)) l
  have ha : ∀ i, dFun cK (x i) = ∑ l, a i l • dFun cK (w l) := fun i => by
    conv_lhs => rw [← bK.sum_repr (dFun cK (x i))]
    exact Finset.sum_congr rfl fun l _ => by rw [hbK]; rfl
  have hdet : a.det = f :=
    (isFreeGen_dForm w bK hbK).1 ((dForm_eq_det_smul x w a ha).symm.trans hf)
  have hL : ∀ i, dFun cL (j (x i)) = ∑ l, j (a i l) • dFun cL (j (w l)) := fun i => by
    letI := cK.toAlgebra
    letI := cL.toAlgebra
    letI := j.toAlgebra
    haveI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' hc.symm
    have := congrArg (KaehlerDifferential.map k k K L) (ha i)

    rw [map_sum] at this
    simp only [map_smul, KaehlerDifferential.map_D] at this
    refine this.trans (Finset.sum_congr rfl fun l _ => ?_)
    rw [← algebraMap_smul L]
    rfl
  let M : Matrix (Fin (r + n)) (Fin (r + n)) L :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 (j.mapMatrix a))
  have hM : M.det = j f := by
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul,
      ← RingHom.map_det, hdet]
  rw [← hM]
  refine dForm_eq_det_smul _ _ M fun i => ?_
  rw [Fin.sum_univ_add]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [M, Matrix.one_apply, Fin.append_left]
  · simp [M, Fin.append_right, hL]

end GlobalTheory.TopFormAppend
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerWedgeFormMapEqSmulOfBasisStatement

section

@[expose] public section

open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.kaehlerWedgeForm_map_eq_smul_of_basis : ∀ {k K L : Type} [CommRing k] [CommRing K] [CommRing L] (cK : k →+* K) (cL : k →+* L)
    (j : K →+* L), j.comp cK = cL → ∀ {n r : ℕ} (x w : Fin n → K) (bK : Module.Basis (Fin n) K (Omega cK)),
    (∀ i, bK i = dFun cK (w i)) → ∀ f : K, dForm cK x = f • dForm cK w → ∀ t : Fin r → L,
    dForm cL (Fin.append t (fun i => j (x i))) = j f • dForm cL (Fin.append t (fun i => j (w i))) := by
  first | exact @GlobalTheory.TopFormAppend.dForm_append_eq_smul | exact GlobalTheory.TopFormAppend.dForm_append_eq_smul | (intros; apply GlobalTheory.TopFormAppend.dForm_append_eq_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrderWedgeEqOfEtaleTowerHeightOnePrime

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FieldPair

theorem formOrd_append_of_ord_eq : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (P : Place cL) (P0 : Place cK),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → P.IsPrimeOf T → P0.IsPrimeOf R →
  (∀ g : R, g ≠ 0 → P.ord (ι g : L) = P0.ord (g : K)) →
  (fun ω => @dite ℤ (∃ a, P.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) = (fun ω => @dite ℤ (∃ a, P0.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cK (fun i => (x i : K))) := by
  intro K L _ _ cK cL n r R T ι ψ τ x P P0 hE hx hP hP0 hord
  have hιinj : Function.Injective ι := fun a b h => by
    have := congrArg ψ h
    rwa [hE.retr, hE.retr] at this
  haveI : IsFractionRing R K := IsFractionRing.of_field R K fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hE.base.frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, eq_div_of_mul_eq hb0 e⟩
  have hginj : Function.Injective (T.subtype.comp ι) := Subtype.val_injective.comp hιinj
  let j : K →+* L := IsFractionRing.lift hginj
  have hj : ∀ g : R, j (g : K) = (ι g : L) := fun g => IsFractionRing.lift_algebraMap hginj g
  have hordK : ∀ f : K, f ≠ 0 → P.ord (j f) = P0.ord f := by
    intro f hf
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hE.base.frac f
    have ha0 : a ≠ 0 := by rw [← e]; exact mul_ne_zero hf hb0
    have ef : f = a * b⁻¹ := by rw [← e, mul_inv_cancel_right₀ hb0]
    have hjb : j b ≠ 0 := (map_ne_zero j).2 hb0
    have hja : j a ≠ 0 := (map_ne_zero j).2 ha0
    have hga : (⟨a, ha⟩ : R) ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
    have hgb : (⟨b, hb⟩ : R) ≠ 0 := fun h => hb0 (congrArg Subtype.val h)
    have h1 := hord _ hga
    have h2 := hord _ hgb
    rw [← hj] at h1 h2
    rw [ef, map_mul, map_inv₀, P.ord_mul hja (inv_ne_zero hjb), P.ord_inv,
      P0.ord_mul ha0 (inv_ne_zero hb0), P0.ord_inv]
    simp only at h1 h2
    rw [h1, h2]
  have hA : ∀ f ∈ P0.ring, j f ∈ P.ring := by
    intro f hf
    by_cases h0 : f = 0
    · rw [h0, map_zero]; exact P.ring.zero_mem
    · have hj0 : j f ≠ 0 := (map_ne_zero j).2 h0
      rw [← P.ord_nonneg_iff hj0, hordK f h0, P0.ord_nonneg_iff h0]
      exact hf
  have hτ : ∀ i, (τ i : L) ∈ P.ring := fun i => hP.1 _ (τ i).2
  let ρ : P0.ring →+* P.ring := j.restrict P0.ring P.ring hA
  let τ' : Fin r → P.ring := fun i => ⟨τ i, hτ i⟩
  have hc : ρ.comp P0.const = P.const := by
    ext a
    change j (cK a) = cL a
    have := hj ⟨cK a, hE.base.const_mem a⟩
    rw [hE.const a] at this
    exact this
  have hFE := GlobalTheory.T.formallyEtale_polynomialPlace_to_place cK cL r R T ι ψ τ P P0 j hE hP hP0 hj hA hτ

  letI := P0.const.toAlgebra
  letI := cK.toAlgebra
  haveI : IsScalarTower ℂ P0.ring K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType ℂ P0.ring := P0.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ P0.ring
  obtain ⟨t0, ht0⟩ := IsDiscreteValuationRing.exists_irreducible P0.ring
  obtain ⟨m, z, b, -, hb⟩ := exists_basis_kaehler_uniformiser ℂ ht0
  have h1 := trdeg_eq_of_basis_kaehler ℂ K b
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
  rw [h1, Cardinal.mk_fin] at h2
  obtain rfl : n = m + 1 := by exact_mod_cast h2
  have hω0 : IsFreeGen P0.ring (dForm P0.const z) := isFreeGen_dForm z b hb
  have hF : IsFreeGen P.ring (dForm P.const (Fin.append τ' (fun i => ρ (z i)))) :=
    GlobalTheory.T.isFreeGen_wedgeForm_of_formallyEtale_mvPolynomial P0.const P.const ρ hc z b hb τ' hFE
  haveI : Algebra.FormallyEtale P0.ring K := .of_isLocalization (nonZeroDivisors P0.ring)
  let bK : Module.Basis (Fin (m + 1)) K (Omega cK) :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ P0.ring K).basis b
  have hbK : ∀ i, bK i = dFun cK (z i : K) := by
    intro i
    simp only [bK, IsBaseChange.basis_apply, hb]
    exact KaehlerDifferential.map_D ℂ ℂ P0.ring K (z i)
  have hrat0 : P0.toRat (m + 1) (dForm P0.const z) = dForm cK (fun i => (z i : K)) :=
    formMap_dForm _ rfl z
  have hratP : P.toRat (r + (m + 1)) (dForm P.const (Fin.append τ' (fun i => ρ (z i)))) =
      dForm cL (Fin.append (fun i => (τ i : L)) (fun i => j (z i : K))) := by
    refine (formMap_dForm _ rfl _).trans (congrArg _ (funext fun k => ?_))
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp only [Fin.append_left]; rfl
    · simp only [Fin.append_right]; rfl
  obtain ⟨f, hf⟩ := (P0.isFreeGen_toRat hω0).2 (dForm cK (fun i => (x i : K)))
  simp only at hf
  have hxK := isFreeGen_dForm_of_trBasis cK hx
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hf
    exact one_ne_zero (hxK.1 (a₁ := 1) (a₂ := 0) (by simp [← hf]))
  have hK : P0.formOrd (dForm cK (fun i => (x i : K))) = P0.ord f := by
    rw [← hf]; exact P0.formOrd_smul_toRat hω0 hf0
  have key := GlobalTheory.T.kaehlerWedgeForm_map_eq_smul_of_basis cK cL j (RingHom.ext fun a => by
      change j (cK a) = cL a
      have := hj ⟨cK a, hE.base.const_mem a⟩
      rw [hE.const a] at this
      exact this) (fun i => (x i : K)) (fun i => (z i : K)) bK hbK f
    (by rw [← hf, hrat0]) (fun i => (τ i : L))
  have e1 : (fun i => j (x i : K)) = fun i => (ι (x i) : L) := funext fun i => hj (x i)
  rw [e1, ← hratP] at key
  change P.formOrd (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) =
    P0.formOrd (dForm cK (fun i => (x i : K)))
  rw [key, P.formOrd_smul_toRat hF ((map_ne_zero j).2 hf0), hordK f hf0, hK]

end GlobalTheory.FieldPair
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrderWedgeEqOfEtaleTowerHeightOnePrimeStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.formOrder_wedge_eq_of_etaleTower_heightOnePrime : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (P : Place cL) (P0 : Place cK),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → P.IsPrimeOf T → P0.IsPrimeOf R →
  (∀ g : R, g ≠ 0 → P.ord (ι g : L) = P0.ord (g : K)) →
  (fun ω => @dite ℤ (∃ a, P.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) = (fun ω => @dite ℤ (∃ a, P0.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cK (fun i => (x i : K))) := by
  first | exact @GlobalTheory.FieldPair.formOrd_append_of_ord_eq | exact GlobalTheory.FieldPair.formOrd_append_of_ord_eq | (intros; apply GlobalTheory.FieldPair.formOrd_append_of_ord_eq <;> assumption)
end
end
