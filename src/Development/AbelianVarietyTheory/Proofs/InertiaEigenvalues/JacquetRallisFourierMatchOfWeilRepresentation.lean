module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualMeasuresAndAbsKScale
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockInvariantsIffIsometryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisInvKRegularIffIsUnitStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisLinearOrbitalIntegralDescentStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisMatchOfDenseSeparableStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegralsInvariantLocallyConStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierPreservesTestFixesUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActionHermitianInvariantsTransitiveStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitalDescent
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyCompactModuleTopology

section

@[expose] public section

open Polynomial TensorProduct

noncomputable section

namespace GlobalTheory.JR.EtExist

variable (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def conjAlg [h : Unram F E] : E →ₐ[F] E :=
  { starRingEnd E with commutes' := fun x => h.star_fix x }

theorem conjAlg_apply [Unram F E] (y : E) : conjAlg F E y = star y := rfl

variable (K : Type) [CommRing K] [Algebra F K]

def conjT [Unram F E] : E ⊗[F] K →ₐ[F] E ⊗[F] K := Algebra.TensorProduct.map (conjAlg F E) (AlgHom.id F K)

theorem conjT_conjT [Unram F E] (z : E ⊗[F] K) : conjT F E K (conjT F E K z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [conjT, conjAlg_apply]
  | add a b ha hb => simp [ha, hb]

@[reducible] def starT [Unram F E] : StarRing (E ⊗[F] K) where
  star := conjT F E K
  star_involutive := conjT_conjT F E K
  star_mul a b := by
    change conjT F E K (a * b) = conjT F E K b * conjT F E K a
    rw [map_mul, mul_comm]
  star_add a b := map_add (conjT F E K) a b

theorem locallyCompact_moduleTopology [LocallyCompactSpace F] [Module.Finite F K] :
    @LocallyCompactSpace K (moduleTopology F K) := by
  letI : TopologicalSpace K := moduleTopology F K
  haveI : IsModuleTopology F K := ⟨rfl⟩
  let b := (Module.finBasis F K).equivFun
  have h1 : Continuous b := IsModuleTopology.continuous_of_linearMap b.toLinearMap
  haveI : ContinuousAdd K := IsModuleTopology.toContinuousAdd F K
  have h2 : Continuous b.symm := IsModuleTopology.continuous_of_linearMap b.symm.toLinearMap
  let e : K ≃ₜ (Fin (Module.finrank F K) → F) := { b.toEquiv with continuous_toFun := h1, continuous_invFun := h2 }
  exact e.isClosedEmbedding.locallyCompactSpace

def ofAlgebra [h : Unram F E] [Module.Finite F K] [IsReduced K] : Et F E :=
  letI : TopologicalSpace K := moduleTopology F K
  haveI : IsModuleTopology F K := ⟨rfl⟩
  letI : TopologicalSpace (E ⊗[F] K) := moduleTopology F (E ⊗[F] K)
  letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  { K := K
    L := E ⊗[F] K
    trK := IsModuleTopology.isTopologicalRing F K
    lcK := haveI := h.lcF; locallyCompact_moduleTopology F K
    mK := borel K
    bK := @BorelSpace.mk _ _ (borel K) rfl
    stL := starT F E K
    mtL := ⟨rfl⟩
    mL := borel (E ⊗[F] K)
    bL := @BorelSpace.mk _ _ (borel (E ⊗[F] K)) rfl
    push := inferInstance
    star_K := fun x => by
      change conjT F E K (1 ⊗ₜ x) = 1 ⊗ₜ x
      simp [conjT]
    star_E := fun y => by
      change conjT F E K (y ⊗ₜ 1) = star y ⊗ₜ 1
      simp [conjT, conjAlg_apply] }

theorem exists_isGen [Unram F E] (r : ℕ) (p : Fin r → F)
    (hs : (X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) : F[X]).Separable) : ∃ (A : Et F E) (τ : A.K), A.IsGen τ p := by
  set P : F[X] := X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) with hP
  have hlt : (∑ i, C (p i) * X ^ (i : ℕ) : F[X]).degree < r := degree_sum_fin_lt p
  have hm : P.Monic := monic_X_pow_add hlt
  have hd : P.natDegree = r := by
    have : P.degree = r := by
      rw [hP, degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
    exact natDegree_eq_of_degree_eq_some this
  let pb := AdjoinRoot.powerBasis' hm
  haveI : Module.Finite F (AdjoinRoot P) := pb.finite
  haveI : IsReduced (AdjoinRoot P) :=
    (Ideal.isRadical_iff_quotient_reduced _).1
      ((isRadical_iff_span_singleton).1 hs.squarefree.isRadical)
  refine ⟨ofAlgebra F E (AdjoinRoot P), AdjoinRoot.root P, ?_, ?_, ?_⟩
  · change LinearIndependent F (fun i : Fin r => AdjoinRoot.root P ^ (i : ℕ))
    have := pb.basis.linearIndependent.comp (Fin.cast (show r = pb.dim from hd.symm)) (Fin.cast_injective _)
    have e : (fun i : Fin r => AdjoinRoot.root P ^ (i : ℕ)) = pb.basis ∘ Fin.cast (show r = pb.dim from hd.symm) := by
      funext i
      rw [Function.comp_apply, pb.basis_eq_pow]
      rfl
    rw [e]; exact this
  · change Module.finrank F (AdjoinRoot P) = r
    rw [pb.finrank]; exact hd
  · change AdjoinRoot.root P ^ r + ∑ i, p i • AdjoinRoot.root P ^ (i : ℕ) = 0
    have := AdjoinRoot.aeval_eq (f := P) P
    rw [AdjoinRoot.mk_self] at this
    have h2 : aeval (AdjoinRoot.root P) (X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) : F[X]) = 0 := this

    simp only [map_add (f := _), map_pow, map_sum, map_mul, aeval_X, aeval_C] at h2
    simpa only [Algebra.smul_def] using h2

end GlobalTheory.JR.EtExist
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleHermitianPairIsGenCompanion

section

@[expose] public section

open Polynomial Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR

theorem charpoly_companion {k : Type} [Field k] {r : ℕ} (p : Fin r → k) :
    (companion p).charpoly = X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) := by
  set P : k[X] := X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) with hP
  have hlt : (∑ i, C (p i) * X ^ (i : ℕ) : k[X]).degree < r := degree_sum_fin_lt p
  have hm : P.Monic := monic_X_pow_add hlt
  have hd : P.natDegree = r := by
    have : P.degree = r := by
      rw [hP, degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
    exact natDegree_eq_of_degree_eq_some this
  let pb := AdjoinRoot.powerBasis' hm
  have hdim : pb.dim = r := hd
  let b : Module.Basis (Fin r) k (AdjoinRoot P) := pb.basis.reindex (finCongr hdim)
  have hb : ∀ i : Fin r, b i = AdjoinRoot.root P ^ (i : ℕ) := by
    intro i
    simp only [b, Module.Basis.reindex_apply, pb.basis_eq_pow]
    rfl
  have hroot : AdjoinRoot.root P ^ r = ∑ i, (- p i) • b i := by
    have h0 := AdjoinRoot.aeval_eq (f := P) P
    rw [AdjoinRoot.mk_self] at h0
    have h2 : aeval (AdjoinRoot.root P) (X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) : k[X]) = 0 := h0

    simp only [map_add (f := _), map_pow, map_sum, map_mul, aeval_X, aeval_C] at h2
    rw [eq_neg_of_add_eq_zero_left h2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb, neg_smul, Algebra.smul_def]
  have hmat : companion p = Algebra.leftMulMatrix b (AdjoinRoot.root P) := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, hb, ← pow_succ']
    simp only [companion, Matrix.of_apply]
    by_cases hj : (j : ℕ) + 1 = r
    · rw [if_pos hj, hj, hroot, ← b.equivFun_symm_apply, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    · rw [if_neg hj]
      have hlt' : (j : ℕ) + 1 < r := lt_of_le_of_ne j.2 hj
      have : AdjoinRoot.root P ^ ((j : ℕ) + 1) = b ⟨(j : ℕ) + 1, hlt'⟩ := by rw [hb]
      rw [this, b.repr_self, Finsupp.single_apply]
      by_cases hi : (i : ℕ) = (j : ℕ) + 1
      · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
      · rw [if_neg hi, if_neg (fun h => hi (congrArg Fin.val h).symm)]
  have hP0 : P ≠ 0 := hm.ne_zero
  haveI : Module.Finite k (AdjoinRoot P) := pb.finite
  rw [hmat, Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, ← LinearMap.charpoly_toMatrix _ pb.basis,
    ← Algebra.leftMulMatrix_apply]
  have hg : pb.gen = AdjoinRoot.root P := rfl
  rw [← hg, charpoly_leftMulMatrix, hg, AdjoinRoot.minpoly_root hP0, hm.leadingCoeff, inv_one, C_1, mul_one]

theorem exists_et_isGen_companion : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (p : Fin r → F),
    (companion p).charpoly.Separable → ∃ (A : Et F E) (τ : A.K), A.IsGen τ p := by
  intro F E _ _ _ _ _ r p hs
  rw [charpoly_companion] at hs
  exact EtExist.exists_isGen F E r p hs

end GlobalTheory.JR
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleHermitianPairIsGenCompanionStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_etaleHermitianPair_isGen_companion : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (p : Fin r → F), (companion p).charpoly.Separable → ∃ (A : Et F E) (τ : A.K), A.IsGen τ p := by
  first | exact @GlobalTheory.JR.exists_et_isGen_companion | exact GlobalTheory.JR.exists_et_isGen_companion | (intros; apply GlobalTheory.JR.exists_et_isGen_companion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualMeasuresAndAbsKScaleStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_selfDual_measures_and_absK_scale : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → Nonempty (A.Meas ψ) ∧ ∀ (m : A.Meas ψ) (x : A.Kˣ), m.μL x = ENNReal.ofReal (A.absK x) • m.μL 1 := by
  first | exact @GlobalTheory.JR.exists_meas_and_scale | exact GlobalTheory.JR.exists_meas_and_scale | (intros; apply GlobalTheory.JR.exists_meas_and_scale <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitalDescentStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_test_orbU_eq_orbL : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (r : ℕ) (M : Meas r F E) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → ∀ (x : A.Kˣ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ Ax : selfAdjoint (Matrix (Fin r) (Fin r) E), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ f : Hn r F E → ℂ, IsTest f → ∃ φ : A.L → ℂ, IsTest φ ∧ ∀ y : A.L, IsUnit y → orbU M f (Ax, j y, lam) = A.orbL m.ν φ y ∧ orbU M (fourU M ψ f) (Ax, j y, lam) = A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) φ) y := by
  first | exact @GlobalTheory.JR.unitary_orbital_descent | exact GlobalTheory.JR.unitary_orbital_descent | (intros; apply GlobalTheory.JR.unitary_orbital_descent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchOfWeilRepresentation

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem fourierMatchAt_of_weil (hW : WeilEt) (hR : RankOne) (hG : GammaOne) {r : ℕ} {F E : Type}
    [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (M : Meas r F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ)
    (hf' : IsTest f') (hf : IsTest f) (hm : Match M f' f) (a : Inv r F) (ha : Delta a ≠ 0)
    (hsep : (companion a.1).charpoly.Separable) :
    MatchAt M (fourG M ψ f') (fourU M ψ f) a := by
  obtain ⟨A, τ, hτ⟩ := GlobalTheory.T.exists_etaleHermitianPair_isGen_companion F E r a.1 hsep
  obtain ⟨hbij, hmom⟩ := GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit F E A r τ a.1 a.2.2 hτ
  obtain ⟨a₀, ha₀⟩ := hbij.2 a.2.1
  have ha₀' : (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * a₀)) = a.2.1 := ha₀
  have hinv : A.invK τ a.1 a.2.2 a₀ = a := by
    simp only [Et.invK, ha₀']
  have hu₀ : IsUnit a₀ := (hmom a₀).2.mp (by rw [hinv]; exact ha)
  obtain ⟨⟨m⟩, -⟩ := GlobalTheory.T.exists_selfDual_measures_and_absK_scale F E A ψ hψ
  obtain ⟨-, -, -, -, -, -, ⟨S, -, hS⟩, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  obtain ⟨φ', κ, hφ', hlin⟩ := GlobalTheory.T.jacquetRallis_linear_orbitalIntegral_descent F E A ψ hψ m r M τ a.1 a.2.2 hτ f' hf'
  obtain ⟨-, -, huniq, -⟩ := GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E r
  obtain ⟨-, horbU, -, -⟩ := GlobalTheory.T.jacquetRallisOrbitalIntegrals_invariant_locallyConstant F E r M
  obtain ⟨hL11a, hL11b⟩ := GlobalTheory.T.hermitianBlock_invariants_iff_isometry F E A r τ a.1 a.2.2 hτ
  have key : ∀ x : A.Kˣ, ∃ φx : A.L → ℂ, IsTest φx ∧
      ((∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j) →
        ∃ (j : A.L ≃ₗ[E] (Fin r → E)) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), A.IsIsom (x : A.K) j ∧
          (∀ y, HasInv ((Ax, j y, a.2.2) : Hn r F E) (A.invK τ a.1 a.2.2 ((x : A.K) * A.NL y))) ∧
          ∀ y : A.L, IsUnit y → orbU M f (Ax, j y, a.2.2) = A.orbL m.ν φx y ∧
            orbU M (fourU M ψ f) (Ax, j y, a.2.2) = A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) φx) y) ∧
      ((¬ ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j) → φx = 0) := by
    intro x
    by_cases hx : ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j
    · obtain ⟨j, hj⟩ := hx
      obtain ⟨Ax, hAx, hinvAx⟩ := hL11b (x : A.K) j hj
      obtain ⟨φx, hφx, hrel⟩ := GlobalTheory.T.exists_test_orbU_eq_orbL F E A ψ hψ m r M τ a.1 a.2.2 hτ x j hj Ax hAx f hf
      exact ⟨φx, hφx, fun _ => ⟨j, Ax, hj, hinvAx, hrel⟩, fun h => absurd ⟨j, hj⟩ h⟩
    · exact ⟨0, ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩, fun h => absurd h hx, fun _ => rfl⟩
  choose φ hφt hφi hφ0 using key
  choose γ Wr hWr using fun x : A.Kˣ => hW F E A ψ hψ x (m.μL x) (m.sdL x)
  have hunit : ∀ (x : A.Kˣ) (y : A.L), IsUnit y → IsUnit ((x : A.K) * A.NL y) := fun x y hy =>
    x.isUnit.mul (hy.map (Algebra.norm A.K))
  have hyp : ∀ x ∈ S, ∀ y : A.L, IsUnit y → κ * A.orbK m.μK φ' (x * A.NL y) = A.orbL m.ν (φ x) y := by
    intro x _ y hy
    have hb := hunit x y hy
    rw [← (hlin _ hb).1]
    by_cases hx : ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j
    · obtain ⟨j, Ax, -, hinvAx, hrel⟩ := hφi x hx
      rw [← (hrel y hy).1]
      exact (hm _ ((hmom _).2.mpr hb)).1 _ (hinvAx y)
    · rw [hφ0 x hx]
      have h0 : orbG M f' (sec (A.invK τ a.1 a.2.2 ((x : A.K) * A.NL y))) = 0 := by
        apply (hm _ ((hmom _).2.mpr hb)).2
        rintro ⟨X, hX⟩
        obtain ⟨j, hj, -⟩ := hL11a _ X hb hX (x : A.K) y hy rfl
        exact hx ⟨j, hj⟩
      rw [h0]
      simp [Et.orbL]
  have hRk := hR F E A ψ hψ m S hS γ Wr (fun x _ => hWr x) φ' φ κ hφ' (fun x _ => hφt x) hyp
  have hG1 : ∀ (x : A.Kˣ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom (x : A.K) j → γ x = 1 :=
    fun x j hj => hG F E A ψ hψ x (m.μL x) (m.sdL x) A.etaK (γ x) (Wr x) (hWr x) r j hj
  obtain ⟨x, ⟨hxS, y, hy, hxy⟩, -⟩ := hS hu₀.unit
  have hxy' : a₀ = x * A.NL y := by simpa using hxy
  have hb := hunit x y hy
  have hlhs : orbG M (fourG M ψ f') (sec a) =
      γ x * A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) (φ x)) y := by
    calc orbG M (fourG M ψ f') (sec a)
        = orbG M (fourG M ψ f') (sec (A.invK τ a.1 a.2.2 ((x : A.K) * A.NL y))) := by rw [← hxy', hinv]
      _ = κ * A.orbK m.μK (A.fourK m.μK ψ φ') ((x : A.K) * A.NL y) := (hlin _ hb).2
      _ = _ := hRk x hxS y hy
  constructor
  · intro X hX
    have hX' : HasInv X (A.invK τ a.1 a.2.2 a₀) := by rw [hinv]; exact hX
    obtain ⟨j₁, hj₁, -⟩ := hL11a a₀ X hu₀ hX' (x : A.K) y hy hxy'
    obtain ⟨j, Ax, hj, hinvAx, hrel⟩ := hφi x ⟨j₁, hj₁⟩
    have hXa : HasInv ((Ax, j y, a.2.2) : Hn r F E) a := by
      have := hinvAx y
      rw [← hxy', hinv] at this
      exact this
    obtain ⟨g, hg, -⟩ := huniq _ X a ha hXa hX
    rw [hlhs, hG1 x j hj, one_mul, ← (hrel y hy).2, ← hg, horbU]
  · intro hno
    have hx : ¬ ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j := by
      intro hx
      obtain ⟨j, Ax, -, hinvAx, -⟩ := hφi x hx
      have := hinvAx y
      rw [← hxy', hinv] at this
      exact hno ⟨_, this⟩
    rw [hlhs, hφ0 x hx]
    simp [fourB, Et.orbL]

theorem fourierMatch_of_weil : WeilEt → RankOne → GammaOne → ∀ r, FourierMatch r := by
  intro hW hR hG r F E _ _ _ _ _ M ψ hψ f' f hf' hf hm
  obtain ⟨h4G, h4U, -⟩ := GlobalTheory.T.partialFourier_preserves_test_fixes_unit F E r M ψ hψ
  exact (GlobalTheory.T.jacquetRallis_match_of_dense_separable F E r M _ _ (h4G f' hf') (h4U f hf)).1
    (fun a ha hsep => fourierMatchAt_of_weil hW hR hG M ψ hψ f' f hf' hf hm a ha hsep)

end GlobalTheory.JR
end
end
