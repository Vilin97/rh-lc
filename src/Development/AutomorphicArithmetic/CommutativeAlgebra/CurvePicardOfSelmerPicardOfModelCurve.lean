module

public import Development.EtaleCohomology.EtaleSheaves.LeafPicCut
public import Development.EtaleCohomology.EtaleSheaves.LeafCurveVCut
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Prime
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
import Mathlib.RingTheory.Henselian
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
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Noetherian.Basic
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiniteSpanKummerSelmerRepresentatives
public import Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteKummerSelmerOnPrimeStratum
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteKummerSelmerOfFiniteExtension
public import Development.AutomorphicArithmetic.CommutativeAlgebra.FinitePicTorsionOfFiniteKummerSelmer
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IsFunctionFieldAndChartsOfIsCurveOfIsUnit
public import GroundTheory.FunctionField.PlaceDefs
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveFunctionField
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ZariskiNoetherianInduction

section

@[expose] public section

theorem UpperTheory.Reformulated.B.ZariskiNoetherianInduction.noetherian_induction_zariski :
    ∀ (k : Type) [inst : Field k] (n : ℕ) (Q : Set (Fin n → k) → Prop),
    Q ∅ →
      (∀ (s t : Set (Fin n → k)), s ⊆ t → Q t → Q s) →
        (∀ (s t : Set (Fin n → k)), Q s → Q t → Q (s ∪ t)) →
          (∀ (I : Ideal (MvPolynomial (Fin n) k)),
              I.IsPrime →
                ∃ g ∉ I,
                  Q
                    {c : Fin n → k |
                      (∀ p ∈ I, (MvPolynomial.eval c : MvPolynomial (Fin n) k → k) p = (0 : k)) ∧
                        (MvPolynomial.eval c : MvPolynomial (Fin n) k → k) g ≠ (0 : k)}) →
            Q Set.univ := by
  intro k inst n Q h0 hmono hunion hprime
  have key : ∀ I : Ideal (MvPolynomial (Fin n) k),
      Q {c : Fin n → k | ∀ p ∈ I, MvPolynomial.eval c p = 0} := by
    intro I
    induction I using IsNoetherian.induction with
    | _ I ih =>
      have step : ∀ g : MvPolynomial (Fin n) k, g ∉ I →
          Q {c : Fin n → k | (∀ p ∈ I, MvPolynomial.eval c p = 0) ∧
            MvPolynomial.eval c g = 0} := by
        intro g hg
        have hlt : I < I ⊔ Ideal.span {g} := by
          refine lt_of_le_of_ne le_sup_left ?_
          intro h
          apply hg
          rw [h]
          exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)
        refine hmono _ _ ?_ (ih _ hlt)
        rintro c ⟨hc, hcg⟩
        have hle : I ⊔ Ideal.span {g} ≤ RingHom.ker (MvPolynomial.eval c) := by
          refine sup_le (fun p hp => (RingHom.mem_ker).2 (hc p hp)) ?_
          rw [Ideal.span_singleton_le_iff_mem]
          exact (RingHom.mem_ker).2 hcg
        exact fun p hp => (RingHom.mem_ker).1 (hle hp)
      by_cases hP : Ideal.IsPrime I
      · obtain ⟨g, hg, hQ⟩ := hprime I hP
        refine hmono _ _ ?_ (hunion _ _ hQ (step g hg))
        intro c hc
        by_cases hcg : MvPolynomial.eval c g = 0
        · exact Or.inr ⟨hc, hcg⟩
        · exact Or.inl ⟨hc, hcg⟩
      · rcases Ideal.not_isPrime_iff.1 hP with htop | ⟨x, hx, y, hy, hxy⟩
        · refine hmono _ _ ?_ h0
          intro c hc
          have h1 := hc 1 (htop ▸ Submodule.mem_top)
          simp at h1
        · refine hmono _ _ ?_ (hunion _ _ (step x hx) (step y hy))
          intro c hc
          have h1 := hc _ hxy
          rw [map_mul] at h1
          rcases mul_eq_zero.1 h1 with h | h
          · exact Or.inl ⟨hc, h⟩
          · exact Or.inr ⟨hc, h⟩
  refine hmono _ _ ?_ (key ⊥)
  intro c _ p hp
  rw [(Ideal.mem_bot).1 hp, map_zero]
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NoethSp

section

@[expose] public section

open TopologicalSpace PrimeSpectrum

theorem UpperTheory.Et.noethSp :
    ∀ (k : Type) [Field k] (n : ℕ) (P : Set (Fin n → k) → Prop), P ∅ → (∀ s t, s ⊆ t → P t → P s) → (∀ s t, P s → P t → P (s ∪ t)) → (∀ I : Ideal (MvPolynomial (Fin n) k), I.IsPrime → ∃ g, g ∉ I ∧ P ({c | ∀ p ∈ I, MvPolynomial.eval c p = 0} ∩ {c | MvPolynomial.eval c g ≠ 0})) → P Set.univ :=
  _root_.UpperTheory.Reformulated.B.ZariskiNoetherianInduction.noetherian_induction_zariski
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteKummerSelmerOfCharts

section

@[expose] public section

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

theorem UpperTheory.finite_kummerSelmer_of_charts :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [IsFunctionField k K] (q : ℕ) [NeZero q], Charts k K q → FinCls q (SelAll k K q) := by
  intro k K _ _ _ _ _ q _ hC
  obtain ⟨n, v, hv⟩ := UpperTheory.exists_finite_span_kummerSelmer_representatives k K q
  let P : Set (Fin n → k) → Prop := fun s =>
    FinCls q {f | f ∈ SelAll k K q ∧ ∃ c, (f : K) = ∑ i, c i • v i ∧ c ∈ s}
  have hall : P Set.univ := by
    apply UpperTheory.Et.noethSp k n P
    · refine ⟨∅, ?_⟩
      rintro f ⟨_, c, _, hc⟩
      exact absurd hc (by simp)
    · intro s t hst ⟨T, hT⟩
      refine ⟨T, ?_⟩
      rintro f ⟨hf, c, hfc, hc⟩
      exact hT f ⟨hf, c, hfc, hst hc⟩
    · intro s t ⟨T₁, h₁⟩ ⟨T₂, h₂⟩
      classical
      refine ⟨T₁ ∪ T₂, ?_⟩
      rintro f ⟨hf, c, hfc, hc | hc⟩
      · obtain ⟨x, hx, u, hu⟩ := h₁ f ⟨hf, c, hfc, hc⟩
        exact ⟨x, Finset.mem_union_left _ hx, u, hu⟩
      · obtain ⟨x, hx, u, hu⟩ := h₂ f ⟨hf, c, hfc, hc⟩
        exact ⟨x, Finset.mem_union_right _ hx, u, hu⟩
    · intro I hI
      obtain ⟨g, hg, T, hT⟩ := UpperTheory.finite_kummerSelmer_on_prime_stratum k K q hC n v I hI
      refine ⟨g, hg, T, ?_⟩
      rintro f ⟨hf, c, hfc, hc₁, hc₂⟩
      exact hT f ⟨hf, c, hfc, hc₁, hc₂⟩
  obtain ⟨T, hT⟩ := hall
  refine ⟨T, ?_⟩
  intro f hf
  obtain ⟨g, hg, ⟨c, hgc⟩, u, hfu⟩ := hv f hf
  obtain ⟨t, ht, w, hw⟩ := hT g ⟨hg, c, hgc, Set.mem_univ c⟩
  refine ⟨t, ht, w * u, ?_⟩
  rw [hfu, hw, mul_pow, mul_assoc]
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.IsFunctionFieldFractionRingOfDedekindFiniteType

section

@[expose] public section

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

theorem UpperTheory.isFunctionField_fractionRing_of_dedekind_finiteType :
    ∀ (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → IsFunctionField k (FractionRing B) := by
  intro k B _ _ _ _ _ hB
  have hdim : ringKrullDim B = 1 := by
    apply eq_of_le_of_not_lt ?_ fun h' ↦ hB ?_
    · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
      infer_instance
    · have h'' : ringKrullDim B ≤ 0 := Order.le_of_lt_succ h'
      rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
      exact Ring.KrullDimLE.isField_of_isDomain
  exact GroundTheory.Arith.SchemeCoh.isFunctionField_of_ringKrullDim_eq_one k B (FractionRing B) hdim
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.CurvePicardOfSelmerPicardOfModelCurve

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.curve_picard_of_selmerPicard_of_modelCurve :
    LateralTheory.E.LeafPicCut.LeafSelPic → LateralTheory.E.LeafCurveVCut.LeafModelCurve → LateralTheory.E.E4.LeafPic := by
  intro hSel hModel hH q _ k B _ _ _ _ _ _ hq
  by_cases hB : IsField B
  · letI := hB.toField
    haveI : Subsingleton (CommRing.Pic B) := inferInstance
    exact Finite.of_subsingleton
  · haveI hK : IsFunctionField k (FractionRing B) := UpperTheory.isFunctionField_fractionRing_of_dedekind_finiteType k B hB
    obtain ⟨u, hu, hfd⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := FractionRing B)
    obtain ⟨C0, c0, x, ψ, hc, hx, hψ⟩ := hModel k (FractionRing B) u hu hfd
    haveI : IsIntegral C0 := hc.1
    obtain rfl : x = genericPoint C0 := hx.eq (genericPoint_spec C0)
    letI : Algebra k C0.functionField :=
      (CommRingCat.ofHom (algebraMap k (FractionRing B)) ≫ Spec.preimage ψ).hom.toAlgebra
    letI : Algebra (FractionRing B) C0.functionField := (Spec.preimage ψ).hom.toAlgebra
    haveI : IsScalarTower k (FractionRing B) C0.functionField := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have heq : Spec.map (CommRingCat.ofHom (algebraMap k C0.functionField)) =
        C0.fromSpecStalk (genericPoint C0) ≫ c0 := by
      change Spec.map (CommRingCat.ofHom (algebraMap k (FractionRing B)) ≫ Spec.preimage ψ) = _
      rw [Spec.map_comp, Spec.map_preimage, hψ]
    obtain ⟨hF, hch⟩ := UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit hH q k hq c0 hc heq
    haveI := hF
    exact UpperTheory.finite_pic_torsion_of_finite_kummerSelmer hSel k B q
      (UpperTheory.finite_kummerSelmer_of_finite_extension k (FractionRing B) C0.functionField q hq (UpperTheory.finite_kummerSelmer_of_charts k _ q hch))
end
end
