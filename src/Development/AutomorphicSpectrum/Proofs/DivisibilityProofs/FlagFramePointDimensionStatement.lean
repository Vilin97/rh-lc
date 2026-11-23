module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenNumLinear
public import Development.WeilBound.CoreStatements.IdealCycleValues.IntersectionNumbersPermInvariant
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSymmetricSpanHsymm
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Polynomial.Basic
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import Development.WeilBound.CoreStatements.IdealCycleValues.ProjIdealIndependentOfBasis
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PflagZ

-- Source module: Development.WeilBound.CoreStatements.IdealCycleValues.GenNumMulExpansion

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.genNum_mul_expansion : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (V : Ideal (MRing ι F)) (cls : σ → K → ℤ) (H G : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (H * G) Q = ∑ μ ∈ G.support, G.coeff μ * genNum F V cls H (classList cls μ ++ Q) := by
  intro F _ K _ _ ι _ σ V cls H G Q
  classical
  have key : ∀ (P : MvPolynomial σ ℝ) (L : List (K → ℤ)) (s : Finset (σ →₀ ℕ)), P.support ⊆ s →
      genNum F V cls P L = ∑ κ ∈ s, AddMonoidAlgebra.coeff P κ * (intNumL F V (classList cls κ ++ L) : ℝ) := by
    intro P L s hs
    show ∑ κ ∈ P.support, AddMonoidAlgebra.coeff P κ * (intNumL F V (classList cls κ ++ L) : ℝ) = _
    refine Finset.sum_subset hs (fun κ _ hκ => ?_)
    rw [MvPolynomial.notMem_support_iff.mp hκ, zero_mul]
  have hadd : ∀ P P' : MvPolynomial σ ℝ, genNum F V cls (P + P') Q = genNum F V cls P Q + genNum F V cls P' Q := by
    intro P P'
    rw [key (P + P') Q (P.support ∪ P'.support) MvPolynomial.support_add,
      key P Q (P.support ∪ P'.support) Finset.subset_union_left,
      key P' Q (P.support ∪ P'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_add, add_mul]
  have hzero : genNum F V cls (0 : MvPolynomial σ ℝ) Q = 0 := by
    rw [key 0 Q ∅ (by simp)]
    simp
  have hsum : ∀ (α : Type) (s : Finset α) (P : α → MvPolynomial σ ℝ),
      genNum F V cls (∑ a ∈ s, P a) Q = ∑ a ∈ s, genNum F V cls (P a) Q := by
    intro α s P
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  have hmon : ∀ (κ : σ →₀ ℕ) (c : ℝ), genNum F V cls (monomial κ c) Q = c * (intNumL F V (classList cls κ ++ Q) : ℝ) := by
    intro κ c
    rw [key _ Q {κ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]
  have hperm : ∀ ν μ : σ →₀ ℕ, intNumL F V (classList cls (ν + μ) ++ Q) = intNumL F V (classList cls ν ++ (classList cls μ ++ Q)) := by
    intro ν μ
    have hp : (classList cls (ν + μ)).Perm (classList cls ν ++ classList cls μ) := by
      rw [← Multiset.coe_eq_coe, ← Multiset.coe_add]
      simp only [classList, Multiset.coe_toList, Finsupp.toMultiset_add, Multiset.map_add (f := _)]
    rw [← List.append_assoc]
    exact BaseChangeColon.intersection_numbers_perm_invariant.1 F K ι V _ _ (hp.append_right Q)
  conv_lhs => rw [H.as_sum, G.as_sum, Finset.sum_mul_sum]
  rw [hsum]
  simp_rw [hsum, MvPolynomial.monomial_mul, hmon]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [key H (classList cls μ ++ Q) H.support subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [hperm]
  ring
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenNumProductExpansion

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem genNum_mul_expand : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (V : Ideal (MRing ι F)) (cls : σ → K → ℤ) (H G : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (H * G) Q = ∑ μ ∈ G.support, G.coeff μ * genNum F V cls H (classList cls μ ++ Q) :=
  @BaseChangeColon.genNum_mul_expansion

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HasExpansionOfMemSpan

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

noncomputable section

def negReal (N : ℕ) : MvPolynomial (Fin N) ℤ →ₐ[ℤ] MvPolynomial (Fin N) ℝ :=
  aeval fun i => (-X i : MvPolynomial (Fin N) ℝ)

theorem negReal_hsymm (N a : ℕ) :
    negReal N (hsymm (Fin N) ℤ a) =
      aeval (fun i => (-X i : MvPolynomial (Fin N) ℝ)) (hsymm (Fin N) ℝ a) := by

  simp only [negReal, hsymm, map_sum, map_multiset_prod, Multiset.map_map, Function.comp_def, aeval_X]

theorem negReal_isHomogeneous {N n : ℕ} {P : MvPolynomial (Fin N) ℤ} (hP : P.IsHomogeneous n) :
    (negReal N P).IsHomogeneous n := by
  have h := hP.aeval (S := ℝ) (n := 1) (fun i => (-X i : MvPolynomial (Fin N) ℝ))
    (fun i => (isHomogeneous_X ℝ i).neg)
  simpa [negReal] using h

theorem negReal_psum (N k : ℕ) :
    negReal N (psum (Fin N) ℤ k) = (-1) ^ k * ∑ i, (X i ^ k : MvPolynomial (Fin N) ℝ) := by

  simp only [negReal, psum, map_sum, map_pow, aeval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_pow]

def HasExpansion (N k : ℕ) (G : MvPolynomial (Fin N) ℤ) : Prop :=
  ∃ R : ℕ → MvPolynomial (Fin N) ℝ, (∀ a, (R a).IsHomogeneous (k - a)) ∧
    negReal N G = ∑ a ∈ Finset.Icc 1 k,
      aeval (fun i => (-X i : MvPolynomial (Fin N) ℝ)) (hsymm (Fin N) ℝ a) * R a

theorem hasExpansion_hsymmPart {N k : ℕ} (hk : 1 ≤ k) (μ : k.Partition) :
    HasExpansion N k (hsymmPart (Fin N) ℤ μ) := by
  classical
  have hne : μ.parts ≠ 0 := by
    intro h
    have := μ.parts_sum
    rw [h] at this
    simp at this
    omega
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem ha
  have hsum : a + t.sum = k := by
    have := μ.parts_sum
    rwa [ht, Multiset.sum_cons] at this
  have hpos : 0 < a := μ.parts_pos ha
  have hmem : a ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hpos, by omega⟩
  refine ⟨Pi.single a (negReal N (t.map (hsymm (Fin N) ℤ)).prod), fun b => ?_, ?_⟩
  · by_cases hb : b = a
    · subst hb
      rw [Pi.single_eq_same]
      have h := negReal_isHomogeneous (SymmetricSpanHsymm.isHomogeneous_prod_map_hsymm (σ := Fin N) t)
      rwa [show t.sum = k - b by omega] at h
    · rw [Pi.single_eq_of_ne hb]
      exact isHomogeneous_zero _ _ _
  · rw [Finset.sum_eq_single_of_mem a hmem
      (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])]
    rw [Pi.single_eq_same, hsymmPart, ht, Multiset.map_cons, Multiset.prod_cons, map_mul,
      negReal_hsymm]

theorem hasExpansion_of_mem_span {N k : ℕ} (hk : 1 ≤ k) {G : MvPolynomial (Fin N) ℤ}
    (hG : G ∈ Submodule.span ℤ (Set.range fun μ : k.Partition => hsymmPart (Fin N) ℤ μ)) :
    HasExpansion N k G := by
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, rfl⟩ := hx
    exact hasExpansion_hsymmPart hk μ
  | zero => exact ⟨0, fun a => isHomogeneous_zero _ _ _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨R, hR, e⟩ := hx
    obtain ⟨S, hS, f⟩ := hy
    refine ⟨R + S, fun a => (hR a).add (hS a), ?_⟩
    simp only [map_add (f := _), e, f, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  | smul c x _ hx =>
    obtain ⟨R, hR, e⟩ := hx
    refine ⟨fun a => C (c : ℝ) * R a, fun a => ?_, ?_⟩
    · simpa using (isHomogeneous_C (Fin N) (c : ℝ)).mul (hR a)
    · rw [map_zsmul, e, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [zsmul_eq_mul, show ((c : MvPolynomial (Fin N) ℝ)) = C (c : ℝ) by simp]
      ring

theorem psum_eq_sum_hsymm_neg :
    ∀ (N k : ℕ), 1 ≤ k → ∃ R : ℕ → MvPolynomial (Fin N) ℝ, (∀ a, (R a).IsHomogeneous (k - a)) ∧
      (∑ i, X i ^ k : MvPolynomial (Fin N) ℝ) = ∑ a ∈ Finset.Icc 1 k,
        aeval (fun i => (-X i : MvPolynomial (Fin N) ℝ)) (hsymm (Fin N) ℝ a) * R a := by
  intro N k hk
  obtain ⟨R, hR, e⟩ := hasExpansion_of_mem_span hk
    (SymmetricSpanHsymm.full N k (psum (Fin N) ℤ k) (isHomogeneous_psum N k) (psum_isSymmetric _ _ _))
  refine ⟨fun a => C ((-1) ^ k) * R a, fun a => ?_, ?_⟩
  · simpa using (isHomogeneous_C (Fin N) (((-1 : ℝ)) ^ k)).mul (hR a)
  · have h1 : ((-1 : MvPolynomial (Fin N) ℝ) ^ k) * (-1) ^ k = 1 := by
      rw [← mul_pow]; simp
    rw [negReal_psum] at e
    calc (∑ i, X i ^ k : MvPolynomial (Fin N) ℝ)
        = (-1) ^ k * ((-1) ^ k * ∑ i, (X i ^ k : MvPolynomial (Fin N) ℝ)) := by
          rw [← mul_assoc, h1, one_mul]
      _ = _ := by
          rw [e, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [map_pow, map_neg, map_one]
          ring

end

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- Source module: Development.WeilBound.CoreStatements.IdealCycleValues.FlagFrameOfPointIdeal

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace BaseChangeColon

theorem foldr_diffStep_zero {K : Type} (l : List (K → ℤ)) (hl : (0 : K → ℤ) ∈ l) (h : (K → ℤ) → ℤ) :
    l.foldr diffStep h = 0 := by
  induction l with
  | nil => simp at hl
  | cons b l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hl with hb | hb
    · subst hb
      funext m
      simp [diffStep]
    · rw [ih hb]
      funext m
      simp [diffStep]

theorem intNumL_of_zero_mem {F : Type} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}
    (V : Ideal (MRing ι F)) (l : List (K → ℤ)) (hl : (0 : K → ℤ) ∈ l) : intNumL F V l = 0 := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get, foldr_diffStep_zero l hl]
  unfold eventualValue
  split_ifs with h
  · obtain ⟨m, hm⟩ := h.choose_spec.exists
    exact hm.symm
  · rfl

theorem flag_frame_of_point_ideal : NumericalSegre.Statement → ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (w : Module.Basis (Fin N) Ω (Fin N → Ω)) (b : Fin N → K → ℤ), IsFlagFrame y (scaledTrivBundle F (segreVec y) N (one_ne_zero (α := Ω))) w b → ∀ a : ℕ, 1 ≤ a → ∀ Y : List (K → ℤ), a + Y.length = e → ∑ α ∈ Finset.Nat.antidiagonalTuple N a, intNumL F (pointIdeal F y) (rootList (fun i => -b i) α ++ Y) = 0 := by
  intro hS F _ Ω _ _ K _ _ ι _ y e hP hd N w b hw a ha Y hY
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    exact Finset.sum_eq_zero fun α hα => by
      rw [Finset.Nat.mem_antidiagonalTuple] at hα
      simp at hα
  have ht : AlgebraicIndependent Ω
      ((IsScalarTower.toAlgHom Ω (MvPolynomial (Fin N) Ω) (FractionRing (MvPolynomial (Fin N) Ω))) ∘ X) :=
    (MvPolynomial.algebraicIndependent_X (Fin N) Ω).map'
      (IsFractionRing.injective (MvPolynomial (Fin N) Ω) (FractionRing (MvPolynomial (Fin N) Ω)))
  have h1 := hS F Ω K ι y e hP hd N hN _ _ w b hw N 0 _ (isTwistedDualGens_triv F y N) _ _ ht
    (N - 1 + a) Y (by omega)
  have h2 := hS F Ω K ι y e hP hd N hN _ _ _ _ (isFlagFrame_scaledTriv F y N (one_ne_zero (α := Ω))) N 0 _
    (isTwistedDualGens_triv F y N) _ _ ht (N - 1 + a) Y (by omega)
  rw [projIdeal_independent_of_basis F Ω K ι y N N _ w (scaledBasis N (one_ne_zero (α := Ω))) _ _ _ ht, h2,
    if_pos (Nat.le_add_right _ _), if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at h1
  simp only [zero_sub] at h1
  rw [← h1]
  refine Finset.sum_eq_zero fun α hα => intNumL_of_zero_mem _ _ ?_
  rw [Finset.Nat.mem_antidiagonalTuple] at hα
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := α) (by omega)
  refine List.mem_append_left _ ?_
  unfold rootList
  refine List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_replicate.mpr ⟨hi, by simp⟩⟩

end BaseChangeColon
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HsymmDualRootsTrivNumZero

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem hsymm_dualRoots_triv_numZero : NumericalSegre.Statement → ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (w : Module.Basis (Fin N) Ω (Fin N → Ω)) (b : Fin N → K → ℤ), IsFlagFrame y (scaledTrivBundle F (segreVec y) N (one_ne_zero (α := Ω))) w b → ∀ a : ℕ, 1 ≤ a → ∀ Y : List (K → ℤ), a + Y.length = e → ∑ α ∈ Finset.Nat.antidiagonalTuple N a, intNumL F (pointIdeal F y) (rootList (fun i => -b i) α ++ Y) = 0 :=
  BaseChangeColon.flag_frame_of_point_ideal

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagFramePointDimension

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_frame_point_dimension : NumericalSegre.Statement → ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (w : Module.Basis (Fin N) Ω (Fin N → Ω)) (b : Fin N → K → ℤ), IsFlagFrame y (scaledTrivBundle F (segreVec y) N (one_ne_zero (α := Ω))) w b → ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = e → genNum F (pointIdeal F y) b (∑ i, X i ^ k) Q = 0 := by
  intro hS F _ Ω _ _ K _ _ ι _ y e hP hdim N w b hb k hk Q hQ
  obtain ⟨R, hR, hsum⟩ := psum_eq_sum_hsymm_neg N k hk
  rw [hsum, (genNum_linear F K ι (Fin N) (pointIdeal F y) b Q).2.2.1]
  refine Finset.sum_eq_zero fun a ha => ?_
  obtain ⟨ha1, hak⟩ := Finset.mem_Icc.mp ha
  rw [genNum_mul_expand]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  have hlen : (classList b μ).length = k - a :=
    PositivityTheory.HtPt.Pflag.length_classList_of_hom b (hR a) hμ
  have hl : a + (classList b μ ++ Q).length = e := by
    rw [List.length_append, hlen]
    omega
  rw [PositivityTheory.HtPt.Pflag.genNum_neg F K ι (pointIdeal F y) e hP hdim b _ a
      (PositivityTheory.HtPt.Pflag.isHomogeneous_hsymm_real N a) _ hl,
    PositivityTheory.HtPt.Pflag.genNum_hsymm,
    hsymm_dualRoots_triv_numZero hS F Ω K ι y e hP hdim N w b hb a ha1 _ hl]
  simp
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagFramePointDimensionStatement

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.flag_frame_point_dimension : NumericalSegre.Statement → ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (w : Module.Basis (Fin N) Ω (Fin N → Ω)) (b : Fin N → K → ℤ), IsFlagFrame y (scaledTrivBundle F (segreVec y) N (one_ne_zero (α := Ω))) w b → ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = e → genNum F (pointIdeal F y) b (∑ i, X i ^ k) Q = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flag_frame_point_dimension | exact GlobalTheory.CompanionTheory.Relay.flag_frame_point_dimension | (intros; apply GlobalTheory.CompanionTheory.Relay.flag_frame_point_dimension <;> assumption)
end
end
