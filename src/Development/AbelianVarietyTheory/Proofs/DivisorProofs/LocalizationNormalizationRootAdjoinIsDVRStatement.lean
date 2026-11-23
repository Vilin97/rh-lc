module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationIntegralClosureArtinianReducedDomainStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisationDvrTensorSeparableFiniteStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerUniformiserAdjoinRootTensorIsReduced

section

@[expose] public section

open IsLocalRing



namespace GlobalTheory

open Polynomial TensorProduct

namespace KummerRootTensor

variable {E : Type} [CommRing E] (B : Type) [CommRing B] [Algebra E B]

theorem aeval_root_map (Q : E[X]) :
    Polynomial.aeval (AdjoinRoot.root (Q.map (algebraMap E B))) Q = 0 := by
  rw [← Polynomial.aeval_map_algebraMap B, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

theorem aeval_one_tmul_root (Q : E[X]) :
    Polynomial.aeval ((1 : B) ⊗ₜ[E] AdjoinRoot.root Q) (Q.map (algebraMap E B)) = 0 := by
  have h : (1 : B) ⊗ₜ[E] AdjoinRoot.root Q =
      (Algebra.TensorProduct.includeRight : AdjoinRoot Q →ₐ[E] B ⊗[E] AdjoinRoot Q)
        (AdjoinRoot.root Q) := rfl
  rw [Polynomial.aeval_map_algebraMap, h, Polynomial.aeval_algHom_apply, AdjoinRoot.aeval_eq,
    AdjoinRoot.mk_self, map_zero]

noncomputable def toMap (Q : E[X]) : AdjoinRoot Q →ₐ[E] AdjoinRoot (Q.map (algebraMap E B)) :=
  AdjoinRoot.liftAlgHom Q (Algebra.ofId E _) (AdjoinRoot.root (Q.map (algebraMap E B)))
    (aeval_root_map B Q)

noncomputable def fromMap (Q : E[X]) :
    AdjoinRoot (Q.map (algebraMap E B)) →ₐ[B] B ⊗[E] AdjoinRoot Q :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId B _) ((1 : B) ⊗ₜ[E] AdjoinRoot.root Q)
    (aeval_one_tmul_root B Q)

theorem toMap_root (Q : E[X]) :
    toMap B Q (AdjoinRoot.root Q) = AdjoinRoot.root (Q.map (algebraMap E B)) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem fromMap_root (Q : E[X]) :
    fromMap B Q (AdjoinRoot.root (Q.map (algebraMap E B))) = (1 : B) ⊗ₜ[E] AdjoinRoot.root Q :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

noncomputable def toTensorMap (Q : E[X]) :
    B ⊗[E] AdjoinRoot Q →ₐ[B] AdjoinRoot (Q.map (algebraMap E B)) :=
  Algebra.TensorProduct.lift (Algebra.ofId B _) (toMap B Q) (fun _ _ => Commute.all _ _)

theorem toTensorMap_one_tmul_root (Q : E[X]) :
    toTensorMap B Q ((1 : B) ⊗ₜ[E] AdjoinRoot.root Q) = AdjoinRoot.root (Q.map (algebraMap E B)) := by
  rw [toTensorMap, Algebra.TensorProduct.lift_tmul, map_one, one_mul, toMap_root]

noncomputable def tensorEquiv (Q : E[X]) :
    B ⊗[E] AdjoinRoot Q ≃ₐ[B] AdjoinRoot (Q.map (algebraMap E B)) :=
  AlgEquiv.ofAlgHom (toTensorMap B Q) (fromMap B Q)
    (by
      apply AdjoinRoot.algHom_ext
      show toTensorMap B Q (fromMap B Q (AdjoinRoot.root _)) = _
      rw [fromMap_root, toTensorMap_one_tmul_root]; rfl)
    (by
      apply Algebra.TensorProduct.ext
      · exact Subsingleton.elim _ _
      · apply AdjoinRoot.algHom_ext
        show fromMap B Q (toTensorMap B Q ((1 : B) ⊗ₜ[E] AdjoinRoot.root Q)) = _
        rw [toTensorMap_one_tmul_root, fromMap_root]; rfl)

end KummerRootTensor

theorem kummer_uniformiser_tensor_isReduced : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    IsReduced (TensorProduct S D L) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ hφ hπ he
  obtain ⟨φ⟩ := hφ
  set f : S[X] := X ^ e - C π with hf
  have hinj : Function.Injective (algebraMap S L) := by
    rw [IsScalarTower.algebraMap_eq S K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective S K)
  have hπ' : algebraMap S L π ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 hπ.ne_zero
  have he' : (e : L) ≠ 0 := by
    have := he.map (algebraMap S L)
    rw [map_natCast] at this
    exact this.ne_zero
  have hmap : f.map (algebraMap S L) = X ^ e - C (algebraMap S L π) := by
    simp [hf, Polynomial.map_sub, Polynomial.map_pow]
  have hsep : (f.map (algebraMap S L)).Separable := by
    rw [hmap]; exact separable_X_pow_sub_C _ he' hπ'
  have hred : IsReduced (AdjoinRoot (f.map (algebraMap S L))) :=
    (Ideal.isRadical_iff_quotient_reduced _).1
      (isRadical_iff_span_singleton.1 hsep.squarefree.isRadical)
  let ψ : TensorProduct S D L ≃ₐ[S] AdjoinRoot (f.map (algebraMap S L)) :=
    (Algebra.TensorProduct.comm S D L).trans
      ((Algebra.TensorProduct.congr AlgEquiv.refl φ).trans
        ((KummerRootTensor.tensorEquiv L f).restrictScalars S))
  exact isReduced_of_injective ψ.toRingHom ψ.injective

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerUniformiserAdjoinRootTensorIsReducedStatement

section

@[expose] public section

open IsLocalRing



theorem _root_.GlobalTheory.T.kummer_uniformiser_adjoinRoot_tensor_isReduced : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    IsReduced (TensorProduct S D L) := by
  first | (exact @GlobalTheory.kummer_uniformiser_tensor_isReduced) | (exact GlobalTheory.kummer_uniformiser_tensor_isReduced) | (intros; apply GlobalTheory.kummer_uniformiser_tensor_isReduced  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationNormalizationRootAdjoinIsDVR

section

@[expose] public section

open IsLocalRing



namespace GlobalTheory.LocNormDVR

theorem artinian (S L D : Type) [CommRing S] [Field L] [Algebra S L] [CommRing D] [Algebra S D]
    [Module.Finite S D] : IsArtinianRing (TensorProduct S D L) := by
  haveI : IsArtinianRing (TensorProduct S L D) := IsArtinianRing.of_finite L _
  exact RingEquiv.isArtinianRing (Algebra.TensorProduct.comm S L D).toRingEquiv

theorem main : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    ∃ _ : IsDomain (Localization.AtPrime Q), IsDiscreteValuationRing (Localization.AtPrime Q) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ hD hπ he _ _ Q _
  obtain ⟨φ⟩ := hD
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at he
    · exact h
  haveI : Module.Finite S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) :=
    (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C π he0.ne')).finite
  haveI : Module.Finite S D := Module.Finite.equiv φ.symm.toLinearEquiv
  haveI : FaithfulSMul S D := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h1 : algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) a =
        algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) b := by
      rw [← φ.commutes, ← φ.commutes, hab]
    set pb := AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C π he0.ne') with hpb
    have hd : 0 < pb.dim := by
      rw [hpb, AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_X_pow_sub_C _]; exact he0
    have h0 : pb.basis ⟨0, hd⟩ = 1 := by rw [PowerBasis.coe_basis]; simp
    have key : ∀ s : S, pb.basis.repr (algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) s)
        ⟨0, hd⟩ = s := by
      intro s
      rw [Algebra.algebraMap_eq_smul_one, ← h0, map_smul, Module.Basis.repr_self]
      simp
    rw [← key a, ← key b, h1]
  haveI : Module.Finite D (integralClosure D (TensorProduct S D L)) := GlobalTheory.T.normalisation_dvr_tensor_separable_finite S K L D
  haveI : IsArtinianRing (TensorProduct S D L) := artinian S L D
  haveI : IsReduced (TensorProduct S D L) := GlobalTheory.T.kummer_uniformiser_adjoinRoot_tensor_isReduced S K L π e D ⟨φ⟩ hπ he
  obtain ⟨hdom, hic⟩ := GlobalTheory.T.localization_integralClosure_artinian_reduced_domain D (TensorProduct S D L) Q
  refine ⟨hdom, ?_⟩
  haveI : IsNoetherianRing (integralClosure D (TensorProduct S D L)) :=
    IsNoetherianRing.of_finite D _
  haveI : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  haveI : Module.Flat S K := IsLocalization.flat K (nonZeroDivisors S)
  haveI : Module.Flat S L := Module.Flat.trans S K L
  have htf : ∀ a : D, a ≠ 0 → ∀ x : integralClosure D (TensorProduct S D L), a • x = 0 → x = 0 := by
    intro a ha x hax
    have hinj : Function.Injective (LinearMap.rTensor L (LinearMap.mulLeft S a)) :=
      Module.Flat.rTensor_preserves_injective_linearMap _
        (fun y z h => (mul_right_injective₀ ha) h)
    have hsmul : ∀ z : TensorProduct S D L,
        a • z = LinearMap.rTensor L (LinearMap.mulLeft S a) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul y l => simp [TensorProduct.smul_tmul']
      | add u v hu hv => rw [smul_add, map_add (f := _), hu, hv]
    have h1 : a • (x : TensorProduct S D L) = 0 := congrArg Subtype.val hax
    rw [hsmul, ← map_zero (LinearMap.rTensor L (LinearMap.mulLeft S a))] at h1
    exact Subtype.ext (hinj h1)
  have hQu : Q.comap (algebraMap D (integralClosure D (TensorProduct S D L))) = maximalIdeal D :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := D) Q)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D
  have hϖQ : algebraMap D (integralClosure D (TensorProduct S D L)) ϖ ∈ Q := by
    rw [← Ideal.mem_comap, hQu]; exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have hnf : ¬ IsField (Localization.AtPrime Q) := by
    intro hF
    have hmax : maximalIdeal (Localization.AtPrime Q) = ⊥ :=
      (IsLocalRing.isField_iff_maximalIdeal_eq).1 hF
    have hmem : algebraMap _ (Localization.AtPrime Q)
        (algebraMap D (integralClosure D (TensorProduct S D L)) ϖ) ∈
        maximalIdeal (Localization.AtPrime Q) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ hϖQ
    rw [hmax, Ideal.mem_bot, IsLocalization.map_eq_zero_iff Q.primeCompl] at hmem
    obtain ⟨⟨t, ht⟩, hts⟩ := hmem
    have ht0 : t = 0 := htf ϖ hϖ.ne_zero t (by rw [Algebra.smul_def, mul_comm]; exact hts)
    exact ht (ht0 ▸ Q.zero_mem)
  refine ((IsDiscreteValuationRing.TFAE (Localization.AtPrime Q) hnf).out 1 4).2
    (⟨hic, ?_⟩ : IsIntegrallyClosed (Localization.AtPrime Q) ∧
      ∃! P : Ideal (Localization.AtPrime Q), P ≠ ⊥ ∧ P.IsPrime)
  refine ⟨maximalIdeal _, ⟨⟨?_, inferInstance⟩, ?_⟩⟩
  · intro h; exact hnf ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)
  · rintro P ⟨hP0, hP⟩
    by_contra hne
    have hlt : P < maximalIdeal _ := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hP.ne_top) hne
    have hbl : (⊥ : Ideal (Localization.AtPrime Q)) < P := bot_lt_iff_ne_bot.2 hP0
    have h1 : (⊥ : Ideal (Localization.AtPrime Q)).comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)) <
        P.comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)) := (IsLocalization.orderEmbedding Q.primeCompl (Localization.AtPrime Q)).strictMono hbl
    have h2 : P.comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)) <
        (maximalIdeal (Localization.AtPrime Q)).comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)) :=
      (IsLocalization.orderEmbedding Q.primeCompl (Localization.AtPrime Q)).strictMono hlt
    have hc : (maximalIdeal (Localization.AtPrime Q)).comap
        (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)) = Q :=
      Localization.AtPrime.under_maximalIdeal
    rw [hc] at h2
    haveI : ((⊥ : Ideal (Localization.AtPrime Q)).comap
        (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q))).IsPrime := Ideal.comap_isPrime _ _
    haveI : (P.comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q))).IsPrime := Ideal.comap_isPrime _ _
    have k1 := Ideal.IsIntegral.comap_lt_comap (R := D) h1
    have k2 := Ideal.IsIntegral.comap_lt_comap (R := D) h2
    change _ < Q.comap (algebraMap D (integralClosure D (TensorProduct S D L))) at k2
    rw [hQu] at k2
    have hp1 : ((P.comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q))).comap
        (algebraMap D (integralClosure D (TensorProduct S D L)))).IsPrime := Ideal.comap_isPrime _ _
    have hmx := hp1.isMaximal (ne_bot_of_gt k1)
    exact (ne_of_lt k2) (IsLocalRing.eq_maximalIdeal hmx)

end GlobalTheory.LocNormDVR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationNormalizationRootAdjoinIsDVRStatement

section

@[expose] public section

open IsLocalRing



theorem _root_.GlobalTheory.T.localization_normalization_rootAdjoin_isDVR : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    ∃ _ : IsDomain (Localization.AtPrime Q), IsDiscreteValuationRing (Localization.AtPrime Q) := by
  first | (exact @GlobalTheory.LocNormDVR.main) | (exact GlobalTheory.LocNormDVR.main) | (intros; apply GlobalTheory.LocNormDVR.main  <;> assumption)
end
end
