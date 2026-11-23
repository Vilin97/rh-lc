module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorQuotientSmulTopOfFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthGeThreeFiniteEtalePuncturedRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleQuotientOfEtalePuncturedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSMulRegularOfEtalePuncturedOfDepthPosStatement
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEQuotientMapSpanSingleton
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoOfIsIntegrallyClosedOfIsRegularLoca
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GDimcpl
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Regular.Flat
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.Field
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ExistsIsRegularAppendOfModDepthGE
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEQuotientMapSpanSingletonStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.modDepthGE_quotient_span_of_isSMulRegular : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Finite R A] (f : R), f ∈ maximalIdeal R → ∀ [IsLocalRing (R ⧸ Ideal.span {f})], IsSMulRegular A f → ∀ n : ℕ, ReciprocityTheory.CA.ModDepthGE R A (n + 1) → ReciprocityTheory.CA.ModDepthGE (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) n := by
  first | exact @GlobalTheory.modDepthGE_quotient_map_span_singleton | exact GlobalTheory.modDepthGE_quotient_map_span_singleton | (intros; apply GlobalTheory.modDepthGE_quotient_map_span_singleton <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoOfIsIntegrallyClosedOfIsRegularLocaStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing' : ∀ (R A : Type) [CommRing R] [IsRegularLocalRing R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], 2 ≤ ringKrullDim R → ReciprocityTheory.CA.ModDepthGE R A 2 := by
  first | exact @GlobalTheory.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing | exact GlobalTheory.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing | (intros; apply GlobalTheory.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleFreeOfRegularOfFreeQuotientLocal

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory.AnnRegSeq

theorem free_of_free_quotient_map (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] (f : R) (hf : f ∈ maximalIdeal R)
    (reg : IsSMulRegular A f)
    (hfree : Module.Free (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A))) :
    Module.Free R A := by
  set I : Ideal R := Ideal.span {f}
  have hsub : I • (⊤ : Submodule R A) = (I.map (algebraMap R A)).restrictScalars R :=
    Ideal.smul_top_eq_map I
  let e0 : (A ⧸ I • (⊤ : Submodule R A)) ≃ₗ[R] (A ⧸ I.map (algebraMap R A)) :=
    (Submodule.quotEquivOfEq _ _ hsub).trans
      (Submodule.Quotient.restrictScalarsEquiv R (I.map (algebraMap R A)))
  let e : (A ⧸ I • (⊤ : Submodule R A)) ≃ₗ[R ⧸ I] (A ⧸ I.map (algebraMap R A)) :=
    { e0.toAddEquiv with
      map_smul' := by
        intro c x
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        show e0 (Ideal.Quotient.mk I c • Submodule.Quotient.mk x) = Ideal.Quotient.mk I c • e0 (Submodule.Quotient.mk x)
        rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul, algebraMap_smul, map_smul] }
  haveI := hfree
  haveI : Module.Free (R ⧸ I) (A ⧸ I • (⊤ : Submodule R A)) := Module.Free.of_equiv e.symm
  exact free_of_free_quotient hf reg

end GlobalTheory.AnnRegSeq
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleFreeOfRegularOfFreeQuotientLocalStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.moduleFree_of_regular_of_free_quotient_local : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Finite R A] (f : R), f ∈ maximalIdeal R → IsSMulRegular A f → Module.Free (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) → Module.Free R A := by
  first | exact @GlobalTheory.AnnRegSeq.free_of_free_quotient_map | exact GlobalTheory.AnnRegSeq.free_of_free_quotient_map | (intros; apply GlobalTheory.AnnRegSeq.free_of_free_quotient_map <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFreeOfCompleteRegularLocal

section

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory.PurityComplete

variable (R : Type) [CommRing R] [IsRegularLocalRing R]

theorem algebraMap_mem_maximalIdeal {r : R} (hr : r ∈ maximalIdeal R) :
    algebraMap R (AdicCompletion (maximalIdeal R) R) r ∈
      maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.mem_map_of_mem _ hr

theorem faithfullyFlat_adicCompletion :
    Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) := by
  haveI : Module.Flat R (AdicCompletion (maximalIdeal R) R) := AdicCompletion.flat_of_isNoetherian _
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

theorem modDepthGE_two_baseChange (A : Type) [CommRing A] [Algebra R A]
    (h : ReciprocityTheory.CA.ModDepthGE R A 2) :
    ReciprocityTheory.CA.ModDepthGE (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R) R ⊗[R] A) 2 := by
  obtain ⟨rs, hl, hm, hreg⟩ := h
  refine ⟨rs.map (algebraMap R (AdicCompletion (maximalIdeal R) R)), by simp [hl], ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    exact algebraMap_mem_maximalIdeal R (hm s hs)
  · haveI := faithfullyFlat_adicCompletion R
    exact hreg.of_faithfullyFlat_of_isBaseChange (S := AdicCompletion (maximalIdeal R) R)
      (TensorProduct.isBaseChange R A (AdicCompletion (maximalIdeal R) R))

theorem etale_baseChange (A : Type) [CommRing A] [Algebra R A]
    (he : ∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
      Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A))
    (P : Ideal (AdicCompletion (maximalIdeal R) R)) [P.IsPrime]
    (hP : P ≠ maximalIdeal (AdicCompletion (maximalIdeal R) R)) :
    Algebra.Etale (Localization.AtPrime P)
      (TensorProduct (AdicCompletion (maximalIdeal R) R) (Localization.AtPrime P)
        (AdicCompletion (maximalIdeal R) R ⊗[R] A)) := by
  set C := AdicCompletion (maximalIdeal R) R
  set p : Ideal R := P.comap (algebraMap R C) with hpdef
  have hp : p ≠ maximalIdeal R := by
    intro h
    apply hP
    refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_le_iff_le_comap, ← hpdef, h]
  haveI := he p hp
  haveI : P.LiesOver p := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver p P
  let e : Localization.AtPrime P ⊗[Localization.AtPrime p] (Localization.AtPrime p ⊗[R] A) ≃ₐ[Localization.AtPrime P]
      Localization.AtPrime P ⊗[C] (C ⊗[R] A) :=
    (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p) (Localization.AtPrime P)
      (Localization.AtPrime P) A).trans
    (Algebra.TensorProduct.cancelBaseChange R C (Localization.AtPrime P)
      (Localization.AtPrime P) A).symm
  exact Algebra.Etale.of_equiv e

theorem free_of_free_baseChange (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A]
    (h : Module.Free (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal R) R ⊗[R] A)) :
    Module.Free R A := by
  haveI := faithfullyFlat_adicCompletion R
  haveI : Module.Flat R A := Module.Flat.of_flat_tensorProduct R A (AdicCompletion (maximalIdeal R) R)
  exact Module.free_of_flat_of_isLocalRing

end GlobalTheory.PurityComplete

namespace GlobalTheory.PurityStep

theorem purityFree_of_complete :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
      (∀ (S : Type) [CommRing S] [IsRegularLocalRing S], IsAdicComplete (maximalIdeal S) S →
        ringKrullDim S = ringKrullDim R → GlobalTheory.PurityFree S) → GlobalTheory.PurityFree R := by
  intro R _ _ H A _ _ _ hd he
  haveI : IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) :=
    GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion R
  have hC := H (AdicCompletion (maximalIdeal R) R) inferInstance (UpperTheory.V.CA.g_dimcpl R)
  refine GlobalTheory.PurityComplete.free_of_free_baseChange R A ?_
  exact hC _ (GlobalTheory.PurityComplete.modDepthGE_two_baseChange R A hd)
    (fun P _ hP => GlobalTheory.PurityComplete.etale_baseChange R A he P hP)

end GlobalTheory.PurityStep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFreeOfCompleteRegularLocalStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.purityFree_of_complete_regularLocal : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], (∀ (S : Type) [CommRing S] [IsRegularLocalRing S], IsAdicComplete (maximalIdeal S) S → ringKrullDim S = ringKrullDim R → GlobalTheory.PurityFree S) → GlobalTheory.PurityFree R := by
  first | exact @GlobalTheory.PurityStep.purityFree_of_complete | exact GlobalTheory.PurityStep.purityFree_of_complete | (intros; apply GlobalTheory.PurityStep.purityFree_of_complete <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfEtalePunctured

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory.PurityStep

theorem finite_quot (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A] (f : R) : Module.Finite (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
  Module.Finite.of_restrictScalars_finite R _ _

theorem lowDim (R : Type) [CommRing R] [IsRegularLocalRing R] (h : ringKrullDim R ≤ 2) :
    PurityFree R := by
  intro A _ _ _ hA _
  refine GlobalTheory.AnnRegSeq.free_of_modDepthGE 2 R A hA ?_
  have h1 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ ((2 : ℕ) : WithBot ℕ∞) := by
    rw [h1]; exact_mod_cast h
  exact_mod_cast this

theorem hyperplane (R : Type) [CommRing R] [IsRegularLocalRing R]
    (hc : IsAdicComplete (maximalIdeal R) R) (hd : 3 ≤ ringKrullDim R) (f : R)
    (hf : f ∈ maximalIdeal R) (hf2 : f ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ Ideal.span {f})]
    (hP : PurityFree (R ⧸ Ideal.span {f})) : PurityFree R := by
  intro A _ _ _ hA het
  have h3 := GlobalTheory.T.depth_ge_three_finite_etale_punctured_regular R hc hd f hf hf2 hP A hA het
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf2 (zero_mem _)
  have hreg := GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos' R A (ReciprocityTheory.CA.ModDepthGE.mono (by norm_num) hA) het f hf0
  haveI := finite_quot R A f
  exact GlobalTheory.T.moduleFree_of_regular_of_free_quotient_local R A f hf hreg (hP _ (GlobalTheory.T.modDepthGE_quotient_span_of_isSMulRegular R A f hf hreg 2 h3) (GlobalTheory.T.etale_quotient_of_etale_punctured' R A f het))

theorem purityFree_of_ringKrullDim (n : ℕ) : ∀ (S : Type) [CommRing S] [IsRegularLocalRing S],
    ringKrullDim S = n → PurityFree S := by
  induction n with
  | zero =>
    intro S _ _ hS
    exact lowDim S (by rw [hS]; norm_num)
  | succ n ih =>
    intro S _ _ hS
    by_cases h2 : n + 1 ≤ 2
    · exact lowDim S (by rw [hS]; exact_mod_cast h2)
    refine GlobalTheory.T.purityFree_of_complete_regularLocal S fun S' _ _ hc hd' => ?_
    rw [hS] at hd'
    have hsq : ¬ maximalIdeal S' ≤ maximalIdeal S' ^ 2 := by
      intro h
      have h0 := GlobalTheory.AnnRegSeq.maximalIdeal_eq_bot_of_le_sq h
      have := ringKrullDim_eq_zero_of_isField ((IsLocalRing.isField_iff_maximalIdeal_eq (R := S')).mpr h0)
      rw [this] at hd'
      exact absurd hd' (by norm_cast)
    obtain ⟨f, hf, hf2⟩ := Set.not_subset.mp hsq
    haveI := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hf
    haveI hQ := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hf hf2
    have hdim := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hf hf2
    have hsp : ((maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank : WithBot ℕ∞) =
        ringKrullDim (S' ⧸ Ideal.span {f}) := IsRegularLocalRing.spanFinrank_maximalIdeal
    rw [← hsp, hd'] at hdim
    have hk : (maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank = n := by
      have : (maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank + 1 = n + 1 := by
        exact_mod_cast hdim
      omega
    refine hyperplane S' hc ?_ f hf hf2 (ih _ ?_)
    · rw [hd']; exact_mod_cast (by omega : 3 ≤ n + 1)
    · rw [← hsp, hk]

theorem free_of_etale_punctured : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 3 ≤ ringKrullDim R → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Module.Free R A := by
  intro R A _ _ _ _ _ _ _ _ _ _ hreg hd het
  haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hreg
  refine purityFree_of_ringKrullDim _ R hreg.symm A (GlobalTheory.T.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing' R A (le_trans (by norm_num) hd)) het

end GlobalTheory.PurityStep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfEtalePuncturedStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.free_of_etale_on_punctured_spectrum : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 3 ≤ ringKrullDim R → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Module.Free R A := by
  first | exact @GlobalTheory.PurityStep.free_of_etale_punctured | exact GlobalTheory.PurityStep.free_of_etale_punctured | (intros; apply GlobalTheory.PurityStep.free_of_etale_punctured <;> assumption)
end
end
