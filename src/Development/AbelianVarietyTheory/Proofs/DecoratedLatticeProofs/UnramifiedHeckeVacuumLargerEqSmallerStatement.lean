module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeActsByScalarCommutative
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalThetaInertPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeA
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeTranslateOfMemSpanFixedTranslates

section

@[expose] public section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta.AvgHecke

open GlobalTheory.PRep

theorem exists_hecke_of_mem_span : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (s w : M), (∀ k ∈ K, ρ k s = s) → (∀ k ∈ K, ρ k w = w) → w ∈ Submodule.span ℂ (Set.range fun g => ρ g s) → ∃ h ∈ Hecke ℂ K, heckeVec ρ K h s = w := by
  classical
  intro G _ K hK M _ _ ρ s w hs hw hspan
  have hx : s ∈ fixed ρ K := GlobalTheory.LGrp.mem_fixed.2 hs
  have hy : w ∈ fixed ρ K := GlobalTheory.LGrp.mem_fixed.2 hw
  have hr : w ∈ LinearMap.range (GlobalTheory.LFun.HeckeScalar.orbitMap ρ K s) := by
    refine Submodule.span_le.2 ?_ hspan
    rintro _ ⟨g, rfl⟩
    exact ⟨Finsupp.single (g : G ⧸ K) 1, by rw [GlobalTheory.LFun.HeckeScalar.orbitMap_single hx, one_smul]⟩
  obtain ⟨φ, rfl⟩ := hr
  obtain ⟨ψ, hψ, e⟩ := GlobalTheory.LFun.HeckeScalar.exists_fixed_preimage _ (GlobalTheory.LFun.HeckeScalar.orbitMap_permRep hx)
    (GlobalTheory.LFun.HeckeScalar.mem_finOrbit hK φ) hy
  refine ⟨fun g => ψ g, ⟨fun a b g => ?_, ψ.support.image Quotient.out, fun g hg => ?_⟩, ?_⟩
  · have := GlobalTheory.LFun.HeckeScalar.permRep_apply (a : G) ψ (g : G ⧸ K)
    rw [GlobalTheory.LGrp.mem_fixed.1 hψ _ a.2] at this
    simpa using this
  · obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul K g
    exact ⟨_, Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.2 hg), 1, j⁻¹, by simp [hj]⟩
  · rw [← e, heckeVec, GlobalTheory.LFun.HeckeScalar.orbitMap, Finsupp.linearCombination_apply, Finsupp.sum,
      finsum_eq_sum_of_support_subset (s := ψ.support)]
    · simp
    · intro c hc
      by_contra h
      exact hc (by simp [Finsupp.notMem_support_iff.1 h])

end GlobalTheory.SphTheta.AvgHecke

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeTranslateOfMemSpanFixedTranslatesStatement

section

@[expose] public section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_hecke_translate_of_mem_span_fixed_translates : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (s w : M), (∀ k ∈ K, ρ k s = s) → (∀ k ∈ K, ρ k w = w) → w ∈ Submodule.span ℂ (Set.range fun g => ρ g s) → ∃ h ∈ Hecke ℂ K, heckeVec ρ K h s = w := by
  first | exact @GlobalTheory.SphTheta.AvgHecke.exists_hecke_of_mem_span | exact GlobalTheory.SphTheta.AvgHecke.exists_hecke_of_mem_span | (intros; apply GlobalTheory.SphTheta.AvgHecke.exists_hecke_of_mem_span <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeckeVacuumLargerEqSmaller

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LFun (heckeVec)

namespace GlobalTheory.ChainOnto


open Formalism.UG GlobalTheory.Hk3 GlobalTheory.SphTheta in
theorem heckeVec_howe : GlobalTheory.Hk3.HoweUnram → ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ h' ∈ Hecke ℂ (KU σ n'), ∃ h ∈ Hecke ℂ (KU σ n), heckeVec (ω.comp (MonoidHom.inl _ _)) (KU σ n) h s = heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s := by
  intro hH L _ _ _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS h' hh'
  have hU := hS.1.unr
  obtain ⟨-, hw2⟩ := hH L ϖ σ q δ n n' (antiG L n) (antiG L n') ψ M ρ ω hS.1 s hS.2.1 hS.2.2.1 hS.2.2.2
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have hK' := P.isCommensurated_integral_unitary_of_unramified hU n'
  have f1 : ∀ k ∈ KU σ n, ω (k, 1) s = s := fun k hk => hS.1.fix k 1 (mem_KU_iff.1 hk) (one_mem _) s hS.2.2.1
  have f2 : ∀ k ∈ KU σ n', ω (1, k) s = s := fun k hk => hS.1.fix 1 k (one_mem _) (mem_KU_iff.1 hk) s hS.2.2.1
  set w := heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s with hw
  have w1 : ∀ k ∈ KU σ n, ω (k, 1) w = w := fun k hk => by
    rw [hw, GlobalTheory.LFun.map_heckeVec hK' hh' (ρ' := ω.comp (MonoidHom.inr _ _)) (ω (k, 1)) (fun g y => by
      show (ω (k, 1) * ω (1, g)) y = (ω (1, g) * ω (k, 1)) y
      rw [← map_mul, ← map_mul]
      simp), f1 k hk]
  have w2 : ∀ k ∈ KU σ n', ω (1, k) w = w := fun k hk => by
    have hs : s ∈ GlobalTheory.PRep.fixed (ω.comp (MonoidHom.inr _ _)) (KU σ n') := GlobalTheory.LGrp.mem_fixed.2 f2
    let e : GU σ n' ⧸ KU σ n' ≃ GU σ n' ⧸ KU σ n' := MulAction.toPerm k
    conv_rhs => rw [hw, GlobalTheory.LFun.heckeVec_eq_of_section hh'.1 hs (fun c => k * (e.symm c).out) (fun c => by
      rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
      exact e.apply_symm_apply c), ← finsum_comp_equiv e]
    rw [hw]
    refine ((ω (1, k)).toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec hK' hh' _ s)).trans (finsum_congr fun c => ?_)
    have := hh'.1 ⟨k, hk⟩ 1 c.out
    simp only [OneMemClass.coe_one, mul_one] at this
    simp only [Equiv.symm_apply_apply, this, map_mul, LinearMap.toAddMonoidHom_coe, map_smul]
    rfl
  obtain ⟨h, hh, e⟩ := GlobalTheory.T.exists_hecke_translate_of_mem_span_fixed_translates _ (KU σ n) hK M (ω.comp (MonoidHom.inl _ _)) s w f1 w1
    (hw2 w fun g hg => w2 g (mem_KU_iff.2 hg))
  exact ⟨h, hh, e⟩

end GlobalTheory.ChainOnto

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeckeVacuumLargerEqSmallerStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unramified_hecke_vacuum_larger_eq_smaller : GlobalTheory.Hk3.HoweUnram → ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ h' ∈ Hecke ℂ (KU σ n'), ∃ h ∈ Hecke ℂ (KU σ n), heckeVec (ω.comp (MonoidHom.inl _ _)) (KU σ n) h s = heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s := by
  first | exact @GlobalTheory.ChainOnto.heckeVec_howe | exact GlobalTheory.ChainOnto.heckeVec_howe | (intros; apply GlobalTheory.ChainOnto.heckeVec_howe <;> assumption)
end
end
