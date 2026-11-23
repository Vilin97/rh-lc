module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnisotropicTorusFundamentalDomainFiniteMeasureStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleUnitaryGroupConcreteStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LinearIndependentE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularSemisimpleUnitaryDataOfRegular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeIdempotentConstantTermVanishStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralTypeTestVanishStatement
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfAdjointFactorIdempotentOrthogonalSplittingRa

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt Formalism.UG

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E}
  {J : Matrix (Fin n) (Fin n) E} {γ : Matrix (Fin n) (Fin n) E} {k : ℕ} {K : Fin k → Type}
  [∀ i, Field (K i)] [∀ i, Algebra F (K i)]

theorem factorIdem_mul (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) (p : plusAlg σ J γ) :
    factorIdem e i * ((p : genAlg γ) : Matrix (Fin n) (Fin n) E) =
      ((e.symm (Pi.single i (e p i)) : plusAlg σ J γ) : genAlg γ) := by
  have h : e.symm (Pi.single i 1) * p = e.symm (Pi.single i (e p i)) := by
    apply e.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_apply, hj]
  rw [← h]; rfl

theorem factorIdem_mul_self (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    factorIdem e i * factorIdem e i = factorIdem e i := by
  have := factorIdem_mul e i (e.symm (Pi.single i 1))
  rw [AlgEquiv.apply_symm_apply, Pi.single_eq_same] at this
  exact this

theorem factorIdem_ne_zero (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) : factorIdem e i ≠ 0 := by
  intro h
  have h1 : e.symm (Pi.single i 1) = 0 := Subtype.ext (Subtype.ext h)
  have h2 := congrFun (e.symm_apply_eq.1 h1) i
  simp at h2

theorem factorIdem_selfAdj (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    cT (σ : E →+* E) (factorIdem e i) * J = J * factorIdem e i :=
  (e.symm (Pi.single i 1)).2

theorem factorIdem_orth (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    cT (σ : E →+* E) (1 - factorIdem e i) * J * factorIdem e i = 0 := by
  have hq : cT (σ : E →+* E) (((1 - e.symm (Pi.single i 1) : plusAlg σ J γ) : genAlg γ) : Matrix (Fin n) (Fin n) E) * J =
      J * (((1 - e.symm (Pi.single i 1) : plusAlg σ J γ) : genAlg γ) : Matrix (Fin n) (Fin n) E) :=
    (1 - e.symm (Pi.single i 1)).2
  have hc : (((1 - e.symm (Pi.single i 1) : plusAlg σ J γ) : genAlg γ) : Matrix (Fin n) (Fin n) E) =
      1 - factorIdem e i := rfl
  rw [hc] at hq
  rw [hq, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, factorIdem_mul_self, sub_self, Matrix.mul_zero]

theorem factorIdem_comm (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    ∀ l ∈ genAlg γ, l * factorIdem e i = factorIdem e i * l := by
  intro l hl
  exact congrArg Subtype.val (mul_comm (⟨l, hl⟩ : genAlg γ) (e.symm (Pi.single i 1) : plusAlg σ J γ))

end GlobalTheory.FactorSplit

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt Formalism.UG Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E}
  {J : Matrix (Fin n) (Fin n) E} {k : ℕ} {K : Fin k → Type}
  [∀ i, Field (K i)] [∀ i, Algebra F (K i)]

theorem rank_factorIdem {γ : GL (Fin n) E} (hA : ClauseAlg σ J γ) (hP : ClausePlus σ J γ)
    (e : plusAlg σ J (γ : Matrix (Fin n) (Fin n) E) ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    (factorIdem e i).rank = Module.finrank E (E ⊗[F] K i) := by
  obtain ⟨-, -, -, ⟨v, hv⟩, -⟩ := hA
  obtain ⟨-, -, hbij⟩ := hP
  let L := genAlg (γ : Matrix (Fin n) (Fin n) E)
  let P := plusAlg σ J (γ : Matrix (Fin n) (Fin n) E)
  let φ : L →ₗ[E] (Fin n → E) :=
    { toFun := fun l => (l : Matrix (Fin n) (Fin n) E) *ᵥ v
      map_add' := fun a b => Matrix.add_mulVec _ _ _
      map_smul' := fun c a => Matrix.smul_mulVec _ _ _ }
  let incl : P →ₗ[F] L := P.val.toLinearMap
  let ψ : E ⊗[F] P →ₗ[E] L := LinearMap.liftBaseChange E incl
  let ι : K i →ₗ[F] P := e.symm.toLinearMap ∘ₗ LinearMap.single F K i
  let Φ : E ⊗[F] K i →ₗ[E] (Fin n → E) := φ ∘ₗ ψ ∘ₗ ι.baseChange E
  have hψ : ∀ t, ψ t = plusTensor σ J (γ : Matrix (Fin n) (Fin n) E) (TensorProduct.comm F E P t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
      change ψ 0 = plusTensor σ J (γ : Matrix (Fin n) (Fin n) E) ((TensorProduct.comm F E P).toLinearMap 0)
      rw [map_zero, map_zero, map_zero]
    | tmul a p =>
      simp [ψ, incl, plusTensor, Algebra.TensorProduct.productMap_apply_tmul, Algebra.smul_def, mul_comm]; rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hψb : Function.Bijective ψ := by
    have : (ψ : E ⊗[F] P → L) = plusTensor σ J (γ : Matrix (Fin n) (Fin n) E) ∘ TensorProduct.comm F E P :=
      funext hψ
    rw [this]; exact hbij.comp (TensorProduct.comm F E P).bijective
  have hι : Function.Injective (ι.baseChange E) := by
    have h0 : Function.Injective ι := e.symm.injective.comp (Pi.single_injective i)
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap ι h0
  have hΦ : Function.Injective Φ := hv.1.comp (hψb.1.comp hι)
  have hΦt : ∀ (a : E) (x : K i), Φ (a ⊗ₜ x) =
      a • ((((e.symm (Pi.single i x) : P) : L) : Matrix (Fin n) (Fin n) E) *ᵥ v) := by
    intro a x
    simp [Φ, φ, ψ, ι, incl, LinearMap.liftBaseChange_tmul, Matrix.smul_mulVec]
  have hrange : LinearMap.range Φ = LinearMap.range (factorIdem e i).mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
        refine ⟨a • ((((e.symm (Pi.single i x) : P) : L) : Matrix (Fin n) (Fin n) E) *ᵥ v), ?_⟩
        rw [hΦt, Matrix.mulVecLin_apply, Matrix.mulVec_smul, Matrix.mulVec_mulVec, factorIdem_mul]
        simp
      | add x y hx hy => rw [map_add Φ]; exact add_mem hx hy
    · rintro _ ⟨w, rfl⟩
      obtain ⟨l, rfl⟩ := hv.2 w
      obtain ⟨s, rfl⟩ := hψb.2 l
      change (factorIdem e i).mulVecLin (φ (ψ s)) ∈ LinearMap.range Φ
      induction s using TensorProduct.induction_on with
      | zero => simp [φ]
      | tmul a p =>
        refine ⟨a ⊗ₜ (e p i), ?_⟩
        rw [hΦt]
        simp only [ψ, incl, LinearMap.liftBaseChange_tmul, Matrix.mulVecLin_apply]
        have hc : (((a • (p : L)) : L) : Matrix (Fin n) (Fin n) E) = a • ((p : L) : Matrix (Fin n) (Fin n) E) := rfl
        change _ = factorIdem e i *ᵥ ((((a • (p : L)) : L) : Matrix (Fin n) (Fin n) E) *ᵥ v)
        rw [hc, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, factorIdem_mul]
      | add x y hx hy =>
        rw [map_add (f := _), map_add (f := _), map_add (f := _)]; exact add_mem hx hy
  rw [← Matrix.finrank_range_mulVecLin, ← hrange, LinearMap.finrank_range_of_inj hΦ]

end GlobalTheory.FactorSplit

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt Formalism.UG Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E}
  {J : Matrix (Fin n) (Fin n) E} {γ : Matrix (Fin n) (Fin n) E} {k : ℕ} {K : Fin k → Type}
  [∀ i, Field (K i)] [∀ i, Algebra F (K i)]

theorem eq_zero_of_mulVec {M : Matrix (Fin n) (Fin n) E} (h : ∀ w, M *ᵥ w = 0) : M = 0 := by
  ext a b
  have := congrFun (h (Pi.single b 1)) a
  simpa [Matrix.mulVec_single_one] using this

theorem rank_pos_of_ne_zero {M : Matrix (Fin n) (Fin n) E} (hM : M ≠ 0) : 0 < M.rank := by
  refine Nat.pos_of_ne_zero fun h => hM (eq_zero_of_mulVec fun w => ?_)
  rw [← Matrix.finrank_range_mulVecLin, Submodule.finrank_eq_zero] at h
  have : M.mulVecLin w ∈ LinearMap.range M.mulVecLin := ⟨w, rfl⟩
  rw [h] at this
  exact (Submodule.mem_bot E).1 this

theorem eq_one_of_idem_rank {M : Matrix (Fin n) (Fin n) E} (hM : M * M = M) (hr : M.rank = n) : M = 1 := by
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Matrix.finrank_range_mulVecLin, hr, Module.finrank_fin_fun]
  have hu : ∀ u, M *ᵥ u = u := by
    intro u
    obtain ⟨w, hw⟩ : u ∈ LinearMap.range M.mulVecLin := htop ▸ Submodule.mem_top
    rw [← hw, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hM]
  have h0 := eq_zero_of_mulVec (M := M - 1) fun w => by rw [Matrix.sub_mulVec, hu, Matrix.one_mulVec, sub_self]
  exact sub_eq_zero.1 h0

theorem two_le_of_decomp {P : Type} [CommRing P] [Algebra F P] {k' : ℕ} {K' : Fin k' → Type}
    [∀ i, Field (K' i)] [∀ i, Algebra F (K' i)] (e' : P ≃ₐ[F] ∀ i, K' i) (hk' : 2 ≤ k')
    (e : P ≃ₐ[F] ∀ i, K i) (i : Fin k) : ∃ j, j ≠ i := by
  by_contra hne
  simp only [not_exists, ne_eq, not_not] at hne
  let a : Fin k' := ⟨0, by omega⟩
  let b : Fin k' := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  let q : P := e'.symm (Pi.single a 1)
  have hqq : q * q = q := by
    apply e'.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, ← Pi.single_mul, one_mul]
  have hq : IsIdempotentElem (e q i) := by
    show e q i * e q i = e q i
    rw [← Pi.mul_apply, ← map_mul, hqq]
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 hq with h | h
  · have : e q = 0 := funext fun j => by rw [hne j]; exact h
    have h2 := congrFun (e'.symm_apply_eq.1 (e.map_eq_zero_iff.1 this)) a
    simp at h2
  · have : e q = 1 := funext fun j => by rw [hne j]; exact h
    have h1 : q = 1 := by rw [← map_one e] at this; exact e.injective this
    have h2 := congrFun (e'.symm_apply_eq.1 h1) b
    simp [Pi.single_apply, hab.symm] at h2

theorem factorIdem_ne_one (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) (hj : ∃ j, j ≠ i) :
    factorIdem e i ≠ 1 := by
  intro h
  obtain ⟨j, hj⟩ := hj
  have h1 : e.symm (Pi.single i 1) = 1 := Subtype.ext (Subtype.ext h)
  have h2 := congrFun (e.symm_apply_eq.1 h1) j
  simp [Pi.single_apply, hj] at h2

end GlobalTheory.FactorSplit

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt

theorem factorIdem_orthSplit_rank : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → ∀ (k : ℕ) (Kf : Fin k → Type) [∀ i, Field (Kf i)] [∀ i, Algebra D.host.F (Kf i)] (e : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg D.sp.cm.sig V.gram γ.1.1 ≃ₐ[D.host.F] ∀ i, Kf i) (i : Fin k), GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsOrthSplit D.sp.cm.sig V.gram γ.1.1 (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i).rank = Module.finrank D.host.E (TensorProduct D.host.F D.host.E (Kf i)) := by
  intro hRS D V γ hss k Kf _ _ e i hnf
  have hreg := GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS γ hss
  obtain ⟨hA, hP, -⟩ := hRS.1 D.host.F D.host.E (Fin V.rank) D.sp.cm.sig V.gram γ.1 hreg
  obtain ⟨-, k', K', _, _, ⟨e'⟩, hk', -⟩ := hnf
  have hj := two_le_of_decomp e' hk' e i
  refine ⟨⟨factorIdem_mul_self e i, factorIdem_selfAdj e i, factorIdem_orth e i, factorIdem_comm e i,
    rank_pos_of_ne_zero (factorIdem_ne_zero e i), lt_of_le_of_ne (Matrix.rank_le_width _) fun h =>
      factorIdem_ne_one e i hj (eq_one_of_idem_rank (factorIdem_mul_self e i) h)⟩,
    rank_factorIdem hA hP e i⟩

end GlobalTheory.FactorSplit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfAdjointFactorIdempotentOrthogonalSplittingRaStatement

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

theorem _root_.GlobalTheory.T.selfAdjointFactorIdempotent_orthogonal_splitting_rank : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → ∀ (k : ℕ) (Kf : Fin k → Type) [∀ i, Field (Kf i)] [∀ i, Algebra D.host.F (Kf i)] (e : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg D.sp.cm.sig V.gram γ.1.1 ≃ₐ[D.host.F] ∀ i, Kf i) (i : Fin k), GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsOrthSplit D.sp.cm.sig V.gram γ.1.1 (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i).rank = Module.finrank D.host.E (TensorProduct D.host.F D.host.E (Kf i)) := by
  first | exact @GlobalTheory.FactorSplit.factorIdem_orthSplit_rank | exact GlobalTheory.FactorSplit.factorIdem_orthSplit_rank | (intros; apply GlobalTheory.FactorSplit.factorIdem_orthSplit_rank <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonFieldTypeVanishing

section

@[expose] public section

open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms (plusAlg genAlg)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH NoFixed radical)
open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.NonFieldType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem localClause {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}
    {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ} (hμf : ∀ v, (μf v).IsHaarMeasure) (hf : IsTestFin T U μf ff)
    {γ : GRat D.sp.cm.sig V.gram} (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1) : LocalClause T μf ff γ := by
  intro k K _ _ e i
  obtain ⟨h1, h2⟩ := GlobalTheory.T.selfAdjointFactorIdempotent_orthogonal_splitting_rank GlobalTheory.T.regularSemisimple_unitaryGroup_concrete D V γ hγ.1 k K e i hγ
  refine ⟨h1, h2, fun v hv dt hdt => ?_⟩
  obtain ⟨hee, -, -, hcomm, hpos, hlt⟩ := h1
  have hγε : γ.1.1 * factorIdem e i = factorIdem e i * γ.1.1 :=
    hcomm _ (Algebra.self_mem_adjoin_singleton _ _)
  have h := GlobalTheory.T.weightedOrbitalIntegral_typeTest_vanish GlobalTheory.T.typeIdempotent_constantTerm_vanish D V T U μf ff hf v (hμf v) γ (factorIdem e i) hγ.1 hee hγε hpos hlt hv 1
    continuous_const (fun _ _ _ => rfl) (fun _ _ _ => rfl) dt
  have e1 : (fun x => (1 : GLoc D.sp.cm.sig V.gram v → ℂ) x *
      ff v (x⁻¹ * proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ) * x)) = conjFn (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ)) (ff v) := by
    funext x; exact one_mul _
  rw [e1] at h
  exact h

theorem isMulCommutative_cent_ratEmb {γ : GRat D.sp.cm.sig V.gram} (hγ : IsRegSS γ.1.1) :
    IsMulCommutative (cent (ratEmb D.sp.cm.sig V.gram γ)) := by
  refine ⟨⟨fun x y => Subtype.ext (GAd_ext _ _ (fun w => ?_) fun v => ?_)⟩⟩
  · have h := (isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ w)).is_comm.comm
      (centMap (projArch D.sp.cm.sig V.gram w) _ x) (centMap (projArch D.sp.cm.sig V.gram w) _ y)
    have h' := congrArg Subtype.val h
    simpa [centMap] using h'
  · have h := (isMulCommutative_cent_HA (isRegSS_proj_ratEmb hγ v)).is_comm.comm
      (centMap (proj D.sp.cm.sig V.gram v) _ x) (centMap (proj D.sp.cm.sig V.gram v) _ y)
    have h' := congrArg Subtype.val h
    simpa [centMap] using h'

theorem ratEmb_mem_GQ (γ : GRat D.sp.cm.sig V.gram) : ratEmb D.sp.cm.sig V.gram γ ∈ GQ V := by
  rw [GlobalTheory.AdelicU.GQ_eq, ← GlobalTheory.AdelicU.range_ratEmb]; exact ⟨γ, rfl⟩

theorem covol_lt_top {γ : GRat D.sp.cm.sig V.gram} (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1)
    (dt : Measure (cent (ratEmb D.sp.cm.sig V.gram γ))) [dt.IsHaarMeasure] (𝓣 : Set (cent (ratEmb D.sp.cm.sig V.gram γ)))
    (h𝓣 : IsFundamentalDomain ((GQ V).subgroupOf (cent (ratEmb D.sp.cm.sig V.gram γ))) 𝓣 dt) : dt 𝓣 < ⊤ := by
  obtain ⟨hreg, k, K, iF, iA, he, -, hK⟩ := hγ
  exact GlobalTheory.T.anisotropic_torus_fundamentalDomain_finite_measure GlobalTheory.T.regularSemisimple_unitaryGroup_concrete D V γ hreg k K he hK dt 𝓣 h𝓣


instance discreteTopology_subgroupOf_cent (γ : GA D V) : DiscreteTopology ((GQ V).subgroupOf (cent γ)) :=
  DiscreteTopology.of_continuous_injective (f := fun t : (GQ V).subgroupOf (cent γ) => (⟨t.1.1, t.2⟩ : GQ V))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    (fun s t h => Subtype.ext (Subtype.ext (by have h' := congrArg Subtype.val h; exact h')))


theorem zeroClause {T : TypeDataG V} (hH : HypH (k := fun v : T.S => ResF v.1) T.τ)
    {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}
    {μ : Measure (GA D V)} {fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    {γ : GRat D.sp.cm.sig V.gram} (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1)
    (hL : LocalClause T μf ff γ) (hP : ProductClause μa μf μ fa ff (ratEmb D.sp.cm.sig V.gram γ)) :
    ZeroClause μ (tensor D.sp.cm.sig V.gram fa ff) (ratEmb D.sp.cm.sig V.gram γ) := by
  intro 𝓕 h𝓕
  haveI hla : ∀ w, LocallyCompactSpace (cent (projArch D.sp.cm.sig V.gram w (ratEmb D.sp.cm.sig V.gram γ))) :=
    fun _ => (isClosed_cent _).locallyCompactSpace
  haveI hlf : ∀ v, LocallyCompactSpace (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ))) :=
    fun _ => (isClosed_cent _).locallyCompactSpace
  have hR := restrGroup_cent (frameLat V) (ratEmb D.sp.cm.sig V.gram γ)
  let K0 : ∀ v, TopologicalSpace.PositiveCompacts (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ))) :=
    fun v => ⟨⟨_, hR.isCompact_K v⟩, by
      simp only [(hR.isOpen_K v).interior_eq]; exact ⟨1, one_mem _⟩⟩
  let dta : ∀ w, Measure (cent (projArch D.sp.cm.sig V.gram w (ratEmb D.sp.cm.sig V.gram γ))) := fun _ => Measure.haar
  let dtf : ∀ v, Measure (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ))) :=
    fun v => Measure.haarMeasure (K0 v)
  haveI : ∀ w, (dta w).IsHaarMeasure := fun _ => inferInstance
  haveI : ∀ v, (dtf v).IsHaarMeasure := fun _ => inferInstance
  have h1 : ∀ᶠ v in cofinite, dtf v ((stabLoc D.sp.cm.sig V.gram (frameLat V) v).subgroupOf
      (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ)))) = 1 :=
    .of_forall fun v => Measure.haarMeasure_self (K₀ := K0 v)
  obtain ⟨dt, hdt, -⟩ := existsUnique_isCentProd (L := frameLat V) (ratEmb D.sp.cm.sig V.gram γ) dta dtf h1
  have h𝓣 := isFundamentalDomain_stdDom ((GQ V).subgroupOf (cent (ratEmb D.sp.cm.sig V.gram γ))) dt
  obtain ⟨-, oa, ob, -, hob, hone, -, hcls⟩ := hP dta dtf dt hdt _ h𝓣
  obtain ⟨-, k, K, iF, iA, ⟨e⟩, hk, -⟩ := hγ
  obtain ⟨hsplit, -, hloc⟩ := hL k K e ⟨0, by omega⟩
  obtain ⟨v, hv⟩ := hH _ hsplit.2.2.2.2.1 hsplit.2.2.2.2.2
  have h0 := hloc v hv (dtf v.1) inferInstance
  have hob0 : ob v.1 = 0 := (hob v.1).2.symm.trans h0.2
  have hfp : ∏ᶠ v, ob v = 0 := finprod_eq_zero ob v.1 hob0 (Filter.eventually_cofinite.1 hone)
  have h := hcls 𝓕 h𝓕
  rwa [hfp, mul_zero, mul_zero] at h


end GlobalTheory.NonFieldType
end
end
end
