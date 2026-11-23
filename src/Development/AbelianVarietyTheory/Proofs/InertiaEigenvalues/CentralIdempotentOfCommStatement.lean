module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.MemTypeSubspaceIffUnipotentCharacter
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTameInertiaElementAtTwistPrime

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulCoeffMem

section

@[expose] public section

open scoped BigOperators

namespace GlobalTheory.CentralIdemIntegral

theorem isIntegral_trace_of_algClosed {L ι : Type} [Field L] [IsAlgClosed L] [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι L) {n : ℕ} (hn : n ≠ 0) (hA : A ^ (n + 1) = A) :
    IsIntegral ℤ A.trace := by
  classical
  rw [Matrix.trace_eq_sum_roots_charpoly]
  refine Multiset.sum_induction (IsIntegral ℤ) _ (fun a b ha hb => ha.add hb) isIntegral_zero ?_
  intro μ hμ

  have hroot := Polynomial.isRoot_of_mem_roots hμ
  rw [Polynomial.IsRoot, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hroot
  have hAv : Matrix.mulVec A v = μ • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]

  have hpowv : ∀ k : ℕ, Matrix.mulVec (A ^ k) v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  have hμpow : μ ^ (n + 1) = μ := by
    have h1 := hpowv (n + 1)
    rw [hA, hAv] at h1
    have h2 : (μ ^ (n + 1) - μ) • v = 0 := by rw [sub_smul, ← h1, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv0

  refine ⟨Polynomial.X ^ (n + 1) - Polynomial.X, Polynomial.monic_X_pow_sub ?_, ?_⟩
  · rw [Polynomial.degree_X]
    exact_mod_cast (show 1 < n + 1 by omega)
  · simp [hμpow]

theorem isIntegral_trace {K ι : Type} [Field K] [CharZero K] [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι K) {n : ℕ} (hn : n ≠ 0) (hA : A ^ (n + 1) = A) :
    IsIntegral ℤ A.trace := by
  classical

  set φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hφ
  have h := isIntegral_trace_of_algClosed (A.map φ) hn (by rw [← Matrix.map_pow, hA])
  rw [← AddMonoidHom.map_trace] at h
  exact (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).1 h

theorem trace_leftMulMatrix {G K : Type} [Group G] [Fintype G] [DecidableEq G] [Field K]
    (x : MonoidAlgebra K G) :
    (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G K)
      (Algebra.lmul K (MonoidAlgebra K G) x)).trace = (Fintype.card G : K) * x.coeff 1 := by

  have hdiag : ∀ g : G, (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G K)
      (Algebra.lmul K (MonoidAlgebra K G) x)) g g = x.coeff 1 := by
    intro g
    rw [LinearMap.toMatrixAlgEquiv_apply]
    change (x * MonoidAlgebra.single g 1).coeff g = x.coeff 1
    rw [MonoidAlgebra.coeff_mul_single_apply, mul_inv_cancel, mul_one]
  rw [Matrix.trace]
  simp only [Matrix.diag, hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem isIntegral_card_mul_coeff {G K : Type} [Group G] [Fintype G] [Field K] [CharZero K]
    (e : MonoidAlgebra K G) (he : e * e = e) (hc : ∀ x, e * x = x * e) (g : G) :
    IsIntegral ℤ ((Fintype.card G : K) * e.coeff g) := by
  classical

  set y : MonoidAlgebra K G := e * MonoidAlgebra.single g⁻¹ 1 with hy
  have hcoeff : y.coeff 1 = e.coeff g := by
    rw [hy, MonoidAlgebra.coeff_mul_single_apply, one_mul, inv_inv, mul_one]
  have hidem : IsIdempotentElem e := he
  have hypow : y ^ (Fintype.card G + 1) = y := by
    rw [hy, (show Commute e (MonoidAlgebra.single g⁻¹ 1) from hc _).mul_pow, hidem.pow_succ_eq,
      MonoidAlgebra.single_pow, one_pow, pow_succ, pow_card_eq_one, one_mul]
  have hM := isIntegral_trace
    (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G K) (Algebra.lmul K (MonoidAlgebra K G) y))
    (n := Fintype.card G) Fintype.card_ne_zero (by rw [← map_pow, ← map_pow, hypow])
  rw [trace_leftMulMatrix, hcoeff] at hM
  exact hM

theorem card_mul_coeff_mem :
    ∀ (G O K : Type) [Group G] [Fintype G] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K] (e : MonoidAlgebra K G), e * e = e → (∀ x, e * x = x * e) → ∀ g, ∃ c : O, algebraMap O K c = (Fintype.card G : K) * e.coeff g := by
  intro G O K _ _ _ _ _ _ _ _ _ e he hc g
  exact (IsIntegrallyClosed.isIntegral_iff (R := O)).1
    (isIntegral_card_mul_coeff e he hc g).tower_top

end GlobalTheory.CentralIdemIntegral
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulCoeffMemStatement

section

@[expose] public section

open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_integral_card_mul_coeff_central_idempotent : ∀ (G O K : Type) [Group G] [Fintype G] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K] (e : MonoidAlgebra K G), e * e = e → (∀ x, e * x = x * e) → ∀ g, ∃ c : O, algebraMap O K c = (Fintype.card G : K) * e.coeff g := by
  first | exact @GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem | exact GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem | (intros; apply GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfComm

section

@[expose] public section

noncomputable section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.IdemAlg

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem card_eq : D.what₂.restRowsFiniteGroupCard = Nat.card (G0g N) := by
  have : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  rw [N.restN_card_levelGroup_eq, Nat.card_pi, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  change _ = ∏ _y : N.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k)))
  rw [Finset.prod_const, Finset.card_univ, N.card_PlG k]

theorem idem_integral (i : X.Tw) (b : Bool) :
    ∃ c : MonoidAlgebra (X.O i) (G0g N),
      MonoidAlgebra.map (algebraMap (X.O i) (FractionRing (X.O i))).toAddMonoidHom c =
        ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • Y.eAlg i b := by
  have : CharZero (FractionRing (X.O0 i)) := charZero_of_injective_ringHom (X.emb0 i).injective
  have : CharZero (X.O0 i) := (algebraMap (X.O0 i) (FractionRing (X.O0 i))).charZero
  have : CharZero (X.O i) := charZero_of_injective_ringHom (X.O_inj i)
  have : CharZero (FractionRing (X.O i)) :=
    charZero_of_injective_ringHom (IsFractionRing.injective (X.O i) (FractionRing (X.O i)))
  have hc := card_eq (N := N)
  have : Finite (G0g N) := Nat.finite_of_card_ne_zero (hc ▸ D.what₂.restRowsFiniteGroupCard_pos.ne')
  let : Fintype (G0g N) := Fintype.ofFinite _
  choose c hcc using GlobalTheory.T.exists_integral_card_mul_coeff_central_idempotent (G0g N) (X.O i) (FractionRing (X.O i)) (Y.eAlg i b) (Y.eAlg_idem i b)
    (Y.eAlg_central i b)
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c), ?_⟩
  ext g
  rw [hc, Nat.card_eq_fintype_card]
  simp [hcc]

theorem admALG_of_commG : ∀ D : D7, CommG D → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp := fun D h =>
  (GlobalTheory.TwistInputsTest.admissibleGoodIdempotent_iff_reduced D.nexp).2 fun i hi b => ⟨idem_integral D.nexp i b, h i hi b⟩

end GlobalTheory.IdemAlg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfCommStatement

section

@[expose] public section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.admALG_of_commG_var : ∀ D : D7, CommG D → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp := by
  first | exact @GlobalTheory.IdemAlg.admALG_of_commG | exact GlobalTheory.IdemAlg.admALG_of_commG | (intros; apply GlobalTheory.IdemAlg.admALG_of_commG <;> assumption)
end
end
