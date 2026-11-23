module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameReflTransGenCyclicChain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedQuasiLogBasisPDivGroupLieDualStatement
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Data.Matrix.Block
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftQuasiLogarithmAlongPdThickening
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentLinearKillsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentOfQuasiLogarithmStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisLiftPdThickening
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorQuasiLogarithmOfCongruentCombinatioStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisOfBlockLowerTriangularInv

section

@[expose] public section

namespace GlobalTheory

open Matrix

theorem exists_basis_of_blockLowerTriangular_inv (O M : Type) [CommRing O] [AddCommGroup M] [Module O M]
    (d k k' : ℕ) (lbs : Module.Basis (Fin k') O M)
    (P : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k') O) (P' : Matrix (Fin d ⊕ Fin k') (Fin d ⊕ Fin k) O)
    (h1 : P * P' = 1) (h2 : P' * P = 1) (hz : ∀ i j, P (Sum.inl i) (Sum.inr j) = 0) :
    ∃ lb : Module.Basis (Fin k) O M, ∀ j, lb j = ∑ j', P (Sum.inr j) (Sum.inr j') • lbs j' := by
  have hAA : P.toBlocks₁₁ * P'.toBlocks₁₁ = 1 := by
    ext i i'
    have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inl i')
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₁₁] using this
  have hA'A : P'.toBlocks₁₁ * P.toBlocks₁₁ = 1 := mul_eq_one_comm.mp hAA
  have hAB : P.toBlocks₁₁ * P'.toBlocks₁₂ = 0 := by
    ext i j
    have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inr j)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂] using this
  have hB : P'.toBlocks₁₂ = 0 := by
    calc P'.toBlocks₁₂ = (P'.toBlocks₁₁ * P.toBlocks₁₁) * P'.toBlocks₁₂ := by rw [hA'A, Matrix.one_mul]
      _ = P'.toBlocks₁₁ * (P.toBlocks₁₁ * P'.toBlocks₁₂) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hAB, Matrix.mul_zero]
  have hb : ∀ a j, P' (Sum.inl a) (Sum.inr j) = 0 := fun a j => by
    simpa [Matrix.toBlocks₁₂] using congrFun (congrFun hB a) j
  have hDD : P.toBlocks₂₂ * P'.toBlocks₂₂ = 1 := by
    ext j j2
    have := congrFun (congrFun h1 (Sum.inr j)) (Sum.inr j2)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hb, Matrix.one_apply, Matrix.toBlocks₂₂] using this
  have hD'D : P'.toBlocks₂₂ * P.toBlocks₂₂ = 1 := by
    ext j j2
    have := congrFun (congrFun h2 (Sum.inr j)) (Sum.inr j2)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₂₂] using this
  set D := P.toBlocks₂₂ with hDdef
  set D' := P'.toBlocks₂₂
  let L : (Fin k → O) ≃ₗ[O] (Fin k' → O) :=
    LinearEquiv.ofLinear (Matrix.toLin' Dᵀ) (Matrix.toLin' D'ᵀ)
      (by rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, hD'D, Matrix.transpose_one, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, hDD, Matrix.transpose_one, Matrix.toLin'_one])
  refine ⟨Module.Basis.ofEquivFun (lbs.equivFun.trans L.symm), fun j => ?_⟩
  rw [Module.Basis.coe_ofEquivFun]
  simp only [LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, Module.Basis.equivFun_symm_apply]
  refine Finset.sum_congr rfl fun j' _ => ?_
  congr 1
  simp [L, Matrix.mulVec, dotProduct, Pi.single_apply, hDdef, Matrix.toBlocks₂₂]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisOfBlockLowerTriangularInvStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_basis_of_blockLowerTriangular_inv' : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (d k k' : ℕ) (lbs : Module.Basis (Fin k') O M) (P : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k') O) (P' : Matrix (Fin d ⊕ Fin k') (Fin d ⊕ Fin k) O), P * P' = 1 → P' * P = 1 → (∀ i j, P (Sum.inl i) (Sum.inr j) = 0) → ∃ lb : Module.Basis (Fin k) O M, ∀ j, lb j = ∑ j', P (Sum.inr j) (Sum.inr j') • lbs j' := by
  first | exact @GlobalTheory.exists_basis_of_blockLowerTriangular_inv | exact GlobalTheory.exists_basis_of_blockLowerTriangular_inv | (intros; apply GlobalTheory.exists_basis_of_blockLowerTriangular_inv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisTransitionMatricesInverse

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.BasisTrans

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_zero : In (⊤ : Ideal B) (0 : MvPowerSeries σ Q) :=
  fun _ => ⟨0, trivial, by simp⟩

theorem in_add {g h : MvPowerSeries σ Q} (hg : In (⊤ : Ideal B) g) (hh : In (⊤ : Ideal B) h) :
    In (⊤ : Ideal B) (g + h) := fun α => by
  obtain ⟨a, -, ha⟩ := hg α
  obtain ⟨b, -, hb⟩ := hh α
  exact ⟨a + b, trivial, by rw [map_add (f := _), ha, hb, map_add (f := _)]⟩

theorem in_smul (c : B) {g : MvPowerSeries σ Q} (hg : In (⊤ : Ideal B) g) :
    In (⊤ : Ideal B) (algebraMap B Q c • g) := fun α => by
  obtain ⟨a, -, ha⟩ := hg α
  exact ⟨c * a, trivial, by rw [coeff_smul, ha, map_mul]⟩

theorem in_sum {κ : Type} (s : Finset κ) (g : κ → MvPowerSeries σ Q)
    (hg : ∀ j ∈ s, In (⊤ : Ideal B) (g j)) : In (⊤ : Ideal B) (∑ j ∈ s, g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using in_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact in_add (hg a (Finset.mem_insert_self _ _)) (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

theorem comb_one {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → MvPowerSeries σ Q) (i : ι) :
    comb ((1 : Matrix ι ι B) i) e = e i := by
  simp [comb, Matrix.one_apply]

theorem comb_mul {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι → MvPowerSeries σ Q)
    (f : κ → MvPowerSeries σ Q) (P : ι → κ → B) (P' : κ → ι → B) (i : ι) :
    e i - comb ((Matrix.of P * Matrix.of P') i) e =
      (e i - comb (P i) f) + ∑ j, algebraMap B Q (P i j) • (f j - comb (P' j) e) := by

  simp only [comb, Matrix.mul_apply, Matrix.of_apply, smul_sub, Finset.sum_sub_distrib,
  Finset.smul_sum, smul_smul, ← map_mul, map_sum, Finset.sum_smul]
  rw [Finset.sum_comm (f := fun j k => algebraMap B Q (P i j * P' j k) • e k)]
  abel

theorem mul_eq_one {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι κ : Type} [Fintype ι]
    [Fintype κ] [DecidableEq ι] (e : ι → MvPowerSeries (Fin d) Q) (f : κ → MvPowerSeries (Fin d) Q)
    (he : IsBasis μ e) (P : ι → κ → B) (P' : κ → ι → B)
    (h1 : ∀ i, In (⊤ : Ideal B) (e i - comb (P i) f))
    (h2 : ∀ j, In (⊤ : Ideal B) (f j - comb (P' j) e)) :
    Matrix.of P * Matrix.of P' = 1 := by
  funext i
  obtain ⟨b, -, hb⟩ := he.2 (e i) (he.1 i)
  have hA : In (⊤ : Ideal B) (e i - comb ((Matrix.of P * Matrix.of P') i) e) := by
    rw [comb_mul e f P P' i]
    exact in_add (h1 i) (in_sum _ _ fun j _ => in_smul _ (h2 j))
  have hB : In (⊤ : Ideal B) (e i - comb ((1 : Matrix ι ι B) i) e) := by
    rw [comb_one, sub_self]; exact in_zero
  exact (hb _ hA).trans (hb _ hB).symm

theorem trans_inverse : ∀ {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι → MvPowerSeries (Fin d) Q) (f : κ → MvPowerSeries (Fin d) Q), IsBasis μ e → IsBasis μ f → ∀ (P : ι → κ → B) (P' : κ → ι → B), (∀ i, In (⊤ : Ideal B) (e i - comb (P i) f)) → (∀ j, In (⊤ : Ideal B) (f j - comb (P' j) e)) → Matrix.of P * Matrix.of P' = 1 ∧ Matrix.of P' * Matrix.of P = 1 := by
  intro B Q _ _ _ d μ ι κ _ _ _ _ e f he hf P P' h1 h2
  exact ⟨mul_eq_one μ e f he P P' h1 h2, mul_eq_one μ f e hf P' P h2 h1⟩

end GlobalTheory.BasisTrans
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisTransitionMatricesInverseStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.quasiLogarithmBasis_transitionMatrices_inverse : ∀ {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι → MvPowerSeries (Fin d) Q) (f : κ → MvPowerSeries (Fin d) Q), IsBasis μ e → IsBasis μ f → ∀ (P : ι → κ → B) (P' : κ → ι → B), (∀ i, In (⊤ : Ideal B) (e i - comb (P i) f)) → (∀ j, In (⊤ : Ideal B) (f j - comb (P' j) e)) → Matrix.of P * Matrix.of P' = 1 ∧ Matrix.of P' * Matrix.of P = 1 := by
  first | exact @GlobalTheory.BasisTrans.trans_inverse | exact GlobalTheory.BasisTrans.trans_inverse | (intros; apply GlobalTheory.BasisTrans.trans_inverse <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmSecondBlockTangentBasisDualLie

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecondTangent

theorem tangent_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → ∃ lb : Module.Basis (Fin k) O G.dual.Lie, ∀ j, c.IsLie (map Θ (e (Sum.inr j))) (lb j) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hμ k e he hadapt Θ hΘ
  have hF : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  have hμeq : (fun i => map F.θ (μ' i)) = c.μ := funext hμ
  obtain ⟨k', es, lbs, hbs, -, hcobs, hlies⟩ := GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual p C v O hv G d c C hF

  have hlift1 : ∀ m, ∃ f : MvPowerSeries (Fin d) F.Q, QL μ' ⊤ f ∧ map Θ f = es m := by
    intro m
    have hq : QL (fun i => map F.θ (μ' i)) ⊤ (es m) := hμeq ▸ hbs.1 m
    choose b _ hb using hq.2.1
    choose w hw using fun i => F.frame.surj (b i)
    obtain ⟨f, hf, hf', -⟩ := GlobalTheory.QLog.KLift.lift_quasiLog p F.B O F.Q F.θ F.frame d μ' hlift C hF
      Θ hΘ (es m) w hq (fun i => by rw [hb, hw])
    exact ⟨f, hf, hf'⟩
  choose f hfq hfm using hlift1
  have hfb : IsBasis μ' f := by
    refine GlobalTheory.basis_lift p F.B O F.Q F.θ F.frame d μ' hlift C hF Θ hΘ _ f hfq ?_
      (GlobalTheory.BChain.reflTransGen_isStep p C v O hv ε hε F)
    have : (fun i => map Θ (f i)) = es := funext hfm
    rw [this, hμeq]; exact hbs

  choose P hP using fun i => (hfb.2 (e i) (he.1 i)).exists
  choose P' hP' using fun j => (he.2 (f j) (hfq j)).exists
  obtain ⟨h1, h2⟩ := GlobalTheory.T.quasiLogarithmBasis_transitionMatrices_inverse μ' e f he hfb P P' hP hP'

  let Ls : Fin d ⊕ Fin k' → G.dual.Lie := Sum.elim 0 lbs
  have hLs : ∀ m, c.IsLie (es m) (Ls m) := by
    rintro (i | j)
    · obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c C hF (es (Sum.inl i)) (hbs.1 _)
      have := (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c C hF _ _ l l 0 hl hl).2.2 (hcobs i)
      subst this; exact hl
    · exact hlies j
  have hμc : ∀ i, constantCoeff (μ' i) = 0 := hlift.const
  have hg : ∀ i, QL c.μ ⊤ (map Θ (e i)) := fun i => by
    rw [← hμeq]; exact GlobalTheory.SmallSecond.ql_map hΘ μ' hμc (he.1 i)
  have hrow : ∀ i, c.IsLie (map Θ (e i)) (∑ m, F.θ (P i m) • Ls m) := by
    intro i
    refine GlobalTheory.T.tangentVector_quasiLogarithm_of_congruent_combination p C v O hv G d c es (hbs.1) Ls hLs _ (hg i) _ ?_
    intro α
    obtain ⟨b, -, hb⟩ := hP i α
    refine ⟨F.θ b, trivial, ?_⟩
    have : map Θ (e i) - comb (fun m => F.θ (P i m)) es = map Θ (e i - comb (P i) f) := by
      rw [map_sub, GlobalTheory.SmallSecond.map_comb hΘ, funext hfm]
    rw [this, coeff_map, hb, hΘ]

  have hzero : ∀ i j, F.θ (P (Sum.inl i) (Sum.inr j)) = 0 := by
    intro i
    have hc : cob1 (up C c.μ) (map Θ (e (Sum.inl i))) = 0 := by
      rw [← hμeq]; exact GlobalTheory.SmallSecond.formalGroupLawCoboundaryOne_map_eq_zero hΘ μ' hμc (hadapt i).1
    have h0 := (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c C hF _ _ _ _ 0 (hrow (Sum.inl i)) (hrow (Sum.inl i))).2.2 hc
    simp only [Fintype.sum_sum_type, Ls, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, smul_zero,
      Finset.sum_const_zero, zero_add] at h0
    exact (Fintype.linearIndependent_iff.1 lbs.linearIndependent) _ h0
  obtain ⟨lb, hlb⟩ := GlobalTheory.T.exists_basis_of_blockLowerTriangular_inv' O G.dual.Lie d k k' lbs ((Matrix.of P).map F.θ)
    ((Matrix.of P').map F.θ) (by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]) hzero
  refine ⟨lb, fun j => ?_⟩
  have := hrow (Sum.inr j)
  simp only [Fintype.sum_sum_type, Ls, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, smul_zero,
    Finset.sum_const_zero, zero_add] at this
  rw [hlb]; exact this

end GlobalTheory.SmallSecondTangent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmSecondBlockTangentBasisDualLieStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.quasiLogarithm_secondBlock_tangent_basis_dual_lie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → ∃ lb : Module.Basis (Fin k) O G.dual.Lie, ∀ j, c.IsLie (map Θ (e (Sum.inr j))) (lb j) := by
  first | exact @GlobalTheory.SmallSecondTangent.tangent_basis | exact GlobalTheory.SmallSecondTangent.tangent_basis | (intros; apply GlobalTheory.SmallSecondTangent.tangent_basis <;> assumption)
end
end
