module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMapNablaSqPad
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsStableDisjoint
public import Formalism.RealPlaceAnalysis.FockPairGl
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCassemLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleOuterTprod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDualWeylOfUnitriangularFixed
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairingEquivariantAndNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowDivEqZeroOfMatRepUnipotentFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightMapDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedHomogeneousComponentColWMem
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColAddFixedOfStable

section

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

theorem rename_swap_matRep_one_right {n n' : ℕ} (g : GL (Fin n) ℂ) (v : MvPolynomial (Fin n' × Fin n) ℂ) :
    rename Prod.swap (matRep n n' (g, 1) v) =
      rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ (rename Prod.swap v) := by
  have : (rename (R := ℂ) (Prod.swap : Fin n' × Fin n → Fin n × Fin n')).comp
      (sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (g : Matrix (Fin n) (Fin n) ℂ))ᵀ) =
      (rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ).comp (rename Prod.swap) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [sub, rowAct, Fintype.sum_prod_type, Matrix.one_apply, apply_ite C]
  rw [matRep_apply]
  exact DFunLike.congr_fun this v

theorem rename_swap_colAdd {n n' : ℕ} (l j : Fin n) (c : ℂ) (v : MvPolynomial (Fin n' × Fin n) ℂ) :
    rename Prod.swap (colAdd ℂ l j c v) =
      Polynomial.eval (C c) (rowGen ℂ l j (rename Prod.swap v)) := by
  induction v using MvPolynomial.induction_on with
  | C a => simp [colAdd, rowGen]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, Polynomial.eval_add]
  | mul_X p v hp =>
    obtain ⟨a, s⟩ := v
    simp only [map_mul, hp, Polynomial.eval_mul]
    congr 1
    by_cases h : s = j <;> simp [colAdd, rowGen, h, mul_comm (C c)]

theorem rowGen_coeff_zero_eq {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    (rowGen ℂ a b f).coeff 0 = f := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowGen]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, Polynomial.eval_add]
  | mul_X p v hp =>
    simp only [map_mul, hp, Polynomial.eval_mul]
    congr 1
    by_cases h : v.1 = b <;> simp [rowGen, h]

theorem exists_colAdd_fixed_of_stable (n n' : ℕ) (N : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ)) (hN : N ≠ ⊥)
    (hst : ∀ g : GL (Fin n) ℂ, ∀ v ∈ N, matRep n n' (g, 1) v ∈ N) :
    ∃ v ∈ N, v ≠ 0 ∧ ∀ l j : Fin n, l < j → ∀ c : ℂ, colAdd ℂ l j c v = v := by
  have hinj : Function.Injective
      (rename (R := ℂ) (Prod.swap : Fin n' × Fin n → Fin n × Fin n')) :=
    rename_injective _ Prod.swap_injective
  let M : Submodule ℂ (MvPolynomial (Fin n × Fin n') ℂ) :=
    N.map (rename (R := ℂ) (Prod.swap : Fin n' × Fin n → Fin n × Fin n')).toLinearMap
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, rowAct ℂ u f ∈ M := by
    rintro u hu _ ⟨f, hf, rfl⟩
    let t : Matrix.unitaryGroup (Fin n) ℂ := Matrix.UnitaryGroup.transpose ⟨u, hu⟩
    exact ⟨_, hst (unitaryIncl n t) f hf, rename_swap_matRep_one_right (unitaryIncl n t) f⟩
  have hcl := rowDivClosed_of_rowAct_stable M (rowAct_mem_of_unitary_stable M hU)
  have hne : M ≠ ⊥ := fun e => hN (Submodule.map_injective_of_injective hinj
    (e.trans (Submodule.map_bot _).symm))
  obtain ⟨_, ⟨v, hv, rfl⟩, hv0, hkill⟩ := exists_killed_of_rowDivClosed M hcl hne
  refine ⟨v, hv, fun e => hv0 (by rw [e, map_zero]), fun l j hlj c => hinj ?_⟩
  have hC : rowGen ℂ l j (rename Prod.swap v) = Polynomial.C (rename Prod.swap v) := by
    apply Polynomial.ext
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [rowGen_coeff_zero_eq, Polynomial.coeff_C_zero]
    · rw [Polynomial.coeff_C_of_ne_zero hk.ne']
      exact hkill l j hlj k hk
  rw [rename_swap_colAdd, hC, Polynomial.eval_C]

end GlobalTheory.GLDuality
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericSubmoduleMonomials

section

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.Proof.GenericSubmoduleMonomials

noncomputable def genSub (n n' k : ℕ) : MvPolynomial (Fin n' × Fin k) ℂ →ₐ[ℂ]
    MvPolynomial (Fin n × Fin k) (MvPolynomial (Fin n' × Fin n) ℂ) :=
  aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (X (v.1, t)) * X (t, v.2))

theorem map_eval_genSub (n n' k : ℕ) (x : Matrix (Fin n') (Fin n) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ) :
    map (eval (fun v : Fin n' × Fin n => x v.1 v.2)) (genSub n n' k f) =
      aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ)) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [genSub, aeval_C, aeval_C]
    simp [MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    have hv : map (eval (fun v : Fin n' × Fin n => x v.1 v.2)) (genSub n n' k (X v)) =
        ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ) := by

      rw [genSub, aeval_X, map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_mul, map_C, map_X, eval_X]
    rw [map_mul, map_mul, hp, map_mul, hv, aeval_X]

theorem repr_basisMonomials {σ : Type} (φ : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    (basisMonomials σ ℂ).repr φ m = AddMonoidAlgebra.coeff φ m := rfl

theorem exists_pairing : ∀ (n n' k : ℕ), ∃ T : MvPolynomial (Fin n × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n) ℂ, ∀ (φ : MvPolynomial (Fin n × Fin k) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ) (x : Matrix (Fin n') (Fin n) ℂ), eval (fun v => x v.1 v.2) (T φ f) = fockF φ (map (starRingEnd ℂ) (aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ)) f)) := by
  intro n n' k
  refine ⟨(basisMonomials (Fin n × Fin k) ℂ).constr ℂ (fun m => ((∏ j ∈ m.support, (m j).factorial : ℕ) : ℂ) •
    (((lcoeff (MvPolynomial (Fin n' × Fin n) ℂ) m).restrictScalars ℂ) ∘ₗ (genSub n n' k).toLinearMap)), ?_⟩
  intro φ f x
  have hs : ((basisMonomials (Fin n × Fin k) ℂ).repr φ).support = φ.support := by
    ext m
    rw [Finsupp.mem_support_iff, repr_basisMonomials, mem_support_iff]

  rw [Module.Basis.constr_apply, Finsupp.sum, hs, fockF, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [repr_basisMonomials, ← map_eval_genSub, coeff_map, coeff_map]
  simp only [LinearMap.smul_apply, smul_eval, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.restrictScalars_apply, lcoeff_apply, starRingEnd_apply, star_star]
  ring

end GlobalTheory.Proof.GenericSubmoduleMonomials
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OuterTensorIntertwiningEqZeroOfLeft

section

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory

theorem tensor_eq_zero_of_forall_contract_right {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (z : V ⊗[ℂ] W)
    (h : ∀ l : Module.Dual ℂ W, TensorProduct.rid ℂ V (LinearMap.lTensor V l z) = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  apply (TensorProduct.equivFinsuppOfBasisRight (M := V) b).injective
  ext i
  simp [TensorProduct.equivFinsuppOfBasisRight_apply, h]

theorem outerTensor_intertwining_eq_zero_of_left :
    ∀ (G H V W V' W' : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (ρ' : Representation ℂ G V') (σ' : Representation ℂ H W'), (∀ ψ : ρ.IntertwiningMap ρ', ψ = 0) → ∀ φ : (Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H)) : Representation ℂ (G × H) (V ⊗[ℂ] W)).IntertwiningMap (Representation.tprod (ρ'.comp (MonoidHom.fst G H)) (σ'.comp (MonoidHom.snd G H)) : Representation ℂ (G × H) (V' ⊗[ℂ] W')), φ = 0 := by
  intro G H V W V' W' _ _ _ _ _ _ _ _ _ _ ρ σ ρ' σ' h φ

  have hpure : ∀ (v : V) (w : W), φ (v ⊗ₜ[ℂ] w) = 0 := by
    intro v w
    apply tensor_eq_zero_of_forall_contract_right
    intro l
    let f : V →ₗ[ℂ] V' :=
      (TensorProduct.rid ℂ V').toLinearMap ∘ₗ LinearMap.lTensor V' l ∘ₗ φ.toLinearMap ∘ₗ
        (TensorProduct.mk ℂ V W).flip w
    have hf : ∀ (g : G) (x : V), f (ρ g x) = ρ' g (f x) := by
      intro g x
      have key : ∀ y : V' ⊗[ℂ] W', TensorProduct.rid ℂ V'
          (LinearMap.lTensor V' l (TensorProduct.map (ρ' g) (σ' 1) y)) =
          ρ' g (TensorProduct.rid ℂ V' (LinearMap.lTensor V' l y)) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a c => simp
        | add a c ha hc => simp only [map_add (f := _), ha, hc]
      have e1 : ρ g x ⊗ₜ[ℂ] w = (Representation.tprod (ρ.comp (MonoidHom.fst G H))
          (σ.comp (MonoidHom.snd G H))) (g, 1) (x ⊗ₜ[ℂ] w) := by
        simp [Representation.tprod_apply]
      have e2 := Representation.IntertwiningMap.isIntertwining _ _ φ (g, 1) (x ⊗ₜ[ℂ] w)
      simp only [f, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
        Representation.IntertwiningMap.toLinearMap_apply, LinearEquiv.coe_coe]
      rw [e1, e2, Representation.tprod_apply]
      exact key _
    have h0 := h (f.intertwiningMap_of_isIntertwiningMap ρ ρ' hf)
    have hv := congrArg (fun ψ : ρ.IntertwiningMap ρ' => ψ v) h0
    simpa [f] using hv
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro v w
  simp [hpure]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqRepTopVecOfUnitriangular

section

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

noncomputable def topVec (r : ℕ) (lam : DomWeight r) : nablaSq ℂ r lam :=
  ⟨extremal ℂ r lam, hwMem ℂ r r le_rfl _ (factNatW r lam).1⟩

theorem sqRep_topVec_of_unitriangular (r : ℕ) (lam : DomWeight r) (g : GL (Fin r) ℂ)
    (h1 : (g : Matrix (Fin r) (Fin r) ℂ).BlockTriangular id) (h2 : ∀ a, (g : Matrix (Fin r) (Fin r) ℂ) a a = 1) :
    sqRep ℂ r lam g (topVec r lam) = topVec r lam :=
  Subtype.ext ((factSqHighestWeight ℂ r lam).2 g h1 h2)

theorem sqRep_topVec_diag {m : ℕ} (r : ℕ) (a : Part m) (t : Fin r → ℂˣ) :
    sqRep ℂ r (pad r a) (diagGL ℂ r t) (topVec r (pad r a)) =
      (∏ i, (t i : ℂ) ^ rowNu (r := r) a.1 i) • topVec r (pad r a) := by
  apply Subtype.ext
  have h := (factSqHighestWeight ℂ r (pad r a)).1 t
  have e : ((∏ i, t i ^ (pad r a).w i : ℂˣ) : ℂ) = ∏ i, (t i : ℂ) ^ rowNu (r := r) a.1 i := by
    simp [pad]
  rw [e] at h
  exact h

theorem exists_intertwining_piece (n n' : ℕ) (a : Part (min n n')) :
    ∃ φ : (pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).IntertwiningMap
      (polyRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ))),
      φ (topVec n (pad n a) ⊗ₜ topVec n' (pad n' a)) ≠ 0 := by
  obtain ⟨T, hT⟩ := GlobalTheory.Proof.GenericSubmoduleMonomials.exists_pairing n n' (min n n')
  obtain ⟨hE, hN⟩ := GlobalTheory.GLDuality.pairing_equivariant_and_ne_zero n n' (min n n') T hT
  obtain ⟨j, hj, hj0⟩ := GlobalTheory.GLDuality.exists_map_nablaSq_pad n (min n n') (min_le_left _ _) a
  obtain ⟨j', hj', hj0'⟩ := GlobalTheory.GLDuality.exists_map_nablaSq_pad n' (min n n') (min_le_right _ _) a
  refine ⟨⟨TensorProduct.lift (T.compl₁₂ j j'), fun p => ?_⟩, ?_⟩
  · apply TensorProduct.ext'
    intro v w
    simp only [LinearMap.comp_apply, pieceRep_tmul, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
    change T (j (sqRep ℂ n _ p.1 v)) (j' (sqRep ℂ n' _ p.2 w)) = matRep n n' (p.1, p.2) (T (j v) (j' w))
    rw [hj, hj', hE]
  · change T (j _) (j' _) ≠ 0
    rw [hj0 _ rfl, hj0' _ rfl]
    exact hN _ _ _

theorem map_topVec_highest (n n' : ℕ) (a : Part (min n n'))
    (φ : (pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).IntertwiningMap
      (polyRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)))) :
    φ (topVec n (pad n a) ⊗ₜ topVec n' (pad n' a)) ∈ dualWeyl ℂ n' n (rowNu (r := n) a.1) ∧
      ∀ i j : Fin n', i < j → ∀ k : ℕ, 1 ≤ k →
        rowDiv ℂ i j k (φ (topVec n (pad n a) ⊗ₜ topVec n' (pad n' a))) = 0 := by
  have hφ : ∀ (g : GL (Fin n) ℂ) (h : GL (Fin n') ℂ) v w, matRep n n' (g, h) (φ (v ⊗ₜ w)) =
      φ (sqRep ℂ n _ g v ⊗ₜ sqRep ℂ n' _ h w) := fun g h v w => by
    have := Representation.IntertwiningMap.isIntertwining _ _ φ (g, h) (v ⊗ₜ w)
    rw [pieceRep_tmul] at this
    exact this.symm
  refine ⟨GlobalTheory.GLDuality.mem_dualWeyl_of_unitriangular_fixed n n' _ _ (fun g h1 h2 => ?_) (fun t => ?_), GlobalTheory.GLDuality.rowDiv_eq_zero_of_matRep_unipotent_fixed n n' _ fun g h1 h2 => ?_⟩
  · rw [hφ, sqRep_topVec_of_unitriangular _ _ g h1 h2, map_one, Module.End.one_apply]
  · rw [hφ, sqRep_topVec_diag, map_one, Module.End.one_apply, ← TensorProduct.smul_tmul', map_smul]
  · rw [hφ, sqRep_topVec_of_unitriangular _ _ g h1 h2, map_one, Module.End.one_apply]

theorem colAdd_matRep_diag {n n' : ℕ} (t : Fin n → ℂˣ) (l j : Fin n) (c : ℂ)
    (v : MvPolynomial (Fin n' × Fin n) ℂ) :
    colAdd ℂ l j c (matRep n n' (diagGL ℂ n t, 1) v) =
      matRep n n' (diagGL ℂ n t, 1) (colAdd ℂ l j (c * t j * (t l)⁻¹) v) := by
  have hX : ∀ (a : Fin n') (s : Fin n),
      sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (diagGL ℂ n t : Matrix (Fin n) (Fin n) ℂ))ᵀ
        (X (a, s)) = C (t s : ℂ) * X (a, s) := by
    intro a s
    rw [← matRep_apply, matRep_X]
    simp [diagGL, Matrix.one_apply, Matrix.diagonal_apply, apply_ite C]
  have e : (colAdd ℂ (r := n') l j c).comp
      (sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (diagGL ℂ n t : Matrix (Fin n) (Fin n) ℂ))ᵀ) =
      (sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (diagGL ℂ n t : Matrix (Fin n) (Fin n) ℂ))ᵀ).comp
        (colAdd ℂ l j (c * t j * (t l)⁻¹)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hX]
    by_cases hs : s = j
    · subst hs
      simp only [colAdd, map_mul, algHom_C, aeval_X, if_true, map_add (f := _), hX, algebraMap_eq]
      have : (C ((t l)⁻¹ : ℂ) : MvPolynomial (Fin n' × Fin n) ℂ) * C (t l : ℂ) = 1 := by
        rw [← map_mul]; simp
      simp only [Units.val_inv_eq_inv_val] at this ⊢
      linear_combination (-(C c * C (t s : ℂ) * X (a, l))) * this
    · simp only [colAdd, map_mul, algHom_C, aeval_X, if_neg hs, hX, algebraMap_eq]
  exact DFunLike.congr_fun e v

theorem exists_mem_dualWeyl_of_stable (n n' : ℕ) (N : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ)) (hN : N ≠ ⊥)
    (hst : ∀ g : GL (Fin n) ℂ, ∀ v ∈ N, matRep n n' (g, 1) v ∈ N) :
    ∃ (ν : Fin n → ℕ) (v : MvPolynomial (Fin n' × Fin n) ℂ), v ∈ N ∧ v ≠ 0 ∧ v ∈ dualWeyl ℂ n' n ν := by
  classical
  obtain ⟨v, hv, hv0, hf⟩ := GlobalTheory.GLDuality.exists_colAdd_fixed_of_stable n n' N hN hst
  let M : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ) :=
    { carrier := {w | w ∈ N ∧ ∀ l j : Fin n, l < j → ∀ c : ℂ, colAdd ℂ l j c w = w}
      add_mem' := fun ha hb => ⟨N.add_mem ha.1 hb.1, fun l j h c => by rw [map_add (f := _), ha.2 l j h, hb.2 l j h]⟩
      zero_mem' := ⟨N.zero_mem, fun l j h c => map_zero _⟩
      smul_mem' := fun a _ ha => ⟨N.smul_mem a ha.1, fun l j h c => by rw [map_smul, ha.2 l j h]⟩ }
  have hM : ∀ t : Fin n → ℂˣ, ∀ w ∈ M, matRep n n' (diagGL ℂ n t, 1) w ∈ M := fun t w hw =>
    ⟨hst _ w hw.1, fun l j h c => by rw [colAdd_matRep_diag, hw.2 l j h]⟩
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hv0
  have hw := GlobalTheory.GLDuality.weightedHomogeneousComponent_colW_mem n n' M hM (Finsupp.weight (colW n' n) d) v ⟨hv, hf⟩
  refine ⟨_, _, hw.1, ne_zero_iff.2 ⟨d, ?_⟩, (dualWeylPoint ℂ n' n _ _).2
    ⟨weightedHomogeneousComponent_isWeightedHomogeneous _ _, hw.2⟩⟩
  rwa [coeff_weightedHomogeneousComponent, if_pos rfl]

theorem exists_highest_of_stable (n n' : ℕ) (N : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ)) (hN : N ≠ ⊥)
    (hst : ∀ p : GL (Fin n) ℂ × GL (Fin n') ℂ, ∀ v ∈ N, matRep n n' p v ∈ N) :
    ∃ (ν : Fin n → ℕ) (v : MvPolynomial (Fin n' × Fin n) ℂ), v ∈ N ∧ v ≠ 0 ∧ v ∈ dualWeyl ℂ n' n ν ∧
      ∀ i j : Fin n', i < j → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ i j k v = 0 := by
  obtain ⟨ν, v, hv, hv0, hvd⟩ := exists_mem_dualWeyl_of_stable n n' N hN fun g => hst (g, 1)
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n') ℂ, ∀ f ∈ N ⊓ dualWeyl ℂ n' n ν,
      rowAct ℂ u f ∈ N ⊓ dualWeyl ℂ n' n ν := by
    intro u hu f hf
    refine ⟨?_, dualWeylRowStable ℂ n' n ν u f hf.2⟩
    have h1 := hst (1, unitaryIncl n' (Matrix.UnitaryGroup.transpose ⟨u, hu⟩)) f hf.1
    rw [matRep_one_left] at h1
    exact h1
  obtain ⟨w, hw, hw0, hk⟩ := exists_killed_of_rowDivClosed _
    (rowDivClosed_of_rowAct_stable _ (rowAct_mem_of_unitary_stable _ hU))
    (fun e => hv0 ((Submodule.eq_bot_iff _).1 e v ⟨hv, hvd⟩))
  exact ⟨ν, w, hw.1, hw0, hw.2, hk⟩

theorem nonempty_equiv_polyRep (n n' : ℕ) :
    Nonempty ((Representation.directSum fun a : Part (min n n') =>
      pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).Equiv
        (polyRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)))) := by
  classical
  have h1 := irreducibleDistinct_gl (min_le_left n n')
  have h2 := irreducibleDistinct_gl (min_le_right n n')
  have hirr : ∀ a : Part (min n n'),
      (pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).IsIrreducible :=
    fun a => GlobalTheory.OuterTensor.isIrreducible_outer_tprod _ _ _ _ _ _ (h1.1 a) (h2.1 a)
  have hdis : ∀ a b : Part (min n n'), a ≠ b →
      ∀ φ : (pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).IntertwiningMap
        (pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) b), φ = 0 := by
    intro a b hab
    refine GlobalTheory.outerTensor_intertwining_eq_zero_of_left _ _ _ _ _ _ _ _ _ _ fun ψ => ?_
    have := h1.1 a
    have := h1.1 b
    refine (Representation.IsIrreducible.bijective_or_eq_zero ψ).resolve_left fun hb => hab (h1.2 a b ?_)
    exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective ψ.toLinearMap hb) ψ.isIntertwining'⟩
  choose φ hφ using exists_intertwining_piece n n'
  let Φ : (Representation.directSum fun a : Part (min n n') =>
      pieceRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ)) a).IntertwiningMap
        (polyRep (MonoidHom.id (GL (Fin n) ℂ)) (MonoidHom.id (GL (Fin n') ℂ))) :=
    ⟨DirectSum.toModule ℂ _ _ (fun i => (φ i).toLinearMap), fun g => by
      refine DirectSum.linearMap_ext ℂ fun i => LinearMap.ext fun v => ?_
      simp [(φ i).isIntertwining]⟩
  have hΦ : ∀ i v, Φ (DirectSum.lof ℂ _ _ i v) = φ i v := fun i v =>
    DirectSum.toModule_lof ℂ (φ := fun i => (φ i).toLinearMap) i v
  have hinj : Function.Injective Φ.toLinearMap := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    refine GlobalTheory.directSum_eq_zero_of_toModule_eq_zero _ _ hirr hdis Φ ?_ (DFinsupp.support x) x
      (fun j hj => DFinsupp.notMem_support_iff.1 hj) hx
    intro i v hv
    have := hirr i
    have hi := (Representation.IsIrreducible.injective_or_eq_zero (φ i)).resolve_right
      (fun e => hφ i (by rw [e]; rfl))
    apply hi
    rw [← hΦ, hv, map_zero]
  have hsurj : Function.Surjective Φ.toLinearMap := by
    rw [← LinearMap.range_eq_top]
    by_contra hM
    obtain ⟨N, hN, hNM, hst⟩ := GlobalTheory.GLDuality.Compl.exists_stable_disjoint n n' _ hM (by
      rintro p _ ⟨x, rfl⟩
      exact ⟨_, Representation.IntertwiningMap.isIntertwining _ _ Φ p x⟩)
    obtain ⟨ν, v, hv, hv0, hvd, hk⟩ := exists_highest_of_stable n n' N hN hst
    obtain ⟨a, rfl⟩ := (GlobalTheory.GLDuality.HighestLine.highest_line n' n ν v hvd hk hv0).1
    obtain ⟨ht1, ht2⟩ := map_topVec_highest n n' a (φ a)
    obtain ⟨c, hc⟩ := (GlobalTheory.GLDuality.HighestLine.highest_line n' n _ _ ht1 ht2 (hφ a)).2 v hvd hk
    refine hv0 ((Submodule.eq_bot_iff _).1 hNM v ⟨hv, ?_⟩)
    rw [hc]
    exact Submodule.smul_mem _ _ ⟨_, hΦ a _⟩
  exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective Φ.toLinearMap ⟨hinj, hsurj⟩) Φ.isIntertwining'⟩

end GlobalTheory.GLDuality

theorem GlobalTheory.Published.glHoweDuality_holds : GlobalTheory.Published.GLHoweDuality :=
  GlobalTheory.Published.glHoweDuality_of_equiv fun n n' _ _ => GlobalTheory.GLDuality.nonempty_equiv_polyRep n n'
end
end
