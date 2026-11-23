module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.LevelModule
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MSplitDefs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.LevelModule
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.Msp

section

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.msp :
    ∀ (O B κ : Type) [CommRing O] [CommRing B] [Algebra O B] [Fintype κ] (n : ℕ) (x : B →ₐ[O] O) (P : κ → Polynomial B) (α : κ → Fin n → O), (∀ j, (P j).map (x : B →+* O) = ∏ i, (Polynomial.X - Polynomial.C (α j i))) → ∀ a : MvPolynomial (κ × Fin n) B, MvPolynomial.eval₂ (x : B →+* O) (fun p => α p.1 p.2) a = 0 → Ideal.Quotient.mk (mSplitIdeal P n) ((∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) * a) ∈ (RingHom.ker x).map (algebraMap B (MSplitAlg P n)) := by
  intro O B κ _ _ _ _ n x P α hP a ha
  classical
  set J : Ideal (MSplitAlg P n) := (RingHom.ker x).map (algebraMap B (MSplitAlg P n)) with hJ
  let ψ : MvPolynomial (κ × Fin n) B →+* (MSplitAlg P n ⧸ J) :=
    (Ideal.Quotient.mk J).comp (Ideal.Quotient.mk (mSplitIdeal P n))
  let g : B →+* (MSplitAlg P n ⧸ J) := ψ.comp MvPolynomial.C
  let h : O →+* (MSplitAlg P n ⧸ J) := g.comp (algebraMap O B)
  have hg : ∀ b : B, g b = (Ideal.Quotient.mk J) (algebraMap B (MSplitAlg P n) b) := by
    intro b
    show (Ideal.Quotient.mk J) ((Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.C b)) = _
    rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
  have hgx : g = h.comp (x : B →+* O) := by
    ext b
    show g b = g (algebraMap O B (x b))
    rw [← sub_eq_zero, ← map_sub, hg, Ideal.Quotient.eq_zero_iff_mem]
    apply Ideal.mem_map_of_mem
    rw [RingHom.mem_ker]
    simp
  have hg' : (Ideal.Quotient.mk J).comp (algebraMap B (MSplitAlg P n)) = h.comp (x : B →+* O) := by
    rw [← hgx]
    ext b
    exact (hg b).symm
  have hroot : ∀ j i, ∏ k, (ψ (MvPolynomial.X (j, i)) - h (α j k)) = 0 := by
    intro j i
    have e := MSplitAlg.prod_root P n j
    have e2 := congrArg (fun q => Polynomial.eval (ψ (MvPolynomial.X (j, i))) (q.map (Ideal.Quotient.mk J))) e
    rw [Polynomial.map_map, hg', ← Polynomial.map_map, hP j] at e2
    simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at e2
    rw [← e2]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  have hh : ∀ c : O, ψ (MvPolynomial.C (algebraMap O B c)) = h c := fun _ => rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change ψ (_ * a) = 0
  rw [map_mul]
  set δ := ψ (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
    (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) with hδ
  have hδX : ∀ p : κ × Fin n, δ * (ψ (MvPolynomial.X p) - h (α p.1 p.2)) = 0 := by
    rintro ⟨j, i⟩
    obtain ⟨q, hq⟩ : (∏ k ∈ Finset.univ.erase i,
        (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k))) : MvPolynomial (κ × Fin n) B) ∣
        ∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k))) :=
      (Finset.dvd_prod_of_mem (fun i => ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) (Finset.mem_univ i)).trans
        (Finset.dvd_prod_of_mem (fun j => ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) (Finset.mem_univ j))
    rw [hδ, hq, map_mul, mul_right_comm]
    simp only [map_prod, map_sub, hh]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i), hroot, zero_mul]
  have key : ∀ b : MvPolynomial (κ × Fin n) B,
      δ * (ψ b - h (MvPolynomial.eval₂ (x : B →+* O) (fun p => α p.1 p.2) b)) = 0 := by
    intro b
    refine MvPolynomial.induction_on
      (motive := fun b => δ * (ψ b - h (MvPolynomial.eval₂ (x : B →+* O) (fun p => α p.1 p.2) b)) = 0)
      b ?_ ?_ ?_
    · intro c
      have hc : ψ (MvPolynomial.C c) = h ((x : B →+* O) c) := by
        show g c = _
        rw [hgx]
        rfl
      rw [MvPolynomial.eval₂_C, hc, sub_self, mul_zero]
    · intro p q hp hq
      rw [map_add (f := _), MvPolynomial.eval₂_add, map_add (f := _)]
      linear_combination hp + hq
    · intro p v hp
      rw [map_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul]
      beta_reduce
      linear_combination (ψ (MvPolynomial.X v)) * hp +
        h (MvPolynomial.eval₂ (x : B →+* O) (fun p => α p.1 p.2) p) * hδX v
  have hk := key a
  rw [ha, map_zero, sub_zero] at hk
  exact hk
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.ImportsTer

section

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.kill :
    ∀ (O R B M V : Type) [CommRing O] [CommRing R] [CommRing B] [Algebra O R] [Algebra O B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →ₐ[O] B) (x : B →ₐ[O] O) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (f : PU R q n) (α : Fin q → Fin n → O) (I : Ideal R) (t₀ : R), Function.Surjective β → TwoMaps (M := M) β.toRingHom P act f → (∀ j, (P j).map (x : B →+* O) = ∏ i, (Polynomial.X - Polynomial.C (α j i))) → (∀ a : B, x a = 0 → ∀ m : M, (β t₀ * a) • m ∈ (I.map β • ⊤ : Submodule B M)) → ∀ a : PU R q n, MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) a = 0 → ∀ v : V, act (MvPolynomial.C t₀ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))) * f * a) v ∈ (I • ⊤ : Submodule R V) := by
  intro O R B M V _ _ _ _ _ _ _ _ _ q n β x P act f α I t₀ hβ hTM hP hker a ha v
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := hTM
  have hπC : ∀ b : B, (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.C b) =
      algebraMap B (MSplitAlg P n) b := fun b => rfl
  have key : ∀ i ∈ I, ∀ w : MSplitAlg P n ⊗[B] M, φ ((β i) • w) ∈ (I • ⊤ : Submodule R V) := by
    intro i hi w
    have e1 : (β i) • w = (Ideal.Quotient.mk (mSplitIdeal P n))
        ((MvPolynomial.map β.toRingHom) (MvPolynomial.C i)) • w := by
      rw [MvPolynomial.map_C, hπC, algebraMap_smul]
      rfl
    rw [e1, h1, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply]
    exact Submodule.smul_mem_smul hi trivial
  have claim : ∀ b : B, x b = 0 → ∀ z : MSplitAlg P n ⊗[B] M,
      φ (algebraMap B (MSplitAlg P n) (β t₀ * b) • z) ∈ (I • ⊤ : Submodule R V) := by
    intro b hb z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      rw [algebraMap_smul, ← TensorProduct.tmul_smul]
      refine Submodule.smul_induction_on (p := fun y => φ (s ⊗ₜ[B] y) ∈ (I • ⊤ : Submodule R V))
        (hker b hb m) ?_ ?_
      · intro r hr m' _
        obtain ⟨i, hi, rfl⟩ := (Ideal.mem_map_iff_of_surjective β hβ).mp hr
        rw [TensorProduct.tmul_smul]
        exact key i hi _
      · intro y1 y2 k1 k2
        rw [TensorProduct.tmul_add, map_add (f := _)]
        exact add_mem k1 k2
    | add z1 z2 k1 k2 =>
      rw [smul_add, map_add (f := _)]
      exact add_mem k1 k2
  have gen : ∀ y ∈ Ideal.map (algebraMap B (MSplitAlg P n)) (RingHom.ker x), ∀ z : MSplitAlg P n ⊗[B] M,
      φ ((algebraMap B (MSplitAlg P n) (β t₀) * y) • z) ∈ (I • ⊤ : Submodule R V) := by
    intro y hy
    unfold Ideal.map at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      intro z
      rw [← map_mul]
      exact claim b (RingHom.mem_ker.mp hb) z
    | zero => intro z; simp
    | add y1 y2 _ _ k1 k2 =>
      intro z
      rw [mul_add, add_smul, map_add (f := _)]
      exact add_mem (k1 z) (k2 z)
    | smul r y _ k =>
      intro z
      rw [smul_eq_mul, mul_left_comm, mul_comm r, mul_smul]
      exact k _
  have hE : MvPolynomial.map β.toRingHom (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
      (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k))) : PU R q n) =
      ∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
      (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k))) := by
    simp [map_prod]
  have hmem := Sp.msp O B (Fin q) n x P α hP (MvPolynomial.map β.toRingHom a)
    (by rw [MvPolynomial.eval₂_map]; exact ha)
  have e3 : act (MvPolynomial.C t₀ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
      (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))) * f * a) v =
      φ (((Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom (MvPolynomial.C t₀ *
        (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))))) *
        (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom a)) • ψ v) := by
    rw [mul_smul, ← h2, h1, h3]
    simp only [map_mul, Module.End.mul_apply]
  rw [e3]
  have e4 : (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom (MvPolynomial.C t₀ *
        (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))))) *
        (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom a) =
      algebraMap B (MSplitAlg P n) (β t₀) * (Ideal.Quotient.mk (mSplitIdeal P n))
        ((∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) *
          MvPolynomial.map β.toRingHom a) := by
    rw [map_mul (MvPolynomial.map β.toRingHom), hE, MvPolynomial.map_C, ← hπC, ← map_mul, ← map_mul,
      mul_assoc]
    rfl
  rw [e4]
  exact gen _ hmem _
end
end
