module

public import Formalism.RealPlaceAnalysis.StatementE
public import GroundTheory.AutomorphicForms.HarishChandraCentre.MemCenterOfCommuteE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HarishChandraProjQuantumDetEqProd
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Polynomial.Vieta
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import GroundTheory.AutomorphicForms.HarishChandraCentre

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricSubalgebraLeAdjoinRangeProdCAddXComplex

section

@[expose] public section

open MvPolynomial in
theorem UpperTheory.symmetricSubalgebra_le_adjoin_range_prod_C_add_X_complex :
    ∀ n : ℕ, MvPolynomial.symmetricSubalgebra (Fin n) ℂ ≤ Algebra.adjoin ℂ (Set.range fun u : ℂ => ∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k : MvPolynomial (Fin n) ℂ)) := by
  intro n
  set S := Algebra.adjoin ℂ (Set.range fun u : ℂ => ∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k : MvPolynomial (Fin n) ℂ)) with hS
  have hv : ∀ u : ℂ, ∏ k : Fin n, (C u + X k : MvPolynomial (Fin n) ℂ)
      = ∑ j ∈ Finset.range (n + 1), u ^ (n - j) • esymm (Fin n) ℂ j := by
    intro u
    have h := congrArg (Polynomial.eval (C u : MvPolynomial (Fin n) ℂ))
      (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ (Fin n))
    simp only [Polynomial.eval_prod, Polynomial.eval_finsetSum, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow, Fintype.card_fin] at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_C_mul, map_pow, mul_comm]
  have he : ∀ j, j < n + 1 → esymm (Fin n) ℂ j ∈ S := by
    intro j hj
    by_contra hc
    obtain ⟨φ, hφ, h0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (p := Subalgebra.toSubmodule S) hc inferInstance
    have h1 : ∀ x ∈ S, φ x = 0 := fun x hx => (Submodule.eq_bot_iff _).1 h0 _ ⟨x, hx, rfl⟩
    have hp : (∑ i ∈ Finset.range (n + 1), Polynomial.monomial (n - i) (φ (esymm (Fin n) ℂ i))) = 0 := by
      apply Polynomial.funext
      intro u
      have h2 := h1 _ (Algebra.subset_adjoin ⟨u, rfl⟩)

      simp only [hv, map_sum, map_smul, smul_eq_mul] at h2
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]
      rw [← h2]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h3 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p (n - j)) hp
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at h3
    rw [Finset.sum_eq_single j] at h3
    · exact hφ (by simpa using h3)
    · intro b hb hbj
      rw [Finset.mem_range] at hb
      exact Finsupp.single_eq_of_ne (by omega)
    · intro h
      exact absurd (Finset.mem_range.2 hj) h
  intro p hp
  obtain ⟨q, hq⟩ := (esymmAlgHom_fin_bijective ℂ n).2 ⟨p, hp⟩
  have hq' : p = aeval (fun i : Fin n => esymm (Fin n) ℂ (i + 1)) q := by
    rw [← esymmAlgHom_apply, hq]
  rw [hq']
  have : Algebra.adjoin ℂ (Set.range fun i : Fin n => esymm (Fin n) ℂ (i + 1)) ≤ S :=
    Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact he _ (by have := i.2; omega))
  apply this
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨q, rfl⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CenterEnvelopingGLLeAdjoinQuantumDet

section

@[expose] public section

open GroundTheory.Automorphic.HarishChandra in
private theorem qdet_mem_center (n : ℕ) (u : ℂ) :
    Formalism.REAL.qdet (fun i j : Fin n => e (i, j)) u ∈ Subalgebra.center ℂ (U n) := by
  have hgl : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j)) := by
    intro i j k l
    exact e_mul_sub_mul (i, j) (k, l)
  refine mem_center_of_commute_e fun a => ?_
  exact (Formalism.REAL.qDetCentral (U n) n _ hgl u a.1 a.2).symm

open GroundTheory.Automorphic.HarishChandra in
private theorem hc_qdet (n : ℕ) (u : ℂ) :
    harishChandraHom (⟨_, qdet_mem_center n (u + ((n : ℂ) - 1) / 2)⟩ : Subalgebra.center ℂ (U n)) =
      ∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k : MvPolynomial (Fin n) ℂ) := by
  rw [harishChandraHom_apply]
  dsimp only
  rw [UpperTheory.harishChandraProj_quantumDet_eq_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold GroundTheory.Automorphic.HarishChandra.translate
  rw [map_add (f := _), MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq,
    add_comm (MvPolynomial.X k), ← add_assoc, ← map_add]
  congr 2
  simp only [rhoVec, Pi.neg_apply]
  ring

theorem UpperTheory.center_envelopingGL_le_adjoin_quantumDet :
    ∀ n : ℕ, Subalgebra.center ℂ (GroundTheory.Automorphic.HarishChandra.U n) ≤ Algebra.adjoin ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet (fun i j : Fin n => GroundTheory.Automorphic.HarishChandra.e (i, j)) u) := by
  intro n z hz
  open GroundTheory.Automorphic.HarishChandra in
  let A : Subalgebra ℂ (Subalgebra.center ℂ (U n)) :=
    Algebra.adjoin ℂ (Set.range fun u : ℂ => ⟨_, qdet_mem_center n u⟩)
  have hle : MvPolynomial.symmetricSubalgebra (Fin n) ℂ ≤
      A.map GroundTheory.Automorphic.HarishChandra.harishChandraHom := by
    refine (UpperTheory.symmetricSubalgebra_le_adjoin_range_prod_C_add_X_complex n).trans (Algebra.adjoin_le ?_)
    rintro _ ⟨u, rfl⟩
    exact ⟨_, Algebra.subset_adjoin ⟨_, rfl⟩, hc_qdet n u⟩
  obtain ⟨a, ha, hae⟩ :=
    hle (GroundTheory.Automorphic.HarishChandra.harishChandraHom_mem_symmetricSubalgebra ⟨z, hz⟩)
  have haz : a = ⟨z, hz⟩ := GroundTheory.Automorphic.HarishChandra.harishChandraHom_injective hae
  have hval : A.map (Subalgebra.center ℂ (GroundTheory.Automorphic.HarishChandra.U n)).val =
      Algebra.adjoin ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet
        (fun i j : Fin n => GroundTheory.Automorphic.HarishChandra.e (i, j)) u) := by
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  rw [← hval]
  exact ⟨a, ha, by rw [haz]; rfl⟩
end
end
