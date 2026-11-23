module

public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
public import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
public import Mathlib.Tactic.Continuity
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Matrix.PEquiv
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv
public import Mathlib.Basic.PEquiv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionCuspidalParabolicProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrrRepHarishChandraDistinctCuspidalLabelsStatement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HarishChandraLabels.Basics
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonotoneBlocksSameHarishChandraCharacter

section

@[expose] public section

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.HCSort

open Formalism.L2.PT GlobalTheory.SerOSys.TranspLabel

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem trace_conj_rep {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (P g : G) : LinearMap.trace ℂ V (ρ (P * g * P⁻¹)) = LinearMap.trace ℂ V (ρ g) := by
  let E : V ≃ₗ[ℂ] V := LinearEquiv.ofLinearMap (ρ P) (ρ P⁻¹)
    (LinearMap.ext fun v => by
      show (ρ P * ρ P⁻¹) v = v
      rw [← map_mul, mul_inv_cancel, map_one]; rfl)
    (LinearMap.ext fun v => by
      show (ρ P⁻¹ * ρ P) v = v
      rw [← map_mul, inv_mul_cancel, map_one]; rfl)
  have h : E.conj (ρ g) = ρ (P * g * P⁻¹) := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply_apply, map_mul, map_mul]
    rfl
  rw [← h, LinearMap.trace_conj']

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {s : ℕ}

def blockEquiv (e : ι ≃ κ) (b : ι → Fin s) (c : Fin s) : {i // b i = c} ≃ {k // (b ∘ e.symm) k = c} :=
  e.subtypeEquiv (fun i => by simp)

def lamT (e : ι ≃ κ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (c : Fin s) :
    FDRep ℂ (GL {k // (b ∘ e.symm) k = c} K) :=
  Formalism.IrreducibleCountingLemmas.TYPES.transp (blockEquiv e b c) (lam c)

theorem mem_parab_symm (e : ι ≃ κ) (b : ι → Fin s) (p : parab K (b ∘ e.symm)) :
    (glEquiv K e).symm p.1 ∈ parab K b := by
  obtain ⟨h1, h2⟩ := p.2
  refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
  · show Matrix.reindex e.symm e.symm (p.1 : Matrix κ κ K) i j = 0
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    exact h1 _ _ (by simpa using hij)
  · rw [← map_inv]
    show Matrix.reindex e.symm e.symm ((p.1⁻¹ : GL κ K) : Matrix κ κ K) i j = 0
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    exact h2 _ _ (by simpa using hij)

theorem mem_parab (e : ι ≃ κ) (b : ι → Fin s) (p : parab K b) :
    glEquiv K e p.1 ∈ parab K (b ∘ e.symm) := by
  obtain ⟨h1, h2⟩ := p.2
  refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
  · show Matrix.reindex e e (p.1 : Matrix ι ι K) i j = 0
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    exact h1 _ _ (by simpa using hij)
  · rw [← map_inv]
    show Matrix.reindex e e ((p.1⁻¹ : GL ι K) : Matrix ι ι K) i j = 0
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    exact h2 _ _ (by simpa using hij)

theorem infl_symm (e : ι ≃ κ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (p : parab K (b ∘ e.symm)) :
    infl K b lam ⟨(glEquiv K e).symm p.1, mem_parab_symm e b p⟩ = infl K (b ∘ e.symm) (lamT e b lam) p := by
  unfold infl
  congr 1

def hcEquiv (e : ι ≃ κ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) :
    hcSpace K b lam ≃ₗ[ℂ] hcSpace K (b ∘ e.symm) (lamT e b lam) where
  toFun F := ⟨fun x => F.1 ((glEquiv K e).symm x), fun p x => by
    show F.1 ((glEquiv K e).symm (p.1 * x)) = infl K (b ∘ e.symm) (lamT e b lam) p (F.1 ((glEquiv K e).symm x))
    rw [map_mul, ← infl_symm]
    exact F.2 ⟨_, mem_parab_symm e b p⟩ _⟩
  map_add' F G := rfl
  map_smul' a F := rfl
  invFun F := ⟨fun y => F.1 (glEquiv K e y), fun p y => by
    show F.1 (glEquiv K e (p.1 * y)) = infl K b lam p (F.1 (glEquiv K e y))
    have hp : (⟨(glEquiv K e).symm (glEquiv K e p.1), mem_parab_symm e b ⟨_, mem_parab e b p⟩⟩ : parab K b) = p :=
      Subtype.ext ((glEquiv K e).symm_apply_apply p.1)
    have hi : infl K b lam p = infl K b lam ⟨(glEquiv K e).symm (glEquiv K e p.1), _⟩ := congrArg _ hp.symm
    rw [map_mul, hi]
    exact (F.2 ⟨_, mem_parab e b p⟩ (glEquiv K e y)).trans
      (LinearMap.congr_fun (infl_symm e b lam ⟨_, mem_parab e b p⟩).symm _)⟩
  left_inv F := by
    apply Subtype.ext
    funext y
    show F.1 ((glEquiv K e).symm (glEquiv K e y)) = F.1 y
    rw [MulEquiv.symm_apply_apply]
  right_inv F := by
    apply Subtype.ext
    funext x
    show F.1 (glEquiv K e ((glEquiv K e).symm x)) = F.1 x
    rw [MulEquiv.apply_symm_apply]

theorem trace_hcRep_lamT (e : ι ≃ κ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (g : GL κ K) :
    LinearMap.trace ℂ _ (hcRep K (b ∘ e.symm) (lamT e b lam) g) =
      LinearMap.trace ℂ _ (hcRep K b lam ((glEquiv K e).symm g)) := by
  have hconj : (hcEquiv e b lam).conj (hcRep K b lam ((glEquiv K e).symm g)) = hcRep K (b ∘ e.symm) (lamT e b lam) g := by
    apply LinearMap.ext
    intro F
    rw [LinearEquiv.conj_apply_apply]
    apply Subtype.ext
    funext x
    show F.1 (glEquiv K e ((glEquiv K e).symm x * (glEquiv K e).symm g)) = F.1 (x * g)
    rw [← map_mul, MulEquiv.apply_symm_apply]
  rw [← hconj, LinearMap.trace_conj']

end GlobalTheory.HCSort

namespace GlobalTheory.HCSort

theorem exists_monotone_same_trace : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → ∃ (b' : Fin r → Fin s) (lam' : ∀ c : Fin s, FDRep ℂ (GL {i // b' i = c} K)), Function.Surjective b' ∧ (∀ c, Simple (lam' c) ∧ IsCuspidal K (lam' c)) ∧ Monotone b' ∧ ∀ x : GL (Fin r) K, LinearMap.trace ℂ (hcSpace K b' lam') (hcRep K b' lam' x) = LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x) := by
  intro K _ _ _ r s b lam hb hl
  let e : Fin r ≃ Fin r := (Tuple.sort b).symm
  refine ⟨b ∘ e.symm, lamT e b lam, hb.comp e.symm.surjective,
    fun c => ⟨Formalism.L2.PT.simple_transp _ (hl c).1, Formalism.L2.PT.isCuspidal_transp _ (hl c).2⟩, ?_, fun x => ?_⟩
  · show Monotone (b ∘ (Tuple.sort b).symm.symm)
    rw [Equiv.symm_symm]
    exact Tuple.monotone_sort b
  · rw [trace_hcRep_lamT]
    let P : GL (Fin r) K := ⟨e.toPEquiv.toMatrix, e.symm.toPEquiv.toMatrix,
      by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
        Equiv.toPEquiv_refl, PEquiv.toMatrix_refl],
      by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
        Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]⟩
    have h : (glEquiv K e).symm x = P * x * P⁻¹ := by
      apply Units.ext
      change Matrix.reindex e.symm e.symm (x : Matrix (Fin r) (Fin r) K) =
        e.toPEquiv.toMatrix * (x : Matrix (Fin r) (Fin r) K) * e.symm.toPEquiv.toMatrix
      rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
      rfl
    rw [h, trace_conj_rep]

end GlobalTheory.HCSort
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonotoneBlocksSameHarishChandraCharacterStatement

section

@[expose] public section

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

theorem _root_.GlobalTheory.T.exists_monotone_blocks_same_harishChandra_character : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → ∃ (b' : Fin r → Fin s) (lam' : ∀ c : Fin s, FDRep ℂ (GL {i // b' i = c} K)), Function.Surjective b' ∧ (∀ c, Simple (lam' c) ∧ IsCuspidal K (lam' c)) ∧ Monotone b' ∧ ∀ x : GL (Fin r) K, LinearMap.trace ℂ (hcSpace K b' lam') (hcRep K b' lam' x) = LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x) := by
  first | exact @GlobalTheory.HCSort.exists_monotone_same_trace | exact GlobalTheory.HCSort.exists_monotone_same_trace | (intros; apply GlobalTheory.HCSort.exists_monotone_same_trace <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionCuspidalParabolicProductStatement

section

@[expose] public section

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

theorem _root_.GlobalTheory.T.harishChandraInduction_cuspidalParabolicProduct : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → Monotone b → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x)) := by
  first | exact @GlobalTheory.HCInduction.isCuspProdChar_trace_hcRep | exact GlobalTheory.HCInduction.isCuspProdChar_trace_hcRep | (intros; apply GlobalTheory.HCInduction.isCuspProdChar_trace_hcRep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarefreeLabelIsCuspidalParabolicProductCharact

section

@[expose] public section

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.SqfreeCuspProd

theorem labO_irreducible {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : LabelConv K}
    (O : LabelMap K C) {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    {σ : FDRep ℂ (GL κ K)} (hs : Simple σ) (hc : IsCuspidal K σ) : Irreducible (labO O σ) :=
  (O.lab_spec _ _ (Nat.succ_le_of_lt Fintype.card_pos) (Formalism.L2.PT.simple_transp _ hs)
    (Formalism.L2.PT.isCuspidal_transp _ hc)).2.1

theorem injective_of_squarefree {R : Type} [CommMonoid R] {s : ℕ} (F : Fin s → R)
    (hF : ∀ c, Irreducible (F c)) (hsq : Squarefree (∏ c, F c)) : Function.Injective F := by
  intro c c' h
  by_contra hne
  have hd : F c * F c' ∣ ∏ x, F x := by
    rw [← Finset.mul_prod_erase Finset.univ F (Finset.mem_univ c),
      ← Finset.mul_prod_erase (Finset.univ.erase c) F
        (Finset.mem_erase.2 ⟨fun h' => hne h'.symm, Finset.mem_univ c'⟩), ← mul_assoc]
    exact dvd_mul_right _ _
  rw [h] at hd
  exact (hF c').not_isUnit (hsq _ hd)

theorem character_eq_of_constituent {Γ : Type} [Group Γ] (τ : FDRep ℂ Γ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ Γ V) (hτ : Simple τ) (hρ : IsIrrRep ρ) (hc : IsConstituent τ ρ)
    (x : Γ) : τ.character x = LinearMap.trace ℂ V (ρ x) := by
  obtain ⟨φ, hφ, hne⟩ := hc
  have hirr := (PI.GreenHCLabel.simple_irreducible Γ τ).1 hτ
  have hker : LinearMap.ker φ = ⊥ := by
    rcases hirr.2 (LinearMap.ker φ) (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      have := congrArg (fun k => k v) (hφ g)
      simp only [LinearMap.comp_apply] at this
      rw [this, hv, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hne
  have hran : LinearMap.range φ = ⊤ := by
    rcases hρ.2 (LinearMap.range φ) (fun g v hv => by
      obtain ⟨y, rfl⟩ := hv
      exact ⟨τ.ρ g y, by simpa using congrArg (fun k => k y) (hφ g)⟩) with h | h
    · exact absurd (LinearMap.range_eq_bot.1 h) hne
    · exact h
  let e : τ ≃ₗ[ℂ] V :=
    LinearEquiv.ofBijective φ ⟨LinearMap.ker_eq_bot.1 hker, LinearMap.range_eq_top.1 hran⟩
  haveI : Module.Finite ℂ V := Module.Finite.equiv e
  have hconj : e.conj (τ.ρ x) = ρ x := by
    ext v
    obtain ⟨w, rfl⟩ := e.surjective v
    rw [LinearEquiv.conj_apply]
    show e (τ.ρ x (e.symm (e w))) = ρ x (e w)
    rw [e.symm_apply_apply]
    exact congrArg (fun k => k w) (hφ x)
  rw [FDRep.character, ← hconj, LinearMap.trace_conj']

theorem isCuspProdChar_of_squarefree : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K)
    (O : LabelMap K C) (r : ℕ) (τ : FDRep ℂ (GL (Fin r) K)) (f : K[X]), Simple τ → HasLabelO O τ f →
    Squarefree f → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => τ.character x) := by
  intro K _ _ _ C O r τ f hτ hL hsq
  obtain ⟨s, b, lam, hb, hl, hc, rfl⟩ := hL
  have hirrF : ∀ c, Irreducible (labO O (lam c)) := fun c => by
    obtain ⟨i, hi⟩ := hb c
    haveI : Nonempty {i // b i = c} := ⟨⟨i, hi⟩⟩
    exact labO_irreducible O (hl c).1 (hl c).2
  have hinj := injective_of_squarefree _ hirrF hsq
  have hirr := GlobalTheory.T.isIrrRep_harishChandra_distinct_cuspidal_labels K r s b lam hb hl C O hinj
  obtain ⟨b', lam', hb', hl', hmono, htr⟩ := GlobalTheory.T.exists_monotone_blocks_same_harishChandra_character K r s b lam hb hl
  have hcp := GlobalTheory.T.harishChandraInduction_cuspidalParabolicProduct K r s b' lam' hb' hl' hmono
  have hfun : (fun x : GL (Fin r) K => τ.character x) =
      fun x => LinearMap.trace ℂ (hcSpace K b' lam') (hcRep K b' lam' x) := by
    funext x
    rw [htr x]
    exact character_eq_of_constituent τ _ hτ hirr hc x
  rw [hfun]
  exact hcp

end GlobalTheory.SqfreeCuspProd
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarefreeLabelIsCuspidalParabolicProductCharactStatement

section

@[expose] public section

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

theorem _root_.GlobalTheory.T.squarefreeLabel_isCuspidalParabolicProductCharacter : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (O : LabelMap K C) (r : ℕ) (τ : FDRep ℂ (GL (Fin r) K)) (f : K[X]), Simple τ → HasLabelO O τ f → Squarefree f → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => τ.character x) := by
  first | exact @GlobalTheory.SqfreeCuspProd.isCuspProdChar_of_squarefree | exact GlobalTheory.SqfreeCuspProd.isCuspProdChar_of_squarefree | (intros; apply GlobalTheory.SqfreeCuspProd.isCuspProdChar_of_squarefree <;> assumption)
end
end
