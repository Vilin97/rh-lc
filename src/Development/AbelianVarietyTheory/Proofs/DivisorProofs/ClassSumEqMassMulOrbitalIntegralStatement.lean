module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentDefiniteUnitaryFinitePartEqLocalPo
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRegroupCommutativeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeProductOfLocalTestFunctionsSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStabiliserLeCentraliserCompactPartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularRationalPointTestSupportDoubleCosetsFinitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevel

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicComm

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinCentComm

theorem commute_aeval {R : Type} [CommRing R] {r : ℕ} {m A : Matrix (Fin r) (Fin r) R}
    (h : Commute m A) (p : R[X]) : Commute m (aeval A p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_right hq
  | monomial k a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact (h.pow_right k).smul_right a

theorem aeval_mulVec_krylov {R : Type} [CommRing R] {r : ℕ} (A : Matrix (Fin r) (Fin r) R)
    (v c : Fin r → R) :
    aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) *ᵥ v = GlobalTheory.ClassParam.krylov A v *ᵥ c := by
  ext i

  simp [GlobalTheory.ClassParam.krylov, map_sum, aeval_monomial, Matrix.sum_mulVec,
  Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.sum_apply,
  Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem eq_aeval_of_cyclic {R : Type} [CommRing R] {r : ℕ} (A : Matrix (Fin r) (Fin r) R) (v : Fin r → R)
    (hKu : IsUnit (GlobalTheory.ClassParam.krylov A v).det) (n : Matrix (Fin r) (Fin r) R) (hn : Commute n A) :
    ∃ q : R[X], n = aeval A q := by
  set K := GlobalTheory.ClassParam.krylov A v with hK
  let c := K⁻¹ *ᵥ (n *ᵥ v)
  refine ⟨∑ j : Fin r, monomial (j : ℕ) (c j), ?_⟩
  set p := aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) with hp
  have hpv : p *ᵥ v = n *ᵥ v := by
    rw [hp, aeval_mulVec_krylov, ← hK]
    simp only [c, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu, Matrix.one_mul]
  have hpA : Commute p A := (commute_aeval (Commute.refl A) _).symm
  have hcol : n * K = p * K := by
    ext i j
    have e1 : ∀ M : Matrix (Fin r) (Fin r) R, Commute M A →
        (M * K) i j = (A ^ (j : ℕ) *ᵥ (M *ᵥ v)) i := by
      intro M hM
      have : (M * K) i j = (M *ᵥ (A ^ (j : ℕ) *ᵥ v)) i := by
        simp [hK, GlobalTheory.ClassParam.krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (hM.pow_right _).eq]
    rw [e1 n hn, e1 p hpA, hpv]
  have := congrArg (· * K⁻¹) hcol
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu] using this

theorem commute_of_commute_map_separable {E R : Type} [Field E] [CommRing R] (f : E →+* R) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) E) (hA : A.charpoly.Separable) (X Y : Matrix (Fin r) (Fin r) R)
    (hX : X * A.map f = A.map f * X) (hY : Y * A.map f = A.map f * Y) : X * Y = Y * X := by
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field A hA
  have hKu : IsUnit (GlobalTheory.ClassParam.krylov (A.map f) (f ∘ v)).det := by
    rw [← GlobalTheory.ClassParam.krylov_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 hv).map f
  obtain ⟨q, rfl⟩ := eq_aeval_of_cyclic (A.map f) (f ∘ v) hKu Y hY
  exact (commute_aeval (m := X) hX q).eq

end GlobalTheory.BCT.FinCentComm

namespace GlobalTheory.BCT.FinCentComm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem map_fst_eq_one (a : finU (E := E) (n := n)) : ((a : UA E n) : GA E n).val.map (FinPtLoc.fstA E) = 1 := by
  have ha : cInf (a : UA E n) = 1 := a.2
  ext i j
  have h := congrArg (fun g : GL (Fin n) (Cinf E) => g.val i j) ha
  change (infEq E).symm (FinPtLoc.fstA E (((a : UA E n) : GA E n).val i j)) = (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j at h
  rw [Matrix.map_apply]
  apply (infEq E).symm.injective
  rw [h]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem map_snd_finPt (γ : UE E n) :
    (((finPt γ : finU (E := E) (n := n)) : UA E n) : GA E n).val.map (pFin E) = γ.1.val.map (algebraMap E (Af E)) := by
  rw [FinPtLoc.finPt_eq]
  ext i j
  rw [Matrix.map_apply, FinPtLoc.snd_entry]
  rfl

end GlobalTheory.BCT.FinCentComm


open GlobalTheory.BCT.FinCentComm in
theorem GlobalTheory.BCT.finCent_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n),
    γ.1.val.charpoly.Separable → ∀ a ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ),
      ∀ b ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ), a * b = b * a := by
  intro E _ _ _ n γ hγ a ha b hb
  have key : ∀ c ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ),
      (((c : UA E n) : GA E n).val.map (pFin E)) * γ.1.val.map (algebraMap E (Af E)) =
        γ.1.val.map (algebraMap E (Af E)) * ((c : UA E n) : GA E n).val.map (pFin E) := by
    intro c hc
    have h : c * finPt γ = finPt γ * c := hc
    have h' := congrArg (fun z : finU (E := E) (n := n) => ((z : UA E n) : GA E n).val.map (pFin E)) h
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul] at h'
    rwa [map_snd_finPt] at h'
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  apply FinPtLoc.ext_ad
  · rw [Matrix.map_mul, Matrix.map_mul, map_fst_eq_one a, map_fst_eq_one b]
  · rw [Matrix.map_mul, Matrix.map_mul]
    exact commute_of_commute_map_separable (algebraMap E (Af E)) γ.1.val hγ _ _ (key a ha) (key b hb)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicCommStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.centralizer_regular_rationalPoint_finiteAdelic_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n), γ.1.val.charpoly.Separable → ∀ a ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ), ∀ b ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ), a * b = b * a := by
  first | exact @GlobalTheory.BCT.finCent_comm | exact GlobalTheory.BCT.finCent_comm | (intros; apply GlobalTheory.BCT.finCent_comm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeProductOfLocalTestFunctionsSectionStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isHecke_productOfLocalTestFunctions_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → IsHecke (globLev S K') (globFn S f) := by
  first | exact @GlobalTheory.BCT.GlobHecke.isHecke_globFn | exact GlobalTheory.BCT.GlobHecke.isHecke_globFn | (intros; apply GlobalTheory.BCT.GlobHecke.isHecke_globFn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeveStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.productOfLocalLevelsUnitary_isOpen_isCompact_isLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → IsOpen (globLev S (KL n) : Set (finU (E := E) (n := n))) ∧ IsCompact (globLev S (KL n) : Set (finU (E := E) (n := n))) ∧ IsLevel (MonoidHom.id _) (globLev S (KL n)) (globLev S K') := by
  first | exact @GlobalTheory.BCT.GlobLev.globLev_isOpen_isCompact_isLevel | exact GlobalTheory.BCT.GlobLev.globLev_isOpen_isCompact_isLevel | (intros; apply GlobalTheory.BCT.GlobLev.globLev_isOpen_isCompact_isLevel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumEqMassMulOrbitalIntegral

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.ClsOrb

theorem clsSum_eq_mass_mul_twOrb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → clsSum S K' f γ = mass (MonoidHom.id _) (ratFinU E n) (finPt γ) * twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f) := by
  intro E _ _ _ hU n hn S hS lam K' hK' f hf γ hγ
  obtain ⟨hKo, hKc, hlev⟩ := GlobalTheory.T.productOfLocalLevelsUnitary_isOpen_isCompact_isLevel E hU n hn S hS K' hK'
  have hH := GlobalTheory.T.isHecke_productOfLocalTestFunctions_section E hU n hn S hS K' hK' f hf
  have hcomm := GlobalTheory.T.centralizer_regular_rationalPoint_finiteAdelic_comm E n γ hγ
  have hcpt := GlobalTheory.T.level_stabiliser_le_centraliser_compact_part E hU n hn S hS K' hK' γ hγ
  have hsupp := GlobalTheory.T.regularRationalPoint_testSupport_doubleCosets_finite E hU n hn S hS K' hK' f hf γ hγ
  have horb := GlobalTheory.BCT.OrbLev.twOrb_eq_sum_smallerLevel (finU (E := E) (n := n)) (MonoidHom.id _) (globLev S (KL n)) hKo hKc
    (fun k hk => hk) (globLev S K') hlev (finPt γ) (globFn S f) hH hcpt hsupp
  set T := twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ) with hT
  have hCT : cptPart T ≤ T := (Subgroup.closure_le T).2 fun t ht => ht.1
  have hU' : ∀ x : finU (E := E) (n := n), T ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom ≤ cptPart T ∧
      (T ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).relIndex (cptPart T) ≠ 0 := fun x =>
    ⟨le_trans (inf_le_inf_left _ (Subgroup.map_mono hlev.2.1)) (hcpt x).1, (hcpt x).2⟩
  have hinv : ∀ t ∈ T, ∀ k ∈ globLev S K', ∀ x : finU (E := E) (n := n),
      globFn S f ((t * x * k)⁻¹ * finPt γ * (t * x * k)) = globFn S f (x⁻¹ * finPt γ * x) := by
    intro t ht k hk x
    have ht' : t * finPt γ = finPt γ * t := ht
    have e1 : t⁻¹ * finPt γ * t = finPt γ := by
      rw [mul_assoc, ← ht', ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 : (t * x * k)⁻¹ * finPt γ * (t * x * k) = k⁻¹ * (x⁻¹ * (t⁻¹ * finPt γ * t) * x) * k := by group
    rw [e2, e1, mul_assoc, (hH.2 k⁻¹ (inv_mem hk) _).1, (hH.2 k hk _).2]
  have hreg := GlobalTheory.T.finsum_doubleCoset_regroup_commutative (finU (E := E) (n := n)) T (ratFinU E n) (cptPart T) (globLev S K')
    (fun x => globFn S f (x⁻¹ * finPt γ * x)) hcomm hCT hU' hinv
  simp only [MonoidHom.id_apply] at horb
  rw [clsSum, horb.1, horb.2, hreg, mass]
  ring

end GlobalTheory.BCT.ClsOrb
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumEqMassMulOrbitalIntegralStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.classSum_eq_mass_mul_orbitalIntegral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → clsSum S K' f γ = mass (MonoidHom.id _) (ratFinU E n) (finPt γ) * twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f) := by
  first | exact @GlobalTheory.BCT.ClsOrb.clsSum_eq_mass_mul_twOrb | exact GlobalTheory.BCT.ClsOrb.clsSum_eq_mass_mul_twOrb | (intros; apply GlobalTheory.BCT.ClsOrb.clsSum_eq_mass_mul_twOrb <;> assumption)
end
end
