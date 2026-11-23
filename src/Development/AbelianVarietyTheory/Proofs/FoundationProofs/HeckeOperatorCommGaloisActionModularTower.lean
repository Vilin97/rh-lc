module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBActCommGamma0CapGamma0LevelShimuraReciprocitStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBActDiagNatOneCommStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSetStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionUpperTriangularHeckeReindexOnBStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumActUpperTriangularHeckeReindexCoprimeUnit
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiamondMatrixGamma1Gamma0OfCoprime

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem diam_exists : ∀ (N l d : ℕ), 0 < N → Nat.Coprime N l → Nat.Coprime d N → ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  intro N l d _ hNl hdN

  obtain ⟨d', hd'N, hd'l⟩ := Nat.chineseRemainder hNl d 1
  have h1 : Nat.Coprime d' N := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hd'N]; exact hdN
  have h2 : Nat.Coprime d' l := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hd'l]; simp
  have h3 : Nat.Coprime d' (N * l) := Nat.Coprime.mul_right h1 h2
  have hg : Int.gcd (d' : ℤ) ((N * l : ℕ) : ℤ) = 1 := by rw [Int.gcd_natCast_natCast]; exact h3
  have hb := Int.gcd_eq_gcd_ab (d' : ℤ) ((N * l : ℕ) : ℤ)
  rw [hg] at hb
  set a := Int.gcdA (d' : ℤ) ((N * l : ℕ) : ℤ)
  set b := Int.gcdB (d' : ℤ) ((N * l : ℕ) : ℤ)
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![a, -b; ((N * l : ℕ) : ℤ), (d' : ℤ)]
  have hdet : M.det = 1 := by
    simp only [M, Matrix.det_fin_two_of]
    push_cast at hb ⊢
    linarith
  let γ : SL(2, ℤ) := ⟨M, hdet⟩
  have hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = M := rfl
  refine ⟨γ, Subgroup.mem_inf.2 ⟨CongruenceSubgroup.Gamma0_mem.2 ?_, CongruenceSubgroup.Gamma0_mem.2 ?_⟩, ?_⟩
  · rw [hγ]; simp [M]
  · rw [hγ]; simp [M]
  · simp only [en, hγ, M]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    push_cast
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hd'N

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiamondMatrixGamma1Gamma0OfCoprimeStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_isDiamondMatrixGamma1Gamma0_of_coprime : ∀ (N l d : ℕ), 0 < N → Nat.Coprime N l → Nat.Coprime d N → ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  first | exact @GlobalTheory.diam_exists | exact GlobalTheory.diam_exists | (intros; apply GlobalTheory.diam_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalAlgClosureRatPrimitiveRootEqPow

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem algEquiv_primitiveRoot_pow :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ), 0 < q →
      ∃ e : ℤ, IsCoprime e (q : ℤ) ∧ ∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e := by
  intro Ω _ _ _ s q hq
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : NeZero (q : Ω) := ⟨Nat.cast_ne_zero.mpr hq.ne'⟩
  obtain ⟨ζ₀, hζ₀⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.mpr hq).ne')
  have h0 : IsPrimitiveRoot ζ₀ q := (Polynomial.isRoot_cyclotomic_iff).mp hζ₀
  have h1 : IsPrimitiveRoot (s ζ₀) q := h0.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := h0.eq_pow_of_pow_eq_one h1.pow_eq_one
  have hcop : i.Coprime q := (h0.pow_iff_coprime hq i).mp (hi ▸ h1)
  refine ⟨(i : ℤ), Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd] using hcop), ?_⟩
  intro ζ hζ
  obtain ⟨k, -, hk⟩ := h0.eq_pow_of_pow_eq_one hζ.pow_eq_one
  subst hk
  rw [zpow_natCast, map_pow, ← hi, ← pow_mul, ← pow_mul, mul_comm]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalAlgClosureRatPrimitiveRootEqPowStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.galAlgClosureRat_primitiveRoot_eq_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ), 0 < q → ∃ e : ℤ, IsCoprime e (q : ℤ) ∧ ∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e := by
  first | exact @GlobalTheory.algEquiv_primitiveRoot_pow | exact GlobalTheory.algEquiv_primitiveRoot_pow | (intros; apply GlobalTheory.algEquiv_primitiveRoot_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumActUpperTriangularHeckeReindexCoprimeUnitStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.sum_act_upperTriangular_hecke_reindex_coprime_unit : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (c : X.Fn l), (∀ t : ℤ, X.act l !![1, t; 0, 1] c = c) → ∀ (q : ℕ) (e : ℤ), 0 < q → IsCoprime e (q : ℤ) → ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ) * e; 0, (q : ℤ)] c = ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] c := by
  first | exact @GlobalTheory.KZ.Tower.sum_act_upper_mul_unit | exact GlobalTheory.KZ.Tower.sum_act_upper_mul_unit | (intros; apply GlobalTheory.KZ.Tower.sum_act_upper_mul_unit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommGaloisActionModularTower

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.HeckeGal

theorem B_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime]
    (b : X.Fn l) (hb : b ∈ X.B N l w) (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) :
    X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 γ hγ
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

def trSL (t : ℤ) : SL(2, ℤ) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem trSL_mem_Gam (N l : ℕ) (t : ℤ) : trSL t ∈ Gam N l := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]; simp [trSL]
  · rw [CongruenceSubgroup.Gamma0_mem]; simp [trSL]

theorem B_inv_tr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime]
    (b : X.Fn l) (hb : b ∈ X.B N l w) (t : ℤ) : X.act l !![1, t; 0, 1] b = b :=
  B_inv X N l w b hb (trSL t) (trSL_mem_Gam N l t)

theorem op_galB_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ T : Letter, admitted N l T → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.op N l T (X.galB l s b) = X.galB l s (X.op N l T b) := by
  intro Ω _ _ _ ε X hε hj N l w _ hl hN hNl hw T hT s b hb
  have hgb : X.galB l s b ∈ X.B N l w := GlobalTheory.T.galB_mem_kummer_invariant_set ε X hε hj N l w hl hN hNl hw s b hb
  have hinv := B_inv_tr X N l w _ hgb

  have hup : ∀ q : ℕ, 0 < q →
      (∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)]) (X.galB l s b) =
        X.galB l s ((∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)]) b) := by
    intro q hq
    obtain ⟨e, he, hζ⟩ := GlobalTheory.T.galAlgClosureRat_primitiveRoot_eq_pow s q hq

    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    rw [← GlobalTheory.T.sum_act_upperTriangular_hecke_reindex_coprime_unit X l _ hinv q e hq he]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (GlobalTheory.T.galoisAction_upperTriangular_hecke_reindex_on_B ε X hε hj N l w hl hN hNl hw s q e hq hζ (j : ℤ) b hb).symm

  have hdiam : ∀ d : ℕ, Nat.Coprime d N → sgD N l d ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l := by
    intro d hd
    have hex := GlobalTheory.T.exists_isDiamondMatrixGamma1Gamma0_of_coprime N l d (by omega) hNl hd
    exact (Classical.epsilon_spec hex).1
  cases T with
  | T q =>
    obtain ⟨hqp, hqd⟩ := hT
    have hqN : Nat.Coprime q N :=
      (Nat.Coprime.coprime_dvd_right (Dvd.intro l rfl) ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqd))
    have hq : 0 < q := hqp.pos
    simp only [Tower.op, Tower.heckeT, LinearMap.add_apply, map_add (f := _)]
    rw [hup q hq]
    congr 1
    have hdet1 : 0 < (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ).det := by
      rw [(sgD N l q).2]; exact one_pos
    have hdet2 : 0 < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      simp [Matrix.det_fin_two_of]; exact_mod_cast hq
    rw [← Tower.act_act Ω ε X l _ _ hdet1 hdet2, ← Tower.act_act Ω ε X l _ _ hdet1 hdet2,
      GlobalTheory.T.galB_act_diagNatOne_comm ε X hε l q hq s,
      GlobalTheory.T.galB_act_comm_gamma0CapGamma0Level_shimuraReciprocity ε X hε hj N l w hl hN hNl hw (sgD N l q) (hdiam q hqN) s b hb]
  | U =>
    simp only [Tower.op, Tower.heckeU]
    exact hup l (Fact.out : l.Prime).pos
  | D d =>
    simp only [Tower.op, Tower.diam]
    exact (GlobalTheory.T.galB_act_comm_gamma0CapGamma0Level_shimuraReciprocity ε X hε hj N l w hl hN hNl hw (sgD N l d) (hdiam d hT) s b hb).symm

end GlobalTheory.KZ.HeckeGal
end
end
