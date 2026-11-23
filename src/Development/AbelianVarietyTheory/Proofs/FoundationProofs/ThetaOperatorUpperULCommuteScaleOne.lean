module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondCommutesHeckeU
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFunctionalOddWeightOddPrime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInvariantLift
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeNormGamma1PrimePowInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeNormPreservesDeltaPowerCondition
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowCalculusStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowHeckeNormStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsThBSuccCoeffCong
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeDiamondAction
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondCommutesHeckeUStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.diamond_commutes_hecke_U : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (w d : ℕ), d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l, b ∈ X.B N l w →
  X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b) = X.heckeU l (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  first | exact @GlobalTheory.KZ.DiamU.act_sgD_heckeU | exact GlobalTheory.KZ.DiamU.act_sgD_heckeU | (intros; apply GlobalTheory.KZ.DiamU.act_sgD_heckeU <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeNormGamma1PrimePowInvariantStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.heckeNorm_gamma1PrimePow_invariant : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ∀ g : X.K,
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g →
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g) := by
  first | exact @GlobalTheory.normInv_gamma1 | exact GlobalTheory.normInv_gamma1 | (intros; apply GlobalTheory.normInv_gamma1 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeNormPreservesDeltaPowerConditionStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.heckeNorm_preserves_delta_powerCondition : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ¬ l ∣ N → ∀ f : X.K,
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) f →
  (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ f * X.sl (ofSL δ) f = g ^ (l ^ n)) →
  (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧
        (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) *
          X.sl (ofSL δ) (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) = g ^ (l ^ n)) := by
  first | exact @GlobalTheory.NormDelta.norm_delta | exact GlobalTheory.NormDelta.norm_delta | (intros; apply GlobalTheory.NormDelta.norm_delta <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumAtCuspHahnCoeffOfIntegralExponents

section

@[expose] public section

noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

namespace GlobalTheory.HeckeInt

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem exists_pre_exp [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ∃ ω : Ω, ε ω = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hn : x.den ≠ 0 := x.den_nz
  haveI : NeZero ((x.den : ℕ) : Ω) := ⟨by exact_mod_cast hn⟩
  haveI : NeZero x.den := ⟨hn⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω x.den
  have hζ' := hζ.map_of_injective ε.injective
  have hz : (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have hx : (x : ℂ) * (x.den : ℂ) = (x.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num x
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = (x.num : ℂ) * (2 * Real.pi * Complex.I) := by
      linear_combination (2 * Real.pi * Complex.I) * hx
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hz
  exact ⟨ζ ^ i, by rw [map_pow]; exact hi⟩

theorem eps_eOm [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) :=
  Function.invFun_eq (exists_pre_exp ε x)

theorem sub_coeff (ε : Ω →+* ℂ) (q : ℕ) (hq : 0 < q) (j : ℚ) (φ : HahnSeries ℚ Ω) (s : ℚ) :
    (sub ε 1 j (q : ℚ) φ).coeff s = eOm ε (s * j) * φ.coeff ((q : ℚ) * s) := by
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have h : (0 : ℚ) < 1 / (q : ℚ) := by positivity
  unfold sub scale
  rw [dite_eq_left h]
  have e : (OrderIso.mulLeft₀ (1 / (q : ℚ)) h).toOrderEmbedding ((q : ℚ) * s) = s := by
    simp only [RelIso.coe_toRelEmbedding, OrderIso.coe_toOrderEmbedding, OrderIso.mulLeft₀_apply]
    field_simp
  have key := HahnSeries.embDomain_coeff (f := (OrderIso.mulLeft₀ (1 / (q : ℚ)) h).toOrderEmbedding)
    (x := cm (fun r => eOm ε (r * j / (q : ℚ))) φ) (a := (q : ℚ) * s)
  rw [e] at key
  rw [key]
  simp only [cm]
  congr 2
  field_simp

theorem sum_eOm [IsAlgClosed Ω] (ε : Ω →+* ℂ) (q : ℕ) (hq : 0 < q) (s : ℚ) (hs : ((q : ℚ) * s).den = 1) :
    ∑ j ∈ Finset.range q, eOm ε (s * (j : ℚ)) = if s.den = 1 then (q : Ω) else 0 := by
  apply ε.injective
  have hz : ∀ j : ℕ, ε (eOm ε (s * (j : ℚ))) = (Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))) ^ j := by
    intro j
    rw [eps_eOm, ← Complex.exp_nat_mul]
    congr 1
    push_cast; ring

  rw [map_sum]
  simp only [hz]
  split_ifs with hd
  · have h1 : Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)) = 1 := by
      have : (s : ℂ) = ((s.num : ℤ) : ℂ) := by
        have := Rat.coe_int_num_of_den_eq_one hd
        rw [← this]; push_cast; rfl
      rw [this, show 2 * (Real.pi : ℂ) * Complex.I * ((s.num : ℤ) : ℂ) = (s.num : ℂ) * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    simp [h1]
  · have hne : Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)) ≠ 1 := by
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have hsn : (s : ℂ) = (n : ℂ) := by
        have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
        apply mul_left_cancel₀ h2
        linear_combination hn
      have : s = (n : ℚ) := by exact_mod_cast hsn
      exact hd (by rw [this]; rfl)
    have hpow : (Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))) ^ q = 1 := by
      rw [← Complex.exp_nat_mul]
      have hx : ((q : ℚ) * s : ℚ) = ((((q : ℚ) * s).num : ℤ) : ℚ) := (Rat.coe_int_num_of_den_eq_one hs).symm
      have hx' : (q : ℂ) * (s : ℂ) = ((((q : ℚ) * s).num : ℤ) : ℂ) := by exact_mod_cast hx
      rw [show (q : ℂ) * (2 * Real.pi * Complex.I * (s : ℂ)) = ((((q : ℚ) * s).num : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
        rw [← hx']; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [geom_sum_eq hne, hpow, sub_self, zero_div, map_zero]

theorem hq_coeff_of_int : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (q : ℕ), 0 < q → ∀ φ : HahnSeries ℚ Ω,
    (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) → ∀ s : ℚ,
      (hq ε q φ).coeff s = if s.den = 1 then φ.coeff ((q : ℚ) * s) else 0 := by
  intro Ω _ _ _ ε q hq0 φ hφ s
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  unfold hq
  rw [HahnSeries.coeff_smul, HahnSeries.coeff_sum, smul_eq_mul]
  simp only [GlobalTheory.HeckeInt.sub_coeff ε q hq0]
  rw [← Finset.sum_mul]
  by_cases hc : φ.coeff ((q : ℚ) * s) = 0
  · simp [hc]
  · rw [GlobalTheory.HeckeInt.sum_eOm ε q hq0 s (hφ _ hc)]
    have hqne : (q : Ω) ≠ 0 := by exact_mod_cast hq0.ne'
    split_ifs
    · field_simp
    · simp

end GlobalTheory.HeckeInt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumAtCuspHahnCoeffOfIntegralExponentsStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

theorem _root_.GlobalTheory.T.heckeSumAtCuspHahn_coeff_of_integral_exponents : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (q : ℕ), 0 < q → ∀ φ : HahnSeries ℚ Ω,
  (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) → ∀ s : ℚ, (hq ε q φ).coeff s = if s.den = 1 then φ.coeff ((q : ℚ) * s) else 0 := by
  first | exact @GlobalTheory.HeckeInt.hq_coeff_of_int | exact GlobalTheory.HeckeInt.hq_coeff_of_int | (intros; apply GlobalTheory.HeckeInt.hq_coeff_of_int <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorUpperULCommuteScaleOne

section

@[expose] public section

noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThHeckeU

theorem eval_kmap {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (σ : X.K ≃+* X.K) (x : X.Khat l) (f : X.Kˣ)
    (h : AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l σ x) = X.cls l n (Units.map σ.toMonoidHom f) := by
  rw [AdicCompletion.eval_apply]
  change (AdicCompletion.map _ _ x).val n = _
  rw [AdicCompletion.map_val_apply, ← AdicCompletion.eval_apply, h]
  rw [Tower.cls, Tower.cls, LinearMap.reduceModIdeal_apply, LinearMap.baseChange_tmul]
  rfl

theorem cls_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (f g : X.Kˣ) : X.cls l n (f * g) = X.cls l n f + X.cls l n g := by
  simp only [Tower.cls, ← Submodule.Quotient.mk_add, ← TensorProduct.tmul_add]
  rfl

theorem eval_sum_kmap {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (s : Finset ℕ) (σ : ℕ → (X.K ≃+* X.K)) (x : X.Khat l) (f : X.Kˣ)
    (h : AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f) :
    AdicCompletion.eval (idl l) (X.Kl l) n (∑ j ∈ s, X.kmap l (σ j) x) =
      X.cls l n (∏ j ∈ s, Units.map (σ j).toMonoidHom f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, map_zero, Finset.prod_empty]
    simp [Tower.cls]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, map_add (f := _), ih, cls_mul, eval_kmap X l n _ x f h]

theorem isThB_zero {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω)
    (N l : ℕ) [Fact l.Prime] (b : X.Fn l) (ψ : HahnSeries ℚ Ω) (hψ : ∀ r, ψ.coeff r ∈ A) : IsThB X A N l 0 b ψ := by
  have hprim : Prim A (X.exp 1) := by
    rw [map_one]
    refine ⟨fun r => ?_, 0, by simp, by simp⟩
    by_cases h : r = 0
    · subst h; simp
    · simp [HahnSeries.coeff_one, h]
  refine ⟨1, fun γ _ => by simp, ?_, fun δ _ _ => ⟨1, fun γ _ => by simp, by simp⟩, hψ, 1, 1, 1, one_ne_zero, by simp,
    hprim, hprim, fun r => ⟨(ψ * X.exp 1 * X.exp 1).coeff r -
      (theta 1 (X.exp 1) * X.exp 1 - X.exp 1 * theta 1 (X.exp 1)).coeff r, ?_, by simp⟩⟩
  · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) 0 (b ![1, 0]))
    rw [← hy, Tower.cls, Submodule.Quotient.eq]
    simp
  · simp only [map_one, mul_one, one_mul, sub_self, HahnSeries.coeff_zero, sub_zero]
    exact hψ r

theorem isThB_act_heckeU_same : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ), d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l,
    b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) →
  IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b)) (hq ε l φ) := by
  intro Ω _ _ _ ε X A N l _ n w d hd hl b hb φ hφ h
  rw [GlobalTheory.T.diamond_commutes_hecke_U Ω ε X N l w d hd hl b hb]
  obtain ⟨f, hinv, hcls, hδ, hdl⟩ := h
  have hint : ∀ r, (hq ε l φ).coeff r ∈ A := by
    intro r
    rw [GlobalTheory.T.heckeSumAtCuspHahn_coeff_of_integral_exponents Ω ε l (Nat.Prime.pos Fact.out) φ hφ r]
    split_ifs
    · exact hdl.1 _
    · exact A.zero_mem
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact isThB_zero X A N l _ _ hint
  set b' := X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b
  have hT : X.sl (ofSL ModularGroup.T) (f : X.K) = f := hinv _ (by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])
  have hcoe : ((∏ j ∈ Finset.range l,
      Units.map (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)])).toRingEquiv.toMonoidHom f : X.Kˣ) : X.K)
      = ∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) (f : X.K) := by
    rw [Units.coe_prod]; rfl
  refine ⟨∏ j ∈ Finset.range l, Units.map (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)])).toRingEquiv.toMonoidHom f,
    ?_, ?_, ?_, ?_⟩
  · rw [hcoe]; exact GlobalTheory.T.heckeNorm_gamma1PrimePow_invariant Ω ε X N l n hn _ hinv
  · have hv : X.heckeU l b' ![1, 0] = ∑ j ∈ Finset.range l,
        X.kmap l (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)])).toRingEquiv (b' ![1, 0]) := by
      simp only [Tower.heckeU]
      rw [LinearMap.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      show X.kmap l _ (b' _) = _
      congr 2
      ext i; fin_cases i <;> simp [mZl]
    rw [hv]
    exact eval_sum_kmap X l n (Finset.range l)
      (fun j => (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)])).toRingEquiv) _ f hcls
  · rw [hcoe]; exact GlobalTheory.T.heckeNorm_preserves_delta_powerCondition Ω ε X N l n hn hl _ hinv hδ
  · rw [hcoe]; exact GlobalTheory.T.isLogDerivQExpansionModPrimePow_heckeNorm Ω ε X A l n _ φ hT hφ hdl

theorem isThB_congr {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n : ℕ)
    (hj : ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) (hlA : (l : Ω) ∈ A.nonunits)
    (x : X.Fn l) (ψ ψ₂ : HahnSeries ℚ Ω) (h : IsThB X A N l n x ψ) (hint : ∀ r, ψ₂.coeff r ∈ A)
    (hc : ∀ r, CgA A l n (ψ.coeff r) (ψ₂.coeff r)) : IsThB X A N l n x ψ₂ := by
  obtain ⟨f, h1, h2, h3, h4⟩ := h
  obtain ⟨φ₀, han, hdiff⟩ := hj
  exact ⟨f, h1, h2, h3, (GlobalTheory.T.isLogDerivQExpansionModPrimePow_calculus ε X ⟨φ₀, hdiff, han⟩ l A hlA n 1 (f : X.K) (f : X.K) ψ ψ₂).2.2.1 h4 hint hc⟩

theorem isThB_act_heckeU : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ), Algebra.IsAlgebraic ℚ Ω →
    (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → 1 ≤ N → Odd w →
    (l : Ω) ∈ A.nonunits → d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsLat 1 φ →
  IsThB X A N l (n + 1) (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b)) (uq l φ) := by
  intro Ω _ _ _ ε X A N l _ n w d hAlg hj hl2 hN1 hw hlA hd hl b hb φ _ h
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, hAlg⟩
  have hl0 : 0 < l := Nat.Prime.pos Fact.out
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hl).symm
  obtain ⟨φ', h', hlat'⟩ := GlobalTheory.ThEx.of_lift GlobalTheory.ThLift.exists_invariant_lift Ω ε X A N l hAlg hj hl2 hl hN1 hlA n w hw _
    (GlobalTheory.CyclotomicQExpansion.ThnEx.diam_B X N l w d hN1 hNl hd b hb)
  have hU := isThB_act_heckeU_same Ω ε X A N l n w d hd hl b hb _
    (fun r hr => by simpa using hlat' r hr) h'
  rw [Api.hq_eq_uq_of_isAlgClosed hl0 hlat'] at hU
  have hc := GlobalTheory.ThBCompat.isThB_succ_coeff_cong Ω ε X A N l hl2 hl hN1 hlA n _ φ _ h h'
  have hφA : ∀ r, φ.coeff r ∈ A := by
    obtain ⟨f, -, -, -, hdl⟩ := h
    exact hdl.1
  refine isThB_congr X A N l n hj hlA _ _ _ hU ?_ ?_
  · intro r
    rw [Api.coeff_uq hl0]
    split_ifs
    · exact hφA _
    · exact A.zero_mem
  · intro r
    rw [Api.coeff_uq hl0, Api.coeff_uq hl0]
    split_ifs
    · obtain ⟨z, hz, e⟩ := hc ((l : ℚ) * r)
      exact ⟨-z, A.neg_mem _ hz, by linear_combination -e⟩
    · exact ⟨0, A.zero_mem, by simp⟩

end GlobalTheory.ThHeckeU
end
end
end
