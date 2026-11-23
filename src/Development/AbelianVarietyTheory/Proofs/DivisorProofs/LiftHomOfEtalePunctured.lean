module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftSquareZeroOfFormallyEtaleAwayDepthStatement
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
public import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRing
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEThreeOfFreeRegularLocal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ExistsIsRegularAppendOfModDepthGE
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
public import Mathlib.RingTheory.AdicCompletion.RingHom
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ExistsIsRegularAppendOfModDepthGE

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtaleAwayOfEtaleOffMaximalIdeal

section

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory.EtaleAway

theorem isEtaleAt_of_formallyEtale_baseChange (S B : Type) [CommRing S] [CommRing B] [Algebra S B]
    (Q : Ideal B) [Q.IsPrime]
    (h : Algebra.FormallyEtale (Localization.AtPrime (Q.under S))
      (TensorProduct S (Localization.AtPrime (Q.under S)) B)) :
    Algebra.FormallyEtale S (Localization.AtPrime Q) := by
  set P : Ideal S := Q.under S with hP
  let M : Submonoid B := Algebra.algebraMapSubmonoid B P.primeCompl
  let Bp := Localization M
  have hpush : Algebra.IsPushout S (Localization.AtPrime P) B Bp :=
    (Algebra.isPushout_of_isLocalization P.primeCompl (Localization.AtPrime P) B Bp).symm
  let e : Localization.AtPrime P ⊗[S] B ≃ₐ[Localization.AtPrime P] Bp := hpush.equiv
  have h1 : Algebra.FormallyEtale (Localization.AtPrime P) Bp := Algebra.FormallyEtale.of_equiv e
  have h0 : Algebra.FormallyEtale S (Localization.AtPrime P) :=
    Algebra.FormallyEtale.of_isLocalization P.primeCompl
  have h2 : Algebra.FormallyEtale S Bp := Algebra.FormallyEtale.comp S (Localization.AtPrime P) Bp
  have hle : M ≤ Q.primeCompl := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [P, Ideal.under] using hx
  letI : Algebra Bp (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Bp (Localization.AtPrime Q) M Q.primeCompl hle
  haveI : IsScalarTower B Bp (Localization.AtPrime Q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Bp (Localization.AtPrime Q) M Q.primeCompl hle
  haveI : IsLocalization (Algebra.algebraMapSubmonoid Bp Q.primeCompl) (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le Bp (Localization.AtPrime Q) M Q.primeCompl hle
  have h3 : Algebra.FormallyEtale Bp (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization (Algebra.algebraMapSubmonoid Bp Q.primeCompl)
  haveI : IsScalarTower S Bp (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq (fun s => by
    rw [IsScalarTower.algebraMap_apply S B Bp, ← IsScalarTower.algebraMap_apply B Bp,
      ← IsScalarTower.algebraMap_apply S B])
  exact Algebra.FormallyEtale.comp S Bp (Localization.AtPrime Q)

end GlobalTheory.EtaleAway

namespace GlobalTheory.EtaleAway

theorem formallyEtale_away : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A],
    (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
      Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
    ∀ g ∈ maximalIdeal R, Algebra.FormallyEtale (Localization.Away g)
      (TensorProduct R (Localization.Away g) A) := by
  intro R _ _ _ A _ _ _ he g hg
  set S := Localization.Away g
  set B := S ⊗[R] A
  refine Algebra.etaleLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun Q => ?_)
  show Algebra.FormallyEtale S (Localization.AtPrime Q.asIdeal)
  apply isEtaleAt_of_formallyEtale_baseChange
  set P : Ideal S := Q.asIdeal.under S
  set q : Ideal R := P.under R with hq
  have hqm : q ≠ maximalIdeal R := by
    intro h
    have hgq : g ∈ q := h ▸ hg
    have : algebraMap R S g ∈ P := hgq
    exact (Ideal.IsPrime.ne_top inferInstance)
      (P.eq_top_of_isUnit_mem this (IsLocalization.Away.algebraMap_isUnit g))
  haveI := he q hqm
  haveI : P.LiesOver q := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver q P
  let e : Localization.AtPrime P ⊗[Localization.AtPrime q] (Localization.AtPrime q ⊗[R] A)
      ≃ₐ[Localization.AtPrime P] Localization.AtPrime P ⊗[S] (S ⊗[R] A) :=
    (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime q) (Localization.AtPrime P)
      (Localization.AtPrime P) A).trans
    (Algebra.TensorProduct.cancelBaseChange R S (Localization.AtPrime P)
      (Localization.AtPrime P) A).symm
  haveI : Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[S] (S ⊗[R] A)) :=
    Algebra.Etale.of_equiv e
  infer_instance

end GlobalTheory.EtaleAway
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtaleAwayOfEtaleOffMaximalIdealStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.formallyEtale_away_of_etale_off_maximalIdeal : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ g ∈ maximalIdeal R, Algebra.FormallyEtale (Localization.Away g) (TensorProduct R (Localization.Away g) A) := by
  first | exact @GlobalTheory.EtaleAway.formallyEtale_away | exact GlobalTheory.EtaleAway.formallyEtale_away | (intros; apply GlobalTheory.EtaleAway.formallyEtale_away <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeMaximalIdeal

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem isAdicComplete_of_le_maximalIdeal :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      IsAdicComplete (maximalIdeal R) R → ∀ (I : Ideal R), I ≤ maximalIdeal R →
        IsAdicComplete I R := by
  intro R _ _ _ hm I hI
  exact isAdicComplete_of_le_of_isNoetherianRing R I (maximalIdeal R) hI hm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeMaximalIdealStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.isAdicComplete_of_le_maximalIdeal' : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (I : Ideal R), I ≤ maximalIdeal R → IsAdicComplete I R := by
  first | exact @GlobalTheory.isAdicComplete_of_le_maximalIdeal | exact GlobalTheory.isAdicComplete_of_le_maximalIdeal | (intros; apply GlobalTheory.isAdicComplete_of_le_maximalIdeal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoQuotientPowFreeOverRegularLocalRing

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory


open Pointwise in
theorem modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R,
      f ≠ 0 → ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B]
      [Nontrivial B] (k : ℕ), 1 ≤ k →
      ReciprocityTheory.CA.ModDepthGE R (B ⧸ (Ideal.span {f}).map (algebraMap R B) ^ k) 2 := by
  intro R _ _ hd f hf hf0 B _ _ _ _ _ k hk
  haveI : IsDomain R := GlobalTheory.isDomain_of_isRegularLocalRing R
  have h3 : ReciprocityTheory.CA.ModDepthGE R B 3 :=
    GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing R hd B
  have hfk0 : f ^ k ≠ 0 := pow_ne_zero k hf0
  have hfkm : f ^ k ∈ maximalIdeal R := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [pow_succ]
    exact Ideal.mul_mem_left _ _ hf
  have hreg : IsSMulRegular B (f ^ k) := smul_right_injective B hfk0
  have h2 : ReciprocityTheory.CA.ModDepthGE R (QuotSMulTop (f ^ k) B) 2 :=
    ReciprocityTheory.CA.ModDepthGE.quotSMulTop hfkm hreg h3
  have hpow : (Ideal.span {f}).map (algebraMap R B) ^ k =
      (Ideal.span {f ^ k}).map (algebraMap R B) := by
    rw [← Ideal.map_pow, Ideal.span_singleton_pow]
  have heq : ((f ^ k) • (⊤ : Submodule R B)) =
      ((Ideal.span {f}).map (algebraMap R B) ^ k).restrictScalars R := by
    rw [hpow]
    ext x
    simp [Submodule.mem_smul_pointwise_iff_exists, Ideal.map_span, Ideal.mem_span_singleton',
      Algebra.smul_def, mul_comm]
  let e : QuotSMulTop (f ^ k) B ≃ₗ[R] (B ⧸ (Ideal.span {f}).map (algebraMap R B) ^ k) :=
    (Submodule.quotEquivOfEq _ _ heq).trans
      (Submodule.Quotient.restrictScalarsEquiv R ((Ideal.span {f}).map (algebraMap R B) ^ k))
  exact (ReciprocityTheory.CA.modDepthGE_congr e 2).mp h2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoQuotientPowFreeOverRegularLocalRingStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.modDepthGE_two_quotient_pow_free_over_regularLocalRing : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ≠ 0 → ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B] [Nontrivial B] (k : ℕ), 1 ≤ k → ReciprocityTheory.CA.ModDepthGE R (B ⧸ (Ideal.span {f}).map (algebraMap R B) ^ k) 2 := by
  first | (exact @GlobalTheory.modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing) | (exact GlobalTheory.modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing) | (intros; apply GlobalTheory.modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHomOfEtalePunctured

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory.LiftHom

theorem liftHom_of_etale_punctured : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ≠ 0 → ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B] (φ : A →ₐ[R] B ⧸ (Ideal.span {f}).map (algebraMap R B)), ∃ ψ : A →ₐ[R] B, (Ideal.Quotient.mkₐ R ((Ideal.span {f}).map (algebraMap R B))).comp ψ = φ := by
  intro R _ _ hcomp hdim f hf hf0 A _ _ _ he B _ _ _ _ φ
  have hfe := GlobalTheory.T.formallyEtale_away_of_etale_off_maximalIdeal R A he
  generalize hJ : (Ideal.span {f}).map (algebraMap R B) = J at φ ⊢
  rcases subsingleton_or_nontrivial B with hB | hB
  · refine ⟨default, ?_⟩
    haveI : Subsingleton (B ⧸ J) := Ideal.Quotient.subsingleton_iff.2 (Subsingleton.elim _ _)
    exact AlgHom.ext fun x => Subsingleton.elim _ _
  haveI : IsAdicComplete (Ideal.span {f}) R :=
    GlobalTheory.T.isAdicComplete_of_le_maximalIdeal' R hcomp _ ((Ideal.span_singleton_le_iff_mem _).2 hf)
  haveI : IsAdicComplete J B := hJ ▸ GlobalTheory.isAdicComplete_map_of_finite (Ideal.span {f}) B
  have hd : ∀ k : ℕ, ReciprocityTheory.CA.ModDepthGE R (B ⧸ J ^ (k + 1)) 2 := fun k =>
    hJ ▸ GlobalTheory.T.modDepthGE_two_quotient_pow_free_over_regularLocalRing R hdim f hf hf0 B (k + 1) (Nat.le_add_left 1 k)
  have hle : ∀ k : ℕ, J ^ (k + 2) ≤ J ^ (k + 1) := fun k => Ideal.pow_le_pow_right (by omega)
  have step : ∀ (k : ℕ) (φk : A →ₐ[R] B ⧸ J ^ (k + 1)),
      ∃ ψ : A →ₐ[R] B ⧸ J ^ (k + 2), (Ideal.Quotient.factorₐ R (hle k)).comp ψ = φk := by
    intro k φk
    refine GlobalTheory.T.algHom_lift_squareZero_of_formallyEtale_away_depth R A hfe (B ⧸ J ^ (k + 2)) (B ⧸ J ^ (k + 1)) (hd (k + 1))
      ((hd k).mono (by norm_num)) (Ideal.Quotient.factorₐ R (hle k))
      (Ideal.Quotient.factor_surjective (hle k)) ?_ φk
    rw [pow_two, eq_bot_iff]
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [RingHom.mem_ker] at hx hy
    change Ideal.Quotient.mk _ a = 0 at hx
    change Ideal.Quotient.mk _ b = 0 at hy
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx hy
    rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have : a * b ∈ J ^ (k + 1) * J ^ (k + 1) := Ideal.mul_mem_mul hx hy
    rw [← pow_add] at this
    exact Ideal.pow_le_pow_right (by omega) this
  let φs : (n : ℕ) → A →ₐ[R] B ⧸ J ^ (n + 1) := fun n => Nat.rec
    ((Ideal.quotientEquivAlgOfEq R (pow_one J).symm).toAlgHom.comp φ)
    (fun k φk => Classical.choose (step k φk)) n
  have hφs : ∀ k x, Ideal.Quotient.factor (hle k) (φs (k + 1) x) = φs k x := fun k x =>
    congrArg (fun F : A →ₐ[R] B ⧸ J ^ (k + 1) => F x) (Classical.choose_spec (step k (φs k)))

  have hcc : ∀ {a b c : ℕ} (h1 : J ^ a ≤ J ^ b) (h2 : J ^ b ≤ J ^ c) (y : B ⧸ J ^ a),
      Ideal.Quotient.factor h2 (Ideal.Quotient.factor h1 y) = Ideal.Quotient.factor (h1.trans h2) y := by
    intro a b c h1 h2 y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [Ideal.Quotient.factor_mk]
  have hchain : ∀ m n (hmn : m ≤ n) x,
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : m + 1 ≤ n + 1) : J ^ (n + 1) ≤ J ^ (m + 1))
        (φs n x) = φs m x := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base =>
      intro x
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (φs m x)
      rw [← hb, Ideal.Quotient.factor_mk]
    | succ n hmn ih =>
      intro x
      rw [← ih x, ← hφs n x, hcc]
  let F : (n : ℕ) → A →ₐ[R] B ⧸ J ^ n := fun n =>
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (φs n)
  have hF : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (F n) = F m := by
    intro m n hmn
    ext x
    show Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n)) (φs n x)) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ m)) (φs m x)
    rw [← hchain m n hmn x, hcc, hcc]
  refine ⟨IsAdicComplete.liftAlgHom J F hF, ?_⟩
  ext x
  have h1 := IsAdicComplete.mk_liftAlgHom J F hF 1 x
  have h2 : F 1 x = φs 0 x := hφs 0 x
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (φ x)
  have h3 : φs 0 x = Ideal.Quotient.mk (J ^ 1) b := by
    show (Ideal.quotientEquivAlgOfEq R (pow_one J).symm) (φ x) = _
    rw [← hb]
    rfl
  rw [h2, h3, Ideal.Quotient.eq, pow_one] at h1
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← hb, Ideal.Quotient.eq]
  exact h1

end GlobalTheory.LiftHom
end
end
