module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamAlgebraQuotientRingSurjectiveAndKernelStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Mathlib.RingTheory.Derivation.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationHomotopyOperatorFiltrationPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerPolyAlgebraHomotopyIdentityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAndAugmentationMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDPMorphismOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractionLieDerivativeDivPowerCompatFiltrationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowerCompatRelFiltrationTwoSidedRelEqBotOfBasStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerLinEMulE

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.CrysConn

namespace GlobalTheory.PDA

variable {B : Type} [CommRing B]

def PDPoly.derVal (Q : PDPoly B) : ℕ → Q.P
  | 0 => 0
  | n + 1 => Q.e n

def PDPoly.derLin (Q : PDPoly B) : Q.P →ₗ[B] Q.P := Q.e.constr B Q.derVal

theorem PDPoly.derLin_e (Q : PDPoly B) (n : ℕ) : Q.derLin (Q.e n) = Q.derVal n := by
  simp [PDPoly.derLin, Module.Basis.constr_basis]

theorem PDPoly.derLin_e_succ (Q : PDPoly B) (n : ℕ) : Q.derLin (Q.e (n + 1)) = Q.e n := Q.derLin_e (n + 1)

theorem PDPoly.derLin_e_zero (Q : PDPoly B) : Q.derLin (Q.e 0) = 0 := Q.derLin_e 0

theorem PDPoly.derLin_e_mul_e (Q : PDPoly B) (m n : ℕ) :
    Q.derLin (Q.e m * Q.e n) = Q.e m * Q.derLin (Q.e n) + Q.e n * Q.derLin (Q.e m) := by
  rcases m with _ | a
  · rw [Q.derLin_e_zero, Q.e_zero]; simp
  rcases n with _ | b
  · rw [Q.derLin_e_zero, Q.e_zero]; simp
  rw [Q.derLin_e_succ, Q.derLin_e_succ, Q.e_mul, Q.e_mul, Q.e_mul, ← nsmul_eq_mul, map_nsmul,
    show a + 1 + (b + 1) = (a + b + 1) + 1 by omega, Q.derLin_e_succ, show a + 1 + b = a + b + 1 by omega,
    show b + 1 + a = a + b + 1 by omega, Nat.choose_succ_succ' (a + b + 1) a,
    Nat.choose_symm_of_eq_add (show a + b + 1 = (b + 1) + a by omega)]
  push_cast
  rw [nsmul_eq_mul]
  push_cast
  ring

theorem PDPoly.derLin_mul (Q : PDPoly B) (x y : Q.P) :
    Q.derLin (x * y) = x * Q.derLin y + y * Q.derLin x := by
  have h2 : ∀ x n, Q.derLin (x * Q.e n) = x * Q.derLin (Q.e n) + Q.e n * Q.derLin x := fun x n ↦ by
    have := Q.e.ext (f₁ := Q.derLin ∘ₗ LinearMap.mulRight B (Q.e n))
      (f₂ := LinearMap.mulRight B (Q.derLin (Q.e n)) + LinearMap.mulLeft B (Q.e n) ∘ₗ Q.derLin)
      (fun m ↦ by simpa using Q.derLin_e_mul_e m n)
    simpa using LinearMap.congr_fun this x
  have := Q.e.ext (f₁ := Q.derLin ∘ₗ LinearMap.mulLeft B x)
    (f₂ := LinearMap.mulLeft B x ∘ₗ Q.derLin + LinearMap.mulRight B (Q.derLin x))
    (fun n ↦ by simpa using h2 x n)
  simpa using LinearMap.congr_fun this y

def PDPoly.der (Q : PDPoly B) : Derivation B Q.P Q.P :=
  Derivation.mk' Q.derLin fun x y ↦ by simpa [smul_eq_mul] using Q.derLin_mul x y

theorem PDPoly.der_apply (Q : PDPoly B) (x : Q.P) : Q.der x = Q.derLin x := rfl

end GlobalTheory.PDA

namespace GlobalTheory.PDA

variable {B : Type} [CommRing B]

theorem PDPoly.der_dpow_succ {J : Ideal B} (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (n : ℕ) {a : Q.P} (ha : a ∈ Q.ext J) :
    Q.der (η.dpow (n + 1) a) = η.dpow n a * Q.der a := by
  set D := Q.der
  let P : Q.P → Prop := fun a ↦ ∀ n, D (η.dpow n a) = dpPred η n a • D a
  have hzero : P 0 := fun n ↦ by
    cases n with
    | zero => simp [η.dpow_zero (Q.ext J).zero_mem]
    | succ n => simp [dpow_eval_zero _ n.succ_ne_zero]
  have hadd : ∀ a ∈ Q.ext J, ∀ b ∈ Q.ext J, P a → P b → P (a + b) := fun a ha b hb iha ihb n ↦ by
    have iha : ∀ n, D (η.dpow n a) = dpPred η n a • D a := iha
    have ihb : ∀ n, D (η.dpow n b) = dpPred η n b • D b := ihb

    simp only [η.dpow_add ha hb, map_sum, D.leibniz, iha, ihb, smul_smul, Finset.sum_add_distrib,
    ← Finset.sum_smul, sum_dpow_mul_dpPred η ha hb, sum_dpow_mul_dpPred' η ha hb, map_add, smul_add]
    exact add_comm _ _
  have hmul : ∀ r, ∀ a ∈ Q.ext J, P a → P (r * a) := fun r a ha hP n ↦ by
    cases n with
    | zero => simp [η.dpow_zero (Ideal.mul_mem_left _ r ha), dpPred]
    | succ m =>
      have hm := hP (m + 1)
      have hs := dpPred_mul_self η ha (m + 1)
      simp only [dpPred, smul_eq_mul] at hm hs ⊢
      rw [η.dpow_mul ha, η.dpow_mul ha, D.leibniz, D.leibniz, D.leibniz_pow, hm]
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
      push_cast at hs ⊢
      linear_combination (-(r ^ m * D r)) * hs
  have hspan : ∀ s : Set Q.P, s ⊆ Q.ext J → (∀ x ∈ s, P x) → ∀ a ∈ Ideal.span s, P a := by
    intro s hs hP a ha
    have hle : Ideal.span s ≤ Q.ext J := Ideal.span_le.2 hs
    induction ha using Submodule.span_induction with
    | mem x hx => exact hP x hx
    | zero => exact hzero
    | add x y hx hy ihx ihy => exact hadd x (hle hx) y (hle hy) ihx ihy
    | smul r x hx ih => exact hmul r x (hle hx) ih
  have hJ : ∀ x ∈ J.map (algebraMap B Q.P), P x := by
    refine hspan _ ?_ ?_
    · rintro _ ⟨j, hj, rfl⟩; exact Q.algebraMap_mem_ext hj
    · rintro _ ⟨j, hj, rfl⟩ n
      rw [h.dp.2 j hj, Derivation.map_algebraMap, Derivation.map_algebraMap, smul_zero]
  have he1 := Q.e_one_mem_ext J
  have hA : ∀ x ∈ Q.aug, P x := by
    refine hspan _ ?_ ?_
    · rintro _ ⟨k, rfl⟩; exact Ideal.mem_sup_right (Q.e_succ_mem_aug k)
    · rintro _ ⟨k, rfl⟩ n
      cases n with
      | zero => simp [η.dpow_zero (Ideal.mem_sup_right (Q.e_succ_mem_aug k)), dpPred]
      | succ m =>
        have c1 : η.dpow (m + 1) (Q.e (k + 1)) =
            (Nat.uniformBell (m + 1) (k + 1) : Q.P) * Q.e ((m * (k + 1) + k) + 1) := by
          rw [← h.var (k + 1), η.dpow_comp (by omega) he1, h.var, show (m + 1) * (k + 1) = m * (k + 1) + k + 1 by ring]
        have c2 : dpPred η (m + 1) (Q.e (k + 1)) * Q.e k =
            (Nat.uniformBell (m + 1) (k + 1) : Q.P) * Q.e (m * (k + 1) + k) := by
          have := dpPred_dpow η he1 (m + 1) (n := k + 1) (by omega)
          rw [h.var, show dpPred η (k + 1) (Q.e 1) = Q.e k from h.var k,
            show (m + 1) * (k + 1) = m * (k + 1) + k + 1 by ring,
            show dpPred η (m * (k + 1) + k + 1) (Q.e 1) = Q.e (m * (k + 1) + k) from h.var _] at this
          exact this
        rw [c1, D.leibniz, D.map_natCast, smul_zero, add_zero, smul_eq_mul, smul_eq_mul, Q.der_apply,
          Q.der_apply, Q.derLin_e_succ, Q.derLin_e_succ, c2]
  have hall : ∀ x ∈ Q.ext J, P x := fun x hx ↦ by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    exact hadd y (Ideal.mem_sup_left hy) z (Ideal.mem_sup_right hz) (hJ y hy) (hA z hz)
  simpa [dpPred, smul_eq_mul] using hall a ha (n + 1)

theorem PDPoly.exists_der (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) :
    Q.IsStd δ η → ∃ D : Derivation R Q.P Q.P, (∀ b, D (algebraMap B Q.P b) = 0) ∧
      (∀ n, D (Q.e (n + 1)) = Q.e n) ∧ ∀ n, ∀ a ∈ Q.ext J, D (η.dpow (n + 1) a) = η.dpow n a * D a := by
  intro h
  refine ⟨Q.der.restrictScalars R, fun b ↦ ?_, fun n ↦ ?_, fun n a ha ↦ ?_⟩
  · rw [Derivation.restrictScalars_apply, Derivation.map_algebraMap]
  · rw [Derivation.restrictScalars_apply, Q.der_apply, Q.derLin_e_succ]
  · simp only [Derivation.restrictScalars_apply]
    exact Q.der_dpow_succ δ η h n ha

end GlobalTheory.PDA
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientDividedPowerFiltrationCompatibleForms

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

namespace GlobalTheory.PDForm

theorem quot_fil_rel : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : B →+* G) (h : SemiHom (RingHom.id R) q) (n : ℕ), IsDPMorphism δ δ' q → Function.Surjective q → J' = J.map q → (∀ b, q b = 0 ↔ b ∈ fil δ (n + 1)) → (∀ x, h.mDR x ∈ rel R δ' → x ∈ filDR R δ n) ∧ ∀ x ∈ filDR R δ (n + 1), h.mDR x ∈ rel R δ' := by
  intro R B _ _ _ J δ G _ _ J' δ' q h n hd hq hJ hk
  obtain ⟨-, -, hsurj, hker⟩ := GlobalTheory.T.deRhamAlgebra_quotientRing_surjective_and_kernel R B G q h hq
  obtain ⟨-, -, hmul, -, -, hanti, -⟩ := (GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base).1 R B J δ
  have hv : ∀ m, ∀ a ∈ J, (0 : Derivation R B B) (δ.dpow (m + 1) a) = δ.dpow m a * (0 : Derivation R B B) a := by
    intro m a _; simp
  have hd0 := ((GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules).2 R B J δ 0 hv n).2.1
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  ·
    have hle : rel R δ' ≤ (rel R δ).map h.mDR := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨m, a', ha', rfl⟩
      rw [hJ, Ideal.mem_map_iff_of_surjective _ hq] at ha'
      obtain ⟨a, ha, rfl⟩ := ha'
      have e : ι1 (D R G (δ'.dpow (m + 1) (q a)) - δ'.dpow m (q a) • D R G (q a)) =
          h.mDR (ι1 (D R B (δ.dpow (m + 1) a) - δ.dpow m a • D R B a)) := by
        rw [h.mDR_ι, map_sub h.m1, h.m1_D, h.oneFormMap_smul_semilinear, h.m1_D, hd.2 a ha, hd.2 a ha]
      rw [e]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨m, a, ha, rfl⟩)
    obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 (hle hx)
    have hK : x - y ∈ filDR R δ n := by
      refine hker (filDR R δ n) (hmul n) (fun b hb ↦ ?_) (x - y) (by rw [map_sub, hxy, sub_self])
      have hb1 : algebraMap B (DR R B) b ∈ filDR R δ (n + 1) :=
        Ideal.mem_sup_left (Ideal.subset_span ⟨b, (hk b).1 hb, rfl⟩)
      refine ⟨hanti n (n + 1) (Nat.le_succ n) hb1, ?_⟩
      rw [← dDR_algebraMap]
      exact hd0 _ hb1
    have hyn : y ∈ filDR R δ n := Ideal.mem_sup_right hy
    simpa using add_mem hK hyn
  · have hle : filDR R δ (n + 1) ≤ (rel R δ').comap h.mDR := by
      refine sup_le (Ideal.span_le.2 ?_) (fun z hz ↦ mDR_mem_rel h hd hz)
      rintro _ ⟨b, hb, rfl⟩
      change h.mDR (algebraMap B _ b) ∈ rel R δ'
      rw [h.mDR_algebraMap, (hk b).2 hb, map_zero]
      exact zero_mem _
    exact hle hx

end GlobalTheory.PDForm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientDividedPowerFiltrationCompatibleFormsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.quotient_dividedPowerFiltration_compatibleForms : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : B →+* G) (h : SemiHom (RingHom.id R) q) (n : ℕ), IsDPMorphism δ δ' q → Function.Surjective q → J' = J.map q → (∀ b, q b = 0 ↔ b ∈ fil δ (n + 1)) → (∀ x, h.mDR x ∈ rel R δ' → x ∈ filDR R δ n) ∧ ∀ x ∈ filDR R δ (n + 1), h.mDR x ∈ rel R δ' := by
  first | exact @GlobalTheory.PDForm.quot_fil_rel | exact GlobalTheory.PDForm.quot_fil_rel | (intros; apply GlobalTheory.PDForm.quot_fil_rel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLemmaTruncatedDivPowerPolyOneVariable

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.Poincare

theorem eq_zero_of_algebraMap_mem_rel {R G : Type} [CommRing R] [CommRing G] [Algebra R G] {J' : Ideal G}
    (δ' : DividedPowers J') (g : G) (hg : algebraMap G (DR R G) g ∈ rel R δ') : g = 0 := by
  have hle : rel R δ' ≤ RingHom.ker (ExteriorAlgebra.algebraMapInv (R := G) (M := Ω[G⁄R])).toRingHom := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨m, a, _, rfl⟩
    simp [ExteriorAlgebra.algebraMapInv]
  have := hle hg
  rw [RingHom.mem_ker] at this
  simpa [ExteriorAlgebra.algebraMap_leftInverse _ g] using this

theorem mDR_mDR {R R' R'' B B' B'' : Type} [CommRing R] [CommRing B] [Algebra R B]
    [CommRing R'] [CommRing B'] [Algebra R' B'] [CommRing R''] [CommRing B''] [Algebra R'' B'']
    {σ : R →+* R'} {α : B →+* B'} {τ : R' →+* R''} {β : B' →+* B''} {ρ : R →+* R''} {γ : B →+* B''}
    (h : SemiHom σ α) (h' : SemiHom τ β) (h'' : SemiHom ρ γ) (e : ∀ b, β (α b) = γ b) (x : DR R B) :
    h'.mDR (h.mDR x) = h''.mDR x := by
  induction x using indDR with
  | h b => simp [e]
  | hd b => simp [e]
  | hm x y hx hy => simp only [map_mul, hx, hy]
  | ha x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.PDForm.Poincare


open GlobalTheory.PDForm.Poincare in
theorem GlobalTheory.PDForm.rq_truncPoly : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : Q.P →+* G) (n : ℕ), Q.IsStd δ η → IsLev δ (n + 1) → SemiHom (RingHom.id R) q → IsDPMorphism η δ' q → Function.Surjective q → J' = (Q.ext J).map q → (∀ b, q b = 0 ↔ b ∈ fil η (n + 1)) → ∀ (α : B →+* G) (h : SemiHom (RingHom.id R) α) (hd : IsDPMorphism δ δ' α), (∀ b, α b = q (algebraMap B Q.P b)) → RQ h hd := by
  intro R B _ _ _ J δ Q _ _ η G _ _ J' δ' q n hstd hlev hq hqd hqs hJ' hker α h hd hα

  obtain ⟨ε, hεs, hεd, hεb, hεe⟩ : ∃ ε : Q.P →+* B, SemiHom (RingHom.id R) ε ∧ IsDPMorphism η δ ε ∧
      (∀ b, ε (algebraMap B Q.P b) = b) ∧ ∀ k, ε (Q.e (k + 1)) = 0 := by
    obtain ⟨ε0, hε0⟩ := (GlobalTheory.PDA.PDPoly.exists_lift_and_aug B Q).2
    have hb : ∀ b, ε0 (algebraMap B Q.P b) = b := fun b ↦ ε0.commutes b
    refine ⟨ε0, fun r p ↦ ?_, ?_, hb, fun k ↦ (hε0 _).1 (Q.e_succ_mem_aug k)⟩
    · change ε0 (r • p) = r • ε0 p
      rw [← algebraMap_smul B r p, map_smul, algebraMap_smul]
    · refine GlobalTheory.PDA.PDPoly.isDPMorphism_of_isStd B J δ Q η hstd B J δ ε0 0 J.zero_mem ⟨?_, ?_⟩ ?_
      · intro x hx
        rw [Ideal.mem_map_iff_of_surjective _ (fun b ↦ ⟨b, hb b⟩)] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        simpa [hb] using hy
      · intro k a _
        simp [hb]
      · intro k
        cases k with
        | zero => change ε0 (Q.e 0) = _; rw [Q.e_zero, map_one, δ.dpow_zero J.zero_mem]
        | succ k => change ε0 (Q.e (k + 1)) = _; rw [(hε0 _).1 (Q.e_succ_mem_aug k), δ.dpow_eval_zero (Nat.succ_ne_zero k)]
  have hi : SemiHom (RingHom.id R) (algebraMap B Q.P) := fun r b ↦ map_smul (IsScalarTower.toAlgHom R B Q.P) r b

  have hkε : ∀ p, q p = 0 → ε p = 0 := by
    intro p hp
    have h1 : ε p ∈ fil δ (n + 1) :=
      (GlobalTheory.PDA.fil_properties Q.P (Q.ext J) η).2.2.2.2.2.2 B J δ ε hεd (n + 1) (Ideal.mem_map_of_mem _ ((hker p).1 hp))
    rw [hlev] at h1
    exact (Ideal.mem_bot).1 h1
  obtain ⟨eb, hebq⟩ : ∃ eb : G →+* B, ∀ p, eb (q p) = ε p :=
    ⟨q.liftOfRightInverse (Function.surjInv hqs) (Function.rightInverse_surjInv hqs) ⟨ε, fun p hp ↦ hkε p hp⟩,
      fun p ↦ RingHom.liftOfRightInverse_comp_apply _ _ _ _ p⟩
  have hebα : ∀ b, eb (α b) = b := fun b ↦ by rw [hα, hebq, hεb]
  have heb : SemiHom (RingHom.id R) eb := by
    intro r g
    obtain ⟨p, rfl⟩ := hqs g
    have := hq r p
    simp only [RingHom.id_apply] at this ⊢
    rw [← this, hebq, hebq]
    simpa using hεs r p
  have hdeb : IsDPMorphism δ' δ eb := by
    have hc : eb.comp q = ε := RingHom.ext hebq
    refine ⟨?_, ?_⟩
    · rw [hJ', Ideal.map_map, hc]; exact hεd.1
    · intro k a ha
      rw [hJ', Ideal.mem_map_iff_of_surjective _ hqs] at ha
      obtain ⟨a, ha, rfl⟩ := ha
      rw [hebq, hqd.2 a ha, hebq, hεd.2 a ha]
  have hid : SemiHom (RingHom.id R) (RingHom.id B) := fun _ _ ↦ rfl
  have hdid : IsDPMorphism δ δ (RingHom.id B) := (DPMorphism.id δ).isDPMorphism
  have ret1 : ∀ x, km1 heb hdeb (km1 h hd x) = x := fun x ↦
    (divPowerCompatOneFormMap_comp h hd heb hdeb hid hdid hebα x).trans (divPowerCompatOneFormMap_id hid hdid (fun _ ↦ rfl) x)
  have ret : ∀ j x, km heb hdeb j (km h hd j x) = x := fun j x ↦
    (km_km h hd heb hdeb hid hdid hebα j x).trans (km_id hid hdid (fun _ ↦ rfl) j x)

  obtain ⟨v, hv0, hv1, hv2⟩ := GlobalTheory.PDA.PDPoly.exists_der R B J δ Q η hstd
  have he : ∀ k, Q.e k ∈ fil η k := fun k ↦ by
    rw [← hstd.var k]
    exact (GlobalTheory.PDA.fil_properties Q.P (Q.ext J) η).2.2.2.2.1 k _ (Q.e_one_mem_ext J)
  have hht := GlobalTheory.T.derivationHomotopyOperator_filtration_properties R Q.P (Q.ext J) η v Q.e (n + 1) hv2 he
  have kq := GlobalTheory.T.quotient_dividedPowerFiltration_compatibleForms R Q.P (Q.ext J) η G J' δ' q hq n hqd hqs hJ' hker
  have kdr := GlobalTheory.T.deRhamAlgebra_quotientRing_surjective_and_kernel R Q.P G q hq hqs
  have key : ∀ X : DR R Q.P, hq.mDR (dDR R Q.P X) ∈ rel R δ' →
      hq.mDR X - h.mDR (hεs.mDR X) - dDR R G (hq.mDR (hot v Q.e (n + 1) X)) ∈ rel R δ' := by
    intro X hX
    have hT := hht.2.2.2.2 n _ (kq.1 _ hX)
    have hH := GlobalTheory.T.dividedPowerPolyAlgebra_homotopy_identity R B J δ Q η v hi hstd hv0 hv1 hv2 ε hεs hεd hεb hεe (n + 1) X
    have h3 := add_mem hH hT
    rw [sub_add_cancel] at h3
    have := kq.2 _ h3
    rwa [map_sub, map_sub, mDR_mDR hi hq h (fun b ↦ (hα b).symm), hq.mDR_dDR] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x _ hx
    have hx' : α x = 0 := hx
    rw [← hebα x, hx', map_zero]
  ·
    intro y hy
    obtain ⟨p, rfl⟩ := hqs y
    have hy' : hq.mDR (dDR R Q.P (algebraMap Q.P (DR R Q.P) p)) ∈ rel R δ' := by
      rw [dDR_algebraMap, hq.mDR_ι, hq.m1_D]
      exact (Submodule.Quotient.mk_eq_zero (N1 R δ')).1 (by rw [← divPowerCompatFunctionDifferential_apply]; exact hy)
    have hk := key _ hy'
    rw [(hht.2.1 p), map_zero, map_zero, sub_zero, hq.mDR_algebraMap, hεs.mDR_algebraMap, h.mDR_algebraMap,
      ← map_sub] at hk
    have hp : q p = α (ε p) := sub_eq_zero.1 (eq_zero_of_algebraMap_mem_rel δ' _ hk)
    refine ⟨ε p, ?_, hp.symm⟩
    have h0 : km1 h hd (kd0 R δ (ε p)) = 0 := by rw [divPowerCompatOneFormMap_functionDifferential, ← hp]; exact hy
    rw [← ret1 (kd0 R δ (ε p)), h0, map_zero]
  ·
    intro x y _ hxy
    refine ⟨eb y, ?_⟩
    rw [← divPowerCompatOneFormMap_functionDifferential heb hdeb, ← hxy, ret1]
  ·
    intro y hy
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨ω, rfl⟩ := kdr.1 y
    have hy' : hq.mDR (dDR R Q.P (ι1 ω)) ∈ rel R δ' := by
      rw [hq.mDR_dDR, hq.mDR_ι]
      exact (Submodule.Quotient.mk_eq_zero (N R δ' 2)).1 (by rw [← divPowerCompatOneFormDerivative_mk]; exact hy)
    obtain ⟨c, hc⟩ : ∃ c, algebraMap Q.P (DR R Q.P) c = hot v Q.e (n + 1) (ι1 ω) := by
      have := hht.2.2.1 0 _ (ι_mem ω)
      change _ ∈ LinearMap.range _ ^ 0 at this
      rwa [pow_zero, Submodule.mem_one] at this
    have hk := key _ hy'
    rw [← hc, hq.mDR_algebraMap, dDR_algebraMap, hq.mDR_ι, hεs.mDR_ι, h.mDR_ι, ← map_sub, ← map_sub] at hk
    set x : K1 R δ := Submodule.Quotient.mk (hεs.m1 ω) with hxdef
    have heq : (Submodule.Quotient.mk (hq.m1 ω) : K1 R δ') = km1 h hd x + kd0 R δ' (q c) := by
      rw [divPowerCompatOneFormMap_mk, divPowerCompatFunctionDifferential_apply, ← Submodule.Quotient.mk_add, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
        Submodule.Quotient.mk_eq_zero, ← sub_sub]
      exact hk
    refine ⟨x, q c, ?_, heq⟩
    have h0 : km h hd 2 (kd1 R δ x) = 0 := by
      rw [divPowerCompatFormMap_oneFormDerivative, show km1 h hd x = Submodule.Quotient.mk (hq.m1 ω) - kd0 R δ' (q c) by rw [heq]; abel,
        map_sub, divPowerCompatOneFormDerivative_comp_differential, sub_zero]
      exact hy
    rw [← ret 2 (kd1 R δ x), h0, map_zero]
  ·
    intro x y _ hxy
    refine ⟨km1 heb hdeb y, ?_⟩
    rw [← divPowerCompatFormMap_oneFormDerivative heb hdeb, ← hxy, ret]
  ·
    intro y hy
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨ω, rfl⟩ := kdr.2.1 2 y
    have hy' : hq.mDR (dDR R Q.P (ω : DR R Q.P)) ∈ rel R δ' := by
      rw [hq.mDR_dDR]
      exact (Submodule.Quotient.mk_eq_zero (N R δ' 3)).1 (by rw [← divPowerCompatTwoFormDerivative_mk]; exact hy)
    obtain ⟨c, hc⟩ : ∃ c, ι1 c = hot v Q.e (n + 1) (ω : DR R Q.P) := by
      have := hht.2.2.1 1 _ ω.2
      change _ ∈ LinearMap.range _ ^ 1 at this
      rwa [pow_one] at this
    have hk := key _ hy'
    rw [← hc, hq.mDR_ι] at hk
    set x : K R δ 2 := Submodule.Quotient.mk (hεs.mOm 2 ω) with hxdef
    have heq : (Submodule.Quotient.mk (hq.mOm 2 ω) : K R δ' 2) = km h hd 2 x + kd1 R δ' (Submodule.Quotient.mk (hq.m1 c)) := by
      rw [km_mk, divPowerCompatOneFormDerivative_mk, ← Submodule.Quotient.mk_add, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
        Submodule.Quotient.mk_eq_zero, ← sub_sub]
      exact hk
    refine ⟨x, Submodule.Quotient.mk (hq.m1 c), ?_, heq⟩
    have h0 : km h hd 3 (kd2 R δ x) = 0 := by
      rw [divPowerCompatFormMap_twoFormDerivative, show km h hd 2 x = Submodule.Quotient.mk (hq.mOm 2 ω) - kd1 R δ' (Submodule.Quotient.mk (hq.m1 c)) by
        rw [heq]; abel, map_sub, divPowerCompatTwoFormDerivative_comp_oneForm, sub_zero]
      exact hy
    rw [← ret 3 (kd2 R δ x), h0, map_zero]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLemmaTruncatedDivPowerPolyOneVariableStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.poincareLemma_truncated_divPowerPoly_oneVariable : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : Q.P →+* G) (n : ℕ), Q.IsStd δ η → IsLev δ (n + 1) → SemiHom (RingHom.id R) q → IsDPMorphism η δ' q → Function.Surjective q → J' = (Q.ext J).map q → (∀ b, q b = 0 ↔ b ∈ fil η (n + 1)) → ∀ (α : B →+* G) (h : SemiHom (RingHom.id R) α) (hd : IsDPMorphism δ δ' α), (∀ b, α b = q (algebraMap B Q.P b)) → RQ h hd := by
  first | exact @GlobalTheory.PDForm.rq_truncPoly | exact GlobalTheory.PDForm.rq_truncPoly | (intros; apply GlobalTheory.PDForm.rq_truncPoly <;> assumption)
end
end
