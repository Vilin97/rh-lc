module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUnique
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagOneUnitConjLiftsSl2IntReductionModStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantPowMulSlashTwelveMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QConjTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionsCoeffwiseConjugateRingClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VactVmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjugateFamilyOfInjectiveStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSlTwoPermutedModularFamilyOfLevelStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeierstrassPFamilySeparatingGl2ZModStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateModularFamilyAlongSeparatingFamily

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem conj_family_sep : ∀ (g : ℂ ≃+* ℂ) (ι : Type) [Fintype ι] (act act' : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t t' F : ι → ℍ → ℂ), 0 < N → ActBij act → ActBij act' → IsFam act m t → IsFam act' m t' → IsFam act k F → (∀ i j, t i = t j → F i = F j) → (∀ i, QConj g N (t i) (t' i)) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ F' : ι → ℍ → ℂ, IsFam act' k F' ∧ ∀ i, QConj g N (F i) (F' i) := by
  intro g ι _ act act' m k N t t' F hN hA hA' ht ht' hF htF hc hq
  classical

  have key : ∀ i j, t i = t j ↔ t' i = t' j := by
    intro i j
    obtain ⟨a, ha, ha'⟩ := hc i
    obtain ⟨b, hb, hb'⟩ := hc j
    constructor
    · intro h
      have hab : a = b := HasQ.coeff_unique hN ha (h ▸ hb)
      subst hab
      exact HasQ.fun_unique ha' hb'
    · intro h
      have hab : (fun n => g (a n)) = fun n => g (b n) := HasQ.coeff_unique hN ha' (h ▸ hb')
      have : a = b := funext fun n => g.injective (congrFun hab n)
      subst this
      exact HasQ.fun_unique ha hb
  let s : Setoid ι := Setoid.ker t
  let κ := Quotient s
  have hs : ∀ i j, (Quotient.mk s i = Quotient.mk s j) ↔ t i = t j := fun i j =>
    ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
  haveI : Fintype κ := Fintype.ofFinite κ
  let actκ : κ → SL(2, ℤ) → κ := fun c γ =>
    Quotient.lift (fun i => Quotient.mk s (act i γ)) (fun i j (h : t i = t j) => by
      apply (hs _ _).2
      rw [← ht i γ, ← ht j γ, h]) c
  let actκ' : κ → SL(2, ℤ) → κ := fun c γ =>
    Quotient.lift (fun i => Quotient.mk s (act' i γ)) (fun i j (h : t i = t j) => by
      apply (hs _ _).2
      rw [key, ← ht' i γ, ← ht' j γ, (key i j).1 h]) c
  let tκ : κ → ℍ → ℂ := fun c => Quotient.lift t (fun i j (h : t i = t j) => h) c
  let tκ' : κ → ℍ → ℂ := fun c => Quotient.lift t' (fun i j (h : t i = t j) => (key i j).1 h) c
  let Fκ : κ → ℍ → ℂ := fun c => Quotient.lift F (fun i j (h : t i = t j) => htF i j h) c
  have bij : ∀ (a : ι → SL(2, ℤ) → ι) (aκ : κ → SL(2, ℤ) → κ), ActBij a →
      (∀ i γ, aκ (Quotient.mk s i) γ = Quotient.mk s (a i γ)) → ActBij aκ := by
    intro a aκ hB hcomp γ
    rw [← Finite.surjective_iff_bijective]
    intro c
    induction c using Quotient.inductionOn with
    | h i =>
      obtain ⟨j, hj⟩ := (hB γ).2 i
      exact ⟨Quotient.mk s j, by simp only [hcomp, hj]⟩
  have hAκ : ActBij actκ := bij act actκ hA (fun _ _ => rfl)
  have hAκ' : ActBij actκ' := bij act' actκ' hA' (fun _ _ => rfl)
  have htκ : IsFam actκ m tκ := by
    intro c γ
    induction c using Quotient.inductionOn with
    | h i => exact ht i γ
  have htκ' : IsFam actκ' m tκ' := by
    intro c γ
    induction c using Quotient.inductionOn with
    | h i => exact ht' i γ
  have hFκ : IsFam actκ k Fκ := by
    intro c γ
    induction c using Quotient.inductionOn with
    | h i => exact hF i γ
  have hinj : Function.Injective tκ := by
    intro c d h
    induction c using Quotient.inductionOn with
    | h i =>
      induction d using Quotient.inductionOn with
      | h j => exact (hs i j).2 h
  have hcκ : ∀ c, QConj g N (tκ c) (tκ' c) := by
    intro c
    induction c using Quotient.inductionOn with
    | h i => exact hc i
  have hqκ : ∀ c, ∃ a, HasQ N (Fκ c) a := by
    intro c
    induction c using Quotient.inductionOn with
    | h i => exact hq i
  obtain ⟨G, hG, hGc⟩ := GlobalTheory.T.exists_conjugate_family_of_injective g κ actκ actκ' m k N tκ tκ' Fκ hN hAκ hAκ' htκ htκ' hFκ hinj hcκ hqκ
  refine ⟨fun i => G (Quotient.mk s i), ?_, fun i => hGc (Quotient.mk s i)⟩
  intro i γ
  exact hG (Quotient.mk s i) γ

end GlobalTheory.FN
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateModularFamilyAlongSeparatingFamilyStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.conjugate_modularFamily_along_separatingFamily : ∀ (g : ℂ ≃+* ℂ) (ι : Type) [Fintype ι] (act act' : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t t' F : ι → ℍ → ℂ), 0 < N → ActBij act → ActBij act' → IsFam act m t → IsFam act' m t' → IsFam act k F → (∀ i j, t i = t j → F i = F j) → (∀ i, QConj g N (t i) (t' i)) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ F' : ι → ℍ → ℂ, IsFam act' k F' ∧ ∀ i, QConj g N (F i) (F' i) := by
  first | exact @GlobalTheory.FN.conj_family_sep | exact GlobalTheory.FN.conj_family_sep | (intros; apply GlobalTheory.FN.conj_family_sep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityConjugateFormLevel

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNConj

theorem slash_neg_one_even {k : ℤ} (hk : Even k) (f : ℍ → ℂ) : f ∣[k] (-1 : SL(2, ℤ)) = f := by
  ext τ
  simp only [ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul, one_smul]
  have : UpperHalfPlane.denom ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = (-1) * UpperHalfPlane.denom ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ := by
    simp [UpperHalfPlane.denom]
  rw [this, mul_zpow, (hk.neg).neg_one_zpow]
  simp [UpperHalfPlane.denom]

theorem redGL_neg_one (N : ℕ) : redGL N (-1) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [redGL, Matrix.SpecialLinearGroup.coe_neg]

theorem redGL_gamma (N : ℕ) (γ : SL(2, ℤ)) (h : γ ∈ CongruenceSubgroup.Gamma N) : redGL N γ = 1 := by
  rw [CongruenceSubgroup.Gamma_mem] at h
  obtain ⟨h00, h01, h10, h11⟩ := h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [redGL, h00, h01, h10, h11]

end GlobalTheory.FNConj

namespace GlobalTheory.FNConj

theorem main : ∀ (g : ℂ ≃+* ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (k : ℕ) (f : ℍ → ℂ), ZetaAct g N d → Even k →
    (∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[(k : ℤ)] γ = f) → (∀ γ : SL(2, ℤ), ∃ a, HasQ N (f ∣[(k : ℤ)] γ) a) →
    ∃ f' : ℍ → ℂ, (∀ γ ∈ CongruenceSubgroup.Gamma N, f' ∣[(k : ℤ)] γ = f') ∧
      ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d → QConj g N (f ∣[(k : ℤ)] γ) (f' ∣[(k : ℤ)] γ') := by
  intro g N _ d k f hg hk hinv hq
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨hvact, hgact, hvass, -, -, -, -, -, -⟩ := GlobalTheory.WpFam.Act.rightActions N
  obtain ⟨c₁, c₂, hsep⟩ := GlobalTheory.T.exists_weierstrassP_family_separating_gl2ZMod N
  obtain ⟨-, hadd, hsmul, -⟩ := GlobalTheory.QFam.isFam_algebra (GL (Fin 2) (ZMod N)) (gact N 1)
  obtain ⟨-, hadd', hsmul', -⟩ := GlobalTheory.QFam.isFam_algebra (GL (Fin 2) (ZMod N)) (gact N (dg d))
  obtain ⟨qc, qadd, -, qmul, -⟩ := GlobalTheory.QFam.qConj_ring g N hN

  set t : GL (Fin 2) (ZMod N) → ℍ → ℂ := fun α τ => wp N (vmul ![1, 0] α) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] α) τ +
    (c₂ : ℂ) * wp N (vmul ![1, 1] α) τ with ht
  set t' : GL (Fin 2) (ZMod N) → ℍ → ℂ := fun α => t (α * dg d) with ht'
  have hw : ∀ e : Fin 2 → ZMod N, IsFam (gact N 1) 2 (fun α => wp N (vmul e α)) := fun e => by
    have := (GlobalTheory.WpFamGL.main N 1 e).1
    simpa only [mul_one] using this
  have hw' : ∀ e : Fin 2 → ZMod N, IsFam (gact N (dg d)) 2 (fun α => wp N (vmul e (α * dg d))) := fun e =>
    (GlobalTheory.WpFamGL.main N (dg d) e).1
  have htF : IsFam (gact N 1) 2 t :=
    (hadd _ _ _ (hadd _ _ _ (hw _) (hsmul _ _ _ (hw _))).1 (hsmul _ _ _ (hw _))).1
  have htF' : IsFam (gact N (dg d)) 2 t' :=
    (hadd' _ _ _ (hadd' _ _ _ (hw' _) (hsmul' _ _ _ (hw' _))).1 (hsmul' _ _ _ (hw' _))).1
  have hqw : ∀ (e : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)),
      QConj g N (wp N (vmul e α)) (wp N (vmul e (α * dg d))) := fun e α => by
    rw [← hvass]
    exact (GlobalTheory.WpFam.ConjExp.qConj_torsion N g d hg (vmul e α)).1
  have hqn : ∀ (c : ℕ) (e : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)),
      QConj g N (fun τ => (c : ℂ) * wp N (vmul e α) τ) (fun τ => (c : ℂ) * wp N (vmul e (α * dg d)) τ) := by
    intro c e α
    have := qmul _ _ _ _ (qc (c : ℂ)) (hqw e α)
    simpa only [map_natCast] using this
  have htq : ∀ α, QConj g N (t α) (t' α) := fun α =>
    qadd _ _ _ _ (qadd _ _ _ _ (hqw _ α) (hqn c₁ _ α)) (hqn c₂ _ α)

  obtain ⟨F, hF, hFγ, hF0⟩ := GlobalTheory.T.exists_slTwoPermutedModularFamily_of_level N (k : ℤ) f hinv
  have hFneg : ∀ α, F (-α) = F α := fun α => by
    have h1 := hF α (-1)
    rw [slash_neg_one_even (by exact_mod_cast hk.natCast) (F α)] at h1
    rw [h1, gact_one, redGL_neg_one, mul_neg_one]
  have hsepF : ∀ i j, t i = t j → F i = F j := fun i j h => by
    rcases hsep i j h with rfl | rfl
    · rfl
    · exact hFneg j
  have hFq : ∀ i, ∃ a, HasQ N (F i) a := fun i => by
    rcases hF0 i with ⟨γ, rfl⟩ | h0
    · rw [hFγ]; exact hq γ
    · refine ⟨fun _ => 0, fun τ => ?_⟩
      rw [h0]; simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  obtain ⟨F', hF', hFF'⟩ := GlobalTheory.T.conjugate_modularFamily_along_separatingFamily g (GL (Fin 2) (ZMod N)) (gact N 1) (gact N (dg d)) 2 k N t t' F hN
    (IsRAct.actBij (hgact 1)) (IsRAct.actBij (hgact (dg d))) htF htF' hF hsepF htq hFq
  have hslash : ∀ γ : SL(2, ℤ), F' 1 ∣[(k : ℤ)] γ = F' (dg d * redGL N γ * (dg d)⁻¹) := fun γ => by
    rw [hF' 1 γ, gact, one_mul]
  refine ⟨F' 1, fun γ hγ => ?_, fun γ γ' hγγ' => ?_⟩
  · rw [hslash, redGL_gamma N γ hγ, mul_one, mul_inv_cancel]
  · rw [hslash, hγγ', mul_inv_cancel_right, ← hFγ]
    exact hFF' _

end GlobalTheory.FNConj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityConjugateFormLevelStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.shimuraReciprocity_conjugate_form_level : ∀ (g : ℂ ≃+* ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (k : ℕ) (f : ℍ → ℂ), ZetaAct g N d → Even k → (∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[(k : ℤ)] γ = f) → (∀ γ : SL(2, ℤ), ∃ a, HasQ N (f ∣[(k : ℤ)] γ) a) → ∃ f' : ℍ → ℂ, (∀ γ ∈ CongruenceSubgroup.Gamma N, f' ∣[(k : ℤ)] γ = f') ∧ ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d → QConj g N (f ∣[(k : ℤ)] γ) (f' ∣[(k : ℤ)] γ') := by
  first | exact @GlobalTheory.FNConj.main | exact GlobalTheory.FNConj.main | (intros; apply GlobalTheory.FNConj.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelNFunctionGaloisConjQExpansion

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem lv_galois_conj : ∀ (g : ℂ ≃+* ℂ) (E : Subring ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (w : ℕ) (f : ℍ → ℂ),
    (∀ x ∈ E, g x ∈ E) → ZetaAct g N d → Lv E N w f → ∃ f' : ℍ → ℂ, Lv E N w f' ∧
      ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d →
        QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * f' (γ' • τ)) := by
  intro g E N _ d w f hE hZ hf
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  set F : ℍ → ℂ := fun τ => DD τ ^ w * f τ with hFdef
  have hsl : ∀ (h : ℍ → ℂ) (γ : SL(2, ℤ)),
      ((fun τ => DD τ ^ w * h τ) ∣[((12 * w : ℕ) : ℤ)] γ) = fun τ => DD τ ^ w * h (γ • τ) :=
    fun h γ => GlobalTheory.T.modularDiscriminant_pow_mul_slash_twelve_mul w h γ
  have hev : Even (12 * w) := ⟨6 * w, by ring⟩
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, F ∣[((12 * w : ℕ) : ℤ)] γ = F := by
    intro γ hγ
    rw [hFdef, hsl]
    funext τ
    rw [hf.1 γ hγ τ]
  have hq : ∀ γ : SL(2, ℤ), ∃ a, HasQ N (F ∣[((12 * w : ℕ) : ℤ)] γ) a := by
    intro γ
    obtain ⟨a, ha, -⟩ := hf.2 γ
    exact ⟨a, by rw [hFdef, hsl]; exact ha⟩
  obtain ⟨F', hF'inv, hF'c⟩ := GlobalTheory.T.shimuraReciprocity_conjugate_form_level g N d (12 * w) F hZ hev hinv hq
  refine ⟨fun τ => F' τ / DD τ ^ w, ?_, ?_⟩
  · have hF'eq : (fun τ => DD τ ^ w * (F' τ / DD τ ^ w)) = F' := by
      funext τ
      have := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      field_simp
    have key : ∀ γ : SL(2, ℤ), (fun τ => DD τ ^ w * (F' (γ • τ) / DD (γ • τ) ^ w)) =
        F' ∣[((12 * w : ℕ) : ℤ)] γ := by
      intro γ
      have := hsl (fun τ => F' τ / DD τ ^ w) γ
      rw [hF'eq] at this
      exact this.symm
    refine ⟨fun γ hγ τ => ?_, fun γ' => ?_⟩
    · have h1 := congrFun (key γ) τ
      rw [hF'inv γ hγ] at h1
      have h2 := congrFun hF'eq τ
      have hne := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      exact mul_left_cancel₀ hne (h1.trans h2.symm)
    · obtain ⟨γ, hγ⟩ := (GlobalTheory.T.diagOneUnit_conj_lifts_sl2IntReductionMod N d).2 γ'
      obtain ⟨a, ha, ha'⟩ := hF'c γ γ' hγ
      obtain ⟨b, hb, hbE⟩ := hf.2 γ
      have hb' : HasQ N (F ∣[((12 * w : ℕ) : ℤ)] γ) b := by rw [hFdef, hsl]; exact hb
      have hab : a = b := GlobalTheory.QFam.hasQ_unique_both.1 N _ a b hN ha hb'
      refine ⟨fun n => g (a n), ?_, fun n => ?_⟩
      · rw [key γ']; exact ha'
      · rw [hab]; exact hE _ (hbE n)
  · intro γ γ' hγ
    have hF'eq : (fun τ => DD τ ^ w * (F' τ / DD τ ^ w)) = F' := by
      funext τ
      have := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      field_simp
    have key : (fun τ => DD τ ^ w * (F' (γ' • τ) / DD (γ' • τ) ^ w)) = F' ∣[((12 * w : ℕ) : ℤ)] γ' := by
      have := hsl (fun τ => F' τ / DD τ ^ w) γ'
      rw [hF'eq] at this
      exact this.symm
    have kf : (fun τ => DD τ ^ w * f (γ • τ)) = F ∣[((12 * w : ℕ) : ℤ)] γ := by rw [hFdef, hsl]
    show QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * (F' (γ' • τ) / DD (γ' • τ) ^ w))
    rw [key, kf]
    exact hF'c γ γ' hγ

end GlobalTheory.FN
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelNFunctionGaloisConjQExpansionStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.levelN_function_galois_conj_qExpansion : ∀ (g : ℂ ≃+* ℂ) (E : Subring ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (w : ℕ) (f : ℍ → ℂ), (∀ x ∈ E, g x ∈ E) → ZetaAct g N d → Lv E N w f → ∃ f' : ℍ → ℂ, Lv E N w f' ∧ ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d → QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * f' (γ' • τ)) := by
  first | exact @GlobalTheory.FN.lv_galois_conj | exact GlobalTheory.FN.lv_galois_conj | (intros; apply GlobalTheory.FN.lv_galois_conj <;> assumption)
end
end
