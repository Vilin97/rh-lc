module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
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
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadSurjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadZeroOfClassZeroStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassSurjective

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CechSerre

theorem clsZ_mem_Ff_succ {R : Type} [CommRing R] (K : DCx.{w} R) {n p q : ℕ} (hpq : p + q = n)
    (hS : Subsingleton ((K.col p).H q)) (z : Zf K n p) : clsZ K n p z ∈ Ff K n (p + 1) := by
  have hv : (K.col p).d q (z.1.1.1 p q) = 0 := dv_lead K z.1.1.1 (D_zero K z.1) p q z.2
  have h1 : (K.col p).cls (z.1.1.1 p q) hv = 0 := Subsingleton.elim _ _
  rw [(P.cls_surj _ q).2.1] at h1
  obtain ⟨W, hW, hl⟩ := lower_vert K z.1.1.1 z.1.1.2 hpq z.2 0 0 (fun _ _ _ => rfl) (by simp)
    (by simpa using h1)
  exact lower K z W hW hl

theorem Ff_eq_top_of_acyclic {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ)
    (h : ∀ p q, a < q → Subsingleton ((K.col p).H q)) : ∀ p, p ≤ j → Ff K (a + j) p = ⊤ := by
  intro p
  induction p with
  | zero =>
    intro _
    refine (Submodule.eq_top_iff').2 fun x => ?_
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
    exact ⟨⟨z, fun p q hp => absurd hp (Nat.not_lt_zero p)⟩, rfl⟩
  | succ p ih =>
    intro hp
    refine (Submodule.eq_top_iff').2 fun x => ?_
    have hx : x ∈ Ff K (a + j) p := by rw [ih (by omega)]; exact Submodule.mem_top
    obtain ⟨z, rfl⟩ := hx
    exact clsZ_mem_Ff_succ K (q := a + j - p) (by omega) (h p _ (by omega)) z

theorem clsZ_surjective_of_acyclic : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ),
    (∀ p q, a < q → Subsingleton ((K.col p).H q)) →
    Function.Surjective (clsZ K (a + j) j) := by
  intro R _ K a j h
  exact LinearMap.range_eq_top.1 (Ff_eq_top_of_acyclic K a j h j le_rfl)

end GlobalTheory.CompanionTheory.CechSerre
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassSurjectiveStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.double_complex_class_surjective : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, a < q → Subsingleton ((K.col p).H q)) →
    Function.Surjective (clsZ K (a + j) j) := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.clsZ_surjective_of_acyclic | exact GlobalTheory.CompanionTheory.CechSerre.clsZ_surjective_of_acyclic | (intros; apply GlobalTheory.CompanionTheory.CechSerre.clsZ_surjective_of_acyclic <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassZeroOfLeadZero

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.RowInj

theorem clsZ_mem_of_leadE {R : Type} [CommRing R] (K : DCx.{w} R) (n a q : ℕ) (haq : a + q = n)
    (z : Zf K n a) (hz : leadE K a q z = 0) : clsZ K n a z ∈ Ff K n (a + 1) := by
  have hT : (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) ∈ K.T n :=
    Subtype.prop (Subtype.val (Subtype.val z))
  have h0 : ∀ p r, p < a → (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) p r = 0 :=
    fun p r hp => z.2 p r hp
  have hdv : K.dv a q ((Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) a q) = 0 :=
    dv_lead K _ (D_zero K (Subtype.val z)) a q h0
  have hB : leadC K a q z ∈ (colH K q).B a := by
    have hz' := hz
    rw [leadE_eq] at hz'
    unfold CrystallineSemistableComparison.Cx.cls at hz'
    rw [Submodule.Quotient.mk_eq_zero] at hz'
    exact hz'
  have hL := leadC_eq K a q z hdv
  obtain ⟨v₁, W₁, hW₁, hD, hv⟩ : ∃ (v₁ : K.X a q) (W₁ : (p q : ℕ) → K.X p q),
      (∀ p r, p + r + 1 ≠ n → W₁ p r = 0) ∧ K.D W₁ = K.sgl a q v₁ ∧
      (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) a q - v₁ ∈ (K.col a).B q := by
    cases a with
    | zero =>
      refine ⟨0, 0, fun _ _ _ => rfl, by simp, ?_⟩
      have hb : leadC K 0 q z ∈ (⊥ : Submodule R ((colH K q).X 0)) := hB
      rw [Submodule.mem_bot, hL] at hb
      unfold CrystallineSemistableComparison.Cx.cls at hb
      rw [Submodule.Quotient.mk_eq_zero] at hb
      simpa using hb
    | succ a' =>
      have hb : leadC K (a' + 1) q z ∈ LinearMap.range ((colH K q).d a') := hB
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hb
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective
        (Submodule.comap ((K.col a').Z q).subtype ((K.col a').B q)) y
      have hw : K.dv a' q (w : K.X a' q) = 0 := w.2
      refine ⟨K.dh a' q w, K.sgl a' q w, ?_, ?_, ?_⟩
      · intro p r hpr
        apply K.sgl_ne
        by_cases hp : p = a'
        · right
          intro hr
          apply hpr
          omega
        · left
          exact hp
      · rw [DCx.D_sgl, hw, map_zero, smul_zero, add_zero]
      · rw [hL] at hy
        unfold CrystallineSemistableComparison.Cx.cls at hy
        change (colMap K a').mapH q (Submodule.Quotient.mk w) = _ at hy
        unfold CrystallineSemistableComparison.Cx.Hom.mapH at hy
        rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hy
        have h2 := Submodule.neg_mem _ hy
        rw [neg_sub] at h2
        exact h2
  obtain ⟨W, hW, hW'⟩ := lower_vert K _ hT haq h0 v₁ W₁ hW₁ hD hv
  exact lower K z W hW hW'

theorem leadE_eq_zero_of_subsingleton {R : Type} [CommRing R] (K : DCx.{w} R) (n a q : ℕ)
    (hs : Subsingleton ((K.col a).H q)) (z : Zf K n a) : leadE K a q z = 0 := by
  have h0 : leadC K a q z = 0 := Subsingleton.elim _ _
  rw [leadE_eq]
  unfold CrystallineSemistableComparison.Cx.cls
  rw [Submodule.Quotient.mk_eq_zero]
  show leadC K a q z ∈ (colH K q).B a
  rw [h0]
  exact Submodule.zero_mem _

theorem Ff_eq_zero {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ)
    (hK : ∀ p q, q < a → Subsingleton ((K.col p).H q)) :
    ∀ k b, j < b → b + k = a + j + 1 → ∀ x ∈ Ff K (a + j) b, x = 0 := by
  intro k
  induction k with
  | zero =>
    intro b _ hbk x hx
    have hb' : b = a + j + 1 := by omega
    subst hb'
    have hs := Ff_top_subsingleton K (a + j)
    have hxx := Subsingleton.elim (⟨x, hx⟩ : ↥(Ff K (a + j) (a + j + 1))) 0
    simpa using congrArg Subtype.val hxx
  | succ k ih =>
    intro b hb hbk x hx
    have hx' : x ∈ LinearMap.range (clsZ K (a + j) b) := hx
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx'
    have hq : b + (a + j - b) = a + j := by omega
    have hz : leadE K b (a + j - b) z = 0 :=
      leadE_eq_zero_of_subsingleton K (a + j) b (a + j - b) (hK b _ (by omega)) z
    exact ih (b + 1) (by omega) (by omega) _ (clsZ_mem_of_leadE K (a + j) b (a + j - b) hq z hz)

theorem clsZ_eq_zero_of_leadE : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, q < a → Subsingleton ((K.col p).H q)) →
    ∀ z : Zf K (a + j) j, leadE K j a z = 0 → clsZ K (a + j) j z = 0 := by
  intro R _ K a j hK z hz
  exact Ff_eq_zero K a j hK a (j + 1) (by omega) (by omega) _
    (clsZ_mem_of_leadE K (a + j) j a (by omega) z hz)

end GlobalTheory.CompanionTheory.RowInj
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassZeroOfLeadZeroStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.double_complex_class_zero_of_lead_zero : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, q < a → Subsingleton ((K.col p).H q)) →
    ∀ z : Zf K (a + j) j, leadE K j a z = 0 → clsZ K (a + j) j z = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RowInj.clsZ_eq_zero_of_leadE | exact GlobalTheory.CompanionTheory.RowInj.clsZ_eq_zero_of_leadE | (intros; apply GlobalTheory.CompanionTheory.RowInj.clsZ_eq_zero_of_leadE <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexDegenerateColumnIso

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CechSerre

theorem row_iso_of_columns : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a : ℕ), (∀ p q, q ≠ a → Subsingleton ((K.col p).H q)) →
    ∀ j, ∃ e : K.tot.H (a + j) ≃ₗ[R] (colH K a).H j, ∀ z : Zf K (a + j) j, e (clsZ K (a + j) j z) = leadE K j a z := by
  intro R _ K a hK j
  have hab : ∀ p q, a < q → Subsingleton ((K.col p).H q) := fun p q h => hK p q (ne_of_gt h)
  have hbe : ∀ p q, q < a → Subsingleton ((K.col p).H q) := fun p q h => hK p q (ne_of_lt h)
  have hs := GlobalTheory.T.double_complex_class_surjective K a j hab
  have hk := GlobalTheory.T.double_complex_lead_zero_of_class_zero K a j hab
  have hi := GlobalTheory.T.double_complex_class_zero_of_lead_zero K a j hbe
  have hl := GlobalTheory.T.double_complex_lead_surjective K a j hbe
  let c := clsZ K (a + j) j
  let ψ : Zf K (a + j) j →ₗ[R] (colH K a).H j := leadE K j a
  have hle : LinearMap.ker c ≤ LinearMap.ker ψ := fun z hz => hk z hz
  let L := (LinearMap.ker c).liftQ ψ hle
  have hL : Function.Bijective L := by
    constructor
    · refine (injective_iff_map_eq_zero L).2 fun x hx => ?_
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
      have hz : ψ z = 0 := by simpa [L] using hx
      have hc : c z = 0 := hi z hz
      exact (Submodule.Quotient.mk_eq_zero _).2 hc
    · intro y
      obtain ⟨z, rfl⟩ := hl y
      exact ⟨Submodule.Quotient.mk z, Submodule.liftQ_apply _ _ _⟩
  let e0 := c.quotKerEquivOfSurjective hs
  refine ⟨e0.symm.trans (LinearEquiv.ofBijective L hL), fun z => ?_⟩
  have h0 : e0.symm (c z) = Submodule.Quotient.mk z :=
    e0.symm_apply_eq.2 (LinearMap.quotKerEquivOfSurjective_apply_mk c hs z).symm
  change L (e0.symm (c z)) = ψ z
  rw [h0]
  exact Submodule.liftQ_apply _ _ _

end GlobalTheory.CompanionTheory.CechSerre
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexDegenerateColumnIsoStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.double_complex_degenerate_column_iso : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a : ℕ), (∀ p q, q ≠ a → Subsingleton ((K.col p).H q)) →
    ∀ j, ∃ e : K.tot.H (a + j) ≃ₗ[R] (colH K a).H j, ∀ z : Zf K (a + j) j, e (clsZ K (a + j) j z) = leadE K j a z := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.row_iso_of_columns | exact GlobalTheory.CompanionTheory.CechSerre.row_iso_of_columns | (intros; apply GlobalTheory.CompanionTheory.CechSerre.row_iso_of_columns <;> assumption)
end
end
