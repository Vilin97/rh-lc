module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthonormalBasisUnimodularHermitianLocalRi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixCharpolyPreservingHermitianFormCMStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.MemMaxVAIff
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.FinNormSurj
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.WittHS

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.WittFN

section

@[expose] public section

noncomputable section

namespace Formalism.IndefR.LocBrg

theorem finNormSurj : FinNormSurj := by
  intro k _ _ τ hτ hnt c hc hc0
  classical
  have hτu : ∀ x : kˣ, Units.map τ.toMonoidHom (Units.map τ.toMonoidHom x) = x := by
    intro x; ext; simp [hτ]
  let T : kˣ →* kˣ := Units.map τ.toMonoidHom
  let N : kˣ →* kˣ :=
    { toFun := fun x => T x * x
      map_one' := by simp
      map_mul' := by intro x y; simp only [map_mul]; exact mul_mul_mul_comm _ _ _ _ }
  let ψ : kˣ →* kˣ :=
    { toFun := fun x => x * (T x)⁻¹
      map_one' := by simp
      map_mul' := by intro x y; simp only [map_mul, mul_inv]; exact mul_mul_mul_comm _ _ _ _ }
  have hTT : ∀ x, T (T x) = x := hτu
  have hT : ∀ x : kˣ, ((T x : kˣ) : k) = τ (x : k) := fun x => rfl
  have hψv : ∀ y : kˣ, ((ψ y : kˣ) : k) = (y : k) * (τ (y : k))⁻¹ := fun y => by
    show ((y * (T y)⁻¹ : kˣ) : k) = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hT]
  have hkerψ : ∀ x, x ∈ ψ.ker ↔ T x = x := by
    intro x
    rw [MonoidHom.mem_ker]
    show x * (T x)⁻¹ = 1 ↔ T x = x
    rw [mul_inv_eq_one, eq_comm]
  have hrangeψ : ψ.range = N.ker := by
    ext x
    rw [MonoidHom.mem_range, MonoidHom.mem_ker]
    constructor
    · rintro ⟨y, rfl⟩
      show T (y * (T y)⁻¹) * (y * (T y)⁻¹) = 1
      rw [map_mul, map_inv, hTT]
      group
    · intro hx
      have hx' : T x * x = 1 := hx
      have hTx : (τ (x : k)) * (x : k) = 1 := by
        have := congrArg (fun u : kˣ => (u : k)) hx'
        simp only [Units.val_mul, Units.val_one, hT] at this
        exact this
      by_cases hm : (x : k) = -1
      · obtain ⟨θ, hθ⟩ := hnt
        have hy0 : θ - τ θ ≠ 0 := fun h => hθ (sub_eq_zero.1 h).symm
        refine ⟨Units.mk0 _ hy0, ?_⟩
        ext
        rw [hψv, Units.val_mk0]
        rw [map_sub, hτ, hm]
        have : τ θ - θ = -(θ - τ θ) := by ring
        rw [this, inv_neg, mul_neg, mul_inv_cancel₀ hy0]
      · have hy0 : (1 : k) + x ≠ 0 := by
          intro h; apply hm; linear_combination h
        refine ⟨Units.mk0 _ hy0, ?_⟩
        ext
        rw [hψv, Units.val_mk0]
        have hx0 : (x : k) ≠ 0 := x.ne_zero
        have hτx : τ (x : k) = (x : k)⁻¹ := eq_inv_of_mul_eq_one_left hTx
        rw [map_add (f := _), map_one, hτx]
        have h1 : (1 : k) + (x : k)⁻¹ = (1 + (x : k)) * (x : k)⁻¹ := by field_simp; ring
        rw [h1, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ hy0, one_mul]
  have hle : N.range ≤ ψ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [hkerψ]
    show T (T x * x) = T x * x
    rw [map_mul, hTT, mul_comm]
  have hcardN := Subgroup.card_mul_index N.ker
  rw [Subgroup.index_ker] at hcardN
  have hcardψ := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, hrangeψ] at hcardψ
  have hpos : 0 < Nat.card N.ker := Nat.card_pos
  have heq : Nat.card N.range = Nat.card ψ.ker := by
    have h := hcardN.trans hcardψ.symm
    rw [mul_comm (Nat.card ψ.ker)] at h
    exact (Nat.eq_of_mul_eq_mul_left hpos h)
  have hEq : N.range = ψ.ker := Subgroup.eq_of_le_of_card_ge hle heq.ge
  have hcu : Units.mk0 c hc0 ∈ ψ.ker := by
    rw [hkerψ]; ext; rw [hT, Units.val_mk0]; exact hc
  rw [← hEq] at hcu
  obtain ⟨x, hx⟩ := hcu
  refine ⟨(x : k), ?_⟩
  have := congrArg (fun u : kˣ => (u : k)) hx
  simp only [Units.val_mk0] at this
  rw [show ((N x : kˣ) : k) = τ (x : k) * (x : k) from rfl] at this
  exact this

end Formalism.IndefR.LocBrg
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.EllipticCharpolyLocalRealisation

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.IntUnitaryPoly

theorem lemGlobal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    ∃ C H : Matrix (Fin n) (Fin n) E, C.charpoly = P ∧ C.det ≠ 0 ∧ H.det ≠ 0 ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom C * H * C = H := GlobalTheory.T.exists_matrix_charpoly_preserving_hermitian_form_CM

theorem lemLocal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → Odd q → ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) L), (∀ i j, H i j ∈ intL L) →
      Valued.v H.det = 1 → cT σ H = H →
      ∃ R ∈ GLint (Fin n) (intL L), cT σ ((R : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * H * ((R : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
  intro L _ _ _ ϖ σ q hU hq n H hint hdet hH
  have hv := hU.2.1
  set O := Formalism.IndefR.LocBrg.VA L
  set s := Formalism.IndefR.LocBrg.sigA σ hv
  have hs : ∀ x, s (s x) = x := Formalism.IndefR.LocBrg.sigA_inv σ hv hU.1
  have h2 : IsUnit (2 : O) := Formalism.IndefR.LocBrg.two_unit_VA hU hq
  have hτ : ∃ τ : O, τ + s τ = 1 := by
    obtain ⟨u, hu⟩ := h2
    refine ⟨((u⁻¹ : Oˣ) : O), ?_⟩
    have hs2 : s 2 = 2 := map_ofNat s 2
    have hfix : s ((u⁻¹ : Oˣ) : O) = ((u⁻¹ : Oˣ) : O) := by
      have e : s ((u⁻¹ : Oˣ) : O) * 2 = 1 := by rw [← hs2, ← map_mul, ← hu, Units.inv_mul, map_one]
      calc s ((u⁻¹ : Oˣ) : O) = s ((u⁻¹ : Oˣ) : O) * (2 * ((u⁻¹ : Oˣ) : O)) := by rw [← hu, Units.mul_inv, mul_one]
        _ = ((u⁻¹ : Oˣ) : O) := by rw [← mul_assoc, e, one_mul]
    rw [hfix, ← two_mul, ← hu, Units.mul_inv]
  have hn : ∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u := fun u hu hsu =>
    Formalism.IndefR.LocBrg.normSurj Formalism.IndefR.LocBrg.finNormSurj Formalism.IndefR.LocBrg.henselSqrt hU hq u hsu hu
  set Q : Matrix (Fin n) (Fin n) O := fun i j =>
    ⟨H i j, Formalism.IndefR.LocBrg.mem_VA.2 (Formalism.IndefR.LocBrg.mem_intL.1 (hint i j))⟩ with hQdef
  have hmap : Q.map O.subtype = H := by ext i j; rfl
  have hQ : cT s Q = Q := by
    ext i j; exact congrFun (congrFun hH i) j
  have hQu : IsUnit Q := by
    rw [Matrix.isUnit_iff_isUnit_det, Formalism.IndefR.LocBrg.isUnit_VA_iff]
    have e : ((Q.det : O) : L) = H.det := by rw [← hmap]; exact RingHom.map_det O.subtype Q
    rw [e]; exact hdet
  obtain ⟨a, ha⟩ := GlobalTheory.Core.Rk.Exh.exists_orthonormal_of_isLocalRing O s hs hτ hn n Q hQ hQu
  let ι : O →+* intL L := O.subtype.codRestrict (intL L)
    (fun x => Formalism.IndefR.LocBrg.mem_intL.2 (Formalism.IndefR.LocBrg.mem_VA.1 x.2))
  refine ⟨bc (n := Fin n) (intL L).subtype (bc (n := Fin n) ι a), ⟨_, rfl⟩, ?_⟩
  have hR : ((bc (n := Fin n) (intL L).subtype (bc (n := Fin n) ι a) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      (a : Matrix (Fin n) (Fin n) O).map O.subtype := by ext i j; rfl
  rw [hR, ← hmap]
  have hc : cT σ ((a : Matrix (Fin n) (Fin n) O).map O.subtype) = (cT s (a : Matrix (Fin n) (Fin n) O)).map O.subtype := by
    ext i j; rfl
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, ha, Matrix.map_one _ (map_zero _) (map_one _)]

theorem lemOdd : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → Valued.v (2 : L) = 1 → Odd q := by
  intro L _ _ ϖ σ q hU h2
  set V := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hcard : Nat.card (IsLocalRing.ResidueField V) = q ^ 2 := hU.2.2.2.2.2.2
  have hq0 : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  haveI : Finite (IsLocalRing.ResidueField V) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hq0)
  have h20 : (2 : L) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
  have hu : IsUnit (2 : V) := by
    have hmem : (2 : L)⁻¹ ∈ V := (Valuation.mem_valuationSubring_iff _ _).2 (by rw [map_inv₀, h2, inv_one])
    have hmul : (2 : V) * ⟨(2 : L)⁻¹, hmem⟩ = 1 := by
      apply Subtype.ext
      first
        | exact mul_inv_cancel₀ h20
        | (show (2 : L) * (2 : L)⁻¹ = 1; exact mul_inv_cancel₀ h20)
        | (push_cast; exact mul_inv_cancel₀ h20)
    exact ⟨⟨2, _, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
  have h2V : (2 : IsLocalRing.ResidueField V) ≠ 0 := by
    intro h
    have hm : (2 : V) ∈ IsLocalRing.maximalIdeal V := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_ofNat]; exact h
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hu
  by_contra hodd
  have heven : Even q := Nat.not_odd_iff_even.1 hodd
  have hdvd : 2 ∣ Nat.card (IsLocalRing.ResidueField V) := by
    rw [hcard]; exact dvd_pow (even_iff_two_dvd.1 heven) two_ne_zero
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' 2 hdvd
  have hx0 : x ≠ 0 := by intro h; rw [h, addOrderOf_zero] at hx; norm_num at hx
  have hmul : (2 : IsLocalRing.ResidueField V) * x = 0 := by
    rw [two_mul, ← two_nsmul, ← hx, addOrderOf_nsmul_eq_zero]
  exact h2V ((mul_eq_zero.1 hmul).resolve_right hx0)

theorem val_alg {E : Type} [Field E] [NumberField E] (w : Pl E) (x : E) :
    Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

theorem ae_int {E : Type} [Field E] [NumberField E] (x : E) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), Valued.v (algebraMap E (w.adicCompletion E) x) ≤ 1 := by
  filter_upwards [(HeightOneSpectrum.Support.finite (𝓞 E) (K := E) x).eventually_cofinite_notMem] with w hw
  have hw' : ¬ 1 < w.valuation E x := hw
  rw [val_alg]
  exact not_lt.1 hw'

theorem ae_unit {E : Type} [Field E] [NumberField E] {x : E} (hx : x ≠ 0) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), Valued.v (algebraMap E (w.adicCompletion E) x) = 1 := by
  filter_upwards [ae_int x, ae_int x⁻¹] with w h1 h2
  rw [map_inv₀, map_inv₀] at h2
  have h0 : Valued.v (algebraMap E (w.adicCompletion E) x) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact (_root_.map_ne_zero _).2 hx
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h2)

theorem mem_GLint {L : Type} [Field L] {O : Subring L} {n : ℕ} (g : GL (Fin n) L)
    (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ O)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ O) :
    g ∈ GLint (Fin n) O := by
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, h2 i j⟩
  have hA : A.map O.subtype = (g : Matrix (Fin n) (Fin n) L) := by ext i j; rfl
  have hB : B.map O.subtype = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by ext i j; rfl
  have inj : ∀ M N : Matrix (Fin n) (Fin n) O, M.map O.subtype = N.map O.subtype → M = N := fun M N h => by
    ext i j; exact congrFun (congrFun h i) j
  have hAB : A * B = 1 := inj _ _ (by
    rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
  have hBA : B * A = 1 := inj _ _ (by
    rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  ext i j; rfl

theorem Ov_eq {E : Type} [Field E] [NumberField E] (w : Pl E) :
    (w.adicCompletionIntegers E).toSubring = intL (w.adicCompletion E) := by
  ext x
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).trans (Valuation.mem_integer_iff _ _).symm

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P ∈ Ell E n →
    (∀ᶠ w in (cofinite : Filter (Pl E)), ∃ y : UL n w, y ∈ KL n w ∧ y.1.val.charpoly = atPl w P) ∧
      ∀ w : Pl E, IsSplitAt w → ∃ y : UL n w, y.1.val.charpoly = atPl w P := by
  intro E _ _ _ hU n P hP
  obtain ⟨C, H, hC, hCd, hHd, hHh, hCH⟩ := lemGlobal E n P hP
  set Ci := C⁻¹ with hCi
  have hCCi : C * Ci = 1 := Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.2 hCd)
  have hCiC : Ci * C = 1 := Matrix.nonsing_inv_mul C (isUnit_iff_ne_zero.2 hCd)
  let f : ∀ w : Pl E, E →+* w.adicCompletion E := fun w => algebraMap E (w.adicCompletion E)
  let Cw : ∀ w : Pl E, GLw n w := fun w =>
    ⟨C.map (f w), Ci.map (f w), by rw [← Matrix.map_mul, hCCi, Matrix.map_one _ (map_zero _) (map_one _)],
      by rw [← Matrix.map_mul, hCiC, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hCwv : ∀ w, ((Cw w : GLw n w) : Matrix (Fin n) (Fin n) _) = C.map (f w) := fun w => rfl
  have hCwi : ∀ w, (((Cw w)⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) = Ci.map (f w) := fun w => rfl
  have hchar : ∀ w, (C.map (f w)).charpoly = atPl w P := fun w => by
    rw [Matrix.charpoly_map, hC]
  refine ⟨?_, fun w hs => ⟨⟨Cw w, by rw [UL, if_pos hs]; exact Subgroup.mem_top _⟩, hchar w⟩⟩
  have hall : ∀ M : Matrix (Fin n) (Fin n) E, ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, Valued.v (f w (M i j)) ≤ 1 :=
    fun M => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ae_int (M i j)
  filter_upwards [hall C, hall Ci, hall H, ae_unit hHd, ae_unit (two_ne_zero : (2 : E) ≠ 0)] with w h1 h2 h3 h4 h5
  have hO : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 → x ∈ (w.adicCompletionIntegers E).toSubring :=
    fun x hx => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx
  have hK : Cw w ∈ GlobalTheory.LFun.KGL w (n := n) :=
    mem_GLint _ (fun i j => hO _ (h1 i j)) (fun i j => hO _ (h2 i j))
  by_cases hs : IsSplitAt w
  · exact ⟨⟨Cw w, by rw [UL, if_pos hs]; exact Subgroup.mem_top _⟩, Subgroup.mem_subgroupOf.2 hK, hchar w⟩
  · obtain ⟨-, -, -, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨hext, ⟨ϖ, q, hUI, -⟩, -, -⟩ := hns hs
    have h2v : Valued.v (2 : w.adicCompletion E) = 1 := by
      have e : f w 2 = 2 := map_ofNat _ 2
      rw [← e]; exact h5
    have hq := lemOdd _ ϖ (cj w) q hUI h2v
    set Hw := H.map (f w) with hHwdef
    have hHw1 : ∀ i j, Hw i j ∈ intL (w.adicCompletion E) := fun i j => (Valuation.mem_integer_iff _ _).2 (h3 i j)
    have hHw2 : Valued.v Hw.det = 1 := by
      rw [show Hw.det = f w H.det from (RingHom.map_det (f w) H).symm]; exact h4
    have hmapc : ∀ M : Matrix (Fin n) (Fin n) E,
        cT (cj w) (M.map (f w)) = (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map (f w) := by
      intro M; refine Matrix.ext fun i j => ?_; simp only [cT, Matrix.map_apply, Matrix.transpose_apply]; exact hext (M j i)
    have hHw3 : cT (cj w) Hw = Hw := by rw [hmapc, hHh]
    have hCHw : cT (cj w) (C.map (f w)) * Hw * C.map (f w) = Hw := by
      rw [hmapc, hHwdef, ← Matrix.map_mul, ← Matrix.map_mul, hCH]
    obtain ⟨R, hR, hRH⟩ := lemLocal (w.adicCompletion E) ϖ (cj w) q hUI hq n Hw hHw1 hHw2 hHw3
    have hRK : R ∈ GlobalTheory.LFun.KGL w (n := n) := by
      have e : GlobalTheory.LFun.KGL w (n := n) = GLint (Fin n) (intL (w.adicCompletion E)) := by
        show GLint (Fin n) (w.adicCompletionIntegers E).toSubring = _
        rw [Ov_eq]
      rw [e]; exact hR
    refine ⟨⟨R⁻¹ * Cw w * R, ?_⟩, Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem (inv_mem hRK) hK) hRK), ?_⟩
    · rw [UL, if_neg hs]
      show cT (cj w) ((R⁻¹ * Cw w * R : GLw n w) : Matrix (Fin n) (Fin n) _) * 1 *
        ((R⁻¹ * Cw w * R : GLw n w) : Matrix (Fin n) (Fin n) _) = 1
      rw [Units.val_mul, Units.val_mul, hCwv]
      set r := ((R : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
      set ri := (((R⁻¹ : GLw n w)) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
      have hri : r * ri = 1 := Units.mul_inv R
      have hH' : Hw = cT (cj w) ri * ri := by
        calc Hw = cT (cj w) (r * ri) * Hw * (r * ri) := by rw [hri, cT_one, Matrix.one_mul, Matrix.mul_one]
          _ = cT (cj w) ri * (cT (cj w) r * Hw * r) * ri := by rw [cT_mul]; simp only [Matrix.mul_assoc]
          _ = cT (cj w) ri * ri := by rw [hRH, Matrix.mul_one]
      rw [Matrix.mul_one, cT_mul, cT_mul]
      calc cT (cj w) r * (cT (cj w) (C.map (f w)) * cT (cj w) ri) * (ri * C.map (f w) * r)
          = cT (cj w) r * (cT (cj w) (C.map (f w)) * (cT (cj w) ri * ri) * C.map (f w)) * r := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [← hH', hCHw, hRH]
    · have hinv : ((((R⁻¹ : GLw n w)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))⁻¹ =
          ((R : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
        rw [← Matrix.coe_units_inv, inv_inv]
      have e := Matrix.charpoly_units_conj (R⁻¹ : GLw n w) (C.map (f w))
      rw [hinv] at e
      have key : ((R⁻¹ * Cw w * R : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).charpoly = atPl w P := by
        rw [Units.val_mul, Units.val_mul, hCwv, e, hchar]
      exact key

end GlobalTheory.IntUnitaryPoly
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.EllipticCharpolyLocalRealisationStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.elliptic_charpoly_local_realisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P ∈ Ell E n → (∀ᶠ w in (cofinite : Filter (Pl E)), ∃ y : UL n w, y ∈ KL n w ∧ y.1.val.charpoly = atPl w P) ∧ ∀ w : Pl E, IsSplitAt w → ∃ y : UL n w, y.1.val.charpoly = atPl w P := by
  first | exact @GlobalTheory.IntUnitaryPoly.main | exact GlobalTheory.IntUnitaryPoly.main | (intros; apply GlobalTheory.IntUnitaryPoly.main <;> assumption)
end
end
