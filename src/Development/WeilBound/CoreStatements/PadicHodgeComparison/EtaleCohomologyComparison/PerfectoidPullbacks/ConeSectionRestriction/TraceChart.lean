module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RaTpowSinglePow
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimeDvdNotUnit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.TorusMemFldF
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FractionFieldTranscendenceBasisExt

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open MvPolynomial

namespace GlobalTheory.CompanionTheory.TraceJac

theorem det_completed_eq_minor {L : Type*} [Field L] {d m : ℕ} (κ : Fin m ↪ Fin d)
    (E : Fin d → L → L) (τ : Fin d → L) (hE : ∀ k j, E k (τ j) = if k = j then 1 else 0)
    (β : Fin m → L) :
    let e : Fin m ⊕ ↥(Set.range κ)ᶜ ≃ Fin d :=
      (Equiv.sumCongr (Equiv.ofInjective κ κ.injective) (Equiv.refl _)).trans
        (Equiv.Set.sumCompl (Set.range κ))
    (Matrix.of fun k l => E k ((Sum.elim β (fun j : ↥(Set.range κ)ᶜ => τ j)) (e.symm l))).det =
      (Matrix.of fun k l => E (κ k) (β l)).det := by
  classical
  intro e
  have he1 : ∀ i, e (Sum.inl i) = κ i := fun i => by simp [e]
  have he2 : ∀ j : ↥(Set.range κ)ᶜ, e (Sum.inr j) = j := fun j => by simp [e]
  rw [← Matrix.det_submatrix_equiv_self e]
  have hblock : (Matrix.of fun k l =>
      E k ((Sum.elim β (fun j : ↥(Set.range κ)ᶜ => τ j)) (e.symm l))).submatrix e e =
      Matrix.fromBlocks (Matrix.of fun k l => E (κ k) (β l)) 0
        (Matrix.of fun (j : ↥(Set.range κ)ᶜ) l => E j (β l)) 1 := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Equiv.symm_apply_apply]
    rcases x with i | j <;> rcases y with i' | j'
    · simp [he1]
    · have hne : κ i ≠ (j' : Fin d) := fun h => j'.2 ⟨i, h⟩
      simp [he1, hE, hne]
    · simp [he2]
    · have : ((j : Fin d) = j') ↔ j = j' := Subtype.ext_iff.symm
      simp [he2, hE, Matrix.one_apply, this]
  rw [hblock, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

theorem trace_minor_mem : ∀ (K : Type) [Field K] [CharZero K] (d : ℕ) (A : Type) [CommRing A] [IsDomain A] [Algebra K A] (t : Fin d → A), Function.Injective (MvPolynomial.aeval t : MvPolynomial (Fin d) K →ₐ[K] A) → (∀ a : A, ∃ f g : MvPolynomial (Fin d) K, IsUnit (MvPolynomial.aeval t g) ∧ a * MvPolynomial.aeval t g = MvPolynomial.aeval t f) → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [Module.Finite A B], Function.Injective (algebraMap A B) → ∀ (F L : Type) [Field F] [Field L] [Algebra A F] [IsFractionRing A F] [Algebra B L] [IsFractionRing B L] [Algebra F L] [Algebra A L] [IsScalarTower A F L] [IsScalarTower A B L] [Algebra K L] [IsScalarTower K B L] (D : Fin d → Derivation K L L), (∀ k j, D k (algebraMap A L (t j)) = if k = j then 1 else 0) → ∀ (m : ℕ) (κ : Fin m ↪ Fin d) (c : B) (b : Fin m → B), ∃ a : A, algebraMap A F a = Algebra.trace F L (algebraMap B L c * (Matrix.of fun k l => D (κ k) (algebraMap B L (b l))).det) := by
  intro K _ _ d A _ _ _ t ht hloc B _ _ _ _ _ _ hB F L _ _ _ _ _ _ _ _ _ _ _ _ D hD m κ c b
  classical
  let e : Fin m ⊕ ↥(Set.range κ)ᶜ ≃ Fin d :=
    (Equiv.sumCongr (Equiv.ofInjective κ κ.injective) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range κ))
  let b' : Fin d → B := fun l =>
    (Sum.elim b (fun j : ↥(Set.range κ)ᶜ => algebraMap A B (t j))) (e.symm l)
  obtain ⟨a, ha⟩ := trace_jacobian_mem K d A t ht hloc B hB F L D hD c b'
  refine ⟨a, ha.trans ?_⟩
  have hdet := det_completed_eq_minor κ (fun k x => D k x) (fun j => algebraMap A L (t j)) hD
    (fun l => algebraMap B L (b l))
  have hmat : (Matrix.of fun k l => D k (algebraMap B L (b' l))) =
      Matrix.of fun k l => D k ((Sum.elim (fun l => algebraMap B L (b l))
        (fun j : ↥(Set.range κ)ᶜ => algebraMap A L (t j))) (e.symm l)) := by
    ext k l
    simp only [Matrix.of_apply, b']
    rcases e.symm l with i | j
    · simp
    · simp [← IsScalarTower.algebraMap_apply A B L]
  rw [hmat]
  exact congrArg (fun x => Algebra.trace F L (algebraMap B L c * x)) hdet

end GlobalTheory.CompanionTheory.TraceJac
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FractionFieldTranscendenceBasisExtStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open MvPolynomial

theorem _root_.GlobalTheory.T.fraction_field_transcendence_basis_ext : ∀ (K : Type) [Field K] [CharZero K] (d : ℕ) (A : Type) [CommRing A] [IsDomain A] [Algebra K A] (t : Fin d → A), Function.Injective (MvPolynomial.aeval t : MvPolynomial (Fin d) K →ₐ[K] A) → (∀ a : A, ∃ f g : MvPolynomial (Fin d) K, IsUnit (MvPolynomial.aeval t g) ∧ a * MvPolynomial.aeval t g = MvPolynomial.aeval t f) → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [Module.Finite A B], Function.Injective (algebraMap A B) → ∀ (F L : Type) [Field F] [Field L] [Algebra A F] [IsFractionRing A F] [Algebra B L] [IsFractionRing B L] [Algebra F L] [Algebra A L] [IsScalarTower A F L] [IsScalarTower A B L] [Algebra K L] [IsScalarTower K B L] (D : Fin d → Derivation K L L), (∀ k j, D k (algebraMap A L (t j)) = if k = j then 1 else 0) → ∀ (m : ℕ) (κ : Fin m ↪ Fin d) (c : B) (b : Fin m → B), ∃ a : A, algebraMap A F a = Algebra.trace F L (algebraMap B L c * (Matrix.of fun k l => D (κ k) (algebraMap B L (b l))).det) := by
  first | exact @GlobalTheory.CompanionTheory.TraceJac.trace_minor_mem | exact GlobalTheory.CompanionTheory.TraceJac.trace_minor_mem | (intros; apply GlobalTheory.CompanionTheory.TraceJac.trace_minor_mem <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.TraceChart

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [Field K] [CharZero K] {R : Type} [CommRing R] [IsDomain R] [Algebra K R] {n : ℕ}

theorem trace_chart (t : Fin (n + 1) → Rˣ) (S : Finset (Fin (n + 2))) (u : Fin (n + 1) → torusS K t S)
    (hinj : Function.Injective (MvPolynomial.aeval u : MvPolynomial (Fin (n + 1)) K →ₐ[K] torusS K t S))
    (hloc : ∀ a : torusS K t S, ∃ f g : MvPolynomial (Fin (n + 1)) K,
      IsUnit (MvPolynomial.aeval u g) ∧ a * MvPolynomial.aeval u g = MvPolynomial.aeval u f)
    (hfr : ∀ k, ∃ a' ∈ torusS K t S, a' ≠ 0 ∧ (t k : R) * a' ∈ torusS K t S)
    (B' : Subalgebra K R) (hTB : torusS K t S ≤ B') (hFG : B'.FG) (hInt : ∀ b ∈ B', IsIntegral (torusS K t S) b)
    (hFrac : ∀ r : R, ∃ b ∈ B', ∃ b' ∈ B', b' ≠ 0 ∧ r * b' = b)
    (E : Fin (n + 1) → Derivation K R R) (hE : ∀ k j, E k (u j : R) = if k = j then 1 else 0)
    {m : ℕ} (κ : Fin m → Fin (n + 1)) (hκ : Function.Injective κ) :
    ∀ y ∈ jacS B' E κ, ∃ a ∈ torusS K t S,
      algebraMap (fldF K t) (FractionRing R)
        (Algebra.trace (fldF K t) (FractionRing R) (algebraMap R (FractionRing R) y)) =
          algebraMap R (FractionRing R) a := by
  classical

  have hι : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R (FractionRing R)
  have hιne : ∀ r : R, r ≠ 0 → algebraMap R (FractionRing R) r ≠ 0 := fun r hr h =>
    hr (hι (h.trans (map_zero _).symm))

  letI : Algebra (torusS K t S) B' := (Subalgebra.inclusion hTB).toRingHom.toAlgebra
  haveI : IsScalarTower K (torusS K t S) B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hAB : Function.Injective (algebraMap (torusS K t S) B') := Subalgebra.inclusion_injective hTB
  let f : B' →ₐ[torusS K t S] R := { B'.val with commutes' := fun _ => rfl }
  haveI : Algebra.IsIntegral (torusS K t S) B' :=
    ⟨fun b => (isIntegral_algHom_iff f Subtype.val_injective).mp (hInt b b.2)⟩
  haveI : Algebra.FiniteType K B' := Subalgebra.fg_iff_finiteType B' |>.mp hFG
  haveI : Algebra.FiniteType (torusS K t S) B' := Algebra.FiniteType.of_restrictScalars_finiteType K _ _
  haveI : Module.Finite (torusS K t S) B' := Algebra.IsIntegral.finite

  let ψ : torusS K t S →+* fldF K t :=
    { toFun := fun a => ⟨algebraMap R (FractionRing R) a, torus_mem_fldF t S a a.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ (a : R) b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ (a : R) b) }
  letI : Algebra (torusS K t S) (fldF K t) := ψ.toAlgebra
  have hψ : ∀ a : torusS K t S, ((algebraMap (torusS K t S) (fldF K t) a : fldF K t) : FractionRing R) =
      algebraMap R (FractionRing R) a := fun _ => rfl
  have hψinj : Function.Injective (algebraMap (torusS K t S) (fldF K t)) := fun a b h =>
    Subtype.ext (hι (by rw [← hψ, ← hψ, h]))

  have hQ : ∀ z ∈ fldF K t, ∃ x y : torusS K t S, algebraMap R (FractionRing R) (y : R) ≠ 0 ∧
      z = algebraMap R (FractionRing R) x / algebraMap R (FractionRing R) y := fun z hz => by
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      obtain ⟨a', ha', ha'0, hta⟩ := hfr k
      refine ⟨⟨_, hta⟩, ⟨a', ha'⟩, hιne _ ha'0, ?_⟩
      simp only [map_mul]
      rw [mul_div_assoc, div_self (hιne _ ha'0), mul_one]
    | algebraMap c =>
      refine ⟨algebraMap K _ c, 1, by simpa using one_ne_zero, ?_⟩
      simp [IsScalarTower.algebraMap_apply K R (FractionRing R)]
    | add x y _ _ hx hy =>
      obtain ⟨x1, x2, hx2, rfl⟩ := hx
      obtain ⟨y1, y2, hy2, rfl⟩ := hy
      refine ⟨x1 * y2 + y1 * x2, x2 * y2, by simpa using mul_ne_zero hx2 hy2, ?_⟩
      simp only [Subalgebra.coe_add, Subalgebra.coe_mul, map_add (f := _), map_mul]
      rw [div_add_div _ _ hx2 hy2]
      ring
    | inv x _ hx =>
      obtain ⟨x1, x2, hx2, rfl⟩ := hx
      by_cases h1 : algebraMap R (FractionRing R) (x1 : R) = 0
      · exact ⟨0, 1, by simpa using one_ne_zero, by simp [h1]⟩
      · exact ⟨x2, x1, h1, by rw [inv_div]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨x1, x2, hx2, rfl⟩ := hx
      obtain ⟨y1, y2, hy2, rfl⟩ := hy
      refine ⟨x1 * y1, x2 * y2, by simpa using mul_ne_zero hx2 hy2, ?_⟩
      simp only [Subalgebra.coe_mul, map_mul]
      rw [div_mul_div_comm]
  haveI : FaithfulSMul (torusS K t S) (fldF K t) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hψinj
  haveI : IsFractionRing (torusS K t S) (fldF K t) := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, y, hy, hz⟩ := hQ z z.2
    refine ⟨x, y, Subtype.ext ?_⟩
    rw [IntermediateField.coe_div, hψ, hψ, ← hz]

  have hBL : Function.Injective (algebraMap B' (FractionRing R)) := fun a b h => Subtype.ext (hι h)
  haveI : FaithfulSMul B' (FractionRing R) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hBL
  haveI : IsFractionRing B' (FractionRing R) := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    obtain ⟨b1, hb1, b1', hb1', hb1'0, hr⟩ := hFrac r
    obtain ⟨b2, hb2, b2', hb2', hb2'0, hs'⟩ := hFrac s
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hb20 : b2 ≠ 0 := by rw [← hs']; exact mul_ne_zero hs0 hb2'0
    refine ⟨⟨b1 * b2', mul_mem hb1 hb2'⟩, ⟨b1' * b2, mul_mem hb1' hb2⟩, ?_⟩
    change _ = algebraMap R (FractionRing R) (b1 * b2') / algebraMap R (FractionRing R) (b1' * b2)
    have hden : algebraMap R (FractionRing R) (b1' * b2) ≠ 0 := hιne _ (mul_ne_zero hb1'0 hb20)
    rw [div_eq_div_iff (hιne _ hs0) hden, ← map_mul, ← map_mul, ← hr, ← hs']
    congr 1
    ring
  haveI : IsScalarTower (torusS K t S) (fldF K t) (FractionRing R) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (torusS K t S) B' (FractionRing R) := IsScalarTower.of_algebraMap_eq fun _ => rfl

  choose Dl hDl using fun k => frac_deriv (E k)
  have hDu : ∀ k j, Dl k (algebraMap (torusS K t S) (FractionRing R) (u j)) = if k = j then 1 else 0 := by
    intro k j
    change Dl k (algebraMap R (FractionRing R) (u j : R)) = _
    rw [hDl, hE]
    split_ifs <;> simp
  intro y hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, bs, rfl⟩ := hy
    obtain ⟨a, ha⟩ := GlobalTheory.T.fraction_field_transcendence_basis_ext K (n + 1) (torusS K t S) u hinj hloc B' hAB (fldF K t) (FractionRing R)
      Dl hDu m ⟨κ, hκ⟩ b bs
    refine ⟨a, a.2, ?_⟩
    have hX : algebraMap R (FractionRing R) ((b : R) * (Matrix.of fun k l => E (κ k) (bs l : R)).det) =
        algebraMap B' (FractionRing R) b *
          (Matrix.of fun k l => Dl ((⟨κ, hκ⟩ : Fin m ↪ Fin (n + 1)) k) (algebraMap B' (FractionRing R) (bs l))).det := by
      rw [map_mul, RingHom.map_det]
      refine congrArg₂ (· * ·) rfl (congrArg Matrix.det ?_)
      ext k l
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      rw [← hDl]
      rfl
    rw [← hψ, ha, hX]
    rfl
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    exact ⟨a + b, add_mem ha hb, by simp only [map_add (f := _)] at hxa hyb ⊢; rw [hxa, hyb]⟩
  | neg x _ hx =>
    obtain ⟨a, ha, hxa⟩ := hx
    exact ⟨-a, neg_mem ha, by simp only [map_neg] at hxa ⊢; rw [hxa]⟩

end CrystallineSemistableComparison.Pb
end
end
end
