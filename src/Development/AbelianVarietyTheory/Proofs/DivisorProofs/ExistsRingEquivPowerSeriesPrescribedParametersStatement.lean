module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CohenStructureFiniteOverNormalCompleteSubring
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Nakayama
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CohenStructureFiniteOverNormalCompleteSubring
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.RingKrullDimQuotientSpanSingletonAddOne
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefficientFieldOfCharZero

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory.CohenRegular

section Field
open Polynomial

theorem exists_coefficientField_of_charZero (S : Type) [CommRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    [CharZero (ResidueField S)] :
    ∃ Λ : Subring S, IsField Λ ∧ ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S := by
  let T : Set (Subring S) := {Λ | ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0}
  have hbot : (⊥ : Subring S) ∈ T := by
    intro x hx hm
    obtain ⟨n, rfl⟩ := Subring.mem_bot.1 hx
    rw [← residue_eq_zero_iff, map_intCast, Int.cast_eq_zero] at hm
    simp [hm]
  obtain ⟨Λ, -, hΛ⟩ := zorn_le_nonempty₀ T (fun c hc hch y hy => by
    refine ⟨sSup c, fun x hx => ?_, fun z hz => le_sSup hz⟩
    obtain ⟨K, hK, hxK⟩ := (Subring.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).1 hx
    exact hc hK x hxK) ⊥ hbot
  have hT : ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0 := hΛ.prop
  have hF : IsField Λ := by
    refine ⟨exists_pair_ne _, mul_comm, fun {x} hx => ?_⟩
    have hu : IsUnit (x : S) := by
      by_contra h
      exact hx (Subtype.ext (hT _ x.2 h))
    let Λ' : Subring S :=
      { carrier := {s | ∃ n : ℕ, (x : S) ^ n * s ∈ Λ}
        one_mem' := ⟨0, by simp⟩
        zero_mem' := ⟨0, by simp⟩
        mul_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by convert Λ.mul_mem hn hm using 1; ring⟩
        add_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by
            convert Λ.add_mem (Λ.mul_mem (Λ.pow_mem x.2 m) hn) (Λ.mul_mem (Λ.pow_mem x.2 n) hm) using 1; ring⟩
        neg_mem' := by
          rintro a ⟨n, hn⟩
          exact ⟨n, by convert Λ.neg_mem hn using 1; ring⟩ }
    have h' : Λ' ∈ T := by
      rintro s ⟨n, hn⟩ hm
      exact (hu.pow n).mul_right_eq_zero.1 (hT _ hn (Ideal.mul_mem_left _ _ hm))
    have hle : Λ' ≤ Λ := hΛ.le_of_ge h' fun s hs => ⟨0, by simpa using hs⟩
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    exact ⟨⟨y, hle ⟨1, by rw [pow_one, hy]; exact Λ.one_mem⟩⟩, Subtype.ext hy⟩
  refine ⟨Λ, hF, fun s => ?_⟩
  letI := hF.toField
  have key : ∀ a : S, (∀ f : Λ[X], aeval a f ∈ maximalIdeal S → aeval a f = 0) → a ∈ Λ := fun a ha => by
    have h' : (aeval (R := Λ) a).toRingHom.range ∈ T := by
      rintro _ ⟨f, rfl⟩ hm
      exact ha f hm
    exact hΛ.le_of_ge h' (fun y hy => ⟨C ⟨y, hy⟩, by simp; rfl⟩) ⟨X, by simp⟩
  have hres : ∀ (a : S) (f : Λ[X]), residue S (aeval a f) = aeval (residue S a) f := fun a f =>
    (aeval_algHom_apply (IsScalarTower.toAlgHom Λ S (ResidueField S)) a f).symm
  by_cases hs : IsAlgebraic Λ (residue S s)
  · have hi := hs.isIntegral
    haveI : CharZero Λ := RingHom.charZero (algebraMap Λ (ResidueField S))
    have hsep : (minpoly Λ (residue S s)).Separable := (minpoly.irreducible hi).separable
    obtain ⟨a, ha, has⟩ := HenselianRing.is_henselian (I := maximalIdeal S)
      ((minpoly Λ (residue S s)).map (algebraMap Λ S)) ((minpoly.monic hi).map _) s
      (by rw [eval_map_algebraMap, ← residue_eq_zero_iff, hres, minpoly.aeval])
      (by
        rw [derivative_map, eval_map_algebraMap]
        have := hsep.aeval_derivative_ne_zero (minpoly.aeval Λ (residue S s))
        rw [← hres] at this
        exact (isUnit_iff_ne_zero (G₀ := ResidueField S)).2 this)
    have e : residue S a = residue S s := by rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact has
    refine ⟨a, key a fun f hf => ?_, by rw [← neg_sub]; exact neg_mem has⟩
    rw [← residue_eq_zero_iff, hres, e] at hf
    obtain ⟨q, rfl⟩ := minpoly.dvd _ _ hf
    rw [IsRoot.def, eval_map_algebraMap] at ha
    rw [map_mul, ha, zero_mul]
  · refine ⟨s, key s fun f hf => ?_, by simp⟩
    rw [← residue_eq_zero_iff, hres] at hf
    by_contra h
    exact hs ⟨f, by rintro rfl; simp at h, hf⟩

end Field

open MvPowerSeries GlobalTheory.CohenStructure

end GlobalTheory.CohenRegular
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SurjectiveOfResidueOfCotangent

section

@[expose] public section

open IsLocalRing Matrix TensorProduct

namespace GlobalTheory.LocalSurj

theorem exists_sub_mem_map_pow_succ {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (n : ℕ) (a : A)
    (ha : a ∈ (m ^ n).map f) : ∃ x ∈ m ^ n, a - f x ∈ (m ^ (n + 1)).map f := by
  change a ∈ Ideal.span (f '' ((m ^ n : Ideal R) : Set R)) at ha
  induction ha using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, by simp⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨x, hx, hx'⟩ := hy
    obtain ⟨x', hx2, hx2'⟩ := hz
    refine ⟨x + x', add_mem hx hx2, ?_⟩
    have : y + z - f (x + x') = (y - f x) + (z - f x') := by rw [map_add (f := _)]; ring
    rw [this]; exact add_mem hx' hx2'
  | smul c y _ hy =>
    obtain ⟨x, hx, hx'⟩ := hy
    obtain ⟨s, hs⟩ := hm c
    refine ⟨s * x, Ideal.mul_mem_left _ _ hx, ?_⟩
    have : c • y - f (s * x) = c * (y - f x) + (c - f s) * f x := by
      rw [smul_eq_mul, map_mul]; ring
    rw [this]
    refine add_mem (Ideal.mul_mem_left _ _ hx') ?_
    rw [pow_succ', Ideal.map_mul]
    exact Ideal.mul_mem_mul hs (Ideal.mem_map_of_mem f hx)

noncomputable def approx {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (a : A) :
    (n : ℕ) → {x : R // a - f x ∈ (m ^ n).map f}
  | 0 => ⟨0, by rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; trivial⟩
  | n + 1 =>
    let p := approx f m hm a n
    let h := exists_sub_mem_map_pow_succ f m hm n _ p.2
    ⟨p.1 + h.choose, by
      have := h.choose_spec.2
      rwa [map_add, ← sub_sub]⟩

theorem approx_succ_sub {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (a : A) (n : ℕ) :
    (approx f m hm a (n + 1)).1 - (approx f m hm a n).1 ∈ m ^ n := by
  simp only [approx, add_sub_cancel_left]
  exact (exists_sub_mem_map_pow_succ f m hm n _ (approx f m hm a n).2).choose_spec.1

theorem approx_sub_mem {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (a : A) {k n : ℕ} (h : k ≤ n) :
    (approx f m hm a n).1 - (approx f m hm a k).1 ∈ m ^ k := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    have e : (approx f m hm a (n + 1)).1 - (approx f m hm a k).1 =
        ((approx f m hm a (n + 1)).1 - (approx f m hm a n).1) +
        ((approx f m hm a n).1 - (approx f m hm a k).1) := by ring
    rw [e]
    exact add_mem (Ideal.pow_le_pow_right hkn (approx_succ_sub f m hm a n)) ih

theorem surjective_of_residue_of_cotangent (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : R →+* A)
    (hc : IsAdicComplete (maximalIdeal R) R) (hf : IsLocalHom f)
    (hres : ∀ z : A, ∃ r, z - f r ∈ maximalIdeal A)
    (hcot : maximalIdeal A ≤ (maximalIdeal R).map f ⊔ maximalIdeal A ^ 2) :
    Function.Surjective f := by
  set m := maximalIdeal R

  have hle : maximalIdeal A ≤ m.map f := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A)
      (IsNoetherian.noetherian _) ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · simpa [pow_two, Ideal.smul_eq_mul] using hcot
  have hm : ∀ z : A, ∃ r, z - f r ∈ m.map f := fun z =>
    (hres z).imp fun r hr => hle hr
  have hmap : m.map f ≤ maximalIdeal A := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact map_nonunit f x hx
  intro a

  obtain ⟨L, hL⟩ := hc.prec' (fun n => (approx f m hm a n).1) (fun {k n} h => by
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
    exact approx_sub_mem f m hm a h)
  refine ⟨L, ?_⟩
  rw [eq_comm, ← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top,
    Ideal.mem_iInf]
  intro n
  have h1 := (approx f m hm a n).2
  have h2 := hL n
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at h2
  have e : a - f L = (a - f (approx f m hm a n).1) + f ((approx f m hm a n).1 - L) := by
    rw [map_sub]; ring
  rw [e]
  refine (Ideal.map_pow f m n ▸ Ideal.pow_right_mono hmap n) (add_mem h1 (Ideal.mem_map_of_mem f h2))

end GlobalTheory.LocalSurj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingEquivPowerSeriesPrescribedParameters

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CohenChart

open IsLocalRing MvPowerSeries

theorem sum_residue_smul_toCotangent {R : Type} [CommRing R] [IsLocalRing R] {Idx : Type} [Fintype Idx]
    (a : Idx → R) (y : Idx → R) (hy : ∀ i, y i ∈ maximalIdeal R) :
    ∑ i, residue R (a i) • (maximalIdeal R).toCotangent ⟨y i, hy i⟩ =
      (maximalIdeal R).toCotangent ⟨∑ i, a i * y i, sum_mem fun i _ => Ideal.mul_mem_left _ _ (hy i)⟩ := by
  have h : (⟨∑ i, a i * y i, sum_mem fun i _ => Ideal.mul_mem_left _ _ (hy i)⟩ : maximalIdeal R) =
      ∑ i, a i • (⟨y i, hy i⟩ : maximalIdeal R) := by
    ext; simp [smul_eq_mul]

  rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]

end GlobalTheory.CohenChart

namespace GlobalTheory.CohenChart

open IsLocalRing MvPowerSeries

theorem exists_ringEquiv_chartRing : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
    IsAdicComplete (maximalIdeal R) R → Nonempty (ℚ →+* R) → ∀ (m : ℕ) (t : Fin m → R),
    (∀ i, t i ∈ maximalIdeal R) →
    (∀ a : Fin m → R, ∑ i, a i * t i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R) →
    ∃ (k : Type) (_ : Field k) (e : ℕ) (σ : R ≃+* ChartRing k m e), ∀ i, σ (t i) = bdParam k m e i := by
  intro R _ _ hc hQ m t ht hind
  classical
  obtain ⟨q⟩ := hQ
  letI : Algebra ℚ (ResidueField R) := ((IsLocalRing.residue R).comp q).toAlgebra
  haveI : CharZero (ResidueField R) := algebraRat.charZero _
  haveI := hc
  obtain ⟨Λ, hF, hΛ⟩ := GlobalTheory.CohenRegular.exists_coefficientField_of_charZero R
  letI := hF.toField

  let v : Fin m → CotangentSpace R := fun i => (maximalIdeal R).toCotangent ⟨t i, ht i⟩
  have hv : LinearIndependent (ResidueField R) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a ha using fun j => residue_surjective (R := R) (g j)
    have h1 : ∑ j, residue R (a j) • v j = 0 := by simpa [ha] using hg
    rw [sum_residue_smul_toCotangent, Ideal.toCotangent_eq_zero] at h1
    rw [← ha i, residue_eq_zero_iff]
    exact hind a h1 i
  set d := Module.finrank (ResidueField R) (CotangentSpace R) with hd
  have hmd : m ≤ d := by simpa using hv.fintype_card_le_finrank
  set W := Submodule.span (ResidueField R) (Set.range v) with hW
  have hWd : Module.finrank (ResidueField R) (CotangentSpace R ⧸ W) = d - m := by
    have h1 := Submodule.finrank_quotient_add_finrank W
    have h2 : Module.finrank (ResidueField R) W = m := by rw [finrank_span_eq_card hv]; simp
    omega
  let b := Module.finBasisOfFinrankEq (ResidueField R) (CotangentSpace R ⧸ W) hWd
  choose w hw using fun j => W.mkQ_surjective (b j)
  choose s hs using fun j => (maximalIdeal R).toCotangent_surjective (w j)
  let x : Fin m ⊕ Fin (d - m) → R := Sum.elim t (fun j => (s j : R))
  have hx : ∀ j, x j ∈ maximalIdeal R := by
    rintro (j | j)
    exacts [ht j, (s j).2]
  let g : Fin m ⊕ Fin (d - m) → CotangentSpace R := fun j => (maximalIdeal R).toCotangent ⟨x j, hx j⟩
  set U := Submodule.span (ResidueField R) (Set.range g) with hU
  have hUtop : ∀ y : CotangentSpace R, y ∈ U := by
    intro y
    have hWU : W ≤ U := Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Sum.inl i, rfl⟩)
    have hwU : ∀ j, w j ∈ U := fun j => Submodule.subset_span ⟨Sum.inr j, by simp [g, x, hs]⟩
    have h1 : W.mkQ (y - ∑ j, b.repr (W.mkQ y) j • w j) = 0 := by

      simp only [map_sub, map_sum, map_smul, hw, b.sum_repr, sub_self]
    have h2 : y - ∑ j, b.repr (W.mkQ y) j • w j ∈ W := by
      rwa [← LinearMap.mem_ker, Submodule.ker_mkQ] at h1
    have h3 : ∑ j, b.repr (W.mkQ y) j • w j ∈ U := U.sum_mem fun j _ => U.smul_mem _ (hwU j)
    have := U.add_mem (hWU h2) h3
    simpa using this

  have hb : maximalIdeal Λ = ⊥ := isField_iff_maximalIdeal_eq.1 hF
  haveI : IsAdicComplete (maximalIdeal Λ) Λ := by rw [hb]; infer_instance
  let f : ChartRing Λ m (d - m) →ₐ[Λ] R := GlobalTheory.mvEvalAdic Λ (maximalIdeal R) x hx
  have hfX : ∀ j, f (X j) = x j := fun j => GlobalTheory.mvEvalAdic_X (A := Λ) (maximalIdeal R) x hx j
  have hfC : ∀ a : Λ, f (C a) = a := fun a => GlobalTheory.mvEvalAdic_C (A := Λ) (maximalIdeal R) x hx a
  have hle : ∀ g ∈ maximalIdeal (ChartRing Λ m (d - m)), f g ∈ maximalIdeal R := by
    intro g hg
    have h4 := GlobalTheory.algHom_sub_constantCoeff_mem f (K := maximalIdeal R) (fun j => by rw [hfX]; exact hx j) g
    have h5 := GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    rw [hb, Ideal.mem_bot] at h5
    rwa [h5, map_zero, sub_zero] at h4
  have hXm : ∀ j, (X j : ChartRing Λ m (d - m)) ∈ maximalIdeal (ChartRing Λ m (d - m)) := fun j =>
    GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp)
  have hloc : IsLocalHom (f : ChartRing Λ m (d - m) →+* R) := ⟨fun g hg => by
    by_contra hn
    exact (hle g hn) hg⟩
  have hres : ∀ z : R, ∃ r, z - (f : ChartRing Λ m (d - m) →+* R) r ∈ maximalIdeal R := by
    intro z
    obtain ⟨a, ha, h⟩ := hΛ z
    exact ⟨C ⟨a, ha⟩, by simpa [hfC] using h⟩
  have hcot : maximalIdeal R ≤ (maximalIdeal (ChartRing Λ m (d - m))).map (f : ChartRing Λ m (d - m) →+* R) ⊔
      maximalIdeal R ^ 2 := by
    intro z hz
    obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun (ResidueField R)).1
      (hUtop ((maximalIdeal R).toCotangent ⟨z, hz⟩))
    choose a ha using fun j => residue_surjective (R := R) (c j)
    have h1 : ∑ j, residue R (a j) • g j = (maximalIdeal R).toCotangent ⟨z, hz⟩ := by simpa [ha] using hc'
    rw [sum_residue_smul_toCotangent, Ideal.toCotangent_eq] at h1
    have h2 : ∑ j, a j * x j ∈ (maximalIdeal (ChartRing Λ m (d - m))).map (f : ChartRing Λ m (d - m) →+* R) :=
      sum_mem fun j _ => Ideal.mul_mem_left _ _ (by rw [← hfX]; exact Ideal.mem_map_of_mem _ (hXm j))
    have h3 : z = ∑ j, a j * x j + (z - ∑ j, a j * x j) := by ring
    rw [h3]
    refine Submodule.add_mem_sup h2 ?_
    have : (z - ∑ j, a j * x j) = -((∑ j, a j * x j) - z) := by ring
    rw [this]
    exact neg_mem h1
  have hcA : IsAdicComplete (maximalIdeal (ChartRing Λ m (d - m))) (ChartRing Λ m (d - m)) :=
    GlobalTheory.CohenStructure.isAdicComplete_of_ringEquiv
      (MvPowerSeries.renameEquiv Λ finSumFinEquiv.symm).toRingEquiv
      (h := GlobalTheory.CohenStructure.isAdicComplete_mvPowerSeries Λ (m + (d - m)))
  have hsurj : Function.Surjective (f : ChartRing Λ m (d - m) →+* R) :=
    GlobalTheory.LocalSurj.surjective_of_residue_of_cotangent _ R _ hcA hloc hres hcot
  letI : Algebra (ChartRing Λ m (d - m)) R := (f : ChartRing Λ m (d - m) →+* R).toAlgebra
  haveI : Module.Finite (ChartRing Λ m (d - m)) R :=
    Module.Finite.of_surjective (Algebra.linearMap (ChartRing Λ m (d - m)) R) hsurj
  have hdA : ringKrullDim (ChartRing Λ m (d - m)) = ((m + (d - m) : ℕ) : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_isField hF, Nat.card_sum,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin, zero_add]
  have hdR : ringKrullDim R = ((m + (d - m) : ℕ) : WithBot ℕ∞) := by
    rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance, ← hd]
    have hmd' : m + (d - m) = d := by omega
    rw [hmd']
  have hinj : Function.Injective (f : ChartRing Λ m (d - m) →+* R) :=
    GlobalTheory.CohenStructure.injective_of_ringKrullDim_eq hdA hdR
  let φ := RingEquiv.ofBijective (f : ChartRing Λ m (d - m) →+* R) ⟨hinj, hsurj⟩
  refine ⟨Λ, inferInstance, d - m, φ.symm, fun i => ?_⟩
  rw [RingEquiv.symm_apply_eq]
  show t i = f (X (Sum.inl i))
  rw [hfX]
  rfl

end GlobalTheory.CohenChart
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingEquivPowerSeriesPrescribedParametersStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_ringEquiv_powerSeries_prescribed_parameters : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → Nonempty (ℚ →+* R) → ∀ (m : ℕ) (t : Fin m → R), (∀ i, t i ∈ maximalIdeal R) → (∀ a : Fin m → R, ∑ i, a i * t i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R) → ∃ (k : Type) (_ : Field k) (e : ℕ) (σ : R ≃+* ChartRing k m e), ∀ i, σ (t i) = bdParam k m e i := by
  first | exact @GlobalTheory.CohenChart.exists_ringEquiv_chartRing | exact GlobalTheory.CohenChart.exists_ringEquiv_chartRing | (intros; apply GlobalTheory.CohenChart.exists_ringEquiv_chartRing <;> assumption)
end
end
