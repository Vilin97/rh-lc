module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ClassGroupDivMemOfMulConjEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.LocFin
public import GroundTheory.GlobalFields.IdeleGroups.LocalNorms
public import Mathlib.NumberTheory.NumberField.CMField
import GroundTheory.GlobalFields.InfiniteNormIndex.LocalSymbol
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
import Formalism.ConjugateSelfDual.Statement
import Formalism.GaloisCohomology.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
public import GroundTheory.GlobalFields.HasseNorm
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.LocInf

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.locInf :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (x : (maximalRealSubfield K)ˣ), (∀ φ : K →+* ℂ, 0 < (φ (algebraMap (maximalRealSubfield K) K x)).re) → ∀ v, GroundTheory.Global.IdeleGroup.infiniteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) x) ∈ (GroundTheory.Global.IdeleNorm.infiniteLocalNorm K v).range := by
  intro K _ _ _ x hx v
  classical
  obtain ⟨W, rfl⟩ := InfinitePlace.comap_surjective (k := maximalRealSubfield K) (K := K) v
  set u := W.comap (algebraMap (maximalRealSubfield K) K) with hu_def
  have hWu : W.LiesOver u := { under_eq := rfl }
  have hu : u.IsReal := IsTotallyReal.isReal u
  have hpos : 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hu
      (algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K)) := by
    have h0 : InfinitePlace.Completion.ringEquivRealOfIsReal hu
        (algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K)) =
        InfinitePlace.embedding_of_isReal hu (x : maximalRealSubfield K) := by
      change InfinitePlace.Completion.extensionEmbeddingOfIsReal hu _ = _
      rw [InfinitePlace.Completion.algebraMap_apply]
      exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hu _
    rw [h0]
    have h1 := InfinitePlace.embedding_of_isReal_apply hu (x : maximalRealSubfield K)
    have h3 := hx W.embedding
    rcases InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq W u with h2 | h2
    · have h4 := congrArg (fun f => (f (x : maximalRealSubfield K)).re) h2
      simp only [RingHom.coe_comp, Function.comp_apply] at h4
      rw [h4, ← h1] at h3
      rwa [Complex.ofReal_re] at h3
    · have h4 := congrArg (fun f => (f (x : maximalRealSubfield K)).re) h2
      simp only [RingHom.coe_comp, Function.comp_apply, ComplexEmbedding.conjugate_coe_eq,
        Complex.conj_re] at h4
      rw [h4, ← h1] at h3
      rwa [Complex.ofReal_re] at h3
  letI : Algebra u.Completion W.Completion := AbsoluteValue.Completion.algebraOfLiesOver u.1 W.1
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hu with he
  set a := algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K) with ha
  set d := Module.finrank u.Completion W.Completion with hd_def
  have hd : 0 < d := by
    rcases W.isUnramified_or_isRamified (maximalRealSubfield K) with h | h
    · rw [hd_def, h.finrank_eq_one u]; norm_num
    · rw [hd_def, h.finrank_eq_two u]; norm_num
  set r : u.Completion := e.symm (e a ^ ((d : ℝ)⁻¹)) with hr_def
  have hr : r ^ d = a := by
    apply e.injective
    rw [map_pow, hr_def, RingEquiv.apply_symm_apply, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le,
      inv_mul_cancel₀ (by exact_mod_cast hd.ne'), Real.rpow_one]
  have ha0 : a ≠ 0 := by
    rw [ha]
    exact (map_ne_zero _).mpr x.ne_zero
  have hr0 : algebraMap u.Completion W.Completion r ≠ 0 := by
    rw [map_ne_zero]
    rintro h0
    rw [h0, zero_pow hd.ne'] at hr
    exact ha0 hr.symm
  let w0 : ↑(InfinitePlace.placesOver K u) := ⟨W, hWu⟩
  refine ⟨Pi.mulSingle w0 (Units.mk0 _ hr0), ?_⟩
  apply Units.ext
  simp only [GroundTheory.Global.IdeleNorm.infiniteLocalNorm, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Fintype.prod_eq_single w0 (fun w hw => by rw [Pi.mulSingle_eq_of_ne hw, map_one]),
    Pi.mulSingle_eq_same, Units.coe_map, Units.val_mk0]
  rw [GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal]
  rw [← InfinitePlace.Completion.algebraMap_apply]
  change Algebra.norm u.Completion (algebraMap u.Completion W.Completion r) = a
  rw [Algebra.norm_algebraMap, ← hd_def, hr]
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormEqMulCE

section

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.Qh29.cE :
    (E : Type) → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsCMField E] → E ≃+* E :=
    fun (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] ↦ (NumberField.IsCMField.complexConj E).toRingEquiv

theorem UpperTheory.Reformulated.B.Qh29.norm_eq_mul_cE :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K] [inst_2 : NumberField.IsCMField K] (y : K),
      (Algebra.algebraMap (↥(NumberField.maximalRealSubfield K)) K : ↥(NumberField.maximalRealSubfield K) → K)
          ((Algebra.norm ↥(NumberField.maximalRealSubfield K) : K → ↥(NumberField.maximalRealSubfield K)) y) =
        y * (UpperTheory.Reformulated.B.Qh29.cE K : K → K) y := by
  intro K _ _ _ y
  classical
  have hne := NumberField.IsCMField.complexConj_ne_one K
  have hcard : Nat.card (K ≃ₐ[NumberField.maximalRealSubfield K] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have huniv : (Finset.univ : Finset (K ≃ₐ[NumberField.maximalRealSubfield K] K)) =
      {1, NumberField.IsCMField.complexConj K} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne.symm, ← Nat.card_eq_fintype_card, hcard]
  have h := Algebra.norm_eq_prod_automorphisms (NumberField.maximalRealSubfield K) y
  rw [huniv, Finset.prod_pair hne.symm] at h
  exact h
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Mk0PrincipalEqOne

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem norm_eq_mul_cE (K : Type) [Field K] [NumberField K] [IsCMField K] (y : K) :
    algebraMap (maximalRealSubfield K) K (Algebra.norm (maximalRealSubfield K) y) = y * cE K y :=
  _root_.UpperTheory.Reformulated.B.Qh29.norm_eq_mul_cE K y

private def prI {K : Type} [Field K] [NumberField K] (b : 𝓞 K) (hb : b ≠ 0) : (Ideal (𝓞 K))⁰ :=
  ⟨Ideal.span {b}, mem_nonZeroDivisors_of_ne_zero (by simpa using hb)⟩

private theorem mk0_principal_eq_one {K : Type} [Field K] [NumberField K] (b : 𝓞 K) (hb : b ≠ 0) :
    ClassGroup.mk0 (prI b hb) = 1 :=
  (ClassGroup.mk0_eq_one_iff _).2 ⟨⟨b, rfl⟩⟩

private theorem prI_mul {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (b : 𝓞 K) (hb : b ≠ 0) :
    (prI b hb * idMap τ (prI b hb)).1 = Ideal.span {b * RingOfIntegers.mapRingEquiv τ b} := by
  change Ideal.span {b} * (Ideal.span {b}).map (RingOfIntegers.mapRingEquiv τ) = _
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_mul_span_singleton]

theorem UpperTheory.V.FW.hasse :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (a : 𝓞 K) (I : (Ideal (𝓞 K))⁰), UnrFin K → cE K (a : K) = a → (∀ φ : K →+* ℂ, 0 < (φ (a : K)).re) → (I * idMap (cE K) I).1 = Ideal.span {a} → ClassGroup.mk0 I ∈ difR (clMap (cE K)) := by
  intro K _ _ _ a I hU ha hpos hI
  have ha0 : a ≠ 0 := by
    intro h
    have := nonZeroDivisors.ne_zero (I * idMap (cE K) I).2
    rw [hI, h] at this
    simp at this
  have ha0' : (a : K) ≠ 0 := by simpa using ha0
  have hmem : (a : K) ∈ maximalRealSubfield K := (IsCMField.complexConj_eq_self_iff K _).1 ha
  have hx0 : (⟨a, hmem⟩ : maximalRealSubfield K) ≠ 0 := fun h => ha0' (congrArg Subtype.val h)
  have hax : (a : K) = algebraMap (maximalRealSubfield K) K (Units.mk0 _ hx0 : (maximalRealSubfield K)ˣ) := rfl
  obtain ⟨β, hβ⟩ := (GroundTheory.Global.mem_range_norm_iff_forall_local_of_finrank_eq_two (L := K)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (Units.mk0 _ hx0)).2
    ⟨locFin K _ a I hU hax hI, locInf K _ fun φ => hax ▸ hpos φ⟩
  have hβ' : (β : K) * cE K β = a := by
    rw [← norm_eq_mul_cE, hax, ← hβ]
    rfl
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (β : K)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd0' : (d : K) ≠ 0 := by simpa using hd0
  have hb : (b : K) = d * β := by
    rw [← hbd]
    exact (mul_div_cancel₀ _ hd0').symm
  have hb0 : b ≠ 0 := by
    intro h
    rw [h] at hb
    exact mul_ne_zero hd0' β.ne_zero (by simpa using hb.symm)
  have key : d * RingOfIntegers.mapRingEquiv (cE K) d * a = b * RingOfIntegers.mapRingEquiv (cE K) b := by
    apply Subtype.ext
    change (d : K) * cE K d * a = (b : K) * cE K b
    rw [hb, map_mul, ← hβ']
    ring
  have := classGroup_div_mem_of_mul_conj_eq K (cE K) (prI d hd0 * I) (prI b hb0) (IsCMField.complexConj_apply_apply K) (by
    apply Subtype.ext
    rw [map_mul, mul_mul_mul_comm, Submonoid.coe_mul, hI, prI_mul, prI_mul,
      Ideal.span_singleton_mul_span_singleton, key])
  rwa [map_mul, mk0_principal_eq_one, mk0_principal_eq_one, one_mul, div_one] at this
end
end
