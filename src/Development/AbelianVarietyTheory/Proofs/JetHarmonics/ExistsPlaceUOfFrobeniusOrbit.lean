module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.RingHoms
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowOfFiniteField
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IdempotentEmbeddingsCard
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.IncomingBounds.IncomingBound
import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TauBasisUnitDeterminant
import Mathlib.RingTheory.Henselian
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Formalism.LocalToGlobal.Divisibility.Numbers

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CardOrthogonalIdempotentsLeNcardPrimesOver

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem padicTensor_eq_mul_add (A : Type) [CommRing A] (p : ℕ) [Fact p.Prime]
    (r : ℤ_[p] ⊗[ℤ] A) :
    ∃ (s : ℤ_[p] ⊗[ℤ] A) (x : A), r = (p : ℤ_[p] ⊗[ℤ] A) * s + (1 : ℤ_[p]) ⊗ₜ[ℤ] x := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a x =>
    have h := PadicInt.zmodRepr_spec a
    obtain ⟨-, h⟩ := h
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨c ⊗ₜ[ℤ] x, (a.zmodRepr : ℤ) • x, ?_⟩
    have ha : a = (p : ℕ) • c + (a.zmodRepr : ℤ) • (1 : ℤ_[p]) := by
      rw [nsmul_eq_mul, ← hc]; simp
    rw [← nsmul_eq_mul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      ← TensorProduct.add_tmul, ← ha]
  | add a b ha hb =>
    obtain ⟨s, x, rfl⟩ := ha
    obtain ⟨s', x', rfl⟩ := hb
    exact ⟨s + s', x + x', by rw [TensorProduct.tmul_add]; ring⟩

end GlobalTheory.CharDepth
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPrimitiveIdempotentMapEqOne

section

@[expose] public section

open TensorProduct

namespace GlobalTheory

theorem exists_primitive_idempotent_map_eq_one {A R : Type*} [CommRing A] [IsNoetherianRing A]
    [CommRing R] [IsDomain R] (φ : A →+* R) :
    ∃ e : A, e * e = e ∧ e ≠ 0 ∧ (∀ f : A, f * f = f → f * e = f → f = 0 ∨ f = e) ∧ φ e = 1 := by
  let S : Set (Ideal A) := {I | ∃ e : A, e * e = e ∧ φ e = 1 ∧ I = Ideal.span {1 - e}}
  have hS : S.Nonempty := ⟨_, 1, by simp, by simp, rfl⟩
  obtain ⟨I, ⟨e, he, hφe, rfl⟩, hmax⟩ :=
    (set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian A A)) S hS
  have key : ∀ f : A, f * f = f → f * e = f → φ f = 1 → f = e := by
    intro f hf hfe hφf
    have hle : Ideal.span {1 - e} ≤ Ideal.span {1 - f} := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton']
      exact ⟨1 - e, by linear_combination hfe⟩
    have heq : Ideal.span {1 - e} = Ideal.span {1 - f} := by
      by_contra hne
      exact hmax _ ⟨f, hf, hφf, rfl⟩ (lt_of_le_of_ne hle hne)
    have hmem : 1 - f ∈ Ideal.span {1 - e} := heq ▸ Ideal.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    linear_combination e * hc - hfe + c * he
  refine ⟨e, he, ?_, ?_, hφe⟩
  · rintro rfl
    simp at hφe
  · intro f hf hfe
    have hid : IsIdempotentElem (φ f) := by
      change φ f * φ f = φ f
      rw [← map_mul, hf]
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 hid with h | h
    · left
      have := key (e - f) (by linear_combination he + hf - 2 * hfe)
        (by linear_combination he - hfe) (by rw [map_sub, h, hφe, sub_zero])
      linear_combination -this
    · exact Or.inr (key f hf hfe h)

theorem exists_placeU_mem_emb (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Finite ℤ OE] (R : Type) [CommRing R] [IsDomain R] [Algebra ℤ_[p] R] (σ : OE →+* R) :
    ∃ w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p OE,
      σ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e := by
  haveI : IsNoetherianRing (ℤ_[p] ⊗[ℤ] OE) :=
    IsNoetherianRing.of_finite ℤ_[p] _
  obtain ⟨e, h1, h2, h3, h4⟩ := exists_primitive_idempotent_map_eq_one
    (ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (p := p) σ).toRingHom
  exact ⟨⟨e, h1, h2, h3⟩, h4⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EmbeddingsCongruentEq

section

@[expose] public section

open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory

theorem ringOfIntegers_hom_injective (E : Type) [Field E] [NumberField E] (C : Type) [Field C]
    [CharZero C] (f : 𝓞 E →+* C) : Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  simp only [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
  simpa using hn

theorem ringOfIntegers_hom_eq_of_congr_maximalIdeal :
    ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ¬ ((p : ℤ) ∣ NumberField.discr E) → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsLocalRing O] [Algebra O C], v.Integers O → ¬ IsUnit (p : O) → ∀ σ σ' : 𝓞 E →+* O, (∀ x, σ x - σ' x ∈ maximalIdeal O) → σ = σ' := by
  intro E _ _ p hp hd C _ _ _ v O _ _ _ hv hpu σ σ' hcong
  classical
  by_contra hne
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj

  have hext : ∀ s : 𝓞 E →+* O, ∃ τ : E →ₐ[ℚ] C,
      ∀ x : 𝓞 E, τ (algebraMap (𝓞 E) E x) = algebraMap O C (s x) := by
    intro s
    refine ⟨(IsFractionRing.lift (K := E)
      (ringOfIntegers_hom_injective E C ((algebraMap O C).comp s))).toRatAlgHom, fun x => ?_⟩
    simp
  obtain ⟨τ, hτ⟩ := hext σ
  obtain ⟨τ', hτ'⟩ := hext σ'
  have hττ : τ ≠ τ' := by
    intro h
    apply hne
    ext x
    apply hinj
    rw [← hτ, ← hτ', h]
  have hmem : ∀ (φ : E →ₐ[ℚ] C) (x : 𝓞 E), ∃ y : O,
      algebraMap O C y = φ (algebraMap (𝓞 E) E x) := by
    intro φ x
    have h1 : IsIntegral ℤ (φ (algebraMap (𝓞 E) E x)) :=
      (x.isIntegral_coe).map (φ.toRingHom.toIntAlgHom)
    have h2 : IsIntegral O (φ (algebraMap (𝓞 E) E x)) := h1.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral h2)
  choose F hF using hmem
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let e : ι ≃ (E →ₐ[ℚ] C) := Fintype.equivOfCardEq (by
    rw [AlgHom.card, Module.finrank_eq_card_basis (integralBasis E)])
  let N : Matrix ι ι O := fun i j => F (e j) (RingOfIntegers.basis E i)
  have hN : (algebraMap O C).mapMatrix N =
      Algebra.embeddingsMatrixReindex ℚ C (integralBasis E) e := by
    ext i j
    show algebraMap O C (F (e j) (RingOfIntegers.basis E i)) = _
    simp [hF, Algebra.embeddingsMatrixReindex, integralBasis_apply]
  have hdisc : ((NumberField.discr E : ℤ) : O) = N.det ^ 2 := by
    apply hinj
    rw [map_pow, RingHom.map_det, hN, ← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two,
      ← NumberField.coe_discr]
    simp
  have hdet : N.det ∈ maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, RingHom.map_det]
    apply Matrix.det_zero_of_column_eq (i := e.symm τ) (j := e.symm τ')
      (fun h => hττ (e.symm.injective h))
    intro k
    show residue O (F (e (e.symm τ)) (RingOfIntegers.basis E k)) =
      residue O (F (e (e.symm τ')) (RingOfIntegers.basis E k))
    simp only [Equiv.apply_symm_apply]
    have a1 : F τ (RingOfIntegers.basis E k) = σ (RingOfIntegers.basis E k) :=
      hinj (by rw [hF, hτ])
    have a2 : F τ' (RingOfIntegers.basis E k) = σ' (RingOfIntegers.basis E k) :=
      hinj (by rw [hF, hτ'])
    rw [a1, a2, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hcong _
  have hdm : ((NumberField.discr E : ℤ) : O) ∈ maximalIdeal O := by
    rw [hdisc]
    exact Ideal.pow_mem_of_mem _ hdet 2 (by norm_num)
  have hpm : (p : O) ∈ maximalIdeal O := hpu
  have hcop : IsCoprime (p : ℤ) (NumberField.discr E) :=
    (Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr hd
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (1 : O) ∈ maximalIdeal O := by
    have := congrArg (Int.cast : ℤ → O) hab
    push_cast at this
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ hdm)
  exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPlaceUOfFrobeniusOrbit

section

@[expose] public section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.OrbitPlace


open ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs in
theorem mem_emb_of_congr_pow (A : Type) [CommRing A] (p : ℕ) [Fact p.Prime] (O : Type)
    [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O] (hp : ¬ IsUnit (p : O))
    (e : ℤ_[p] ⊗[ℤ] A) (he : e * e = e) (σ σ' : A →+* O)
    (h : ∀ x, σ' x - σ x ^ p ∈ IsLocalRing.maximalIdeal O) (hσ : σ ∈ Emb (O := O) e) :
    σ' ∈ Emb (O := O) e := by
  obtain ⟨s, x, hx⟩ := GlobalTheory.CharDepth.padicTensor_eq_mul_add A p e
  have hp0 : IsLocalRing.residue O (p : O) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 hp
  have key : ∀ ρ : A →+* O,
      IsLocalRing.residue O (tauExt ρ e) = IsLocalRing.residue O (ρ x) := by
    intro ρ
    have h1 : tauExt (p := p) ρ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) = ρ x := by simp [tauExt]
    rw [hx, map_add (f := _), map_mul, map_natCast, h1, map_add (f := _), map_mul, hp0, zero_mul, zero_add]
  have h1 : IsLocalRing.residue O (σ x) = 1 := by
    have : tauExt σ e = 1 := hσ
    rw [← key, this, map_one]
  have h2 : IsLocalRing.residue O (tauExt σ' e) = 1 := by
    have := (IsLocalRing.residue_eq_zero_iff _).2 (h x)
    rw [map_sub, map_pow, h1, one_pow, sub_eq_zero] at this
    rw [key, this]
  have hu : IsUnit (tauExt σ' e) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, h2]
    exact one_ne_zero
  have hid : tauExt σ' e * tauExt σ' e = tauExt σ' e * 1 := by rw [← map_mul, he, mul_one]
  exact hu.mul_left_cancel hid

theorem exists_placeU_of_frobenius_orbit : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [IsLocalRing O] [Algebra ℤ_[p] O], ¬ IsUnit (p : O) → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (d : ℕ) [NeZero d] (τ : ZMod d → (𝓞 E →+* O)), Function.Injective τ → (∀ s x, τ (s + 1) x - τ s x ^ p ∈ IsLocalRing.maximalIdeal O) → ∃ (w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p (𝓞 E)) (_ : w.n = d) (t : Fin w.n ≃ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e), (∀ j : Fin w.n, ((t j : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e) : 𝓞 E →+* O) = τ ((j.val : ℕ) : ZMod d)) ∧ ∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)), IsUnit (Matrix.det (Matrix.of fun i j => ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt ((t j : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e) : 𝓞 E →+* O) (b i : ℤ_[p] ⊗[ℤ] 𝓞 E))) := by
  intro E _ _ p hpp C _ _ _ v O _ _ hv _ _ hp hd d _ τ hτ hfr
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  obtain ⟨w, hw⟩ := GlobalTheory.exists_placeU_mem_emb p (𝓞 E) O (τ 0)
  have hsep := GlobalTheory.ringOfIntegers_hom_eq_of_congr_maximalIdeal E p hpp.out hd C v O hv hp
  have hmem : ∀ k : ℕ, τ (k : ZMod d) ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e := by
    intro k
    induction k with
    | zero => simpa using hw
    | succ k ih =>
      rw [Nat.cast_succ]
      exact mem_emb_of_congr_pow _ p O hp w.e w.idem _ _ (hfr _) ih
  have hpow : ∀ (k : ℕ) x, IsLocalRing.residue O (τ (k : ZMod d) x) =
      IsLocalRing.residue O (τ 0 x) ^ (p ^ k) := by
    intro k x
    induction k with
    | zero => simp
    | succ k ih =>
      have := (IsLocalRing.residue_eq_zero_iff _).2 (hfr (k : ZMod d) x)
      rw [map_sub, map_pow, sub_eq_zero] at this
      rw [Nat.cast_succ, this, ih, ← pow_mul, pow_succ]
  have hsurj : ∀ σ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e, ∃ s, τ s = σ := by
    intro σ hσ
    obtain ⟨i, hi⟩ := GlobalTheory.EmbFrob.exists_frobenius_pow p (𝓞 E) C v O hv hp w (τ 0) σ hw hσ
    refine ⟨(i : ZMod d), hsep _ _ fun x => ?_⟩
    have h1 : σ x - τ 0 x ^ (p ^ i) ∈ IsLocalRing.maximalIdeal O := by
      intro hu
      exact (hi x).ne (hv.one_of_isUnit hu)
    have := (IsLocalRing.residue_eq_zero_iff _).2 h1
    rw [map_sub, map_pow, sub_eq_zero] at this
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hpow, this, sub_self]
  have hmem' : ∀ s : ZMod d, τ s ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e := by
    intro s
    have := hmem s.val
    rwa [ZMod.natCast_zmod_val] at this
  have hbij : Function.Bijective
      (fun s : ZMod d => (⟨τ s, hmem' s⟩ : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e)) :=
    ⟨fun a b h => hτ (congrArg Subtype.val h), fun σ => by
      obtain ⟨s, hs⟩ := hsurj σ.1 σ.2
      exact ⟨s, Subtype.ext hs⟩⟩
  obtain ⟨⟨t₀⟩, -⟩ := GlobalTheory.EmbCount.card_emb E p C v O hv w.e w.idem
  have hn : w.n = d := by
    have h1 := Nat.card_congr (t₀.trans (Equiv.ofBijective _ hbij).symm)
    rw [Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    exact h1
  have hcast : Function.Bijective (fun j : Fin w.n => ((j.val : ℕ) : ZMod d)) := by
    refine ⟨fun a b h => ?_, fun s => ⟨⟨s.val, hn ▸ ZMod.val_lt s⟩, ZMod.natCast_zmod_val s⟩⟩
    have h' := congrArg ZMod.val h
    simp only [ZMod.val_natCast] at h'
    rw [Nat.mod_eq_of_lt (hn ▸ a.2), Nat.mod_eq_of_lt (hn ▸ b.2)] at h'
    exact Fin.ext h'
  let t : Fin w.n ≃ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e :=
    (Equiv.ofBijective _ hcast).trans (Equiv.ofBijective _ hbij)
  refine ⟨w, hn, t, fun j => rfl, ?_⟩
  exact GlobalTheory.tau_basis_unit_determinant.exists_basis_isUnit_det p (𝓞 E) O w (fun j => (t j).1) (fun j => (t j).2)
    (fun j j' h => t.injective (Subtype.ext (hsep _ _ h)))

end GlobalTheory.OrbitPlace
end
end
