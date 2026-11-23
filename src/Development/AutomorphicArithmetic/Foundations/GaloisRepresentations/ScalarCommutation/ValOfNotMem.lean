module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIdemP
public import GroundTheory.AutomorphicForms.HermitianSpaces
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import GroundTheory.AutomorphicForms.StableConjCyclic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: GroundTheory.AutomorphicForms.StableConjTorus

section

@[expose] public section

namespace GroundTheory.Automorphic

open Module

section CommuteField

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]

theorem commute_of_commute_of_separable_charpoly {f g g' : Module.End E V}
    (hf : f.charpoly.Separable) (hg : Commute f g) (hg' : Commute f g') : Commute g g' := by
  classical
  set n := finrank E V
  let b : Basis (Fin n) E V := Module.finBasis E V
  let K := AlgebraicClosure E
  let φ : E →+* K := algebraMap E K
  let Φ : Module.End E V →+* Matrix (Fin n) (Fin n) K :=
    φ.mapMatrix.comp (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom
  let Ψ : Matrix (Fin n) (Fin n) K →+* Module.End K (Fin n → K) :=
    (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).toRingEquiv.toRingHom
  have hsep : (Ψ (Φ f)).charpoly.Separable := by
    change (Matrix.toLin' ((LinearMap.toMatrix b b f).map φ)).charpoly.Separable
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
    exact hf.map
  have hc := commute_of_commute_of_separable hsep ((hg.map Φ).map Ψ) ((hg'.map Φ).map Ψ)
  have hinj : Function.Injective (Ψ.comp Φ) := by
    intro x y hxy
    have h1 : Φ x = Φ y := (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).injective hxy
    have h2 : LinearMap.toMatrixAlgEquiv b x = LinearMap.toMatrixAlgEquiv b y := by
      ext i j
      exact φ.injective (congrFun (congrFun h1 i) j)
    exact (LinearMap.toMatrixAlgEquiv b).injective h2
  change g * g' = g' * g
  apply hinj
  rw [map_mul, map_mul]
  exact hc.eq

end CommuteField

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V]

namespace HermitianForm

variable (h : HermitianForm F E V)

noncomputable def adjoint (A : Module.End E V) : Module.End E V where
  toFun y := (Equiv.ofBijective _ h.nonsingular).symm ((h.toSesq y).comp A)
  map_add' x y := by
    apply h.nonsingular.1
    simp only [Equiv.ofBijective_apply_symm_apply, map_add (f := _), LinearMap.add_comp]
  map_smul' c x := by
    apply h.nonsingular.1
    simp only [Equiv.ofBijective_apply_symm_apply, LinearMap.map_smulₛₗ, LinearMap.smul_comp,
      RingHom.id_apply]

theorem toSesq_adjoint_left (A : Module.End E V) (y x : V) :
    h.toSesq (h.adjoint A y) x = h.toSesq y (A x) := by
  change h.toSesq ((Equiv.ofBijective _ h.nonsingular).symm ((h.toSesq y).comp A)) x = _
  rw [Equiv.ofBijective_apply_symm_apply (⇑h.toSesq) h.nonsingular]
  rfl

theorem eq_adjoint_iff (A B : Module.End E V) :
    B = h.adjoint A ↔ ∀ y x, h.toSesq (B y) x = h.toSesq y (A x) := by
  refine ⟨fun hB y x => hB ▸ h.toSesq_adjoint_left A y x, fun hB => LinearMap.ext fun y => ?_⟩
  apply h.nonsingular.1
  ext x
  rw [hB, toSesq_adjoint_left]

theorem adjoint_mul (A B : Module.End E V) : h.adjoint (A * B) = h.adjoint B * h.adjoint A := by
  symm
  rw [eq_adjoint_iff]
  intro y x
  rw [Module.End.mul_apply, toSesq_adjoint_left, toSesq_adjoint_left, Module.End.mul_apply]

theorem adjoint_one : h.adjoint 1 = 1 := by
  symm
  rw [eq_adjoint_iff]
  intro y x
  rfl

noncomputable def adjointEquiv (g : V ≃ₗ[E] V) : V ≃ₗ[E] V where
  toLinearMap := h.adjoint g.toLinearMap
  invFun := h.adjoint g.symm.toLinearMap
  left_inv x := by
    change (h.adjoint g.symm.toLinearMap * h.adjoint g.toLinearMap) x = x
    rw [← adjoint_mul]
    have : g.toLinearMap * g.symm.toLinearMap = 1 := by
      ext y; simp
    rw [this, adjoint_one]
    rfl
  right_inv x := by
    change (h.adjoint g.toLinearMap * h.adjoint g.symm.toLinearMap) x = x
    rw [← adjoint_mul]
    have : g.symm.toLinearMap * g.toLinearMap = 1 := by
      ext y; simp
    rw [this, adjoint_one]
    rfl

end HermitianForm

section Stable

variable [FiniteDimensional E V]

def IsRegularSemisimple (γ : V ≃ₗ[E] V) : Prop :=
  (γ.toLinearMap).charpoly.Separable

def torusE (γ : V ≃ₗ[E] V) : Subgroup (V ≃ₗ[E] V) :=
  Subgroup.centralizer {γ}



def TorusE (γ : V ≃ₗ[E] V) : Type _ := torusE γ

namespace TorusE

variable {γ : V ≃ₗ[E] V}




variable [Fact (IsRegularSemisimple γ)]

end TorusE

end Stable

end GroundTheory.Automorphic
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ValOfNotMem

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp mat sim AfQ)
open UpperTheory.Gal.W2.Seed
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open scoped TensorProduct

namespace UpperTheory.Gal.Spc

private theorem mat_comm {K : Type} [Field K] {n : ℕ} {A B C : Matrix (Fin n) (Fin n) K}
    (hA : A.charpoly.Separable) (hB : A * B = B * A) (hC : A * C = C * A) : B * C = C * B := by
  have hsep : (Matrix.toLin' A).charpoly.Separable := by
    have := LinearMap.charpoly_toMatrix (Matrix.toLin' A) (Pi.basisFun K (Fin n))
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] at this
    rwa [← this]
  have h := GroundTheory.Automorphic.commute_of_commute_of_separable_charpoly (f := Matrix.toLin' A) (g := Matrix.toLin' B)
    (g' := Matrix.toLin' C) hsep
    (by show _ * _ = _ * _
        rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hB])
    (by show _ * _ = _ * _
        rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hC])
  have h2 : Matrix.toLin' (B * C) = Matrix.toLin' (C * B) := by
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul]; exact h
  exact Matrix.toLin'.injective h2

private theorem tensor_comm {R Q C : Type} [CommRing R] [Algebra ℚ R] [CommRing Q] [Algebra ℚ Q] [Ring C] [Algebra ℚ C]
    (ev : R →ₐ[ℚ] Q) (r : R) (s : Q →ₗ[ℚ] R) (hs1 : ∀ x, ev (s x) = x) (hs2 : ∀ a, s (ev a) = r * a) (hr : ev r = 1)
    (M : R ⊗[ℚ] C)
    (H : ∀ x y : R ⊗[ℚ] C, (r ⊗ₜ[ℚ] (1 : C)) * (x * M - M * x) = 0 → (r ⊗ₜ[ℚ] (1 : C)) * (y * M - M * y) = 0 →
      (r ⊗ₜ[ℚ] (1 : C)) * (x * y - y * x) = 0)
    (x y : Q ⊗[ℚ] C) (hx : Commute x (Algebra.TensorProduct.map ev (AlgHom.id ℚ C) M))
    (hy : Commute y (Algebra.TensorProduct.map ev (AlgHom.id ℚ C) M)) : Commute x y := by
  set EV := Algebra.TensorProduct.map ev (AlgHom.id ℚ C) with hEV
  let σ : Q ⊗[ℚ] C →ₗ[ℚ] R ⊗[ℚ] C := LinearMap.rTensor C s
  have h1 : ∀ z, EV (σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [σ, hEV, hs1]
    | add a b ha hb => simp [map_add (f := _), ha, hb]
  have h2 : ∀ z, σ (EV z) = (r ⊗ₜ[ℚ] (1 : C)) * z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [σ, hEV, hs2]
    | add a b ha hb => simp only [map_add (f := _), ha, hb, mul_add]
  have h3 : EV (r ⊗ₜ[ℚ] (1 : C)) = 1 := by simp [hEV, hr, Algebra.TensorProduct.one_def]
  have key : ∀ z, Commute z (EV M) → (r ⊗ₜ[ℚ] (1 : C)) * (σ z * M - M * σ z) = 0 := by
    intro z hz
    rw [← h2, map_sub, map_mul, map_mul, h1, sub_eq_zero.2 hz.eq, map_zero]
  have := H _ _ (key x hx) (key y hy)
  have h4 := congrArg EV this
  rw [map_mul, h3, one_mul, map_sub, map_mul, map_mul, h1, h1, map_zero] at h4
  exact sub_eq_zero.1 h4

private theorem afp_ext {p : ℕ} {a b : AfP p} (h : ∀ v : AwayP p, AfP.eval v a = AfP.eval v b) : a = b :=
  RestrictedProduct.ext (fun v : AwayP p => v.1.adicCompletion ℚ) (fun v => (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) h

private def placeZ (q : ℕ) (hq : q.Prime) : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(q : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).2 (Nat.prime_iff_prime_int.1 hq)
  ne_bot := by simpa [Ideal.span_singleton_eq_bot] using hq.ne_zero

private def placeAway {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p) : AwayP p :=
  ⟨placeZ q hq, fun h => by
    have h1 : (q : ℤ) ∈ Ideal.span {(p : ℤ)} := by
      rw [← h]; exact Ideal.subset_span rfl
    rw [Ideal.mem_span_singleton] at h1
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).1 (by exact_mod_cast h1)).symm⟩

private theorem val_of_not_mem {R : Type} [CommRing R] [IsDedekindDomain R] [Algebra R ℚ] [IsFractionRing R ℚ]
    (v : HeightOneSpectrum R) (z : R) (h : z ∉ v.asIdeal) (f : ℚ →+* v.adicCompletion ℚ) :
    Valued.v (f (algebraMap R ℚ z)) = 1 := by
  obtain rfl : f = algebraMap ℚ (v.adicCompletion ℚ) := RingHom.ext_rat _ _
  have h1 := v.valuation_le_one (K := ℚ) z
  have h2 : ¬ v.valuation ℚ (algebraMap R ℚ z) < 1 := fun h' => h ((v.valuation_lt_one_iff_mem z).1 h')
  have h3 : v.valuation ℚ (algebraMap R ℚ z) = 1 := le_antisymm h1 (not_lt.1 h2)
  rw [← h3]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _

private theorem val_of_mem {R : Type} [CommRing R] [IsDedekindDomain R] [Algebra R ℚ] [IsFractionRing R ℚ]
    (v : HeightOneSpectrum R) (z : R) (h : z ∈ v.asIdeal) (f : ℚ →+* v.adicCompletion ℚ) :
    Valued.v (f (algebraMap R ℚ z)) < 1 := by
  obtain rfl : f = algebraMap ℚ (v.adicCompletion ℚ) := RingHom.ext_rat _ _
  have h3 := (v.valuation_lt_one_iff_mem (K := ℚ) z).2 h
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap R ℚ z)
  exact (this.trans_lt h3)

private theorem exists_place {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p) :
    ∃ v : Plc ℚ, (q : 𝓞 ℚ) ∈ v.asIdeal ∧ (p : 𝓞 ℚ) ∉ v.asIdeal := by
  have hq0 : (q : 𝓞 ℚ) ≠ 0 := by
    intro h
    have := congrArg Rat.ringOfIntegersEquiv h
    rw [map_natCast, map_zero] at this
    exact hq.ne_zero (by exact_mod_cast this)
  have hne : Ideal.span {(q : 𝓞 ℚ)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro h
    have := h.map Rat.ringOfIntegersEquiv
    rw [map_natCast, Int.ofNat_isUnit, Nat.isUnit_iff] at this
    exact hq.one_lt.ne' this
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have hqm : (q : 𝓞 ℚ) ∈ m := hle (Ideal.subset_span rfl)
  refine ⟨⟨m, hm.isPrime, fun hb => hq0 (by simpa [hb] using hqm)⟩, hqm, fun hpm => ?_⟩
  have hco : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hqp.symm)
  obtain ⟨a, b, hab⟩ := hco
  have h1 : ((a : 𝓞 ℚ) * (p : 𝓞 ℚ) + (b : 𝓞 ℚ) * (q : 𝓞 ℚ)) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 ℚ) hab
  have h2 : (1 : 𝓞 ℚ) ∈ m := h1 ▸ m.add_mem (m.mul_mem_left _ hpm) (m.mul_mem_left _ hqm)
  exact hm.ne_top ((Ideal.eq_top_iff_one _).2 h2)

private theorem rho_idem {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p) (T : AdQ p) (e : AfQ)
    (he : ∀ v : Plc ℚ, ((q : 𝓞 ℚ) ∈ v.asIdeal → e v = 1) ∧ ((q : 𝓞 ℚ) ∉ v.asIdeal → e v = 0)) :
    AfP.eval (placeAway hq Fact.out hqp) (T.ρ e) = 1 ∧
      ∀ v : AwayP p, v ≠ placeAway hq Fact.out hqp → AfP.eval v (T.ρ e) = 0 := by
  have hp : p.Prime := Fact.out
  have hee : e * e = e := by
    refine FiniteAdeleRing.ext ℚ fun v => ?_
    by_cases h : (q : 𝓞 ℚ) ∈ v.asIdeal
    · show e v * e v = e v
      rw [(he v).1 h, one_mul]
    · show e v * e v = e v
      rw [(he v).2 h, zero_mul]
  have hr : T.ρ e * T.ρ e = T.ρ e := by rw [← map_mul, hee]
  have h01 : ∀ v : AwayP p, AfP.eval v (T.ρ e) = 0 ∨ AfP.eval v (T.ρ e) = 1 := fun v => by
    have : AfP.eval v (T.ρ e) * AfP.eval v (T.ρ e) = AfP.eval v (T.ρ e) := by rw [← map_mul, hr]
    exact IsIdempotentElem.iff_eq_zero_or_one.1 this
  have hrat : ∀ c : ℚ, T.ρ (algebraMap ℚ AfQ c) = algebraMap ℚ (AfP p) c := fun c =>
    DFunLike.congr_fun (RingHom.ext_rat (T.ρ.comp (algebraMap ℚ AfQ)) (algebraMap ℚ (AfP p))) c
  have hev : ∀ (u : Plc ℚ) (c : ℚ), (algebraMap ℚ AfQ c) u = algebraMap ℚ (u.adicCompletion ℚ) c := fun u c =>
    DFunLike.congr_fun (RingHom.ext_rat
      ((RestrictedProduct.evalRingHom (fun v : Plc ℚ => v.adicCompletion ℚ) u).comp (algebraMap ℚ AfQ))
      (algebraMap ℚ (u.adicCompletion ℚ))) c
  have hA : ∀ v : AwayP p, v ≠ placeAway hq hp hqp → AfP.eval v (T.ρ e) = 0 := by
    intro v hv
    refine (h01 v).resolve_right fun h1 => ?_
    have hqv : (q : ℤ) ∉ v.1.asIdeal := by
      intro hmem
      apply hv
      apply Subtype.ext
      apply HeightOneSpectrum.ext
      have hmax : (placeZ q hq).asIdeal.IsMaximal := (placeZ q hq).isMaximal
      exact (hmax.eq_of_le v.1.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hmem)).symm
    obtain ⟨t, l, hl, htl⟩ := v.1.isMaximal.exists_inv hqv
    have hlq : ∀ u : Plc ℚ, (q : 𝓞 ℚ) ∈ u.asIdeal → (l : 𝓞 ℚ) ∉ u.asIdeal := by
      intro u hu hlu
      have h1 : ((t : 𝓞 ℚ) * (q : 𝓞 ℚ) + (l : 𝓞 ℚ)) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 ℚ) htl
      have h2 : (1 : 𝓞 ℚ) ∈ u.asIdeal := h1 ▸ u.asIdeal.add_mem (u.asIdeal.mul_mem_left _ hu) hlu
      exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
    let a : AfQ := algebraMap ℚ AfQ ((l : ℚ)⁻¹) * e
    have hint : IsIntAf (T.ρ a) := by
      refine (T.int a).2 fun u _ => ?_
      by_cases h : (q : 𝓞 ℚ) ∈ u.asIdeal
      · have h1 : a u = algebraMap ℚ (u.adicCompletion ℚ) ((l : ℚ)⁻¹) * e u := by
          rw [← hev]; rfl
        have h2 := val_of_not_mem u (l : 𝓞 ℚ) (hlq u h) (algebraMap ℚ (u.adicCompletion ℚ))
        have h3 : algebraMap (𝓞 ℚ) ℚ (l : 𝓞 ℚ) = (l : ℚ) := by simp
        rw [h3] at h2
        rw [h1, (he u).1 h, mul_one, map_inv₀, map_inv₀]
        exact ((congrArg Inv.inv h2).trans inv_one).le
      · have h1 : a u = algebraMap ℚ (u.adicCompletion ℚ) ((l : ℚ)⁻¹) * e u := by
          rw [← hev]; rfl
        rw [h1, (he u).2 h, mul_zero, map_zero]
        exact zero_le'
    have hv1 := hint v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv1
    have h2 : AfP.eval v (T.ρ a) = algebraMap ℚ (v.1.adicCompletion ℚ) ((l : ℚ)⁻¹) := by
      show AfP.eval v (T.ρ (algebraMap ℚ AfQ ((l : ℚ)⁻¹) * e)) = _
      rw [map_mul, map_mul, hrat, h1, mul_one, AlgHom.commutes]
    have h3 := val_of_mem v.1 l hl (algebraMap ℚ (v.1.adicCompletion ℚ))
    have h4 : algebraMap ℤ ℚ l = (l : ℚ) := by simp
    rw [h4] at h3
    have hl0 : (l : ℚ) ≠ 0 := by
      intro h0
      have hl0' : l = 0 := by exact_mod_cast h0
      obtain ⟨u, hu, -⟩ := exists_place hq hp hqp
      exact hlq u hu (by simp [hl0'])
    have h5 : Valued.v (algebraMap ℚ (v.1.adicCompletion ℚ) (l : ℚ)) ≠ 0 := by
      rw [Ne, map_eq_zero, map_eq_zero]; exact hl0
    have h6 := (one_lt_inv₀ (zero_lt_iff.2 h5)).2 h3
    have h7 : AfP.eval v (T.ρ a) ∈ v.1.adicCompletionIntegers ℚ := hint v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, h2, map_inv₀, map_inv₀] at h7
    exact absurd h7 (not_le.2 h6)
  refine ⟨(h01 _).resolve_left fun h0 => ?_, hA⟩
  have hz : T.ρ e = 0 := by
    refine afp_ext fun v => ?_
    by_cases hv : v = placeAway hq hp hqp
    · rw [hv, h0, map_zero]
    · rw [hA v hv, map_zero]
  obtain ⟨u, hu, hpu⟩ := exists_place hq hp hqp
  have := ((T.ker e).1 hz) u hpu
  rw [(he u).1 hu] at this
  exact one_ne_zero this


open Classical in
private def secAdd {p : ℕ} (v₀ : AwayP p) : v₀.1.adicCompletion ℚ →+ AfP p where
  toFun x := ⟨Pi.single v₀ x, by
    have : ({v₀}ᶜ : Set (AwayP p)) ∈ Filter.cofinite := by simp
    refine Filter.mem_of_superset this fun v hv => ?_
    have : v ≠ v₀ := hv
    simp only [Set.mem_setOf_eq, Pi.single_eq_of_ne this]
    exact zero_mem _⟩
  map_zero' := by
    refine afp_ext fun v => ?_
    show (Pi.single v₀ (0 : v₀.1.adicCompletion ℚ) : ∀ v : AwayP p, v.1.adicCompletion ℚ) v = 0
    simp
  map_add' x y := by
    refine afp_ext fun v => ?_
    show (Pi.single v₀ (x + y) : ∀ v : AwayP p, v.1.adicCompletion ℚ) v =
      (Pi.single v₀ x : ∀ v : AwayP p, v.1.adicCompletion ℚ) v + (Pi.single v₀ y : ∀ v : AwayP p, v.1.adicCompletion ℚ) v
    simp [Pi.single_add]

private theorem eval_secAdd {p : ℕ} (v₀ : AwayP p) (x) : AfP.eval v₀ (secAdd v₀ x) = x := by
  classical
  show (Pi.single v₀ x : ∀ v : AwayP p, v.1.adicCompletion ℚ) v₀ = x
  simp

private theorem secAdd_eval {p : ℕ} (v₀ : AwayP p) (r a : AfP p) (h1 : AfP.eval v₀ r = 1)
    (h0 : ∀ v, v ≠ v₀ → AfP.eval v r = 0) : secAdd v₀ (AfP.eval v₀ a) = r * a := by
  classical
  refine afp_ext fun v => ?_
  rw [map_mul]
  by_cases hv : v = v₀
  · subst hv
    rw [eval_secAdd, h1, one_mul]
  · rw [h0 v hv, zero_mul]
    show (Pi.single v₀ _ : ∀ v : AwayP p, v.1.adicCompletion ℚ) v = 0
    exact Pi.single_eq_of_ne hv _

private theorem core {E R : Type} [Field E] [NumberField E] [CommRing R] [Algebra ℚ R] {n p : ℕ}
    (Φ : Af E →+* R ⊗[ℚ] E) (Φ_surj : Function.Surjective Φ)
    (Φ_ker : ∀ x, Φ x = 0 ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → pLoc E w x = 0)
    (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) (mu : IsMu μ)
    (r : R) (c : Af E) (hc : Φ c = r ⊗ₜ[ℚ] (1 : E)) (Z : Matrix (Fin n) (Fin n) (Af E))
    (hZ : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal →
      pLoc E w c = 0 ∨ (pLoc E w c = 1 ∧ (Z.map (pLoc E w)).charpoly.Separable))
    (M : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) (hM : μ M = Z.map Φ) (x y : R ⊗[ℚ] Matrix (Fin n) (Fin n) E)
    (hx : (r ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E)) * (x * M - M * x) = 0)
    (hy : (r ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E)) * (y * M - M * y) = 0) :
    (r ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E)) * (x * y - y * x) = 0 := by
  classical
  have lift : ∀ u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E, ∃ U : Matrix (Fin n) (Fin n) (Af E), Φ.mapMatrix U = μ u := fun u =>
    ⟨Matrix.of fun i k => (Φ_surj (μ u i k)).choose, Matrix.ext fun i k => (Φ_surj (μ u i k)).choose_spec⟩
  obtain ⟨X, hX⟩ := lift x
  obtain ⟨Y, hY⟩ := lift y
  have hM' : μ M = Φ.mapMatrix Z := hM
  have hcc : μ (r ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E)) = Φ.mapMatrix (c • (1 : Matrix (Fin n) (Fin n) (Af E))) := by
    refine Matrix.ext fun i k => ?_
    rw [mu, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · simp [hc]
    · simp
  have hzero : ∀ W : Matrix (Fin n) (Fin n) (Af E), Φ.mapMatrix ((c • (1 : Matrix (Fin n) (Fin n) (Af E))) * W) = 0 ↔
      ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → pLoc E w c • (pLoc E w).mapMatrix W = 0 := by
    intro W
    constructor
    · intro h w hw
      refine Matrix.ext fun i k => ?_
      have h1 := congrFun (congrFun h i) k
      simp only [smul_mul_assoc, one_mul, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.zero_apply] at h1
      have h2 := (Φ_ker _).1 h1 w hw
      simpa [map_mul] using h2
    · intro h
      refine Matrix.ext fun i k => ?_
      simp only [smul_mul_assoc, one_mul, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.zero_apply]
      refine (Φ_ker _).2 fun w hw => ?_
      have h1 := congrFun (congrFun (h w hw) i) k
      simpa [map_mul] using h1
  have hd : ∀ (u v : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) (U V : Matrix (Fin n) (Fin n) (Af E)), Φ.mapMatrix U = μ u →
      Φ.mapMatrix V = μ v → μ ((r ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E)) * (u * v - v * u)) =
        Φ.mapMatrix ((c • (1 : Matrix (Fin n) (Fin n) (Af E))) * (U * V - V * U)) := by
    intro u v U V hU hV
    rw [map_mul, map_mul, map_sub, map_sub, map_mul, map_mul, map_mul, map_mul, hU, hV, hcc]
  have hloc : ∀ (u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) (U : Matrix (Fin n) (Fin n) (Af E)), Φ.mapMatrix U = μ u →
      (r ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E)) * (u * M - M * u) = 0 → ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal →
      pLoc E w c = 1 → (pLoc E w).mapMatrix Z * (pLoc E w).mapMatrix U = (pLoc E w).mapMatrix U * (pLoc E w).mapMatrix Z := by
    intro u U hU h w hw h1
    have h2 := hd u M U Z hU hM'.symm
    rw [h, map_zero] at h2
    have h3 := (hzero _).1 h2.symm w hw
    rw [h1, one_smul, map_sub, map_mul, map_mul] at h3
    exact (sub_eq_zero.1 h3).symm
  apply μ.injective
  rw [map_zero, hd x y X Y hX hY, hzero]
  intro w hw
  rcases hZ w hw with h0 | ⟨h1, hs⟩
  · rw [h0, zero_smul]
  · rw [h1, one_smul, map_sub, map_mul, map_mul]
    exact sub_eq_zero.2 (mat_comm hs (hloc x X hX hx w hw h1) (hloc y Y hY hy w hw h1))

theorem regTr : RegTr := by
  intro E _ _ _ A n p _ S T q hq hqp g hg
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨e, he, heE⟩ := UpperTheory.Gal.W2.Seed.pIdemP q E
  obtain ⟨h1, h0⟩ := rho_idem hq hqp T.toAdQ e he
  refine ⟨placeAway hq Fact.out hqp, fun x y hx hy => ?_⟩
  refine tensor_comm (AfP.eval (placeAway hq Fact.out hqp)) (T.ρ e)
    (secAdd (placeAway hq Fact.out hqp)).toRatLinearMap (eval_secAdd _)
    (fun a => secAdd_eval _ _ a h1 h0) h1 (S.mx (T.j g)) (fun x y hx hy => ?_) x y hx hy
  refine core T.Φ T.Φ_surj T.Φ_ker T.μ T.mu (T.ρ e) (finiteAdeleMap ℚ E e) (T.Φ_Q e)
    (T.a * mat g * T.a⁻¹).val (fun w hw => ?_) _ (T.j_mx g) x y hx hy
  by_cases hqw : (q : 𝓞 E) ∈ w.asIdeal
  · refine Or.inr ⟨(heE w).1 hqw, ?_⟩
    have h2 : ((T.a * mat g * T.a⁻¹).val).map (pLoc E w) =
        (GeneralLinearGroup.map (pLoc E w) T.a).val * (comp w g).val * ((GeneralLinearGroup.map (pLoc E w) T.a)⁻¹).val := by
      have : GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹) =
          GeneralLinearGroup.map (pLoc E w) T.a * comp w g * (GeneralLinearGroup.map (pLoc E w) T.a)⁻¹ := by
        rw [map_mul, map_mul, map_inv]; rfl
      exact congrArg Units.val this
    rw [h2, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact hg w hqw
  · exact Or.inl ((heE w).2 hqw)

end UpperTheory.Gal.Spc
end
end
end
