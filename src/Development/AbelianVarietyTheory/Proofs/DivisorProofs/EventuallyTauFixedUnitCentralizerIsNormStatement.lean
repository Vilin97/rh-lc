module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeFixedCentraliserAlg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralOfIntegralCoordsLocalTensorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSqSubMulSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfNilpotentCommuteSeparableMinpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsConjOfMinpolyEqOfSeparable
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingUnitsIntegralCofinite

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocNormTau

variable {p : ℕ} [Fact p.Prime]

def tauR (G : HTGroup p) (β : G.Cˣ) (R : Type) [CommRing R] [Algebra ℚ R] (x : R ⊗[ℚ] G.C) : R ⊗[ℚ] G.C :=
  inC G R (β : G.C) * (starT G.star R x).unop * inC G R ((β⁻¹ : G.Cˣ) : G.C)

variable (G : HTGroup p) (β : G.Cˣ) (R : Type) [CommRing R] [Algebra ℚ R]

theorem tauR_add (x y : R ⊗[ℚ] G.C) : tauR G β R (x + y) = tauR G β R x + tauR G β R y := by
  simp only [tauR, map_add (f := _), MulOpposite.unop_add, mul_add, add_mul]

theorem inC_inv_mul : inC G R ((β⁻¹ : G.Cˣ) : G.C) * inC G R (β : G.C) = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

theorem tauR_mul (x y : R ⊗[ℚ] G.C) : tauR G β R (x * y) = tauR G β R y * tauR G β R x := by
  have h := inC_inv_mul G β R
  simp only [tauR, map_mul, MulOpposite.unop_mul, mul_assoc]
  congr 2
  rw [← mul_assoc (inC G R ((β⁻¹ : G.Cˣ) : G.C)), h, one_mul]

theorem tauR_one : tauR G β R 1 = 1 := by
  simp only [tauR, map_one, MulOpposite.unop_one, mul_one]
  rw [← map_mul, Units.mul_inv, map_one]

theorem sh_mul (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem tauR_inC (c : G.C) :
    tauR G β R (inC G R c) = inC G R ((β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C)) := by
  have h : (starT G.star R (inC G R c)).unop = inC G R (sh G c) := by
    change (starT G.star R ((1 : R) ⊗ₜ c)).unop = (1 : R) ⊗ₜ (G.star c).unop
    exact starT_tmul G.star R 1 c
  simp only [tauR, h, map_mul]

theorem commute_inC_of_forall (e : G.C) (he : ∀ c : G.C, Commute e c) (x : R ⊗[ℚ] G.C) :
    Commute (inC G R e) x := by
  induction x using TensorProduct.induction_on with
  | zero => exact Commute.zero_right _
  | tmul r c =>
    change (1 : R) ⊗ₜ e * r ⊗ₜ c = r ⊗ₜ c * (1 : R) ⊗ₜ e
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, (he c).eq]
  | add x y hx hy => exact hx.add_right hy

end GlobalTheory.LocNormTau

namespace GlobalTheory.LocNormTau

variable {p : ℕ} [Fact p.Prime]

theorem exists_conj_neg (G : HTGroup p) : ∃ f : G.F, f ≠ 0 ∧ IsCMField.complexConj G.F f = -f := by
  have hne := IsCMField.complexConj_ne_one G.F
  obtain ⟨x, hx⟩ : ∃ x, IsCMField.complexConj G.F x ≠ x := by
    by_contra h
    push_neg at h
    exact hne (AlgEquiv.ext h)
  refine ⟨x - IsCMField.complexConj G.F x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
  simp [IsCMField.complexConj_apply_apply]

theorem norm_aux {A : Type*} [Ring A] (a b E : A) (ha : Commute E a) (hb : Commute E b) (hab : a * b = b * a) :
    (a + b * E) * (a - E * b) = a * a - E * E * (b * b) ∧ (a - E * b) * (a + b * E) = a * a - E * E * (b * b) := by
  have h1 : a * (E * b) = a * b * E := by rw [hb.eq, mul_assoc]
  have h2 : b * E * a = a * b * E := by rw [mul_assoc, ha.eq, ← mul_assoc, hab]
  have h3 : b * E * (E * b) = E * E * (b * b) := by
    calc b * E * (E * b) = b * (E * E) * b := by noncomm_ring
      _ = E * E * (b * b) := by rw [← (hb.mul_left hb).eq, mul_assoc]
  have h4 : E * b * a = a * b * E := by rw [mul_assoc, ← hab, (ha.mul_right hb).eq]
  have h5 : E * b * (b * E) = E * E * (b * b) := by
    calc E * b * (b * E) = E * ((b * b) * E) := by noncomm_ring
      _ = E * E * (b * b) := by rw [← (hb.mul_right hb).eq, mul_assoc]
  constructor
  · rw [show (a + b * E) * (a - E * b) = a * a - a * (E * b) + b * E * a - b * E * (E * b) by noncomm_ring,
      h1, h2, h3]
    abel
  · rw [show (a - E * b) * (a + b * E) = a * a + a * b * E - E * b * a - E * b * (b * E) by noncomm_ring,
      h4, h5]
    abel

end GlobalTheory.LocNormTau
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralCoordsScalarTensorInclusion

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.FinClsLoc
open IsDedekindDomain

theorem ratAdicInt_eventually (q : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ := by
  have h := (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  filter_upwards [h] with v hv
  exact hv

theorem intC_inC_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C), ∀ᶠ w : AwayP p in Filter.cofinite,
    IntC G w (inC G (w.1.adicCompletion ℚ) c) := by
  intro p _ G c
  have hall : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ i : Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (v.adicCompletion ℚ) ((Module.finBasis ℚ G.C).repr c i) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i => ratAdicInt_eventually _
  have ht : Filter.Tendsto (Subtype.val : AwayP p → HeightOneSpectrum ℤ) Filter.cofinite Filter.cofinite :=
    Subtype.val_injective.tendsto_cofinite
  filter_upwards [ht.eventually hall] with w hw
  intro i
  have : coordL G w (inC G (w.1.adicCompletion ℚ) c) i =
      algebraMap ℚ (w.1.adicCompletion ℚ) ((Module.finBasis ℚ G.C).repr c i) := by
    have e : inC G (w.1.adicCompletion ℚ) c = (1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] c := rfl
    rw [coordL, e, Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  rw [this]; exact hw i

end GlobalTheory.FinClsLoc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralCoordsScalarTensorInclusionStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eventually_integralCoords_scalarTensorInclusion : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C), ∀ᶠ w : AwayP p in Filter.cofinite,
    IntC G w (inC G (w.1.adicCompletion ℚ) c) := by
  first | (exact @GlobalTheory.FinClsLoc.intC_inC_eventually) | (exact GlobalTheory.FinClsLoc.intC_inC_eventually) | (intros; apply GlobalTheory.FinClsLoc.intC_inC_eventually  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedAlgebraExists

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FixedCentraliserReg

theorem fixed_algebra_exists : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β Y : G.Cˣ),
    (minpoly G.F (Y : G.C)).Separable → (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∃ (L : Type) (_ : CommRing L) (_ : IsReduced L) (_ : Algebra ℚ L) (_ : FiniteDimensional ℚ L) (ι : L →ₐ[ℚ] G.C), Function.Injective ι ∧
      ∀ c : G.C, c ∈ Set.range ι ↔ Commute c (Y : G.C) ∧ (β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C) = c := by
  intro p _ G β Y hsep hdeg
  have hcomm : ∀ a b : G.C, Commute a (Y : G.C) → Commute b (Y : G.C) → Commute a b :=
    fun a b ha hb => GlobalTheory.LKCx.ClsReg.commute_of_commute_of_separable G (Y : G.C) hsep hdeg a b ha hb
  have hshmul : ∀ x y : G.C, sh G (x * y) = sh G y * sh G x := by
    intro x y; simp only [sh, map_mul, MulOpposite.unop_mul]
  have hshadd : ∀ x y : G.C, sh G (x + y) = sh G x + sh G y := by
    intro x y; simp only [sh, map_add (f := _), MulOpposite.unop_add]
  have hshalg : ∀ q : ℚ, sh G (algebraMap ℚ G.C q) = algebraMap ℚ G.C q := by
    intro q
    have h := RingHom.congr_fun (RingHom.ext_rat (G.star.comp (algebraMap ℚ G.C)) (algebraMap ℚ G.Cᵐᵒᵖ)) q
    simp only [RingHom.comp_apply, MulOpposite.algebraMap_apply] at h
    simp only [sh, h, MulOpposite.unop_op]
  have hββ : ((β⁻¹ : G.Cˣ) : G.C) * (β : G.C) = 1 := by simp
  let S : Subalgebra ℚ G.C :=
    { carrier := {c | Commute c (Y : G.C) ∧ (β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C) = c}
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨ha1.mul_left hb1, ?_⟩
        calc (β : G.C) * sh G (a * b) * ((β⁻¹ : G.Cˣ) : G.C)
            = ((β : G.C) * sh G b * ((β⁻¹ : G.Cˣ) : G.C)) * ((β : G.C) * sh G a * ((β⁻¹ : G.Cˣ) : G.C)) := by
              rw [hshmul]
              simp only [mul_assoc]
              rw [← mul_assoc ((β⁻¹ : G.Cˣ) : G.C) (β : G.C), hββ, one_mul]
          _ = b * a := by rw [ha2, hb2]
          _ = a * b := (hcomm a b ha1 hb1).eq.symm
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨ha1.add_left hb1, ?_⟩
        rw [hshadd, mul_add, add_mul, ha2, hb2]
      algebraMap_mem' := by
        intro q
        refine ⟨Algebra.commutes q _, ?_⟩
        rw [hshalg, ← Algebra.commutes q (β : G.C), mul_assoc, Units.mul_inv, mul_one] }
  letI cr : CommRing S :=
    { (inferInstance : Ring S) with
      mul_comm := fun a b => Subtype.ext (hcomm a b a.2.1 b.2.1).eq }
  have hred : IsReduced S := by
    refine ⟨fun x ⟨k, hk⟩ => Subtype.ext ?_⟩
    have hk' : (x : G.C) ^ k = 0 := by
      have := congrArg Subtype.val hk
      simpa using this
    exact GlobalTheory.LKCx.ClsReg.eq_zero_of_commute_of_pow_eq_zero p G (Y : G.C) hsep hdeg x x.2.1 k hk'
  haveI := G.towerC
  haveI := G.finC
  haveI : FiniteDimensional ℚ G.C := Module.Finite.trans G.F G.C
  have hfd : FiniteDimensional ℚ S :=
    Module.Finite.of_injective (S.val.toLinearMap) Subtype.val_injective
  refine ⟨S, cr, hred, S.algebra, hfd, S.val, Subtype.val_injective, fun c => ?_⟩
  constructor
  · rintro ⟨x, rfl⟩; exact x.2
  · intro h; exact ⟨⟨c, h⟩, rfl⟩

end GlobalTheory.FixedCentraliserReg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTauFixedUnitCentralizerIsNorm

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical


open GlobalTheory.LocNormTau in
theorem GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G (β : G.C) = β →
    ∀ (Y : G.Cˣ) (s : ℚ), (Y : G.C) * β * sh G (Y : G.C) = algebraMap ℚ G.C s * β →
    (minpoly G.F (Y : G.C)).Separable → (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) →
      IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) → IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) →
      inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) = m →
      ∃ v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = v * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G β hβ Y s hY hsep hdeg
  obtain ⟨f, hf0, hfc⟩ := exists_conj_neg G
  set e : G.C := algebraMap G.F G.C f with he_def
  set e' : G.C := algebraMap G.F G.C f⁻¹ with he'_def
  have hecomm : ∀ c : G.C, Commute e c := fun c => Algebra.commutes f c
  have he'comm : ∀ c : G.C, Commute e' c := fun c => Algebra.commutes f⁻¹ c
  have hee' : e * e' = 1 := by rw [he_def, he'_def, ← map_mul, mul_inv_cancel₀ hf0, map_one]
  have hsh_e : sh G e = -e := by
    simp only [sh, he_def, G.star_F, hfc, map_neg]
  have hsh_e' : sh G e' = -e' := by
    simp only [sh, he'_def, G.star_F, map_inv₀, hfc, inv_neg, map_neg]
  have hτe : (β : G.C) * sh G e * ((β⁻¹ : G.Cˣ) : G.C) = -e := by
    rw [hsh_e, mul_neg, neg_mul, (hecomm _).symm.eq, mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨L, _, _, _, _, ι, hιinj, hιrange⟩ := GlobalTheory.FixedCentraliserReg.fixed_algebra_exists p G β Y hsep hdeg
  have hee : e * e ∈ Set.range ι := by
    refine (hιrange _).2 ⟨(hecomm _).mul_left (hecomm _), ?_⟩
    rw [sh_mul, hsh_e, neg_mul_neg, ← ((hecomm (β : G.C)).mul_left (hecomm _)).eq, mul_assoc, Units.mul_inv,
      mul_one]
  have hee'' : e' * e' ∈ Set.range ι := by
    refine (hιrange _).2 ⟨(he'comm _).mul_left (he'comm _), ?_⟩
    rw [sh_mul, hsh_e', neg_mul_neg, ← ((he'comm (β : G.C)).mul_left (he'comm _)).eq, mul_assoc, Units.mul_inv,
      mul_one]
  obtain ⟨d, hd⟩ := hee
  obtain ⟨di, hdi⟩ := hee''
  have hddi : d * di = 1 := hιinj (by
    rw [map_mul, hd, hdi, map_one, mul_assoc, ← mul_assoc e e', hee', one_mul, hee'])
  have hne2 : ∀ᶠ w : AwayP p in Filter.cofinite, w.1.asIdeal ≠ Ideal.span {2} := by
    rw [Filter.eventually_cofinite]
    refine Set.Subsingleton.finite ?_
    intro w₁ h₁ w₂ h₂
    simp only [Set.mem_setOf_eq, not_not] at h₁ h₂
    exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext (h₁.trans h₂.symm))
  filter_upwards [hne2, GlobalTheory.T.eventually_isIntegral_of_integralCoordsLocalTensor p G, GlobalTheory.T.eventually_integralCoords_scalarTensorInclusion p G (ι d), GlobalTheory.T.eventually_integralCoords_scalarTensorInclusion p G (ι di)] with w h2 hint hId hId'
  intro m hmY hmI hmI' hmτ
  set K := w.1.adicCompletion ℚ
  obtain ⟨hΦinj, hΦrange⟩ := GlobalTheory.FinClsLoc.baseChange_fixedCentraliser_alg p G β Y L ι hιinj hιrange K
  set Φ := Algebra.TensorProduct.map (AlgHom.id K K) ι with hΦ
  have hmτ' : tauR G β K (m : K ⊗[ℚ] G.C) = m := hmτ
  have hm'τ : tauR G β K ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) = ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) := by
    have h1 : tauR G β K ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) * (m : K ⊗[ℚ] G.C) = 1 := by
      rw [← hmτ', ← tauR_mul, Units.mul_inv, tauR_one]
    calc _ = tauR G β K ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) * ((m : K ⊗[ℚ] G.C) * ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C)) := by
          rw [Units.mul_inv, mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  obtain ⟨y, hy⟩ := (hΦrange m).2 ⟨hmY, hmτ⟩
  obtain ⟨y', hy'⟩ := (hΦrange ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C)).2 ⟨hmY.units_inv_left, hm'τ⟩
  have hyy' : y * y' = 1 := hΦinj (by rw [map_mul, hy, hy', Units.mul_inv, map_one])
  set dK : K ⊗[ℚ] L := (1 : K) ⊗ₜ d
  set dK' : K ⊗[ℚ] L := (1 : K) ⊗ₜ di
  have hdd' : dK * dK' = 1 := by
    simp only [dK, dK', Algebra.TensorProduct.tmul_mul_tmul, one_mul, hddi]
    rfl
  have hΦd : Φ dK = inC G K (ι d) := by
    simp only [hΦ, dK, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  have hΦd' : Φ dK' = inC G K (ι di) := by
    simp only [hΦ, dK', Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  have pull : ∀ z : K ⊗[ℚ] L, IntC G w (Φ z) →
      ∃ g : Polynomial K, g.Monic ∧ (∀ i, g.coeff i ∈ w.1.adicCompletionIntegers ℚ) ∧ Polynomial.aeval z g = 0 := by
    intro z hz
    obtain ⟨g, hg1, hg2, hg3⟩ := hint _ hz
    refine ⟨g, hg1, hg2, hΦinj ?_⟩
    rw [← Polynomial.aeval_algHom_apply, hg3, map_zero]
  obtain ⟨a', b', hab⟩ := GlobalTheory.OddLocalNormEtale.exists_eq_sq_sub_mul_sq L w.1 h2 y y' dK dK' hyy' hdd'
    (pull y (by rw [hy]; exact hmI)) (pull y' (by rw [hy']; exact hmI'))
    (pull dK (by rw [hΦd]; exact hId)) (pull dK' (by rw [hΦd']; exact hId'))
  set a := Φ a'
  set b := Φ b'
  set E := inC G K e
  have haY := ((hΦrange a).1 ⟨a', rfl⟩).1
  have haτ : tauR G β K a = a := ((hΦrange a).1 ⟨a', rfl⟩).2
  have hbY := ((hΦrange b).1 ⟨b', rfl⟩).1
  have hbτ : tauR G β K b = b := ((hΦrange b).1 ⟨b', rfl⟩).2
  have hE : ∀ x : K ⊗[ℚ] G.C, Commute E x := commute_inC_of_forall G K e hecomm
  have hτE : tauR G β K E = -E := by
    rw [tauR_inC, hτe, map_neg]
  have habc : a * b = b * a := by
    simp only [a, b, ← map_mul, mul_comm a' b']
  have hEE : Φ dK = E * E := by rw [hΦd, hd, map_mul]
  have hm : (m : K ⊗[ℚ] G.C) = a * a - E * E * (b * b) := by
    rw [← hy, hab, map_sub, map_mul, map_mul, map_mul, hEE]
  set vv : K ⊗[ℚ] G.C := a + b * E
  have hτv : tauR G β K vv = a - E * b := by
    rw [tauR_add, tauR_mul, haτ, hbτ, hτE, neg_mul, sub_eq_add_neg]
  obtain ⟨key1, key2⟩ := norm_aux a b E (hE a) (hE b) habc
  rw [← hm] at key1 key2
  have hmv : Commute (m : K ⊗[ℚ] G.C) vv := by
    show (m : K ⊗[ℚ] G.C) * vv = vv * m
    calc (m : K ⊗[ℚ] G.C) * vv = vv * (a - E * b) * vv := by rw [key1]
      _ = vv * m := by rw [mul_assoc, key2]
  refine ⟨⟨vv, (a - E * b) * ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C), ?_, ?_⟩, ?_, ?_⟩
  · rw [← mul_assoc, key1, Units.mul_inv]
  · rw [mul_assoc, hmv.units_inv_left.eq, ← mul_assoc, key2, Units.mul_inv]
  · exact haY.add_left (hbY.mul_left (hE _))
  · change (m : K ⊗[ℚ] G.C) = vv * tauR G β K vv
    rw [hτv, key1]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTauFixedUnitCentralizerIsNormStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eventually_tauFixed_unit_centralizer_is_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G (β : G.C) = β →
    ∀ (Y : G.Cˣ) (s : ℚ), (Y : G.C) * β * sh G (Y : G.C) = algebraMap ℚ G.C s * β →
    (minpoly G.F (Y : G.C)).Separable → (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) →
      IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) → IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) →
      inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) = m →
      ∃ v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = v * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
  first | (exact @GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep) | (exact GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep) | (intros; apply GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep  <;> assumption)
end
end
