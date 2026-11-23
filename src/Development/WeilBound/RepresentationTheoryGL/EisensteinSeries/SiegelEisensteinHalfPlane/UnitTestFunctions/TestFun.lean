module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpProfileEqZeroOfLtHalf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousInfiniteIdeleInclusion
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOfChiNeZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasCompactSupportSmallF
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleOfFiniteEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteModuleOfFinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemOHOfMemIntAd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemStabOfInvCol
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdFunHasCompactSupport
public import GroundTheory.GlobalFields.TateThesis.EulerFactorsInfinite
public import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionGood
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ToIdeleMulSelf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValEqOneOfMulEq

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfForallInM

section

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Topology
open PositivityTheory.RgEis PositivityTheory.RgEis.TF

namespace GlobalTheory.CompanionTheory.RgEis.InMTopPf

variable {k : Type} [Field k] [NumberField k]

theorem natCast_isUnit (M : ℕ) (hM : M ≠ 0) : IsUnit (M : FiniteAdeleRing (𝓞 k) k) := by
  have : (M : FiniteAdeleRing (𝓞 k) k) = algebraMap k _ (M : k) := by simp
  rw [this]
  exact (IsUnit.mk0 _ (by exact_mod_cast hM)).map _

theorem inM_iff (M : ℕ) (hM : M ≠ 0) (x : FiniteAdeleRing (𝓞 k) k) :
    InM M x ↔ (((natCast_isUnit (k := k) M hM).unit⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) :
      FiniteAdeleRing (𝓞 k) k) * x ∈ OH k := by
  set u := (natCast_isUnit (k := k) M hM).unit
  have hu : (u : FiniteAdeleRing (𝓞 k) k) = M := rfl
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]

theorem isOpen_isClosed (M : ℕ) (hM : M ≠ 0) :
    IsOpen {x : FiniteAdeleRing (𝓞 k) k | InM M x} ∧ IsClosed {x : FiniteAdeleRing (𝓞 k) k | InM M x} := by
  have hS : {x : FiniteAdeleRing (𝓞 k) k | InM M x} =
      (fun x => (((natCast_isUnit (k := k) M hM).unit⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) :
        FiniteAdeleRing (𝓞 k) k) * x) ⁻¹' (OH k : Set (FiniteAdeleRing (𝓞 k) k)) := by
    ext x; exact inM_iff M hM x
  have hc : Continuous (fun x : FiniteAdeleRing (𝓞 k) k =>
      (((natCast_isUnit (k := k) M hM).unit⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) * x) :=
    continuous_const.mul continuous_id
  have ho : IsOpen (OH k : Set (FiniteAdeleRing (𝓞 k) k)) := GroundTheory.Global.isOpen_integralFiniteAdeles
  rw [hS]
  exact ⟨ho.preimage hc, (AddSubgroup.isClosed_of_isOpen (OH k).toAddSubgroup ho).preimage hc⟩

theorem exists_pow_lt' {c a : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hc : c < 1) : ∃ n : ℕ, c ^ n < a := by
  rcases eq_or_ne c 0 with rfl | hc0
  · exact ⟨1, by simpa using (zero_lt_iff.mpr ha)⟩
  obtain ⟨α, rfl⟩ := WithZero.ne_zero_iff_exists.mp hc0
  obtain ⟨β, rfl⟩ := WithZero.ne_zero_iff_exists.mp ha
  have hα : Multiplicative.toAdd α < 0 := by
    have h1 : ((α : WithZero (Multiplicative ℤ))) < ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      simpa using hc
    rw [WithZero.coe_lt_coe] at h1
    exact h1
  refine ⟨(Multiplicative.toAdd β).natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
  show Multiplicative.toAdd (α ^ ((Multiplicative.toAdd β).natAbs + 1)) < Multiplicative.toAdd β
  rw [toAdd_pow, nsmul_eq_mul]
  set a := Multiplicative.toAdd α
  set b := Multiplicative.toAdd β
  have ha1 : a ≤ -1 := by omega
  have h3 : (((b.natAbs + 1 : ℕ) : ℤ)) * a ≤ -(((b.natAbs + 1 : ℕ) : ℤ)) := by
    have : (0 : ℤ) ≤ ((b.natAbs + 1 : ℕ) : ℤ) := by positivity
    nlinarith
  push_cast at h3 ⊢
  have h4 := neg_abs_le b
  linarith

theorem natCast_apply' (v : HeightOneSpectrum (𝓞 k)) (M : ℕ) :
    (M : FiniteAdeleRing (𝓞 k) k) v = (M : v.adicCompletion k) := by
  rw [← map_natCast (algebraMap k (FiniteAdeleRing (𝓞 k) k)) M, FiniteAdeleRing.algebraMap_apply]
  exact map_natCast (algebraMap k (v.adicCompletion k)) M

theorem valued_natCast (v : HeightOneSpectrum (𝓞 k)) (n : ℕ) :
    Valued.v (n : v.adicCompletion k) = v.intValuation (n : 𝓞 k) := by
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := k) v (n : 𝓞 k)
  rw [HeightOneSpectrum.valuation_of_algebraMap] at this
  rw [← this]
  congr 1
  simp

theorem eq_zero_of_forall_inM (x : FiniteAdeleRing (𝓞 k) k) (hx : ∀ M : ℕ, M ≠ 0 → InM M x) : x = 0 := by
  refine Subtype.ext (funext fun v => ?_)
  change x v = 0
  by_contra hxv
  set N : ℕ := Ideal.absNorm v.asIdeal with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hNmem : (N : 𝓞 k) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have hlt : v.intValuation (N : 𝓞 k) < 1 := (v.intValuation_lt_one_iff_mem _).mpr hNmem
  have hxv0 : Valued.v (x v) ≠ 0 := by simpa using hxv
  obtain ⟨n, hn⟩ := exists_pow_lt' hxv0 hlt
  obtain ⟨y, hy, hxy⟩ := hx (N ^ n) (pow_ne_zero _ hN0)
  have hcomp : x v = ((N ^ n : ℕ) : v.adicCompletion k) * y v := by
    rw [hxy]
    have h1 := natCast_apply' v (N ^ n)
    change ((N ^ n : ℕ) : FiniteAdeleRing (𝓞 k) k) v * y v = _
    rw [h1]
  have hyv : Valued.v (y v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp (hy v)
  have hle : Valued.v (x v) ≤ v.intValuation (N : 𝓞 k) ^ n := by
    rw [hcomp, map_mul, valued_natCast, Nat.cast_pow, map_pow]
    exact mul_le_of_le_one_right' hyv
  exact absurd (lt_of_le_of_lt hle hn) (lt_irrefl _)

theorem inMTop : InMTop := fun k _ _ =>
  ⟨fun M hM => isOpen_isClosed M hM, fun x hx => eq_zero_of_forall_inM x hx⟩

end GlobalTheory.CompanionTheory.RgEis.InMTopPf
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatCastFiniteAdeleApply

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup PositivityTheory.RgEis PositivityTheory.RgEis.TF
open WithZero Multiplicative

namespace GlobalTheory.CompanionTheory.EisTF

variable {k : Type} [Field k] [NumberField k]

theorem natCast_finiteAdele_apply (v : HeightOneSpectrum (𝓞 k)) (M : ℕ) :
    ((M : FiniteAdeleRing (𝓞 k) k) v) = (M : v.adicCompletion k) := by
  induction M with
  | zero => simp only [Nat.cast_zero]; rfl
  | succ m ih =>
    simp only [Nat.cast_succ]
    change ((m : FiniteAdeleRing (𝓞 k) k) v) + (1 : FiniteAdeleRing (𝓞 k) k) v = _
    rw [ih]
    rfl

theorem valued_natCast_le_one (v : HeightOneSpectrum (𝓞 k)) (M : ℕ) :
    Valued.v (M : v.adicCompletion k) ≤ 1 := by
  have : (M : v.adicCompletion k) ∈ v.adicCompletionIntegers k := natCast_mem _ M
  exact this

theorem valued_absNorm_lt_one (v : HeightOneSpectrum (𝓞 k)) :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion k) < 1 := by
  have hv : ∀ x : k, Valued.v (algebraMap k (v.adicCompletion k) x) = v.valuation k x :=
    fun x => v.valuedAdicCompletion_eq_valuation' x
  have h : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 k) ∈ v.asIdeal := Ideal.absNorm_mem _
  have h2 := (v.valuation_lt_one_iff_mem (K := k) _).2 h
  have h3 : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion k) =
      algebraMap k (v.adicCompletion k) (algebraMap (𝓞 k) k ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 k)) := by
    simp
  rw [h3, hv]
  exact h2

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ exp (-1 : ℤ) := by
  by_cases hx : x = 0
  · simp [hx]
  · obtain ⟨a, rfl⟩ : ∃ a : ℤ, x = exp a := ⟨log x, (exp_log hx).symm⟩
    rw [← exp_zero, exp_lt_exp] at h
    rw [exp_le_exp]
    omega

theorem valued_absNorm_pow_le (v : HeightOneSpectrum (𝓞 k)) (n : ℕ) :
    Valued.v (((Ideal.absNorm v.asIdeal ^ n : ℕ)) : v.adicCompletion k) ≤ exp (-(n : ℤ)) := by
  have h1 := le_exp_neg_one_of_lt_one (valued_absNorm_lt_one v)
  rw [Nat.cast_pow, map_pow]
  refine (pow_le_pow_left₀ zero_le' h1 n).trans (le_of_eq ?_)
  rw [← exp_nsmul]
  congr 1
  simp

theorem valued_prod_le (S : Finset (HeightOneSpectrum (𝓞 k))) (n : HeightOneSpectrum (𝓞 k) → ℕ)
    {v : HeightOneSpectrum (𝓞 k)} (hv : v ∈ S) :
    Valued.v (((∏ w ∈ S, Ideal.absNorm w.asIdeal ^ n w : ℕ)) : v.adicCompletion k) ≤ exp (-(n v : ℤ)) := by
  classical
  rw [← Finset.mul_prod_erase S _ hv, Nat.cast_mul, map_mul]
  calc _ ≤ Valued.v (((Ideal.absNorm v.asIdeal ^ n v : ℕ)) : v.adicCompletion k) * 1 :=
        mul_le_mul_right (valued_natCast_le_one v _) _
    _ ≤ exp (-(n v : ℤ)) := by rw [mul_one]; exact valued_absNorm_pow_le v (n v)

theorem condM : CondM := by
  intro k _ _ ω
  let χ : (FiniteAdeleRing (𝓞 k) k)ˣ →* Circle := ω.toIdele.comp ofFinite
  have hχ : Continuous χ := ω.continuous_toIdele.comp continuous_ofFinite
  obtain ⟨S, n, -, h0, hker⟩ := exists_finiteLevel_le_ker_circle χ hχ
  refine ⟨∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n v, ?_, ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ ?_
    exact fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · rintro u hu ⟨y, hy, huy⟩
    have hmem : u ∈ finiteLevel n := by
      refine mem_finiteLevel.2 fun v => ?_
      have hz : finiteComponent v u ∈ unitsLevel (K := k) v 0 := by
        rw [unitsLevel_zero, Submonoid.mem_units_iff]
        exact (mem_finiteIntegralUnits k).1 hu v
      by_cases hv : v ∈ S
      · refine mem_unitsLevel.2 ⟨(mem_unitsLevel.1 hz).1, ?_⟩
        have hyv : Valued.v (y v) ≤ 1 := mem_integralFiniteAdeles.1 hy v
        have huv : ((u : FiniteAdeleRing (𝓞 k) k) v) - 1 =
            ((∏ w ∈ S, Ideal.absNorm w.asIdeal ^ n w : ℕ) : v.adicCompletion k) * y v := by
          have := congrArg (fun x : FiniteAdeleRing (𝓞 k) k => x v) huy
          rw [← natCast_finiteAdele_apply]
          exact this
        rw [coe_finiteComponent, huv, map_mul]
        calc _ ≤ Valued.v ((∏ w ∈ S, Ideal.absNorm w.asIdeal ^ n w : ℕ) : v.adicCompletion k) * 1 :=
              mul_le_mul_right hyv _
          _ ≤ _ := by rw [mul_one]; exact valued_prod_le S n hv
      · rw [h0 v hv]
        exact hz
    exact MonoidHom.mem_ker.1 (hker hmem)

end GlobalTheory.CompanionTheory.EisTF
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealComponentCoe

section

@[expose] public section

noncomputable section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GlobalTheory.CompanionTheory.RgEisSign

variable {k : Type} [Field k] [NumberField k]


open scoped Classical in
def even_im_hermitian_sub (ω : HeckeCharacter k) (w : {w : InfinitePlace k // w.IsReal}) : ℕ :=
  if ω.realComponent w.2 (-1) = 1 then 0 else 1

theorem realComponent_coe (ω : HeckeCharacter k) (h : IsOfFinOrder ω)
    (w : {w : InfinitePlace k // w.IsReal}) (x : ℝˣ) :
    (ω.realComponent w.2 x : ℂ) = if 0 < (x : ℝ) then (1 : ℂ) else (-1) ^ even_im_hermitian_sub ω w := by
  split_ifs with hx
  · rw [ω.realComponent_eq_one_of_isOfFinOrder h w.2 hx]; simp
  · have hneg : (x : ℝ) < 0 := lt_of_le_of_ne (not_lt.1 hx) x.ne_zero
    have hpos : 0 < ((-x : ℝˣ) : ℝ) := by simpa using hneg
    have hx' : x = (-1) * (-x) := by simp
    have hc : ω.realComponent w.2 (-1) * ω.realComponent w.2 (-1) = 1 := by
      rw [← map_mul]; simp
    rw [hx', map_mul, ω.realComponent_eq_one_of_isOfFinOrder h w.2 hpos, mul_one]
    unfold even_im_hermitian_sub
    split_ifs with h1
    · rw [h1]; simp
    · have h2 : ((ω.realComponent w.2 (-1) : Circle) : ℂ) * ((ω.realComponent w.2 (-1) : Circle) : ℂ) = 1 := by
        rw [← Circle.coe_mul, hc]; simp
      rcases mul_self_eq_one_iff.1 h2 with h3 | h3
      · exact absurd (Circle.ext (by simpa using h3)) h1
      · simpa using h3

theorem real_factor (ω : HeckeCharacter k) (h : IsOfFinOrder ω) (a : (InfiniteAdeleRing k)ˣ)
    (w : {w : InfinitePlace k // w.IsReal}) :
    (ω.infiniteComponent w.1 (infiniteComponent w.1 a) : ℂ) =
      if 0 < (homeomorphMixedSpace k (a : InfiniteAdeleRing k)).1 w then (1 : ℂ)
      else (-1) ^ even_im_hermitian_sub ω w := by
  have hs := realUnitsHom_surjective w.2 (infiniteComponent w.1 a)
  have hv : ((Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal w.2 : w.1.Completion →+* ℝ).toMonoidHom
      (infiniteComponent w.1 a) : ℝˣ) : ℝ) = (homeomorphMixedSpace k (a : InfiniteAdeleRing k)).1 w := rfl
  rw [← hs, ← hv]
  exact realComponent_coe ω h w _

theorem complex_factor (ω : HeckeCharacter k) (h : IsOfFinOrder ω) (a : (InfiniteAdeleRing k)ˣ)
    (w : {w : InfinitePlace k // w.IsComplex}) :
    (ω.infiniteComponent w.1 (infiniteComponent w.1 a) : ℂ) = 1 := by
  rw [← complexUnitsHom_surjective w.2 (infiniteComponent w.1 a)]
  have := ω.complexComponent_eq_one_of_isOfFinOrder h w.2
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2 : w.1.Completion →+* ℂ).toMonoidHom
      (infiniteComponent w.1 a))
  exact congrArg (fun c : Circle => (c : ℂ)) this |>.trans (by simp)

theorem signChar : PositivityTheory.RgEis.TF.SignChar := by
  intro k _ _ ω h
  have hf : IsOfFinOrder ω :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, by rw [pow_two]; exact h⟩
  refine ⟨even_im_hermitian_sub ω, fun a => ?_⟩
  rw [HeckeCharacter.toIdele_ofInfinite]
  have h1 : ((∏ w, ω.infiniteComponent w (infiniteComponent w a) : Circle) : ℂ) =
      ∏ w, (ω.infiniteComponent w (infiniteComponent w a) : ℂ) :=
    map_prod Circle.coeHom (fun w => ω.infiniteComponent w (infiniteComponent w a)) Finset.univ
  rw [h1, InfinitePlace.prod_eq_prod_mul_prod, Finset.prod_eq_one (fun w _ => complex_factor ω hf a w),
    mul_one]
  exact Finset.prod_congr rfl fun w _ => real_factor ω hf a w

end GlobalTheory.CompanionTheory.RgEisSign
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegrandTensor

section

@[expose] public section

noncomputable section

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.RgEisTF

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup

theorem zetaIntegrand_tensor {k : Type} [Field k] [NumberField k]
    (φ : 𝓢(Unit → mixedSpace k, ℂ)) (g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ)
    (ω : HeckeCharacter k) (s : ℂ) (x : IdeleGroup k) :
    GJMatrix.schwartzBruhatTensorPi φ g (fun _ => (x : 𝔸[k])) * (ω.toIdele x : ℂ) *
        ((ideleModule k x : ℝ) : ℂ) ^ s =
      (rd φ (fun _ => ((toInfinite k x : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k)) *
          (ω.toIdele (ofInfinite (toInfinite k x)) : ℂ) *
          ((ideleModule k (ofInfinite (toInfinite k x)) : ℝ) : ℂ) ^ s) *
        (g (fun _ => ((toFinite k x : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k)) *
          (ω.toIdele (ofFinite (toFinite k x)) : ℂ) *
          ((ideleModule k (ofFinite (toFinite k x)) : ℝ) : ℂ) ^ s) := by
  have hchi : (ω.toIdele x : ℂ) = (ω.toIdele (ofFinite (toFinite k x)) : ℂ) *
      (ω.toIdele (ofInfinite (toInfinite k x)) : ℂ) := by
    rw [← Circle.coe_mul, ← map_mul, ofFinite_mul_ofInfinite]
  have hmod : ((ideleModule k x : ℝ) : ℂ) ^ s =
      ((ideleModule k (ofInfinite (toInfinite k x)) : ℝ) : ℂ) ^ s *
        ((ideleModule k (ofFinite (toFinite k x)) : ℝ) : ℂ) ^ s := by
    have h : (ideleModule k x : ℝ) = (ideleModule k (ofInfinite (toInfinite k x)) : ℝ) *
        (ideleModule k (ofFinite (toFinite k x)) : ℝ) := by
      conv_lhs => rw [← ofFinite_mul_ofInfinite x, map_mul]
      rw [mul_comm]
      rfl
    rw [h, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (ideleModule k _).2.le
      (ideleModule k _).2.le]
  rw [hchi, hmod]
  change φ (fun _ => homeomorphMixedSpace k (x : 𝔸[k]).1) * g (fun _ => (x : 𝔸[k]).2) * _ * _ = _
  change _ = (φ (fun _ => homeomorphMixedSpace k (x : 𝔸[k]).1) * _ * _) *
    (g (fun _ => (x : 𝔸[k]).2) * _ * _)
  ring

theorem zSplit : ZSplit := by
  intro k _ _ φ g ω s _
  set A : (InfiniteAdeleRing k)ˣ → ℂ := fun a =>
    rd φ (fun _ => (a : InfiniteAdeleRing k)) * (ω.toIdele (ofInfinite a) : ℂ) *
      ((ideleModule k (ofInfinite a) : ℝ) : ℂ) ^ s with hA
  set B : (FiniteAdeleRing (𝓞 k) k)ˣ → ℂ := fun b =>
    g (fun _ => (b : FiniteAdeleRing (𝓞 k) k)) * (ω.toIdele (ofFinite b) : ℂ) *
      ((ideleModule k (ofFinite b) : ℝ) : ℂ) ^ s with hB
  have hF : ∀ x : IdeleGroup k,
      GJMatrix.schwartzBruhatTensorPi φ g (fun _ => (x : 𝔸[k])) * (ω.toIdele x : ℂ) *
        ((ideleModule k x : ℝ) : ℂ) ^ s = (fun p => A p.1 * B p.2) (IdeleGroup.prodEquiv k x) :=
    zetaIntegrand_tensor φ g ω s
  have hemb : MeasurableEmbedding (IdeleGroup.prodEquiv k) :=
    (IdeleGroup.prodEquiv k).toHomeomorph.measurableEmbedding
  unfold globalZeta zInf zFin
  simp_rw [hF]
  rw [(measurePreserving_prodEquiv (K := k)).integral_comp hemb (fun p => A p.1 * B p.2)]
  exact integral_prod_mul A B

end GlobalTheory.CompanionTheory.RgEisTF
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.TestFun

section

@[expose] public section

theorem PositivityTheory.RgEis.TF.testFun : PositivityTheory.RgEis.TestFun :=
  GlobalTheory.CompanionTheory.RgEisAsm.asm GlobalTheory.CompanionTheory.EisCol.colLaw GlobalTheory.CompanionTheory.RgEis.InMTopPf.inMTop (GlobalTheory.CompanionTheory.RgEisSupp.supp GlobalTheory.CompanionTheory.EisCol.colLaw GlobalTheory.CompanionTheory.RgEis.InMTopPf.inMTop) (GlobalTheory.CompanionTheory.EisTF.archFun_of_bumps GlobalTheory.CompanionTheory.TestFun.realBump GlobalTheory.CompanionTheory.TestBump.cplxBump GlobalTheory.CompanionTheory.RgEisSign.signChar)
    (GlobalTheory.CompanionTheory.RgEisFin.finFun GlobalTheory.CompanionTheory.EisTF.condM GlobalTheory.CompanionTheory.EisTF.liftUnit GlobalTheory.CompanionTheory.RgEis.InMTopPf.inMTop) GlobalTheory.CompanionTheory.RgEisTF.zSplit GlobalTheory.CompanionTheory.EisTestFun.zInf_ne_zero GlobalTheory.CompanionTheory.EisTestFun.zFinPos GlobalTheory.CompanionTheory.EisTF.zFinLim GlobalTheory.CompanionTheory.StdGoodAd.stdGood
end
end
