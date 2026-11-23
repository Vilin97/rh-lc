module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousExtensionAdicCompletion
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsHomOfBasis
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocG
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular
import ReciprocityTheory.Automorphisms.PlaceA

-- Source module: ReciprocityTheory.ReductiveGroups.LatticeEmbeddings.IotaPlace

section

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain

namespace ReciprocityTheory.ChartRestriction.B3.IotaPl

theorem norm_le_one_of_isIntegral_int {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨f, hf, hfx⟩ := hx
  set n := f.natDegree with hn
  have hsum := hf.as_sum
  rw [hsum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at hfx
  have key : x ^ n = -∑ i ∈ Finset.range n,
      Polynomial.eval₂ (algebraMap ℤ ℂ_[p]) x (Polynomial.C (f.coeff i) * Polynomial.X ^ i) := by
    rw [eq_neg_iff_add_eq_zero]
    exact hfx
  have hx1 : 1 ≤ ‖x‖ := hlt.le
  have bound : ‖∑ i ∈ Finset.range n,
      Polynomial.eval₂ (algebraMap ℤ ℂ_[p]) x (Polynomial.C (f.coeff i) * Polynomial.X ^ i)‖ ≤
        ‖x‖ ^ (n - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow]
    have hc : ‖(algebraMap ℤ ℂ_[p]) (f.coeff i)‖ ≤ 1 := by
      have h := IsUltrametricDist.norm_intCast_le_one ℂ_[p] (f.coeff i)
      first
        | (simpa using h)
        | (rw [algebraMap_int_eq, eq_intCast]; exact h)
        | (convert h using 2; exact (algebraMap ℤ ℂ_[p]).eq_intCast _)
    have hi' : i ≤ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖(algebraMap ℤ ℂ_[p]) (f.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (n - 1) :=
          mul_le_mul hc (pow_le_pow_right₀ hx1 hi') (by positivity) zero_le_one
      _ = ‖x‖ ^ (n - 1) := one_mul _
  have h2 : ‖x‖ ^ n ≤ ‖x‖ ^ (n - 1) := by
    rw [← norm_pow, key, norm_neg]
    exact bound
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0] at key
    simp at key
  · have h3 : ‖x‖ ^ (n - 1) < ‖x‖ ^ n := pow_lt_pow_right₀ hlt (by omega)
    linarith

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

theorem norm_int_le (ι : K →+* ℂ_[p]) (y : 𝓞 K) : ‖ι (y : K)‖ ≤ 1 := by
  obtain ⟨f, hf, hfy⟩ := NumberField.RingOfIntegers.isIntegral_coe y
  refine norm_le_one_of_isIntegral_int ⟨f, hf, ?_⟩
  have e : (algebraMap ℤ ℂ_[p]) = ι.comp (algebraMap ℤ K) := RingHom.ext_int _ _
  rw [e, ← Polynomial.hom_eval₂, hfy, map_zero]

def smallIdeal (ι : K →+* ℂ_[p]) : Ideal (𝓞 K) where
  carrier := {y | ‖ι (y : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have : ι ((a + b : 𝓞 K) : K) = ι (a : K) + ι (b : K) := by simp
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have : ι ((c • a : 𝓞 K) : K) = ι (c : K) * ι (a : K) := by simp
    rw [this, norm_mul]
    have h1 := norm_int_le ι c
    nlinarith [norm_nonneg (ι (c : K)), norm_nonneg (ι (a : K))]

theorem mem_smallIdeal (ι : K →+* ℂ_[p]) (y : 𝓞 K) : y ∈ smallIdeal ι ↔ ‖ι (y : K)‖ < 1 := Iff.rfl

theorem smallIdeal_isPrime (ι : K →+* ℂ_[p]) : (smallIdeal ι).IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (1 : 𝓞 K) ∈ smallIdeal ι := (Ideal.eq_top_iff_one _).mp h
    rw [mem_smallIdeal] at h1
    simp at h1
  · intro a b hab
    simp only [mem_smallIdeal] at hab ⊢
    have e : ι ((a * b : 𝓞 K) : K) = ι (a : K) * ι (b : K) := by simp
    rw [e, norm_mul] at hab
    by_contra hc
    push_neg at hc
    obtain ⟨ha, hb⟩ := hc
    nlinarith [norm_int_le ι a, norm_int_le ι b]

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have e : (p : ℂ_[p]) = (((algebraMap ℚ_[p] (PadicAlgCl p)) (p : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) := by
    first
      | simp
      | (rw [map_natCast]; exact (map_natCast UniformSpace.Completion.coeRingHom p).symm)
  rw [e, PadicComplex.norm_extends, PadicAlgCl.norm_extends]
  first
    | exact Padic.norm_p_lt_one
    | (rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))
    | (rw [padicNormE.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))

end ReciprocityTheory.ChartRestriction.B3.IotaPl

namespace ReciprocityTheory.ChartRestriction.B3

end ReciprocityTheory.ChartRestriction.B3
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleEmbeddingExtension

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.EvExtend

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]

theorem norm_natCast_lt_one : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h := PadicComplex.norm_extends l ((l : ℕ) : PadicAlgCl l)
  rw [← h]
  simpa using ReciprocityTheory.ChartRestriction.B3.IotaPl.norm_p_lt_one (p := l)

omit [NumberField F] in
theorem norm_int_le_one (φ : F →+* PadicAlgCl l) (y : 𝓞 F) : ‖φ (y : F)‖ ≤ 1 := by
  have hi : IsIntegral ℤ (φ (y : F)) := (RingOfIntegers.isIntegral_coe y).map φ.toIntAlgHom
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).isIntegral_iff_v_le_one.mp
    hi.tower_top
  exact_mod_cast (show ‖φ (y : F)‖₊ ≤ 1 from h2)

def placeOf (φ : F →+* PadicAlgCl l) : HeightOneSpectrum (𝓞 F) where
  asIdeal := ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal ((algebraMap (PadicAlgCl l) ℂ_[l]).comp φ)
  isPrime := ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal_isPrime _
  ne_bot := by
    intro h
    have hm : ((l : ℕ) : 𝓞 F) ∈ ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal ((algebraMap (PadicAlgCl l) ℂ_[l]).comp φ) := by
      rw [ReciprocityTheory.ChartRestriction.B3.IotaPl.mem_smallIdeal]
      simpa using ReciprocityTheory.ChartRestriction.B3.IotaPl.norm_p_lt_one (p := l)
    rw [h, Submodule.mem_bot] at hm
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hm

theorem mem_placeOf (φ : F →+* PadicAlgCl l) (x : 𝓞 F) : x ∈ (placeOf φ).asIdeal ↔ ‖φ (x : F)‖ < 1 := by
  show ‖(algebraMap (PadicAlgCl l) ℂ_[l]) (φ (x : F))‖ < 1 ↔ _
  rw [show ‖(algebraMap (PadicAlgCl l) ℂ_[l]) (φ (x : F))‖ = ‖φ (x : F)‖ from PadicComplex.norm_extends _ _]

theorem norm_le_one_iff (φ : F →+* PadicAlgCl l) (x : F) : ‖φ x‖ ≤ 1 ↔ (placeOf φ).valuation F x ≤ 1 :=
  Formalism.BasicNotions.Examples₂.norm_le_one_iff_val φ (placeOf φ) (norm_int_le_one φ) (mem_placeOf φ) x

theorem val_lt_one_iff (φ : F →+* PadicAlgCl l) (x : F) : (placeOf φ).valuation F x < 1 ↔ ‖φ x‖ < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := norm_le_one_iff φ x⁻¹
  have hpos : 0 < ‖φ x‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hx)
  have hv : 0 < (placeOf φ).valuation F x := by
    rw [pos_iff_ne_zero]; exact (Valuation.ne_zero_iff _).2 hx
  rw [map_inv₀, norm_inv, inv_le_one₀ hpos, map_inv₀, inv_le_one₀ hv] at h
  rw [← not_le, ← not_le, h]

end GlobalTheory.EvExtend

namespace GlobalTheory.EvExtend

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]

theorem exists_ext (φ : F →+* PadicAlgCl l) :
    ∃ j : (placeOf φ).adicCompletion F →+* PadicAlgCl l, Continuous j ∧
      (∀ x : F, j (algebraMap F _ x) = φ x) ∧
      (∀ y ∈ (placeOf φ).adicCompletionIntegers F, ‖j y‖ ≤ 1) ∧
      ∀ (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → (∀ x, φ x ∈ K) → ∀ y, j y ∈ K := by
  obtain ⟨j, hjc, hj⟩ := GlobalTheory.exists_continuous_extension_adicCompletion F l φ (placeOf φ) (val_lt_one_iff φ)
  have hj' : ∀ x : F, j (algebraMap F _ x) = φ x := fun x => RingHom.congr_fun hj x
  have hd := HeightOneSpectrum.denseRange_algebraMap F (placeOf φ)
  refine ⟨j, hjc, hj', fun y hy => ?_, fun K hK hφK y => ?_⟩
  · have hO : IsOpen (((placeOf φ).adicCompletionIntegers F : Set ((placeOf φ).adicCompletion F))) :=
      Valued.isOpen_valuationSubring _
    have hcl : IsClosed {y : (placeOf φ).adicCompletion F | ‖j y‖ ≤ 1} :=
      isClosed_le (continuous_norm.comp hjc) continuous_const
    refine closure_minimal ?_ hcl (hd.open_subset_closure_inter hO hy)
    rintro _ ⟨hy1, x, rfl⟩
    show ‖j (algebraMap F _ x)‖ ≤ 1
    rw [hj', norm_le_one_iff]
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, ReciprocityTheory.Aut.adic_valued_algebraMap] at hy1
    exact hy1
  · have : CompleteSpace K := FiniteDimensional.completeSpace ℚ_[l] K
    have hKc : IsClosed (K : Set (PadicAlgCl l)) := (completeSpace_coe_iff_isComplete.mp ‹_›).isClosed
    exact hd.induction_on (p := fun y => j y ∈ K) y (hKc.preimage hjc) fun x => by
      show j (algebraMap F _ x) ∈ K
      rw [hj']; exact hφK x

end GlobalTheory.EvExtend

namespace GlobalTheory.EvExtend

theorem exists_evOk : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (l : ℕ) [Fact l.Prime]
    (i : E →+* PadicAlgCl l), ∃ ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l, GlobalTheory.FrameOf.EvOk i ev := by
  intro F E _ _ _ _ _ l _ i
  let φ : F →+* PadicAlgCl l := i.comp (algebraMap F E)
  obtain ⟨j, -, hj, hint, hK⟩ := exists_ext φ
  let v := placeOf φ
  let e0 : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
    { toFun := fun a => a v, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  let : Algebra F (PadicAlgCl l) := φ.toAlgebra
  let f : FiniteAdeleRing (𝓞 F) F →ₐ[F] PadicAlgCl l :=
    { j.comp e0 with commutes' := fun x => hj x }
  let g : E →ₐ[F] PadicAlgCl l := { i with commutes' := fun x => rfl }
  let ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l :=
    (Algebra.TensorProduct.lift f g fun _ _ => Commute.all _ _).toRingHom
  have hev : ∀ a e, ev (a ⊗ₜ[F] e) = j (a v) * i e := fun a e => Algebra.TensorProduct.lift_tmul _ _ _ _ _
  refine ⟨ev, fun x => ?_, fun a ha => ?_, fun a ha => ?_, fun y => ?_⟩
  · rw [hev]
    show j 1 * i x = i x
    rw [map_one, one_mul]
  · rw [hev, map_one, mul_one]
    exact hint _ (ha v)
  · have hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal := by
      rw [mem_placeOf]
      simpa [φ] using norm_natCast_lt_one (l := l)
    rw [hev, ha v hl, map_zero, zero_mul]
  · have hKle : Formalism.BasicNotions.Examples₂.LB.Kphi i ≤ IntermediateField.adjoin ℚ_[l] (Set.range i) :=
      IntermediateField.adjoin.mono _ _ _ (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩)
    have hmem : ∀ a e, ev (a ⊗ₜ[F] e) ∈ Formalism.BasicNotions.Examples₂.LB.Kphi i := fun a e => by
      rw [hev]
      exact mul_mem (hK _ inferInstance (fun x => Formalism.BasicNotions.Examples₂.LB.phi_mem i _) _) (Formalism.BasicNotions.Examples₂.LB.phi_mem i e)
    refine hKle ?_
    induction y using TensorProduct.inductionOn with
    | tmul a e => exact hmem a e
    | add y z hy hz => rw [map_add]; exact add_mem hy hz

end GlobalTheory.EvExtend
end
end
end
