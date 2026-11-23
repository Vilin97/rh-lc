module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsForallAbvSubLt
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.InvMemUFin
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ClassFieldTheory.GlobalClassField.AsGabLim
public import ReciprocityTheory.ClassFieldTheory.GlobalClassField.IsFrobAtMulOfMemInertiaGroup

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDiagMulRayMulUnif

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.RayGen

variable {K : Type} [Field K] [NumberField K]

def compAt (v : HeightOneSpectrum (𝓞 K)) : Ideles K →* v.adicCompletion K where
  toFun a := (a : AdeleRing (𝓞 K) K).2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def compInf (w : InfinitePlace K) : Ideles K →* w.Completion where
  toFun a := (a : AdeleRing (𝓞 K) K).1 w
  map_one' := rfl
  map_mul' _ _ := rfl

def unifAway (𝔮 : Ideal (𝓞 K)) : Subgroup (Ideles K) :=
  Subgroup.closure {x : Ideles K | ∃ (v : HeightOneSpectrum (𝓞 K)) (π : (v.adicCompletion K)ˣ),
    ¬ v.asIdeal ∣ 𝔮 ∧ IsUniformiserAt K v (π : v.adicCompletion K) ∧ x = localIdele K v π}

theorem comp_of_mem_unifAway {𝔮 : Ideal (𝓞 K)} {b : Ideles K} (hb : b ∈ unifAway 𝔮) :
    (∀ w, compInf w b = 1) ∧ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔮 → compAt v b = 1 := by
  induction hb using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, π, hv, -, rfl⟩ := hx
    exact ⟨(localIdele_isSupportedAt K v π).1,
      fun v' hv' => (localIdele_isSupportedAt K v π).2 v' (by rintro rfl; exact hv hv')⟩
  | one => exact ⟨fun w => map_one _, fun v _ => map_one _⟩
  | mul x y _ _ hx hy =>
    exact ⟨fun w => by rw [map_mul, hx.1, hy.1, one_mul], fun v hv => by rw [map_mul, hx.2 v hv, hy.2 v hv, one_mul]⟩
  | inv x _ hx => exact ⟨fun w => by rw [map_inv, hx.1, inv_one], fun v hv => by rw [map_inv, hx.2 v hv, inv_one]⟩

theorem exists_unifAway {𝔮 : Ideal (𝓞 K)} (c : Ideles K)
    (hc : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔮 → Valued.v (compAt v c) = 1) :
    ∃ b ∈ unifAway 𝔮, ∀ v, Valued.v (compAt v b) = Valued.v (compAt v c) := by
  classical
  choose π hπ using exists_isUniformiserAt K
  have hfin := Filter.eventually_cofinite.mp (valued_comp_eventually K c)
  let S := hfin.toFinset
  have hS : ∀ v, v ∈ S ↔ Valued.v (compAt v c) ≠ 1 := fun v => hfin.mem_toFinset
  refine ⟨∏ v ∈ S, localIdele K v (π v) ^ ordAt K v c, Subgroup.prod_mem _ fun v hv => Subgroup.zpow_mem _
    (Subgroup.subset_closure (by exact ⟨v, π v, fun h => (hS v).1 hv (hc v h), hπ v, rfl⟩)) _, fun w => ?_⟩
  have h1 : ∀ v, v ≠ w → compAt w (localIdele K v (π v) ^ ordAt K v c) = 1 := fun v hv => by
    rw [map_zpow, show compAt w (localIdele K v (π v)) = 1 from (localIdele_isSupportedAt K v _).2 w hv.symm,
      one_zpow]
  rw [map_prod]
  by_cases hw : w ∈ S
  · rw [Finset.prod_eq_single_of_mem w hw fun v _ hv => h1 v hv, map_zpow,
      show compAt w (localIdele K w (π w)) = π w from localIdele_snd_self K w _, map_zpow₀,
      valued_eq_exp_of_isUniformiserAt K w _ (hπ w), ← WithZero.exp_zsmul, ordAt]
    rw [smul_neg, neg_smul, neg_neg, smul_eq_mul, mul_one]
    exact WithZero.exp_log (valued_comp_ne_zero K c w)
  · rw [Finset.prod_eq_one fun v hv => h1 v (fun e => hw (e ▸ hv)), map_one]
    exact (not_not.1 ((hS w).not.1 hw)).symm

theorem valued_lt_one_of_mem (v : HeightOneSpectrum (𝓞 K)) {x : 𝓞 K} (hx : x ∈ v.asIdeal) :
    Valued.v (algebraMap K (v.adicCompletion K) (x : K)) < 1 := by
  have e : algebraMap K (v.adicCompletion K) (x : K) =
      ((algebraMap (𝓞 K) K x : K) : v.adicCompletion K) := rfl
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (v.valuation_lt_one_iff_mem x).2 hx

theorem exists_approx {𝔮 : Ideal (𝓞 K)} (h𝔮 : 𝔮 ≠ ⊥) {x : 𝓞 K} (hx : x ∈ 𝔮) (hx0 : x ≠ 0) (a : Ideles K) :
    ∃ k : Kˣ, (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔮 →
      Valued.v (compAt v ((diagUnits K k)⁻¹ * a) - 1) ≤ Valued.v (algebraMap K (v.adicCompletion K) (x : K))) ∧
      ∀ w : InfinitePlace K, w.IsReal → IsSquare (compInf w ((diagUnits K k)⁻¹ * a)) := by
  classical
  let T := (Ideal.finite_factors h𝔮).toFinset
  let t' : InfinitePlace K → ℝ := fun w =>
    if hw : w.IsReal then InfinitePlace.Completion.ringEquivRealOfIsReal hw (compInf w a) else 1
  have ht' : ∀ w, t' w ≠ 0 := fun w => by
    simp only [t']
    split_ifs with hw
    · exact (map_ne_zero _).2 (inf_comp_ne_zero K a w)
    · exact one_ne_zero
  let t : (K →+* ℝ) → ℝ := fun σ => t' (InfinitePlace.mk (Complex.ofRealHom.comp σ))
  let r : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K := fun v =>
    (algebraMap K (v.adicCompletion K) (x : K) * compAt v a)⁻¹
  let U : Set (((v : T) → v.1.adicCompletion K) × ((K →+* ℝ) → ℝ)) :=
    (⋂ v : T, {y | (y.1 v - compAt v.1 a) * r v.1 ∈ v.1.adicCompletionIntegers K}) ∩
      ⋂ σ : K →+* ℝ, {y | 0 < y.2 σ * t σ}
  have : Finite (K →+* ℝ) :=
    Finite.of_injective (fun σ : K →+* ℝ => Complex.ofRealHom.comp σ) (fun σ τ h => by
      ext y
      simpa using RingHom.congr_fun h y)
  have hU : IsOpen U := by
    refine (isOpen_iInter_of_finite fun v => ?_).inter (isOpen_iInter_of_finite fun σ => ?_)
    · have h : IsOpen (v.1.adicCompletionIntegers K : Set (v.1.adicCompletion K)) :=
        Valued.isOpen_valuationSubring _
      exact h.preimage ((((continuous_apply v).comp continuous_fst).sub continuous_const).mul continuous_const)
    · exact isOpen_lt continuous_const (((continuous_apply σ).comp continuous_snd).mul continuous_const)
  obtain ⟨k, hk1, hk2⟩ := (GlobalTheory.LocalQuad.denseRange_finite_real K T).exists_mem_open hU
    ⟨(fun v => compAt v.1 a, t), Set.mem_iInter.2 fun v => by simp,
      Set.mem_iInter.2 fun σ => mul_self_pos.2 (ht' _)⟩
  have hxK : (x : K) ≠ 0 := by exact_mod_cast hx0
  have h1 : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔮 →
      Valued.v (algebraMap K (v.adicCompletion K) k - compAt v a) ≤
        Valued.v (algebraMap K (v.adicCompletion K) (x : K)) * Valued.v (compAt v a) := fun v hv => by
    have h : Valued.v ((algebraMap K (v.adicCompletion K) k - compAt v a) * r v) ≤ 1 :=
      Set.mem_iInter.1 hk1 ⟨v, (Ideal.finite_factors h𝔮).mem_toFinset.2 hv⟩
    have h0 : Valued.v (algebraMap K (v.adicCompletion K) (x : K) * compAt v a) ≠ 0 :=
      (map_ne_zero _).2 (mul_ne_zero ((map_ne_zero _).2 hxK) (comp_ne_zero K a v))
    rwa [map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 h0), one_mul, map_mul] at h
  have h2 : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔮 →
      Valued.v (algebraMap K (v.adicCompletion K) k) = Valued.v (compAt v a) := fun v hv => by
    refine Valuation.map_eq_of_sub_lt _ ((h1 v hv).trans_lt ?_)
    exact mul_lt_of_lt_one_left (zero_lt_iff.2 (valued_comp_ne_zero K a v))
      (valued_lt_one_of_mem v (Ideal.le_of_dvd hv hx))
  have h3 : ∀ (w : InfinitePlace K) (hw : w.IsReal), 0 < InfinitePlace.embedding_of_isReal hw k *
      InfinitePlace.Completion.ringEquivRealOfIsReal hw (compInf w a) := fun w hw => by
    have h : 0 < InfinitePlace.embedding_of_isReal hw k * t (InfinitePlace.embedding_of_isReal hw) :=
      Set.mem_iInter.1 hk2 _
    have e : InfinitePlace.mk (Complex.ofRealHom.comp (InfinitePlace.embedding_of_isReal hw)) = w := by
      refine Eq.trans ?_ (InfinitePlace.mk_embedding w)
      congr 1
      ext y
      simp
    change 0 < _ * t' _ at h
    rw [e] at h
    simpa only [t', dif_pos hw] using h
  by_cases hk : k = 0
  · subst hk
    refine ⟨1, fun v hv => absurd (h2 v hv).symm ?_, fun w hw => absurd (h3 w hw) (by simp)⟩
    rw [map_zero, map_zero]
    exact valued_comp_ne_zero K a v
  refine ⟨Units.mk0 k hk, fun v hv => ?_, fun w hw => ?_⟩
  · have hk' : algebraMap K (v.adicCompletion K) k ≠ 0 := (map_ne_zero _).2 hk
    rw [map_mul, map_inv, show compAt v (diagUnits K (Units.mk0 k hk)) = algebraMap K (v.adicCompletion K) k from rfl,
      show (algebraMap K (v.adicCompletion K) k)⁻¹ * compAt v a - 1 =
        (compAt v a - algebraMap K (v.adicCompletion K) k) * (algebraMap K (v.adicCompletion K) k)⁻¹ by
          field_simp, map_mul, map_inv₀, h2 v hv, Valuation.map_sub_swap,
      mul_inv_le_iff₀ (c := Valued.v (compAt v a)) (zero_lt_iff.2 (valued_comp_ne_zero K a v))]
    exact h1 v hv
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have he : e (algebraMap K w.Completion k) = InfinitePlace.embedding_of_isReal hw k := by
      simp [e, AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
    have hp : 0 < e (compInf w ((diagUnits K (Units.mk0 k hk))⁻¹ * a)) := by
      rw [map_mul, map_inv, show compInf w (diagUnits K (Units.mk0 k hk)) = algebraMap K w.Completion k from rfl,
        map_mul, map_inv₀, he, mul_comm, ← div_eq_mul_inv, div_pos_iff, ← mul_pos_iff, mul_comm]
      exact h3 w hw
    have := (Real.isSquare_iff.2 hp.le).map e.symm
    rwa [e.symm_apply_apply] at this

theorem exists_diag_mul_ray_mul_unif : ∀ (K : Type) [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ → ∀ a : Ideles K, ∃ k : Kˣ, ∃ u ∈ rayUnits K 𝔮 {w | w.IsReal}, ∃ b ∈ Subgroup.closure {x : Ideles K | ∃ (v : HeightOneSpectrum (𝓞 K)) (π : (v.adicCompletion K)ˣ), ¬ v.asIdeal ∣ 𝔮 ∧ IsUniformiserAt K v (π : v.adicCompletion K) ∧ x = localIdele K v π}, a = diagUnits K k * u * b := by
  intro K _ _ 𝔮 h𝔮 a
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔮
  obtain ⟨k, hk1, hk2⟩ := exists_approx h𝔮 hx hx0 a
  set c := (diagUnits K k)⁻¹ * a with hc
  obtain ⟨b, hb, hbv⟩ := exists_unifAway (𝔮 := 𝔮) c fun v hv => by
    rw [Valuation.map_eq_of_sub_lt _ (x := 1), map_one]
    rw [map_one]
    exact (hk1 v hv).trans_lt (valued_lt_one_of_mem v (Ideal.le_of_dvd hv hx))
  obtain ⟨hb1, hb2⟩ := comp_of_mem_unifAway hb
  refine ⟨k, c * b⁻¹, ⟨fun w hw => ?_, fun v => ?_⟩, b, hb, by rw [hc]; group⟩
  · change IsSquare (compInf w (c * b⁻¹))
    rw [map_mul, map_inv, hb1, inv_one, mul_one]
    exact hk2 w hw
  · have h1 : Valued.v (compAt v (c * b⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_inv₀, hbv]
      exact mul_inv_cancel₀ (valued_comp_ne_zero K c v)
    refine ⟨h1, ?_⟩
    change ∃ x ∈ 𝔮, Valued.v (compAt v (c * b⁻¹) - 1) ≤ _
    by_cases hv : v.asIdeal ∣ 𝔮
    · rw [map_mul, map_inv, hb2 v hv, inv_one, mul_one]
      exact ⟨x, hx, hk1 v hv⟩
    · obtain ⟨y, hy, hyv⟩ := SetLike.not_le_iff_exists.mp (Ideal.dvd_iff_le.not.1 hv)
      refine ⟨y, hy, ?_⟩
      rw [valued_algebraMap_eq_one K v y hyv]
      exact Valuation.map_sub_le _ h1.le (map_one _).le

end GlobalTheory.RayGen

end
end
end

-- Source module: ReciprocityTheory.ClassFieldTheory.GlobalClassField.AsGabLimB

section

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.GlobalClassField

open _root_.Neutral.B1 Topology Function

variable {F : Type*} [Field F] {L : IntermediateField F (AlgebraicClosure F)}

theorem isOpen_fiber_of_isOpen_ker {A B : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [Group B]
    (φ : A →* B) (h : IsOpen (φ.ker : Set A)) (b : B) : IsOpen {a | φ a = b} := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  have ha' : φ a = b := ha
  have hO : IsOpen ((fun y : A => a⁻¹ * y) ⁻¹' (φ.ker : Set A)) := h.preimage (continuous_const.mul continuous_id)
  refine Filter.mem_of_superset (hO.mem_nhds ?_) ?_
  · show a⁻¹ * a ∈ φ.ker
    rw [inv_mul_cancel]; exact one_mem _
  · intro y hy
    have hy' : φ (a⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv, inv_mul_eq_one] at hy'
    exact hy'.symm.trans ha'

theorem isOpen_ker_abRestrict (h : IsFiniteAbelian F L) :
    IsOpen ((abRestrict F L h).ker : Set (Field.absoluteGaloisGroupAbelianization F)) := by
  have := h.finiteDimensional
  have hq : IsOpen ((toAb F) ⁻¹' ((abRestrict F L h).ker : Set (Field.absoluteGaloisGroupAbelianization F))) := by
    have e : (toAb F) ⁻¹' ((abRestrict F L h).ker : Set (Field.absoluteGaloisGroupAbelianization F)) =
        ((L.fixingSubgroup : Subgroup Gal(AlgebraicClosure F/F)) : Set Gal(AlgebraicClosure F/F)) := by
      ext g
      exact abRestrict_toAb_eq_one_iff h g
    rw [e]
    exact L.fixingSubgroup_isOpen
  exact ((QuotientGroup.isQuotientMap_mk _).isOpen_preimage).1 hq

theorem isOpen_abRestrict_fiber (h : IsFiniteAbelian F L) (τ : L ≃ₐ[F] L) :
    IsOpen {x : Field.absoluteGaloisGroupAbelianization F | abRestrict F L h x = τ} :=
  isOpen_fiber_of_isOpen_ker _ (isOpen_ker_abRestrict h) τ

end ReciprocityTheory.DiscreteGroups.GlobalClassField
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinMapAbelianUnique

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.ArtinUniq

variable {K : Type} [Field K] [NumberField K]

theorem exists_ideal_unramified (L : Type) [Field L] [NumberField L] [Algebra K L] :
    ∃ 𝔡 : Ideal (𝓞 K), 𝔡 ≠ ⊥ ∧
      ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔡 → IsUnramifiedIn K v L := by
  refine ⟨(differentIdeal (𝓞 K) (𝓞 L)).under (𝓞 K), ?_, fun v hv Q hQ hl => ?_⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  · have hnd : ¬ Q ∣ differentIdeal (𝓞 K) (𝓞 L) := fun hd => hv (Ideal.dvd_iff_le.2 (by
      rw [hl.over]
      exact Ideal.comap_mono (Ideal.dvd_iff_le.1 hd)))
    exact Ideal.ramificationIdx_eq_one_iff.2 (not_dvd_differentIdeal_iff.1 hnd)

theorem mem_of_units_of_unif (v : HeightOneSpectrum (𝓞 K)) (M : Subgroup (v.adicCompletion K)ˣ)
    (hu : ∀ x : (v.adicCompletion K)ˣ, Valued.v (x : v.adicCompletion K) = 1 → x ∈ M)
    (π : (v.adicCompletion K)ˣ) (hπ : IsUniformiserAt K v (π : v.adicCompletion K)) (hM : π ∈ M)
    (x : (v.adicCompletion K)ˣ) : x ∈ M := by
  have key : ∀ x : (v.adicCompletion K)ˣ, Valued.v (x : v.adicCompletion K) ≤ 1 → x ∈ M := by
    intro x hx
    obtain ⟨hπ1, hirr⟩ := hπ
    have hxm : (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K := hx
    have hx0 : (⟨x, hxm⟩ : v.adicCompletionIntegers K) ≠ 0 := fun h0 =>
      x.ne_zero (congrArg Subtype.val h0)
    obtain ⟨n, u, e⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hirr
    have e' : (x : v.adicCompletion K) =
        ((u : v.adicCompletionIntegers K) : v.adicCompletion K) * (π : v.adicCompletion K) ^ n :=
      congrArg Subtype.val e
    have h1 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1 :=
      (u : v.adicCompletionIntegers K).2
    have h2 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) :
        v.adicCompletion K) ≤ 1 := ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K).2
    have h3 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
        Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) :
        v.adicCompletion K) = 1 := by
      rw [← map_mul]
      have : ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
          (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) :
          v.adicCompletion K) = 1 := congrArg Subtype.val u.mul_inv
      rw [this, map_one]
    have h4 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 :=
      le_antisymm h1 (h3 ▸ mul_le_of_le_one_right' h2)
    have hy : x * (π ^ n)⁻¹ ∈ M := by
      refine hu _ ?_
      have : ((x * (π ^ n)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          ((u : v.adicCompletionIntegers K) : v.adicCompletion K) := by
        rw [Units.val_mul, e', Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
        exact mul_inv_cancel_right₀ (pow_ne_zero n π.ne_zero) _
      rw [this, h4]
    have := M.mul_mem hy (M.pow_mem hM n)
    rwa [inv_mul_cancel_right] at this
  rcases le_total (Valued.v (x : v.adicCompletion K)) 1 with h | h
  · exact key x h
  · refine inv_mem_iff.1 (key x⁻¹ ?_)
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_le_one_of_one_le₀ h

theorem localIdele_eq {Art Art' : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K}
    (hA : IsGlobalArtinMap K Art) (hA' : IsGlobalArtinMap K Art')
    (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L)
    (v : HeightOneSpectrum (𝓞 K)) (hv : IsUnramifiedIn K v L) (x : (v.adicCompletion K)ˣ) :
    abRestrict K L h (Art (QuotientGroup.mk (localIdele K v x))) =
      abRestrict K L h (Art' (QuotientGroup.mk (localIdele K v x))) := by
  haveI := h.finiteDimensional
  haveI : NumberField L := NumberField.of_module_finite K L
  obtain ⟨π, hπ⟩ := exists_isUniformiserAt K v
  obtain ⟨Q, hQ, hQv⟩ := ReciprocityTheory.DiscreteGroups.GlobalClassField.exists_liesOver (K := K) L v
  refine mem_of_units_of_unif v (MonoidHom.eqLocus (localComposite K Art L h v)
    (localComposite K Art' L h v)) (fun y hy => ?_) π hπ ?_ x
  · have hy' : Valued.v ((localIdele K v y : AdeleRing (𝓞 K) K).2 v) = 1 := by
      rw [localIdele_snd_self]
      exact hy
    exact ((hA.2.2.2.1 L h v hv _ (localIdele_isSupportedAt K v y)).2 hy').trans
      ((hA'.2.2.2.1 L h v hv _ (localIdele_isSupportedAt K v y)).2 hy').symm
  · have hπ' : IsUniformiserAt K v ((localIdele K v π : AdeleRing (𝓞 K) K).2 v) := by
      rw [localIdele_snd_self]
      exact hπ
    exact ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_unique v Q hv _ _
      ((hA.2.2.2.1 L h v hv _ (localIdele_isSupportedAt K v π)).1 hπ' Q hQ hQv)
      ((hA'.2.2.2.1 L h v hv _ (localIdele_isSupportedAt K v π)).1 hπ' Q hQ hQv)

def infI : (InfiniteAdeleRing K)ˣ →* Ideles K :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) : _ →* _)

theorem inf_mem [_root_.NumberField.IsTotallyComplex K] (N : Subgroup (Ideles K)) (m : ℕ) (hm : 0 < m)
    (hpow : ∀ x : Ideles K, x ^ m ∈ N) (y : (InfiniteAdeleRing K)ˣ) :
    infI y ∈ N := by
  haveI : ∀ w : InfinitePlace K, IsAlgClosed w.Completion := fun w =>
    IsAlgClosed.of_ringEquiv ℂ _
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm
  choose r hr using fun w : InfinitePlace K =>
    IsAlgClosed.exists_pow_nat_eq ((y : InfiniteAdeleRing K) w) hm
  obtain ⟨r', hb⟩ : ∃ r' : InfiniteAdeleRing K, r' ^ m = (y : InfiniteAdeleRing K) :=
    ⟨r, funext hr⟩
  obtain ⟨z, rfl⟩ : IsUnit r' := (isUnit_pow_iff hm.ne').1 (hb ▸ y.isUnit)
  have e : z ^ m = y := Units.ext (by rw [Units.val_pow_eq_pow_val, hb])
  rw [← e, map_pow]
  exact hpow _

theorem valued_le_of_mem (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) {x : 𝓞 K}
    (hx : x ∈ v.asIdeal ^ n) :
    Valued.v (algebraMap K (v.adicCompletion K) (x : K)) ≤ WithZero.exp (-(n : ℤ)) := by
  have e2 : algebraMap K (v.adicCompletion K) (x : K) =
      ((algebraMap (𝓞 K) K x : K) : v.adicCompletion K) := rfl
  rw [e2, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_le_pow_iff_mem x n).2 hx

theorem exists_modulus (𝔡 : Ideal (𝓞 K)) (h𝔡 : 𝔡 ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) : ∃ 𝔮 : Ideal (𝓞 K), 𝔮 ≠ ⊥ ∧ 𝔡 ∣ 𝔮 ∧ ∀ v ∈ S, 𝔮 ≤ v.asIdeal ^ n := by
  refine ⟨𝔡 * ∏ v ∈ S, v.asIdeal ^ n,
    mul_ne_zero h𝔡 (Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero n v.ne_bot),
    dvd_mul_right _ _, fun v hv => ?_⟩
  exact Ideal.le_of_dvd ((Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 K) =>
    v.asIdeal ^ n) hv).mul_left _)

theorem abRestrict_eq : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (Art Art' : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K),
    IsGlobalArtinMap K Art → IsGlobalArtinMap K Art' →
    ∀ (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L)
      (c : IdeleClassGroup K),
      abRestrict K L h (Art c) = abRestrict K L h (Art' c) := by
  intro K _ _ _ Art Art' hA hA' L h c
  haveI := h.finiteDimensional
  haveI := h.isGalois
  haveI : NumberField L := NumberField.of_module_finite K L
  let f : Ideles K →* (L ≃ₐ[K] L) :=
    (abRestrict K L h).comp (Art.comp (QuotientGroup.mk' (diagUnits K).range))
  let f' : Ideles K →* (L ≃ₐ[K] L) :=
    (abRestrict K L h).comp (Art'.comp (QuotientGroup.mk' (diagUnits K).range))
  let N : Subgroup (Ideles K) := MonoidHom.eqLocus f f'
  have hfib : ∀ (B : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K),
      Continuous B → ∀ τ : L ≃ₐ[K] L,
      IsOpen {a : Ideles K | abRestrict K L h (B (QuotientGroup.mk a)) = τ} := fun B hB τ =>
    (ReciprocityTheory.DiscreteGroups.GlobalClassField.isOpen_abRestrict_fiber h τ).preimage (hB.comp continuous_quot_mk)
  have hopen : IsOpen (N : Set (Ideles K)) := by
    have e : (N : Set (Ideles K)) = ⋃ τ : L ≃ₐ[K] L,
        {a : Ideles K | abRestrict K L h (Art (QuotientGroup.mk a)) = τ} ∩
        {a : Ideles K | abRestrict K L h (Art' (QuotientGroup.mk a)) = τ} := by
      ext a
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      exact ⟨fun ha => ⟨_, rfl, ha.symm⟩, fun ⟨τ, h1, h2⟩ => h1.trans h2.symm⟩
    rw [e]
    exact isOpen_iUnion fun τ => (hfib Art hA.1 τ).inter (hfib Art' hA'.1 τ)
  obtain ⟨𝔡, h𝔡, hun⟩ := exists_ideal_unramified (K := K) L
  obtain ⟨S, n, hS⟩ := PI.AlgValsFin.W.exists_nbhd (N : Set (Ideles K)) hopen N.one_mem
  obtain ⟨𝔮, h𝔮, hd𝔮, hS𝔮⟩ := exists_modulus 𝔡 h𝔡 S n
  have hpow : ∀ x : Ideles K, x ^ Nat.card (L ≃ₐ[K] L) ∈ N := fun x => by
    show f _ = f' _
    rw [map_pow, map_pow, pow_card_eq_one', pow_card_eq_one']
  have hray : ∀ u ∈ rayUnits K 𝔮 {w | w.IsReal}, u ∈ N := by
    rintro u ⟨-, hu⟩
    have e : u = infI
        (Units.map (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) : _ →* _) u) *
        GlobalTheory.Mem.Chr.finPartI K u :=
      Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    rw [e]
    refine N.mul_mem (inf_mem N _ Nat.card_pos hpow _) (hS _ ⟨rfl, fun v => (hu v).1⟩ fun v hv => ?_)
    obtain ⟨-, x, hx, hle⟩ := hu v
    exact hle.trans (valued_le_of_mem v n (hS𝔮 v hv hx))
  have hloc : Subgroup.closure {x : Ideles K | ∃ (v : HeightOneSpectrum (𝓞 K))
      (π : (v.adicCompletion K)ˣ), ¬ v.asIdeal ∣ 𝔮 ∧
        IsUniformiserAt K v (π : v.adicCompletion K) ∧ x = localIdele K v π} ≤ N := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨v, π, hv, -, rfl⟩
    exact localIdele_eq hA hA' L h v (hun v fun hd => hv (hd.trans hd𝔮)) π
  have hdiag : (diagUnits K).range ≤ N := by
    rintro _ ⟨k, rfl⟩
    have e : QuotientGroup.mk' (diagUnits K).range (diagUnits K k) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨k, rfl⟩
    show abRestrict K L h (Art (QuotientGroup.mk' (diagUnits K).range (diagUnits K k))) =
      abRestrict K L h (Art' (QuotientGroup.mk' (diagUnits K).range (diagUnits K k)))
    simp only [e, map_one]
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨k, u, hu, b, hb, e⟩ := GlobalTheory.RayGen.exists_diag_mul_ray_mul_unif K 𝔮 h𝔮 a
  have ha : a ∈ N := e ▸ N.mul_mem (N.mul_mem (hdiag ⟨k, rfl⟩) (hray u hu)) (hloc hb)
  exact ha

end GlobalTheory.CompanionTheory.ArtinUniq
end
end
end
