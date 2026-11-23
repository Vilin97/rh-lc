module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorGeneralPointBranches
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorGeneralPointBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelExists
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorRegularGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalDivisorChartGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalDoublePointsGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorGoodPointBranches
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
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
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
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorGeneralPointBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorGoodPointBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorOneComponent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLeadIdealDim
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMultGeneral
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.Topology.Algebra.MvPolynomial
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PJacobianRankOffHypersurface
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCodimOneCompleteIntersection
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCodimOneUniformiser
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelDivisorChartGeneric
public import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.Tactic.Linter.Style
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalDoublePointsGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelGoodPointGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelGoodPointChart
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelExists
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelGoodPointChart
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelGoodPointGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionUnramifiedGeneric
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.BranchInverseOffHypersurfaceHolds

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorBranches

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

namespace DivisorBranches

theorem quotient_inf_dim_lt {R : Type*} [CommRing R] {I₁ I₂ : Ideal R} {d : ℕ}
    (h₁ : ringKrullDim (R ⧸ I₁) < (d : ℕ)) (h₂ : ringKrullDim (R ⧸ I₂) < (d : ℕ)) :
    ringKrullDim (R ⧸ (I₁ ⊓ I₂)) < (d : ℕ) := by
  apply _root_.GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.quotient_inf_dim_lt <;> assumption

theorem not_mem_zeroSet_of_le {n : ℕ} {I I' : Ideal (MvPolynomial (Fin n) ℂ)} (hle : I ≤ I')
    {q : Fin n → ℂ} (hq : q ∉ zeroSet I) : q ∉ zeroSet I' :=
  fun h => hq fun f hf => h f (hle hf)

theorem proof (hModel : IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.Statement)
    (hReg : DivisorRegularGeneric.Statement) (hChart : NormalDivisorChartGeneric.Statement)
    (hDouble : NormalDoublePointsGeneric.Statement) (hGood : DivisorGoodPointBranches.Statement) :
    DivisorBranches.Statement := by
  intro n d J u hJ hdim hu
  obtain ⟨M⟩ := hModel n J hJ
  obtain ⟨I₁, hle₁, hdim₁, hI₁⟩ := hReg n d J u hJ hdim hu
  obtain ⟨I₂, hle₂, hdim₂, hI₂⟩ := hChart n d J u M hJ hdim hu
  obtain ⟨I₃, hle₃, hdim₃, hI₃⟩ := hDouble n d J u M hJ hdim hu
  refine ⟨I₁ ⊓ I₂ ⊓ I₃, le_inf (le_inf hle₁ hle₂) hle₃,
    quotient_inf_dim_lt (quotient_inf_dim_lt hdim₁ hdim₂) hdim₃, ?_⟩
  intro q hqJ hqu hqI
  exact hGood n d J u M q hJ hdim hu hqJ hqu
    (hI₁ q hqJ hqu (not_mem_zeroSet_of_le (inf_le_left.trans inf_le_left) hqI))
    (hI₂ q hqJ hqu (not_mem_zeroSet_of_le (inf_le_left.trans inf_le_right) hqI))
    (hI₃ q hqJ hqu (not_mem_zeroSet_of_le inf_le_right hqI))

end DivisorBranches

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorOneComponent

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

namespace DivisorOneComponent

theorem mem_zeroSet_iff {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    q ∈ zeroSet K ↔ K ≤ RingHom.ker (eval q) :=
  ⟨fun h f hf => RingHom.mem_ker.2 (h f hf), fun h _ hf => RingHom.mem_ker.1 (h hf)⟩

theorem isClosed_zeroSet {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet K) := by
  have : zeroSet K = ⋂ f ∈ K, {x : Fin n → ℂ | eval x f = 0} := by ext x; simp [zeroSet]
  rw [this]
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const

theorem exists_bound (d : ℕ) : ∃ N : WithBot ℕ∞, N < (d : WithBot ℕ∞) ∧
    ∀ x : WithBot ℕ∞, x + 1 ≤ (d : WithBot ℕ∞) → x ≤ N := by
  rcases d with _ | k
  · refine ⟨⊥, WithBot.bot_lt_coe _, fun x hx => ?_⟩
    cases x using WithBot.recBotCoe with
    | bot => exact le_rfl
    | coe y =>
      have : y + 1 ≤ 0 := by exact_mod_cast hx
      simp at this
  · refine ⟨(k : WithBot ℕ∞), by exact_mod_cast Nat.lt_succ_self k, fun x hx => ?_⟩
    cases x using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe y =>
      have h1 : y + 1 ≤ ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast hx
      have h2 : y ≤ (k : ℕ∞) := by
        cases y using ENat.recTopCoe with
        | top => simp at h1
        | coe y =>
          have h3 : y + 1 ≤ k + 1 := by exact_mod_cast h1
          exact_mod_cast (by omega : y ≤ k)
      exact_mod_cast h2

theorem dim_sup_add_one_le {n d : ℕ} {J W W' : Ideal (MvPolynomial (Fin n) ℂ)} [J.IsPrime] {u : Fin n → ℂ}
    (hu : linForm u ∉ J) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hW : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes)
    (hW' : W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes) (hne : W ≠ W') :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ W')) + 1 ≤ (d : WithBot ℕ∞) := by
  have _ : W.IsPrime := hW.1.1
  obtain ⟨x, hxW', hxW⟩ : ∃ x ∈ W', x ∉ W := by
    by_contra! h
    exact hne (le_antisymm (hW.2 hW'.1 h) h)
  have hle : W ⊔ Ideal.span {x} ≤ W ⊔ W' := sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 hxW') _
  have hx : x ∈ W ⊔ Ideal.span {x} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
  have hr : Ideal.Quotient.mk W x ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ W) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hsurj : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ W')) ≤
      ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W x}) := by
    refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor
      (le_sup_left.trans hle)) ?_) (Ideal.Quotient.lift_surjective_of_surjective _ _
        (Ideal.Quotient.factor_surjective _))
    intro y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    have h0 : Ideal.Quotient.mk (W ⊔ W') (c' * x) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (hle hx))
    simpa [Ideal.Quotient.factor_mk, map_mul] using h0
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ W')) + 1
      ≤ ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W x}) + 1 := by gcongr
    _ ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
    _ = (d : WithBot ℕ∞) := ringKrullDim_component hu hW hdim

end DivisorOneComponent


open DivisorOneComponent in
theorem DivisorOneComponent.proof : DivisorOneComponent.Statement := by
  classical
  intro n d J u hJ hdim hu
  have hKq : ∀ x ∈ zeroSet J, linEval u x = 0 → J ⊔ Ideal.span {linForm u} ≤ RingHom.ker (eval x) := by
    intro x hxJ hxu
    refine sup_le ((mem_zeroSet_iff J x).1 hxJ) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    simpa [linForm, linEval] using hxu
  generalize hK : J ⊔ Ideal.span {linForm u} = K at hKq ⊢
  have hM : K.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ K
  obtain ⟨S, hS⟩ : ∃ S : Finset (Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ)),
      ∀ p, p ∈ S ↔ p.1 ∈ K.minimalPrimes ∧ p.2 ∈ K.minimalPrimes ∧ p.1 ≠ p.2 :=
    ⟨(hM.prod hM).toFinset.filter fun p => p.1 ≠ p.2, fun p => by rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_prod, and_assoc]⟩
  obtain ⟨I, hI⟩ : ∃ I, I = S.inf fun p => p.1 ⊔ p.2 := ⟨_, rfl⟩
  have hmemS : ∀ p ∈ S, p.1 ∈ K.minimalPrimes ∧ p.2 ∈ K.minimalPrimes ∧ p.1 ≠ p.2 := fun p hp => (hS p).1 hp
  have hpair : ∀ W W', W ∈ K.minimalPrimes → W' ∈ K.minimalPrimes → W ≠ W' → I ≤ W ⊔ W' :=
    fun W W' hW hW' hne => by
      have h := Finset.inf_le (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) ((hS (W, W')).2 ⟨hW, hW', hne⟩)
      rw [hI]; exact h
  have hKI : K ≤ I := by
    have h := Finset.le_inf (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) (a := K) (s := S) fun p hp => (hmemS p hp).1.1.2.trans le_sup_left
    rw [hI]; exact h
  obtain ⟨N, hN, hxN⟩ := exists_bound d
  refine ⟨I, hKI, ?_, ?_⟩
  · refine lt_of_le_of_lt (ComplexSets.quotient_dim_le_of_minimalPrimes I fun Z hZ => ?_) hN
    have hZI : S.inf (fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) ≤ Z := by rw [← hI]; exact hZ.1.2
    obtain ⟨p, hp, hpZ⟩ := (Ideal.IsPrime.inf_le' (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) hZ.1.1).1 hZI
    obtain ⟨h1, h2, h12⟩ := hmemS p hp
    exact (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hpZ)).trans
      (hxN _ (dim_sup_add_one_le hu hdim (by rw [hK]; exact h1) (by rw [hK]; exact h2) h12))
  · intro q hqJ hqu hqI
    obtain ⟨W, hW, hWq⟩ := Ideal.exists_minimalPrimes_le (hKq q hqJ hqu)
    have huniq : ∀ W' ∈ K.minimalPrimes, q ∈ zeroSet W' → W' = W := by
      intro W' hW' hq'
      by_contra hne
      exact hqI ((mem_zeroSet_iff I q).2 ((hpair W W' hW hW' (Ne.symm hne)).trans
        (sup_le hWq ((mem_zeroSet_iff W' q).1 hq'))))
    refine ⟨W, hW, (mem_zeroSet_iff W q).2 hWq, huniq, ⋂ W' ∈ K.minimalPrimes \ {W}, (zeroSet W')ᶜ, ?_, ?_⟩
    · refine (biInter_mem (hM.subset Set.sdiff_subset)).2 fun W' hW' => (isClosed_zeroSet W').isOpen_compl.mem_nhds ?_
      exact fun hq' => hW'.2 (huniq W' hW'.1 hq')
    · rintro x ⟨hxJ, hxU⟩ hxu
      obtain ⟨W'', hW'', hW''x⟩ := Ideal.exists_minimalPrimes_le (hKq x hxJ hxu)
      by_cases h : W'' = W
      · subst h; exact (mem_zeroSet_iff W'' x).2 hW''x
      · exact absurd ((mem_zeroSet_iff W'' x).2 hW''x) (Set.mem_iInter₂.1 hxU W'' ⟨hW'', h⟩)

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalDivisorChartGeneric

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace NormalDivisorChartGeneric

theorem ringKrullDim_le_of_injective_isIntegral {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective f) (hint : f.IsIntegral) : ringKrullDim R ≤ ringKrullDim S := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hint⟩
  refine iSup_le fun l => ?_
  have hker : (⊥ : Ideal S).comap (algebraMap R S) ≤ (RelSeries.head l).asIdeal := by
    intro r hr
    have : f r = 0 := hr
    rw [show r = 0 from hinj (by rw [this, map_zero])]
    exact Ideal.zero_mem _
  obtain ⟨P, -, hP, hPo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ ⊥ hker
  have : P.LiesOver (RelSeries.head l).asIdeal := ⟨hPo.symm⟩
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  exact le_iSup_of_le L (by rw [hlen])

theorem isIntegral_mk_comp_rename {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) {B : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ)} (hB : M.ideal ≤ B) :
    ((Ideal.Quotient.mk B).comp (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom).IsIntegral := by
  set f := (Ideal.Quotient.mk B).comp (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom with hf
  let : Algebra (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) := f.toAlgebra
  have hX : ∀ s, IsIntegral (MvPolynomial (Fin n) ℂ) (Ideal.Quotient.mk B (X s)) := by
    rintro (i | i)
    · have h : Ideal.Quotient.mk B (X (Sum.inl i)) =
          algebraMap (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) (X i) := by
        show _ = f (X i)
        simp [hf]
      rw [h]
      exact isIntegral_algebraMap
    · obtain ⟨P, hPm, hP⟩ := M.integral i
      refine ⟨P, hPm, ?_⟩
      have h := Ideal.Quotient.eq_zero_iff_mem.mpr (hB hP)
      rw [Polynomial.hom_eval₂] at h
      exact h
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  show IsIntegral (MvPolynomial (Fin n) ℂ) (Ideal.Quotient.mk B p)
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : Ideal.Quotient.mk B (C a) =
        algebraMap (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) (C a) := by
      show _ = f (C a)
      simp [hf]
    rw [h]
    exact isIntegral_algebraMap
  | add p q hp hq =>
    rw [map_add (f := _)]
    exact hp.add hq
  | mul_X p s hp =>
    rw [map_mul]
    exact hp.mul (hX s)

theorem proof (hUp : NormalModelDivisorChartGeneric.Statement) : NormalDivisorChartGeneric.Statement := by
  intro n d J u M hJ hdim hu
  obtain ⟨B, hleB, hdimB, hB⟩ := hUp n d J u M hJ hdim hu
  refine ⟨B.comap (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom, ?_, ?_, ?_⟩
  · refine sup_le ?_ ((Ideal.span_le).2 (Set.singleton_subset_iff.2 ?_))
    · exact M.comap_eq.symm.le.trans (Ideal.comap_mono (le_sup_left.trans hleB))
    · exact hleB (Ideal.mem_sup_right (Ideal.subset_span rfl))
  · refine lt_of_le_of_lt ?_ hdimB
    exact ringKrullDim_le_of_injective_isIntegral _ Ideal.quotientMap_injective
      ((isIntegral_quotientMap_iff _).2 (isIntegral_mk_comp_rename M (le_sup_left.trans hleB)))
  · intro q _ hqu hqI w hw hwq
    refine hB w hw (hwq ▸ hqu) fun hwB => hqI fun f hf => ?_
    have h := hwB _ hf
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, eval_rename] at h
    rw [← hwq]
    exact h

end NormalDivisorChartGeneric

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelDivisorChartGeneric

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

theorem NormalModelDivisorChartGeneric.proof (h₁ : NormalModelGoodPointGeneric.Statement)
    (h₂ : NormalModelGoodPointChart.Statement) : NormalModelDivisorChartGeneric.Statement := by
  intro n d J u M hJ hd hu
  obtain ⟨B, hB, hBd, hgood⟩ := h₁ n d J u M hJ hd hu
  exact ⟨B, hB, hBd, fun w hw hu0 hwB => h₂ n d J u M w (hgood w hw hu0 hwB)⟩

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisorGeneralPointBranches

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.ComplexSets


open GroundTheory.Heights₂.Heights in
theorem divisorGeneralPointBranches : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement :=
  DivisorGeneralPointBranches.proof DivisorOneComponent.proof
    (DivisorBranches.proof IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof
      GroundTheory.Heights₂.Heights.AutoClose.DivisorRegularGeneric
      (NormalDivisorChartGeneric.proof
        (NormalModelDivisorChartGeneric.proof
          (NormalModelGoodPointGeneric.proof NormalCodimOneCompleteIntersection.proof
            NormalCodimOneUniformiser.proof JacobianRankOffHypersurface.proof
            ProjectionUnramifiedGeneric.proof)
          NormalModelGoodPointChart.proof))
      NormalDoublePointsGeneric.proof DivisorGoodPointBranches.proof)

end GlobalTheory.CompanionTheory.ComplexSets
end
end
