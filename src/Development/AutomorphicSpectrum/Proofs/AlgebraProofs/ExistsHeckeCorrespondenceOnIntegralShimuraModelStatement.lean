module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosure
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CutEffectiveDivisorStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommuteStatement
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutContraction
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutForms
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutLiesOver
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutForms
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisBis
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutTools
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RelevantMinimalOfDivCycleNeZero
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSegreFlagCutDivisorX
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutChartSection
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutChartSection
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersLocalIntegralClosureFinite
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.NumbersDVRC3ResidualContractionComponent

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutProjection

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagCutProjection

theorem relDim_anti {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} {I J : Ideal (MRing ι F)}
    (hIJ : I ≤ J) : FieldNumbers.relDim J ≤ FieldNumbers.relDim I := by
  have hmono : Monotone (fun x : WithBot ℕ∞ =>
      WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d) x) :=
    WithBot.monotone_map_iff.2 (WithTop.monotone_map_iff.2 (fun a b h =>
      Int.sub_le_sub_right (by exact_mod_cast h) _))
  exact hmono (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hIJ) (Ideal.Quotient.factor_surjective hIJ))

theorem specialIdeal_le_contractPrime {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K K' : Type*} [DecidableEq K] [DecidableEq K'] (j : K ↪ K') {ι' : K' → Type*}
    {I : Ideal (MRing (fun k => ι' (j k)) O)} {W : Ideal (MRing ι' O)}
    (h : I ≤ W.comap (rename (FieldNumbers.blockIncl j ι'))) :
    specialIdeal I ≤ FieldNumbers.contractPrime j (specialIdeal W) := by
  refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
  simp only [Ideal.mem_comap, FieldNumbers.contractPrime, specialIdeal]
  rw [← map_rename]
  exact Ideal.mem_map_of_mem _ (h hf)

end SegreFlagCutProjection

open SegreFlagCutProjection in
theorem SegreFlagCutProjection.proof (hLies : SegreFlagCutLiesOver.Statement)
    (hDim : SegreFlagProjSpecialDim.Statement) : SegreFlagCutProjection.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk
  obtain ⟨hl1, hl2⟩ := hLies O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  obtain ⟨hd1, hd2⟩ := hDim O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  refine ⟨fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW => ?_,
    fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW => ?_⟩
  · exact lt_of_le_of_lt (relDim_anti (specialIdeal_le_contractPrime _
      (hl1 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW))) hd1
  · exact lt_of_le_of_lt (relDim_anti (specialIdeal_le_contractPrime _
      (hl2 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW))) hd2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutSection

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem SegreFlagCutSection.proof (hModel : SegreFlagClosureModel.Statement)
    (hForms : SegreFlagCutForms.Statement) (hDiv : SegreFlagCutDivisor.Statement)
    (hD0 : SegreFlagDegreeZero.Statement) : SegreFlagCutSection.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk r a ha
  classical
  set I := pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) with hI
  have hIp : I.IsPrime := (hModel O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht (k + 1) (Nat.le_add_left 1 k) hk).1.multiProj.isPrime
  have hpt : ∀ (j : ℕ) (p : Σ k, ι k),
      flagClosurePt y w e φ φ' t j ⟨some (some p.1), p.2⟩ = algebraMap Ω Φ (y p) := fun _ _ => rfl
  have hlift : ∀ i, liftPairForm M M' (a i) ∉ I := fun i hm =>
    ha i ((liftPairForm_mem_iff (hpt (k + 1)) _).1 hm)
  obtain ⟨f₃, g₃, hD₃, hv₃, hk₃⟩ := hD0 O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk

  let bad : MRing (bundleIdx (bundleIdx ι M) M') O → Set (Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)) :=
    fun z => {Q | Q ∈ (I ⊔ Ideal.span {z}).minimalPrimes ∧ IsRelevant Q ∧
      (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ Q}
  let T := bad f₃ ∪ bad g₃ ∪ ⋃ i, bad (liftPairForm M M' (a i))
  have hbfin : ∀ z, (bad z).Finite := fun z =>
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (I ⊔ Ideal.span {z})).subset fun Q hQ => hQ.1
  have hTfin : T.Finite := ((hbfin _).union (hbfin _)).union (Set.finite_iUnion fun i => hbfin _)
  have hbad : ∀ z, ∀ Q ∈ bad z, Q.IsPrime ∧ IsRelevant Q ∧ I ≤ Q ∧
      (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ Q :=
    fun _ _ hQ => ⟨Ideal.IsMinimalPrime.isPrime hQ.1, hQ.2.1,
      le_sup_left.trans (Ideal.IsMinimalPrime.le hQ.1), hQ.2.2⟩
  obtain ⟨cs, ch, s, h, hs, hh, hdeg, hsI, hhI, hval, havoid⟩ :=
    hForms O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk
      hTfin.toFinset (by
        intro Q hQ
        rcases (hTfin.mem_toFinset.1 hQ) with (hQ | hQ) | hQ
        · exact hbad _ Q hQ
        · exact hbad _ Q hQ
        · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hQ
          exact hbad _ Q hi)
  have hdiv := hDiv O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk
    cs ch s h hs hh hdeg hsI hhI hval
  refine ⟨cs, ch, s, h, f₃, g₃, hs, hh, hdeg, hsI, hhI, hval, hdiv, hD₃, hv₃, hk₃, ?_⟩
  intro H hH hϖH
  by_cases hh0 : divCycle I h H = 0
  ·
    have hs0 : divCycle I s H ≠ 0 := hH.resolve_right (not_not.2 hh0)
    have hne : ratDiv I s h H ≠ 0 := by
      unfold ratDiv
      rw [hh0, sub_zero]
      exact hs0
    rw [hdiv H hϖH] at hne
    split_ifs at hne with hc
    · obtain ⟨hk0, rfl⟩ := hc
      obtain ⟨hf, hg, -⟩ := hk₃ hk0
      exact ⟨hf, hg, fun i hm => ha i ((liftPairForm_mem_iff (hpt k) _).1 hm)⟩
    · exact absurd rfl hne
  ·
    obtain ⟨hmin, hrel⟩ := relevant_minimal_of_divCycle_ne_zero hh0
    have hhH : h ∈ H :=
      Ideal.IsMinimalPrime.le hmin (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))
    have avoid : ∀ z, z ∉ I → (H ∈ bad z → H ∈ T) → z ∉ H := by
      intro z hz hT hzH
      exact havoid H (hTfin.mem_toFinset.2 (hT ⟨mem_minimalPrimes_sup_span_of_mem hmin hz hzH, hrel, hϖH⟩)) hhH
    exact ⟨avoid f₃ hD₃.num_not_mem fun h' => Set.mem_union_left _ (Set.mem_union_left _ h'),
      avoid g₃ hD₃.den_not_mem fun h' => Set.mem_union_left _ (Set.mem_union_right _ h'),
      fun i => avoid _ (hlift i) fun h' => Set.mem_union_right _ (Set.mem_iUnion.2 ⟨i, h'⟩)⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutLiesOver

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagCutLiesOverProof

variable {κ : Type} [Fintype κ] [DecidableEq κ] {ικ : κ → Type} [∀ o, Fintype (ικ o)] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] {Φ : Type} [Field Φ] [Algebra O Φ]

theorem le_comap_of_chart (pt : (Σ o, ικ o) → Φ) {A F : Type*} [CommRing A] [FunLike F A (MRing ικ O)]
    [RingHomClass F A (MRing ικ O)] (ρ : F) (Q : Ideal A) (u : MRing ικ O) (τ : Φ) {cs ch dl dm : κ → ℕ}
    {s h l μ : MRing ικ O} (hs : IsMultiHomog s cs) (hh : IsMultiHomog h ch) (hl : IsMultiHomog l dl)
    (hμ : IsMultiHomog μ dm) (hdeg : cs + dm = dl + ch) (hsP : s ∉ pointIdeal O pt)
    (hhP : h ∉ pointIdeal O pt) (hsv : aeval pt s = τ * aeval pt h) (hlv : aeval pt l = τ * aeval pt μ)
    (hsat : ∀ q ∈ Q, ∃ n : ℕ, u ^ n * ρ q ∈ pointIdeal O pt ⊔ Ideal.span {l})
    {W : Ideal (MRing ικ O)} (hμW : μ ∉ W) (huW : ∀ n : ℕ, u ^ n ∉ W)
    (hPW : pointIdeal O pt ≤ W) (hW : ratDiv (pointIdeal O pt) s h W ≠ 0) : Q ≤ W.comap ρ := by
  have : (pointIdeal O pt).IsPrime := RingHom.ker_isPrime _
  have hμP : μ ∉ pointIdeal O pt := fun h' => hμW (hPW h')
  have hsv0 : aeval pt s ≠ 0 := fun h0 => hsP (GenericProjClosureDivisor.mem_of_homog hs h0)
  have hτ : τ ≠ 0 := by
    rintro rfl
    exact hsv0 (by rw [hsv, zero_mul])
  have hμv : aeval pt μ ≠ 0 := fun h0 => hμP (GenericProjClosureDivisor.mem_of_homog hμ h0)
  have hlP : l ∉ pointIdeal O pt := fun h' =>
    mul_ne_zero hτ hμv (hlv ▸ GenericProjClosureDivisor.aeval_eq_zero_of_mem h')
  have hdiff : s * μ - l * h ∈ pointIdeal O pt := by
    have h2 := hl.mul hh
    rw [← hdeg] at h2
    have h1 : IsMultiHomog (s * μ - l * h) (cs + dm) :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sub_mem _
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hs.mul hμ))
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))
    refine GenericProjClosureDivisor.mem_of_homog h1 ?_
    rw [map_sub, map_mul, map_mul, hsv, hlv]
    ring
  have hrat := congrFun (ratDiv_eq_of_sub_mem hsP hhP hlP hμP hdiff) W
  have hμ0 : divCycle (pointIdeal O pt) μ W = 0 := by
    unfold divCycle
    rw [dite_eq_right]
    rintro ⟨h', -⟩
    exact hμW (h'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self μ)))
  have hl0 : divCycle (pointIdeal O pt) l W ≠ 0 := by
    rw [hrat] at hW
    unfold ratDiv at hW
    rwa [hμ0, sub_zero] at hW
  have hmin : W ∈ (pointIdeal O pt ⊔ Ideal.span {l}).minimalPrimes := by
    unfold divCycle at hl0
    split_ifs at hl0 with h'
    · exact h'.1
    · exact absurd rfl hl0
  have hWp : W.IsPrime := hmin.1.1
  intro q hq
  obtain ⟨n, hn⟩ := hsat q hq
  exact (hWp.mem_or_mem (hmin.1.2 hn)).resolve_left (huW n)


omit [Fintype κ] [DecidableEq κ] [∀ o, Fintype (ικ o)] [IsDomain O] [IsDiscreteValuationRing O] in
theorem support_ratDiv {P W : Ideal (MRing ικ O)} {s h : MRing ικ O} (hW : ratDiv P s h W ≠ 0) :
    W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
  have key : ∀ v, divCycle P v W ≠ 0 → W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
    intro v hv
    unfold divCycle at hv
    split_ifs at hv with h'
    · exact ⟨h'.1.1.1, le_sup_left.trans h'.1.1.2, h'.2⟩
    · exact absurd rfl hv
  by_cases h1 : divCycle P s W = 0
  · exact key h fun h2 => hW (by simp [ratDiv, h1, h2])
  · exact key s h1

end SegreFlagCutLiesOverProof


open SegreFlagCutLiesOverProof in
theorem SegreFlagCutLiesOver.proof (hChart : SegreFlagCutChartSection.Statement) :
    SegreFlagCutLiesOver.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk
  have hchart : ∀ (s h : MRing (bundleIdx (bundleIdx ι M) M') O) (W : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)),
      ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
      ∃ c : ∀ j, ι j, segreVec y c ≠ 0 ∧ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ W ∧
        ∀ m : K → ℕ, (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O) ^ m j) ∉ W := by
    intro s h W hW
    obtain ⟨hWp, hPW, hWr⟩ := support_ratDiv hW
    choose c hc using fun j : K => hWr (some (some j))
    refine ⟨c, ?_, hPW, ?_⟩
    · unfold segreVec
      rw [Finset.prod_ne_zero_iff]
      intro j _ hj
      apply hc j (hPW ?_)
      refine GenericProjClosureDivisor.mem_of_homog (isWeightedHomogeneous_X O _ _) ?_
      rw [aeval_X]
      simp [flagClosurePt, pairProjCoord, projCoord, hj]
    · intro m hm
      obtain ⟨j, -, hj⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hWp)).mp hm
      exact hc j (hWp.mem_of_pow_mem _ hj)
  have hdeg : ∀ {cs ch dl dm : Option (Option K) → ℕ} {D : Option (Option K) → ℤ},
      (fun o => (cs o : ℤ) - ch o) = D → (fun o => (dl o : ℤ) - dm o) = D → cs + dm = dl + ch := by
    intro cs ch dl dm D h1 h2
    funext o
    have e1 := congrFun h1 o
    have e2 := congrFun h2 o
    simp only [Pi.add_apply] at e1 e2 ⊢
    omega
  refine ⟨fun cs ch s h hs hh hsh hsP hhP hsv W _ hW => ?_, fun cs ch s h hs hh hsh hsP hhP hsv W _ hW => ?_⟩
  · obtain ⟨c, hc, hPW, hmono⟩ := hchart s h W hW
    obtain ⟨⟨dl, dm, l, μ, m, hμ, hl, hμh, hdl, hlv, hsat⟩, -⟩ :=
      hChart O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk c hc
    exact le_comap_of_chart _ _ _ _ _ hs hh hl hμh (hdeg hsh hdl) hsP hhP hsv hlv hsat (hμ ▸ hmono m)
      (fun n => by rw [← Finset.prod_pow]; exact hmono fun _ => n) hPW hW
  · obtain ⟨c, hc, hPW, hmono⟩ := hchart s h W hW
    obtain ⟨-, ⟨dl, dm, l, μ, m, hμ, hl, hμh, hdl, hlv, hsat⟩⟩ :=
      hChart O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk c hc
    exact le_comap_of_chart _ _ _ _ _ hs hh hl hμh (hdeg hsh hdl) hsP hhP hsv hlv hsat (hμ ▸ hmono m)
      (fun n => by rw [← Finset.prod_pow]; exact hmono fun _ => n) hPW hW

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSegreFlagCutLiesOverX

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

theorem SegreFlagCutLiesOver.closed : SegreFlagCutLiesOver.Statement :=
  SegreFlagCutLiesOver.proof SegreFlagCutChartSection.proof

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHeckeCorrespondenceOnIntegralShimuraModel

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.CommAlg.SegreFlag

open GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.AutoClose

theorem segreFlagClosureCut : SegreFlagClosureCut.Statement :=
  SegreFlagClosureCut.proof GlobalTheory.T.cut_effective_divisor
    (PairNumberExpansionIndependence.proof GlobalTheory.T.vertical_divisors_commute)
    NumbersDVR_SegreFlagClosureModel
    (SegreFlagCutSection.proof NumbersDVR_SegreFlagClosureModel
      SegreFlagCutForms.proof SegreFlagCutDivisor.closed segre_flag_degree_zero_holds)
    (SegreFlagCutContraction.proof NumbersDVR_SegreFlagClosureModel
      (SegreFlagCutProjection.proof SegreFlagCutLiesOver.closed NumbersDVR_SegreFlagProjSpecialDim))

end GlobalTheory.CompanionTheory.CommAlg.SegreFlag
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHeckeCorrespondenceOnIntegralShimuraModelStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_heckeCorrespondence_on_integral_shimuraModel : GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureCut.Statement := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.SegreFlag.segreFlagClosureCut | exact GlobalTheory.CompanionTheory.CommAlg.SegreFlag.segreFlagClosureCut | (intros; apply GlobalTheory.CompanionTheory.CommAlg.SegreFlag.segreFlagClosureCut <;> assumption)
end
end
