module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentValuationFibre
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalDivisorJoinPullback

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagFrameBaseExtension

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullFlagFrame

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)

theorem tri_solve {F : Type} [Field F] {N : ℕ} (T : Fin N → Fin N → F) (a : Fin N → F)
    (hT : ∀ j l, j < l → T j l = 0) (hd : ∀ j, T j j ≠ 0) (i : Fin N)
    (h : ∀ l, i < l → ∑ j, a j * T j l = 0) : ∀ j, i < j → a j = 0 := by
  classical
  by_contra hne
  push_neg at hne
  obtain ⟨j₀, hj₀, ha₀⟩ := hne
  let S := Finset.univ.filter (fun j => i < j ∧ a j ≠ 0)
  have hS : S.Nonempty := ⟨j₀, by simp [S, hj₀, ha₀]⟩
  have hm : S.max' hS ∈ S := S.max'_mem hS
  obtain ⟨m, hmd⟩ : ∃ m, m = S.max' hS := ⟨_, rfl⟩
  rw [← hmd] at hm
  have hm' : i < m ∧ a m ≠ 0 := by simpa [S] using hm
  have hsum := h m hm'.1
  rw [Finset.sum_eq_single m] at hsum
  · exact mul_ne_zero hm'.2 (hd m) hsum
  · intro j _ hjm
    rcases lt_or_gt_of_ne hjm with hlt | hgt
    · rw [hT j m hlt, mul_zero]
    · have hz : a j = 0 := by
        by_contra hz
        have hjS : j ∈ S := by simp [S, hz, hm'.1.trans hgt]
        have := S.le_max' j hjS
        rw [← hmd] at this
        exact absurd this (not_le.2 hgt)
      rw [hz, zero_mul]
  · simp

section BC

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω₁ : Type} [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem mseg_bcCoord (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (bcCoord x z) s =
      algebraMap Ω Ω₁ (mseg x (restrictChart s)) * ∏ k, z ⟨k, s (.inr k)⟩ := by
  simp [mseg, Fintype.prod_sum_type, bcCoord, joinCoord, restrictChart, map_prod]

theorem map_mem_chartRing_bc (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (bcCoord x z) s ≠ 0) {a : Ω}
    (ha : a ∈ chartRing O (mseg x) (restrictChart s)) :
    algebraMap Ω Ω₁ a ∈ chartRing O (mseg (bcCoord x z)) s := by
  have hZ : (∏ k, z ⟨k, s (.inr k)⟩) ≠ 0 := by
    intro h0
    exact hs (by rw [mseg_bcCoord, h0, mul_zero])
  induction ha using Algebra.adjoin_induction with
  | mem t ht =>
    obtain ⟨j, rfl⟩ := ht
    let j' : ∀ k : K ⊕ K', Sum.elim ι ι' k := fun k =>
      match k with
      | .inl k => j k
      | .inr k => s (.inr k)
    have hj : restrictChart j' = j := rfl
    have hz : (∏ k, z ⟨k, j' (.inr k)⟩) = ∏ k, z ⟨k, s (.inr k)⟩ := rfl
    have e : algebraMap Ω Ω₁ (mseg x j / mseg x (restrictChart s)) =
        mseg (bcCoord x z) j' / mseg (bcCoord x z) s := by
      rw [mseg_bcCoord, mseg_bcCoord, hj, hz, map_div₀, mul_div_mul_right _ _ hZ]
    rw [e]
    exact Algebra.subset_adjoin ⟨j', rfl⟩
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply O Ω Ω₁]
    exact Subalgebra.algebraMap_mem _ r
  | add s t _ _ hs ht => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hs ht
  | mul s t _ _ hs ht => rw [map_mul]; exact Subalgebra.mul_mem _ hs ht

variable {N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]
  {V₁ : Type} [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁]

theorem repr_bc (bc : V →ₗ[Ω] V₁) (w : Module.Basis (Fin N) Ω V) (w₁ : Module.Basis (Fin N) Ω₁ V₁)
    (hw : ∀ i, w₁ i = bc (w i)) (e : V) (j : Fin N) :
    w₁.repr (bc e) j = algebraMap Ω Ω₁ (w.repr e j) := by
  have h1 : bc e = ∑ i, algebraMap Ω Ω₁ (w.repr e i) • w₁ i := by
    conv_lhs => rw [← w.sum_repr e]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hw, algebraMap_smul]

  rw [h1, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
      mul_one]
  · intro i _ hij
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg hij,
      smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem isFlagFrame_bc (x : (Σ k, ι k) → Ω) (E : ChartBundle O (mseg x) N V)
    (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ) (h : IsFlagFrame x E w b)
    (z : (Σ k, ι' k) → Ω₁) (bc : V →ₗ[Ω] V₁) (w₁ : Module.Basis (Fin N) Ω₁ V₁)
    (hw : ∀ i, w₁ i = bc (w i)) (EB : ChartBundle O (mseg (bcCoord x z)) N V₁)
    (hp : IsPullBC O x z bc E EB) :
    IsFlagFrame (bcCoord x z) EB w₁ (fun i => pullDeg (K' := K') (b i)) := by
  classical
  refine ⟨fun s hs0 i => ?_⟩
  have hs : mseg (bcCoord x z) s ≠ 0 := hs0
  have hc : mseg x (restrictChart s) ≠ 0 := by
    intro h0
    exact hs (by rw [mseg_bcCoord, h0, map_zero, zero_mul])
  obtain ⟨u, hu, hup, hdiag, hgen⟩ :=
    FlagPairExt.exists_frame x E w b h (restrictChart s) hc
  have hx : ∀ k, x ⟨k, restrictChart s k⟩ ≠ 0 := fun k =>
    (Finset.prod_ne_zero_iff.1 hc) k (Finset.mem_univ k)
  have hM : ∀ i, (∏ k, x ⟨k, restrictChart s k⟩ ^ b i k) ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hx k)
  have hMon : (∏ k : K ⊕ K', (bcCoord x z) ⟨k, s k⟩ ^ pullDeg (K' := K') (b i) k) =
      algebraMap Ω Ω₁ (∏ k, x ⟨k, restrictChart s k⟩ ^ b i k) := by
    rw [Fintype.prod_sum_type]
    simp [pullDeg, bcCoord, joinCoord, restrictChart, map_prod, map_zpow₀]
  have hbu : ∀ j, bc (u j) ∈ EB.lat s := by
    intro j
    rw [hp s hs]
    exact AddSubgroup.subset_closure ⟨1, Subalgebra.one_mem _, u j, hu j, (one_smul _ _).symm⟩
  have hgenL : ∀ v ∈ EB.lat s, ∃ a : Fin N → Ω₁,
      (∀ j, a j ∈ chartRing O (mseg (bcCoord x z)) s) ∧ v = ∑ j, a j • bc (u j) := by
    intro v hv
    rw [hp s hs] at hv
    induction hv using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨a, ha, e, he, rfl⟩ := hv
      obtain ⟨t, ht, rfl⟩ := hgen e he
      refine ⟨fun j => a * algebraMap Ω Ω₁ (t j), fun j =>
        Subalgebra.mul_mem _ ha (map_mem_chartRing_bc x z s hs (ht j)), ?_⟩

      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← algebraMap_smul Ω₁ (t j), smul_smul]
    | zero => exact ⟨0, fun _ => Subalgebra.zero_mem _, by simp⟩
    | add v v' _ _ hv hv' =>
      obtain ⟨a, ha, rfl⟩ := hv
      obtain ⟨a', ha', rfl⟩ := hv'
      exact ⟨a + a', fun j => Subalgebra.add_mem _ (ha j) (ha' j), by
        simp [add_smul, Finset.sum_add_distrib]⟩
    | neg v _ hv =>
      obtain ⟨a, ha, rfl⟩ := hv
      exact ⟨-a, fun j => Subalgebra.neg_mem _ (ha j), by simp [Finset.sum_neg_distrib]⟩
  ext t
  constructor
  · rintro ⟨v, hv, htri, rfl⟩
    obtain ⟨a, ha, hav⟩ := hgenL v hv
    let T : Fin N → Fin N → Ω₁ := fun j l => algebraMap Ω Ω₁ (w.repr (u j) l)
    have hrepr : ∀ l, w₁.repr v l = ∑ j, a j * T j l := by
      intro l
      rw [hav]

      simp [T, map_sum, repr_bc bc w w₁ hw]
    have hT : ∀ j l, j < l → T j l = 0 := fun j l hjl => by simp [T, hup j l hjl]
    have hd : ∀ j, T j j ≠ 0 := fun j => by
      simp only [T, hdiag j]
      exact (map_ne_zero _).2 (hM j)
    have hz := tri_solve T a hT hd i fun l hl => by rw [← hrepr l]; exact htri l hl
    refine ⟨a i, ha i, ?_⟩
    rw [hrepr i, Finset.sum_eq_single i]
    · show a i * T i i = _
      rw [hMon]
      simp only [T, hdiag i]
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · rw [hT j i hlt, mul_zero]
      · rw [hz j hgt, zero_mul]
    · simp
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a • bc (u i), EB.stable s a ha _ (hbu i), fun j hj => ?_, ?_⟩
    · simp [repr_bc bc w w₁ hw, hup i j hj]
    · rw [hMon]
      simp [repr_bc bc w w₁ hw, hdiag i]

end BC

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V) (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b → (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsFlagFrame (joinCoord x z) EB w (fun i => pullDeg (K' := K') (b i))) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁) (w₁ : Module.Basis (Fin N) Ω₁ V₁), (∀ i, w₁ i = bc (w i)) → ∀ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB → IsFlagFrame (bcCoord x z) EB w₁ (fun i => pullDeg (K' := K') (b i)) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E w b h
  refine ⟨?_, ?_⟩
  · intro K' _ _ ι' _ z EB hp
    exact isFlagFrame_bc (Ω₁ := Ω) (V₁ := V) x E w b h z LinearMap.id w (fun _ => rfl) EB hp
  · intro Ω₁ _ _ _ _ K' _ _ ι' _ z V₁ _ _ _ _ bc w₁ hw EB hp
    exact isFlagFrame_bc x E w b h z bc w₁ hw EB hp

end GlobalTheory.CompanionTheory.Ar.Num.PullFlagFrame
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagFrameBaseExtensionStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.flag_frame_base_extension : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V) (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b → (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsFlagFrame (joinCoord x z) EB w (fun i => pullDeg (K' := K') (b i))) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁) (w₁ : Module.Basis (Fin N) Ω₁ V₁), (∀ i, w₁ i = bc (w i)) → ∀ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB → IsFlagFrame (bcCoord x z) EB w₁ (fun i => pullDeg (K' := K') (b i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PullFlagFrame.main | exact GlobalTheory.CompanionTheory.Ar.Num.PullFlagFrame.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PullFlagFrame.main <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPullFlagpair

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_pull_flagpair

theorem joinCoord_eq {K K' : Type} {ι : K → Type} {ι' : K' → Type} {Ω : Type} [Field Ω]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) : joinCoord x z = joinCoords x z := by
  funext p
  rcases p with ⟨k | k, i⟩ <;> rfl

theorem pullDeg_sub {K K' : Type} (b b' : K → ℤ) :
    pullDeg (K' := K') b - pullDeg (K' := K') b' = joinDeg (K' := K') (b - b') := by
  funext s
  rcases s with k | k <;> simp [pullDeg, joinDeg]

theorem pointIdeal_algebraMap {K : Type} {ι : K → Type} (O : Type) [CommRing O] {Ω Ω₁ : Type}
    [Field Ω] [Field Ω₁] [Algebra O Ω] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁]
    (x : (Σ k, ι k) → Ω) :
    pointIdeal O (fun p => algebraMap Ω Ω₁ (x p)) = pointIdeal O x := by
  have key : ∀ f : MRing ι O, pointConeMap O (fun p => algebraMap Ω Ω₁ (x p)) f =
      MvPolynomial.map (algebraMap Ω Ω₁) (pointConeMap O x f) := by
    intro f
    simp only [pointConeMap]
    induction f using MvPolynomial.induction_on with
    | C a => simp [IsScalarTower.algebraMap_apply O Ω Ω₁]
    | add p q hp hq => simp [hp, hq]
    | mul_X p v hp => simp [hp]
  ext f
  simp only [pointIdeal, RingHom.mem_ker, key]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective _ (algebraMap Ω Ω₁).injective)

theorem vertical_join (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] [DecidableEq K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (b b' : K → ℤ) (f g : MRing ι O)
    (h : IsVerticalDivisor (pointIdeal O x) ϖ (b - b') f g) :
    IsVerticalDivisor (pointIdeal O (joinCoord x z)) ϖ
      (pullDeg (K' := K') b - pullDeg (K' := K') b') (rename (liftVar ι') f) (rename (liftVar ι') g) := by
  rw [joinCoord_eq, pullDeg_sub]
  exact VerticalDivisorJoinPullback.proof O ϖ Ω K ι K' ι' x z (b - b') f g h

theorem aeval_join {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    {K K' : Type} {ι : K → Type} {ι' : K' → Type}
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (f : MRing ι O) :
    aeval (joinCoord x z) (rename (liftVar ι') f) = aeval x f := by
  rw [aeval_rename]
  rfl

theorem repr_bc {Ω Ω₁ : Type} [Field Ω] [Field Ω₁] [Algebra Ω Ω₁] {N : ℕ}
    {V : Type} [AddCommGroup V] [Module Ω V]
    {V₁ : Type} [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁]
    (bc : V →ₗ[Ω] V₁) (w : Module.Basis (Fin N) Ω V) (w₁ : Module.Basis (Fin N) Ω₁ V₁)
    (hw : ∀ i, w₁ i = bc (w i)) (v : V) (j : Fin N) :
    w₁.repr (bc v) j = algebraMap Ω Ω₁ (w.repr v j) := by
  have h : bc v = ∑ i, algebraMap Ω Ω₁ (w.repr v i) • w₁ i := by

    conv_lhs => rw [← w.sum_repr v, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hw, algebraMap_smul]
  rw [h, w₁.repr_sum_self]

end PositivityTheory.Xgn.A_pull_flagpair

open PositivityTheory.Xgn.A_pull_flagpair in
theorem PositivityTheory.Xgn.t_pull_flagpair : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K → ℤ) (f g : Fin N → MRing ι O), IsFlagPair ϖ x E E' w w' b b' f g → (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → IsFlagPair ϖ (joinCoord x z) EB E'B w w' (fun i => pullDeg (K' := K') (b i)) (fun i => pullDeg (K' := K') (b' i)) (fun i => rename (liftVar ι') (f i)) (fun i => rename (liftVar ι') (g i))) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁) (w₁ w₁' : Module.Basis (Fin N) Ω₁ V₁), (∀ i, w₁ i = bc (w i)) → (∀ i, w₁' i = bc (w' i)) → ∀ EB E'B : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB → IsPullBC O x z bc E' E'B → IsFlagPair ϖ (bcCoord x z) EB E'B w₁ w₁' (fun i => pullDeg (K' := K') (b i)) (fun i => pullDeg (K' := K') (b' i)) (fun i => rename (liftVar ι') (f i)) (fun i => rename (liftVar ι') (g i)) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ N V _ _ E E' w w' b b' f g h
  obtain ⟨h1, h1'⟩ := GlobalTheory.T.flag_frame_base_extension O Ω K ι x N V E w b h.flag
  obtain ⟨h2, h2'⟩ := GlobalTheory.T.flag_frame_base_extension O Ω K ι x N V E' w' b' h.flag'
  refine ⟨?_, ?_⟩
  · intro K' _ _ ι' _ z EB E'B hE hE'
    refine ⟨h1 K' ι' z EB hE, h2 K' ι' z E'B hE', h.sameFlag, fun i => ?_, fun i => ?_⟩
    · exact vertical_join O ϖ x z _ _ _ _ (h.vertical i)
    · rw [aeval_join, aeval_join]
      exact h.generic i
  · intro Ω₁ _ _ _ _ K' _ _ ι' _ z V₁ _ _ _ _ bc w₁ w₁' hw hw' EB E'B hE hE'
    refine ⟨h1' Ω₁ K' ι' z V₁ bc w₁ hw EB hE, h2' Ω₁ K' ι' z V₁ bc w₁' hw' E'B hE',
      fun i j hij => ?_, fun i => ?_, fun i => ?_⟩
    · rw [hw', repr_bc bc w w₁ hw, h.sameFlag i j hij, map_zero]
    · refine vertical_join O ϖ _ z _ _ _ _ ?_
      rw [pointIdeal_algebraMap]
      exact h.vertical i
    · unfold bcCoord
      have e : ∀ p : MRing ι O, aeval (fun q => algebraMap Ω Ω₁ (x q)) p =
          algebraMap Ω Ω₁ (aeval x p) := fun p => aeval_algebraMap_apply Ω₁ x p
      rw [aeval_join, aeval_join, hw', repr_bc bc w w₁ hw, e, e, h.generic i, map_mul]
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagPairBaseExtension

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullFlagPair

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K → ℤ) (f g : Fin N → MRing ι O), IsFlagPair ϖ x E E' w w' b b' f g → (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → IsFlagPair ϖ (joinCoord x z) EB E'B w w' (fun i => pullDeg (K' := K') (b i)) (fun i => pullDeg (K' := K') (b' i)) (fun i => rename (liftVar ι') (f i)) (fun i => rename (liftVar ι') (g i))) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁) (w₁ w₁' : Module.Basis (Fin N) Ω₁ V₁), (∀ i, w₁ i = bc (w i)) → (∀ i, w₁' i = bc (w' i)) → ∀ EB E'B : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB → IsPullBC O x z bc E' E'B → IsFlagPair ϖ (bcCoord x z) EB E'B w₁ w₁' (fun i => pullDeg (K' := K') (b i)) (fun i => pullDeg (K' := K') (b' i)) (fun i => rename (liftVar ι') (f i)) (fun i => rename (liftVar ι') (g i)) :=
  PositivityTheory.Xgn.t_pull_flagpair

end GlobalTheory.CompanionTheory.Ar.Num.PullFlagPair
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagPairBaseExtensionStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.flag_pair_base_extension : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K → ℤ) (f g : Fin N → MRing ι O), IsFlagPair ϖ x E E' w w' b b' f g → (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → IsFlagPair ϖ (joinCoord x z) EB E'B w w' (fun i => pullDeg (K' := K') (b i)) (fun i => pullDeg (K' := K') (b' i)) (fun i => rename (liftVar ι') (f i)) (fun i => rename (liftVar ι') (g i))) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁) (w₁ w₁' : Module.Basis (Fin N) Ω₁ V₁), (∀ i, w₁ i = bc (w i)) → (∀ i, w₁' i = bc (w' i)) → ∀ EB E'B : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB → IsPullBC O x z bc E' E'B → IsFlagPair ϖ (bcCoord x z) EB E'B w₁ w₁' (fun i => pullDeg (K' := K') (b i)) (fun i => pullDeg (K' := K') (b' i)) (fun i => rename (liftVar ι') (f i)) (fun i => rename (liftVar ι') (g i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PullFlagPair.main | exact GlobalTheory.CompanionTheory.Ar.Num.PullFlagPair.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PullFlagPair.main <;> assumption)
end
end
