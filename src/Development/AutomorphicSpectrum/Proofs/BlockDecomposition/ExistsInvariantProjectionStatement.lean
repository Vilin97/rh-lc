module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrableSmoothSubmoduleGL
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Topology.Algebra.ConstMulAction
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply

section

section

noncomputable section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil

namespace GlobalTheory.RankFibreKer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def tw (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g : GL (Fin a) k) : ℂ :=
  (ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)

def minor {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) : k := (Y.submatrix id J).det

def idx {a d : ℕ} : (Fin a ↪ Fin d) ≃ Fin (Fintype.card (Fin a ↪ Fin d)) := Fintype.equivFin _


variable (k) in
def slice (a d : ℕ) : Set (Matrix (Fin a) (Fin d) k) :=
  {Z | ∃ J : Fin a ↪ Fin d, Z.submatrix id J = 1 ∧ ∀ J' : Fin a ↪ Fin d,
    valuation k (minor Z J') ≤ 1 ∧ (idx J' < idx J → valuation k (minor Z J') < 1)}

def IsFirstMax {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) : Prop :=
  minor Y J ≠ 0 ∧ ∀ J' : Fin a ↪ Fin d, valuation k (minor Y J') ≤ valuation k (minor Y J) ∧
    (idx J' < idx J → valuation k (minor Y J') < valuation k (minor Y J))


open Classical in
def sec {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) : GL (Fin a) k := by
  classical
  exact if h : ∃ J, IsFirstMax Y J then
    GeneralLinearGroup.mkOfDetNeZero (Y.submatrix id h.choose) h.choose_spec.1
  else 1

theorem tw_mul (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g x : GL (Fin a) k) : tw ν d (g * x) = tw ν d g * tw ν d x := by
  simp only [tw, gdet_mul, map_mul, Units.val_mul, apow_mul]; ring

theorem tw_ne_zero (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g : GL (Fin a) k) : tw ν d g ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)

theorem omA_one_apply (ν β : kˣ →* ℂˣ) {a b : ℕ} (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin (a + b)) k → ℂ)
    (Y : Matrix (Fin a) (Fin (a + b)) k) : omA ν β g 1 Ψ Y = (tw ν (a + b) g)⁻¹ * Ψ ((g⁻¹).val * Y) := by
  have e : apow (gdet g) (-(((a + b : ℕ)) : ℂ) / 2) = (apow (gdet g) (((a + b : ℕ) : ℂ) / 2))⁻¹ := by
    rw [neg_div, apow_neg]
  simp only [omA, tw, Fintype.card_fin, e, map_one, Units.val_one, apow_one, mul_one, invT_val, inv_one,
    transpose_one, Units.val_inv_eq_inv_val, mul_inv, Matrix.mul_one]

theorem minor_mul {a d : ℕ} (g : Matrix (Fin a) (Fin a) k) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) :
    minor (g * Y) J = g.det * minor Y J := by
  rw [minor, minor, ← det_mul]
  congr 1

end GlobalTheory.RankFibreKer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCoveredByOpenCosets

section

@[expose] public section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory

open scoped Pointwise

theorem compact_finite_leftCoset_reps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    ∀ C : Set G, IsCompact C →
    ∃ R : Finset G, (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') ∧ ∀ g ∈ C, ∃ r ∈ R, r⁻¹ * g ∈ K := by
  intro G _ _ _ K hK C hC
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun g : G => g • (K : Set G)) (fun g => hK.smul g)
    (fun x _ => Set.mem_iUnion.2 ⟨x, Set.mem_smul_set.2 ⟨1, K.one_mem, by simp⟩⟩)
  refine ⟨(t.image (fun g => (QuotientGroup.mk g : G ⧸ K))).image Quotient.out, ?_, ?_⟩
  · intro r hr r' hr' hrr'
    simp only [Finset.mem_image] at hr hr'
    obtain ⟨a, -, rfl⟩ := hr
    obtain ⟨b, -, rfl⟩ := hr'
    have h : (QuotientGroup.mk (Quotient.out a) : G ⧸ K) = QuotientGroup.mk (Quotient.out b) :=
      QuotientGroup.eq.2 hrr'
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h
    rw [h]
  · intro g hg
    have hm := ht hg
    simp only [Set.mem_iUnion] at hm
    obtain ⟨gi, hgi, hmem⟩ := hm
    obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hmem
    refine ⟨Quotient.out (QuotientGroup.mk gi : G ⧸ K),
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hgi), ?_⟩
    have h1 : (Quotient.out (QuotientGroup.mk gi : G ⧸ K))⁻¹ * gi ∈ K :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    simpa [smul_eq_mul, mul_assoc] using K.mul_mem h1 hk

end GlobalTheory
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantProjection

section

@[expose] public section

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDiscAvg

theorem exists_sum_fixed {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [AddCommGroup W] [Module ℂ W] (ρ : G →* Module.End ℂ W) (x : W) (ho : IsOpen {k | ρ k x = x}) :
    ∃ R : Finset G, R.Nonempty ∧ ∀ u, ρ u (∑ r ∈ R, ρ r x) = ∑ r ∈ R, ρ r x := by
  let K : Subgroup G :=
    { carrier := {k | ρ k x = x}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h : ρ a⁻¹ (ρ a x) = x := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [ha] at h }
  have hK : ∀ k, k ∈ K ↔ ρ k x = x := fun _ => Iff.rfl
  obtain ⟨R, hR, hc⟩ := GlobalTheory.compact_finite_leftCoset_reps G K ho Set.univ isCompact_univ
  have hc' : ∀ g : G, ∃ r ∈ R, r⁻¹ * g ∈ K := fun g => hc g (Set.mem_univ g)
  have hne : R.Nonempty := by
    obtain ⟨r, hr, -⟩ := hc' 1
    exact ⟨r, hr⟩
  refine ⟨R, hne, fun u => ?_⟩
  choose! σ hσR hσ using fun r : G => hc' (u * r)
  have hval : ∀ r, ρ (u * r) x = ρ (σ r) x := by
    intro r
    have h := (hK _).1 (hσ r)
    have e : u * r = σ r * ((σ r)⁻¹ * (u * r)) := by group
    rw [e, map_mul, Module.End.mul_apply, h]
  have hinj : Set.InjOn σ R := by
    intro r hr r' hr' e
    refine hR r hr r' hr' ?_
    have h1 := hσ r
    have h2 := hσ r'
    rw [show σ r = σ r' from e] at h1
    have := K.mul_mem (K.inv_mem h1) h2
    have e2 : ((σ r')⁻¹ * (u * r))⁻¹ * ((σ r')⁻¹ * (u * r')) = r⁻¹ * r' := by group
    rwa [e2] at this
  have himg : R.image σ = R := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro s hs
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hs
      exact hσR r
    · rw [Finset.card_image_of_injOn hinj]
  calc ρ u (∑ r ∈ R, ρ r x) = ∑ r ∈ R, ρ (σ r) x := by

        rw [map_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [← hval, map_mul, Module.End.mul_apply]
    _ = ∑ s ∈ R.image σ, ρ s x := (Finset.sum_image (f := fun s => ρ s x) hinj).symm
    _ = ∑ r ∈ R, ρ r x := by rw [himg]

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem l2Map_right_translate (k : GL (Fin N) (Af E)) {a : Sm E N} (ha : a ∈ squareIntegrableSmoothSubmoduleGL μ) (hb : finRep E N k a ∈ squareIntegrableSmoothSubmoduleGL μ) :
    l2Map μ (finRep E N k a) = R (latticeGL E N) μ (finGL E N k) (l2Map μ a) := by
  rw [l2Map_apply μ ha, l2Map_apply μ hb, right_translate_toL2]
  rfl

theorem inner_R (g : GA E N) (u v : L2 (latticeGL E N) μ) :
    ⟪R (latticeGL E N) μ g u, R (latticeGL E N) μ g v⟫_ℂ = ⟪u, v⟫_ℂ := by
  let T : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ :=
    ⟨(R (latticeGL E N) μ g : L2 (latticeGL E N) μ →L[ℂ] L2 (latticeGL E N) μ).toLinearMap, norm_R g⟩
  exact T.inner_map_map u v

theorem exists_avg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ L : Subgroup (GL (Fin N) (Af E)), IsCompact (L : Set (GL (Fin N) (Af E))) → ∀ x ∈ V, ∃ x' ∈ V, (∀ u ∈ L, finRep E N u x' = x') ∧ ∀ y : Sm E N, y ∈ squareIntegrableSmoothSubmoduleGL μ → (∀ u ∈ L, finRep E N u y = y) → ⟪l2Map μ x, l2Map μ y⟫_ℂ = ⟪l2Map μ x', l2Map μ y⟫_ℂ := by
  intro E _ _ _ N μ _ _ V hV L hL x hx
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL
  let ρ : L →* Module.End ℂ (Sm E N) := (finRep E N).comp L.subtype
  have hρ : ∀ l : L, ρ l = finRep E N (l : GL (Fin N) (Af E)) := fun _ => rfl
  have ho : IsOpen {k : L | ρ k x = x} :=
    (hV.aut x hx).level.preimage continuous_subtype_val
  obtain ⟨S, hS, hfix⟩ := exists_sum_fixed ρ x ho
  have hn : ((S.card : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hS.card_pos.ne'
  have hmem : ∀ l : L, ρ l x ∈ V := fun l => hV.stable (.fin _) x hx
  refine ⟨(S.card : ℂ)⁻¹ • ∑ r ∈ S, ρ r x, V.smul_mem _ (V.sum_mem fun r _ => hmem r), ?_, ?_⟩
  · intro u hu
    rw [map_smul, ← hρ ⟨u, hu⟩ , hfix]
  · intro y hy hyL
    have hl2 : ∀ z ∈ V, z ∈ squareIntegrableSmoothSubmoduleGL μ := fun z hz => mem_l2Sub_of_isAutForm μ (hV.aut z hz) (hV.sqInt z hz)
    have hxl := hl2 x hx
    have key : ∀ r : L, ⟪l2Map μ (ρ r x), l2Map μ y⟫_ℂ = ⟪l2Map μ x, l2Map μ y⟫_ℂ := by
      intro r
      have e1 := l2Map_right_translate μ (r : GL (Fin N) (Af E)) hxl (hl2 _ (hmem r))
      have e2 := l2Map_right_translate μ (r : GL (Fin N) (Af E)) hy (by rw [hyL _ r.2]; exact hy)
      rw [hyL _ r.2] at e2
      rw [hρ, e1]
      conv_lhs => rw [e2]
      exact inner_R μ _ _ _

    rw [map_smul, map_sum, inner_smul_left, sum_inner, Finset.sum_congr rfl fun r _ => key r,
    Finset.sum_const, nsmul_eq_mul, map_inv₀, Complex.conj_natCast, inv_mul_cancel_left₀ hn]

end GlobalTheory.CompanionTheory.FinDiscAvg

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantProjectionStatement

section

@[expose] public section

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.exists_invariant_projection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ L : Subgroup (GL (Fin N) (Af E)), IsCompact (L : Set (GL (Fin N) (Af E))) → ∀ x ∈ V, ∃ x' ∈ V, (∀ u ∈ L, finRep E N u x' = x') ∧ ∀ y : Sm E N, y ∈ squareIntegrableSmoothSubmoduleGL μ → (∀ u ∈ L, finRep E N u y = y) → ⟪l2Map μ x, l2Map μ y⟫_ℂ = ⟪l2Map μ x', l2Map μ y⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscAvg.exists_avg | exact GlobalTheory.CompanionTheory.FinDiscAvg.exists_avg | (intros; apply GlobalTheory.CompanionTheory.FinDiscAvg.exists_avg <;> assumption)
end
end
