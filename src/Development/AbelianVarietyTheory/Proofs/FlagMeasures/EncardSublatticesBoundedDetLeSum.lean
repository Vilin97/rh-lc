module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLatticeDiscriminantModuleCardDetSq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
public import Formalism.HermitianLattices.StatementMass
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSquareIdxNOfCovBy
public import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Mathlib.Algebra.Order.Star.Real

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSquareCardOfInvolution

section

@[expose] public section

set_option autoImplicit false

namespace GlobalTheory.InertSquareNorm

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S.Lat
open scoped Classical

theorem isSquare_card_of_involution {k : Type} [Field k] [Finite k] (s : k ≃+* k)
    (hs : ∀ x, s (s x) = x) (h1 : ∃ x, s x ≠ x) : IsSquare (Nat.card k) := by
  classical
  have hs2 : s ^ 2 = 1 := by
    ext x
    simp [pow_two, hs]
  have hs1 : s ≠ 1 := by
    obtain ⟨x, hx⟩ := h1
    intro h
    exact hx (by rw [h]; rfl)
  have hord : orderOf s = 2 := orderOf_eq_prime hs2 hs1

  haveI : Finite (k ≃+* k) := Finite.of_injective (fun f : k ≃+* k => (f : k → k))
    (fun a b h => RingEquiv.ext (congrFun h))
  haveI : Fintype (Subgroup.zpowers s) := Fintype.ofFinite _
  haveI : FaithfulSMul (Subgroup.zpowers s) k :=
    ⟨fun {g₁ g₂} h => Subtype.ext (RingEquiv.ext h)⟩
  have hcardG : Fintype.card (Subgroup.zpowers s) = 2 := by
    rw [Fintype.card_eq_nat_card]
    exact (Nat.card_zpowers s).trans hord
  have hfin : Module.finrank (FixedPoints.subfield (Subgroup.zpowers s) k) k = 2 :=
    (FixedPoints.finrank_eq_card (Subgroup.zpowers s) k).trans hcardG
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype (FixedPoints.subfield (Subgroup.zpowers s) k) := Fintype.ofFinite _
  have hk : Fintype.card k = Fintype.card (FixedPoints.subfield (Subgroup.zpowers s) k) ^
      Module.finrank (FixedPoints.subfield (Subgroup.zpowers s) k) k :=
    Module.card_eq_pow_finrank
  refine ⟨Fintype.card (FixedPoints.subfield (Subgroup.zpowers s) k), ?_⟩
  rw [Nat.card_eq_fintype_card, hk, hfin, pow_two]

theorem isSquare_absNorm : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ P : HeightOneSpectrum (𝓞 E), Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = P.asIdeal → IsSquare (Ideal.absNorm P.asIdeal) := by
  intro E _ _ _ hE P hP
  classical

  let c : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)
  have hc : ∀ x : 𝓞 E, algebraMap (𝓞 E) E (c x) = star (algebraMap (𝓞 E) E x) := fun x => rfl
  have hcc : ∀ x : 𝓞 E, c (c x) = x := fun x => RingOfIntegers.ext (by simp [c])

  have hle : P.asIdeal ≤ P.asIdeal.comap c := by
    intro x hx
    rw [Ideal.mem_comap, ← hP]
    exact Ideal.subset_span ⟨x, hx, hc x⟩
  haveI hmax : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  let sb : (𝓞 E ⧸ P.asIdeal) →+* (𝓞 E ⧸ P.asIdeal) := Ideal.quotientMap P.asIdeal c hle
  have hsb_mk : ∀ x : 𝓞 E, sb (Ideal.Quotient.mk P.asIdeal x) = Ideal.Quotient.mk P.asIdeal (c x) :=
    fun x => Ideal.quotientMap_mk
  have hsb : ∀ y, sb (sb y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hsb_mk, hsb_mk, hcc]
  let s : (𝓞 E ⧸ P.asIdeal) ≃+* (𝓞 E ⧸ P.asIdeal) :=
    { sb with invFun := sb, left_inv := hsb, right_inv := hsb }
  have hN : Ideal.absNorm P.asIdeal = Nat.card (𝓞 E ⧸ P.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := by
    apply Nat.finite_of_card_ne_zero
    rw [← hN]
    exact fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)

  obtain ⟨θ, t, ht, hθ⟩ := hE.2.2 P.asIdeal P.isMaximal
  have htc : t = c θ := FaithfulSMul.algebraMap_injective (𝓞 E) E (ht.trans (hc θ).symm)
  rw [hN]
  refine isSquare_card_of_involution s hsb ⟨Ideal.Quotient.mk P.asIdeal θ, fun h => hθ ?_⟩
  have h2 : Ideal.Quotient.mk P.asIdeal θ = Ideal.Quotient.mk P.asIdeal t := by
    rw [htc, ← hsb_mk]
    exact h.symm
  exact Ideal.Quotient.eq.mp h2

end GlobalTheory.InertSquareNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesBoundedDetLeSum

section

@[expose] public section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.SubCount

theorem encard_biUnion_le_sum {ι β : Type} (s : Finset ι) (Y : ι → Set β) :
    ((⋃ i ∈ s, Y i).encard : ℝ≥0∞) ≤ ∑ i ∈ s, ((Y i).encard : ℝ≥0∞) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.set_biUnion_insert]
    refine le_trans (ENat.toENNReal_le.2 (Set.encard_union_le _ _)) ?_
    rw [ENat.toENNReal_add]
    gcongr

theorem encard_biUnion_le_mul {ι β : Type} (S : Set ι) (Y : ι → Set β) (c : ℝ≥0∞) (hc : c ≠ 0)
    (h : ∀ i ∈ S, ((Y i).encard : ℝ≥0∞) ≤ c) :
    ((⋃ i ∈ S, Y i).encard : ℝ≥0∞) ≤ (S.encard : ℝ≥0∞) * c := by
  rcases S.finite_or_infinite with hS | hS
  · lift S to Finset ι using hS
    refine (encard_biUnion_le_sum S Y).trans ((Finset.sum_le_card_nsmul S _ c h).trans (le_of_eq ?_))
    rw [Set.encard_coe_eq_coe_finsetCard, nsmul_eq_mul]
    simp
  · rw [hS.encard_eq, ENat.toENNReal_top, ENNReal.top_mul hc]
    exact le_top

section Index

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V] [Module K V]
  [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]

theorem index_eq (M : Submodule (𝓞 K) V) (hM : M.FG) (j : ℕ) (hj : 1 ≤ j) :
    (({P : Submodule (𝓞 K) V | P ≤ M ∧ Nat.card (M ⧸ P.comap M.subtype) = j}).encard : ℝ≥0∞) ≤
      ENNReal.ofReal ((j : ℝ) ^ ((finrank K V : ℝ) + Real.logb 2 (finrank ℚ K))) := by
  haveI : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.2 hM
  haveI : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  haveI : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  have hr : finrank (𝓞 K) M ≤ finrank K V := by
    refine Module.finrank_le_of_rank_le ((Submodule.rank_le M).trans (le_of_eq ?_))
    rw [Module.finrank_eq_rank, IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl]
  obtain ⟨h1, h2⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.c2a K M (finrank K V) j hj hr
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal h2)
  rw [ENNReal.ofReal_natCast, ← ENat.toENNReal_coe, h1.cast_ncard_eq, ENat.toENNReal_le]
  refine Set.encard_le_encard_of_injOn (f := fun P => P.comap M.subtype) (fun P hP => hP.2) ?_
  intro P hP Q hQ e
  have := congrArg (Submodule.map M.subtype) e
  simpa only [Submodule.map_comap_subtype, inf_eq_right.2 hP.1, inf_eq_right.2 hQ.1] using this

theorem index_le (M : Submodule (𝓞 K) V) (hM : M.FG) (x : ℝ) (hx : 0 < x) :
    (({P : Submodule (𝓞 K) V | P ≤ M ∧ 1 ≤ Nat.card (M ⧸ P.comap M.subtype) ∧
      (Nat.card (M ⧸ P.comap M.subtype) : ℝ) ≤ x}).encard : ℝ≥0∞) ≤
      ENNReal.ofReal (x ^ ((finrank K V : ℝ) + Real.logb 2 (finrank ℚ K) + 1)) := by
  have he : 0 ≤ (finrank K V : ℝ) + Real.logb 2 (finrank ℚ K) :=
    add_nonneg (Nat.cast_nonneg _) (Real.logb_nonneg one_lt_two (by exact_mod_cast Module.finrank_pos))
  calc _ ≤ ((⋃ j ∈ Finset.Icc 1 ⌊x⌋₊,
        {P : Submodule (𝓞 K) V | P ≤ M ∧ Nat.card (M ⧸ P.comap M.subtype) = j}).encard : ℝ≥0∞) := by
        refine ENat.toENNReal_le.2 (Set.encard_le_encard fun P hP => ?_)
        simp only [Set.mem_iUnion]
        exact ⟨_, Finset.mem_Icc.2 ⟨hP.2.1, Nat.le_floor hP.2.2⟩, hP.1, rfl⟩
    _ ≤ _ := encard_biUnion_le_sum _ _
    _ ≤ (Finset.Icc 1 ⌊x⌋₊).card • ENNReal.ofReal (x ^ ((finrank K V : ℝ) + Real.logb 2 (finrank ℚ K))) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun j hj => ?_
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
        refine (index_eq M hM j h1).trans (ENNReal.ofReal_le_ofReal ?_)
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) ((Nat.le_floor_iff hx.le).1 h2) he
    _ ≤ _ := by
        rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, Real.rpow_add_one hx.ne',
          ENNReal.ofReal_mul' hx.le, mul_comm, ← ENNReal.ofReal_natCast]
        gcongr
        exact Nat.floor_le hx.le

end Index

theorem main : ∀ (D : D7) (L : LatW D), IsPosDef (D.sp.X 0).hT → finrank D.host.E (D.sp.X 0).V = D.R.k → L.FG → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT L → ∀ (n : ℕ) (De : ℝ), 1 ≤ De → (Set.encard {P : LatW D | P ≤ L ∧ rkW D P = n ∧ detW D P ≤ De} : ℝ≥0∞) ≤ ∑ de ∈ Finset.Icc 1 ⌊De⌋₊, (cntPrim (D.sp.X 0).hT L n de : ℝ≥0∞) * ENNReal.ofReal ((De / (de : ℝ)) ^ ((D.R.k : ℝ) + lg2f D.R.f + 1)) := by
  intro D L hpos hk hL hint n De hDe
  have hf : ((finrank ℚ D.host.E : ℕ) : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [(GlobalTheory.real_places_facts D).2.1]; push_cast; rfl
  calc _ ≤ ((⋃ de ∈ Finset.Icc 1 ⌊De⌋₊, ⋃ M ∈ PrimSubs (D.sp.X 0).hT L n de,
        {P : LatW D | P ≤ M ∧ 1 ≤ Nat.card (M ⧸ P.comap M.subtype) ∧
          (Nat.card (M ⧸ P.comap M.subtype) : ℝ) ≤ De / (de : ℝ)}).encard : ℝ≥0∞) := by
        refine ENat.toENNReal_le.2 (Set.encard_le_encard ?_)
        rintro P ⟨hP, hr, hd⟩
        have hS : sat D L P ≤ L := inf_le_left
        have hPS : P ≤ sat D L P := fun x hx => ⟨hP hx, Submodule.subset_span hx⟩
        have hfg : (sat D L P).FG := hL.of_le hS
        have hi : Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (sat D L P) :=
          fun x hx y hy => hint x (hS hx) y (hS hy)
        have hsp : Submodule.span D.host.E (sat D L P : Set (D.sp.X 0).V) =
            Submodule.span D.host.E (P : Set (D.sp.X 0).V) :=
          le_antisymm (Submodule.span_le.2 fun x hx => hx.2) (Submodule.span_mono hPS)
        have hrk : rkW D P = rkW D (sat D L P) := by unfold rkW; rw [hsp]
        obtain ⟨h4, h5⟩ := (GlobalTheory.LoopC.DetCard.main D _ hfg hpos hi).2.2 P hPS hrk
        have ha : ∀ x : (D.sp.X 0).V, (D.sp.X 0).hT x x = 0 → x = 0 := by
          intro x hx
          by_contra h0
          obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
          have := hpos τ x h0
          rw [hx] at this
          simp at this
        obtain ⟨de, h1, h2⟩ := GlobalTheory.Mass.DetNat.main D.host.E (D.sp.X 0) D.sp.cm.cmUnram.2.1
          (GlobalTheory.InertSquareNorm.isSquare_absNorm _ D.sp.cm.cmUnram) ha _ hfg fun x hx =>
            ⟨(Formalism.HermitianLatticesTheory.dualBasic_mem_dual _ _ _).2 fun y hy => hi y hy x hx, Submodule.subset_span hx⟩
        have h3 : detW D (sat D L P) = de := h2
        have hde : (1 : ℝ) ≤ de := by exact_mod_cast h1
        have hj : (1 : ℝ) ≤ idxW D (sat D L P) P := by exact_mod_cast h4
        rw [h5, h3] at hd
        simp only [Set.mem_iUnion]
        refine ⟨de, Finset.mem_Icc.2 ⟨h1, Nat.le_floor (by nlinarith)⟩, sat D L P,
          ⟨⟨hS, by rw [hsp]; rfl⟩, hrk.symm.trans hr, h2⟩, hPS, h4, ?_⟩
        rw [le_div_iff₀' (by linarith)]
        exact hd
    _ ≤ _ := encard_biUnion_le_sum _ _
    _ ≤ _ := by
        refine Finset.sum_le_sum fun de hde => ?_
        have h1 : (0 : ℝ) < de := by exact_mod_cast (Finset.mem_Icc.1 hde).1
        have hx : 0 < De / (de : ℝ) := div_pos (by linarith) h1
        refine encard_biUnion_le_mul _ _ _ (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hx _)).ne' fun M hM => ?_
        have := index_le (K := D.host.E) M (hL.of_le hM.1.1) _ hx
        rwa [hk, hf] at this

end GlobalTheory.LoopC.SubCount
end
end
