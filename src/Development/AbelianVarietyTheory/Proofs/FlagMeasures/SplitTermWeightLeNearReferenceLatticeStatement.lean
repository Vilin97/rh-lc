module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefiniteThetaLatticeLeFixedIndexBoundStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarInvVolumeMiddleLayerEichlerLe
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummaryStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitiveStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexCongruenceSubgroupLeAbsNormPowStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHermitianLatticeOfDeepStarCongruenceStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormInvVolTopLayerLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolEqInfMulSupAndMono
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexNeZero
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarInvVolumeMiddleLayerEichlerLeStatement

section

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.haarInvVolume_middleLayer_eichler_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → N.Split Λ → GlobalTheory.HL.invVol ((N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.R1) ⊔ N.ZI) ((N.Gam Λ ⊓ N.R1) ⊔ N.ZI) ≤ (N.bI Λ : ℝ) ^ Module.finrank K N.Wt * ((N.gI g Λ : ℝ) * N.iI g Λ) ^ (r - N.j) := by
  first | exact @GlobalTheory.DegCnt.MidLayer.invVol_mid_layer_le | exact GlobalTheory.DegCnt.MidLayer.invVol_mid_layer_le | (intros; apply GlobalTheory.DegCnt.MidLayer.invVol_mid_layer_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormInvVolSkewLayerLe

section

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.WtSkew

theorem invVol_le_relIndex {G : Type} [Group G] (A B : Subgroup G) :
    GlobalTheory.HL.invVol A B ≤ (B.relIndex A : ℝ) := by
  unfold GlobalTheory.HL.invVol
  rcases Nat.eq_zero_or_pos (A.relIndex B) with h | h
  · simp [h]
  · exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast h)

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

omit [NumberField K] [StarRing K] in
theorem line_le {A : Submodule (𝓞 K) K} {v : V} {S : Submodule K V} (h : v ∈ S) :
    line A v ≤ rs (𝓞 K) S := by
  rintro _ ⟨t, -, rfl⟩
  exact S.smul_mem t h

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem e_mem_X (F : FlagD H r) (a : Fin r) : F.e a.castSucc ∈ F.X :=
  Submodule.subset_span ⟨a, a.2, rfl⟩

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem lastVector_mem_jointSpan_left (F F' : FlagD H r) : F.z ∈ V0 F F' :=
  Submodule.mem_sup_right (Submodule.subset_span (by simp))

theorem normalForm_baseLattice_le_dualSpan_sup_line (N : NF H r) : N.P0 ≤ rs (𝓞 K) (V0 N.F N.F' ⊔ N.Ist) := by
  unfold NF.P0
  refine sup_le (sup_le (sup_le (iSup_le fun a => line_le ?_) (iSup_le fun a => iSup_le fun _ => line_le ?_))
    (line_le ?_)) (iSup_le fun a => iSup_le fun ha => line_le ?_)
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_X _ a)))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (e_mem_X _ a)))
  · exact Submodule.mem_sup_left (lastVector_mem_jointSpan_left _ _)
  · exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, ha, rfl⟩)

theorem ref_inf_Pi (N : NF H r) (L : Submodule (𝓞 K) V) (hc : IsCompl N.Wt N.Pi)
    (hn : N.Wn = N.Wt ⊔ Submodule.span K {N.F.z}) (hp : N.Pi = V0 N.F N.F' ⊔ N.Ist)
    (hz : ∀ t : K, t • N.F.z ∈ L → t ∈ (1 : Submodule (𝓞 K) K)) :
    N.Ref L ⊓ rs (𝓞 K) N.Pi = N.P0 := by
  have h0 : N.P0 ≤ rs (𝓞 K) N.Pi := hp ▸ normalForm_baseLattice_le_dualSpan_sup_line N
  have hzP : N.F.z ∈ N.Pi := hp ▸ Submodule.mem_sup_left (lastVector_mem_jointSpan_left _ _)
  refine le_antisymm ?_ (le_inf le_sup_left h0)
  rintro x ⟨hx, hxP⟩
  obtain ⟨p, hpP, l, ⟨hlL, hlW⟩, rfl⟩ := Submodule.mem_sup.1 hx
  have hlW' : l ∈ N.Wt ⊔ Submodule.span K {N.F.z} := hn ▸ hlW
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hlW'
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hxP' : p + (w + t • N.F.z) ∈ N.Pi := hxP
  have hpP' : p ∈ N.Pi := h0 hpP
  have hwP : w ∈ N.Pi := by
    have := N.Pi.sub_mem (N.Pi.sub_mem hxP' hpP') (N.Pi.smul_mem t hzP)
    simpa using this
  have hw0 : w = 0 := (Submodule.disjoint_def.1 hc.disjoint) w hw hwP
  subst hw0
  rw [zero_add] at hlL ⊢
  refine N.P0.add_mem hpP ?_
  unfold NF.P0
  exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨t, hz t hlL, rfl⟩)

theorem invVol_skew_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) (N.Gam Λ ⊓ N.ZI) ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hT 𝔠 h0 hst hdT hD e hS hN
  obtain ⟨-, -, hc, hdim, hn, -, -, -, -, -, -, hp⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨hR, -⟩ := GlobalTheory.T.hermFramePairCommonUnipotentStabiliser_summary K V H hK r N
  obtain ⟨-, -, hz, -, hlat, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hT
  have hstab := GlobalTheory.T.stabilizer_hermitianLattice_of_deep_star_congruence K V H hK r N g Λ hg hT 𝔠 h0 hst hdT hD e hS hN
  have hP := ref_inf_Pi N (latL N.F N.F' Λ) hc hn hp (fun t ht => (hz t).1 ht)
  have hfg : N.P0.FG := by
    refine Submodule.FG.of_le hlat.fg ?_
    rw [← hP]; exact inf_le_left
  have hmap : ∀ s ∈ N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI, ∀ x ∈ N.P0, s x ∈ N.P0 := by
    rintro s ⟨⟨hsR, hsS⟩, -, hsW⟩ x hx
    rw [← hP] at hx ⊢
    have hsS' : s • N.Ref (latL N.F N.F' Λ) = N.Ref (latL N.F N.F' Λ) := hsS
    refine ⟨?_, ?_⟩
    · rw [← hsS']
      exact Submodule.smul_mem_pointwise_smul _ _ _ hx.1
    · have hx2 : x ∈ perp H N.Wt := hx.2
      change s x ∈ perp H N.Wt
      rw [mem_perp_iff] at hx2 ⊢
      intro w hw
      have hw' : s w = w := (mem_fixingSubgroup_iff _).1 hsW w hw
      have := ((hR s).1 hsR).1.1 x w
      simp only [LinearEquiv.coe_coe, hw'] at this
      rw [this]; exact hx2 w hw
  have hfix : ∀ s ∈ N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI, s • N.P0 = N.P0 := by
    intro s hs
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
      exact hmap s hs x hx
    · intro y hy
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨s⁻¹ y, hmap _ (inv_mem hs) y hy, ?_⟩
      exact s.apply_symm_apply y
  have hm : 𝔠 ^ (3 * e + 10) ≠ ⊥ := pow_ne_zero _ h0
  obtain ⟨-, hle⟩ := GlobalTheory.T.relIndex_congruence_subgroup_le_absNorm_pow K V (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) N.P0 (𝔠 ^ (3 * e + 10))
    (N.Gam Λ ⊓ N.ZI) hfg hm hfix (fun s hs hx =>
      ⟨⟨hs.1.1, hstab s ⟨hs.1.1, hs.2.2⟩ hx⟩, hs.2⟩)
  have hrk : Module.finrank K (Submodule.span K (N.P0 : Set V)) ≤ 2 * r + 1 := by
    have h1 : Submodule.span K (N.P0 : Set V) ≤ N.Pi := by
      rw [Submodule.span_le, ← hP]
      exact fun x hx => hx.2
    have h2 := Submodule.finrank_mono h1
    have h3 := Submodule.finrank_add_eq_of_isCompl hc
    omega
  have hpos : 1 ≤ Ideal.absNorm 𝔠 := Nat.one_le_iff_ne_zero.2 (fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h))
  refine (invVol_le_relIndex _ _).trans ?_
  have : (N.Gam Λ ⊓ N.ZI).relIndex (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) ≤
      Ideal.absNorm 𝔠 ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
    refine hle.trans ?_
    rw [map_pow, ← pow_mul]
    exact Nat.pow_le_pow_right hpos (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hrk 2))
  exact_mod_cast this

end GlobalTheory.DegCnt.WtSkew
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormInvVolSkewLayerLeStatement

section

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFramePairNormalForm_invVol_skew_layer_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) (N.Gam Λ ⊓ N.ZI) ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
  first | exact @GlobalTheory.DegCnt.WtSkew.invVol_skew_le | exact GlobalTheory.DegCnt.WtSkew.invVol_skew_le | (intros; apply GlobalTheory.DegCnt.WtSkew.invVol_skew_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitTermWeightLeNearReferenceLattice

section

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.Weight

theorem invVol_three {G : Type} [Group G] (R M Z A B : Subgroup G) (hM : M ≤ R) (hZ : Z ≤ M) (hA : A ≤ R) (hB : B ≤ R)
    (nM : ∀ s ∈ R, ∀ t ∈ M, s * t * s⁻¹ ∈ M) (nZ : ∀ s ∈ R, ∀ t ∈ Z, s * t * s⁻¹ ∈ Z)
    (h1 : A.relIndex B ≠ 0) (h2 : B.relIndex A ≠ 0)
    (h3 : (A ⊓ M).relIndex (B ⊓ M) ≠ 0) (h4 : (B ⊓ M).relIndex (A ⊓ M) ≠ 0) :
    GlobalTheory.HL.invVol A B = GlobalTheory.HL.invVol (A ⊓ Z) (B ⊓ Z) * GlobalTheory.HL.invVol ((A ⊓ M) ⊔ Z) ((B ⊓ M) ⊔ Z) *
      GlobalTheory.HL.invVol (A ⊔ M) (B ⊔ M) := by
  rw [(GlobalTheory.IndexProd.invVol_eq_inf_mul_sup_and_mono G R M A B hM hA hB nM h1 h2).1,
    (GlobalTheory.IndexProd.invVol_eq_inf_mul_sup_and_mono G M Z (A ⊓ M) (B ⊓ M) hZ inf_le_right inf_le_right
      (fun s hs t ht => nZ s (hM hs) t ht) h3 h4).1,
    inf_assoc, inf_assoc, inf_eq_right.mpr hZ]

theorem invVol_nonneg {G : Type} [Group G] (A B : Subgroup G) : 0 ≤ GlobalTheory.HL.invVol A B := by
  unfold GlobalTheory.HL.invVol
  positivity

theorem om_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → N.om Λ ≤ (N.bI Λ : ℝ) ^ Module.finrank K N.Wt * N.Del ^ r * (Ideal.absNorm 𝔠 : ℝ) ^ (2 * (3 * e + 11) * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hT 𝔠 hc hs hTd hD e hSp hNe
  obtain ⟨-, -, nM, nZ, hnil⟩ := GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N
  obtain ⟨-, -, -, -, hRef, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hT
  obtain ⟨-, hg0, hi0, -, hgi, -⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ hg hT
  have hTop := GlobalTheory.T.hermFramePairNormalForm_invVol_top_layer_le K V H hK r N g Λ hg hT 𝔠 hc hs hTd hD e hSp hNe
  have hBot := GlobalTheory.T.hermFramePairNormalForm_invVol_skew_layer_le K V H hK r N g Λ hg hT 𝔠 hc hs hTd hD e hSp hNe
  have hMid := GlobalTheory.T.haarInvVolume_middleLayer_eichler_le K V H hK r N g Λ hg hT hSp
  have hΛ : Submodule.IsFullLattice K Λ := by
    have h := hT.1.1.1
    unfold IsLatMod at h
    obtain ⟨⟨M, hM, hE⟩, hsp⟩ := h
    have hfg : Λ.FG := by
      rw [hE, rs, Submodule.restrictScalars_bot, sup_bot_eq]
      exact hM
    letI : Submodule.IsLattice K Λ := Submodule.IsLattice.of_fg K hfg
    exact ⟨hsp⟩
  have hRefFull : Submodule.IsFullLattice K (N.Ref (latL N.F N.F' Λ)) := by
    letI := hRef
    obtain ⟨_, _, hC, _, hWn, hUp, _, _, _, _, _, hPi⟩ :=
      GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
    have hspan : Submodule.span K (N.Ref (latL N.F N.F' Λ) : Set V) = ⊤ := by
      apply eq_top_iff.mpr
      rw [← hC.sup_eq_top]
      apply sup_le
      · intro w hw
        obtain ⟨c, hc, hcΛ⟩ := GlobalTheory.DegCnt.InnerLat.exists_mult hΛ.span_eq_top w
        have hwN : w ∈ N.Wn := by rw [hWn]; exact Submodule.mem_sup_left hw
        have hwU : w ∈ uPerp N.F N.F' := by rw [hUp]; exact Submodule.mem_sup_left hwN
        rw [← Submodule.smul_mem_iff _ hc]
        apply Submodule.subset_span
        exact Submodule.mem_sup_right ⟨⟨(uPerp N.F N.F').smul_mem c hwU,
          Submodule.mem_sup_left hcΛ⟩, N.Wn.smul_mem c hwN⟩
      · rw [hPi, ← GlobalTheory.DegCnt.InnerLat.span_hermFramePair_lattice_eq_sup N]
        exact Submodule.span_mono (show (N.P0 : Set V) ⊆ N.Ref (latL N.F N.F' Λ) from
          fun _ hx => Submodule.mem_sup_left hx)
    exact ⟨hspan⟩
  have hR1 : N.R1 ≤ N.R := inf_le_left
  have hZ : N.ZI ≤ N.R1 := inf_le_left
  have key : ∀ L : Submodule (𝓞 K) V, N.Gam L ⊓ N.R1 = N.R1 ⊓ MulAction.stabilizer (V ≃ₗ[K] V) L := by
    intro L
    unfold NF.Gam
    rw [inf_right_comm, inf_eq_right.mpr hR1]
  have hnil1 : ∀ s ∈ N.R1, ((s : V →ₗ[K] V) - 1) ^ (2 * r + 1) = 0 := fun s hs => hnil s (hR1 hs)
  have h3 := (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R1 _ hnil1 _ _ hRefFull hΛ).1
  have h4 := (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R1 _ hnil1 _ _ hΛ hRefFull).1
  rw [← key, ← key] at h3 h4
  have hprod := invVol_three N.R N.R1 N.ZI (N.Gam (N.Ref (latL N.F N.F' Λ))) (N.Gam Λ) hR1 hZ inf_le_left inf_le_left
    nM nZ (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R _ hnil _ _ hRefFull hΛ).1
    (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R _ hnil _ _ hΛ hRefFull).1 h3 h4
  have h1 : (1 : ℝ) ≤ (N.gI g Λ : ℝ) * N.iI g Λ := by
    have : 1 ≤ N.gI g Λ * N.iI g Λ := Nat.mul_pos hg0 hi0
    exact_mod_cast this
  have hpow : ((N.gI g Λ : ℝ) * N.iI g Λ) ^ (r - N.j) ≤ N.Del ^ r :=
    (pow_le_pow_right₀ h1 (Nat.sub_le _ _)).trans (pow_le_pow_left₀ (by linarith) hgi r)
  have hMid' := hMid.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hDel : (0 : ℝ) ≤ N.Del := by linarith
  unfold NF.om
  rw [hprod]
  calc _ ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) *
        ((N.bI Λ : ℝ) ^ Module.finrank K N.Wt * N.Del ^ r) *
        (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) :=
        mul_le_mul (mul_le_mul hBot hMid' (invVol_nonneg _ _) (by positivity)) hTop (invVol_nonneg _ _) (by positivity)
    _ = _ := by rw [mul_assoc 2, two_mul ((3 * e + 11) * _), pow_add]; ring

end GlobalTheory.DegCnt.Weight
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitTermWeightLeNearReferenceLatticeStatement

section

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.splitTermWeight_le_near_referenceLattice : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → N.om Λ ≤ (N.bI Λ : ℝ) ^ Module.finrank K N.Wt * N.Del ^ r * (Ideal.absNorm 𝔠 : ℝ) ^ (2 * (3 * e + 11) * (2 * r + 1) ^ 2) := by
  first | exact @GlobalTheory.DegCnt.Weight.om_le | exact GlobalTheory.DegCnt.Weight.om_le | (intros; apply GlobalTheory.DegCnt.Weight.om_le <;> assumption)
end
end
