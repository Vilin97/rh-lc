module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SigmaCount
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LiPin
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtHomInjective
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsGlobalOfFibLocNeZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsVecOfHermRep
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InvMemLocROfUnimod
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityEighth
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountEqSum
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSmulMem
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SumLocRepsEq
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoMeanAlphaN
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NuGmapLocF

section

@[expose] public section

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem nu_gmap_locF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) :
    nu h (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) 𝔭 = nu h L 𝔭 ∧
      vd h (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) 𝔭 = vd h L 𝔭 := by
  have hv : vd h (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) 𝔭 = vd h L 𝔭 := by
    rw [UnimodularLocalization.vd_gmap hg, vd_locF hK hF hs hd hL hLi h𝔭]
  have ha : alphaL h (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) 𝔭 = alphaL h L 𝔭 := by
    rw [BrB.alphaL_gmap hg]
    unfold alphaL
    simp only [akCount_locF hF h L 𝔭 h𝔭]
  refine ⟨?_, hv⟩
  unfold nu
  rw [ha, hv]

theorem main_term (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {M₂ : Submodule (𝓞 K) V} (hM₂ : Submodule.IsFullLattice K M₂)
    (hM₂i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₂) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hx₂ : S.x₀ ∈ locF 𝔭 M₂)
    {s : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s) :
    ∀ᶠ J in atTop, ∀ᶠ k in atTop,
      (nkCount h L 𝔭 k n : ℝ) = kap S (locF 𝔭 M₂) 𝔭 n J k *
        ((Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 * nu h L 𝔭) *
        ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * (nu h' T 𝔭)⁻¹ := by
  have hL_gmap (g : V ≃ₗ[K] V) :
      Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.gmap g L) := by
    refine { toIsLattice := Submodule.IsLattice.of_fg K (hL.fg.map _), span_eq_top := ?_ }
    change Submodule.span K ((g : V →ₗ[K] V) '' (L : Set V)) = ⊤
    rw [Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact g.surjective
  obtain ⟨R, hR⟩ := exists_mReps hK hF hs hd S (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hn hx hsr
  have h1 := nkCount_eq_sum hK hF hs hd S (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hn hx hR
  have h2 : ∀ M ∈ R, ∀ᶠ J in atTop, ∀ᶠ k in atTop,
      kap S M 𝔭 n J k = kap S (locF 𝔭 M₂) 𝔭 n J k := by
    intro M hM
    obtain ⟨⟨⟨g, hg, rfl⟩, hxM⟩, -⟩ := hR.1 M hM
    rw [LocalizedFibreSets.gmap_locF] at hxM ⊢
    exact kap_eq hK hF hs hd S (by first | exact hL_gmap g | exact (hL_gmap g).toIsLattice) (UnimodularLocalization.isIntegralLat_gmap hg hLi) (by first | exact hM₂ | exact hM₂.toIsLattice) hM₂i
      h𝔭 hn hx hxM hx₂
  have h3 : ∀ᶠ J in atTop, ∀ᶠ k in atTop, ∀ M ∈ R,
      kap S M 𝔭 n J k = kap S (locF 𝔭 M₂) 𝔭 n J k := by
    filter_upwards [(Finset.eventually_all R).mpr h2] with J hJ
    exact (Finset.eventually_all R).mpr hJ
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    exact_mod_cast reductionMapsOfForms.absNorm_pos h𝔭
  filter_upwards [h1, h3] with J hJ1 hJ3
  filter_upwards [hJ1, hJ3] with k hk1 hk3
  rw [hk1, ← sum_oM hK hF hs hd S (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hsr hR (fun T => (nu h' T 𝔭)⁻¹), Nat.cast_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun M hM => ?_
  rw [← hk3 M hM]
  obtain ⟨⟨⟨g, hg, rfl⟩, hxM⟩, -⟩ := hR.1 M hM
  obtain ⟨e1, e2⟩ := nu_gmap_locF hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hg
  have hν : 0 < nu h L 𝔭 := by
    rw [← e1, LocalizedFibreSets.gmap_locF]
    exact nu_pos hK hF hs hd (by first | exact hL_gmap g | exact (hL_gmap g).toIsLattice) (UnimodularLocalization.isIntegralLat_gmap hg hLi) h𝔭
  have hν' : 0 < nu h' (S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))) 𝔭 := by
    rw [LocalizedFibreSets.gmap_locF, LocalizedFibreSets.cut_locF]
    exact nu_pos hK hF (S.isSymm hs) (S.isTotPosDef hd)
      (by
        have hcut := StabilizerLattices.isFullLattice_cut S (hL_gmap g)
        first | exact hcut | exact hcut.toIsLattice)
      (UnimodularLocalization.isIntegralLat_cut S (UnimodularLocalization.isIntegralLat_gmap hg hLi)) h𝔭
  have ho : (oM S (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) : ℝ) ≠ 0 := by
    rw [LocalizedFibreSets.gmap_locF] at hxM ⊢
    exact_mod_cast oM_ne_zero hs S (by first | exact hL_gmap g | exact (hL_gmap g).toIsLattice) h𝔭 hxM
  unfold kap
  rw [e1, e2]
  have hq' := pow_pos hq (vd h L 𝔭)
  field_simp

end Formalism.HermitianLattices.Ext.L3.LIOrb
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RepRatioEqZero

section

@[expose] public section

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem eigenvalue_eq₂ (T : Submodule (𝓞 K) V') (𝔭 : Ideal (𝓞 F)) :
    lamP h' T 𝔭 = alphaStd K 𝔭 (finrank K V') * (nu h' T 𝔭)⁻¹ := by
  unfold lamP nu
  rw [inv_div, mul_div_assoc]

theorem repRatio_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {k : ℕ}
    (hk : 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 ≤ k) {κ σ : ℝ}
    (e : (nkCount h L 𝔭 k n : ℝ) = κ * ((Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 * nu h L 𝔭) * σ) :
    repRatio h L 𝔭 n = κ / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) * σ := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    exact_mod_cast reductionMapsOfForms.absNorm_pos h𝔭
  have hα := alphaL_pos hK hF hs hd hL hLi h𝔭
  unfold repRatio
  rw [alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn hk, e]
  unfold nu
  have e2 : (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h L 𝔭) =
      (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vd h L 𝔭) * (Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 := by
    rw [← pow_add, ← S.finrank_add_one, Nat.add_sub_cancel, Nat.succ_mul]
  rw [e2]
  have h1 := pow_pos hq ((finrank K V - 1) * vd h L 𝔭)
  have h2 := pow_pos hq (vd h L 𝔭)
  have h3 := pow_pos hq (k * (2 * finrank K V - 1))
  field_simp

theorem repRatio_eq_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hE : ¬ ∃ M₂ : Submodule (𝓞 K) V, Submodule.IsFullLattice K M₂ ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h M₂ ∧
      S.x₀ ∈ locF 𝔭 M₂) : repRatio h L 𝔭 n = 0 := by
  obtain ⟨s, hsr⟩ := exists_locReps hK hF hs hd S hL hLi h𝔭
  obtain ⟨R, hR⟩ := exists_mReps hK hF hs hd S hL hLi h𝔭 hn hx hsr
  have hR0 : R = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro M hM
    obtain ⟨⟨⟨g, hg, rfl⟩, hxM⟩, -⟩ := hR.1 M hM
    rw [LocalizedFibreSets.gmap_locF] at hxM
    have hL_gmap : Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.gmap g L) := by
      refine { toIsLattice := Submodule.IsLattice.of_fg K (hL.fg.map _), span_eq_top := ?_ }
      change Submodule.span K ((g : V →ₗ[K] V) '' (L : Set V)) = ⊤
      rw [Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
      exact g.surjective
    exact hE ⟨_, hL_gmap, UnimodularLocalization.isIntegralLat_gmap hg hLi, hxM⟩
  obtain ⟨J, hJ⟩ := (nkCount_eq_sum hK hF hs hd S hL hLi h𝔭 hn hx hR).exists
  obtain ⟨k, hk1, hk2⟩ := (hJ.and (eventually_ge_atTop (2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2))).exists
  rw [hR0, Finset.sum_empty] at hk1
  rw [repRatio_eq hK hF hs hd S hL hLi h𝔭 hn hk2 (κ := 0) (σ := 0) (by rw [hk1]; simp)]
  simp

end LIOrb

open LIOrb in
theorem liRatio : LIRatio := by
  intro K F _ _ _ _ _ _ hK hF V V' _ _ _ _ _ _ _ _ _ _ h h' S L L₀ 𝔭 n hs hd h𝔭 hn hx hL hLi hL₀ hL₀i
  by_cases hE : ∃ M₂ : Submodule (𝓞 K) V, Submodule.IsFullLattice K M₂ ∧
      Formalism.HermitianLatticesTheory.IsIntegralLat h M₂ ∧ S.x₀ ∈ locF 𝔭 M₂
  · obtain ⟨M₂, hM₂, hM₂i, hx₂⟩ := hE
    obtain ⟨s, hsr⟩ := exists_locReps hK hF hs hd S hL hLi h𝔭
    obtain ⟨s₀, hsr₀⟩ := exists_locReps hK hF hs hd S hL₀ hL₀i h𝔭
    obtain ⟨J, hJ, hJ₀⟩ := ((main_term hK hF hs hd S hL hLi hM₂ hM₂i h𝔭 hn hx hx₂ hsr).and
      (main_term hK hF hs hd S hL₀ hL₀i hM₂ hM₂i h𝔭 hn hx hx₂ hsr₀)).exists
    obtain ⟨k, ⟨hk, hk₀⟩, hk1, hk2⟩ := ((hJ.and hJ₀).and
      ((eventually_ge_atTop (2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2)).and
        (eventually_ge_atTop (2 * vd h L₀ 𝔭 + 2 * vF 𝔭 n + 2)))).exists
    rw [psiP_eq_sum hK hF hs hd S hL.toIsLattice hLi h𝔭 hsr,
      psiP_eq_sum hK hF hs hd S hL₀.toIsLattice hL₀i h𝔭 hsr₀,
      repRatio_eq hK hF hs hd S hL hLi h𝔭 hn hk1 hk, repRatio_eq hK hF hs hd S hL₀ hL₀i h𝔭 hn hk2 hk₀]
    simp only [eigenvalue_eq₂, mul_left_comm _ (alphaStd K 𝔭 (finrank K V')), ← Finset.mul_sum]
    ring
  · rw [repRatio_eq_zero hK hF hs hd S hL hLi h𝔭 hn hx hE,
      repRatio_eq_zero hK hF hs hd S hL₀ hL₀i h𝔭 hn hx hE, mul_zero, mul_zero]

end Formalism.HermitianLattices.Ext.L3
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LiStatOf

section

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

theorem liStat_of (hR : LIRatio) (hP : LIPin) : LIStat := by
  intro K F _ _ _ _ _ _ hK hF V V' _ _ _ _ _ _ _ _ _ _ h h' S L 𝔭 n hs hd h𝔭 hn hx hL hLi
  obtain ⟨L₀, hL₀, hL₀i, hR0, hpin⟩ := hP K F hK hF V V' h h' S 𝔭 n hs hd h𝔭 hn hx
  have hrat := hR K F hK hF V V' h h' S L L₀ 𝔭 n hs hd h𝔭 hn hx hL hLi hL₀ hL₀i
  rw [hpin] at hrat
  have key : psiP S L 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vF 𝔭 n) *
      alphaStd K 𝔭 (finrank K V - 1) * repRatio h L 𝔭 n := by
    apply mul_right_cancel₀ hR0
    rw [hrat]
    ring
  rw [key, repRatio, Nat.mul_add, pow_add]
  ring

theorem liStat : LIStat := liStat_of liRatio liPin

end Formalism.HermitianLattices.Ext.L3
end
end
end
