module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormSpanEqProd
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.BoxInterEqEmpty
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CovolumeIntegerLatticeEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsClassReps
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FactorIdentity
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsClassRepsMap
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassRatioEqLvalue
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MeasurableSetBallSet
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormSpanSingletonEq
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DiscreteTopologyOfZsmul
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOrthBasisMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSingSSum
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VdEqZeroOfNotLe
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormLeOfMemBoxSet

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoBallCount

section

@[expose] public section

open NumberField Module Filter Topology


set_option synthInstance.maxSize 1024

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem tendsto_ballCount (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    Tendsto (fun j : ℕ => (ballCount h L ((j : ℝ) ^ 2) : ℝ) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 ((Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
        (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L))) := by
  classical
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr (hK.1.isComplex w.1) w.2⟩
  obtain ⟨b, hbL, ho⟩ := BallB.exists_orth_basis_mem hK hs hd hL
  have hBL : Submodule.span (𝓞 K) (Set.range b) ≤ L :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbL i)
  have hB : Submodule.IsFullLattice K (Submodule.span (𝓞 K) (Set.range b)) :=
    { toIsLattice := BallB.isLattice_span b
      span_eq_top := by
        apply top_unique
        rw [← b.span_eq]
        exact Submodule.span_mono Submodule.subset_span }
  obtain ⟨N, hN, hNx⟩ := LocF.exists_zsmul_le hL.toIsLattice hB
  have hlat1 : BallD.lat b (Submodule.span (𝓞 K) (Set.range b)) =
      Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) := BallD.lat_span b
  have hle : Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) ≤ BallD.lat b L := by
    rw [← hlat1]
    intro y hy
    rw [BallD.mem_lat] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hBL hx, rfl⟩
  have hNy : ∀ y ∈ BallD.lat b L,
      N • y ∈ Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) := by
    intro y hy
    rw [← hlat1]
    rw [BallD.mem_lat] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨N • x, hNx x hx, map_zsmul (BallD.emb b) N x⟩
  have hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re :=
    fun w i => hd (b i) (b.ne_zero i) w.1.embedding
  obtain ⟨hidx, hT⟩ := BallA.tendsto_card_of_le (μ := MeasureTheory.volume)
    (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) (BallD.lat b L) hle hN hNy
    (BallD.isBounded_ballSet hA) BallD.measurableSet_ballSet (BallD.convex_ballSet hA)
  have hfr : finrank ℝ (Fin (finrank K V) → NumberField.mixedEmbedding.mixedSpace K) = 2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      NumberField.mixedEmbedding.finrank, finrank_eq_two_fDeg hK]
    ring
  have hcov : ZLattice.covolume (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) MeasureTheory.volume =
      Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) := by
    rw [BallC.covolume_piBasis, covolume_integerLattice_eq hK, Fintype.card_fin, ← pow_mul]
  have hidx' : (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))).toAddSubgroup.relIndex
      (BallD.lat b L).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup := by
    rw [← hlat1]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ (BallD.emb_injective b)
  have hI0 : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
    rw [← hidx']; exact hidx
  have hnorm := BallB.normD_mul_relIndex hK hLi b hbL hI0
  have hgdet := BallB.prod_place_gdet hK hs hd b ho
  have hvol := BallD.volume_ballSet hA
  have hP : 0 < ∏ w : {w : InfinitePlace K // w.IsComplex}, ∏ i, (w.1.embedding (h (b i) (b i))).re :=
    Finset.prod_pos fun w _ => Finset.prod_pos fun i _ => hA w i
  have hIr : ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≠ 0 := by
    exact_mod_cast hI0
  have hND : normD h L ≠ 0 := by
    intro h0
    rw [h0, zero_mul, hgdet] at hnorm
    linarith
  have hV : Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) ≠ 0 := pow_ne_zero _ (vInv_pos K).ne'
  have hlim : MeasureTheory.volume.real (BallD.ballSet h b) *
      ((Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))).toAddSubgroup.relIndex
        (BallD.lat b L).toAddSubgroup : ℝ) /
      ZLattice.covolume (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) MeasureTheory.volume =
      (Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
        (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L) := by
    rw [hvol, hcov, hidx', ← hgdet, ← hnorm, nrComplexPlaces_eq_fDeg hK]
    field_simp
  rw [← hlim]
  refine Tendsto.congr' ?_ hT
  filter_upwards [eventually_gt_atTop 0] with j hj
  rw [BallD.card_eq hK ho L hj, hfr]

end Formalism.HermitianLattices.Ext.L3
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassConstSucc

section

@[expose] public section

open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

namespace Step

theorem final_algebra (μ c lam D P a mm vv sq lV : ℝ) (f : ℕ) (hD : 0 < D) (hP : 0 < P)
    (ha : 0 < a) (hmm : 0 < mm) (hvv : 0 < vv) (hsq : 0 < sq)
    (h : μ * ((P / (mm * a)) ^ f / (vv * D)) = 0 + c * lam * D⁻¹ * ((mm ^ f)⁻¹ / sq * lV)) :
    μ = c * ((a / P) ^ f * vv / sq * lV) * lam := by
  have hD' := hD.ne'
  have hP' := hP.ne'
  have ha' := ha.ne'
  have hmm' := hmm.ne'
  have hvv' := hvv.ne'
  have hsq' := hsq.ne'
  have hX : (P / (mm * a)) ^ f / (vv * D) ≠ 0 := by positivity
  rw [zero_add] at h
  rw [eq_div_of_mul_eq hX h, div_pow, mul_pow, div_pow]
  field_simp

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem normD_pos {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) : 0 < normD h L := by
  have hd' : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd x hne φ
    simp [hx] at this
  have hne := LocF.discrIdeal_ne_bot hd' hL hLi
  unfold normD
  apply Real.sqrt_pos.mpr
  have : Ideal.absNorm (discrIdeal h L) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hne
  exact_mod_cast Nat.pos_of_ne_zero this

theorem tendsto_left (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s) :
    Tendsto (fun j : ℕ => (∑ M ∈ s, (ballCount h M ((j : ℝ) ^ 2) : ℝ) /
        (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 (Formalism.HermitianLatticesTheory.mass h L *
        ((Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
          (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L)))) := by
  rw [RankOne.mass_eq_sum h L s hsr, Finset.sum_mul]
  simp_rw [Finset.sum_div]
  refine tendsto_finsetSum _ fun M hM => ?_
  have hg := hsr.1 M hM
  obtain ⟨hMi, -, hMD⟩ := integral_of_mem_genus hK hF hs hd hL hLi hg
  have ht := (tendsto_ballCount hK hF hs hd hg.1 hMi).const_mul
    ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)⁻¹)
  rw [hMD] at ht
  refine ht.congr fun j => ?_
  rw [div_eq_mul_inv (ballCount h M ((j : ℝ) ^ 2) : ℝ), div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem tendsto_right (hH : HermRepUnram) (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (hm : 2 ≤ finrank K V) {c : ℝ} (hc : MassConst K F (finrank K V - 1) c) :
    Tendsto (fun j : ℕ => (Formalism.HermitianLatticesTheory.mass h L + ∑ᶠ n ∈ boxSet K F ((j : ℝ) ^ 2),
        repMass h L (algebraMap F K (n : F))) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 (0 + c * lamG F h L * (normD h L)⁻¹ *
        ((finrank K V : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
          Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) * lValEtaF K F (finrank K V)))) := by
  have hf : 0 < Formalism.HermitianLatticesTheory.fDeg K := Fintype.card_pos
  have hexp : 2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V ≠ 0 := by positivity
  have h1 : Tendsto (fun j : ℕ => Formalism.HermitianLatticesTheory.mass h L /
      (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hexp).comp tendsto_natCast_atTop_atTop)
  have h2 := (tendsto_singS_sum hK hF hs hd hL hLi hm).const_mul
    (c * lamG F h L * (normD h L)⁻¹)
  refine (h1.add h2).congr fun j => ?_
  rw [add_div]
  congr 1
  rw [finsum_mem_congr rfl fun n hn => repMass_eq hH hLI hK hF hs hd hL hLi hm hc hn,
    finsum_mem_eq_finite_toFinset_sum _ (A5.boxSet_finite hK hF ((j : ℝ) ^ 2)),
    finsum_mem_eq_finite_toFinset_sum _ (A5.boxSet_finite hK hF ((j : ℝ) ^ 2)),
    ← Finset.mul_sum, zpow_neg, zpow_natCast, ← pow_mul, ← mul_assoc 2, div_eq_mul_inv]
  ring

end Step

theorem massConst_succ (hH : HermRepUnram) (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : IsFixF K F) {m : ℕ} (hm : 2 ≤ m) {c : ℝ} (hc0 : 0 < c) (hc : MassConst K F (m - 1) c) :
    MassConst K F m (c * Formalism.HermitianLatticesTheory.massRatioRightSide K m) := by
  unfold MassConst
  intro V _ _ _ _ _ h L hs hd hfin hL hLi
  subst hfin
  obtain ⟨s, hsr⟩ := StabilizerLattices.exists_classReps hs hd hL.toIsLattice
  have hlim := Step.tendsto_left hK hF hs hd hL hLi hsr
  have hlim2 := Step.tendsto_right hH hLI hK hF hs hd hL hLi hm hc
  have hfun : (fun j : ℕ => (∑ M ∈ s, (ballCount h M ((j : ℝ) ^ 2) : ℝ) /
        (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V)) =
      fun j : ℕ => (Formalism.HermitianLatticesTheory.mass h L + ∑ᶠ n ∈ boxSet K F ((j : ℝ) ^ 2),
        repMass h L (algebraMap F K (n : F))) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V) := by
    funext j
    rw [sum_ballCount_eq hK hF hs hd hL.toIsLattice hLi hsr (by positivity)]
  rw [hfun] at hlim
  have hAB := tendsto_nhds_unique hlim hlim2
  have hn0 : 0 < finrank K V := by omega
  have hfact : ((finrank K V).factorial : ℝ) =
      (finrank K V : ℝ) * ((finrank K V - 1).factorial : ℝ) := by
    rw [← Nat.mul_factorial_pred hn0.ne']
    push_cast
    ring
  rw [hfact, zpow_neg, zpow_natCast] at hAB
  have hv := vInv_pos K
  have key := Step.final_algebra (Formalism.HermitianLatticesTheory.mass h L) c (lamG F h L) (normD h L)
    (Real.pi ^ finrank K V) ((finrank K V - 1).factorial : ℝ) (finrank K V : ℝ)
    (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
    (Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K)) (lValEtaF K F (finrank K V))
    (Formalism.HermitianLatticesTheory.fDeg K) (Step.normD_pos hd hL hLi) (by positivity) (by positivity)
    (by exact_mod_cast hn0) (by positivity) (by positivity) hAB
  rw [massRatio_eq_lvalue hK hF (finrank K V) hm]
  exact key

end Formalism.HermitianLattices.Ext.L3
end
end
end
