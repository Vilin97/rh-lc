module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorizationBoundMonoLattices
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DensityNumericalFacts
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LocalHypothesisOfGlobal
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ColumnSpanNumericalFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatticeMapsOfFunctorComparison
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ModelIdentificationOfExplicitMap
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudPropOfMapsRetractionBasis
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.BlockSplit
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankLetter
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FunctorComparisonOfSingleWeightFacts
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.InvariantSectionsTransportGL
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatticeCountPrimeMonoLevel
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ResidueClassCountOfTensorBasisInclusion
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RestOIso
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Tensor
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.EdgeLatRS
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoUpperBoundSmallDepth
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TensorBoundOfOrderBound
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MeanDefs
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ThrLPOf
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ThresholdDensityFacts
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ThresholdFinalFacts
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ThresholdFixedWeightFacts
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LpRingIndepOf

-- Source module: Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MidMeanOf

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def FM (K : Cst) (X : Dat) : Prop := FixedWeightNumericalFacts K X ∧ DensityNumericalFacts K X ∧ MeanKappaNumericalFacts K X ∧ ColumnSpanNumericalFacts K X

theorem midMean_of (D : Formalism.BasicNotions.D7) (h61a : RhoSumLowerBoundEdge) (h60ab : RhoUpperBoundSmallDepth) (hE : RestEdge) (hD : RestDims) (K : Cst)
    (hK : K.Pos) : MidMean D K (FM K) := fun hA X hF R =>
  have hk := keyIneq_of D K hA h61a h60ab hE hD X hF.1 R
  mean_of K hK X hF.2.2.2 R (avg_of hD K X hF.2.1 R hk 0 (Nat.zero_le _)) (avg_of hD K X hF.2.1 R hk X.ccl le_rfl)
    (meanX_of D K hK hA X hF.2.2.1 R)

theorem TransportedAlt.and {K : Cst} {F G : ℝ → Dat → Prop} (hF : TransportedAlt K F) (hG : TransportedAlt K G) : TransportedAlt K fun C X => F C X ∧ G C X := by
  obtain ⟨T, Cn, hT, hCn, h⟩ := hF
  obtain ⟨T', Cn', _, _, h'⟩ := hG
  exact ⟨max T T', max Cn Cn', lt_max_of_lt_left hT, lt_max_of_lt_left hCn, fun CH hCH C hC X hX =>
    ⟨h CH (le_trans (le_max_left _ _) hCH) C (le_trans (le_max_left _ _) hC) X hX,
      h' CH (le_trans (le_max_right _ _) hCH) C (le_trans (le_max_right _ _) hC) X hX⟩⟩

end Formalism.MainNotions.flipOneThree.Pf

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudPropOfMapsBasis

section

@[expose] public section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem latRetract : LatRetract := by
  unfold LatRetract
  intro O K V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι ι' _ _ b b' io hio
  classical
  set L := Submodule.span O (Set.range b) with hL
  set L' := Submodule.span O (Set.range b') with hL'
  have hcoord : ∀ x ∈ L, ∀ i, ∃ a : O, algebraMap O K a = b.repr x i := by
    intro x hx i
    exact ⟨(b.restrictScalars O).repr ⟨x, hx⟩ i, Module.Basis.restrictScalars_repr_apply O b ⟨x, hx⟩ i⟩
  have hinj : Function.Injective io := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro F hF
    rw [LinearMap.mem_ker] at hF
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, b.repr F i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (b.ext_elem (fun j => by simp [h j]))
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hϖ0 : algebraMap O K ϖ ≠ 0 := fun h0 =>
      hϖ.ne_zero (IsFractionRing.injective O K (by rw [h0, map_zero]))
    have hmem : ((algebraMap O K ϖ)⁻¹ * (b.repr F i)⁻¹) • F ∈ L := by
      rw [← hio, map_smul, hF, smul_zero]
      exact Submodule.zero_mem _
    obtain ⟨a, ha⟩ := hcoord _ hmem i
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hi, mul_one] at ha
    apply hϖ.not_isUnit
    refine isUnit_iff_exists_inv.mpr ⟨a, ?_⟩
    apply IsFractionRing.injective O K
    rw [map_mul, ha, map_one, mul_inv_cancel₀ hϖ0]
  let φ : L →ₗ[O] L' :=
    LinearMap.codRestrict L' ((io.restrictScalars O).domRestrict L) (fun x => (hio x).2 x.2)
  have hφ : Function.Injective φ := fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))
  haveI : Module.Finite O L' := Module.Finite.span_of_finite O (Set.finite_range b')
  haveI : NoZeroSMulDivisors O (L' ⧸ LinearMap.range φ) := by
    refine ⟨fun {a q} h => ?_⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    rcases eq_or_ne a 0 with ha | ha
    · exact Or.inl ha
    right
    rw [Submodule.Quotient.mk_eq_zero]
    obtain ⟨x, hx⟩ := h
    have hx' : io (x : V) = a • (y : V') := congrArg Subtype.val hx
    have hK : algebraMap O K a ≠ 0 := fun h0 =>
      ha (IsFractionRing.injective O K (by rw [h0, map_zero]))
    have hyio : (y : V') = io ((algebraMap O K a)⁻¹ • (x : V)) := by
      rw [map_smul, hx', ← algebraMap_smul K a (y : V'), smul_smul, inv_mul_cancel₀ hK, one_smul]
    have hmem : (algebraMap O K a)⁻¹ • (x : V) ∈ L := (hio _).1 (hyio ▸ y.2)
    exact ⟨⟨_, hmem⟩, Subtype.ext hyio.symm⟩
  haveI : Module.Free O (L' ⧸ LinearMap.range φ) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range φ).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  let pr : L' →ₗ[O] L' := LinearMap.id - s ∘ₗ (LinearMap.range φ).mkQ
  have hpr : ∀ y, pr y ∈ LinearMap.range φ := by
    intro y
    have h2 := LinearMap.congr_fun hs ((LinearMap.range φ).mkQ y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
    rw [← Submodule.ker_mkQ (LinearMap.range φ), LinearMap.mem_ker]
    simp only [pr, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h2, sub_self]
  let e := LinearEquiv.ofInjective φ hφ
  let r0 : L' →ₗ[O] L := e.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range φ) pr hpr
  have hr0 : ∀ x : L, r0 (φ x) = x := by
    intro x
    have h1 : (LinearMap.range φ).mkQ (φ x) = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact LinearMap.mem_range_self φ x
    show e.symm (LinearMap.codRestrict _ pr hpr (φ x)) = x
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    simp [LinearMap.codRestrict_apply, h1, e, pr, LinearEquiv.ofInjective_apply]
  let ret : V' →ₗ[K] V := b'.constr K (fun j => ((r0 ⟨b' j, Submodule.subset_span ⟨j, rfl⟩⟩ : L) : V))
  have hA : ∀ y : L', ret (y : V') = (r0 y : V) := by
    have h3 : (ret.restrictScalars O) ∘ₗ L'.subtype = L.subtype ∘ₗ r0 := by
      refine (b'.restrictScalars O).ext (fun j => ?_)
      have hj : (b'.restrictScalars O) j = ⟨b' j, Submodule.subset_span ⟨j, rfl⟩⟩ :=
        Subtype.ext (Module.Basis.restrictScalars_apply _ _ _)
      rw [hj]
      simp [ret, Module.Basis.constr_basis]
    intro y
    exact LinearMap.congr_fun h3 y
  refine ⟨ret, ?_, ?_⟩
  · have h4 : ret ∘ₗ io = LinearMap.id := by
      refine b.ext (fun i => ?_)
      have hbi : b i ∈ L := Submodule.subset_span ⟨i, rfl⟩
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      have h5 := hA (φ ⟨b i, hbi⟩)
      rw [hr0] at h5
      exact h5
    intro F
    exact LinearMap.congr_fun h4 F
  · intro G hG
    rw [hA ⟨G, hG⟩]
    exact (r0 ⟨G, hG⟩).2

theorem cloud_prop_of_maps_basis (hC : RestCloudMaps) (hBP : BePerfect) (hD3 : DualHeightBasis) : CloudLowerBoundWeyl :=
  cloud_prop_of_maps_retraction_basis hC latRetract hBP hD3

theorem cloud_bound_of_maps (hC : RestCloudMaps) (hBP : BePerfect) (hD3 : DualHeightBasis) (hW : WeylV) : CloudWeightLowerBound :=
  cloud_bound_of_prop_and_weyl_dimension (cloud_prop_of_maps_basis hC hBP hD3) hW

end Formalism.MainNotions.flipOneThree.Pf
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RestTensor

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

theorem restLeLat : RestLeLat := by
  intro p n' R m e he s
  obtain ⟨gs, hgs, -, h2, -⟩ := edgeLat_RS R e he
  refine ⟨_, ?_, h2 s⟩
  rw [Matrix.det_mul]
  exact (hgs s).mul (lb_D_det (m + 1) 1 _ (RS.w_ne R))

theorem restTensor : RestTensor := restTensor_of restLeLat

end Formalism.MainNotions.flipOneThree.Pf

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TheoremIOfIntermediateBounds

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem kF_nonneg (X : Dat) (K : Cst) (R : RS X.p X.n') (al be : X.TT → ℕ) : 0 ≤ X.kF K R al be :=
  Real.sInf_nonneg fun _ h => h.1

open Classical in
theorem kText_nonneg (X : Dat) (K : Cst) (R : RS X.p X.n') (hb : 0 < X.b') (aa bb : X.TT → ℤ) :
    0 ≤ X.kText K R aa bb := by
  unfold Dat.kText
  have h1 : 0 ≤ (if X.Inside aa bb then
      X.kF K R (fun s => (aa s - X.ccl).toNat) (fun s => (bb s - X.ccl).toNat) else 1) := by
    split_ifs
    · exact kF_nonneg _ _ _ _ _
    · exact zero_le_one
  have h2 := kF_nonneg X K R (fun s => (aa s + X.ccl).toNat) (fun s => (bb s + X.ccl).toNat)
  have h3 : 0 ≤ 12 * (X.N : ℝ) * X.k * X.ccl / X.b' := by
    unfold Dat.k
    positivity
  linarith

theorem theorem_I_of_intermediate_bounds (D : Formalism.BasicNotions.D7) (FM : Cst → Dat → Prop) (hR : LPRingIndep) (hLP : ∀ K C, MidLP K C)
    (hMean : ∀ K : Cst, K.Pos → MidMean D K (FM K)) (hN1 : ∀ K : Cst, K.Pos → TransportedAlt K (FactsLP K))
    (hN2 : ∀ K : Cst, K.Pos → TransportedAlt K (fun _ => FM K)) : SecondPartClosed D := by
  intro hA
  obtain ⟨T0, hT0, h0⟩ := hA 4 (by norm_num)
  refine ⟨T0, hT0, fun C₀ hC₀ => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C₀ hC₀
  obtain ⟨T2, hT2, h2⟩ := h1 T1 T1 T1 le_rfl le_rfl le_rfl
  obtain ⟨CA, Ckap, Ct, Cs, hCA, hCkap, hCt, hCs, hAdm⟩ := h2 T2 le_rfl
  let K : Cst := ⟨C₀, T2, CA, T1, T1, T1, Ckap, Ct, Cs⟩
  have hK : K.Pos := ⟨lt_of_lt_of_le hT0 hC₀, hT2, hCA, hT1, hT1, hT1, hCkap, hCt, hCs⟩
  obtain ⟨Ta, Ca, hTa, hCa, hFa⟩ := hN1 K hK
  obtain ⟨Tb, Cb, hTb, hCb, hFb⟩ := hN2 K hK
  refine ⟨max Ta Tb, max (max Ca Cb) K.Cmean, lt_max_of_lt_left hTa,
    lt_max_of_lt_left (lt_max_of_lt_left hCa), fun CH hCH => ?_⟩
  intro p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar hH
  have hm : m ≠ 0 := by
    have := hH.2.2.2.2.2.2.1
    omega
  have hY : 1 ≤ Y := hH.1
  let X : Dat := ⟨p, n', m, hm, TT, G', N₁, Y, Yb, a, b', bl, bu, ccl, Dp, cStar⟩
  have hX : X.Hyp K.C₀ CH := hH
  have hLPf : FactsLP K (max (max Ca Cb) K.Cmean) X :=
    hFa CH (le_trans (le_max_left _ _) hCH) _ (le_trans (le_max_left _ _) (le_max_left _ _)) X hX
  have hMf : FM K X :=
    hFb CH (le_trans (le_max_right _ _) hCH) (max (max Ca Cb) K.Cmean)
      (le_trans (le_max_right _ _) (le_max_left _ _)) X hX
  have hnn : 0 ≤ (TT.card : ℝ) * N₁ / Y := by positivity
  by_cases hne : Nonempty (RS p n')
  · obtain ⟨R₀⟩ := hne
    refine ⟨X.kText K R₀, kText_nonneg X K R₀ hLPf.bpos, ?_, ?_⟩
    · have h := hMean K hK hAdm X hMf R₀
      have h' : K.Cmean * (TT.card : ℝ) * N₁ / Y ≤ max (max Ca Cb) K.Cmean * (TT.card : ℝ) * N₁ / Y := by
        have := mul_le_mul_of_nonneg_right (le_max_right (max Ca Cb) K.Cmean) hnn
        calc K.Cmean * (TT.card : ℝ) * N₁ / Y = K.Cmean * ((TT.card : ℝ) * N₁ / Y) := by ring
          _ ≤ max (max Ca Cb) K.Cmean * ((TT.card : ℝ) * N₁ / Y) := this
          _ = _ := by ring
      exact le_trans h h'
    · intro W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hstd aw bw lam0 hW t ht
      let R : RS p n' := ⟨W, Qq, O, Kf, ι, σ, j, w, hstd⟩
      exact hR p n' R₀ R m 1 lam0 t Dp _ cStar (hLP K _ X hLPf R₀ aw bw lam0 hW t ht)
  · refine ⟨fun _ _ => 0, fun _ _ => le_rfl, ?_, ?_⟩
    · have h0 : meanKap TT m Y a bl bu (fun _ _ => (0 : ℝ)) = 0 := by simp [meanKap]
      rw [h0]
      have hC : 0 ≤ max (max Ca Cb) K.Cmean := le_of_lt (lt_max_of_lt_left (lt_max_of_lt_left hCa))
      have := mul_nonneg hC hnn
      calc (0 : ℝ) ≤ max (max Ca Cb) K.Cmean * ((TT.card : ℝ) * N₁ / Y) := this
        _ = _ := by ring
    · intro W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hstd
      exact absurd ⟨(⟨W, Qq, O, Kf, ι, σ, j, w, hstd⟩ : RS p n')⟩ hne

end Formalism.MainNotions.flipOneThree.Pf

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TheoremIOfLatticeFunctorComparison

section

@[expose] public section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem tools_of_admitted_statements (D : Formalism.BasicNotions.D7) (hA : AdmBE D) : AdmT D := by
  obtain ⟨T0, _, h0⟩ := hA 4 (by norm_num)
  obtain ⟨T1, _, h1⟩ := h0 T0 le_rfl
  obtain ⟨T2, _, h2⟩ := h1 T1 T1 T1 le_rfl le_rfl le_rfl
  obtain ⟨CA, Ckap, Ct, Cs, _, _, _, _, hAdm⟩ := h2 T2 le_rfl
  exact hAdm.2.2.2.2

theorem thrFM (K : Cst) (hK : K.Pos) : TransportedAlt K (fun _ => FM K) :=
  (threshold_fixed_weight_facts K hK).and ((threshold_density_facts K hK).and ((threshold_mean_kappa_facts K hK).and (threshold_final_facts K hK)))

theorem restEdge : RestEdge := restEdge_of restFunct

theorem blockSplit' : BlockSplit := fun _ _ _ _ _ _ n z hz A h => KP.blockSplit n z hz A h

theorem second_estimate_of_restrictions (D : Formalism.BasicNotions.D7) (hR : LPRingIndep) (h61a : RhoSumLowerBoundEdge) (h62 : CloudWeightLowerBound) (h63 : ResidueClassCount) :
    SecondPartClosed D := by
  intro hA
  have hT := tools_of_admitted_statements D hA
  have h16 : PairedPathIndependence D := hT.2.2.2.2.2.2.2.2.2.2.2
  have hD : RestDims := restDims_of D h16.1 h16.2
  exact theorem_I_of_intermediate_bounds D FM hR (midLP_of rho_lower_bound_large_conductor h62 h63)
    (fun K hK => midMean_of D h61a rho_upper_bound_small_depth restEdge hD K hK) thrLP thrFM hA

theorem theorem_I_of_finer_open_statements (D : Formalism.BasicNotions.D7) (hR : LPRingIndep) (h61 : LatticeFunctorComparison) (hC : RestCloudMaps) : SecondPartClosed D := by
  intro hA
  have hT := tools_of_admitted_statements D hA
  have h16 : PairedPathIndependence D := hT.2.2.2.2.2.2.2.2.2.2.2
  have h13 : TypeDecompositionsCommute D := hT.2.2.2.2.2.2.2.2.1
  exact second_estimate_of_restrictions D hR (rho_sum_bound_of_maps_splitting (lattice_maps_of_functor_comparison h61) blockSplit') (cloud_bound_of_maps hC h13.2.2.1 h13.1 h16.2)
    (tensor_bound_of_order_bound restTensor restOrdBound h13.1 h13.2.1) hA

theorem theorem_I_of_lattice_functor_comparison (D : Formalism.BasicNotions.D7) (h61 : LatticeFunctorComparison) (hC : RestCloudMaps) : SecondPartClosed D := by
  intro hA
  have h12 : NestedTypeBound D := (tools_of_admitted_statements D hA).2.2.2.2.2.2.2.1
  exact theorem_I_of_finer_open_statements D (lpRingIndep_of'' h12.1 restOIso) h61 hC hA

theorem theorem_I_of_model_identification (D : Formalism.BasicNotions.D7) (hTie : TwoLetterModelIdentification) (hC : RestCloudMaps) : SecondPartClosed D :=
  theorem_I_of_lattice_functor_comparison D (functor_comparison_of_single_weight_facts (single_weight_of_model_identification hTie)) hC

theorem theorem_I_of_explicit_minor_map (D : Formalism.BasicNotions.D7) (hPsi : TiePsi) (hC : RestCloudMaps) : SecondPartClosed D :=
  theorem_I_of_model_identification D (model_identification_of_explicit_map hPsi) hC

end Formalism.MainNotions.flipOneThree.Pf
end
end
