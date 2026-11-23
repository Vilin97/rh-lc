module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfColCover
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.TranslationIndependent
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MultiplicityMeasurability.MeasurableMult
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Mathlib.Tactic.TypeStar

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfCol

section

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RegroupPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ColUniqPf

theorem colUniq_of {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
    {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')
    (hK : X.LevelSubgroupCharacter) (hR : ColReps hK cs') : ColUniq cs cs' := by
  intro ρ ρ₁ ρ₂ γ₁ γ₂ h₁ h₂ hs
  have hB : ((cs'.h ρ₁ : X.B.I.Gf) * X.xu u')⁻¹ * (γ₁⁻¹ * γ₂).2 * ((cs'.h ρ₂ : X.B.I.Gf) * X.xu u') ∈ X.K2 := by
    have e : ((cs'.h ρ₁ : X.B.I.Gf) * X.xu u')⁻¹ * (γ₁⁻¹ * γ₂).2 * ((cs'.h ρ₂ : X.B.I.Gf) * X.xu u') =
        (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ₁ : X.B.I.Gf) γ₁)⁻¹ *
          kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ₂ : X.B.I.Gf) γ₂ := by
      simp only [kOf, Prod.snd_mul, Prod.snd_inv]
      group
    rw [e]
    exact hK.2.1 _ (hK.2.2.1 _ h₁.2) _ h₂.2
  obtain ⟨hsI, hsf⟩ := Formalism.L2.SG.PoincareInHH.Cut.sratComp_holds X u' _ hs
  obtain ⟨ν, η, hνη, -, -, hνf, hη⟩ :=
    Formalism.L2.SG.Pf.ratLevi_holds X u' _ (Subgroup.mem_inf.1 hs).1 hsI hsf
  have hs2 : (γ₁⁻¹ * γ₂).2 = ν.2 * η.2 := by rw [hνη, Prod.snd_mul]
  have hio : ((iotaF X u' ⟨η, hη⟩ : Hfin X u') : X.B.I.Gf) = η.2 := rfl
  have hn := ((Formalism.L2.SG.PoincareInHH.Cut.nfinConj_holds X u') (cs'.h ρ₁)⁻¹ ν.2 hνf).1
  have hlev := Formalism.L2.SG.Pf.levelDec_holds X u' _ hn
    ((cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂) (by
      have e : (X.xu u')⁻¹ * ((((cs'.h ρ₁)⁻¹ : Hfin X u') : X.B.I.Gf) * ν.2 *
          (((cs'.h ρ₁)⁻¹ : Hfin X u') : X.B.I.Gf)⁻¹ *
          (((cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂ : Hfin X u') : X.B.I.Gf)) * X.xu u' =
          ((cs'.h ρ₁ : X.B.I.Gf) * X.xu u')⁻¹ * (γ₁⁻¹ * γ₂).2 * ((cs'.h ρ₂ : X.B.I.Gf) * X.xu u') := by
        rw [hs2]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hio]
        group
      rw [e]
      exact hB)
  obtain ⟨ρ0, -, huniq⟩ := hR (cs'.h ρ₂)
  have e1 := huniq ρ₂ ⟨1, 1, by simp⟩
  have e2 := huniq ρ₁ ⟨(⟨η, hη⟩ : Gam X u')⁻¹,
    ⟨(cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂, hlev.1⟩, by
      show cs'.h ρ₂ = iotaF X u' (⟨η, hη⟩ : Gam X u')⁻¹ * cs'.h ρ₁ *
        ((cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂)
      rw [map_inv]
      group⟩
  exact e2.trans e1.symm

end ColUniqPf

theorem column_uniqueness : ColUniqC := by
  intro D X Y u u' _
  exact ColUniqPf.colUniq_of (Y.cs u) (Y.cs u') Y.hK (Y.colReps u')

end Formalism.L2.SG.Pf.RegroupPf
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfSlabAbs

section

@[expose] public section

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

section SlabAbsGen

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]

theorem lintegral_le_of_uniq (Γ : Subgroup G) [Countable Γ] (FS : Set G) (hFS : IsFundamentalDomain Γ FS μ)
    (P : Set G) (hP : MeasurableSet P) (f : G → ℝ≥0∞) (hfm : Measurable f)
    (hfi : ∀ s ∈ Γ, ∀ y, f (s * y) = f y) (huniq : ∀ y ∈ P, ∀ s ∈ Γ, s * y ∈ P → s = 1) :
    ∫⁻ x in P, f x ∂μ ≤ ∫⁻ x in FS, f x ∂μ := by
  have hinv : ∀ (g : Γ) (x : G), f (g⁻¹ • x) = f x := by
    intro g x
    rw [Subgroup.smul_def, smul_eq_mul]
    exact hfi _ (g⁻¹).2 x
  rw [hFS.setLIntegral_eq_tsum']
  simp_rw [hinv]
  rw [← lintegral_iUnion₀]
  · exact lintegral_mono_set (Set.iUnion_subset fun g => Set.inter_subset_right)
  · intro g
    exact (hP.const_smul g).nullMeasurableSet.inter hFS.nullMeasurableSet
  · intro g h hgh
    apply Disjoint.aedisjoint
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨⟨p, hp, rfl⟩, -⟩ ⟨⟨q, hq, hqx⟩, -⟩
    apply hgh
    have e : (h : G) * q = (g : G) * p := by simpa [Subgroup.smul_def] using hqx
    have hsq : ((h⁻¹ * g : Γ) : G) * p = q := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, ← e, ← mul_assoc, inv_mul_cancel, one_mul]
    have h1 : ((h⁻¹ * g : Γ) : G) = 1 := huniq p hp _ (h⁻¹ * g).2 (by rw [hsq]; exact hq)
    have h2 : h⁻¹ * g = 1 := Subtype.ext h1
    exact (inv_mul_eq_one.mp h2).symm

end SlabAbsGen

theorem lintegral_slab (I : Formalism.MainNotions.S.AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsMulLeftInvariant]
    (K : Set I.Gf) (hK : MeasurableSet K) (Ω : Set I.Ginf) (hΩ : MeasurableSet Ω) (a : I.Gf) (f : I.GA → ℝ≥0∞)
    (hfm : Measurable f) (hf : ∀ y : I.Ginf, ∀ k ∈ K, f (y, a * k) = f (y, a)) :
    ∫⁻ x in Ω ×ˢ ((a * ·) '' K), f x ∂(I.muA μf) =
      μf K * ∫⁻ y in Ω, f (y, a) ∂(Formalism.L2.SG.ProjRows.muInf I) := by
  have hs : MeasurableSet ((a * ·) '' K) := by
    rw [Set.image_mul_left]
    exact measurable_const_mul a⁻¹ hK
  have hvol : μf ((a * ·) '' K) = μf K := by
    rw [Set.image_mul_left]
    exact measure_preimage_mul μf a⁻¹ K
  have hin : ∀ y ∈ Ω, ∫⁻ x in (a * ·) '' K, f (y, x) ∂μf = f (y, a) * μf K := by
    intro y _
    rw [← hvol, ← setLIntegral_const]
    first
      | exact setLIntegral_congr_fun hs (fun x hx => by obtain ⟨k, hk, rfl⟩ := hx; exact hf y k hk)
      | exact setLIntegral_congr_fun hs (Filter.Eventually.of_forall fun x hx => by
          obtain ⟨k, hk, rfl⟩ := hx; exact hf y k hk)
  have hfa : Measurable fun y : I.Ginf => f (y, a) := by fun_prop
  unfold Formalism.MainNotions.S.AutInst.muA
  rw [← Measure.prod_restrict, lintegral_prod _ hfm.aemeasurable]
  have hout : ∫⁻ y in Ω, ∫⁻ x in (a * ·) '' K, f (y, x) ∂μf ∂(Measure.pi fun v => Formalism.REAL.muG (I.ε v)) =
      ∫⁻ y in Ω, f (y, a) * μf K ∂(Measure.pi fun v => Formalism.REAL.muG (I.ε v)) := by
    first
      | exact setLIntegral_congr_fun hΩ hin
      | exact setLIntegral_congr_fun hΩ (Filter.Eventually.of_forall hin)
  rw [hout, lintegral_mul_const _ hfa, mul_comm]

section SlabAbsPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

theorem slabAbsC_of (hW : PhWellDefC) (hSC : Formalism.L2.SG.Pf.Slab.SlabCoverC)
    (hR : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), X.LevelSubgroupNormalized → FoldReadyX X)
    (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), X.LevelSubgroupNormalized →
      NeatKu X u Y.hK) :
    SlabAbsC := by
  intro D X Y u u' hH Ωs hΩ T T' ρ
  obtain ⟨hKL, hOK, hOK', -⟩ := hH
  have hRX := hR D X hKL
  have hWD := hW D X Y u hKL
  have hWD' := hW D X Y u' hKL
  obtain ⟨⟨FS, hFS⟩, Ω₀, a, hc0, h10, hT⟩ := hOK
  obtain ⟨⟨F', hF'⟩, Ω₀', a', hc0', h10', hT'⟩ := hOK'
  have hΩc : IsCompact (Ω₀ ∪ Ω₀') := hc0.union hc0'
  have h1 : (1 : X.B.I.GA) ∈ Ω₀ ∪ Ω₀' := Or.inl h10
  have hFD := (hT T).1 _ hΩc Set.subset_union_left
  have hFD' := (hT' T').1 _ hΩc Set.subset_union_right
  have : LocallyCompactSpace X.B.I.GA := hRX.1
  have : SecondCountableTopology X.B.I.GA := hRX.2.1
  have : T2Space X.B.I.GA := hRX.2.2.1
  have : BorelSpace X.B.I.GA := hRX.2.2.2.1
  have : DiscreteTopology (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) := hRX.2.2.2.2
  have : Countable (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) := Formalism.L2.SG.Pf.countable_of_discrete _
  have : Countable (Srat X u) := Formalism.L2.SG.Pf.Slab.countable_of_le (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u) inf_le_left
  have : SigmaFinite X.B.μf := X.B.sf
  have : X.B.μf.IsHaarMeasure := X.B.haar
  have := @muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar
  have hD' : IsRightTransversal (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u') (Y.Dt u') := Y.reps u'
  have : Countable (Y.Dt u') := by
    have hinj : Function.Injective
        (fun d : Y.Dt u' => (⟨d.1, hD'.1 d.2⟩ : Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I)) := by
      intro d e h
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
    exact hinj.countable
  set ph := Ph X u Y.hK T with hph
  set ph' := Ph X u' Y.hK T' with hph'
  set g : X.B.I.GA → ℝ≥0∞ := fun x => ‖ph x‖ₑ * ∑' δ : Y.Dt u', ‖ph' ((δ : X.B.I.GA) * x)‖ₑ with hg
  have hgm : Measurable g :=
    hFD.1.enorm.mul (Measurable.tsum fun δ => hFD'.1.enorm.comp (measurable_const_mul _))

  have hb := foldBound_holds X.B.I.GA (X.B.I.muA X.B.μf) (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u')
    inferInstance inf_le_left (Ω₀ ∪ Ω₀') hΩc.isClosed.measurableSet a' ph' hFD'.1 hFD'.2.1 hFD'.2.2 F' hF'
    (Y.Dt u') hD'
  have hm1 : ∀ x, 1 ≤ mult (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Ω₀ ∪ Ω₀') x :=
    fun x => PI.FoldMult.UnitaryGroupMassFormula.one_le_mult _ _ h1 x
  have hq' : quotientLIntegral (X.B.I.muA X.B.μf) F' ph' ≠ ⊤ := by
    refine ne_top_of_le_ne_top ((hT' T').2 _ hΩc F' hF').ne (lintegral_mono fun y => ?_)
    calc ‖ph' y‖ₑ = 1 * ‖ph' y‖ₑ := (one_mul _).symm
      _ ≤ _ := by gcongr; exact hm1 y
  have hfinFS : ∫⁻ x in FS, g x ∂(X.B.I.muA X.B.μf) < ⊤ := by
    calc ∫⁻ x in FS, g x ∂(X.B.I.muA X.B.μf)
        ≤ ∫⁻ x in FS, ((a' : ℝ≥0∞) * quotientLIntegral (X.B.I.muA X.B.μf) F' ph') *
            (mult (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Ω₀ ∪ Ω₀') x * ‖ph x‖ₑ) ∂(X.B.I.muA X.B.μf) :=
          lintegral_mono fun x => by
            calc g x ≤ ‖ph x‖ₑ * ((a' : ℝ≥0∞) * mult (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Ω₀ ∪ Ω₀') x *
                  quotientLIntegral (X.B.I.muA X.B.μf) F' ph') := by
                  simp only [hg]; gcongr; exact hb x
              _ = _ := by ring
      _ = ((a' : ℝ≥0∞) * quotientLIntegral (X.B.I.muA X.B.μf) F' ph') *
            multiplicityLIntegral (X.B.I.muA X.B.μf) (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Ω₀ ∪ Ω₀') FS ph := by
          rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top hq')]
          rfl
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hq'.lt_top)
          ((hT T).2 _ hΩc FS hFS)

  have hgi : ∀ s ∈ Srat X u, ∀ y, g (s * y) = g y := by
    intro s hs y
    simp only [hg]
    rw [hFD.2.1 s hs y]
    congr 1
    have e := PI.FoldDCUnfold.W.translation_independent X.B.I.GA (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u')
      (Y.Dt u') (Y.Dt u') hD' hD' s (Subgroup.mem_inf.1 hs).1 (fun z => ‖ph' (z * y)‖ₑ)
      (fun t ht z => by simp only [mul_assoc]; rw [hFD'.2.1 t ht])
    simpa [mul_assoc] using e

  have hKm := level_subgroup_measurable X Y.hK hKL
  have hsm : MeasurableSet (slab (Y.cs u) ρ (Ωs ρ)) :=
    (hΩ ρ).1.prod ((MeasurableEquiv.mulLeft (aC (Y.cs u) ρ)).measurableSet_image.2 hKm)
  have huniq := (hSC D X Y u Ωs hKL (hN D X Y u hKL) hΩ).2
  have hslab := lintegral_le_of_uniq (X.B.I.muA X.B.μf) (Srat X u) FS hFS (slab (Y.cs u) ρ (Ωs ρ)) hsm g hgm
    hgi (fun y hy s hs hsy => (huniq ρ ρ y s hs hy hsy).1)

  have hK2 : ∀ y : X.B.I.Ginf, ∀ k ∈ X.K2, g (y, aC (Y.cs u) ρ * k) = g (y, aC (Y.cs u) ρ) := by
    intro y k hk
    have hyk : ((y, aC (Y.cs u) ρ * k) : X.B.I.GA) = (y, aC (Y.cs u) ρ) * (1, k) := by simp
    have hn : ‖X.chi2 k‖ₑ = 1 := by
      rw [← ofReal_norm, Y.hK.2.2.2.2 k hk, ENNReal.ofReal_one]
    simp only [hg]
    rw [hyk, hph, ph_right_K X u Y.hK hWD T _ k hk, enorm_mul, hn, one_mul]
    congr 1
    refine tsum_congr fun δ => ?_
    rw [hph', ← mul_assoc, ph_right_K X u' Y.hK hWD' T' _ k hk, enorm_mul, hn, one_mul]
  have hEq := lintegral_slab X.B.I X.B.μf X.K2 hKm (Ωs ρ) (hΩ ρ).1 (aC (Y.cs u) ρ) g hgm hK2
  have hlt : X.B.μf X.K2 * ∫⁻ y in Ωs ρ, g (y, aC (Y.cs u) ρ) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤ := by
    rw [← hEq]
    exact lt_of_le_of_lt hslab hfinFS
  have key : ∫⁻ y in Ωs ρ, g (y, aC (Y.cs u) ρ) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤ := by
    rcases ENNReal.mul_lt_top_iff.1 hlt with h | h | h
    · exact h.2
    · exact absurd h hKL.2.2.1.ne'
    · rw [h]; exact ENNReal.zero_lt_top
  exact key

end SlabAbsPf

end Formalism.L2.SG.Pf.RegroupPf
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfWellDef

section

@[expose] public section

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.BasicNotions

theorem phase_well_defined_all_words : PhWellDefC := fun _ X _ u _ => Formalism.L2.SG.Pf.phWellDef_holds X u

end Formalism.L2.SG.Pf.RegroupPf
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfFinal

section

@[expose] public section

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.BasicNotions

theorem regrouping_of_neatness (hSA : NStrongApproxC) (hO : OrbitAlgC) (hSC : Formalism.L2.SG.Pf.Slab.SlabCoverC)
    (hR : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), X.LevelSubgroupNormalized → Formalism.L2.SG.PoincareInHH.Cut.FoldReadyX X)
    (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word),
      X.LevelSubgroupNormalized → Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) :
    Formalism.L2.SG.Pf.Slab.RegroupC :=
  regrouping_of_closed_lemmas phase_well_defined_all_words column_uniqueness (colCoverC_of hSA) (slabAbsC_of phase_well_defined_all_words hSC hR hN) hO

end Formalism.L2.SG.Pf.RegroupPf
end
end
