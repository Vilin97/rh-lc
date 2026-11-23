module

public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMatchHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameActionMulEquivFiniteAdelicUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralFiniteAdeleIsoCommutesWithConjugation
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivariantUnitaryCoefficientMapOntoStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LatExistsOfSteps
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimitiveVectorNormNegHyperbolicPairStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedDegreeOneOfNcardPlacesOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LevelConjHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MExistsHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlaceFunctionBlockExistsOfBesselCoef
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RescaleStep3
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExistsHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcExistsAll

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

theorem hcExists_all : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), HcExists D F := by
  intro D F X u wt ιA h0 hW hA c
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.frameAction_mulEquiv_finiteAdelic_unitary D X u wt ιA hW hA (GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hA)
  exact ⟨Φ.symm ((F u).cls0.y c * h0⁻¹), (hΦ _ _).2 (Φ.apply_symm_apply _)⟩

end GlobalTheory.St.G
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.JExistsAll

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem jExists_all : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), JExists D F := by
  intro D F X u wt hw
  obtain ⟨J, hJ, -⟩ := GlobalTheory.T.exists_equivariant_unitary_coefficientMap_onto D X u (F u) wt hw
  exact ⟨J, hJ⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsotropicOrthHyp

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoOrthHyp

open Matrix

theorem exists_norm_one {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (n : ℕ) (h : S.rank = n)
    (hn : 0 < n) (C : GL (Fin n) E)
    (hC : (C.1.map (starRingEnd E))ᵀ * C.1 = S.gram.reindex (finCongr h) (finCongr h)) :
    ∃ x : S.V, S.hT x x = 1 := by
  classical
  set e : Fin S.rank ≃ Fin n := finCongr h with he
  set M : Matrix (Fin n) (Fin n) E := ((C⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hM
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  refine ⟨∑ j : Fin n, M j i₀ • S.frame (e.symm j), ?_⟩
  have hCM : C.1 * M = 1 := by
    rw [hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hstar : (C.1.map (starRingEnd E))ᵀ = C.1ᴴ := rfl
  have hprod : Mᴴ * S.gram.reindex e e * M = (C.1 * M)ᴴ * (C.1 * M) := by
    rw [← hC, hstar, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have key : (Mᴴ * S.gram.reindex e e * M) i₀ i₀ = 1 := by
    rw [hprod, hCM]
    simp
  rw [← key]

  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
  Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
  HSpace.gram, starRingEnd_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, RingHom.id_apply]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem star_eq_hostConj (D : D7) (x : D.host.E) : starRingEnd D.host.E x = D.host.conj x := by
  have := D.host.isCMField_hostE
  obtain ⟨ψ⟩ := (inferInstance : Nonempty (D.host.E →+* ℂ))
  apply ψ.injective
  have h1 : ∀ y, ψ (D.host.conj y) = starRingEnd ℂ (ψ y) :=
    (D.host.der.conj_iff ψ D.host.conj).2 (MulEquiv.apply_symm_apply _ _)
  rw [h1]
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E ψ x

theorem exists_isotropic_orth_hyp : ∀ (D : D7), Formalism.L2.Forms.Forms0 D D.u₀ → ∃ w : (VS D).V, w ≠ 0 ∧ (VS D).hT w w = 0 ∧ ∀ i, (VS D).hT (D.sp.hypE i) w = 0 ∧ (VS D).hT (D.sp.hypF i) w = 0 := by
  intro D hF
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hi : (0 : ℕ) ≤ D.R.m := Nat.zero_le _
  obtain ⟨C, hC, -⟩ := hF.val0.de
  have hN : 0 < D.R.N 0 := by
    show 0 < D.R.k + 0 * (D.R.t + 1)
    have := D.R.m_add_three_le_k
    omega
  have hC' : (C.1.map (starRingEnd D.host.E))ᵀ * C.1 =
      (D.sp.X 0).gram.reindex (finCongr (Formalism.L2.Forms.rankN D 0 hi))
        (finCongr (Formalism.L2.Forms.rankN D 0 hi)) := hC
  obtain ⟨x, hx⟩ := exists_norm_one (D.sp.X 0) (D.R.N 0) (Formalism.L2.Forms.rankN D 0 hi) hN C hC'
  have hπ : (hF.atT.piU : D.host.E) * D.host.conj (hF.atT.piU : D.host.E) =
      ((D.mem D.u₀).A.T : D.host.E) := hF.atT.piU_norm
  have hT0 : ((D.mem D.u₀).A.T : D.host.E) ≠ 0 := by
    rw [← D.sp_T]
    exact_mod_cast D.sp.T_prime.ne_zero
  have hsym : ∀ a b : (VS D).V, (VS D).hT a b = 0 → (VS D).hT b a = 0 := by
    intro a b hab
    rw [← (VS D).herm.eq a b, hab, map_zero]
  have hvv : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x))
      (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x)) = ((D.mem D.u₀).A.T : D.host.E) := by
    rw [D.sp.iXY_isom 0 hm]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hx, mul_one, RingHom.id_apply,
      star_eq_hostConj]
    linear_combination hπ
  have hvz : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x)) D.sp.zm = 0 := D.sp.zm_orth _
  have hzv := hsym _ _ hvz
  have hzz : (VS D).hT D.sp.zm D.sp.zm = -((D.mem D.u₀).A.T : D.host.E) := by
    rw [D.sp.zm_norm, D.sp_T]
  refine ⟨D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x) + D.sp.zm, ?_, ?_, ?_⟩
  · intro h0
    have h1 : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x) + D.sp.zm) D.sp.zm = 0 := by
      rw [h0, map_zero, LinearMap.zero_apply]
    rw [map_add (f := _), LinearMap.add_apply, hvz, hzz, zero_add, neg_eq_zero] at h1
    exact hT0 h1
  · simp only [map_add (f := _), LinearMap.add_apply, hvv, hvz, hzv, hzz]
    ring
  · intro i
    constructor
    · rw [map_add (f := _), hsym _ _ (D.sp.hyp_orthX i _).1, hsym _ _ (D.sp.hyp_orthz i).1, add_zero]
    · rw [map_add (f := _), hsym _ _ (D.sp.hyp_orthX i _).2, hsym _ _ (D.sp.hyp_orthz i).2, add_zero]

end GlobalTheory.IsoOrthHyp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatExistsOfForms0

section

@[expose] public section

open Formalism.BasicNotions Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.St.Lat

theorem latExists_of_forms0 : ∀ D : D7, Formalism.L2.Forms.Forms0 D D.u₀ → LatExists D := by
  intro D hF
  refine GlobalTheory.St.Lat.latExists_of ?_ ?_ D ?_
  · exact GlobalTheory.T.exists_primitive_vector_norm_neg_hyperbolicPair
  · exact GlobalTheory.unramified_degree_one_of_ncard_placesOver
  · exact GlobalTheory.IsoOrthHyp.exists_isotropic_orth_hyp D hF

end GlobalTheory.St.Lat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalSetting

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.ColDict

namespace GlobalTheory.St.SpectralData

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_transport {D : D7} (F : ∀ u, Formalism.L2.Forms.Forms0 D u)
    (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (hι : ∃ ιA, GlobalTheory.St.IsAdeleIso X ιA) (u : D.what₂.Word) :
    ∃ Tr : Transport X u (F u), LevelMatch X Tr hK := by
  obtain ⟨wt, hw⟩ := GlobalTheory.St.WittT.wittExists D X u
  obtain ⟨ιA, hι⟩ := hι
  obtain ⟨g0, hg0⟩ := GlobalTheory.St.G.genusMatch_holds D F X u wt ιA hw hι
  obtain ⟨h0, hL, hKm⟩ := GlobalTheory.St.G.levelConj_holds D F X hK u wt ιA g0 hw hι hg0
  choose hcf hcr using GlobalTheory.St.G.hcExists_all D F X u wt ιA h0 hw hι
  obtain ⟨J, hJ1, hJ2, hJ3⟩ := GlobalTheory.jExists_all D F X u wt hw
  exact ⟨⟨wt, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, ιA, hι.1, hι.2, h0, hcf, hcr, J, hJ1, hJ2, hJ3⟩, hL, hKm⟩


open Formalism.L2.SG.SplitPrimeNormLemmas in
theorem exists_setting (hSW : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent)
    (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) :
      ∃ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D ∧
        (∀ x : X.B.I.E, HEq (X.ιE x) x) ∧ X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧
        Formalism.L2.SG.LocVol.IsStdChar ψ ∧
        Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧
        ∀ hK : X.LevelSubgroupCharacter, ∀ u, ∃ Tr : Transport X u (F u), LevelMatch X Tr hK := by
  have hB : BesselNVGap := Formalism.L2.SG.Closed.BesselNVGap_holds
  have hC : CoefWeightedLoc := Formalism.L2.SG.Closed.CoefWeightedLoc_holds
  let A := Formalism.L2.SG.InstExistsPf.instanceOfRecord D
  obtain ⟨L⟩ := GlobalTheory.St.Lat.latExists_of_forms0 D (F D.u₀)
  obtain ⟨P⟩ := Formalism.L2.SG.Closed.PsiExists_holds D A
  obtain ⟨Rf⟩ := Formalism.L2.SG.Closed.RefExists_holds D A L
  obtain ⟨Xu⟩ := Formalism.L2.SG.Closed.XuExists_holds D A L Rf
  obtain ⟨Bu⟩ := Formalism.L2.SG.Closed.BunExists_holds D hC hG A L P Rf
  obtain ⟨Pi⟩ := Formalism.L2.SG.Closed.PiExists_holds D A L
  obtain ⟨Mu⟩ := Formalism.L2.SG.Closed.MuExists_holds D A L
  obtain ⟨Wb⟩ := GlobalTheory.WBlockExists.realPlaceFunctionBlockExists_of_bessel_coef hB hC D hG A L P Rf Bu Pi Mu
  obtain ⟨Mb, hb, hM⟩ := GlobalTheory.St.mExists_holds D A L P Rf Xu Bu Pi Mu Wb
  obtain ⟨mg, hg, mw, hw, hM', ψ, hψ, hstd, hCm, hL⟩ :=
    GlobalTheory.St.Rescale.rescaleStep3 hSW D (mk A L P Rf Xu Bu Pi Mu Wb Mb) hb hM
  refine ⟨Formalism.L2.SG.SettingExistsMeasured.withMeas (mk A L P Rf Xu Bu Pi Mu Wb Mb) mg hg mw hw, hb, ψ, rfl,
    fun _ => HEq.rfl, hM', hψ, hstd, hCm, hL, fun hK u => ?_⟩
  exact exists_transport F _ hK ⟨RingEquiv.refl _, fun _ => rfl, fun _ => Iff.rfl⟩ u

end GlobalTheory.St.SpectralData
end
end
end
