module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Placed
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.QuotientMetricDivisors.Statement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstIsotropicVectorCoordinatesNeZeroStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselTranslateVector
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LineIndepStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SdYFramesStatement
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatSmulSingle

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitMultipliersLineInMovedLatticeSplit

section

@[expose] public section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.LineIdeal

open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}

theorem exists_dominant {k : ℕ} (f : Fin k → Fv F v) (hf : ∃ j, f j ≠ 0) :
    ∃ j, f j ≠ 0 ∧ ∀ c : Fv F v,
      (∀ i, c * f i ∈ v.adicCompletionIntegers F) ↔ c * f j ∈ v.adicCompletionIntegers F := by
  obtain ⟨j0, hj0⟩ := hf
  haveI : Nonempty (Fin k) := ⟨j0⟩
  obtain ⟨j, hj⟩ := Finite.exists_max fun i => ‖f i‖₊
  refine ⟨j, fun h0 => hj0 ?_, fun c => ⟨fun h => h j, fun h i => ?_⟩⟩
  · have := hj j0
    rw [h0, nnnorm_zero] at this
    exact nnnorm_eq_zero.1 (le_antisymm this zero_le)
  · rw [← nnnorm_le_one_iff_mem] at h ⊢
    rw [nnnorm_mul] at h ⊢
    exact (mul_le_mul_of_nonneg_left (hj i) zero_le).trans h

theorem exists_unit_gen (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {k : ℕ} {u l : Fin k → Fv F v ⊗[F] E}
    (hl : ∑ j, l j * u j = 1) :
    ∃ α : (Fv F v ⊗[F] E)ˣ, ∀ c : Fv F v ⊗[F] E,
      (∀ j, c * u j ∈ intLoc F E v) ↔ ((α⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * c ∈ intLoc F E v := by
  have hne : ∀ ρ : E →ₐ[F] Fv F v, ∃ j, splitProj ρ (u j) ≠ 0 := fun ρ => by
    by_contra hc
    push_neg at hc
    have := congrArg (splitProj ρ) hl

    rw [map_sum, map_one, Finset.sum_eq_zero fun j _ => by rw [map_mul, hc j, mul_zero]] at this
    exact zero_ne_one this
  obtain ⟨j1, h1, hj1⟩ := exists_dominant (fun j => splitProj τ (u j)) (hne τ)
  obtain ⟨j2, h2, hj2⟩ := exists_dominant (fun j => splitProj (τ.comp σ) (u j)) (hne _)
  beta_reduce at h1 h2 hj1 hj2
  refine ⟨⟨(splitAlgEquiv h τ).symm ((splitProj τ (u j1))⁻¹, (splitProj (τ.comp σ) (u j2))⁻¹),
    (splitAlgEquiv h τ).symm (splitProj τ (u j1), splitProj (τ.comp σ) (u j2)), ?_, ?_⟩, fun c => ?_⟩
  · rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel₀ h1, inv_mul_cancel₀ h2]
    exact map_one _
  · rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel₀ h1, mul_inv_cancel₀ h2]
    exact map_one _
  · show _ ↔ (splitAlgEquiv h τ).symm (splitProj τ (u j1), splitProj (τ.comp σ) (u j2)) * c ∈ intLoc F E v
    simp only [mem_intLoc_iff_split h τ, map_mul, splitProj_symm, splitProj_comp_symm, forall_and]
    rw [hj1 (splitProj τ c), hj2 (splitProj (τ.comp σ) c), mul_comm (splitProj τ c),
      mul_comm (splitProj (τ.comp σ) c)]

end Local



theorem exists_unit_mult_latLoc : ∀ (D : D7) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)), Nonempty (D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) → ∀ (n : ℕ) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Submodule.IsFullLattice D.host.E L → ∀ (g : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)) (ε : Fin n → D.host.E), ε ≠ 0 → ∃ α : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, Matrix.mulVec g.val (c • fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] ε i) ∈ GlobalTheory.AdelicU.latLoc D.host.F L v ↔ ((α⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) * c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
  intro D v hτ n L hL g ε hε
  obtain ⟨τ⟩ := hτ
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := SelfDual.exists_frame L hL
  have h2 := SelfDual.map_mul_eq_one (F := D.host.F) (Fv D.host.F v) h1
  let w : Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E := g.val *ᵥ fun i => (1 : Fv D.host.F v) ⊗ₜ[D.host.F] ε i
  obtain ⟨l, hl⟩ : ∃ l : Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E, l ⬝ᵥ w = 1 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hε
    refine ⟨Pi.single i ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (ε i)⁻¹) ᵥ* (g⁻¹ : GL (Fin n) _).val, ?_⟩
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, single_dotProduct,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ (by simpa using hi)]
    rfl
  let u := Φ.map (inclR (F := D.host.F) (Fv D.host.F v)) *ᵥ w
  have hl' : ∑ j, (l ᵥ* S.map (inclR (F := D.host.F) (Fv D.host.F v))) j * u j = 1 := by
    change (l ᵥ* _) ⬝ᵥ u = 1
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, hl]
  have key : ∀ a : Fv D.host.F v ⊗[D.host.F] D.host.E,
      a • w ∈ latLoc D.host.F L v ↔ ∀ j, a * u j ∈ intLoc D.host.F D.host.E v := fun a => by
    rw [SelfDual.mem_latLoc_iff_of_frame h1 hS hΦ v, Matrix.mulVec_smul]
    rfl
  obtain ⟨α, hα⟩ := exists_unit_gen (isCMExt_host D) τ hl'
  refine ⟨α, fun c => ?_⟩
  have hcw : g.val *ᵥ (c • fun i => (1 : Fv D.host.F v) ⊗ₜ[D.host.F] ε i) = c • w := Matrix.mulVec_smul _ _ _
  rw [hcw, key, hα]

end GlobalTheory.LineIdeal

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitMultipliersLineInMovedLatticeSplitStatement

section

@[expose] public section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.exists_unit_multipliers_line_in_movedLattice_split : ∀ (D : D7) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)), Nonempty (D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) → ∀ (n : ℕ) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Submodule.IsFullLattice D.host.E L → ∀ (g : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)) (ε : Fin n → D.host.E), ε ≠ 0 → ∃ α : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, Matrix.mulVec g.val (c • fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] ε i) ∈ GlobalTheory.AdelicU.latLoc D.host.F L v ↔ ((α⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) * c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
  first | exact @GlobalTheory.LineIdeal.exists_unit_mult_latLoc | exact GlobalTheory.LineIdeal.exists_unit_mult_latLoc | (intros; apply GlobalTheory.LineIdeal.exists_unit_mult_latLoc <;> first | assumption | (letI := ‹Submodule.IsFullLattice _ _›; infer_instance))
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlaceFrameExists

section

@[expose] public section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section

namespace GlobalTheory.LineAtG



theorem mem_latLoc_line_iff {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (L : GlobalTheory.FinPl.Lat V) (hL : L.FG) (v : GlobalTheory.FinPl.Pl D) (t : GA D V)
    (ε : Fin V.rank → D.host.E) (y : AE D) (hy : y ∈ GlobalTheory.FinPl.idAt D (· = v)) :
    Matrix.mulVec ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig V.gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v t))⁻¹).val
        (GlobalTheory.AdelicU.vecLoc v (finPart D ∘ fun _ : Fin 1 => y) 0 • fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] ε i) ∈
        GlobalTheory.AdelicU.latLoc D.host.F L v ↔
      Matrix.mulVec (Formalism.L2.Theta.mt V t⁻¹) (fun i => y * Formalism.L2.Theta.incA D (ε i)) ∈ GlobalTheory.FinPl.latV V L (· = v) := by
  have hy' : ∀ i, (fun i => y * Formalism.L2.Theta.incA D (ε i)) i ∈ GlobalTheory.FinPl.idAt D (· = v) := fun i => Ideal.mul_mem_right _ _ hy
  rw [GlobalTheory.StMoves.mem_latV_iff_latLoc V L hL v _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ t⁻¹ hy'), GlobalTheory.FinPl.KOpen.fin_mulVec,
    GlobalTheory.AdelicU.vecLoc_mulVec, map_inv, map_inv]
  have hv : GlobalTheory.AdelicU.vecLoc v (finPart D ∘ fun i => y * Formalism.L2.Theta.incA D (ε i)) =
      GlobalTheory.AdelicU.vecLoc v (finPart D ∘ fun _ : Fin 1 => y) 0 • fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] ε i := by
    funext i
    simp only [Function.comp, GlobalTheory.AdelicU.vecLoc, Pi.smul_apply, smul_eq_mul, map_mul]
    congr 1
  rw [hv]


end GlobalTheory.LineAtG
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TOfFixFirst

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.LineAtG
theorem tOf_fix_first_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) (hr : 1 ≤ D.R.rS) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (a₀ a : GA D (D.sp.X 0)) (c : AE D) :
    Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)⁻¹) (fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) =
      Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) (fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) := by
  have hId : GlobalTheory.Core.Mi.IdE W.S.X := hW.bot.idE
  set v0 : Fin (D.sp.Y 0).rank → AE D := fun i => Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩
    (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))) with hv0
  have hv : (fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) = c • v0 := rfl
  rw [hv]
  set x : GA D (D.sp.Y 0) := (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) with hxdef
  set E : GA D (D.sp.Y 0) := embA B.d B.o (a₀ * a) with hEdef
  set b : GA D (D.sp.Y 0) := (show GA D (D.sp.Y 0) from f.g.b 0) with hbdef
  have hx : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) x) v0 = v0 := by
    refine GlobalTheory.MiTop.fixAux W.S.X W.Q.instEq hId {W.S.X.eR ⟨0, hr⟩} _ rfl x ?_
    have e : iotaX W.S.X W.Q.instEq x = (1, W.S.X.xu u) := (iotaX W.S.X W.Q.instEq).apply_symm_apply _
    rw [e]
    refine ⟨Subgroup.one_mem _, ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (W.S.X.xu_fix u ⟨0, hr⟩).1
  have hE : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) E⁻¹) v0 = v0 := by
    refine GlobalTheory.MiTop.fixAux W.S.X W.Q.instEq hId (Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet W.S.X u) (W.S.X.eR ⟨0, hr⟩) (Or.inl (Or.inl ⟨⟨0, hr⟩, rfl⟩)) E⁻¹ ?_
    exact (B.tieH E⁻¹).1 ((embA B.d B.o).range.inv_mem ⟨a₀ * a, rfl⟩)
  have e : (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)⁻¹ = b⁻¹ * (E⁻¹ * x) := by
    show (x⁻¹ * E * b)⁻¹ = _
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  rw [e]
  show Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹ * (Formalism.L2.Theta.mt (D.sp.Y 0) E⁻¹ * Formalism.L2.Theta.mt (D.sp.Y 0) x)) (c • v0) = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul, hx, hE]

theorem line_atG_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v) → ∃ (e : Fin (D.sp.Y 0).rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) (α : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, Matrix.mulVec ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)))⁻¹).val (c • e) ∈ GlobalTheory.AdelicU.latLoc D.host.F ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v ↔ ((α⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) * c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr v hv
  refine ⟨fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)), ?_⟩
  by_cases hex : ∃ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B ∧ ∃ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a
  · obtain ⟨u₀, f₀, B₀, hP₀, b₀₀, b₀₁, hA₀⟩ := hex
    obtain ⟨hτ, hm⟩ : Nonempty (D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ∧ 0 < D.R.m := by
      obtain ⟨PP, hPP, rfl⟩ := hv
      obtain ⟨k, _, _, _, _, ι, v', o, n, G, pl, -, -, -, -, -, hGR, -⟩ := hP₀
      have hs := (G (pl.symm ⟨PP, hPP⟩)).hs
      refine ⟨?_, by omega⟩
      obtain ⟨w, τ, -, hw⟩ := GlobalTheory.AdelicU.Supp.isIdemAt_iff_exists.1 (hGR.idem (pl.symm ⟨PP, hPP⟩)).1
      rw [Equiv.apply_symm_apply] at hw
      change PP = GlobalTheory.AdelicU.splitPrime τ at hw
      subst hw
      rw [GlobalTheory.AdelicU.splitPrime_under]
      exact ⟨τ⟩
    have hΛ := (_root_.GlobalTheory.T.selfDual_and_frame_of_pkHyp W hW 0 hm).1
    haveI : Submodule.IsLattice D.host.E ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) := hΛ.1
    have hfg : ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0).FG := Submodule.IsLattice.fg (A := D.host.E) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0)
    obtain ⟨α, hα⟩ := GlobalTheory.T.exists_unit_multipliers_line_in_movedLattice_split D v hτ _ ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0)
      (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hΛ)
      ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (_root_.GlobalTheory.MiTop.translationElement f₀ B₀ b₀₀ b₀₁)))⁻¹) _ (GlobalTheory.T.firstIsotropicVector_coordinates_ne_zero W.S.X W.Q.instEq hr)
    refine ⟨α, fun u f B hP a₀ a hA c => ?_⟩
    rw [← hα c]
    obtain ⟨y, hy, hyc⟩ := GlobalTheory.StMoves.exists_supp_vecLoc_eq (D := D) (n := 1) v fun _ => c
    have hc : GlobalTheory.AdelicU.vecLoc v (finPart D ∘ fun _ : Fin 1 => y 0) 0 = c := congrFun hyc 0
    rw [← hc]
    refine (mem_latLoc_line_iff (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) hfg v _ (fun i => W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))) (y 0) (hy 0)).trans
      (Iff.trans ?_ (mem_latLoc_line_iff (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) hfg v _ (fun i => W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))) (y 0) (hy 0)).symm)
    beta_reduce
    rw [_root_.GlobalTheory.LineAtG.tOf_fix_first_alt W hW hr, _root_.GlobalTheory.LineAtG.tOf_fix_first_alt W hW hr]
    exact _root_.GlobalTheory.T.placed_bessel_pair_central_alt W hW hr u u₀ f f₀ B B₀ hP hP₀ a₀ a b₀₀ b₀₁ hA hA₀ v hv (y 0) (hy 0)
  · exact ⟨1, fun u f B hP a₀ a hA c => absurd ⟨u, f, B, hP, a₀, a, hA⟩ hex⟩
end GlobalTheory.LineAtG
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TOfFixFirstStatement

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.level_place_frame_exists_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v) → ∃ (e : Fin (D.sp.Y 0).rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) (α : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, Matrix.mulVec ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)))⁻¹).val (c • e) ∈ GlobalTheory.AdelicU.latLoc D.host.F ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v ↔ ((α⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) * c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
  first | exact @_root_.GlobalTheory.LineAtG.line_atG_alt | exact _root_.GlobalTheory.LineAtG.line_atG_alt | (intros; apply _root_.GlobalTheory.LineAtG.line_atG_alt <;> assumption)
end
end
end
