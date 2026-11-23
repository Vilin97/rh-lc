module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulLeOfIsConjPl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetIndicatorReadsAsTranslateCurveTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairBigMemberTwistedTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterFiniteIdeleValueEqStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealIndicatorReadsNormPowMulIntertwinedVacuum
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddEigenvectorUniqueUpToUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddEisensteinRatioAlgebraicUnitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstConjEqSumCosetIndicatorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDetCharacterIntegralFramePowEqOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionIntegralPointCosetVectorEqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqNegOfCommute
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealIndicatorReadsNormPowMulIntertwinedVacuumStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead


theorem _root_.GlobalTheory.T.idealIndicator_reads_norm_pow_mul_intertwinedVacuum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
  D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 → ∀ v : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (stdL D S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) v →
  ∀ G ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d), Reads ψ θ hS hT ⊤ δ 1 G v → ∀ (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 →
  ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) 1 v Tm →
  Reads ψ θ hS hT ⊤ δ 1 (cosV δ 𝔪 0 G) (Tm (cosInd e 𝔪 hS hT 0)) := by
  first | exact @GlobalTheory.IopRead.indicator_reads | exact GlobalTheory.IopRead.indicator_reads | (intros; apply GlobalTheory.IopRead.indicator_reads <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigenStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead


theorem _root_.GlobalTheory.T.integral_action_unit_character_eigen : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 →
  ∀ ν : (AE D)ˣ →* Circle, HasFinPart ν⁻¹ P.W.chV' P.W.ep' → KillsCong ν 𝔪 →
  ∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a, k ∈ intG D P.a → P.W.Om k 1 P.e0 = unitChar ν e (matE k) • P.e0 := by
  first | exact @GlobalTheory.StdRead.CharVal.om_vac_eq | exact GlobalTheory.StdRead.CharVal.om_vac_eq | (intros; apply GlobalTheory.StdRead.CharVal.om_vac_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixFrameCompletedStandardLattice

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

open scoped TensorProduct

namespace GlobalTheory.StdRead

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem int_of_mem_hatL_pi {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E))) (i : Fin n) :
    z i ∈ Formalism.L2.Herm.intAf F E := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hy i (Set.mem_univ i))
    exact Subring.subset_closure (Or.inl ⟨⟨y i, b, hb⟩, rfl⟩)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact mul_mem a.2 hx

theorem single_mem_hatL_pi (j : Fin n) :
    (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.L2.Herm.hatL (F := F) (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS
  refine Submodule.subset_span ⟨Pi.single j 1, fun i _ => ?_, funext fun i => ?_⟩
  · by_cases h : i = j
    · subst h
      rw [Pi.single_eq_same]
      exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]
      exact zero_mem _
  · by_cases h : i = j
    · subst h
      simp only [Pi.single_eq_same, map_one]
    · simp only [Pi.single_eq_of_ne h, map_zero]

theorem entries_int_of_isFrame_pi (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hβ : Formalism.L2.DIV.IsFrame β (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E))) :
    (∀ i j, β.val i j ∈ Formalism.L2.Herm.intAf F E) ∧ ∀ i j, (β⁻¹).val i j ∈ Formalism.L2.Herm.intAf F E := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have h1 : Matrix.mulVec β.1 (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
        Formalism.L2.Herm.hatL (F := F) (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
      refine (hβ _).2 fun l => ?_
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      exact int_of_mem_hatL_pi (single_mem_hatL_pi j) l
    have h2 := int_of_mem_hatL_pi h1 i
    rwa [Matrix.mulVec_single_one] at h2
  · have h2 := (hβ _).1 (single_mem_hatL_pi j) i
    rwa [Matrix.mulVec_single_one] at h2

end Gen

theorem isIntM_of_isFrame_stdL : ∀ {D : D7} {n : ℕ} (β : GL (Fin n) (EAf D)),
    Formalism.L2.DIV.IsFrame β (stdL D n) → IsIntM β.val ∧ IsIntM (β⁻¹).val :=
  fun β hβ => entries_int_of_isFrame_pi β hβ

end GlobalTheory.StdRead
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixFrameCompletedStandardLatticeStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead


theorem _root_.GlobalTheory.T.isIntegralMatrix_frame_completedStandardLattice : ∀ {D : D7} {n : ℕ} (β : GL (Fin n) (EAf D)), Formalism.L2.DIV.IsFrame β (stdL D n) → IsIntM β.val ∧ IsIntM (β⁻¹).val := by
  first | exact @GlobalTheory.StdRead.isIntM_of_isFrame_stdL | exact GlobalTheory.StdRead.isIntM_of_isFrame_stdL | (intros; apply GlobalTheory.StdRead.isIntM_of_isFrame_stdL <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleUnitConstant

section

@[expose] public section

noncomputable section

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.StdRead

variable {D : D7}

theorem xiN_eq {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {a d : ℕ}
    (hS : S.rank = a) (hT : T.rank = d) {δ : ℂ} (hs : δ ≠ 0) {G : VC D a d → ℂ} {f : WO S T → ℂ}
    (h : Reads ψ θ hS hT ⊤ δ 1 G f) :
    GlobalTheory.AdForm.xiN θ S T hS hT (-δ) (Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ))⁻¹ f = G := by
  funext z
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have hsp : ∀ Z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ,
      (GlobalTheory.AdForm.realPt θ Z).map (finPart D) = 0 ∧ ∀ τ, compAt θ τ (GlobalTheory.AdForm.realPt θ Z) = Z τ := fun Z => by
    refine Classical.epsilon_spec (p := fun w : Mx D T.rank S.rank => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = Z τ)
      ⟨Matrix.of fun i j => σ fun τ => Z τ i j, ?_, fun τ => ?_⟩
    · ext i j; exact hσ.fin _
    · ext i j; exact hσ.comp _ _
  unfold GlobalTheory.AdForm.xiN
  obtain ⟨h1, h2⟩ := hsp fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))
  have hY : GlobalTheory.NormExact.coordY θ hS hT δ 1 (GlobalTheory.AdForm.realPt θ
      fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))) = z := by
    funext τ i j
    unfold GlobalTheory.NormExact.coordY
    rw [h2, map_one, mul_one, Matrix.of_apply, inv_neg, neg_mul, neg_neg, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    rfl
  rw [h.2 _ h1, hY, ← mul_assoc, ← Complex.exp_add]
  have hH : Formalism.L2.Ker.HV (Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ))⁻¹ z z = Formalism.MainNotions.TaylorLogMetric.Hf D (tor0 D ⊤ δ) z z := by
    change (((Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ))⁻¹ : ℝ) : ℂ) * _ = _ / ((Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ) : ℝ) : ℂ)
    rw [div_eq_inv_mul, Complex.ofReal_inv]
  rw [hH, neg_mul, add_neg_cancel, Complex.exp_zero, one_mul]

theorem reads_sum {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d}
    {δ : ℂ} {ι : Type} (R : Finset ι) (G : ι → VC D a d → ℂ) (f : ι → WO S T → ℂ)
    (h : ∀ r ∈ R, Reads ψ θ hS hT ⊤ δ 1 (G r) (f r)) : Reads ψ θ hS hT ⊤ δ 1 (∑ r ∈ R, G r) (∑ r ∈ R, f r) := by
  induction R using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact (h x (Finset.mem_insert_self _ _)).add (ih fun r hr => h r (Finset.mem_insert_of_mem hr))

def IsPh (u : ℂ) : Prop := ‖u‖ = 1 ∧ u ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam u‖ = 1

theorem IsPh.mul {u v : ℂ} (hu : IsPh u) (hv : IsPh v) : IsPh (u * v) :=
  ⟨by rw [norm_mul, hu.1, hv.1, mul_one], mul_mem hu.2.1 hv.2.1, fun p _ lam => by
    rw [GlobalTheory.BotFormula.lamC_mul lam hu.2.1 hv.2.1, norm_mul, hu.2.2, hv.2.2, mul_one]⟩

theorem lamC_one {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : lamC lam 1 = 1 := by
  unfold lamC
  rw [dite_eq_left (one_mem _)]
  exact map_one lam

theorem IsPh.conj {u : ℂ} (hu : IsPh u) : IsPh (starRingEnd ℂ u) := by
  have h0 : u ≠ 0 := fun h => by simpa [h] using hu.1
  have e : starRingEnd ℂ u = u⁻¹ := (Complex.inv_eq_conj hu.1).symm
  refine ⟨by rw [Complex.norm_conj, hu.1], e ▸ inv_mem hu.2.1, fun p _ lam => ?_⟩
  have h := GlobalTheory.BotFormula.lamC_mul lam hu.2.1 (inv_mem hu.2.1)
  rw [mul_inv_cancel₀ h0, lamC_one] at h
  have h2 := congrArg norm h
  rw [norm_mul, hu.2.2, norm_one, one_mul] at h2
  rw [e, ← h2]

theorem isPh_of_pow {u : ℂ} {m : ℕ} (hm : 0 < m) (h : u ^ m = 1) : IsPh u := by
  have hQ : u ∈ Qbar := by
    rw [mem_algebraicClosure_iff]
    exact (IsIntegral.of_pow hm (h ▸ isIntegral_one)).isAlgebraic
  refine ⟨(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 (by rw [← norm_pow, h, norm_one]), hQ, fun p _ lam => ?_⟩
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 ?_
  unfold lamC
  rw [dite_eq_left hQ, ← norm_pow, ← map_pow, show (⟨u, hQ⟩ : Qbar) ^ m = 1 from Subtype.ext h, map_one, norm_one]

theorem exists_const (hI : GlobalTheory.NormSum.Inp D) (δ t0 : ℂ) {a d : ℕ} (G : VC D a d → ℂ)
    (hG : G ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d)) (h0 : G ≠ 0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ e0, Crv D ⊤ δ → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → oddE0 D ⊤ δ t0 a d e0 → e0 ≠ 0 →
      ∃ u, IsPh u ∧ G = (κ * u) • e0 := by
  by_cases hex : ∃ e1, Crv D ⊤ δ ∧ oddE0 D ⊤ δ t0 a d e1 ∧ e1 ≠ 0
  · obtain ⟨e1, hC, h1, hne⟩ := hex
    have k0 := GlobalTheory.NormSum.VacMove.klat (D := D) (tor0 D ⊤ δ) (GlobalTheory.NormSum.VacMove.moves_one D a)
      (GlobalTheory.NormSum.VacMove.moves_one D d)
    obtain ⟨hline, -⟩ := GlobalTheory.ThetaLine.theta_line D hI.g1 ⊤ δ hC a d _ k0
    obtain ⟨κ, hκ⟩ := hline G hG e1 h1.1 hne
    refine ⟨κ, fun h => h0 (by rw [hκ, h, zero_smul]), fun e0 _ ht he hn => ?_⟩
    obtain ⟨u, hu, e⟩ := GlobalTheory.VacuumUnique.vacuum_unique hI hC he h1 hn
    obtain ⟨a1, a2⟩ := GlobalTheory.T.odd_eisenstein_ratio_algebraic_unit hI hC ht he h1 hn u e
    exact ⟨u, ⟨hu, a1, a2⟩, by rw [hκ, e, smul_smul]⟩
  · exact ⟨1, one_ne_zero, fun e0 hC _ he hn => absurd ⟨e0, hC, he, hn⟩ hex⟩

theorem reads_std (hI : GlobalTheory.NormSum.Inp D) {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {S T : HSp D} (hS : S.rank = P.a) (hT : T.rank = P.d) (hcc : D.host.ccK = ⊤) (hs : Setup ψ θ S T ⊤ δ 1) {v f : WO S T → ℂ}
    (hv : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) v)
    {c : ℂ} (hc : c • P.e0 ∈ Th D (tor0 D ⊤ δ) (stdL D P.a) (stdL D P.d)) (hr : Reads ψ θ hS hT ⊤ δ 1 (c • P.e0) v)
    {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (hm : GoodMod e 𝔪) {ν : (AE D)ˣ →* Circle} (hν : HasFinPart ν⁻¹ P.W.chV' P.W.ep')
    (hk : KillsCong ν 𝔪) {β : GL (Fin S.rank) (EAf D)} (hβ : Formalism.L2.DIV.IsFrame β (stdL D S.rank))
    (hstd : GlobalTheory.FunObj.SqNum.IsStdDatum P 𝔪 0) {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) 1 v Tm)
    (hf : f = Tm fun w => starRingEnd ℂ (stdFst ν e 𝔪 S T β 1 w)) :
    ∃ u, IsPh u ∧ Reads ψ θ hS hT ⊤ δ 1 ((c * u) • P.F) f := by
  obtain ⟨R, hR1, hR2, hF⟩ := hstd
  obtain ⟨b1, b2⟩ := GlobalTheory.T.isIntegralMatrix_frame_completedStandardLattice β hβ
  obtain ⟨m, hm0, hpow⟩ := GlobalTheory.T.unitDetCharacter_integralFrame_pow_eq_one e 𝔪 hm ν hk β b1 b2
  choose! z hz using fun (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (hk : k ∈ intG D P.a) => exists_approx hm.ne_bot 0 P.d hk
  have hz' : ∀ r ∈ R, IsIntE (z r) ∧ Approx 𝔪 0 r (z r) := fun r hr => hz r (hR1 r hr)
  have h0 := GlobalTheory.T.idealIndicator_reads_norm_pow_mul_intertwinedVacuum ψ θ S T hS hT δ hcc hs v hv _ hc hr e 𝔪 hm Tm hTm
  have h1 := GlobalTheory.T.cosetIndicator_reads_as_translate_curveTheta ψ θ S T hS hT δ hcc hs v hv _ hc hr e 𝔪 hm Tm hTm h0
  refine ⟨_, (isPh_of_pow hm0 hpow).conj, ?_⟩

  rw [hf, GlobalTheory.T.standardPairFirst_conj_eq_sum_cosetIndicators S T hS hT P.a_le e 𝔪 hm ν hk β b1 b2 R hR1 hR2 z hz', map_smul, map_sum, mul_comm c, mul_smul, hF,
  Finset.smul_sum]
  refine Reads.smul (reads_sum R _ _ fun r hr => ?_) _
  rw [GlobalTheory.T.weilAction_integralPoint_cosetVector_eq hI P hm.ne_bot 0 r (hR1 r hr) _ (GlobalTheory.T.integral_action_unit_character_eigen hI P e 𝔪 hm ν hν hk r (hR1 r hr)) (z r) (hz' r hr).1 (hz' r hr).2,
    map_smul, smul_comm c, ← cosV_smul]
  exact (h1 (z r) (hz' r hr).1).smul _

variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}


open GlobalTheory.FunObj.SqNum GlobalTheory.FunObj.StdDatum GlobalTheory.Mem.Col2.SplitChar in
theorem killsCong {μ₀ : T} (hL : L.Is μ₀) (G : GlobalTheory.ChiGrid.GridData L sc) (t : T) (i j : Fin D.R.m) :
    KillsCong (G.nu t i (j + 1)) (GlobalTheory.SqTop.modT G t) := by
  intro x u hxu hu hm
  have hle := Ideal.mul_mono (TwBig.modT_le_condE G t) (TwBig.conj_smul_mono (TwBig.modT_le_condE G t))
  have h1 := TwBig.nuInv_base_eq_one hL G i j u hu (TwBig.hatId_mono hle hm)
  have h2 := GlobalTheory.BotPairSmall.CondXi.xiH_eq_one_of_cong hL G t u hu hm
  have e : nuH G t i j = nuH G μ₀ i j * L.xiH t := by
    show L.C.mu0 j * L.xiH t / G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH μ₀ / G.ch.chiH (D.R.m - i) * L.xiH t
    rw [hL.xi_base, mul_one, mul_div_right_comm]
  have h3 := GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ (chrEq_nu G t i j hL) x u hxu
  have e1 : (nuH G μ₀ i j * L.xiH t).1 (finIdl D u) = (nuH G μ₀ i j).1 (finIdl D u) * (L.xiH t).1 (finIdl D u) := rfl
  have e2 : (nuH G μ₀ i j).1 (finIdl D u) = 1 := inv_eq_one.1 h1
  rw [e, e1, e2, h2, mul_one] at h3
  exact Circle.coe_injective (by simpa using h3)

end GlobalTheory.StdRead

end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdRead

end GlobalTheory.StdRead

end
end
end
end
