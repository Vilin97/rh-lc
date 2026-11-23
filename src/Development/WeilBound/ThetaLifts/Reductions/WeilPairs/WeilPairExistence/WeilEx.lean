module

public import Development.WeilBound.ThetaLifts.TowerModels.PlaneHerm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroConjNegOfCmExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermitianNondegenerateNegTraceZeroSmulInvSkewHStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramSkewHermitianSignatureStatement
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticPowOfRestrictsToQuadraticSig
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
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.RowsStackRight
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportWeilDatumCmExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOnWeilDatumTransportAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumCMPreservesSchwartzHeisenberStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTransportCmPreservesAdmissibleFormsStatement
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.TargetDoubling
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledTargetWeilTransportRestrictFirstFactorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalLagrangianInvariantFormUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainRationalMatricesTower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilSectionLawDiagonalLagrangian
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairExistence.ExistsIsWeilDatumOF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairExistence.ExistsIsWeilDatumOF
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticPowOfRestrictsToQuadraticSigStatement

section

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.restrictsToQuadraticPow_of_restrictsToQuadraticSignPow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (χ : (AF F ⊗[F] E)ˣ →* Circle) (n : ℕ),
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n → Formalism.IndefR.DatumF.ResEtaF χ n := by
  first | exact @GlobalTheory.ResEtaFOfPow.resEtaF_of_resEtaPow | exact GlobalTheory.ResEtaFOfPow.resEtaF_of_resEtaPow | (intros; apply GlobalTheory.ResEtaFOfPow.resEtaF_of_resEtaPow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilSectionLawDiagonalLagrangianStatement

section

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
theorem _root_.GlobalTheory.T.siegelWeil_section_law_diagonalLagrangian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.ResEtaF χS nS →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
          Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
            Module.End ℂ ((κ → AF F) → ℂ),
          GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ωd omp →
      ∀ (p : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)) (t : GL (Fin nT) (AF F ⊗[F] E)),
        p.1.1 * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
      ∀ Φ ∈ schA F κ, omp (p, 1) Φ ∈ schA F κ ∧
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (omp (p, 1) Φ)) =
          (χS (Matrix.GeneralLinearGroup.det t) : ℂ) *
            ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
              (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) *
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  first | exact @GlobalTheory.SiegelLawDblTargetF.main_law | exact GlobalTheory.SiegelLawDblTargetF.main_law | (intros; apply GlobalTheory.SiegelLawDblTargetF.main_law <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumDoubledTargetSiegelRule

section

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

theorem GlobalTheory.WeilSchrodinger.DblTargetF.siegelRule_dblTarget : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.ResEtaF χS nS →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
        ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
          Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
        ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
            Module.End ℂ ((κ → AF F) → ℂ),
          GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ωd omp →
          SiegelRule (cA σ) (adeleClass F) B.ψ ξ (incM F JB) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)
            (GlobalTheory.WeilSchrodinger.transD (cA σ) co) χS
            ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)
            (omp.comp (MonoidHom.inl _ _)) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS hχS rχS JB ξ hξ κ _ co hco ωd hωd omp htr
  intro l hl hinv p t hpt φ hφ
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := GlobalTheory.TowerFD.exists_fd_any F E nS nT
  obtain ⟨c, hc⟩ := GlobalTheory.T.diagonalLagrangian_invariantForm_unique F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ JB ξ hξ κ co hco ν 𝓕 hν h𝓕 l hl hinv
  obtain ⟨hmem, hrule⟩ := GlobalTheory.T.siegelWeil_section_law_diagonalLagrangian F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ JB ξ hξ κ co hco ν 𝓕 hν h𝓕 χS hχS rχS
    ωd hωd omp htr p t hpt φ hφ
  show l (omp (p, 1) φ) = _
  rw [hc _ hmem, hrule, hc _ hφ]
  ring

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumDoubledTargetSiegelRuleStatement

section

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.weilDatum_doubledTarget_siegelRule : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.ResEtaF χS nS →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
        ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
          Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
        ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
            Module.End ℂ ((κ → AF F) → ℂ),
          GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ωd omp →
          SiegelRule (cA σ) (adeleClass F) B.ψ ξ (incM F JB) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)
            (GlobalTheory.WeilSchrodinger.transD (cA σ) co) χS
            ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)
            (omp.comp (MonoidHom.inl _ _)) := by
  first | exact @GlobalTheory.WeilSchrodinger.DblTargetF.siegelRule_dblTarget | exact GlobalTheory.WeilSchrodinger.DblTargetF.siegelRule_dblTarget | (intros; apply GlobalTheory.WeilSchrodinger.DblTargetF.siegelRule_dblTarget <;> assumption)
end
end

-- Source module: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairExistence.ExistsDblTarget

section

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace PositivityTheory.ThKW.S

theorem exists_dbl_target : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → PositivityTheory.ThKW.LatH σ JS JT ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
              ∃ (dd : Darboux (symp (cA σ) ξ (incM F JB) (dbl (incM F JA))) (κ ⊕ κ))
                (omd : UG (cA σ) (dbl (incM F JA)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)),
                IsDblCoord (cA σ) ξ (incM F JB) (incM F JA) (GlobalTheory.WeilSchrodinger.transD (cA σ) co) dd ∧
                IsUWeilSplit (cA σ) (adeleClass F) B.ψ ξ (incM F JB) (dbl (incM F JA)) dd χS (diagCols (Fin nT)) omd ∧
                ∀ (g : UG (cA σ) (incM F JA)) (gd : UG (cA σ) (dbl (incM F JA))),
                  gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                  ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omd gd (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ hLat χS χT hS hT rS rT ω hω JA JB ξ hA hBm κ _ co hrat om hom
  have h2 : Module.finrank F E = 2 := hB.cm.2.2.1
  have hJTd := GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hJT
  have h1 := GlobalTheory.WeilSchrodinger.DblTargetF.isHeckeCharF_one (F := F) (E := E)
  have r1 := GlobalTheory.WeilSchrodinger.DblTargetF.resEtaF_one_dbl h2 rT
  obtain ⟨ωd, hωd⟩ := PositivityTheory.ThKW.S.exists_isWeilDatumOF F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ (PositivityTheory.ThKW.LatH.dblT hLat) χS 1 hS h1 rS r1
  have hrat' := GlobalTheory.WeilSchrodinger.DblTargetF.coDbl_rat hA co hrat
  obtain ⟨omp, hmp⟩ := GlobalTheory.T.exists_weilTransport_adelicSchwartz_cmExtension F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ χS 1 hS h1 rS r1 ωd hωd _ JB ξ rfl
    hBm (κ ⊕ κ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat'
  have k2 := GlobalTheory.T.transportedWeilDatum_CM_preserves_schwartz_heisenberg F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ χS 1 hS h1 rS r1 ωd hωd _ JB ξ rfl
    hBm (κ ⊕ κ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat' omp hmp
  have k3 := GlobalTheory.T.weilDatumTransport_cm_preserves_admissibleForms F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ χS 1 hS h1 rS r1 ωd hωd _ JB ξ rfl
    hBm (κ ⊕ κ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat' omp hmp
  have k4 := GlobalTheory.T.isUnitaryOn_weilDatum_transport_adelicSchwartz F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ χS 1 hS h1 rS r1 ωd hωd _ JB ξ rfl
    hBm (κ ⊕ κ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat' omp hmp
  have k5 := GlobalTheory.T.continuous_transport_weil_datum_cm_extension F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ χS 1 hS h1 rS r1 ωd hωd _ JB ξ rfl
    hBm (κ ⊕ κ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat' omp hmp
  have hsp : IsUSplitting (adeleClass F) B.ψ (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) (actAB (cA σ)) omp :=
    ⟨⟨k2.1, k2.2, k3⟩, k4, k5⟩
  have hsg := GlobalTheory.T.weilDatum_doubledTarget_siegelRule F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS hS rS JB ξ hBm (κ ⊕ κ)
    (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat' ωd hωd omp hmp
  have t1 := GlobalTheory.WeilSchrodinger.DblTarget.isDblCoord_transD co
  have t2 : IsLagr (cA σ) (dbl (incM F JA)) (diagCols (Fin nT)) := isLagr_diagCols _ _
  have t4 := GlobalTheory.WeilSchrodinger.DblTarget.isUSplitting_reindex finSumFinEquiv
    (GlobalTheory.WeilSchrodinger.DblTarget.dblRows co) _ (GlobalTheory.WeilSchrodinger.DblTargetF.reindex_dbl_incM hA)
    (GlobalTheory.WeilSchrodinger.isUSplitting_inl hsp)
  have t5 := GlobalTheory.WeilSchrodinger.DblTarget.siegelRule_reindex finSumFinEquiv
    (GlobalTheory.WeilSchrodinger.DblTarget.dblRows co) _ (GlobalTheory.WeilSchrodinger.DblTargetF.reindex_dbl_incM hA) χS _ hsg
  refine ⟨_, _, t1, ⟨t2, t4, t5⟩, ?_⟩
  intro g gd hgd φ₁ hφ₁ φ₂ hφ₂
  have key := GlobalTheory.T.doubled_target_weil_transport_restrict_first_factor F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω hω JA JB ξ hA hBm κ co hrat om hom
    ωd hωd omp hmp g (GlobalTheory.WeilSchrodinger.DblTargetF.ugDbl hA gd)
    (by rw [GlobalTheory.WeilSchrodinger.DblTargetF.ugDbl_coe, hgd]) φ₁ hφ₁ φ₂ hφ₂
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.inl_apply]
  exact key

end PositivityTheory.ThKW.S

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairExistence.ExistsIsUWeilPairCm

section

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem PositivityTheory.ThKW.S.exists_isUWeilPair_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → PositivityTheory.ThKW.LatH σ JS JT ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω, Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∃ om, IsUWeilPair (cA σ) (adeleClass F) B.ψ ξ (incM F JA) (incM F JB) co χT χS om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ hLat χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ _ co hrat
  obtain ⟨om, hom⟩ := GlobalTheory.T.exists_weilTransport_adelicSchwartz_cmExtension F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ co hrat
  have h2 := GlobalTheory.T.transportedWeilDatum_CM_preserves_schwartz_heisenberg F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ co hrat om hom
  have h3 := GlobalTheory.T.weilDatumTransport_cm_preserves_admissibleForms F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ co hrat om hom
  have h4 := GlobalTheory.T.isUnitaryOn_weilDatum_transport_adelicSchwartz F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ co hrat om hom
  have h5 := GlobalTheory.T.continuous_transport_weil_datum_cm_extension F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ co hrat om hom
  have h6 := PositivityTheory.ThKW.dblS_of_dblT PositivityTheory.ThKW.S.exists_dbl_target F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ hLat χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ co hrat om hom
  have h7 := PositivityTheory.ThKW.S.exists_dbl_target F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ hLat χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ co hrat om hom
  have hsp : IsUSplitting (adeleClass F) B.ψ co (actAB (cA σ)) om := ⟨⟨h2.1, h2.2, h3⟩, h4, h5⟩
  exact ⟨om, ⟨GlobalTheory.WeilSchrodinger.isUSplitting_inr hsp, h6⟩,
    ⟨GlobalTheory.WeilSchrodinger.transD _ co, GlobalTheory.WeilSchrodinger.transD_e co, GlobalTheory.WeilSchrodinger.isUSplitting_inl hsp, h7⟩, h5⟩
end
end

-- Source module: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairExistence.WeilEx

section

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace PositivityTheory.ThKW.S

theorem exists_isWeil : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∀ M : Model σ X W, M.IsGood B.ψ →
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → ∃ om, M.IsWeil B.ψ χX χW om := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW M hM χX χW hcX hcW rX rW
  obtain ⟨ξ₀, hξ, hσξ⟩ := GlobalTheory.T.exists_ne_zero_conj_neg_of_cmExtension F E σ B hB
  have hXu := GlobalTheory.T.isUnit_det_gram_of_hermitianSelfDualLatticeSpace F E σ B n X r s hX
  have hWu := GlobalTheory.T.isUnit_det_gram_skewHermitian_signature F E σ B d W r' s' hW
  have hT : IsHermND σ X.Jᵀ := ⟨fun i j => by simpa using hX.herm j i, by rw [Matrix.det_transpose]; exact hXu.ne_zero⟩
  have hS : IsHermND σ (-ξ₀ • W.J⁻¹) := GlobalTheory.T.isHermitianNondegenerate_neg_traceZero_smul_inv_skewHermitian F E σ d W.J hW.skew hWu ξ₀ hξ hσξ
  have hLat : PositivityTheory.ThKW.LatH σ (-ξ₀ • W.J⁻¹) X.Jᵀ ξ₀ := PositivityTheory.ThKW.latH_of hB.cm hX hW hXu hWu hξ
  obtain ⟨ω, hω⟩ := PositivityTheory.ThKW.S.exists_isWeilDatumOF F E σ B hB d n (-ξ₀ • W.J⁻¹) X.Jᵀ hS hT ξ₀ hξ hσξ hLat χW χX hcW hcX
    (GlobalTheory.T.restrictsToQuadraticPow_of_restrictsToQuadraticSignPow F E σ B hB χW d rW) (GlobalTheory.T.restrictsToQuadraticPow_of_restrictsToQuadraticSignPow F E σ B hB χX n rX)
  have eB : (-1 : AF F ⊗[F] E) • incM F W.J = incM F (ξ₀ • (-ξ₀ • W.J⁻¹)⁻¹) := by
    have e1 : (-ξ₀ • W.J⁻¹)⁻¹ = (-ξ₀)⁻¹ • W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hWu,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
    have e2 : ξ₀ • (-ξ₀)⁻¹ • W.J = -W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    rw [e1, e2]
    funext i j
    simp [incM]
  exact PositivityTheory.ThKW.S.exists_isUWeilPair_cm F E σ B hB d n (-ξ₀ • W.J⁻¹) X.Jᵀ hS hT ξ₀ hξ hσξ hLat χW χX hcW hcX
    (GlobalTheory.T.restrictsToQuadraticPow_of_restrictsToQuadraticSignPow F E σ B hB χW d rW) (GlobalTheory.T.restrictsToQuadraticPow_of_restrictsToQuadraticSignPow F E σ B hB χX n rX) ω hω X.J W.J (-1) (by simp) eB
    (Fin n × Fin d) M.co hM.rat

theorem weilEx : PositivityTheory.ThKG.Tow.WeilEx := exists_isWeil

end PositivityTheory.ThKW.S

end
end
end
