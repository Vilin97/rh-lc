module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalThetaSecondVariableDiagonalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainTsumRationalTranslatesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRatPairFundamentalDomainAdelicIteratedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatDarbouxCoordsRationalMatrixIffRatPairStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumNormAdelicSchwartzRationalTranslatesLeStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsTransportCovolumeOneHaar

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

namespace GlobalTheory.DarbouxMeasure

theorem transport_covol_one : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)) ≃ₗ[AF D.host.F]
      (κ → AF D.host.F) × (κ → AF D.host.F)),
    (∀ w : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      w ∈ ratL T S ↔ e w ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) →
    ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
      Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
    letI : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
    ∃ (lam : MeasureTheory.Measure ((κ → AF D.host.F) × (κ → AF D.host.F)))
      (𝓖 : Set ((κ → AF D.host.F) × (κ → AF D.host.F))),
      lam.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) 𝓖 lam ∧
      lam 𝓖 = 1 ∧ ∀ g : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ,
        ∫ w in 𝓕, g (e w) ∂ν = ∫ p in 𝓖, g p ∂lam := by
  intro D S T κ _ e he ν 𝓕 hc
  letI mP : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
  haveI : BorelSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.IndefR.Datum.WO S T) := ⟨rfl⟩
  haveI : IsModuleTopology (AF D.host.F)
      (Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))) :=
    inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin T.rank → Fin S.rank → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)))
  obtain ⟨hH, hF, h1⟩ := hc
  have hc1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : Formalism.IndefR.Datum.WO S T ≃ₜ ((κ → AF D.host.F) × (κ → AF D.host.F)) :=
    { toEquiv := e.toEquiv, continuous_toFun := hc1, continuous_invFun := hc2 }
  let m := h.toMeasurableEquiv
  refine ⟨Measure.map m ν, m '' 𝓕, ?_, ?_, ?_, ?_⟩
  · exact AddEquiv.isAddHaarMeasure_map ν e.toAddEquiv hc1 hc2
  · let r : GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ ≃ ratL T S :=
      { toFun := fun p => ⟨e.symm p, (he (e.symm p)).2 (by simpa using p.2)⟩
        invFun := fun γ => ⟨e γ, (he γ).1 γ.2⟩
        left_inv := fun p => by ext1; simp
        right_inv := fun γ => by ext1; simp }
    refine hF.image_of_equiv m.toEquiv (m.measurePreserving_symm ν).quasiMeasurePreserving r ?_
    intro g x
    change e (e.symm (g : (κ → AF D.host.F) × (κ → AF D.host.F)) + x) = (g : (κ → AF D.host.F) × (κ → AF D.host.F)) + e x
    rw [map_add (f := _), LinearEquiv.apply_symm_apply]
  · rw [MeasurableEquiv.map_apply, Set.preimage_image_eq _ m.injective, h1]
  · intro g
    rw [m.measurableEmbedding.setIntegral_map, Set.preimage_image_eq _ m.injective]
    rfl

end GlobalTheory.DarbouxMeasure
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsTransportCovolumeOneHaarStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory


theorem _root_.GlobalTheory.T.darbouxCoords_transport_covolumeOne_haar : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)) ≃ₗ[AF D.host.F]
      (κ → AF D.host.F) × (κ → AF D.host.F)),
    (∀ w : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      w ∈ ratL T S ↔ e w ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) →
    ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
      Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
    letI : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
    ∃ (lam : MeasureTheory.Measure ((κ → AF D.host.F) × (κ → AF D.host.F)))
      (𝓖 : Set ((κ → AF D.host.F) × (κ → AF D.host.F))),
      lam.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) 𝓖 lam ∧
      lam 𝓖 = 1 ∧ ∀ g : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ,
        ∫ w in 𝓕, g (e w) ∂ν = ∫ p in 𝓖, g p ∂lam := by
  first | exact @GlobalTheory.DarbouxMeasure.transport_covol_one | exact GlobalTheory.DarbouxMeasure.transport_covol_one | (intros; apply GlobalTheory.DarbouxMeasure.transport_covol_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaSumRationalPairInvariant

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

namespace GlobalTheory.DiagThetaRatInv

theorem dot_elim {R : Type} [CommRing R] {κ : Type} [Fintype κ] (x : κ ⊕ κ → R) (v : κ → R) :
    x ⬝ᵥ Sum.elim v (-v) = ∑ i, (x (Sum.inl i) - x (Sum.inr i)) * v i := by
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg, sub_mul,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]
  simp only [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem schr_diag {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (u v : κ → R) (Φ : (κ ⊕ κ → R) → ℂ) (x : κ ⊕ κ → R) :
    GlobalTheory.WeilM.schr ψ (Sum.elim u u, Sum.elim v (-v)) Φ x =
      ψ (∑ i, (x (Sum.inl i) - x (Sum.inr i)) * v i) * Φ (x + Sum.elim u u) := by
  simp only [GlobalTheory.WeilM.schr]
  rw [dot_elim, dot_elim]
  simp

theorem diag_theta_rat_inv : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ]
    (Φ : (κ ⊕ κ → AF F) → ℂ), ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w : (κ → AF F) × (κ → AF F),
      GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim (γ + w).1 (γ + w).1, Sum.elim (γ + w).2 (-(γ + w).2)) Φ) =
        GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ) := by
  intro F _ _ ψ hψ κ _ Φ γ hγ w
  obtain ⟨a, b, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff γ).1 hγ
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [← (Equiv.subRight (Sum.elim a a)).tsum_eq]
  congr 1
  funext η
  rw [schr_diag, schr_diag]
  simp only [Equiv.subRight_apply, Prod.fst_add, Prod.snd_add]
  have h1 : (∑ i, (algebraMap F (AF F) ((η - Sum.elim a a) (Sum.inl i)) -
        algebraMap F (AF F) ((η - Sum.elim a a) (Sum.inr i))) * ((fun i => algebraMap F (AF F) (b i)) + w.2) i) =
      algebraMap F (AF F) (∑ i, (η (Sum.inl i) - η (Sum.inr i)) * b i) +
        ∑ i, (algebraMap F (AF F) (η (Sum.inl i)) - algebraMap F (AF F) (η (Sum.inr i))) * w.2 i := by

    rw [map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, map_sub, map_mul]
    ring
  have h2 : (fun i => algebraMap F (AF F) ((η - Sum.elim a a) i)) +
        Sum.elim ((fun i => algebraMap F (AF F) (a i)) + w.1) ((fun i => algebraMap F (AF F) (a i)) + w.1) =
      (fun i => algebraMap F (AF F) (η i)) + Sum.elim w.1 w.1 := by
    funext j
    cases j <;> simp <;> abel
  rw [h1, h2, AddChar.map_add_eq_mul, hψ.2.2.1, one_mul]

end GlobalTheory.DiagThetaRatInv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaSumRationalPairInvariantStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory


theorem _root_.GlobalTheory.T.diagonalThetaSum_rationalPair_invariant : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ]
    (Φ : (κ ⊕ κ → AF F) → ℂ), ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w : (κ → AF F) × (κ → AF F),
      GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim (γ + w).1 (γ + w).1, Sum.elim (γ + w).2 (-(γ + w).2)) Φ) =
        GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ) := by
  first | exact @GlobalTheory.DiagThetaRatInv.diag_theta_rat_inv | exact GlobalTheory.DiagThetaRatInv.diag_theta_rat_inv | (intros; apply GlobalTheory.DiagThetaRatInv.diag_theta_rat_inv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaIntegralEqNonzeroMulDiagonal

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagSiegelUnfold

open MeasureTheory



theorem diag_theta_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
            Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
          ∀ μ : @MeasureTheory.Measure (κ → AF D.host.F) (borel _),
            @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
            ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
              GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) =
                c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  intro D ψ hψ S T JA JB ξ hJA hJB κ _ co hrat ν 𝓕 hν μ hμ
  letI mV : MeasurableSpace (κ → AF D.host.F) := borel _
  haveI : BorelSpace (κ → AF D.host.F) := ⟨rfl⟩
  letI mVV : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
  haveI : BorelSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := ⟨rfl⟩
  have hψc : IsCharAF D.host.F ψ := hψ.1
  obtain ⟨lam, 𝓖, hlam, h𝓖, -, htr⟩ := GlobalTheory.T.darbouxCoords_transport_covolumeOne_haar D S T κ co.e (GlobalTheory.T.ratDarbouxCoords_rationalMatrix_iff_ratPair D S T κ co.e hrat) ν 𝓕 hν
  obtain ⟨𝓕₁, h𝓕₁, h0, htop⟩ := GlobalTheory.RatVecDomain.exists_fundamentalDomain D.host.F κ μ hμ
  obtain ⟨c₁, hc₁, hiter⟩ := GlobalTheory.T.integral_ratPairFundamentalDomain_adelic_iterated D.host.F κ μ hμ lam hlam 𝓖 h𝓖 𝓕₁ h𝓕₁ htop
  have hpos : 0 < μ.real 𝓕₁ := ENNReal.toReal_pos h0 htop
  refine ⟨((c₁ * μ.real 𝓕₁ : ℝ) : ℂ), Complex.ofReal_ne_zero.mpr (mul_pos hc₁ hpos).ne', fun Φ hΦ => ?_⟩

  set G : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ := fun p =>
    GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ (Sum.elim p.1 p.1, Sum.elim p.2 (-p.2)) Φ) with hGdef
  have hdiag : ∀ w, GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ (GlobalTheory.DiagSiegel.diagMat w) =
      G (co.e w) := by
    intro w
    have h1 : (GlobalTheory.DblSchr.ddr co).e (GlobalTheory.DiagSiegel.diagMat w) =
        (Sum.elim (co.e w).1 (co.e w).1, Sum.elim (co.e w).2 (-(co.e w).2)) := by
      rw [GlobalTheory.DblSchr.ddr, GlobalTheory.DblSchr.reD_e]
      have h2 : (GlobalTheory.DiagSiegel.diagMat w).submatrix id finSumFinEquiv.symm.symm = Matrix.fromCols w w := by
        ext i j
        simp only [GlobalTheory.DiagSiegel.diagMat, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.symm_apply_apply, id]
      rw [h2]
      rfl
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, h1, hGdef]

  obtain ⟨B, hB⟩ := GlobalTheory.T.tsum_norm_adelicSchwartz_rationalTranslates_le D.host.F (κ ⊕ κ) Φ hΦ
  have hsumΦ : ∀ z : κ ⊕ κ → AF D.host.F, Summable fun ξ : κ ⊕ κ → D.host.F =>
      ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + z)‖ := fun z => by
    have h1 := GlobalTheory.WeilM.summable_norm_of_mem_schA D.host.F (GlobalTheory.SchwartzTranslate.schA_translate D.host.F z hΦ)
    exact h1
  have hGbd : ∃ B : ℝ, ∀ w, ‖G w‖ ≤ B := by
    refine ⟨B, fun w => ?_⟩
    have hn : ∀ ξ : κ ⊕ κ → D.host.F, ‖GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ
        (fun i => algebraMap D.host.F (AF D.host.F) (ξ i))‖ =
        ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + Sum.elim w.1 w.1)‖ := by
      intro ξ
      simp only [GlobalTheory.WeilM.schr, norm_mul, hψc.2.1, one_mul]
    have hs : Summable fun ξ : κ ⊕ κ → D.host.F => ‖GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ
        (fun i => algebraMap D.host.F (AF D.host.F) (ξ i))‖ := by
      simp_rw [hn]
      exact hsumΦ _
    calc ‖G w‖ ≤ ∑' ξ : κ ⊕ κ → D.host.F, ‖GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ
          (fun i => algebraMap D.host.F (AF D.host.F) (ξ i))‖ := norm_tsum_le_tsum_norm hs
      _ = ∑' ξ : κ ⊕ κ → D.host.F, ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + Sum.elim w.1 w.1)‖ :=
          tsum_congr hn
      _ ≤ B := hB _
  have hGm : Measurable G := by
    letI mW : MeasurableSpace ((κ ⊕ κ → AF D.host.F) × (κ ⊕ κ → AF D.host.F)) := borel _
    haveI : BorelSpace ((κ ⊕ κ → AF D.host.F) × (κ ⊕ κ → AF D.host.F)) := ⟨rfl⟩
    have hm := GlobalTheory.ThetaTransformMeas.main D.host.F ψ hψc (κ ⊕ κ) Φ hΦ
    have hc : Continuous fun p : (κ → AF D.host.F) × (κ → AF D.host.F) =>
        ((Sum.elim p.1 p.1, Sum.elim p.2 (-p.2)) : (κ ⊕ κ → AF D.host.F) × (κ ⊕ κ → AF D.host.F)) := by
      refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun i => ?_) <;> rcases i with i | i
      · exact (continuous_apply i).comp continuous_fst
      · exact (continuous_apply i).comp continuous_fst
      · exact (continuous_apply i).comp continuous_snd
      · exact ((continuous_apply i).comp continuous_snd).neg
    exact hm.comp hc.measurable
  have hGper : ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ, ∀ w, G (γ + w) = G w :=
    fun γ hγ w => GlobalTheory.T.diagonalThetaSum_rationalPair_invariant D.host.F ψ hψc κ Φ γ hγ w

  set h : (κ → AF D.host.F) → ℂ := fun u => Φ (Sum.elim u u) with hhdef
  have hcont : Continuous h :=
    (GlobalTheory.ThetaUnfold.schA_continuous D.host.F hΦ).comp
      (continuous_pi fun i => by rcases i with i | i <;> exact continuous_apply i)
  have hhbd : ∃ B : ℝ, ∀ x : κ → AF D.host.F, Summable (fun η : κ → D.host.F =>
      ‖h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x)‖) ∧
      ∑' η : κ → D.host.F, ‖h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x)‖ ≤ B := by
    refine ⟨B, fun x => ?_⟩
    have hj : Function.Injective fun η : κ → D.host.F => (Sum.elim η η : κ ⊕ κ → D.host.F) := by
      intro η η' e
      funext i
      exact congrFun e (Sum.inl i)
    have key : ∀ η : κ → D.host.F, ‖h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x)‖ =
        ((fun ξ : κ ⊕ κ → D.host.F => ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + Sum.elim x x)‖) ∘
          fun η : κ → D.host.F => (Sum.elim η η : κ ⊕ κ → D.host.F)) η := by
      intro η
      simp only [hhdef, Function.comp_apply]
      congr 2
      funext i
      rcases i with i | i <;> rfl
    simp_rw [key]
    exact ⟨(hsumΦ _).comp_injective hj,
      (tsum_comp_le_tsum_of_inj (hsumΦ _) (fun _ => norm_nonneg _) hj).trans (hB _)⟩
  have hinner : ∀ x, ∫ y in 𝓕₁, G (x, y) ∂μ = (μ.real 𝓕₁ : ℂ) *
      ∑' η : κ → D.host.F, h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x) := by
    intro x
    exact GlobalTheory.T.integral_diagonalTheta_secondVariable_diagonal D.host.F ψ hψc κ μ hμ 𝓕₁ h𝓕₁ htop Φ hΦ x
  calc GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ)
      = ∫ w in 𝓕, G (co.e w) ∂ν := by
        unfold GlobalTheory.DiagSiegel.thetaDiagInt
        simp_rw [hdiag]
    _ = ∫ p in 𝓖, G p ∂lam := htr G
    _ = c₁ * ∫ x in 𝓕₁, ∫ y in 𝓕₁, G (x, y) ∂μ ∂μ := hiter G hGm hGper hGbd
    _ = c₁ * ((μ.real 𝓕₁ : ℂ) * ∫ u, h u ∂μ) := by
        simp_rw [hinner]
        rw [integral_const_mul, GlobalTheory.T.integral_fundamentalDomain_tsum_rationalTranslates D.host.F κ μ hμ 𝓕₁ h𝓕₁ htop h hcont hhbd]
    _ = ((c₁ * μ.real 𝓕₁ : ℝ) : ℂ) * GlobalTheory.DiagSiegel.diagInt μ Φ := by
        push_cast
        rw [mul_assoc]
        rfl

end GlobalTheory.DiagSiegelUnfold

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaIntegralEqNonzeroMulDiagonalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.diagonalThetaIntegral_eq_nonzero_mul_diagonal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
            Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
          ∀ μ : @MeasureTheory.Measure (κ → AF D.host.F) (borel _),
            @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
            ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
              GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) =
                c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  first | exact @GlobalTheory.DiagSiegelUnfold.diag_theta_integral | exact GlobalTheory.DiagSiegelUnfold.diag_theta_integral | (intros; apply GlobalTheory.DiagSiegelUnfold.diag_theta_integral <;> assumption)
end
end
