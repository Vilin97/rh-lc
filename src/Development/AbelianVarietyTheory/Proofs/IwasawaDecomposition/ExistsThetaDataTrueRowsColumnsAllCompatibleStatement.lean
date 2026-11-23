module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAllTiedEqTiedOnOfRealised
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfFam
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueIsStdChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueNormalizedHaarMeasureAdelicUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneTupleRowsCuspFormsIsometricThetaLifts
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
import Mathlib.Tactic.ReduceModChar
public import Formalism.LocalToGlobal.JointCharacters.SameChr
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMkTauE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakCompatibilityOfRealRowSideAdelicChainStatement
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilEq

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneTupleRowsCuspFormsIsometricThetaLiftsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.oneTuple_rows_cuspForms_isometric_thetaLifts : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsChain → ∀ (t : T) (μ : D.what₂.Tup), (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC t j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX t) (R.fdX t) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY t j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX t (eX y')).1 (e (D.R.m - 1) x).1) → ∀ (Wf : WeilFun D R.ψ) (κ : ℕ → ℝ), (∀ j, 0 < κ j) → ∃ (row : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j)) (Phi : ∀ j, ThS R.ψ (D.sp.Y (j + 1)) (D.sp.Y j)), (∀ j, j < D.R.m → Phi j ≠ 0) ∧ (∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun h => star ((row j x).1 h) * (row j y).1 h) (inner ℂ x y)) ∧ ∀ j, j < D.R.m → ∀ y : D.what₂.Mult μ (j + 1), ∃ L : GA D (D.sp.Y j) → ℂ, (∀ g, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y (j + 1)) (κ (j + 1)) (fun h => Wf.ker _ _ (if Even (j + 1) then R.toLevCh.mu t (j + 1) * R.eta⁻¹ else R.toLevCh.mu t (j + 1)) (if Even j then R.toLevCh.mu t (j + 1) * R.eta⁻¹ else R.toLevCh.mu t (j + 1)) (Phi j) h g * (row (j + 1) y).1 h) (L g)) ∧ ∀ x : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun g => star (L g) * (row j x).1 g) (inner ℂ (D.what₂.io μ j y) x) := by
  first | exact @GlobalTheory.Mem.OneTuple.rows_theta | exact GlobalTheory.Mem.OneTuple.rows_theta | (intros; apply GlobalTheory.Mem.OneTuple.rows_theta <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionLevelDataOfEqualTuplesZeroIntertwiners

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.RowsTies

theorem isQuotInt_zero {D : D7} (V : HSp D) (hV : V.SigOK) (c : ℝ) {φ : GA D V → ℂ} (h : ∀ g, φ g = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V c φ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨μ, hμ, -⟩ := GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG D V hV
  obtain ⟨-, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ.1
  have e : φ = fun _ => 0 := funext h
  subst e
  exact ⟨⟨(μ, 𝓕), ⟨hμ, h𝓕⟩⟩, fun m _ => ⟨integrableOn_zero, by simp⟩⟩

theorem rows_of_ties : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsChain → ∀ (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) (U : Set D.what₂.Tup) (tupT : D.what₂.Tup → T), (∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n) → (∀ μ, (xi μ).TrivOn D.host.F) → (∀ μ ∈ U, R.xiH (tupT μ) = xi μ ∧ (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC (tupT μ) j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ)) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY (tupT μ) j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX (tupT μ) (eX y')).1 (e (D.R.m - 1) x).1)) → (∀ μ, μ ∉ U → ∀ j, j < D.R.m → D.what₂.io μ j = 0) → (∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ, ∃ Rc : RecFun D θ ψ, Rc.ChrIs R.C xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y)) := by
  intro hD D G _ _ Pl0 T A Ks _ _ _ R hL hM hC xi U tupT hf ht hU hoff θ hθ ψ hψ Wf
  obtain rfl : θ = R.θ := (GlobalTheory.Mem.InfFamUnique.existsUnique_infFam D).unique hθ hM.inf
  obtain rfl : ψ = R.ψ := (GlobalTheory.StdAdelicChar.existsUnique_isStdChar D (-1) (Or.inr rfl)).unique hψ (hC.ωX A.μ0).std
  obtain ⟨Rc, hR⟩ := RecFun.exists_chrIs R.C xi hf ht R.θ R.ψ
  have hu := (GlobalTheory.ChrEqUnique.chrEq_unique D).2.1
  have he : Rc.eta = R.eta := hu _ _ _ hR.eta hL.eta
  have key : ∀ μ, ∃ (row : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j)) (Phi : ∀ j, ThS R.ψ (D.sp.Y (j + 1)) (D.sp.Y j)),
      (∀ j, j < D.R.m → Phi j ≠ 0) ∧
      (μ ∈ U → ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j,
        GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j))
          (fun h => star ((row j x).1 h) * (row j y).1 h) (inner ℂ x y)) ∧
      ∀ j, j < D.R.m → ∀ y : D.what₂.Mult μ (j + 1), ∃ L : GA D (D.sp.Y j) → ℂ,
        (∀ g, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y (j + 1)) (Rc.mY μ (j + 1) * Rc.petC (D.sp.Y (j + 1)))
          (fun h => Wf.ker _ _ (Rc.carY μ (j + 1) (j + 1)) (Rc.carY μ (j + 1) j) (Phi j) h g *
            (row (j + 1) y).1 h) (L g)) ∧
        ∀ x : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j))
          (fun g => star (L g) * (row j x).1 g) (inner ℂ (D.what₂.io μ j y) x) := fun μ => by
    by_cases hμ : μ ∈ U
    · obtain ⟨hx, hT⟩ := hU μ hμ
      have hc : ∀ j, j < D.R.m → Rc.chr μ (j + 1) = R.toLevCh.mu (tupT μ) (j + 1) := fun j hj =>
        hu _ _ _ (hR.chr μ ⟨j, hj⟩) (hx ▸ GlobalTheory.Mem.TupChar.chrEq_mul (hL.mu0 ⟨j, hj⟩) (hL.xi (tupT μ)))
      obtain ⟨row, Phi, h1, h2, h3⟩ := GlobalTheory.T.oneTuple_rows_cuspForms_isometric_thetaLifts hD D G Pl0 T A Ks R hL hM hC (tupT μ) μ hT Wf
        (fun j => Rc.mY μ j * Rc.petC (D.sp.Y j)) fun j =>
          mul_pos (Rc.mY_pos _ _) (mul_pos (Rc.petF_pos _) (Finset.prod_pos fun _ _ => Rc.meas.petR_pos _ _))
      refine ⟨row, Phi, h1, fun _ => h2, fun j hj y => ?_⟩
      unfold RecFun.carY
      rw [hc j hj, he]
      exact h3 j hj y
    · refine ⟨0, Rc.Phi μ, Rc.Phi_ne hψ μ, fun h => absurd h hμ, fun j hj y => ⟨0, fun g => ?_, fun x => ?_⟩⟩
      · exact isQuotInt_zero _ (D.sp.Y_sig _) _ fun h => by simp
      · rw [hoff μ hμ j hj]
        simpa using isQuotInt_zero _ (D.sp.Y_sig _) _ fun h => by simp
  choose row Phi h1 h2 h3 using key
  exact ⟨{ Rc with row := row, Phi := Phi, Phi_ne := fun _ => h1 }, ⟨hR.chr, hR.eta⟩, h3, h2⟩

end GlobalTheory.Mem.RowsTies
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionLevelDataOfEqualTuplesZeroIntertwinersStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.functionLevelData_of_equal_tuples_zero_intertwiners : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsChain → ∀ (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) (U : Set D.what₂.Tup) (tupT : D.what₂.Tup → T), (∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n) → (∀ μ, (xi μ).TrivOn D.host.F) → (∀ μ ∈ U, R.xiH (tupT μ) = xi μ ∧ (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC (tupT μ) j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ)) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY (tupT μ) j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX (tupT μ) (eX y')).1 (e (D.R.m - 1) x).1)) → (∀ μ, μ ∉ U → ∀ j, j < D.R.m → D.what₂.io μ j = 0) → (∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ, ∃ Rc : RecFun D θ ψ, Rc.ChrIs R.C xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y)) := by
  first | exact @GlobalTheory.Mem.RowsTies.rows_of_ties | exact GlobalTheory.Mem.RowsTies.rows_of_ties | (intros; apply GlobalTheory.Mem.RowsTies.rows_of_ties <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameChrOfChrEq

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SameChrFin

theorem sameChr_of_chrEq : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch) (X : ThetaX D)
    (T : ThetaTied D X) (H : Formalism.L2.Host.ThetaChrTied D C nch Tp X),
    (∀ c, Formalism.IndefR.Links.ChrEq (T.eChr c) (H.eChr c)) → Formalism.L2.JoinChr.SameChr T H := by
  intro D C nch Tp X T H h
  refine ⟨fun P => ?_, fun c P e he k x hx => (h c).2 P e he k x hx,
    fun θ hθ c τ k x hx => GlobalTheory.CharInfPlace.chrEq_infLoc D (T.eChr c) (H.eChr c) (h c) θ hθ τ k x hx⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  exact ⟨e, he⟩

end GlobalTheory.SameChrFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilTiedEqOfEqTied

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem weilTiedEq_of_eqTied : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (W : WeilTied D X T), WeilThetaCompatibility W → WeilCompatibleEquivariance W :=
  fun _ _ _ _ h => ⟨h.range, h.Heisenberg₂, h.aut, h.cont, h.unit, h.split, ⟨h.twW, h.twV⟩, h.th⟩

end GlobalTheory.Mem.Th
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaDataTrueRowsColumnsAllCompatible

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaRecordTrue

theorem recFun_of_rows (hR : GlobalTheory.Published.CuspRapidDecay) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (what₂ : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch)
    (hio : ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0) :
    ∀ θ : InfF (w.D Z), IsInfFam θ → ∀ ψ, IsStdChar (w.D Z) ψ (-1) → ∀ Wf : WeilFun (w.D Z) ψ,
      ∃ Rc : RecFun (w.D Z) θ ψ, Rc.ChrIs (TC.cf w.I w.l Z) n.tp.xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ}, ∀ j, j ≤ (w.D Z).R.m → ∀ x y : (w.D Z).what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt ((w.D Z).sp.Y j) (Rc.mY μ j * Rc.petC ((w.D Z).sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y) := by
  intro θ hθ ψ hψ Wf
  letI : Algebra what₂.r.z.core.Q.c.F (w.D Z).what₂.LL := what₂.r.z.alg
  have h3 := Formalism.IndefR.Links.RealDat3.characterisation_of_weak what₂.r.z.pins.char what₂.exAt
  have hC : what₂.r.z.R.toRealDat.C = TC.cf w.I w.l Z := what₂.r.z.lev.C
  obtain ⟨Rc, h1, h2, h4⟩ := GlobalTheory.T.functionLevelData_of_equal_tuples_zero_intertwiners hR (w.D Z) _ _ _ _ _ what₂.r.z.R.toRealDat h3.lev h3.models h3.chain n.tp.xi
    {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ} what₂.r.Y.tupT n.tp.xi_fin n.tp.xi_triv
    (fun μ hμ => ⟨by
        rw [what₂.r.z.lev.xiH, ← what₂.r.tup_ix, what₂.r.Y.tupTie μ hμ, ← n.xi]; rfl,
      GlobalTheory.T.weakCompatibility_of_realRowSide_adelicChain (w.D Z) _ _ _ _ _ what₂.r.z.R.toRealDat what₂.r.z.F.lv2 what₂.r.Y.tupT what₂.r.Y.hm what₂.r.Y.hTop what₂.r.Y.Ish _
        (w.D Z).what₂.onb (w.D Z).what₂.ft h3.models h3.chain what₂.r.Y.tied.sharp μ hμ⟩)
    (fun μ hμ => hio μ hμ) θ hθ ψ hψ Wf
  rw [hC] at h1
  exact ⟨Rc, h1, h2, h4⟩



theorem thEx_main : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) → ∀ 𝒮 : Slots, (∀ K B f T (w : ColW B f T) (Z : w.Lt) Wt p0 (t : RowsT K w Z Wt p0), 𝒮.Rx K B f T w Z Wt p0 t → ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0) → ThEx 𝒮 := by
  intro hW hR _ _ hDS hDSu hDSR 𝒮 hio
  refine StepW.of_all fun K B f T w _ _ _ Z l => ?_
  obtain ⟨X, hio', -, A, a, heq, hchr⟩ := GlobalTheory.Mem.Th.exists_allTied_eqTied_on hW hR hDS hDSu hDSR (w.D Z) (TC.cf w.I w.l Z) l.n.tp.xi
    {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ} l.real (recFun_of_rows hR l.what₂ l.n (hio K B f T w Z l.Wt l.p0 l.what₂ l.rx))
  obtain ⟨H, hH⟩ := hchr l.nch l.n.tp rfl
  exact ⟨X, ⟨⟨A, a, GlobalTheory.Mem.Th.weilTiedEq_of_eqTied _ _ _ _ heq, H,
    GlobalTheory.SameChrFin.sameChr_of_chrEq _ _ _ _ _ _ _ hH, a.W.ψ_std, hio'⟩⟩⟩

end GlobalTheory.ThetaRecordTrue

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaDataTrueRowsColumnsAllCompatibleStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_thetaData_trueRowsColumns_allCompatible : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) → ∀ 𝒮 : Slots, (∀ K B f T (w : ColW B f T) (Z : w.Lt) Wt p0 (t : RowsT K w Z Wt p0), 𝒮.Rx K B f T w Z Wt p0 t → ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0) → ThEx 𝒮 := by
  first | exact @GlobalTheory.ThetaRecordTrue.thEx_main | exact GlobalTheory.ThetaRecordTrue.thEx_main | (intros; apply GlobalTheory.ThetaRecordTrue.thEx_main <;> assumption)
end
end
