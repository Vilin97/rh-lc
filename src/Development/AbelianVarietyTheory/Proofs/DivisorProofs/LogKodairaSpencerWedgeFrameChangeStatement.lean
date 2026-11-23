module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPairDForm
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFrameChangeBalancedTensorsCmType
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointLogKodairaSpencerFrameChange
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFrameChangeBalancedTensorsCmTypeStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep


theorem _root_.GlobalTheory.T.det_frameChange_balancedTensors_cmType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (K : Type) [Field K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) (n n' : ℕ)
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (ε ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) K),
    (∀ j, _root_.Matrix.transpose (GlobalTheory.LogKSDiv.flatFrame A e e') * GlobalTheory.LogKSDiv.symPair (R := K) e (ε j) * GlobalTheory.LogKSDiv.flatFrame A e e' =
      ∑ k, L k j • GlobalTheory.LogKSDiv.symPair (R := K) e' (ε' k)) →
    ∃ u : K, (u = 1 ∨ u = -1) ∧
      L.det = u * ∏ τ : E →+* ℂ, (A τ).det ^ (if τ (H.rt : E) = H.rt0 then Dw.q else Dw.p) := by
  first | exact @GlobalTheory.LogKSDiv.det_frameChange_balanced | exact GlobalTheory.LogKSDiv.det_frameChange_balanced | (intros; apply GlobalTheory.LogKSDiv.det_frameChange_balanced <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointLogKodairaSpencerFrameChangeStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep


theorem _root_.GlobalTheory.T.genericPoint_logKodairaSpencer_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (w w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (X₀ TF.Y Z).functionField) ⟶ TF.Y.t.G.left)) (D D' : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField), GlobalTheory.LogKSDiv.GenKS TF Z w D → GlobalTheory.LogKSDiv.GenKS TF Z w' D' → (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (w' τ) (A τ i) (w τ i)) →
    ∃ (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
      (ε ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) (X₀ TF.Y Z).functionField),
      (∀ j, _root_.Matrix.transpose (GlobalTheory.LogKSDiv.flatFrame A e e') * GlobalTheory.LogKSDiv.symPair (R := (X₀ TF.Y Z).functionField) e (ε j) * GlobalTheory.LogKSDiv.flatFrame A e e' =
        ∑ k, L k j • GlobalTheory.LogKSDiv.symPair (R := (X₀ TF.Y Z).functionField) e' (ε' k)) ∧
      (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j, D j = ∑ k, L k j • D' k) := by
  first | exact @GlobalTheory.LogKSDiv.GenChange.genKS_change | exact GlobalTheory.LogKSDiv.GenChange.genKS_change | (intros; apply GlobalTheory.LogKSDiv.GenChange.genKS_change <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormDerivationDetPairingChangeMatrix

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.LogKSDiv

theorem topPair_change_matrix : ∀ {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}
    (D D' : Fin n → (letI := α.toAlgebra; Derivation k A A)) (L : Matrix (Fin n) (Fin n) A),
    (letI := α.toAlgebra; ∀ j, D j = ∑ i, L i j • D' i) →
    ∀ η, GlobalTheory.LogKSDiv.topPair α D η = L.det * GlobalTheory.LogKSDiv.topPair α D' η := by
  intro k A _ _ α n D D' L hD η
  letI := α.toAlgebra
  have key : (Matrix.detRowAlternating.compLinearMap
      (LinearMap.pi fun j => (KaehlerDifferential.linearMapEquivDerivation k A).symm (D j)) :
        (Ω[A⁄k]) [⋀^Fin n]→ₗ[A] A) =
      L.det • Matrix.detRowAlternating.compLinearMap
      (LinearMap.pi fun j => (KaehlerDifferential.linearMapEquivDerivation k A).symm (D' j)) := by
    ext v
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul]
    change Matrix.det (Matrix.of fun i j =>
        (KaehlerDifferential.linearMapEquivDerivation k A).symm (D j) (v i)) =
      L.det * Matrix.det (Matrix.of fun i j =>
        (KaehlerDifferential.linearMapEquivDerivation k A).symm (D' j) (v i))
    rw [mul_comm, ← Matrix.det_mul]
    congr 1
    ext i j

    simp only [Matrix.of_apply, Matrix.mul_apply, hD j, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  show (exteriorPower.alternatingMapLinearEquiv _ : _ →ₗ[A] A) η = L.det * (exteriorPower.alternatingMapLinearEquiv _ : _ →ₗ[A] A) η
  rw [key, map_smul, LinearMap.smul_apply, smul_eq_mul]

end GlobalTheory.LogKSDiv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormDerivationDetPairingChangeMatrixStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep


theorem _root_.GlobalTheory.T.topFormDerivationDetPairing_change_matrix : ∀ {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}
    (D D' : Fin n → (letI := α.toAlgebra; Derivation k A A)) (L : Matrix (Fin n) (Fin n) A),
    (letI := α.toAlgebra; ∀ j, D j = ∑ i, L i j • D' i) →
    ∀ η, GlobalTheory.LogKSDiv.topPair α D η = L.det * GlobalTheory.LogKSDiv.topPair α D' η := by
  first | exact @GlobalTheory.LogKSDiv.topPair_change_matrix | exact GlobalTheory.LogKSDiv.topPair_change_matrix | (intros; apply GlobalTheory.LogKSDiv.topPair_change_matrix <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerWedgeFrameChange

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.LogKSDiv.topPair_frameChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (w w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (X₀ TF.Y Z).functionField) ⟶ TF.Y.t.G.left)) (D D' : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), GlobalTheory.LogKSDiv.GenKS TF Z w D → GlobalTheory.LogKSDiv.GenKS TF Z w' D' → (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (w' τ) (A τ i) (w τ i)) → (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) → ∃ u : (X₀ TF.Y Z).functionField, (u = 1 ∨ u = -1) ∧ ∀ η : RatForms (s₀ TF.Y Z) Dw.dim, GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D η = u * ((∏ τ, d τ ^ (if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p) : (X₀ TF.Y Z).functionFieldˣ) : (X₀ TF.Y Z).functionField) * GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D' η := by
  intro E _ _ _ H Dw l Xo c TF Z hpq hF _ _ w w' D D' A d hw hw' hA hd
  obtain ⟨n, n', e, e', ε, ε', L, hM, hD⟩ := GlobalTheory.T.genericPoint_logKodairaSpencer_frame_change E H Dw l Xo c TF Z hpq hF w w' D D' A hw hw' hA
  obtain ⟨u, hu, hdet⟩ := GlobalTheory.T.det_frameChange_balancedTensors_cmType E H Dw _ A n n' e e' ε ε' L hM
  refine ⟨u, hu, fun η => ?_⟩
  rw [GlobalTheory.T.topFormDerivationDetPairing_change_matrix _ D D' L hD η, hdet]
  congr 2
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  split_ifs <;> simp [zpow_natCast, hd]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerWedgeFrameChangeStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.logKodairaSpencer_wedge_frameChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (w w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (X₀ TF.Y Z).functionField) ⟶ TF.Y.t.G.left)) (D D' : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), GlobalTheory.LogKSDiv.GenKS TF Z w D → GlobalTheory.LogKSDiv.GenKS TF Z w' D' → (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (w' τ) (A τ i) (w τ i)) → (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) → ∃ u : (X₀ TF.Y Z).functionField, (u = 1 ∨ u = -1) ∧ ∀ η : RatForms (s₀ TF.Y Z) Dw.dim, GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D η = u * ((∏ τ, d τ ^ (if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p) : (X₀ TF.Y Z).functionFieldˣ) : (X₀ TF.Y Z).functionField) * GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D' η := by
  first | exact @GlobalTheory.LogKSDiv.topPair_frameChange | exact GlobalTheory.LogKSDiv.topPair_frameChange | (intros; apply GlobalTheory.LogKSDiv.topPair_frameChange <;> assumption)
end
end
